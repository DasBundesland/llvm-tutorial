#include "KaleidoscopeJIT.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>

using namespace llvm;
using namespace orc;
class ExprAST
{
public:
    virtual ~ExprAST() {}
    virtual Value *codegen() = 0;
};

class NumberExprAST : public ExprAST
{
    double Val;

public:
    NumberExprAST(double v) : Val(v) {}
    virtual Value *codegen();
};

class VariableExprAST : public ExprAST
{
    std::string Name;

public:
    VariableExprAST(const std::string &Name) : Name(Name) {}
    virtual Value *codegen();
};

class BinaryExprAST : public ExprAST
{
    char Op;
    std::unique_ptr<ExprAST> LHS, RHS;

public:
    BinaryExprAST(char op, std::unique_ptr<ExprAST> LHS, std::unique_ptr<ExprAST> RHS)
        : Op(op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}
    Value *codegen() override;
};

class UnaryExprAST : public ExprAST {
    char Opcode;
    std::unique_ptr<ExprAST> Operand;

public:
    UnaryExprAST(char Opcode, std::unique_ptr<ExprAST> Operand):
    Opcode(Opcode), Operand(std::move(Operand)) {}

    Value * codegen() override;
};

class CallExprAST : public ExprAST
{
    std::string Callee;
    std::vector<std::unique_ptr<ExprAST>> Args;

public:
    CallExprAST(const std::string &Callee, std::vector<std::unique_ptr<ExprAST>> Args) : Callee(Callee), Args(std::move(Args)) {}
    Value *codegen() override;
};

class PrototypeAST : public ExprAST
{
    std::string Name;
    std::vector<std::string> Args;
    bool IsOp;
    unsigned Prec;

public:
    PrototypeAST(const std::string &name, std::vector<std::string> Args,
                 bool IsOp = false, unsigned Prec = 0)
        : Name(name), Args(std::move(Args)), IsOp(IsOp), Prec(Prec) {}
    Function *codegen() override;
    const std::string &getName() const { return Name; }
    bool isUnaryOp() const { return IsOp && Args.size() == 1; }
    bool isBinaryOp() const { return IsOp && Args.size() == 2; }

    char getOperatorName() const
    {
        assert(isUnaryOp() || isBinaryOp());
        return Name[Name.size() - 1];
    }

    unsigned getPrecedence() const { return Prec; }
};

class FunctionAST : public ExprAST
{
    std::unique_ptr<PrototypeAST> Proto;
    std::unique_ptr<ExprAST> Body;

public:
    FunctionAST(std::unique_ptr<PrototypeAST> Proto, std::unique_ptr<ExprAST> Body)
        : Proto(std::move(Proto)), Body(std::move(Body)) {}
    Function *codegen() override;
};

class IfExprAST : public ExprAST
{
    std::unique_ptr<ExprAST> Cond, Then, Else;

public:
    IfExprAST(std::unique_ptr<ExprAST> Cond, std::unique_ptr<ExprAST> Then,
              std::unique_ptr<ExprAST> Else) : Cond(std::move(Cond)), Then(std::move(Then)),
                                               Else(std::move(Else)) {}
    Value *codegen() override;
};

class ForExprAST : public ExprAST
{
    std::string VarName;
    std::unique_ptr<ExprAST> Start, End, Step, Body;

public:
    ForExprAST(const std::string &VarName, std::unique_ptr<ExprAST> Start,
               std::unique_ptr<ExprAST> End, std::unique_ptr<ExprAST> Step,
               std::unique_ptr<ExprAST> Body) : VarName(VarName), Start(std::move(Start)), End(std::move(End)), Step(std::move(Step)),
                                                Body(std::move(Body)) {}

    Value *codegen() override;
};

enum Token
{
    // The EOF token
    tok_eof = -1,
    // Tokens for the def and extern keywords
    tok_def = -2,
    tok_extern = -3,
    // Base tokens in the language, double literals and identifiers
    tok_identifier = -4,
    tok_number = -5,
    tok_if = -6,
    tok_then = -7,
    tok_else = -8,
    tok_for = -9,
    tok_in = -10,
    tok_binary = -11,
    tok_unary = -12
};

static std::string Identifier;
static double Number;

static int gettok()
{
    static int LastChar = ' ';

    while (isspace(LastChar))
        LastChar = getchar();
    if (isalpha(LastChar))
    {
        Identifier = LastChar;
        while (isalnum((LastChar = getchar())))
            Identifier += LastChar;

        if (Identifier == "def")
            return tok_def;
        if (Identifier == "extern")
            return tok_extern;
        if (Identifier == "if")
            return tok_if;
        if (Identifier == "then")
            return tok_then;
        if (Identifier == "else")
            return tok_else;
        if (Identifier == "for")
            return tok_for;
        if (Identifier == "in")
            return tok_in;
        if (Identifier == "binary")
            return tok_binary;
        if (Identifier == "unary")
            return tok_unary;
        return tok_identifier;
    }
    if (isdigit(LastChar) || LastChar == '.')
    {
        int DotCt = 0;
        std::string Lit;
        do
        {
            Lit += LastChar;
            if (LastChar == '.')
            {
                DotCt++;
            }
            LastChar = getchar();

        } while (DotCt <= 1 && (isdigit(LastChar) || LastChar == '.'));
        Number = strtod(Lit.c_str(), nullptr);
        // printf("%s\n", Lit.c_str());
        return tok_number;
    }
    if (LastChar == '#')
    {
        do
            LastChar = getchar();
        while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

        if (LastChar != EOF)
            return gettok();
    }
    if (LastChar == EOF)
    {
        return tok_eof;
    }
    int RetChar = LastChar;
    LastChar = getchar();
    return RetChar;
}

static int CurTok;
static int getNextToken()
{
    return CurTok = gettok();
}
std::unique_ptr<ExprAST> LogError(const char *Str)
{
    fprintf(stderr, "Logerror: %s\n", Str);
    return nullptr;
}
std::unique_ptr<PrototypeAST> LogErrorP(const char *Str)
{
    LogError(Str);
    return nullptr;
}

static std::unique_ptr<ExprAST> ParseNumberExpr()
{
    auto Result = std::make_unique<NumberExprAST>(Number);
    getNextToken();
    return std::move(Result);
}

static std::unique_ptr<ExprAST> ParseExpression();

static std::unique_ptr<ExprAST> ParseParenExpr()
{
    getNextToken();
    auto V = ParseExpression();
    if (!V)
        return nullptr;
    if (CurTok != ')')
        return LogError("Expected ')'");
    getNextToken();
    return V;
}

static std::unique_ptr<ExprAST> ParseIdentifierExpr()
{
    std::string IdName = Identifier;

    getNextToken();

    if (CurTok != '(')
        return std::make_unique<VariableExprAST>(IdName);
    getNextToken();
    std::vector<std::unique_ptr<ExprAST>> Args;
    if (CurTok != ')')
    {
        while (true)
        {
            if (auto Arg = ParseExpression())
                Args.push_back(std::move(Arg));
            else
                return nullptr;

            if (CurTok == ')')
                break;

            if (CurTok != ',')
                return LogError("Expected ')' or ',' in argument list");
            getNextToken();
        }
    }
    getNextToken();
    return std::make_unique<CallExprAST>(IdName, std::move(Args));
}

static std::unique_ptr<ExprAST> ParseIfExpr()
{
    getNextToken();

    auto Condition = ParseExpression();
    if (!Condition)
        return nullptr;

    if (CurTok != tok_then)
        return LogError("Expected then after if!");

    getNextToken();

    auto ThenBlock = ParseExpression();
    if (!ThenBlock)
        return nullptr;
    if (CurTok != tok_else)
        return LogError("Expected else after then block!");
    getNextToken();
    auto Else = ParseExpression();
    if (!Else)
        return nullptr;

    return std::make_unique<IfExprAST>(std::move(Condition), std::move(ThenBlock), std::move(Else));
}

static std::unique_ptr<ExprAST> ParseForExpr()
{
    getNextToken();

    if (CurTok != tok_identifier)
        return LogError("Expected identifier after for!");
    std::string IdName = Identifier;
    getNextToken();

    if (CurTok != '=')
        return LogError("Expected assignment for variable after for!");
    getNextToken();

    auto Start = ParseExpression();
    if (!Start)
        return nullptr;
    if (CurTok != ',')
        return LogError("Expected ',' after for start value!");
    getNextToken();

    auto End = ParseExpression();
    if (!End)
        return nullptr;

    std::unique_ptr<ExprAST> Step;
    if (CurTok == ',')
    {
        getNextToken();
        Step = ParseExpression();
        if (!Step)
            return nullptr;
    }

    if (CurTok != tok_in)
        return LogError("Expected 'in' after for");
    getNextToken();

    auto Body = ParseExpression();
    if (!Body)
        return nullptr;

    return std::make_unique<ForExprAST>(IdName, std::move(Start),
                                        std::move(End), std::move(Step), std::move(Body));
}

static std::unique_ptr<ExprAST> ParsePrimary()
{
    switch (CurTok)
    {
    default:
        return LogError("Unknown token!");
    case tok_identifier:
        return ParseIdentifierExpr();
    case tok_number:
        return ParseNumberExpr();
    case '(':
        return ParseParenExpr();
    case tok_if:
        return ParseIfExpr();
    case tok_for:
        return ParseForExpr();
    }
}

static std::map<char, int> BINOP_PRECEDENCE;

static int GetTokPrecedence()
{
    if (!isascii(CurTok))
        return -1;

    int TokPrec = BINOP_PRECEDENCE[CurTok];
    if (TokPrec <= 0)
        return -1;
    return TokPrec;
}

static std::unique_ptr<ExprAST> ParseUnary() {
    if(!isascii(CurTok) || CurTok == '(' || CurTok == ',') return ParsePrimary();

    int Opc = CurTok;
    getNextToken();
    if(auto Operand = ParseUnary()) return std::make_unique<UnaryExprAST>(Opc, std::move(Operand));
    return nullptr;
}

static std::unique_ptr<ExprAST> ParseBinOpRHS(int Prec, std::unique_ptr<ExprAST> LHS);

static std::unique_ptr<ExprAST> ParseExpression()
{
    auto LHS = ParseUnary();
    if (!LHS)
        return nullptr;
    return ParseBinOpRHS(0, std::move(LHS));
}

static std::unique_ptr<ExprAST> ParseBinOpRHS(int Prec, std::unique_ptr<ExprAST> LHS)
{
    while (1)
    {
        int TokPrec = GetTokPrecedence();
        if (TokPrec < Prec)
            return LHS;

        int BinOp = CurTok;
        getNextToken();

        auto RHS = ParseUnary();
        if (!RHS)
            return nullptr;
        int NextPrec = GetTokPrecedence();
        if (TokPrec < NextPrec)
        {
            RHS = ParseBinOpRHS(TokPrec + 1, std::move(RHS));
            if (!RHS)
                return nullptr;
        }

        LHS = std::make_unique<BinaryExprAST>(BinOp, std::move(LHS), std::move(RHS));
    }
}

static std::unique_ptr<PrototypeAST> ParseProto()
{

    std::string FuncName = Identifier;
    unsigned FType = 0;
    unsigned OPrec = 30;
    
    switch (CurTok) {
    default:
        return LogErrorP("Expected function name in prototype!");
        case tok_identifier:
            FuncName = Identifier;
            FType = 0;
            getNextToken();
            break;
        case tok_unary:
            getNextToken();
            if(!isascii(CurTok)) return LogErrorP("Expected unop");
            FuncName = "unary";
            FuncName += (char) CurTok;
            FType = 1;
            getNextToken();
            break;
        case tok_binary:
            getNextToken();
            if(!isascii(CurTok)) return LogErrorP("Expected binop!");
            FuncName = "binary";
            FuncName += (char)CurTok;
            FType = 2;
            getNextToken();
            if(CurTok == tok_number){
                if(Number < 1 || Number > 100) return LogErrorP("Precedence must be within (1,100).");
                OPrec = (unsigned) Number;
                getNextToken();
            }
            break;
    }

    if (CurTok != '(')
        return LogErrorP("Expected opening paren!");

    std::vector<std::string> ArgNames;

    while (getNextToken() == tok_identifier)
    {
        ArgNames.push_back(Identifier);
    }
    if (CurTok != ')')
        return LogErrorP("Expected closing paren!");

    getNextToken();
    if(FType && ArgNames.size() != FType) return LogErrorP("Invalid number of operands for operator!");
    
    return std::make_unique<PrototypeAST>(FuncName, std::move(ArgNames), FType != 0, OPrec);
}

static std::unique_ptr<FunctionAST> ParseDefinition()
{
    getNextToken();
    auto Proto = ParseProto();
    if (!Proto)
        return nullptr;
    if (auto E = ParseExpression())
        return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
    return nullptr;
}

static std::unique_ptr<PrototypeAST> ParseExtern()
{
    getNextToken();
    return ParseProto();
}

static std::unique_ptr<FunctionAST> ParseTopLevelExpr()
{
    if (auto E = ParseExpression())
    {
        auto Proto = std::make_unique<PrototypeAST>("_anon_expr", std::vector<std::string>());
        return std::make_unique<FunctionAST>(std::move(Proto), std::move(E));
    }
    return nullptr;
}


// CODEGEN
static std::unique_ptr<LLVMContext> TheContext;
static std::unique_ptr<IRBuilder<>> Builder;
static std::unique_ptr<Module> TheModule;
static std::unique_ptr<legacy::FunctionPassManager> TheFPM;
static std::map<std::string, Value *> NamedValues;
static std::unique_ptr<KaleidoscopeJIT> TheJIT;
static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;

static void InitializeModule()
{
    TheContext = std::make_unique<LLVMContext>();
    TheModule = std::make_unique<Module>("my cool jit", *TheContext);

    Builder = std::make_unique<IRBuilder<>>(*TheContext);
}

Function *getFunction(std::string Name)
{
    if (auto *F = TheModule->getFunction(Name))
    {
        return F;
    }

    auto FI = FunctionProtos.find(Name);
    if (FI != FunctionProtos.end())
    {
        return FI->second->codegen();
    }

    return nullptr;
}

static void InitializeModuleAndPassManager(void)
{
    TheModule = std::make_unique<Module>("my cool jit", *TheContext);
    TheModule->setDataLayout(TheJIT->getTargetMachine().createDataLayout());
    TheFPM = std::make_unique<legacy::FunctionPassManager>(TheModule.get());
    TheFPM->add(createInstructionCombiningPass());
    TheFPM->add(createReassociatePass());
    TheFPM->add(createGVNPass());
    TheFPM->add(createCFGSimplificationPass());
    TheFPM->doInitialization();
}

Value *LogErrorV(const char *Str)
{
    LogError(Str);
    return nullptr;
}

Value *NumberExprAST::codegen()
{
    return ConstantFP::get(*TheContext, APFloat(Val));
}

Value *VariableExprAST::codegen()
{
    Value *V = NamedValues[Name];
    if (!V)
        LogErrorV("Unknown variable name");
    return V;
}

Value *BinaryExprAST::codegen()
{
    Value *L = LHS->codegen();
    Value *R = RHS->codegen();
    if (!L || !R)
        return nullptr;

    switch (Op)
    {
    case '+':
        return Builder->CreateFAdd(L, R, "addtmp");
    case '-':
        return Builder->CreateFSub(L, R, "subtmp");
    case '*':
        return Builder->CreateFMul(L, R, "multmp");
    case '<':
        L = Builder->CreateFCmpULT(L, R, "cmptmp");
        return Builder->CreateUIToFP(L, Type::getDoubleTy(*TheContext), "booltmp");
    case '>':
        L = Builder->CreateFCmpUGT(L, R, "cmptmp");
        return Builder->CreateUIToFP(L, Type::getDoubleTy(*TheContext), "booltmp");
    default:
        break;
    }

    Function* F = getFunction(std::string("binary") + Op);
    assert(F && "binary operator not found!");

    Value* Ops[2] = {L, R};
    return Builder->CreateCall(F, Ops, "binop");
}

Value* UnaryExprAST::codegen(){
    Value* OperandV = Operand->codegen();
    if(!OperandV) return nullptr;

    Function* f = getFunction(std::string("unary") + Opcode);
    if(!f) return LogErrorV("Unknown unop!");
    return Builder->CreateCall(f, OperandV, "unop");
}

Value *CallExprAST::codegen()
{
    Function *CalleeF = getFunction(Callee);
    if (!CalleeF)
        return LogErrorV("Unknown function!");
    if (CalleeF->arg_size() != Args.size())
        return LogErrorV("Incorrect number of arguments passed to function!");
    std::vector<Value *> ArgsV;
    for (unsigned i = 0, e = Args.size(); i != e; ++i)
    {
        ArgsV.push_back(Args[i]->codegen());
        if (!ArgsV.back())
            return nullptr;
    }

    return Builder->CreateCall(CalleeF, ArgsV, "calltmp");
}

Function *PrototypeAST::codegen()
{
    std::vector<Type *> Doubles(Args.size(), Type::getDoubleTy(*TheContext));
    FunctionType *FT = FunctionType::get(Type::getDoubleTy(*TheContext), Doubles, false);
    Function *F = Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());
    unsigned Idx = 0;
    for (auto &Arg : F->args())
    {
        Arg.setName(Args[Idx++]);
    }
    return F;
}

Function *FunctionAST::codegen()
{
    auto &P = *Proto;
    FunctionProtos[Proto->getName()] = std::move(Proto);
    Function *TheFunction = getFunction(P.getName());
    if (!TheFunction)
        return nullptr;
    if(P.isBinaryOp()) BINOP_PRECEDENCE[P.getOperatorName()] = P.getPrecedence();
    BasicBlock *BB = BasicBlock::Create(*TheContext, "entry", TheFunction);
    Builder->SetInsertPoint(BB);
    NamedValues.clear();
    for (auto &Arg : TheFunction->args())
    {
        NamedValues[Arg.getName()] = &Arg;
    }

    if (Value *RetVal = Body->codegen())
    {
        Builder->CreateRet(RetVal);
        verifyFunction(*TheFunction);
        TheFPM->run(*TheFunction);
        return TheFunction;
    }
    TheFunction->eraseFromParent();
    return nullptr;
}

Value *IfExprAST::codegen()
{
    Value *CondVal = Cond->codegen();
    if (!CondVal)
        return nullptr;
    CondVal = Builder->CreateFCmpONE(CondVal, ConstantFP::get(*TheContext, APFloat(0.0)), "ifcond");
    Function *TheFunc = Builder->GetInsertBlock()->getParent();
    BasicBlock *ThenBB = BasicBlock::Create(*TheContext, "then", TheFunc);
    BasicBlock *ElseBB = BasicBlock::Create(*TheContext, "else");
    BasicBlock *MergeBB = BasicBlock::Create(*TheContext, "ifcont");
    Builder->CreateCondBr(CondVal, ThenBB, ElseBB);
    Builder->SetInsertPoint(ThenBB);

    Value *ThenV = Then->codegen();
    if (!ThenV)
        return nullptr;

    Builder->CreateBr(MergeBB);
    ThenBB = Builder->GetInsertBlock();

    TheFunc->getBasicBlockList().push_back(ElseBB);
    Builder->SetInsertPoint(ElseBB);
    Value *ElseV = Else->codegen();
    if (!ElseV)
        return nullptr;
    Builder->CreateBr(MergeBB);
    ElseBB = Builder->GetInsertBlock();

    TheFunc->getBasicBlockList().push_back(MergeBB);
    Builder->SetInsertPoint(MergeBB);
    PHINode *PN = Builder->CreatePHI(Type::getDoubleTy(*TheContext), 2, "iftmp");

    PN->addIncoming(ThenV, ThenBB);
    PN->addIncoming(ElseV, ElseBB);
    return PN;
}

Value *ForExprAST::codegen()
{
    Value *StartVal = Start->codegen();
    if (!StartVal)
        return nullptr;

    Function *TheFunction = Builder->GetInsertBlock()->getParent();
    BasicBlock *PreHeader = Builder->GetInsertBlock();
    BasicBlock *Loop = BasicBlock::Create(*TheContext, "loop", TheFunction);
    Builder->CreateBr(Loop);

    Builder->SetInsertPoint(Loop);
    PHINode *IterVar = Builder->CreatePHI(Type::getDoubleTy(*TheContext), 2, VarName.c_str());
    IterVar->addIncoming(StartVal, PreHeader);

    Value *Old = NamedValues[VarName];
    NamedValues[VarName] = IterVar;
    if (!Body->codegen())
        return nullptr;

    Value *StepValue = nullptr;
    if (Step)
    {
        StepValue = Step->codegen();
        if (!StepValue)
            return nullptr;
    }
    else
    {
        StepValue = ConstantFP::get(*TheContext, APFloat(1.0));
    }

    Value *NextVar = Builder->CreateFAdd(IterVar, StepValue, "nextvar");
    Value *EndCond = End->codegen();
    if (!EndCond)
        return nullptr;

    EndCond = Builder->CreateFCmpONE(EndCond, ConstantFP::get(*TheContext, APFloat(0.0)), "loopcond");
    BasicBlock *LoopEndBB = Builder->GetInsertBlock();

    BasicBlock *AfterBB = BasicBlock::Create(*TheContext, "afterloop", TheFunction);
    Builder->CreateCondBr(EndCond, Loop, AfterBB);
    Builder->SetInsertPoint(AfterBB);

    IterVar->addIncoming(NextVar, LoopEndBB);
    if (Old)
        NamedValues[VarName] = Old;
    else
        NamedValues.erase(VarName);
    return Constant::getNullValue(Type::getDoubleTy(*TheContext));
}

static void HandleDefinition()
{
    if (auto FnAST = ParseDefinition())
    {
        if (auto FnIR = FnAST->codegen())
        {
            fprintf(stderr, "Parsed a func definition. \n");
            FnIR->print(errs());
            fprintf(stderr, "\n");
            TheJIT->addModule(std::move(TheModule));
            InitializeModuleAndPassManager();
        }
    }
    else
    {
        getNextToken();
    }
}

static void HandleExtern()
{
    if (auto PrAST = ParseExtern())
    {
        if (auto *PrIR = PrAST->codegen())
        {
            fprintf(stderr, "Parsed an extern. \n");
            PrIR->print(errs());
            fprintf(stderr, "\n");
            FunctionProtos[PrAST->getName()] = std::move(PrAST);
        }
    }
    else
    {
        getNextToken();
    }
}

static void HandleTopLevelExpression()
{
    if (auto FnAST = ParseTopLevelExpr())
    {
        if (auto FnIR = FnAST->codegen())
        {
            fprintf(stderr, "Parsed top-level expression. \n\n");
            // FnIR->print(errs());
            auto H = TheJIT->addModule(std::move(TheModule));
            InitializeModuleAndPassManager();

            auto ExprSymbol = TheJIT->findSymbol("_anon_expr");
            assert(ExprSymbol && "Function not found");

            double (*FP)() = (double (*)())(intptr_t)cantFail(ExprSymbol.getAddress());
            fprintf(stderr, "Evaluated to %f\n", FP());

            TheJIT->removeModule(H);
        }
    }
    else
    {
        getNextToken();
    }
}

#ifdef _WIN32
#define DLLEXPORT _declspec(dllexport)
#else
#define DLLEXPORT
#endif

extern "C" DLLEXPORT double putchard(double X)
{
    fputc((char)X, stderr);
    return 0;
}

extern "C" DLLEXPORT double printd(double X){
    printf("%f\n", X);
    return 0;
}

static void DriverLoop()
{
    while (true)
    {
        fprintf(stderr, "in>");
        switch (CurTok)
        {
        case tok_eof:
            return;
        case ';':
            getNextToken();
            break;
        case tok_def:
            HandleDefinition();
            break;
        case tok_extern:
            HandleExtern();
            break;
        default:
            HandleTopLevelExpression();
            break;
        }
    }
}

int main()
{
    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();
    BINOP_PRECEDENCE['<'] = 10;
    BINOP_PRECEDENCE['>'] = 10;
    BINOP_PRECEDENCE['+'] = 20;
    BINOP_PRECEDENCE['-'] = 20;
    BINOP_PRECEDENCE['*'] = 40;
    fprintf(stderr, "in>");
    getNextToken();
    InitializeModule();
    TheJIT = std::make_unique<KaleidoscopeJIT>();
    InitializeModuleAndPassManager();
    DriverLoop();
    TheModule->print(errs(), nullptr);
    return 0;
}