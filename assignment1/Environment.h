//==--- tools/clang-check/ClangInterpreter.cpp - Clang Interpreter tool --------------===//
//===----------------------------------------------------------------------===//
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/EvaluatedExprVisitor.h"

using namespace clang;

class StackFrame {
    /// StackFrame maps Variable Declaration to Value
    /// Which are either integer or addresses (also represented using an Integer value)
    std::map<Decl*, int> mVars;
    std::map<Stmt*, int> mExprs;
    std::map<std::pair<Decl*, int>, int> mArrays;
public:
    StackFrame() : mVars(), mExprs() {
    }

    void bindDecl(Decl* decl, int val) {
        mVars[decl] = val;
    }    
    int getDeclVal(Decl * decl) {
        assert (mVars.find(decl) != mVars.end());
        return mVars.find(decl)->second;
    }
    void bindStmt(Stmt * stmt, int val) {
        mExprs[stmt] = val;
    }
    void bindStmtArray(Decl* base, int idx, int val) {
        mArrays[std::make_pair(base, idx)] = val;
    }
    int getStmtVal(Stmt * stmt) {
        assert (mExprs.find(stmt) != mExprs.end());
        return mExprs[stmt];
    }
    int getStmtValArray(Decl* base, int idx) {
        auto array = std::make_pair(base, idx);
        assert (mArrays.find(array) != mArrays.end());
        return mArrays[array];
    }
    int getRetValue() {
        for (auto item : mExprs) {
            if (dyn_cast<ReturnStmt>(item.first)) {
                return item.second;
            }
        }
        llvm::errs() << "[ERROR] Function return value not found!\n";
        exit(-1);
    } 
};

class HeapFrame {
public:
    int val;
    int size;
    bool isValid;
    HeapFrame(int _val=0) : val(_val), isValid(true), size(-1) {}
};

class Environment {
    std::vector<StackFrame> mStack;
    std::vector<HeapFrame> mHeap;

    /// Declartions to the built-in function!
    FunctionDecl * mFree;				
    FunctionDecl * mMalloc;
    FunctionDecl * mInput;
    FunctionDecl * mOutput;
    FunctionDecl * mEntry;

public:
    /// Get the declartions to the built-in functions
    Environment() : mStack(), mHeap(), mFree(NULL), mMalloc(NULL), mInput(NULL), mOutput(NULL), mEntry(NULL) {}

    /// Initialize the Environment
    void init(TranslationUnitDecl * unit) {
        /// Global symbols
        mStack.push_back(StackFrame());
        for (auto it = unit->decls_begin(); it != unit->decls_end(); ++it) {
            if (auto fdecl = dyn_cast<FunctionDecl>(*it) ) {
                if (fdecl->getName().equals("FREE")) mFree = fdecl;
                else if (fdecl->getName().equals("MALLOC")) mMalloc = fdecl;
                else if (fdecl->getName().equals("GET")) mInput = fdecl;
                else if (fdecl->getName().equals("PRINT")) mOutput = fdecl;
                else if (fdecl->getName().equals("main")) mEntry = fdecl;
            }
            else if (auto vdecl = dyn_cast<VarDecl>(*it)) {
                addVarDecl(vdecl);
            }
        }
        mStack.push_back(mStack.back());
    }

    FunctionDecl * getEntry() {
        return mEntry;
    }

    int getValue(Expr *expr) {
        /// For literal, get its raw data.
        if (auto expr_int = dyn_cast<IntegerLiteral>(expr)) {
            return *(expr_int->getValue().getRawData());
        }
        else if (auto expr_char = dyn_cast<CharacterLiteral>(expr)) {
            return expr_char->getValue();
        }
        /// For variable, get its value for stack.
        else if (auto expr_array = dyn_cast<ArraySubscriptExpr>(expr)) {
            return mStack.back().getStmtValArray(
                getArrayDecl(expr_array),
                getValue(expr_array->getIdx())
            );
        }
        else if (auto pointer_type = dyn_cast<UnaryOperator>(expr)) {
            if (pointer_type->getOpcode() != UO_Deref) {
                return mStack.back().getStmtVal(expr);
            }
            return mHeap[mStack.back().getStmtVal(expr)].val;
        }
        else {
            return mStack.back().getStmtVal(expr);
        }
    }

    void paren(ParenExpr * expr) {
        mStack.back().bindStmt(expr, getValue(expr->getSubExpr()));
    }

    void typeTraitExpr(UnaryExprOrTypeTraitExpr * expr) {
        if (auto array_type = dyn_cast<ConstantArrayType>(expr->getTypeOfArgument())) {
            mStack.back().bindStmt(expr, array_type->getSize().getSExtValue());
        }
        else {
            mStack.back().bindStmt(expr, 1);
        }
    }

    void unop(UnaryOperator *uop) {
        auto opcode = uop->getOpcode();
        if (opcode == UO_Minus) {
            mStack.back().bindStmt(uop, -getValue(uop->getSubExpr()));
        }
        else if (opcode == UO_Deref) {
            int addr = getValue(uop->getSubExpr());
            assert(mHeap[addr].isValid);
            mStack.back().bindStmt(uop, addr);
        }
        else {
            llvm::errs() << "[ERROR] Unknown unary op!\n";
            exit(-1);
        }
    }

    Decl* getArrayDecl(ArraySubscriptExpr* array) {
        auto cast = dyn_cast<ImplicitCastExpr>(array->getBase());
        auto ref = dyn_cast<DeclRefExpr>(cast->getSubExpr());
        return ref->getFoundDecl();
    }

    void binop(BinaryOperator *bop) {
        Expr * left = bop->getLHS();
        Expr * right = bop->getRHS();

        auto opcode = bop->getOpcode();
        if (opcode == BO_Assign) {
            int val = getValue(right);
            if (auto array = dyn_cast<ArraySubscriptExpr>(left)) {
                mStack.back().bindStmtArray(
                    getArrayDecl(array),
                    getValue(array->getIdx()),
                    val
                );
            }
            else if (auto pointer_type = dyn_cast<UnaryOperator>(left)) {
                if (pointer_type->getOpcode() != UO_Deref) {
                    mStack.back().bindStmt(left, val);
                }
                else {
                    auto addr = mStack.back().getStmtVal(left); 
                    mHeap[addr].val = val;
                }
            }
            else {
                mStack.back().bindStmt(left, val);
            }
            if (DeclRefExpr * declexpr = dyn_cast<DeclRefExpr>(left)) {
                Decl * decl = declexpr->getFoundDecl();
                mStack.back().bindDecl(decl, val);
            }
        }
        else if (opcode == BO_Add) {
            mStack.back().bindStmt(bop, getValue(left) + getValue(right));
        }
        else if (opcode == BO_Sub) {
            mStack.back().bindStmt(bop, getValue(left) - getValue(right));
        }
        else if (opcode == BO_Mul) {
            mStack.back().bindStmt(bop, getValue(left) * getValue(right));
        }
        else if (opcode == BO_Div) {
            mStack.back().bindStmt(bop, getValue(left) / getValue(right));
        }
        else if (opcode == BO_GT) {
            mStack.back().bindStmt(bop, getValue(left) > getValue(right));
        }
        else if (opcode == BO_GE) {
            mStack.back().bindStmt(bop, getValue(left) >= getValue(right));
        }
        else if (opcode == BO_LT) {
            mStack.back().bindStmt(bop, getValue(left) < getValue(right));
        }
        else if (opcode == BO_LE) {
            mStack.back().bindStmt(bop, getValue(left) <= getValue(right));
        }
        else if (opcode == BO_EQ) {
            mStack.back().bindStmt(bop, getValue(left) == getValue(right));
        }
        else {
            llvm::errs() << "[ERROR] Unknown binary op!\n";
            exit(-1);
        }
    }

    void addVarDecl(VarDecl *vdecl) {
        if (vdecl->hasInit()) {
            mStack.back().bindDecl(vdecl, getValue(vdecl->getInit()));
        }
        else {
            mStack.back().bindDecl(vdecl, 0);
        }
    }

    void decl(DeclStmt * declstmt) {
        for (auto it = declstmt->decl_begin(); it != declstmt->decl_end(); ++it) {
            if (VarDecl * vdecl = dyn_cast<VarDecl>(*it)) {
                addVarDecl(vdecl);
            }
        }
    }

    void declref(DeclRefExpr * declref) {
        if (declref->getType()->isFunctionType()) {
            mStack.back().bindStmt(declref, -1);
            return;
        }
        Decl* decl = declref->getFoundDecl();
        int val = mStack.back().getDeclVal(decl);
        mStack.back().bindStmt(declref, val);
    }

    void cast(CastExpr * castexpr) {
        Expr * expr = castexpr->getSubExpr();
        int val = getValue(expr);
        mStack.back().bindStmt(castexpr, val);
    }

    void save(CallExpr *callexpr) {
        StackFrame currentFrame = mStack.front();
        FunctionDecl *callee = callexpr->getDirectCallee()->getDefinition();
        auto formalArgs = callee->param_begin();
        auto actualArgs = callexpr->arg_begin();
        while (formalArgs != callee->param_end() && actualArgs != callexpr->arg_end()) {
            currentFrame.bindDecl(*formalArgs, getValue(*actualArgs));
            formalArgs++;
            actualArgs++;
        }
        assert(formalArgs == callee->param_end() && actualArgs == callexpr->arg_end());
        mStack.push_back(currentFrame);
    }

    void load(CallExpr *callexpr) {
        FunctionDecl *callee = callexpr->getDirectCallee();
        if (callee->getReturnType()->isVoidType()) {
            mStack.pop_back();
            return;
        }
        int retval = mStack.back().getRetValue();
        mStack.pop_back();
        mStack.back().bindStmt(callexpr, retval);
    }

    void retStmt(ReturnStmt *ret) {
        mStack.back().bindStmt(ret, getValue(ret->getRetValue()));
    }

    /// !TODO Support Function Call
    Stmt* getFuncBody(CallExpr *callexpr) {
        FunctionDecl * callee = callexpr->getDirectCallee();
        if (callee == mInput) {
            int val;
            llvm::errs() << "Please Input an Integer Value : ";
            scanf("%d", &val);
            mStack.back().bindStmt(callexpr, val);
            return nullptr;
        } 
        else if (callee == mOutput) {
            int val;
            Expr * decl = callexpr->getArg(0);
            val = getValue(decl);
            llvm::errs() << val;
            return nullptr;
        }
        else if (callee == mMalloc) {
            Expr * decl = callexpr->getArg(0);
            size_t size = getValue(decl); 
            int addr = mHeap.size();
            mStack.back().bindStmt(callexpr, addr);
            mHeap.resize(mHeap.size() + size);
            mHeap[addr].size = size;
            return nullptr;
        }
        else if (callee == mFree) {
            Expr * decl = callexpr->getArg(0);
            int addr = getValue(decl);
            int size = mHeap[addr].size;
            assert(size != -1);
            for (int i = addr; i < addr + size; ++i) {
                mHeap[i].isValid = false;
            }
            mHeap[addr].size = -1; 
            return nullptr;
        }
        else {
            return callee->getBody();
        }
    }

    bool getCondValue(Expr *cond) {
        return getValue(cond);
    }

};

class InterpreterVisitor : public EvaluatedExprVisitor<InterpreterVisitor> {
    bool isReturned;
public:
    explicit InterpreterVisitor(const ASTContext &context, Environment * env) 
        : EvaluatedExprVisitor(context), mEnv(env), isReturned(false) {}

    virtual ~InterpreterVisitor() {}

    virtual void VisitStmt(Stmt * stmt) {
        for (auto substmt : stmt->children()) {
            if (isReturned) {
                break;
            }
            if (substmt) {
                Visit(substmt);
            }
        }
    }

    virtual void VisitUnaryExprOrTypeTraitExpr(UnaryExprOrTypeTraitExpr * expr) {
        VisitStmt(expr);
        mEnv->typeTraitExpr(expr);
    }
    
    virtual void VisitParenExpr(ParenExpr * expr) {
        VisitStmt(expr);
        mEnv->paren(expr);
    }

    virtual void VisitArraySubscriptExpr(ArraySubscriptExpr * expr) {
        VisitStmt(expr);        
    }

    virtual void VisitUnaryOperator(UnaryOperator * uop) {
        VisitStmt(uop);
        mEnv->unop(uop);
    }

    virtual void VisitBinaryOperator (BinaryOperator * bop) {
        VisitStmt(bop);
        mEnv->binop(bop);
    }

    virtual void VisitDeclRefExpr(DeclRefExpr * expr) {
        VisitStmt(expr);
        mEnv->declref(expr);
    }

    virtual void VisitCastExpr(CastExpr * expr) {
        VisitStmt(expr);
        mEnv->cast(expr);
    }

    virtual void VisitCallExpr(CallExpr * call) {
        VisitStmt(call);
        Stmt* body = mEnv->getFuncBody(call);
        if (!body) return;
        mEnv->save(call);
        VisitStmt(body);
        isReturned = false;
        mEnv->load(call);
    }

    virtual void VisitDeclStmt(DeclStmt * declstmt) {
        VisitStmt(declstmt);
        mEnv->decl(declstmt);
    }

    virtual void VisitReturnStmt(ReturnStmt* ret) {
        VisitStmt(ret);
        mEnv->retStmt(ret);
        isReturned = true;
    }

    virtual void VisitIfStmt(IfStmt* ifstmt) {
        auto cond = ifstmt->getCond();
        Visit(cond);
        if (mEnv->getCondValue(cond)) {
            Visit(ifstmt->getThen());
        }
        else {
            if (auto elsestmt = ifstmt->getElse()) {
                Visit(elsestmt);
            }
        }
    }

    virtual void VisitWhileStmt(WhileStmt* whilestmt) {
        while (true) {
            auto cond = whilestmt->getCond();
            Visit(cond);
            if (!mEnv->getCondValue(cond)) {
                break;
            }
            if (auto body = whilestmt->getBody()) {
                Visit(body);
            }
        }
    }

    virtual void VisitForStmt(ForStmt* forstmt) {
        if (auto init = forstmt->getInit()) {
            Visit(init);
        }
        while (true) {
            if (auto cond = forstmt->getCond()) {
                Visit(cond);
                if (!mEnv->getCondValue(cond)) {
                    break;
                }
            }
            if (auto body = forstmt->getBody()) {
                Visit(body);
            }
            if (auto inc = forstmt->getInc()) {
                Visit(inc);
            }
        }
    }

private:
    Environment * mEnv;
};
