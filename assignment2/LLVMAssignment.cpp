//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <llvm/IR/Use.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/ToolOutputFile.h>

#include <llvm/Transforms/Scalar.h>
#include <llvm/Transforms/Utils.h>

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>

#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>
#include <llvm/IR/Instructions.h>

using namespace llvm;
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }
/* In LLVM 5.0, when  -O0 passed to clang , the functions generated with clang will
 * have optnone attribute which would lead to some transform passes disabled, like mem2reg.
 */
struct EnableFunctionOptPass: public FunctionPass {
    static char ID;
    EnableFunctionOptPass():FunctionPass(ID){}
    bool runOnFunction(Function & F) override{
        if(F.hasFnAttribute(Attribute::OptimizeNone))
        {
            F.removeFnAttr(Attribute::OptimizeNone);
        }
        return true;
    }
};

char EnableFunctionOptPass::ID=0;

// Merge s2 to s1.
template<typename T>
void mergeSet(std::set<T>& s1, const std::set<T> s2) {
    s1.insert(s2.begin(), s2.end());
}

struct FuncPtrPass : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    FuncPtrPass() : ModulePass(ID) {}
    std::map<Value*, std::vector<Use*>> argTable;

    // Get function call recursively from the variable used by it.
    std::set<Function*> getFunctions(Use& use) {
        std::set<Function*> funcSet;
        // For trivial function, add it to set. 
        if (auto f = dyn_cast<Function>(use)) {
            funcSet.insert(f);
        }
        // For phi inst, union all functions of its possible values.
        else if (auto phi = dyn_cast<PHINode>(use)) {
            for (auto& subUse : phi->incoming_values()) {
                mergeSet<Function*>(funcSet, getFunctions(subUse));
            }
        }
        // For call inst, get functions from its return values. 
        else if (auto call = dyn_cast<CallInst>(use)) {
            // Case 1: The call inst is a trivial function.
            if (auto func = call->getCalledFunction()) {
                mergeSet<Function*>(funcSet, getFunctionsFromRetVal(func));
            }
            // Case 2: The call inst is a function pointer.
            else {
                for (auto& func : getFunctions(call->getCalledOperandUse())) {
                    mergeSet<Function*>(funcSet, getFunctionsFromRetVal(func));
                }
            }
        }
        // For formal args, union all the actual args of the function.
        else if (argTable.count(use)) {
            for (auto subUse : argTable[use]) {
                mergeSet<Function*>(funcSet, getFunctions(*subUse));
            }
        }
        return funcSet;
    }

    // Get all functions used from return values of `func`.
    std::set<Function*> getFunctionsFromRetVal(Function* func) {
        std::set<Function*> funcSet;
        for (auto block = func->begin(); block != func->end(); ++block) {
            for (auto inst = block->begin(); inst != block->end(); ++inst) {
                if (auto ret = dyn_cast<ReturnInst>(inst)) {
                    for (auto& subUse : ret->getReturnValue()->uses()) {
                        mergeSet<Function*>(funcSet, getFunctions(subUse));
                    }
                }
            }
        }
        return funcSet;
    }

    // Get all calls of function or function pointer `user`. 
    std::set<CallInst*> getFuncCallUser(User* user) {
        std::set<CallInst*> callSet;
        if (auto call = dyn_cast<CallInst>(user)) {
            callSet.insert(call);
        }
        else {
            for (auto subUser : user->users()) {
                mergeSet<CallInst*>(callSet, getFuncCallUser(subUser));
            }
        }
        return callSet;
    }

    // Get map from formalArgs to actualArgs. 
    void getArgTable(Module& M) {
        for (auto func = M.begin(); func != M.end(); ++func) {
            for (auto user : func->users()) {
                auto callSet = getFuncCallUser(user);
                for (auto call : callSet) {
                    auto formalArg = func->arg_begin();
                    auto actualArg = call->arg_begin();
                    while (formalArg != func->arg_end() && actualArg != call->arg_end()) {
                        auto formalArgsName = formalArg->getName().str();
                        if (argTable.count(formalArg)) {
                            argTable[formalArg].push_back(actualArg); 
                        }
                        else {
                            argTable[formalArg] = {actualArg};
                        }
                        ++formalArg;
                        ++actualArg;
                    }
                }
            }
        }
    }

    // Travel all functions to output their calls.
    bool runOnModule(Module &M) override {
        getArgTable(M);
        for (auto func = M.begin(); func != M.end(); ++func) {
            for (auto block = func->begin(); block != func->end(); ++block) {
                for (auto inst = block->begin(); inst != block->end(); ++inst) {
                    if (auto call = dyn_cast<CallInst>(inst)) {
                        // For trivial functions. 
                        if (call->getCalledFunction()) {
                            auto name = call->getCalledFunction()->getName();
                            if (name != "llvm.dbg.value") {
                                errs() << call->getDebugLoc().getLine() << " : ";
                                errs() << call->getCalledFunction()->getName() << "\n";
                            }
                        }
                        // For function pointers. 
                        else {
                            Use& use = call->getCalledOperandUse();
                            auto funcSet = getFunctions(use);
                            assert(funcSet.size() != 0);
                            errs() << call->getDebugLoc().getLine() << " : ";
                            auto it = funcSet.begin();
                            errs() << (*it++)->getName();
                            while (it != funcSet.end()) {
                                errs() << ", " << (*it++)->getName();
                            }
                            errs() << "\n";
                        }
                    }
                }
            }
        }
        return false;
    }
};


char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass", "Print function call instruction");

static cl::opt<std::string>
InputFilename(cl::Positional,
        cl::desc("<filename>.bc"),
        cl::init(""));


int main(int argc, char **argv) {
    LLVMContext &Context = getGlobalContext();
    SMDiagnostic Err;
    // Parse the command line to read the Inputfilename
    cl::ParseCommandLineOptions(argc, argv,
            "FuncPtrPass \n My first LLVM too which does not do much.\n");


    // Load the input module
    std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
    if (!M) {
        Err.print(argv[0], errs());
        return 1;
    }

    llvm::legacy::PassManager Passes;

    ///Remove functions' optnone attribute in LLVM5.0
    Passes.add(new EnableFunctionOptPass());
    ///Transform it to SSA
    Passes.add(llvm::createPromoteMemoryToRegisterPass());

    /// Your pass to print Function and Call Instructions
    Passes.add(new FuncPtrPass());
    Passes.run(*M.get());
}

