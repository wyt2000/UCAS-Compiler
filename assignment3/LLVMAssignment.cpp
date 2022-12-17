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

#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/ToolOutputFile.h>

#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>


#include <llvm/Transforms/Utils.h>
#include <llvm/Transforms/Scalar.h>

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>

#include "Liveness.h"
using namespace llvm;
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }

struct EnableFunctionOptPass : public FunctionPass {
    static char ID;
    EnableFunctionOptPass() :FunctionPass(ID) {}
    bool runOnFunction(Function & F) override {
        if (F.hasFnAttribute(Attribute::OptimizeNone))
        {
            F.removeFnAttr(Attribute::OptimizeNone);
        }
        return true;
    }
};

char EnableFunctionOptPass::ID = 0;

// Merge s2 to s1.
template<typename T>
void mergeSet(std::set<T>& s1, const std::set<T> s2) {
    s1.insert(s2.begin(), s2.end());
}

struct FuncPtrSet {
    std::map<BasicBlock*, std::map<Value*, std::set<Use*>>> in, out;
    bool operator == (const FuncPtrSet& s) const {
        auto o = s.out;
        for (auto item : out) {
            if (!o.count(item.first)) {
                return false;
            }
            if (o[item.first] != item.second) {
                return false;
            }
        }
        return true;
    }
};

struct FuncPtrPass : public ModulePass {
    using FuncCallTableType = std::map<CallInst*, std::set<Function*>, bool(*)(CallInst*, CallInst*)>;
    static char ID; // Pass identification, replacement for typeid
    FuncPtrPass() : ModulePass(ID) {
        // Sort results by row number.
        funcCallTable = FuncCallTableType([](CallInst* p, CallInst *q) {
            if (!p) return true;
            if (!q) return false;
            return p->getDebugLoc().getLine() < q->getDebugLoc().getLine();
        });
    }
    std::map<Value*, std::set<Use*>> argTable;
    FuncCallTableType funcCallTable;
    std::stack<std::pair<CallInst*, Function*>> callStack;
    std::map<std::pair<Value*, unsigned>, std::set<Use*>> GEPTable;
    std::map<Function*, FuncPtrSet> funcPtrTable;

    void printFuncPtrSet(FuncPtrSet s) {
        for (auto item : s.out) {
            item.first->dump();
            for (auto p : item.second) {
                if (auto inst = dyn_cast<Instruction>(p.first)) {
                    inst->dump();
                }
                for (auto f : p.second) {
                    outs() << f->get()->getName() << " ";
                }
                outs() << "\n";
            }
        }
    }

    void getFuncPtrTable(Module& M) {
        for (auto func = M.begin(); func != M.end(); ++func) {
            FuncPtrSet funcPtrSet;
            for (auto block = func->begin(); block != func->end(); ++block) {
                auto bb = &*block;
                funcPtrSet.in[bb] = std::map<Value*, std::set<Use*>>();
                funcPtrSet.out[bb] = std::map<Value*, std::set<Use*>>();
            }
            while (true) {
                auto oldFuncPtrSet = funcPtrSet;
                for (auto block = func->begin(); block != func->end(); ++block) {
                    std::map<Value*, std::set<Use*>> myPtrSet;
                    auto bb = &*block;
                    for (auto it = pred_begin(bb); it != pred_end(bb); ++it) {
                        auto pred = *it;
                        for (auto item : funcPtrSet.out[pred]) {
                            auto inst = item.first;
                            auto funcSet = item.second;
                            if (myPtrSet.count(inst)) {
                                myPtrSet[inst].insert(funcSet.begin(), funcSet.end());
                            }
                            else {
                                myPtrSet[inst] = funcSet;
                            }
                        }
                    }
                    funcPtrSet.in[bb] = myPtrSet;
                    for (auto inst = block->begin(); inst != block->end(); ++inst) {
                        if (auto store = dyn_cast<StoreInst>(inst)) {
                            if (auto bitcast = dyn_cast<BitCastInst>(store->getOperand(1))) {
                                auto target = bitcast->getOperand(0);
                                myPtrSet[target] = {&store->getOperandUse(0)};
                            }
                            else if (auto getElemPtr = dyn_cast<GetElementPtrInst>(store->getOperand(1))) {
                                auto target = getElemPtr->getOperand(0);
                                myPtrSet[target] = {&store->getOperandUse(0)};
                            }
                        }
                    }
                    funcPtrSet.out[bb] = myPtrSet;
                }
                if (oldFuncPtrSet == funcPtrSet) {
                    break;
                }
            }
            funcPtrTable[&*func] = funcPtrSet;
            //printFuncPtrSet(funcPtrSet);
        }
    }

    std::set<Function*> getFunctionsFromPtr(Instruction* inst) {
        Value* target = nullptr;
        if (auto bitcast = dyn_cast<BitCastInst>(inst->getOperand(0))) {
            target = bitcast->getOperand(0);
        }
        else if (auto getElemPtr = dyn_cast<GetElementPtrInst>(inst->getOperand(0))) {
            target = getElemPtr->getOperand(0);
        }
        else {
            assert(0);
        }
        std::set<Function*> funcSet;
        auto bb = inst->getParent();
        auto func = bb->getParent();
        auto in = funcPtrTable[func].in[bb];
        if (in.count(target)) {
            for (auto use : in[target]) {
                mergeSet<Function*>(funcSet, getFunctions(*use));
            }
        }
        for (auto it = bb->begin(); it != bb->end(); ++it) {
            if (&*it == inst) break;
            if (auto store = dyn_cast<StoreInst>(it)) {
                if (auto bitcast = dyn_cast<BitCastInst>(store->getOperand(1))) {
                    auto value = bitcast->getOperand(0);
                    if (value == target) {
                        funcSet = {getFunctions(store->getOperandUse(0))};
                    }
                }
                else if (auto getElemPtr = dyn_cast<GetElementPtrInst>(store->getOperand(1))) {
                    auto value = getElemPtr->getOperand(0);
                    if (value == target) {
                        funcSet = {getFunctions(store->getOperandUse(0))};
                    }
                }
            }
        } 
        return funcSet;
    }
            

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
                callStack.push({call, func});
                mergeSet<Function*>(funcSet, getFunctionsFromRetVal(call, func));
                callStack.pop();
            }
            // Case 2: The call inst is a function pointer.
            else {
                for (auto& func : getFunctions(call->getCalledOperandUse())) {
                    callStack.push({call, func});
                    mergeSet<Function*>(funcSet, getFunctionsFromRetVal(call, func));
                    callStack.pop();
                }
            }
        }
        // For formal args.
        else if (argTable.count(use)) {
            // Case 1: Outside of calling, just look up from arg table to find all calling points.
            if (callStack.empty()) {
                for (auto subUse : argTable[use]) {
                    mergeSet<Function*>(funcSet, getFunctions(*subUse));
                }
            } 
            // Case 2: Called by other function, compare with the formal args.
            else {
                auto call = callStack.top().first;
                auto func = callStack.top().second;
                auto formalArg = func->arg_begin();
                auto actualArg = call->arg_begin();
                while (formalArg != func->arg_end() && actualArg != call->arg_end()) {
                    if (use == formalArg) {
                        callStack.pop();
                        mergeSet<Function*>(funcSet, getFunctions(*actualArg));
                        callStack.push({call, func});
                        break;
                    }
                    ++formalArg;
                    ++actualArg;
                }
            }
        }
        // For load instr. 
        else if (auto load = dyn_cast<LoadInst>(use)) {
            if (auto bitcast = dyn_cast<BitCastInst>(load->getOperand(0))) {
                mergeSet<Function*>(funcSet, getFunctionsFromPtr(load));
            }
            else if (auto getElemPtr = dyn_cast<GetElementPtrInst>(load->getOperand(0))) {
                mergeSet<Function*>(funcSet, getFunctionsFromPtr(load));
            }
            else {
                mergeSet<Function*>(funcSet, getFunctions(load->getOperandUse(0)));
            }
        }
        //else {
        //    use->dump();
        //}
        return funcSet;
    }

    // Get all functions used from return values of `func`.
    std::set<Function*> getFunctionsFromRetVal(CallInst* call, Function* func) {
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

    // Update map from formalArgs to actualArgs. 
    void updateArgTable(Function* func, CallInst* call) {
        assert(func->arg_size() == call->arg_size());
        auto formalArg = func->arg_begin();
        auto actualArg = call->arg_begin();
        while (formalArg != func->arg_end() && actualArg != call->arg_end()) {
            if (!argTable.count(formalArg)) {
                argTable[formalArg] = {};
            }
            argTable[formalArg].insert(actualArg);
            ++formalArg;
            ++actualArg;
        }
    }

    // Filter func calls which needn't to be printed.
    bool needToOutput(CallInst* call) {
        auto func = call->getCalledFunction();
        auto name = func->getName();
        if (name == "llvm.dbg.value") {
            return false;
        }
        if (name == "llvm.dbg.declare") {
            return false;
        }
        if (auto memset = dyn_cast<MemSetInst>(call)) {
            return false;
        }
        return true;
    }

    // Travel all functions to output their calls.
    bool runOnModule(Module &M) override {
        getFuncPtrTable(M);
        // Iter all calls until no change.
        while (true) {
            auto oldFuncCallTable = funcCallTable;
            for (auto func = M.begin(); func != M.end(); ++func) {
                for (auto block = func->begin(); block != func->end(); ++block) {
                    for (auto inst = block->begin(); inst != block->end(); ++inst) {
                        if (auto call = dyn_cast<CallInst>(inst)) {
                            // For trivial functions. 
                            if (auto calledFunc = call->getCalledFunction()) {
                                if (needToOutput(call)) {
                                    if (!funcCallTable.count(call)) {
                                        funcCallTable[call] = {};
                                    }
                                    funcCallTable[call].insert(calledFunc);
                                    updateArgTable(calledFunc, call);
                                }
                            }
                            // For function pointers. 
                            else {
                                Use& use = call->getCalledOperandUse();
                                auto funcSet = getFunctions(use);
                                if (!funcCallTable.count(call)) {
                                    funcCallTable[call] = {};
                                }
                                for (auto calledFunc : funcSet) {
                                    funcCallTable[call].insert(calledFunc);
                                    updateArgTable(calledFunc, call);
                                }
                            }
                        }
                    }
                }
            }
            // Output results.
            if (funcCallTable == oldFuncCallTable) {
                for (auto funcCall : funcCallTable) {
                    auto call = funcCall.first; 
                    auto funcSet = funcCall.second;
                    assert(funcSet.size() != 0);
                    errs() << call->getDebugLoc().getLine() << " : ";
                    auto it = funcSet.begin();
                    errs() << (*it++)->getName();
                    while (it != funcSet.end()) {
                        errs() << ", " << (*it++)->getName();
                    }
                    errs() << "\n";
                }
                break;
            }
        }
        return false;
    }
};


char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass", "Print function call instruction");

char Liveness::ID = 0;
static RegisterPass<Liveness> Y("liveness", "Liveness Dataflow Analysis");

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
//#if LLVM_VERSION_MAJOR == 5
   Passes.add(new EnableFunctionOptPass());
//#endif
   ///Transform it to SSA
   Passes.add(llvm::createPromoteMemoryToRegisterPass());

   /// Your pass to print Function and Call Instructions
   //Passes.add(new Liveness());
   Passes.add(new FuncPtrPass());
   Passes.run(*M.get());
#ifndef NDEBUG
   //system("pause");
#endif
}

