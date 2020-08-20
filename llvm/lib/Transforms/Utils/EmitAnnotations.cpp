//===-- UnrollLoop.cpp - Loop unrolling utilities -------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements some loop unrolling utilities. It does not define any
// actual pass or policy, but provides a single function to perform loop
// unrolling.
//
// The process of unrolling can produce extraneous basic blocks linked with
// unconditional branches.  This will be corrected in the future.
//
//===----------------------------------------------------------------------===//

#include <string>
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Pass.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/EmitAnnotations.h"
#include "llvm/InitializePasses.h"

using namespace llvm;

llvm::cl::opt<bool> ignoreStringAttributes("hto_nostring", cl::init(false), cl::Hidden,
                cl::desc("Don't print string attributes"));

#define DEBUG_TYPE "emit-annotations"

std::string fixQuotes(std::string str) {
    str.erase(std::remove(str.begin(), str.end(), '"'), str.end());
    return '"' + str + '"';
}

void EmitAnnotations(Function *F, OptimizationRemarkEmitter &ORE) {
        OptimizationRemarkAnnotation annotations(DEBUG_TYPE, "annotation ", F);
        AttributeList list = F->getAttributes();
        bool prev = false;
        if (F->hasPrivateLinkage() || F->hasInternalLinkage()) return;
        if (F->getName() == "main") return;
	if (list.hasFnAttribute("nohto")) return;
	for(auto a : list.getFnAttributes()) {
            if (ignoreStringAttributes && a.isStringAttribute()) continue; 
            if (prev) annotations << ",";
            prev = true;
            annotations << "fn_attr(" << fixQuotes(a.getAsString(true)) << ") ";
        }
        bool structreturn = false;
        unsigned j = 0;
        for(unsigned i=0; i<F->getFunctionType()->getNumParams(); i++) {
            if (list.hasParamAttribute(i, Attribute::StructRet)) {
                assert(structreturn == false);
                structreturn = true;
                /*
                for(auto a : list.getParamAttributes(i)) {
                  if (a == Attribute::StructReturn) continue;
                  if (prev) annotations << ",";
                  prev = true;
                  annotations << "ret_attr(" << fixQuotes(a.getAsString(true)) << ") ";
                }
                */
            } else {
                for(auto a : list.getParamAttributes(i)) {
                  if (ignoreStringAttributes && a.isStringAttribute()) continue; 
                  if (prev) annotations << ",";
                  prev = true;
                  annotations << "arg_attr(" << std::to_string(j+1) << ", " << fixQuotes(a.getAsString(true)) << ") ";
                }
                j++;
            }
        }
        for(auto a : list.getRetAttributes()) {
            assert(structreturn == false);
            if (ignoreStringAttributes && a.isStringAttribute()) continue; 
            if (prev) annotations << ",";
            prev = true;
            annotations << "ret_attr(" << fixQuotes(a.getAsString(true)) << ") ";
        }
        annotations << "\n";
      //llvm::errs() << "considering emmitting annotation for prev: " << prev << " F:"  << *F << "\n";
      if (prev) {
        ORE.emit(annotations);
      }
}

namespace llvm {

struct EmitAnnotationsLegacyPass : public FunctionPass {
  // Pass identification, replacement for typeid
  static char ID;

  EmitAnnotationsLegacyPass() : FunctionPass(ID) {
    initializeEmitAnnotationsLegacyPassPass(*PassRegistry::getPassRegistry());
  }

  // runOnFunction - To run this pass, first we calculate the alloca
  // instructions that are safe for promotion, then we promote each one.
  bool runOnFunction(Function &F) override {
    OptimizationRemarkEmitter &ORE = getAnalysis<OptimizationRemarkEmitterWrapperPass>().getORE();
    EmitAnnotations(&F, ORE);
    return false;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<OptimizationRemarkEmitterWrapperPass>();
    AU.setPreservesCFG();
  }
};

} // end anonymous namespace

char EmitAnnotationsLegacyPass::ID = 0;

PreservedAnalyses EmitAnnotationsPass::run(Function &F,
                                               FunctionAnalysisManager &FM) {
  OptimizationRemarkEmitter &ORE = FM.getResult<OptimizationRemarkEmitterAnalysis>(F);
  EmitAnnotations(&F, ORE);
  return PreservedAnalyses::all();
}

INITIALIZE_PASS_BEGIN(EmitAnnotationsLegacyPass, "emit-annotation", "Emit annotations", 
                      false, false)
INITIALIZE_PASS_DEPENDENCY(OptimizationRemarkEmitterWrapperPass)
INITIALIZE_PASS_END(EmitAnnotationsLegacyPass, "emit-annotation", "Emit annotations", 
                    false, false)

FunctionPass *llvm::createEmitAnnotationsPass() {
  return new EmitAnnotationsLegacyPass();
}
