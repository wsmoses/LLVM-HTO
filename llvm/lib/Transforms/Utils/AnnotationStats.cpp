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
#include "llvm/Pass.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/AnnotationStats.h"
#include "llvm/InitializePasses.h"

using namespace llvm;

#define DEBUG_TYPE "annotation-stats"

#include <map>
using namespace std;

static bool ignoreStringAttributes = true;
void AnnotationStats(Module &M) {
    std::map<std::string, std::map<std::string, int>> attrs;

    for (Function &F : M) {
        AttributeList list = F.getAttributes();
        for(auto a : list.getFnAttributes()) {
            if (ignoreStringAttributes && a.isStringAttribute()) continue;
            attrs[a.getAsString(true)][""]++;
            //attrs[a.getKindAsString().str()][a.getValueAsString().str()]++;
        }
        
        for(unsigned i=0; i<F.getFunctionType()->getNumParams(); i++) {
            for(auto a : list.getParamAttributes(i)) {
                if (ignoreStringAttributes && a.isStringAttribute()) continue; 
                attrs[a.getAsString(true)][""]++;
                //attrs[a.getKindAsString().str()][a.getValueAsString().str()]++;
            }
        }

        for(auto a : list.getRetAttributes()) {
            if (ignoreStringAttributes && a.isStringAttribute()) continue; 
            attrs[a.getAsString(true)][""]++;
            //attrs[a.getKindAsString().str()][a.getValueAsString().str()]++;
        }
    }

    for(auto pair : attrs) {
        for(auto pair2 : pair.second) {
            llvm::errs() << pair.first << " | " << pair2.second << "\n";
            //llvm::errs() << pair.first << "=" << pair2.first << " | " << pair2.second << "\n";
        }
    }
}

namespace llvm {

struct AnnotationStatsLegacyPass : public ModulePass {
  // Pass identification, replacement for typeid
  static char ID;

  AnnotationStatsLegacyPass() : ModulePass(ID) {
    initializeAnnotationStatsLegacyPassPass(*PassRegistry::getPassRegistry());
  }

  // runOnFunction - To run this pass, first we calculate the alloca
  // instructions that are safe for promotion, then we promote each one.
  bool runOnModule(Module &M) override {
    AnnotationStats(M);
    return false;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
  }
};

} // end anonymous namespace

char AnnotationStatsLegacyPass::ID = 0;

PreservedAnalyses AnnotationStatsPass::run(Module &M,
                                               ModuleAnalysisManager &FM) {
  AnnotationStats(M);
  return PreservedAnalyses::all();
}

INITIALIZE_PASS_BEGIN(AnnotationStatsLegacyPass, "annotation-stats", "Emit annotation statistics", 
                      false, false)
INITIALIZE_PASS_END(AnnotationStatsLegacyPass, "annotation-stats", "Emit annotation statistics", 
                    false, false)

ModulePass *llvm::createAnnotationStatsPass() {
  return new AnnotationStatsLegacyPass();
}
