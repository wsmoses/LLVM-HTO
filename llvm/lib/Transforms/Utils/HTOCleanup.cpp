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
#include "llvm/Transforms/Utils/HTOCleanup.h"

using namespace llvm;

#define DEBUG_TYPE "hto-cleanup"

#include <map>
#include <vector>
using namespace std;

void HTOFixup(Module &M) {
    //llvm::errs() << "running hto fixup\n";
    std::vector<GlobalVariable*> erase;
    for(auto &g : M.globals()) {
        if (g.getName().startswith("__hto_global")) {
            erase.push_back(&g);
        }
    }
    for(auto g : erase) {
        //llvm::errs() << " erasing " << *g << "\n";
        g->eraseFromParent();
    }
}

namespace llvm {

struct HTOCleanupLegacyPass : public ModulePass {
  // Pass identification, replacement for typeid
  static char ID;

  HTOCleanupLegacyPass() : ModulePass(ID) {
    initializeHTOCleanupLegacyPassPass(*PassRegistry::getPassRegistry());
  }

  // runOnFunction - To run this pass, first we calculate the alloca
  // instructions that are safe for promotion, then we promote each one.
  bool runOnModule(Module &M) override {
    HTOFixup(M);
    return false;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
  }
};

} // end anonymous namespace

char HTOCleanupLegacyPass::ID = 0;

PreservedAnalyses HTOCleanupPass::run(Module &M,
                                               ModuleAnalysisManager &FM) {
  HTOFixup(M);
  return PreservedAnalyses::all();
}

INITIALIZE_PASS_BEGIN(HTOCleanupLegacyPass, "hto-cleanup", "Cleanup HTO pieces", 
                      false, false)
INITIALIZE_PASS_END(HTOCleanupLegacyPass, "hto-cleanup", "Cleanup HTO pieces", 
                    false, false)

ModulePass *llvm::createHTOCleanupPass() {
  return new HTOCleanupLegacyPass();
}
