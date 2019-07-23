//===-- EmitAnnotations.h - Emit Annotations Pass -----*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file emits function annotations
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_UTILS_EMIT_ANNOTATIONS_H
#define LLVM_TRANSFORMS_UTILS_EMIT_ANNOTATIONS_H

#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"

namespace llvm {

/// Simple pass that canonicalizes aliases.
class EmitAnnotationsPass : public PassInfoMixin<EmitAnnotationsPass> {
public:
  EmitAnnotationsPass() = default;

  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FM);
};

} // end namespace llvm

#endif // LLVM_TRANSFORMS_UTILS_EMIT_ANNOTATIONS_H
