//===-- CodeTemplate.h ------------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// A set of structures and functions to craft instructions for the
/// SnippetGenerator.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_TOOLS_LLVM_EXEGESIS_CODETEMPLATE_H
#define LLVM_TOOLS_LLVM_EXEGESIS_CODETEMPLATE_H

#include "MCInstrDescView.h"
#include "llvm/ADT/BitmaskEnum.h"

namespace llvm {
namespace exegesis {

// A template for an Instruction holding values for each of its Variables.
struct InstructionTemplate {
  InstructionTemplate(const Instruction &Instr);

  InstructionTemplate(const InstructionTemplate &);            // default
  InstructionTemplate &operator=(const InstructionTemplate &); // default
  InstructionTemplate(InstructionTemplate &&);                 // default
  InstructionTemplate &operator=(InstructionTemplate &&);      // default

  unsigned getOpcode() const;
  llvm::MCOperand &getValueFor(const Variable &Var);
  const llvm::MCOperand &getValueFor(const Variable &Var) const;
  llvm::MCOperand &getValueFor(const Operand &Op);
  const llvm::MCOperand &getValueFor(const Operand &Op) const;
  bool hasImmediateVariables() const;

  // Builds an llvm::MCInst from this InstructionTemplate setting its operands
  // to the corresponding variable values. Precondition: All VariableValues must
  // be set.
  llvm::MCInst build() const;

  Instruction Instr;
  llvm::SmallVector<llvm::MCOperand, 4> VariableValues;
};

enum class ExecutionMode : uint8_t {
  UNKNOWN = 0U,
  // The instruction is always serial because implicit Use and Def alias.
  // e.g. AAA (alias via EFLAGS)
  ALWAYS_SERIAL_IMPLICIT_REGS_ALIAS = 1u << 0,

  // The instruction is always serial because one Def is tied to a Use.
  // e.g. AND32ri (alias via tied GR32)
  ALWAYS_SERIAL_TIED_REGS_ALIAS = 1u << 1,

  // The execution can be made serial by inserting a second instruction that
  // clobbers/reads memory.
  // e.g. MOV8rm
  SERIAL_VIA_MEMORY_INSTR = 1u << 2,

  // The execution can be made serial by picking one Def that aliases with one
  // Use.
  // e.g. VXORPSrr XMM1, XMM1, XMM2
  SERIAL_VIA_EXPLICIT_REGS = 1u << 3,

  // The execution can be made serial by inserting a second instruction that
  // uses one of the Defs and defs one of the Uses.
  // e.g.
  // 1st instruction: MMX_PMOVMSKBrr ECX, MM7
  // 2nd instruction: MMX_MOVD64rr MM7, ECX
  //  or instruction: MMX_MOVD64to64rr MM7, ECX
  //  or instruction: MMX_PINSRWrr MM7, MM7, ECX, 1
  SERIAL_VIA_NON_MEMORY_INSTR = 1u << 4,

  // The execution is always parallel because the instruction is missing Use or
  // Def operands.
  ALWAYS_PARALLEL_MISSING_USE_OR_DEF = 1u << 5,

  // The execution can be made parallel by repeating the same instruction but
  // making sure that Defs of one instruction do not alias with Uses of the
  // second one.
  PARALLEL_VIA_EXPLICIT_REGS = 1u << 6,

  LLVM_MARK_AS_BITMASK_ENUM(/*Largest*/ PARALLEL_VIA_EXPLICIT_REGS)
};

// Returns whether Execution is one of the values defined in the enum above.
bool isEnumValue(ExecutionMode Execution);

// Returns a human readable string for the enum.
llvm::StringRef getName(ExecutionMode Execution);

// Returns a sequence of increasing powers of two corresponding to all the
// Execution flags.
llvm::ArrayRef<ExecutionMode> getAllExecutionBits();

// Decomposes Execution into individual set bits.
llvm::SmallVector<ExecutionMode, 4> getExecutionModeBits(ExecutionMode);

LLVM_ENABLE_BITMASK_ENUMS_IN_NAMESPACE();

// A CodeTemplate is a set of InstructionTemplates that may not be fully
// specified (i.e. some variables are not yet set). This allows the
// SnippetGenerator to instantiate it many times with specific values to study
// their impact on instruction's performance.
struct CodeTemplate {
  CodeTemplate() = default;

  CodeTemplate(CodeTemplate &&);            // default
  CodeTemplate &operator=(CodeTemplate &&); // default
  CodeTemplate(const CodeTemplate &) = delete;
  CodeTemplate &operator=(const CodeTemplate &) = delete;

  ExecutionMode Execution = ExecutionMode::UNKNOWN;
  // See InstructionBenchmarkKey.::Config.
  std::string Config;
  // Some information about how this template has been created.
  std::string Info;
  // The list of the instructions for this template.
  std::vector<InstructionTemplate> Instructions;
  // If the template uses the provided scratch memory, the register in which
  // the pointer to this memory is passed in to the function.
  unsigned ScratchSpacePointerInReg = 0;
};

} // namespace exegesis
} // namespace llvm

#endif // LLVM_TOOLS_LLVM_EXEGESIS_CODETEMPLATE_H
