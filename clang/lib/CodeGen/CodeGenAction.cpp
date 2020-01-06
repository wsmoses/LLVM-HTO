//===--- CodeGenAction.cpp - LLVM Code Generation Frontend Action ---------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "clang/CodeGen/CodeGenAction.h"
#include "CodeGenModule.h"
#include "CoverageMappingGen.h"
#include "MacroPPCallbacks.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclGroup.h"
#include "clang/Basic/DiagnosticFrontend.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/LangStandard.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/CodeGen/BackendUtil.h"
#include "clang/CodeGen/ModuleBuilder.h"
#include "clang/Driver/DriverDiagnostic.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendDiagnostic.h"
#include "clang/Lex/Preprocessor.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/CodeGen/MachineOptimizationRemarkEmitter.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/DiagnosticPrinter.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LLVMRemarkStreamer.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Linker/Linker.h"
#include "llvm/Pass.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/TimeProfiler.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/YAMLTraits.h"
#include "llvm/Transforms/IPO/Internalize.h"

#include <memory>
using namespace clang;
using namespace llvm;

namespace clang {
  class BackendConsumer;
  class ClangDiagnosticHandler final : public DiagnosticHandler {
  public:
    ClangDiagnosticHandler(const CodeGenOptions &CGOpts, BackendConsumer *BCon)
        : CodeGenOpts(CGOpts), BackendCon(BCon) {}

    bool handleDiagnostics(const DiagnosticInfo &DI) override;

    bool isAnalysisRemarkEnabled(StringRef PassName) const override {
      return (CodeGenOpts.OptimizationRemarkAnalysisPattern &&
              CodeGenOpts.OptimizationRemarkAnalysisPattern->match(PassName));
    }
    bool isMissedOptRemarkEnabled(StringRef PassName) const override {
      return (CodeGenOpts.OptimizationRemarkMissedPattern &&
              CodeGenOpts.OptimizationRemarkMissedPattern->match(PassName));
    }
    bool isPassedOptRemarkEnabled(StringRef PassName) const override {
      return (CodeGenOpts.OptimizationRemarkPattern &&
              CodeGenOpts.OptimizationRemarkPattern->match(PassName));
    }

    bool isAnyRemarkEnabled() const override {
      return (CodeGenOpts.OptimizationRemarkAnalysisPattern ||
              CodeGenOpts.OptimizationRemarkMissedPattern ||
              CodeGenOpts.OptimizationRemarkPattern);
    }

  private:
    const CodeGenOptions &CodeGenOpts;
    BackendConsumer *BackendCon;
  };

  static void reportOptRecordError(Error E, DiagnosticsEngine &Diags,
                                   const CodeGenOptions CodeGenOpts) {
    handleAllErrors(
        std::move(E),
      [&](const LLVMRemarkSetupFileError &E) {
          Diags.Report(diag::err_cannot_open_file)
              << CodeGenOpts.OptRecordFile << E.message();
        },
      [&](const LLVMRemarkSetupPatternError &E) {
          Diags.Report(diag::err_drv_optimization_remark_pattern)
              << E.message() << CodeGenOpts.OptRecordPasses;
        },
      [&](const LLVMRemarkSetupFormatError &E) {
          Diags.Report(diag::err_drv_optimization_remark_format)
              << CodeGenOpts.OptRecordFormat;
        });
    }

  class BackendConsumer : public ASTConsumer {
    using LinkModule = CodeGenAction::LinkModule;

    virtual void anchor();
    DiagnosticsEngine &Diags;
    BackendAction Action;
    const HeaderSearchOptions &HeaderSearchOpts;
    const CodeGenOptions &CodeGenOpts;
    const TargetOptions &TargetOpts;
    const LangOptions &LangOpts;
    std::unique_ptr<raw_pwrite_stream> AsmOutStream;
    ASTContext *Context;

    Timer LLVMIRGeneration;
    unsigned LLVMIRGenerationRefCount;

    /// True if we've finished generating IR. This prevents us from generating
    /// additional LLVM IR after emitting output in HandleTranslationUnit. This
    /// can happen when Clang plugins trigger additional AST deserialization.
    bool IRGenFinished = false;

    std::unique_ptr<CodeGenerator> Gen;

    SmallVector<LinkModule, 4> LinkModules;

    // This is here so that the diagnostic printer knows the module a diagnostic
    // refers to.
    llvm::Module *CurLinkModule = nullptr;
    CompilerInstance *CI;
  public:
    BackendConsumer(BackendAction Action, DiagnosticsEngine &Diags,
                    const HeaderSearchOptions &HeaderSearchOpts,
                    const PreprocessorOptions &PPOpts,
                    const CodeGenOptions &CodeGenOpts,
                    const TargetOptions &TargetOpts,
                    const LangOptions &LangOpts, bool TimePasses,
                    const std::string &InFile,
                    SmallVector<LinkModule, 4> LinkModules,
                    std::unique_ptr<raw_pwrite_stream> OS, LLVMContext &C,
                    CoverageSourceInfo *CoverageInfo = nullptr, CompilerInstance *_CI = nullptr)
        : Diags(Diags), Action(Action), HeaderSearchOpts(HeaderSearchOpts),
          CodeGenOpts(CodeGenOpts), TargetOpts(TargetOpts), LangOpts(LangOpts),
          AsmOutStream(std::move(OS)), Context(nullptr),
          LLVMIRGeneration("irgen", "LLVM IR Generation Time"),
          LLVMIRGenerationRefCount(0),
          Gen(CreateLLVMCodeGen(Diags, InFile, HeaderSearchOpts, PPOpts,
                                CodeGenOpts, C, CoverageInfo)),
          LinkModules(std::move(LinkModules)), CI(_CI) {
      FrontendTimesIsEnabled = TimePasses;
      llvm::TimePassesIsEnabled = TimePasses;
    }

    // This constructor is used in installing an empty BackendConsumer
    // to use the clang diagnostic handler for IR input files. It avoids
    // initializing the OS field.
    BackendConsumer(BackendAction Action, DiagnosticsEngine &Diags,
                    const HeaderSearchOptions &HeaderSearchOpts,
                    const PreprocessorOptions &PPOpts,
                    const CodeGenOptions &CodeGenOpts,
                    const TargetOptions &TargetOpts,
                    const LangOptions &LangOpts, bool TimePasses,
                    SmallVector<LinkModule, 4> LinkModules, LLVMContext &C,
                    CoverageSourceInfo *CoverageInfo = nullptr)
        : Diags(Diags), Action(Action), HeaderSearchOpts(HeaderSearchOpts),
          CodeGenOpts(CodeGenOpts), TargetOpts(TargetOpts), LangOpts(LangOpts),
          Context(nullptr),
          LLVMIRGeneration("irgen", "LLVM IR Generation Time"),
          LLVMIRGenerationRefCount(0),
          Gen(CreateLLVMCodeGen(Diags, "", HeaderSearchOpts, PPOpts,
                                CodeGenOpts, C, CoverageInfo)),
          LinkModules(std::move(LinkModules)) {
      FrontendTimesIsEnabled = TimePasses;
      llvm::TimePassesIsEnabled = TimePasses;
    }
    llvm::Module *getModule() const { return Gen->GetModule(); }
    std::unique_ptr<llvm::Module> takeModule() {
      return std::unique_ptr<llvm::Module>(Gen->ReleaseModule());
    }

    CodeGenerator *getCodeGenerator() { return Gen.get(); }

    void HandleCXXStaticMemberVarInstantiation(VarDecl *VD) override {
      Gen->HandleCXXStaticMemberVarInstantiation(VD);
    }

    void Initialize(ASTContext &Ctx) override {
      assert(!Context && "initialized multiple times");

      Context = &Ctx;

      if (FrontendTimesIsEnabled)
        LLVMIRGeneration.startTimer();

      Gen->Initialize(Ctx);

      if (FrontendTimesIsEnabled)
        LLVMIRGeneration.stopTimer();
    }

    bool HandleTopLevelDecl(DeclGroupRef D) override {
      PrettyStackTraceDecl CrashInfo(*D.begin(), SourceLocation(),
                                     Context->getSourceManager(),
                                     "LLVM IR generation of declaration");

      // Recurse.
      if (FrontendTimesIsEnabled) {
        LLVMIRGenerationRefCount += 1;
        if (LLVMIRGenerationRefCount == 1)
          LLVMIRGeneration.startTimer();
      }

      Gen->HandleTopLevelDecl(D);

      if (FrontendTimesIsEnabled) {
        LLVMIRGenerationRefCount -= 1;
        if (LLVMIRGenerationRefCount == 0)
          LLVMIRGeneration.stopTimer();
      }

      return true;
    }

    void HandleInlineFunctionDefinition(FunctionDecl *D) override {
      PrettyStackTraceDecl CrashInfo(D, SourceLocation(),
                                     Context->getSourceManager(),
                                     "LLVM IR generation of inline function");
      if (FrontendTimesIsEnabled)
        LLVMIRGeneration.startTimer();

      Gen->HandleInlineFunctionDefinition(D);

      if (FrontendTimesIsEnabled)
        LLVMIRGeneration.stopTimer();
    }

    void HandleInterestingDecl(DeclGroupRef D) override {
      // Ignore interesting decls from the AST reader after IRGen is finished.
      if (!IRGenFinished)
        HandleTopLevelDecl(D);
    }

    // Links each entry in LinkModules into our module.  Returns true on error.
    bool LinkInModules() {
      for (auto &LM : LinkModules) {
        if (LM.PropagateAttrs)
          for (Function &F : *LM.Module)
            Gen->CGM().addDefaultFunctionDefinitionAttributes(F);

        CurLinkModule = LM.Module.get();

        bool Err;
        if (LM.Internalize) {
          Err = Linker::linkModules(
              *getModule(), std::move(LM.Module), LM.LinkFlags,
              [](llvm::Module &M, const llvm::StringSet<> &GVS) {
                internalizeModule(M, [&GVS](const llvm::GlobalValue &GV) {
                  return !GV.hasName() || (GVS.count(GV.getName()) == 0);
                });
              });
        } else {
          Err = Linker::linkModules(*getModule(), std::move(LM.Module),
                                    LM.LinkFlags);
        }

        if (Err)
          return true;
      }
      return false; // success
    }

    void HandleTranslationUnit(ASTContext &C) override {
      {
        llvm::TimeTraceScope TimeScope("Frontend");
        PrettyStackTraceString CrashInfo("Per-file LLVM IR generation");
        if (FrontendTimesIsEnabled) {
          LLVMIRGenerationRefCount += 1;
          if (LLVMIRGenerationRefCount == 1)
            LLVMIRGeneration.startTimer();
        }

        Gen->HandleTranslationUnit(C);

        if (FrontendTimesIsEnabled) {
          LLVMIRGenerationRefCount -= 1;
          if (LLVMIRGenerationRefCount == 0)
            LLVMIRGeneration.stopTimer();
        }

        IRGenFinished = true;
      }

      // Silently ignore if we weren't initialized for some reason.
      if (!getModule())
        return;

      // Install an inline asm handler so that diagnostics get printed through
      // our diagnostics hooks.
      LLVMContext &Ctx = getModule()->getContext();
      LLVMContext::InlineAsmDiagHandlerTy OldHandler =
        Ctx.getInlineAsmDiagnosticHandler();
      void *OldContext = Ctx.getInlineAsmDiagnosticContext();
      Ctx.setInlineAsmDiagnosticHandler(InlineAsmDiagHandler, this);

      std::unique_ptr<DiagnosticHandler> OldDiagnosticHandler =
          Ctx.getDiagnosticHandler();
      Ctx.setDiagnosticHandler(std::make_unique<ClangDiagnosticHandler>(
        CodeGenOpts, this));

      Expected<std::unique_ptr<llvm::ToolOutputFile>> OptRecordFileOrErr =
          setupLLVMOptimizationRemarks(
              Ctx, CodeGenOpts.OptRecordFile, CodeGenOpts.OptRecordPasses,
              CodeGenOpts.OptRecordFormat, CodeGenOpts.DiagnosticsWithHotness,
              CodeGenOpts.DiagnosticsHotnessThreshold);

      if (Error E = OptRecordFileOrErr.takeError()) {
        reportOptRecordError(std::move(E), Diags, CodeGenOpts);
        return;
      }

      std::unique_ptr<llvm::ToolOutputFile> OptRecordFile =
          std::move(*OptRecordFileOrErr);

      if (OptRecordFile &&
          CodeGenOpts.getProfileUse() != CodeGenOptions::ProfileNone)
        Ctx.setDiagnosticsHotnessRequested(true);

      // Link each LinkModule into our module.
      if (LinkInModules())
        return;

      EmbedBitcode(getModule(), CodeGenOpts, llvm::MemoryBufferRef());

      EmitBackendOutput(Diags, HeaderSearchOpts, CodeGenOpts, TargetOpts,
                        LangOpts, C.getTargetInfo().getDataLayout(),
                        getModule(), Action, std::move(AsmOutStream));

      Ctx.setInlineAsmDiagnosticHandler(OldHandler, OldContext);

      Ctx.setDiagnosticHandler(std::move(OldDiagnosticHandler));

      if (OptRecordFile)
        OptRecordFile->keep();
    }

    void HandleTagDeclDefinition(TagDecl *D) override {
      PrettyStackTraceDecl CrashInfo(D, SourceLocation(),
                                     Context->getSourceManager(),
                                     "LLVM IR generation of declaration");
      Gen->HandleTagDeclDefinition(D);
    }

    void HandleTagDeclRequiredDefinition(const TagDecl *D) override {
      Gen->HandleTagDeclRequiredDefinition(D);
    }

    void CompleteTentativeDefinition(VarDecl *D) override {
      Gen->CompleteTentativeDefinition(D);
    }

    void CompleteExternalDeclaration(VarDecl *D) override {
      Gen->CompleteExternalDeclaration(D);
    }

    void AssignInheritanceModel(CXXRecordDecl *RD) override {
      Gen->AssignInheritanceModel(RD);
    }

    void HandleVTable(CXXRecordDecl *RD) override {
      Gen->HandleVTable(RD);
    }

    static void InlineAsmDiagHandler(const llvm::SMDiagnostic &SM,void *Context,
                                     unsigned LocCookie) {
      SourceLocation Loc = SourceLocation::getFromRawEncoding(LocCookie);
      ((BackendConsumer*)Context)->InlineAsmDiagHandler2(SM, Loc);
    }

    /// Get the best possible source location to represent a diagnostic that
    /// may have associated debug info.
    const FullSourceLoc
    getBestLocationFromDebugLoc(const llvm::DiagnosticInfoWithLocationBase &D,
                                bool &BadDebugInfo, StringRef &Filename,
                                unsigned &Line, unsigned &Column) const;

    void InlineAsmDiagHandler2(const llvm::SMDiagnostic &,
                               SourceLocation LocCookie);

    void DiagnosticHandlerImpl(const llvm::DiagnosticInfo &DI);
    /// Specialized handler for InlineAsm diagnostic.
    /// \return True if the diagnostic has been successfully reported, false
    /// otherwise.
    bool InlineAsmDiagHandler(const llvm::DiagnosticInfoInlineAsm &D);
    /// Specialized handler for StackSize diagnostic.
    /// \return True if the diagnostic has been successfully reported, false
    /// otherwise.
    bool StackSizeDiagHandler(const llvm::DiagnosticInfoStackSize &D);
    /// Specialized handler for unsupported backend feature diagnostic.
    void UnsupportedDiagHandler(const llvm::DiagnosticInfoUnsupported &D);
    /// Specialized handler for misexpect warnings.
    /// Note that misexpect remarks are emitted through ORE
    void MisExpectDiagHandler(const llvm::DiagnosticInfoMisExpect &D);
    /// Specialized handlers for optimization remarks.
    /// Note that these handlers only accept remarks and they always handle
    /// them.
    void EmitOptimizationMessage(const llvm::DiagnosticInfoOptimizationBase &D,
                                 unsigned DiagID);
    void
    OptimizationRemarkHandler(const llvm::DiagnosticInfoOptimizationBase &D);
    void OptimizationRemarkHandler(
        const llvm::OptimizationRemarkAnnotation &D);
    void OptimizationRemarkHandler(
        const llvm::OptimizationRemarkAnalysisFPCommute &D);
    void OptimizationRemarkHandler(
        const llvm::OptimizationRemarkAnalysisAliasing &D);
    void OptimizationFailureHandler(
        const llvm::DiagnosticInfoOptimizationFailure &D);
  };

  void BackendConsumer::anchor() {}
}

bool ClangDiagnosticHandler::handleDiagnostics(const DiagnosticInfo &DI) {
  BackendCon->DiagnosticHandlerImpl(DI);
  return true;
}

/// ConvertBackendLocation - Convert a location in a temporary llvm::SourceMgr
/// buffer to be a valid FullSourceLoc.
static FullSourceLoc ConvertBackendLocation(const llvm::SMDiagnostic &D,
                                            SourceManager &CSM) {
  // Get both the clang and llvm source managers.  The location is relative to
  // a memory buffer that the LLVM Source Manager is handling, we need to add
  // a copy to the Clang source manager.
  const llvm::SourceMgr &LSM = *D.getSourceMgr();

  // We need to copy the underlying LLVM memory buffer because llvm::SourceMgr
  // already owns its one and clang::SourceManager wants to own its one.
  const MemoryBuffer *LBuf =
  LSM.getMemoryBuffer(LSM.FindBufferContainingLoc(D.getLoc()));

  // Create the copy and transfer ownership to clang::SourceManager.
  // TODO: Avoid copying files into memory.
  std::unique_ptr<llvm::MemoryBuffer> CBuf =
      llvm::MemoryBuffer::getMemBufferCopy(LBuf->getBuffer(),
                                           LBuf->getBufferIdentifier());
  // FIXME: Keep a file ID map instead of creating new IDs for each location.
  FileID FID = CSM.createFileID(std::move(CBuf));

  // Translate the offset into the file.
  unsigned Offset = D.getLoc().getPointer() - LBuf->getBufferStart();
  SourceLocation NewLoc =
  CSM.getLocForStartOfFile(FID).getLocWithOffset(Offset);
  return FullSourceLoc(NewLoc, CSM);
}


/// InlineAsmDiagHandler2 - This function is invoked when the backend hits an
/// error parsing inline asm.  The SMDiagnostic indicates the error relative to
/// the temporary memory buffer that the inline asm parser has set up.
void BackendConsumer::InlineAsmDiagHandler2(const llvm::SMDiagnostic &D,
                                            SourceLocation LocCookie) {
  // There are a couple of different kinds of errors we could get here.  First,
  // we re-format the SMDiagnostic in terms of a clang diagnostic.

  // Strip "error: " off the start of the message string.
  StringRef Message = D.getMessage();
  if (Message.startswith("error: "))
    Message = Message.substr(7);

  // If the SMDiagnostic has an inline asm source location, translate it.
  FullSourceLoc Loc;
  if (D.getLoc() != SMLoc())
    Loc = ConvertBackendLocation(D, Context->getSourceManager());

  unsigned DiagID;
  switch (D.getKind()) {
  case llvm::SourceMgr::DK_Error:
    DiagID = diag::err_fe_inline_asm;
    break;
  case llvm::SourceMgr::DK_Warning:
    DiagID = diag::warn_fe_inline_asm;
    break;
  case llvm::SourceMgr::DK_Note:
    DiagID = diag::note_fe_inline_asm;
    break;
  case llvm::SourceMgr::DK_Remark:
    llvm_unreachable("remarks unexpected");
  }
  // If this problem has clang-level source location information, report the
  // issue in the source with a note showing the instantiated
  // code.
  if (LocCookie.isValid()) {
    Diags.Report(LocCookie, DiagID).AddString(Message);

    if (D.getLoc().isValid()) {
      DiagnosticBuilder B = Diags.Report(Loc, diag::note_fe_inline_asm_here);
      // Convert the SMDiagnostic ranges into SourceRange and attach them
      // to the diagnostic.
      for (const std::pair<unsigned, unsigned> &Range : D.getRanges()) {
        unsigned Column = D.getColumnNo();
        B << SourceRange(Loc.getLocWithOffset(Range.first - Column),
                         Loc.getLocWithOffset(Range.second - Column));
      }
    }
    return;
  }

  // Otherwise, report the backend issue as occurring in the generated .s file.
  // If Loc is invalid, we still need to report the issue, it just gets no
  // location info.
  Diags.Report(Loc, DiagID).AddString(Message);
}

#define ComputeDiagID(Severity, GroupName, DiagID)                             \
  do {                                                                         \
    switch (Severity) {                                                        \
    case llvm::DS_Error:                                                       \
      DiagID = diag::err_fe_##GroupName;                                       \
      break;                                                                   \
    case llvm::DS_Warning:                                                     \
      DiagID = diag::warn_fe_##GroupName;                                      \
      break;                                                                   \
    case llvm::DS_Remark:                                                      \
      llvm_unreachable("'remark' severity not expected");                      \
      break;                                                                   \
    case llvm::DS_Note:                                                        \
      DiagID = diag::note_fe_##GroupName;                                      \
      break;                                                                   \
    }                                                                          \
  } while (false)

#define ComputeDiagRemarkID(Severity, GroupName, DiagID)                       \
  do {                                                                         \
    switch (Severity) {                                                        \
    case llvm::DS_Error:                                                       \
      DiagID = diag::err_fe_##GroupName;                                       \
      break;                                                                   \
    case llvm::DS_Warning:                                                     \
      DiagID = diag::warn_fe_##GroupName;                                      \
      break;                                                                   \
    case llvm::DS_Remark:                                                      \
      DiagID = diag::remark_fe_##GroupName;                                    \
      break;                                                                   \
    case llvm::DS_Note:                                                        \
      DiagID = diag::note_fe_##GroupName;                                      \
      break;                                                                   \
    }                                                                          \
  } while (false)

bool
BackendConsumer::InlineAsmDiagHandler(const llvm::DiagnosticInfoInlineAsm &D) {
  unsigned DiagID;
  ComputeDiagID(D.getSeverity(), inline_asm, DiagID);
  std::string Message = D.getMsgStr().str();

  // If this problem has clang-level source location information, report the
  // issue as being a problem in the source with a note showing the instantiated
  // code.
  SourceLocation LocCookie =
      SourceLocation::getFromRawEncoding(D.getLocCookie());
  if (LocCookie.isValid())
    Diags.Report(LocCookie, DiagID).AddString(Message);
  else {
    // Otherwise, report the backend diagnostic as occurring in the generated
    // .s file.
    // If Loc is invalid, we still need to report the diagnostic, it just gets
    // no location info.
    FullSourceLoc Loc;
    Diags.Report(Loc, DiagID).AddString(Message);
  }
  // We handled all the possible severities.
  return true;
}

bool
BackendConsumer::StackSizeDiagHandler(const llvm::DiagnosticInfoStackSize &D) {
  if (D.getSeverity() != llvm::DS_Warning)
    // For now, the only support we have for StackSize diagnostic is warning.
    // We do not know how to format other severities.
    return false;

  if (const Decl *ND = Gen->GetDeclForMangledName(D.getFunction().getName())) {
    // FIXME: Shouldn't need to truncate to uint32_t
    Diags.Report(ND->getASTContext().getFullLoc(ND->getLocation()),
                 diag::warn_fe_frame_larger_than)
      << static_cast<uint32_t>(D.getStackSize()) << Decl::castToDeclContext(ND);
    return true;
  }

  return false;
}

const FullSourceLoc BackendConsumer::getBestLocationFromDebugLoc(
    const llvm::DiagnosticInfoWithLocationBase &D, bool &BadDebugInfo,
    StringRef &Filename, unsigned &Line, unsigned &Column) const {
  SourceManager &SourceMgr = Context->getSourceManager();
  FileManager &FileMgr = SourceMgr.getFileManager();
  SourceLocation DILoc;

  if (D.isLocationAvailable()) {
    D.getLocation(Filename, Line, Column);
    if (Line > 0) {
      auto FE = FileMgr.getFile(Filename);
      if (!FE)
        FE = FileMgr.getFile(D.getAbsolutePath());
      if (FE) {
        // If -gcolumn-info was not used, Column will be 0. This upsets the
        // source manager, so pass 1 if Column is not set.
        DILoc = SourceMgr.translateFileLineCol(*FE, Line, Column ? Column : 1);
      }
    }
    BadDebugInfo = DILoc.isInvalid();
  }

  // If a location isn't available, try to approximate it using the associated
  // function definition. We use the definition's right brace to differentiate
  // from diagnostics that genuinely relate to the function itself.
  FullSourceLoc Loc(DILoc, SourceMgr);
  if (Loc.isInvalid())
    if (const Decl *FD = Gen->GetDeclForMangledName(D.getFunction().getName()))
      Loc = FD->getASTContext().getFullLoc(FD->getLocation());

  if (DILoc.isInvalid() && D.isLocationAvailable())
    // If we were not able to translate the file:line:col information
    // back to a SourceLocation, at least emit a note stating that
    // we could not translate this location. This can happen in the
    // case of #line directives.
    Diags.Report(Loc, diag::note_fe_backend_invalid_loc)
        << Filename << Line << Column;

  return Loc;
}

void BackendConsumer::UnsupportedDiagHandler(
    const llvm::DiagnosticInfoUnsupported &D) {
  // We only support warnings or errors.
  assert(D.getSeverity() == llvm::DS_Error ||
         D.getSeverity() == llvm::DS_Warning);

  StringRef Filename;
  unsigned Line, Column;
  bool BadDebugInfo = false;
  FullSourceLoc Loc;
  std::string Msg;
  raw_string_ostream MsgStream(Msg);

  // Context will be nullptr for IR input files, we will construct the diag
  // message from llvm::DiagnosticInfoUnsupported.
  if (Context != nullptr) {
    Loc = getBestLocationFromDebugLoc(D, BadDebugInfo, Filename, Line, Column);
    MsgStream << D.getMessage();
  } else {
    DiagnosticPrinterRawOStream DP(MsgStream);
    D.print(DP);
  }

  auto DiagType = D.getSeverity() == llvm::DS_Error
                      ? diag::err_fe_backend_unsupported
                      : diag::warn_fe_backend_unsupported;
  Diags.Report(Loc, DiagType) << MsgStream.str();

  if (BadDebugInfo)
    // If we were not able to translate the file:line:col information
    // back to a SourceLocation, at least emit a note stating that
    // we could not translate this location. This can happen in the
    // case of #line directives.
    Diags.Report(Loc, diag::note_fe_backend_invalid_loc)
        << Filename << Line << Column;
}

void BackendConsumer::MisExpectDiagHandler(
    const llvm::DiagnosticInfoMisExpect &D) {
  StringRef Filename;
  unsigned Line, Column;
  bool BadDebugInfo = false;
  FullSourceLoc Loc;
  std::string Msg;
  raw_string_ostream MsgStream(Msg);
  DiagnosticPrinterRawOStream DP(MsgStream);

  // Context will be nullptr for IR input files, we will construct the diag
  // message from llvm::DiagnosticInfoMisExpect.
  if (Context != nullptr) {
    Loc = getBestLocationFromDebugLoc(D, BadDebugInfo, Filename, Line, Column);
    MsgStream << D.getMsg();
  } else {
    DiagnosticPrinterRawOStream DP(MsgStream);
    D.print(DP);
  }
  Diags.Report(Loc, diag::warn_profile_data_misexpect) << MsgStream.str();

  if (BadDebugInfo)
    // If we were not able to translate the file:line:col information
    // back to a SourceLocation, at least emit a note stating that
    // we could not translate this location. This can happen in the
    // case of #line directives.
    Diags.Report(Loc, diag::note_fe_backend_invalid_loc)
        << Filename << Line << Column;
}

void BackendConsumer::EmitOptimizationMessage(
    const llvm::DiagnosticInfoOptimizationBase &D, unsigned DiagID) {
  // We only support warnings and remarks.
  assert(D.getSeverity() == llvm::DS_Remark ||
         D.getSeverity() == llvm::DS_Warning);

  StringRef Filename;
  unsigned Line, Column;
  bool BadDebugInfo = false;
  FullSourceLoc Loc;
  std::string Msg;
  raw_string_ostream MsgStream(Msg);

  // Context will be nullptr for IR input files, we will construct the remark
  // message from llvm::DiagnosticInfoOptimizationBase.
  if (Context != nullptr) {
    Loc = getBestLocationFromDebugLoc(D, BadDebugInfo, Filename, Line, Column);
    MsgStream << D.getMsg();
  } else {
    DiagnosticPrinterRawOStream DP(MsgStream);
    D.print(DP);
  }

  if (D.getHotness())
    MsgStream << " (hotness: " << *D.getHotness() << ")";

  Diags.Report(Loc, DiagID)
      << AddFlagValue(D.getPassName())
      << MsgStream.str();

  if (BadDebugInfo)
    // If we were not able to translate the file:line:col information
    // back to a SourceLocation, at least emit a note stating that
    // we could not translate this location. This can happen in the
    // case of #line directives.
    Diags.Report(Loc, diag::note_fe_backend_invalid_loc)
        << Filename << Line << Column;
}

void BackendConsumer::OptimizationRemarkHandler(
    const llvm::DiagnosticInfoOptimizationBase &D) {
  // Without hotness information, don't show noisy remarks.
  if (D.isVerbose() && !D.getHotness())
    return;

  if (D.isPassed()) {
    // Optimization remarks are active only if the -Rpass flag has a regular
    // expression that matches the name of the pass name in \p D.
    if (CodeGenOpts.OptimizationRemarkPattern &&
        CodeGenOpts.OptimizationRemarkPattern->match(D.getPassName()))
      EmitOptimizationMessage(D, diag::remark_fe_backend_optimization_remark);
  } else if (D.isMissed()) {
    // Missed optimization remarks are active only if the -Rpass-missed
    // flag has a regular expression that matches the name of the pass
    // name in \p D.
    if (CodeGenOpts.OptimizationRemarkMissedPattern &&
        CodeGenOpts.OptimizationRemarkMissedPattern->match(D.getPassName()))
      EmitOptimizationMessage(
          D, diag::remark_fe_backend_optimization_remark_missed);
  } else {
    assert(D.isAnalysis() && "Unknown remark type");

    bool ShouldAlwaysPrint = false;
    if (auto *ORA = dyn_cast<llvm::OptimizationRemarkAnalysis>(&D))
      ShouldAlwaysPrint = ORA->shouldAlwaysPrint();

    if (ShouldAlwaysPrint ||
        (CodeGenOpts.OptimizationRemarkAnalysisPattern &&
         CodeGenOpts.OptimizationRemarkAnalysisPattern->match(D.getPassName())))
      EmitOptimizationMessage(
          D, diag::remark_fe_backend_optimization_remark_analysis);
  }
}

#include "clang/Sema/Lookup.h"
#include <fstream>
#include "clang/AST/PrettyPrinter.h"

static cl::opt<std::string> hto_file(
            "hto_file", cl::init("/tmp/annotations.h"), cl::Hidden,
                cl::desc("File to dump annotations into"));

static cl::opt<std::string> hto_dir(
            "hto_dir", cl::init(""), cl::Hidden,
                cl::desc("Directory to dump annotations into"));

void replaceAll( std::string &s, const std::string &search, const std::string &replace ) {
    for( size_t pos = 0; ; pos += replace.length() ) {
        // Locate the substring to replace
        pos = s.find( search, pos );
        if( pos == std::string::npos ) break;
        // Replace by erasing and inserting
        s.erase( pos, search.length() );
        s.insert( pos, replace );
    }
}

#include <cstdlib>
#include <map>
#include <map>

std::map<std::string, SmallPtrSet<const clang::Type*, 4>> doneRecords;
SmallSet<std::string, 4> addedbool;

void BackendConsumer::OptimizationRemarkHandler(
    const llvm::OptimizationRemarkAnnotation &D) {
  // Optimization analysis remarks are active if the pass name is set to
  // llvm::DiagnosticInfo::AlwasyPrint or if the -Rpass-analysis flag has a
  // regular expression that matches the name of the pass name in \p D.
  if (!CodeGenOpts.OptimizationRemarkAnnotation) return;
  

  GlobalDecl Decl;
  Gen->CGM().lookupRepresentativeDecl(D.getFunction().getName(), Decl);
  if (!Decl.getDecl()) {
        llvm::errs() << "!!!couldn't lookup decl " << D.getFunction().getName() << "\n";
             return;
  }

  const FunctionDecl* fd = dyn_cast<FunctionDecl>(Decl.getDecl());
  if (!Decl.getDecl()) {
      llvm::errs() << "!!!couldn't lookup function decl\n";
      return;
  }

  std::string myfile;
  if (hto_dir.size() != 0) {
    PresumedLoc PLoc = Context->getSourceManager().getPresumedLoc(fd->getBeginLoc());
    if (PLoc.isInvalid()) {
        fd->dump();
    }
    assert(!PLoc.isInvalid());

    auto nam = PLoc.getFilename();
    SmallVector< char, 10 > outp;
    std::string name;
    if (Context->getSourceManager().getFileManager().getVirtualFileSystem().getRealPath(nam, outp)) {
        name = std::string("nopath/") + std::string(nam);
    } else {
        name = std::string(outp.data(), outp.size());
    }

    std::string newfn = name.substr(0, name.rfind(".")) + ".h";
    replaceAll(newfn, "/", "-");
    myfile = hto_dir + "/" + newfn;
  } else {
      myfile = hto_file;
  }
  //llvm::errs() << "hto file: " << hto_file << "\n";

  std::string Msg;
  {
  raw_string_ostream MsgStream(Msg);
  MsgStream << D.getMsg();
  }
  
  std::string toprint;
  raw_string_ostream printstream(toprint);

  using ContextsTy = SmallVector<const DeclContext *, 8>;
  bool error = false;
  auto hasNamespace = [&](const NamedDecl *fd) {
   const DeclContext *Ctx = fd->getDeclContext();
   
   // Collect named contexts.
   while (Ctx) {
     if (isa<NamedDecl>(Ctx))
       return true;
     Ctx = Ctx->getParent();
   }
   return false;
  };
  auto inStdNamespace = [&](const NamedDecl *fd) {
   const DeclContext *Ctx = fd->getDeclContext();
   
   // Collect named contexts.
   while (Ctx) {
     if (auto nd = dyn_cast<NamedDecl>(Ctx)) {
         if (nd->getName() == "std") return true;
     }
     Ctx = Ctx->getParent();
   }
   return false;
  };

  bool requireshtocpp = false;
  auto namespaceBefore = [&](ContextsTy& Contexts, const NamedDecl *fd, raw_ostream &printstream, bool newline = true) {
   const DeclContext *Ctx = fd->getDeclContext();
 
   if (Ctx->isFunctionOrMethod()) {
	 llvm::errs() << "illegal nested function " << fd->getName() << "\n";
     return;
   } 
   
   bool notinclass = false; 
 
   while (Ctx) {
     if (isa<NamedDecl>(Ctx)) {
        if (isa<RecordDecl>(Ctx)) {
          requireshtocpp = true;
          if (notinclass) {
	   		llvm::errs() << "cannot handle function inside namespace inside class " << *fd << "\n";
            error = true;
       		return;
         }
        } else {
          notinclass = true;
          Contexts.push_back(Ctx);
        }
     }
     Ctx = Ctx->getParent();
   }

   for (const auto dc : llvm::reverse(Contexts)) {
     if (const auto *nd = dyn_cast<NamespaceDecl>(dc)) {

       if (nd->isAnonymousNamespace()) {
	   		llvm::errs() << "illegal anonymous namespace function " << *fd << "\n";
            error = true;
       		return;
       }
       if (nd->isInline()) {
           printstream << "inline ";
       }
	   printstream << "namespace "<< nd->getName() << " {";
     } else if (const auto *RD = dyn_cast<RecordDecl>(dc)) {
      if (!RD->getIdentifier()) {
          llvm::errs() << "illegal " << RD->getKindName() << " {anon} function " << *fd << "\n";
          error = true;
          return;
      }
      llvm::errs() << "illegal " << RD->getKindName() << " " << RD->getName() << " function " << *fd << "\n";
      error = true;
      return;
     } else if (const auto *RF = dyn_cast<FunctionDecl>(dc)) {
      if (!RF->getIdentifier()) {
          llvm::errs() << "illegal subfn" << *fd << "\n";
          error = true;
          return;
      }
      llvm::errs() << "illegal subfn in " << RF->getName() << ", " << *fd << "\n";
      error = true;
      return;
     } else {
	   llvm::errs() << "illegal not namespace function " << *fd << " in " << *nd << "\n";
       error = true;
       return;
     } 
   }
   if (newline) {
     printstream << "\n";
   }
  };

  bool seenbool = false;
  std::function<void(const clang::Type*)> handleType;
  std::function<void(std::string name, QualType)> handleTypedef = [&](std::string name, QualType qt)  {
    //llvm::errs() << "handling type "; ot->dump(); llvm::errs() << "\n";
      
    PrintingPolicy policy(Gen->CGM().getLangOpts());
      policy.Indentation = 0;
      policy.SuppressTagKeyword = false;
      policy.SuppressUnwrittenScope = false;
      policy.SuppressInitializers = true;
      policy.IncludeNewlines = false;
      policy.SuppressScope = false;
      policy.FullyQualifiedName = true;
      policy.Bool = false;
      policy.handleSubType = handleType;
      policy.handleTypedef = handleTypedef;

      std::string output;
      raw_string_ostream ostr(output);
      qt.print(ostr, policy, name, 0);
      printstream << "typedef " << ostr.str() << ";\n";
  };

  handleType = [&](const clang::Type* ot)  {
    if (doneRecords[myfile].count(ot) > 0) return;
    doneRecords[myfile].insert(ot);

    if (ot == (const clang::Type*)0xDEADBEEF) {
        seenbool = true;
        return;
    }
    if (auto bt = dyn_cast<BuiltinType>(ot)) {
        if (bt->getKind() == BuiltinType::Kind::Bool) {
            seenbool = true;
            return;
        }
    }

    if (auto tst = dyn_cast<TemplateSpecializationType>(ot)) {

        //if(!isa<RecordType>(ot)) return;
      
        std::string output;
        raw_string_ostream ostr(output);
      PrintingPolicy policy(Gen->CGM().getLangOpts());
      policy.Indentation = 0;
      policy.SuppressTagKeyword = false;
      policy.SuppressUnwrittenScope = false;
      policy.SuppressInitializers = true;
      policy.IncludeNewlines = false;
      policy.SuppressScope = false;
      policy.handleSubType = handleType;
      policy.handleTypedef = handleTypedef;
      policy.FullyQualifiedName = false;//true;
        
      auto dcl = tst->getTemplateName().getAsTemplateDecl();
      assert(dcl);
      //for(auto n : *dcl->getTemplateParameters()) {
      //  n->print(llvm::errs(), policy);
      //}

      dcl->print(ostr, policy);
            
        ContextsTy Contexts;
        printstream << "#ifdef __cplusplus\n";
        namespaceBefore(Contexts, dcl, printstream, false);

        printstream << ostr.str() << ";";
      
        for (const auto dc : llvm::reverse(Contexts)) {
          printstream << "}; "; 
        }
        printstream << "\n";
        printstream << "#endif\n";

        return;
    }
    
    if(const auto et = dyn_cast<RecordType>(ot)) {
      auto dcl = et->getDecl();
      auto str2 = dcl->getName().str();
      if (str2.size() == 0) {
            llvm::errs() << "Illegal -- please give all structs names\n";
            FullSourceLoc startloc(dcl->getOuterLocStart(), Context->getSourceManager());
            llvm::errs() << "specifically at file " << startloc.getFileEntry()->getName() << " line " << startloc.getLineNumber() << " col " << startloc.getColumnNumber() << "\n";
            assert(0 && "bad");
            exit(1);
      }

      /*
      PrintingPolicy policy(Gen->CGM().getLangOpts());
      policy.Indentation = 0;
      policy.SuppressTagKeyword = false;
      policy.SuppressUnwrittenScope = false;
      policy.SuppressInitializers = true;
      policy.IncludeNewlines = false;
      policy.SuppressScope = false;
      policy.handleSubType = handleType;
      policy.handleTypedef = handleTypedef;
      policy.FullyQualifiedName = false;//true;
      std::string outp;
      QualType(ot, 0).getAsStringInternal(outp, policy);
      */

      ContextsTy Contexts;
      if (dcl->getKind() == Decl::Kind::CXXRecord || hasNamespace(dcl)) {
        printstream << "#ifdef __cplusplus\n";
      }
      namespaceBefore(Contexts, dcl, printstream, false);

      printstream << dcl->getKindName() << " ";
      
    const DeclContext *Ctx = dcl->getDeclContext();
    SmallVector<const RecordDecl*,8> RContexts;
     while (Ctx) {
        if (const auto *RD = dyn_cast<RecordDecl>(Ctx)) {
          assert(RD->getIdentifier());
          RContexts.push_back(RD);
        }
        Ctx = Ctx->getParent();
     }
      for (const auto dc : llvm::reverse(RContexts)) {
        printstream << dc->getName().str() + "::";
      }

      printstream << dcl->getName() << "; ";
      //printstream << outp << "; ";
       
      for (const auto dc : llvm::reverse(Contexts)) {
         printstream << "}; "; 
      }
      printstream << "\n";
      if (dcl->getKind() == Decl::Kind::CXXRecord || hasNamespace(dcl)) {
        printstream << "#endif\n";
      }
      printstream << "\n";

      /*
        */
    }
  };

  if (inStdNamespace(fd)) return;
  
  std::string fnstring;
  raw_string_ostream fnstream(fnstring);

  ContextsTy Contexts;

  if (fd->getLanguageLinkage() == clang::LanguageLinkage::CLanguageLinkage ) {
    fnstream << "#ifdef __cplusplus\n";
    fnstream << "extern \"C\" {\n";
    if (!fd->isInExternCContext())
      fnstream << "#endif\n";
  } else if (fd->getLanguageLinkage() == clang::LanguageLinkage::CXXLanguageLinkage ) {
    fnstream << "#ifdef __cplusplus\n";
    fnstream << "extern \"C\" {\n";
  }



  //namespaceBefore(Contexts, fd, fnstream);
  if (error) return;

  fnstream << "__attribute__(( " << D.getMsg() << " ))\n";

  PrintingPolicy policy(Gen->CGM().getLangOpts());
  policy.Indentation = 0;
  policy.SuppressTagKeyword = false;
  policy.SuppressUnwrittenScope = false;
  policy.SuppressInitializers = true;
  policy.IncludeNewlines = false;
  policy.SuppressScope = false;
  policy.FullyQualifiedName = true;
  policy.TerseOutput = true;
  policy.Bool = fd->getLanguageLinkage() == clang::LanguageLinkage::CXXLanguageLinkage;
  policy.handleSubType = handleType;
  policy.handleTypedef = handleTypedef;
  std::string mangledname = "";
  policy.nameMangler = [&](FunctionDecl* myf) -> std::string{
     GlobalDecl gd;
     if (auto cons = dyn_cast<CXXConstructorDecl>(myf)) {
        error = true;
        return "";
         //gd = GlobalDecl(cons);
     } else if(auto des = dyn_cast<CXXDestructorDecl>(myf)) {
        error = true;
        return "";
         //gd = GlobalDecl(des);
     } else {
         gd = GlobalDecl(myf);
     }
     auto ret = Gen->CGM().getMangledName(gd);
     mangledname = ret.str();
     return ret.str();
  };
  std::string outp;

  std::string sstream;
  raw_string_ostream outstring(sstream);
  fd->print(outstring, policy, 0, false);
  if (error) return;

  //llvm::errs() << "__attribute__(( " << D.getMsg() << " ))\n";
  //
  if (requireshtocpp) {
    printstream << "#ifdef __hto_cpp__\n";
  }

  printstream << fnstream.str();
  //llvm::errs() << outstring.str() << ";\n";
  printstream << outstring.str() << ";\n";

  printstream << "void* __hto_global_" << mangledname << " = " << mangledname << ";\n";
   
  //for (const auto dc : llvm::reverse(Contexts)) {
  //   printstream << "}; "; 
  //}

  if (fd->getLanguageLinkage() == clang::LanguageLinkage::CLanguageLinkage ) {
    if (!fd->isInExternCContext())
      printstream << "#ifdef __cplusplus\n";
    printstream << "}\n";
    printstream << "#endif\n";
  } else if (fd->getLanguageLinkage() == clang::LanguageLinkage::CXXLanguageLinkage ) {
    printstream << "}\n";
    printstream << "#endif\n";
  }
  
  if (requireshtocpp) {
    printstream << "#endif\n";
  }
  
  printstream << "\n";

  if (error) return;
  
  {
  std::error_code error;
  raw_fd_ostream outfile(myfile, error, llvm::sys::fs::OpenFlags::F_Append);
	if (error) {
		llvm::errs() << "could not open file " << myfile << " because of " << error.message() << "\n";
		llvm_unreachable("badfile");
    }
  if (addedbool.count(myfile) == 0 && seenbool) {
    outfile << "#include <stdbool.h>\n";
    addedbool.insert(myfile);
  }
  outfile << printstream.str();
  outfile.close();
  }
}

void BackendConsumer::OptimizationRemarkHandler(
    const llvm::OptimizationRemarkAnalysisFPCommute &D) {
  // Optimization analysis remarks are active if the pass name is set to
  // llvm::DiagnosticInfo::AlwasyPrint or if the -Rpass-analysis flag has a
  // regular expression that matches the name of the pass name in \p D.

  if (D.shouldAlwaysPrint() ||
      (CodeGenOpts.OptimizationRemarkAnalysisPattern &&
       CodeGenOpts.OptimizationRemarkAnalysisPattern->match(D.getPassName())))
    EmitOptimizationMessage(
        D, diag::remark_fe_backend_optimization_remark_analysis_fpcommute);
}

void BackendConsumer::OptimizationRemarkHandler(
    const llvm::OptimizationRemarkAnalysisAliasing &D) {
  // Optimization analysis remarks are active if the pass name is set to
  // llvm::DiagnosticInfo::AlwasyPrint or if the -Rpass-analysis flag has a
  // regular expression that matches the name of the pass name in \p D.

  if (D.shouldAlwaysPrint() ||
      (CodeGenOpts.OptimizationRemarkAnalysisPattern &&
       CodeGenOpts.OptimizationRemarkAnalysisPattern->match(D.getPassName())))
    EmitOptimizationMessage(
        D, diag::remark_fe_backend_optimization_remark_analysis_aliasing);
}

void BackendConsumer::OptimizationFailureHandler(
    const llvm::DiagnosticInfoOptimizationFailure &D) {
  EmitOptimizationMessage(D, diag::warn_fe_backend_optimization_failure);
}

/// This function is invoked when the backend needs
/// to report something to the user.
void BackendConsumer::DiagnosticHandlerImpl(const DiagnosticInfo &DI) {
  unsigned DiagID = diag::err_fe_inline_asm;
  llvm::DiagnosticSeverity Severity = DI.getSeverity();
  // Get the diagnostic ID based.
  switch (DI.getKind()) {
  case llvm::DK_InlineAsm:
    if (InlineAsmDiagHandler(cast<DiagnosticInfoInlineAsm>(DI)))
      return;
    ComputeDiagID(Severity, inline_asm, DiagID);
    break;
  case llvm::DK_StackSize:
    if (StackSizeDiagHandler(cast<DiagnosticInfoStackSize>(DI)))
      return;
    ComputeDiagID(Severity, backend_frame_larger_than, DiagID);
    break;
  case DK_Linker:
    assert(CurLinkModule);
    // FIXME: stop eating the warnings and notes.
    if (Severity != DS_Error)
      return;
    DiagID = diag::err_fe_cannot_link_module;
    break;
  case llvm::DK_OptimizationRemark:
    // Optimization remarks are always handled completely by this
    // handler. There is no generic way of emitting them.
    OptimizationRemarkHandler(cast<OptimizationRemark>(DI));
    return;
  case llvm::DK_OptimizationRemarkMissed:
    // Optimization remarks are always handled completely by this
    // handler. There is no generic way of emitting them.
    OptimizationRemarkHandler(cast<OptimizationRemarkMissed>(DI));
    return;
  case llvm::DK_OptimizationRemarkAnalysis:
    // Optimization remarks are always handled completely by this
    // handler. There is no generic way of emitting them.
    OptimizationRemarkHandler(cast<OptimizationRemarkAnalysis>(DI));
    return;
  case llvm::DK_OptimizationRemarkAnnotation:
    // Optimization remarks are always handled completely by this
    // handler. There is no generic way of emitting them.
    OptimizationRemarkHandler(cast<OptimizationRemarkAnnotation>(DI));
    return;
  case llvm::DK_OptimizationRemarkAnalysisFPCommute:
    // Optimization remarks are always handled completely by this
    // handler. There is no generic way of emitting them.
    OptimizationRemarkHandler(cast<OptimizationRemarkAnalysisFPCommute>(DI));
    return;
  case llvm::DK_OptimizationRemarkAnalysisAliasing:
    // Optimization remarks are always handled completely by this
    // handler. There is no generic way of emitting them.
    OptimizationRemarkHandler(cast<OptimizationRemarkAnalysisAliasing>(DI));
    return;
  case llvm::DK_MachineOptimizationRemark:
    // Optimization remarks are always handled completely by this
    // handler. There is no generic way of emitting them.
    OptimizationRemarkHandler(cast<MachineOptimizationRemark>(DI));
    return;
  case llvm::DK_MachineOptimizationRemarkMissed:
    // Optimization remarks are always handled completely by this
    // handler. There is no generic way of emitting them.
    OptimizationRemarkHandler(cast<MachineOptimizationRemarkMissed>(DI));
    return;
  case llvm::DK_MachineOptimizationRemarkAnalysis:
    // Optimization remarks are always handled completely by this
    // handler. There is no generic way of emitting them.
    OptimizationRemarkHandler(cast<MachineOptimizationRemarkAnalysis>(DI));
    return;
  case llvm::DK_OptimizationFailure:
    // Optimization failures are always handled completely by this
    // handler.
    OptimizationFailureHandler(cast<DiagnosticInfoOptimizationFailure>(DI));
    return;
  case llvm::DK_Unsupported:
    UnsupportedDiagHandler(cast<DiagnosticInfoUnsupported>(DI));
    return;
  case llvm::DK_MisExpect:
    MisExpectDiagHandler(cast<DiagnosticInfoMisExpect>(DI));
    return;
  default:
    // Plugin IDs are not bound to any value as they are set dynamically.
    ComputeDiagRemarkID(Severity, backend_plugin, DiagID);
    break;
  }
  std::string MsgStorage;
  {
    raw_string_ostream Stream(MsgStorage);
    DiagnosticPrinterRawOStream DP(Stream);
    DI.print(DP);
  }

  if (DiagID == diag::err_fe_cannot_link_module) {
    Diags.Report(diag::err_fe_cannot_link_module)
        << CurLinkModule->getModuleIdentifier() << MsgStorage;
    return;
  }

  // Report the backend message using the usual diagnostic mechanism.
  FullSourceLoc Loc;
  Diags.Report(Loc, DiagID).AddString(MsgStorage);
}
#undef ComputeDiagID

CodeGenAction::CodeGenAction(unsigned _Act, LLVMContext *_VMContext)
    : Act(_Act), VMContext(_VMContext ? _VMContext : new LLVMContext),
      OwnsVMContext(!_VMContext) {}

CodeGenAction::~CodeGenAction() {
  TheModule.reset();
  if (OwnsVMContext)
    delete VMContext;
}

bool CodeGenAction::hasIRSupport() const { return true; }

void CodeGenAction::EndSourceFileAction() {
  // If the consumer creation failed, do nothing.
  if (!getCompilerInstance().hasASTConsumer())
    return;

  // Steal the module from the consumer.
  TheModule = BEConsumer->takeModule();
}

std::unique_ptr<llvm::Module> CodeGenAction::takeModule() {
  return std::move(TheModule);
}

llvm::LLVMContext *CodeGenAction::takeLLVMContext() {
  OwnsVMContext = false;
  return VMContext;
}

static std::unique_ptr<raw_pwrite_stream>
GetOutputStream(CompilerInstance &CI, StringRef InFile, BackendAction Action) {
  switch (Action) {
  case Backend_EmitAssembly:
    return CI.createDefaultOutputFile(false, InFile, "s");
  case Backend_EmitLL:
    return CI.createDefaultOutputFile(false, InFile, "ll");
  case Backend_EmitBC:
    return CI.createDefaultOutputFile(true, InFile, "bc");
  case Backend_EmitNothing:
    return nullptr;
  case Backend_EmitMCNull:
    return CI.createNullOutputFile();
  case Backend_EmitObj:
    return CI.createDefaultOutputFile(true, InFile, "o");
  }

  llvm_unreachable("Invalid action!");
}

std::unique_ptr<ASTConsumer>
CodeGenAction::CreateASTConsumer(CompilerInstance &CI, StringRef InFile) {
  BackendAction BA = static_cast<BackendAction>(Act);
  std::unique_ptr<raw_pwrite_stream> OS = CI.takeOutputStream();
  if (!OS)
    OS = GetOutputStream(CI, InFile, BA);

  if (BA != Backend_EmitNothing && !OS)
    return nullptr;

  // Load bitcode modules to link with, if we need to.
  if (LinkModules.empty())
    for (const CodeGenOptions::BitcodeFileToLink &F :
         CI.getCodeGenOpts().LinkBitcodeFiles) {
      auto BCBuf = CI.getFileManager().getBufferForFile(F.Filename);
      if (!BCBuf) {
        CI.getDiagnostics().Report(diag::err_cannot_open_file)
            << F.Filename << BCBuf.getError().message();
        LinkModules.clear();
        return nullptr;
      }

      Expected<std::unique_ptr<llvm::Module>> ModuleOrErr =
          getOwningLazyBitcodeModule(std::move(*BCBuf), *VMContext);
      if (!ModuleOrErr) {
        handleAllErrors(ModuleOrErr.takeError(), [&](ErrorInfoBase &EIB) {
          CI.getDiagnostics().Report(diag::err_cannot_open_file)
              << F.Filename << EIB.message();
        });
        LinkModules.clear();
        return nullptr;
      }
      LinkModules.push_back({std::move(ModuleOrErr.get()), F.PropagateAttrs,
                             F.Internalize, F.LinkFlags});
    }

  CoverageSourceInfo *CoverageInfo = nullptr;
  // Add the preprocessor callback only when the coverage mapping is generated.
  if (CI.getCodeGenOpts().CoverageMapping)
    CoverageInfo = CodeGen::CoverageMappingModuleGen::setUpCoverageCallbacks(
        CI.getPreprocessor());

  std::unique_ptr<BackendConsumer> Result(new BackendConsumer(
      BA, CI.getDiagnostics(), CI.getHeaderSearchOpts(),
      CI.getPreprocessorOpts(), CI.getCodeGenOpts(), CI.getTargetOpts(),
      CI.getLangOpts(), CI.getFrontendOpts().ShowTimers, std::string(InFile),
      std::move(LinkModules), std::move(OS), *VMContext, CoverageInfo, &CI));
  BEConsumer = Result.get();

  // Enable generating macro debug info only when debug info is not disabled and
  // also macro debug info is enabled.
  if (CI.getCodeGenOpts().getDebugInfo() != codegenoptions::NoDebugInfo &&
      CI.getCodeGenOpts().MacroDebugInfo) {
    std::unique_ptr<PPCallbacks> Callbacks =
        std::make_unique<MacroPPCallbacks>(BEConsumer->getCodeGenerator(),
                                            CI.getPreprocessor());
    CI.getPreprocessor().addPPCallbacks(std::move(Callbacks));
  }

  return std::move(Result);
}

static void BitcodeInlineAsmDiagHandler(const llvm::SMDiagnostic &SM,
                                         void *Context,
                                         unsigned LocCookie) {
  SM.print(nullptr, llvm::errs());

  auto Diags = static_cast<DiagnosticsEngine *>(Context);
  unsigned DiagID;
  switch (SM.getKind()) {
  case llvm::SourceMgr::DK_Error:
    DiagID = diag::err_fe_inline_asm;
    break;
  case llvm::SourceMgr::DK_Warning:
    DiagID = diag::warn_fe_inline_asm;
    break;
  case llvm::SourceMgr::DK_Note:
    DiagID = diag::note_fe_inline_asm;
    break;
  case llvm::SourceMgr::DK_Remark:
    llvm_unreachable("remarks unexpected");
  }

  Diags->Report(DiagID).AddString("cannot compile inline asm");
}

std::unique_ptr<llvm::Module>
CodeGenAction::loadModule(MemoryBufferRef MBRef) {
  CompilerInstance &CI = getCompilerInstance();
  SourceManager &SM = CI.getSourceManager();

  // For ThinLTO backend invocations, ensure that the context
  // merges types based on ODR identifiers. We also need to read
  // the correct module out of a multi-module bitcode file.
  if (!CI.getCodeGenOpts().ThinLTOIndexFile.empty()) {
    VMContext->enableDebugTypeODRUniquing();

    auto DiagErrors = [&](Error E) -> std::unique_ptr<llvm::Module> {
      unsigned DiagID =
          CI.getDiagnostics().getCustomDiagID(DiagnosticsEngine::Error, "%0");
      handleAllErrors(std::move(E), [&](ErrorInfoBase &EIB) {
        CI.getDiagnostics().Report(DiagID) << EIB.message();
      });
      return {};
    };

    Expected<std::vector<BitcodeModule>> BMsOrErr = getBitcodeModuleList(MBRef);
    if (!BMsOrErr)
      return DiagErrors(BMsOrErr.takeError());
    BitcodeModule *Bm = FindThinLTOModule(*BMsOrErr);
    // We have nothing to do if the file contains no ThinLTO module. This is
    // possible if ThinLTO compilation was not able to split module. Content of
    // the file was already processed by indexing and will be passed to the
    // linker using merged object file.
    if (!Bm) {
      auto M = std::make_unique<llvm::Module>("empty", *VMContext);
      M->setTargetTriple(CI.getTargetOpts().Triple);
      return M;
    }
    Expected<std::unique_ptr<llvm::Module>> MOrErr =
        Bm->parseModule(*VMContext);
    if (!MOrErr)
      return DiagErrors(MOrErr.takeError());
    return std::move(*MOrErr);
  }

  llvm::SMDiagnostic Err;
  if (std::unique_ptr<llvm::Module> M = parseIR(MBRef, Err, *VMContext))
    return M;

  // Translate from the diagnostic info to the SourceManager location if
  // available.
  // TODO: Unify this with ConvertBackendLocation()
  SourceLocation Loc;
  if (Err.getLineNo() > 0) {
    assert(Err.getColumnNo() >= 0);
    Loc = SM.translateFileLineCol(SM.getFileEntryForID(SM.getMainFileID()),
                                  Err.getLineNo(), Err.getColumnNo() + 1);
  }

  // Strip off a leading diagnostic code if there is one.
  StringRef Msg = Err.getMessage();
  if (Msg.startswith("error: "))
    Msg = Msg.substr(7);

  unsigned DiagID =
      CI.getDiagnostics().getCustomDiagID(DiagnosticsEngine::Error, "%0");

  CI.getDiagnostics().Report(Loc, DiagID) << Msg;
  return {};
}

void CodeGenAction::ExecuteAction() {
  // If this is an IR file, we have to treat it specially.
  if (getCurrentFileKind().getLanguage() == Language::LLVM_IR) {
    BackendAction BA = static_cast<BackendAction>(Act);
    CompilerInstance &CI = getCompilerInstance();
    auto &CodeGenOpts = CI.getCodeGenOpts();
    auto &Diagnostics = CI.getDiagnostics();
    std::unique_ptr<raw_pwrite_stream> OS =
        GetOutputStream(CI, getCurrentFile(), BA);
    if (BA != Backend_EmitNothing && !OS)
      return;

    bool Invalid;
    SourceManager &SM = CI.getSourceManager();
    FileID FID = SM.getMainFileID();
    const llvm::MemoryBuffer *MainFile = SM.getBuffer(FID, &Invalid);
    if (Invalid)
      return;

    TheModule = loadModule(*MainFile);
    if (!TheModule)
      return;

    const TargetOptions &TargetOpts = CI.getTargetOpts();
    if (TheModule->getTargetTriple() != TargetOpts.Triple) {
      Diagnostics.Report(SourceLocation(),
                         diag::warn_fe_override_module)
          << TargetOpts.Triple;
      TheModule->setTargetTriple(TargetOpts.Triple);
    }

    EmbedBitcode(TheModule.get(), CodeGenOpts,
                 MainFile->getMemBufferRef());

    LLVMContext &Ctx = TheModule->getContext();
    Ctx.setInlineAsmDiagnosticHandler(BitcodeInlineAsmDiagHandler,
                                      &Diagnostics);

    // Set clang diagnostic handler. To do this we need to create a fake
    // BackendConsumer.
    BackendConsumer Result(BA, CI.getDiagnostics(), CI.getHeaderSearchOpts(),
                           CI.getPreprocessorOpts(), CI.getCodeGenOpts(),
                           CI.getTargetOpts(), CI.getLangOpts(),
                           CI.getFrontendOpts().ShowTimers,
                           std::move(LinkModules), *VMContext, nullptr);
    // PR44896: Force DiscardValueNames as false. DiscardValueNames cannot be
    // true here because the valued names are needed for reading textual IR.
    Ctx.setDiscardValueNames(false);
    Ctx.setDiagnosticHandler(
        std::make_unique<ClangDiagnosticHandler>(CodeGenOpts, &Result));

    Expected<std::unique_ptr<llvm::ToolOutputFile>> OptRecordFileOrErr =
        setupLLVMOptimizationRemarks(
            Ctx, CodeGenOpts.OptRecordFile, CodeGenOpts.OptRecordPasses,
            CodeGenOpts.OptRecordFormat, CodeGenOpts.DiagnosticsWithHotness,
            CodeGenOpts.DiagnosticsHotnessThreshold);

    if (Error E = OptRecordFileOrErr.takeError()) {
      reportOptRecordError(std::move(E), Diagnostics, CodeGenOpts);
      return;
    }
    std::unique_ptr<llvm::ToolOutputFile> OptRecordFile =
        std::move(*OptRecordFileOrErr);

    EmitBackendOutput(Diagnostics, CI.getHeaderSearchOpts(), CodeGenOpts,
                      TargetOpts, CI.getLangOpts(),
                      CI.getTarget().getDataLayout(), TheModule.get(), BA,
                      std::move(OS));

    if (OptRecordFile)
      OptRecordFile->keep();
    return;
  }

  // Otherwise follow the normal AST path.
  this->ASTFrontendAction::ExecuteAction();
}

//

void EmitAssemblyAction::anchor() { }
EmitAssemblyAction::EmitAssemblyAction(llvm::LLVMContext *_VMContext)
  : CodeGenAction(Backend_EmitAssembly, _VMContext) {}

void EmitBCAction::anchor() { }
EmitBCAction::EmitBCAction(llvm::LLVMContext *_VMContext)
  : CodeGenAction(Backend_EmitBC, _VMContext) {}

void EmitLLVMAction::anchor() { }
EmitLLVMAction::EmitLLVMAction(llvm::LLVMContext *_VMContext)
  : CodeGenAction(Backend_EmitLL, _VMContext) {}

void EmitLLVMOnlyAction::anchor() { }
EmitLLVMOnlyAction::EmitLLVMOnlyAction(llvm::LLVMContext *_VMContext)
  : CodeGenAction(Backend_EmitNothing, _VMContext) {}

void EmitCodeGenOnlyAction::anchor() { }
EmitCodeGenOnlyAction::EmitCodeGenOnlyAction(llvm::LLVMContext *_VMContext)
  : CodeGenAction(Backend_EmitMCNull, _VMContext) {}

void EmitObjAction::anchor() { }
EmitObjAction::EmitObjAction(llvm::LLVMContext *_VMContext)
  : CodeGenAction(Backend_EmitObj, _VMContext) {}
