//===--- CGCall.cpp - Encapsulate calling convention details --------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// These classes wrap the information about a call or function
// definition used to handle ABI compliancy.
//
//===----------------------------------------------------------------------===//

#include "CGCall.h"
#include "ABIInfo.h"
#include "CGBlocks.h"
#include "CGCXXABI.h"
#include "CGCleanup.h"
#include "CGRecordLayout.h"
#include "CodeGenFunction.h"
#include "CodeGenModule.h"
#include "TargetInfo.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclObjC.h"
#include "clang/Basic/CodeGenOptions.h"
#include "clang/Basic/TargetBuiltins.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/CodeGen/CGFunctionInfo.h"
#include "clang/CodeGen/SwiftCallingConv.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Transforms/Utils/Local.h"
using namespace clang;
using namespace CodeGen;

/***/

unsigned CodeGenTypes::ClangCallConvToLLVMCallConv(CallingConv CC) {
  switch (CC) {
  default: return llvm::CallingConv::C;
  case CC_X86StdCall: return llvm::CallingConv::X86_StdCall;
  case CC_X86FastCall: return llvm::CallingConv::X86_FastCall;
  case CC_X86RegCall: return llvm::CallingConv::X86_RegCall;
  case CC_X86ThisCall: return llvm::CallingConv::X86_ThisCall;
  case CC_Win64: return llvm::CallingConv::Win64;
  case CC_X86_64SysV: return llvm::CallingConv::X86_64_SysV;
  case CC_AAPCS: return llvm::CallingConv::ARM_AAPCS;
  case CC_AAPCS_VFP: return llvm::CallingConv::ARM_AAPCS_VFP;
  case CC_IntelOclBicc: return llvm::CallingConv::Intel_OCL_BI;
  // TODO: Add support for __pascal to LLVM.
  case CC_X86Pascal: return llvm::CallingConv::C;
  // TODO: Add support for __vectorcall to LLVM.
  case CC_X86VectorCall: return llvm::CallingConv::X86_VectorCall;
  case CC_AArch64VectorCall: return llvm::CallingConv::AArch64_VectorCall;
  case CC_SpirFunction: return llvm::CallingConv::SPIR_FUNC;
  case CC_OpenCLKernel: return CGM.getTargetCodeGenInfo().getOpenCLKernelCallingConv();
  case CC_PreserveMost: return llvm::CallingConv::PreserveMost;
  case CC_PreserveAll: return llvm::CallingConv::PreserveAll;
  case CC_Swift: return llvm::CallingConv::Swift;
  }
}

/// Derives the 'this' type for codegen purposes, i.e. ignoring method CVR
/// qualification. Either or both of RD and MD may be null. A null RD indicates
/// that there is no meaningful 'this' type, and a null MD can occur when
/// calling a method pointer.
CanQualType CodeGenTypes::DeriveThisType(const CXXRecordDecl *RD,
                                         const CXXMethodDecl *MD) {
  QualType RecTy;
  if (RD)
    RecTy = Context.getTagDeclType(RD)->getCanonicalTypeInternal();
  else
    RecTy = Context.VoidTy;

  if (MD)
    RecTy = Context.getAddrSpaceQualType(RecTy, MD->getMethodQualifiers().getAddressSpace());
  return Context.getPointerType(CanQualType::CreateUnsafe(RecTy));
}

/// Returns the canonical formal type of the given C++ method.
static CanQual<FunctionProtoType> GetFormalType(const CXXMethodDecl *MD) {
  return MD->getType()->getCanonicalTypeUnqualified()
           .getAs<FunctionProtoType>();
}

/// Returns the "extra-canonicalized" return type, which discards
/// qualifiers on the return type.  Codegen doesn't care about them,
/// and it makes ABI code a little easier to be able to assume that
/// all parameter and return types are top-level unqualified.
static CanQualType GetReturnType(QualType RetTy) {
  return RetTy->getCanonicalTypeUnqualified().getUnqualifiedType();
}

/// Arrange the argument and result information for a value of the given
/// unprototyped freestanding function type.
const CGFunctionInfo &
CodeGenTypes::arrangeFreeFunctionType(CanQual<FunctionNoProtoType> FTNP) {
  // When translating an unprototyped function type, always use a
  // variadic type.
  return arrangeLLVMFunctionInfo(FTNP->getReturnType().getUnqualifiedType(),
                                 /*instanceMethod=*/false,
                                 /*chainCall=*/false, None,
                                 FTNP->getExtInfo(), {}, RequiredArgs(0));
}

static void addExtParameterInfosForCall(
         llvm::SmallVectorImpl<FunctionProtoType::ExtParameterInfo> &paramInfos,
                                        const FunctionProtoType *proto,
                                        unsigned prefixArgs,
                                        unsigned totalArgs) {
  assert(proto->hasExtParameterInfos());
  assert(paramInfos.size() <= prefixArgs);
  assert(proto->getNumParams() + prefixArgs <= totalArgs);

  paramInfos.reserve(totalArgs);

  // Add default infos for any prefix args that don't already have infos.
  paramInfos.resize(prefixArgs);

  // Add infos for the prototype.
  for (const auto &ParamInfo : proto->getExtParameterInfos()) {
    paramInfos.push_back(ParamInfo);
    // pass_object_size params have no parameter info.
    if (ParamInfo.hasPassObjectSize())
      paramInfos.emplace_back();
  }

  assert(paramInfos.size() <= totalArgs &&
         "Did we forget to insert pass_object_size args?");
  // Add default infos for the variadic and/or suffix arguments.
  paramInfos.resize(totalArgs);
}

/// Adds the formal parameters in FPT to the given prefix. If any parameter in
/// FPT has pass_object_size attrs, then we'll add parameters for those, too.
static void appendParameterTypes(const CodeGenTypes &CGT,
                                 SmallVectorImpl<CanQualType> &prefix,
              SmallVectorImpl<FunctionProtoType::ExtParameterInfo> &paramInfos,
                                 CanQual<FunctionProtoType> FPT) {
  // Fast path: don't touch param info if we don't need to.
  if (!FPT->hasExtParameterInfos()) {
    assert(paramInfos.empty() &&
           "We have paramInfos, but the prototype doesn't?");
    prefix.append(FPT->param_type_begin(), FPT->param_type_end());
    return;
  }

  unsigned PrefixSize = prefix.size();
  // In the vast majority of cases, we'll have precisely FPT->getNumParams()
  // parameters; the only thing that can change this is the presence of
  // pass_object_size. So, we preallocate for the common case.
  prefix.reserve(prefix.size() + FPT->getNumParams());

  auto ExtInfos = FPT->getExtParameterInfos();
  assert(ExtInfos.size() == FPT->getNumParams());
  for (unsigned I = 0, E = FPT->getNumParams(); I != E; ++I) {
    prefix.push_back(FPT->getParamType(I));
    if (ExtInfos[I].hasPassObjectSize())
      prefix.push_back(CGT.getContext().getSizeType());
  }

  addExtParameterInfosForCall(paramInfos, FPT.getTypePtr(), PrefixSize,
                              prefix.size());
}

/// Arrange the LLVM function layout for a value of the given function
/// type, on top of any implicit parameters already stored.
static const CGFunctionInfo &
arrangeLLVMFunctionInfo(CodeGenTypes &CGT, bool instanceMethod,
                        SmallVectorImpl<CanQualType> &prefix,
                        CanQual<FunctionProtoType> FTP) {
  SmallVector<FunctionProtoType::ExtParameterInfo, 16> paramInfos;
  RequiredArgs Required = RequiredArgs::forPrototypePlus(FTP, prefix.size());
  // FIXME: Kill copy.
  appendParameterTypes(CGT, prefix, paramInfos, FTP);
  CanQualType resultType = FTP->getReturnType().getUnqualifiedType();

  return CGT.arrangeLLVMFunctionInfo(resultType, instanceMethod,
                                     /*chainCall=*/false, prefix,
                                     FTP->getExtInfo(), paramInfos,
                                     Required);
}

/// Arrange the argument and result information for a value of the
/// given freestanding function type.
const CGFunctionInfo &
CodeGenTypes::arrangeFreeFunctionType(CanQual<FunctionProtoType> FTP) {
  SmallVector<CanQualType, 16> argTypes;
  return ::arrangeLLVMFunctionInfo(*this, /*instanceMethod=*/false, argTypes,
                                   FTP);
}

static CallingConv getCallingConventionForDecl(const Decl *D, bool IsWindows) {
  // Set the appropriate calling convention for the Function.
  if (D->hasAttr<StdCallAttr>())
    return CC_X86StdCall;

  if (D->hasAttr<FastCallAttr>())
    return CC_X86FastCall;

  if (D->hasAttr<RegCallAttr>())
    return CC_X86RegCall;

  if (D->hasAttr<ThisCallAttr>())
    return CC_X86ThisCall;

  if (D->hasAttr<VectorCallAttr>())
    return CC_X86VectorCall;

  if (D->hasAttr<PascalAttr>())
    return CC_X86Pascal;

  if (PcsAttr *PCS = D->getAttr<PcsAttr>())
    return (PCS->getPCS() == PcsAttr::AAPCS ? CC_AAPCS : CC_AAPCS_VFP);

  if (D->hasAttr<AArch64VectorPcsAttr>())
    return CC_AArch64VectorCall;

  if (D->hasAttr<IntelOclBiccAttr>())
    return CC_IntelOclBicc;

  if (D->hasAttr<MSABIAttr>())
    return IsWindows ? CC_C : CC_Win64;

  if (D->hasAttr<SysVABIAttr>())
    return IsWindows ? CC_X86_64SysV : CC_C;

  if (D->hasAttr<PreserveMostAttr>())
    return CC_PreserveMost;

  if (D->hasAttr<PreserveAllAttr>())
    return CC_PreserveAll;

  return CC_C;
}

/// Arrange the argument and result information for a call to an
/// unknown C++ non-static member function of the given abstract type.
/// (A null RD means we don't have any meaningful "this" argument type,
///  so fall back to a generic pointer type).
/// The member function must be an ordinary function, i.e. not a
/// constructor or destructor.
const CGFunctionInfo &
CodeGenTypes::arrangeCXXMethodType(const CXXRecordDecl *RD,
                                   const FunctionProtoType *FTP,
                                   const CXXMethodDecl *MD) {
  SmallVector<CanQualType, 16> argTypes;

  // Add the 'this' pointer.
  argTypes.push_back(DeriveThisType(RD, MD));

  return ::arrangeLLVMFunctionInfo(
      *this, true, argTypes,
      FTP->getCanonicalTypeUnqualified().getAs<FunctionProtoType>());
}

/// Set calling convention for CUDA/HIP kernel.
static void setCUDAKernelCallingConvention(CanQualType &FTy, CodeGenModule &CGM,
                                           const FunctionDecl *FD) {
  if (FD->hasAttr<CUDAGlobalAttr>()) {
    const FunctionType *FT = FTy->getAs<FunctionType>();
    CGM.getTargetCodeGenInfo().setCUDAKernelCallingConvention(FT);
    FTy = FT->getCanonicalTypeUnqualified();
  }
}

/// Arrange the argument and result information for a declaration or
/// definition of the given C++ non-static member function.  The
/// member function must be an ordinary function, i.e. not a
/// constructor or destructor.
const CGFunctionInfo &
CodeGenTypes::arrangeCXXMethodDeclaration(const CXXMethodDecl *MD) {
  assert(!isa<CXXConstructorDecl>(MD) && "wrong method for constructors!");
  assert(!isa<CXXDestructorDecl>(MD) && "wrong method for destructors!");

  CanQualType FT = GetFormalType(MD).getAs<Type>();
  setCUDAKernelCallingConvention(FT, CGM, MD);
  auto prototype = FT.getAs<FunctionProtoType>();

  if (MD->isInstance()) {
    // The abstract case is perfectly fine.
    const CXXRecordDecl *ThisType = TheCXXABI.getThisArgumentTypeForMethod(MD);
    return arrangeCXXMethodType(ThisType, prototype.getTypePtr(), MD);
  }

  return arrangeFreeFunctionType(prototype);
}

bool CodeGenTypes::inheritingCtorHasParams(
    const InheritedConstructor &Inherited, CXXCtorType Type) {
  // Parameters are unnecessary if we're constructing a base class subobject
  // and the inherited constructor lives in a virtual base.
  return Type == Ctor_Complete ||
         !Inherited.getShadowDecl()->constructsVirtualBase() ||
         !Target.getCXXABI().hasConstructorVariants();
}

const CGFunctionInfo &
CodeGenTypes::arrangeCXXStructorDeclaration(GlobalDecl GD) {
  auto *MD = cast<CXXMethodDecl>(GD.getDecl());

  SmallVector<CanQualType, 16> argTypes;
  SmallVector<FunctionProtoType::ExtParameterInfo, 16> paramInfos;
  argTypes.push_back(DeriveThisType(MD->getParent(), MD));

  bool PassParams = true;

  if (auto *CD = dyn_cast<CXXConstructorDecl>(MD)) {
    // A base class inheriting constructor doesn't get forwarded arguments
    // needed to construct a virtual base (or base class thereof).
    if (auto Inherited = CD->getInheritedConstructor())
      PassParams = inheritingCtorHasParams(Inherited, GD.getCtorType());
  }

  CanQual<FunctionProtoType> FTP = GetFormalType(MD);

  // Add the formal parameters.
  if (PassParams)
    appendParameterTypes(*this, argTypes, paramInfos, FTP);

  CGCXXABI::AddedStructorArgCounts AddedArgs =
      TheCXXABI.buildStructorSignature(GD, argTypes);
  if (!paramInfos.empty()) {
    // Note: prefix implies after the first param.
    if (AddedArgs.Prefix)
      paramInfos.insert(paramInfos.begin() + 1, AddedArgs.Prefix,
                        FunctionProtoType::ExtParameterInfo{});
    if (AddedArgs.Suffix)
      paramInfos.append(AddedArgs.Suffix,
                        FunctionProtoType::ExtParameterInfo{});
  }

  RequiredArgs required =
      (PassParams && MD->isVariadic() ? RequiredArgs(argTypes.size())
                                      : RequiredArgs::All);

  FunctionType::ExtInfo extInfo = FTP->getExtInfo();
  CanQualType resultType = TheCXXABI.HasThisReturn(GD)
                               ? argTypes.front()
                               : TheCXXABI.hasMostDerivedReturn(GD)
                                     ? CGM.getContext().VoidPtrTy
                                     : Context.VoidTy;
  return arrangeLLVMFunctionInfo(resultType, /*instanceMethod=*/true,
                                 /*chainCall=*/false, argTypes, extInfo,
                                 paramInfos, required);
}

static SmallVector<CanQualType, 16>
getArgTypesForCall(ASTContext &ctx, const CallArgList &args) {
  SmallVector<CanQualType, 16> argTypes;
  for (auto &arg : args)
    argTypes.push_back(ctx.getCanonicalParamType(arg.Ty));
  return argTypes;
}

static SmallVector<CanQualType, 16>
getArgTypesForDeclaration(ASTContext &ctx, const FunctionArgList &args) {
  SmallVector<CanQualType, 16> argTypes;
  for (auto &arg : args)
    argTypes.push_back(ctx.getCanonicalParamType(arg->getType()));
  return argTypes;
}

static llvm::SmallVector<FunctionProtoType::ExtParameterInfo, 16>
getExtParameterInfosForCall(const FunctionProtoType *proto,
                            unsigned prefixArgs, unsigned totalArgs) {
  llvm::SmallVector<FunctionProtoType::ExtParameterInfo, 16> result;
  if (proto->hasExtParameterInfos()) {
    addExtParameterInfosForCall(result, proto, prefixArgs, totalArgs);
  }
  return result;
}

/// Arrange a call to a C++ method, passing the given arguments.
///
/// ExtraPrefixArgs is the number of ABI-specific args passed after the `this`
/// parameter.
/// ExtraSuffixArgs is the number of ABI-specific args passed at the end of
/// args.
/// PassProtoArgs indicates whether `args` has args for the parameters in the
/// given CXXConstructorDecl.
const CGFunctionInfo &
CodeGenTypes::arrangeCXXConstructorCall(const CallArgList &args,
                                        const CXXConstructorDecl *D,
                                        CXXCtorType CtorKind,
                                        unsigned ExtraPrefixArgs,
                                        unsigned ExtraSuffixArgs,
                                        bool PassProtoArgs) {
  // FIXME: Kill copy.
  SmallVector<CanQualType, 16> ArgTypes;
  for (const auto &Arg : args)
    ArgTypes.push_back(Context.getCanonicalParamType(Arg.Ty));

  // +1 for implicit this, which should always be args[0].
  unsigned TotalPrefixArgs = 1 + ExtraPrefixArgs;

  CanQual<FunctionProtoType> FPT = GetFormalType(D);
  RequiredArgs Required = PassProtoArgs
                              ? RequiredArgs::forPrototypePlus(
                                    FPT, TotalPrefixArgs + ExtraSuffixArgs)
                              : RequiredArgs::All;

  GlobalDecl GD(D, CtorKind);
  CanQualType ResultType = TheCXXABI.HasThisReturn(GD)
                               ? ArgTypes.front()
                               : TheCXXABI.hasMostDerivedReturn(GD)
                                     ? CGM.getContext().VoidPtrTy
                                     : Context.VoidTy;

  FunctionType::ExtInfo Info = FPT->getExtInfo();
  llvm::SmallVector<FunctionProtoType::ExtParameterInfo, 16> ParamInfos;
  // If the prototype args are elided, we should only have ABI-specific args,
  // which never have param info.
  if (PassProtoArgs && FPT->hasExtParameterInfos()) {
    // ABI-specific suffix arguments are treated the same as variadic arguments.
    addExtParameterInfosForCall(ParamInfos, FPT.getTypePtr(), TotalPrefixArgs,
                                ArgTypes.size());
  }
  return arrangeLLVMFunctionInfo(ResultType, /*instanceMethod=*/true,
                                 /*chainCall=*/false, ArgTypes, Info,
                                 ParamInfos, Required);
}

/// Arrange the argument and result information for the declaration or
/// definition of the given function.
const CGFunctionInfo &
CodeGenTypes::arrangeFunctionDeclaration(const FunctionDecl *FD) {
  if (const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(FD))
    if (MD->isInstance())
      return arrangeCXXMethodDeclaration(MD);

  CanQualType FTy = FD->getType()->getCanonicalTypeUnqualified();

  assert(isa<FunctionType>(FTy));
  setCUDAKernelCallingConvention(FTy, CGM, FD);

  // When declaring a function without a prototype, always use a
  // non-variadic type.
  if (CanQual<FunctionNoProtoType> noProto = FTy.getAs<FunctionNoProtoType>()) {
    return arrangeLLVMFunctionInfo(
        noProto->getReturnType(), /*instanceMethod=*/false,
        /*chainCall=*/false, None, noProto->getExtInfo(), {},RequiredArgs::All);
  }

  return arrangeFreeFunctionType(FTy.castAs<FunctionProtoType>());
}

/// Arrange the argument and result information for the declaration or
/// definition of an Objective-C method.
const CGFunctionInfo &
CodeGenTypes::arrangeObjCMethodDeclaration(const ObjCMethodDecl *MD) {
  // It happens that this is the same as a call with no optional
  // arguments, except also using the formal 'self' type.
  return arrangeObjCMessageSendSignature(MD, MD->getSelfDecl()->getType());
}

/// Arrange the argument and result information for the function type
/// through which to perform a send to the given Objective-C method,
/// using the given receiver type.  The receiver type is not always
/// the 'self' type of the method or even an Objective-C pointer type.
/// This is *not* the right method for actually performing such a
/// message send, due to the possibility of optional arguments.
const CGFunctionInfo &
CodeGenTypes::arrangeObjCMessageSendSignature(const ObjCMethodDecl *MD,
                                              QualType receiverType) {
  SmallVector<CanQualType, 16> argTys;
  SmallVector<FunctionProtoType::ExtParameterInfo, 4> extParamInfos(2);
  argTys.push_back(Context.getCanonicalParamType(receiverType));
  argTys.push_back(Context.getCanonicalParamType(Context.getObjCSelType()));
  // FIXME: Kill copy?
  for (const auto *I : MD->parameters()) {
    argTys.push_back(Context.getCanonicalParamType(I->getType()));
    auto extParamInfo = FunctionProtoType::ExtParameterInfo().withIsNoEscape(
        I->hasAttr<NoEscapeAttr>());
    extParamInfos.push_back(extParamInfo);
  }

  FunctionType::ExtInfo einfo;
  bool IsWindows = getContext().getTargetInfo().getTriple().isOSWindows();
  einfo = einfo.withCallingConv(getCallingConventionForDecl(MD, IsWindows));

  if (getContext().getLangOpts().ObjCAutoRefCount &&
      MD->hasAttr<NSReturnsRetainedAttr>())
    einfo = einfo.withProducesResult(true);

  RequiredArgs required =
    (MD->isVariadic() ? RequiredArgs(argTys.size()) : RequiredArgs::All);

  return arrangeLLVMFunctionInfo(
      GetReturnType(MD->getReturnType()), /*instanceMethod=*/false,
      /*chainCall=*/false, argTys, einfo, extParamInfos, required);
}

const CGFunctionInfo &
CodeGenTypes::arrangeUnprototypedObjCMessageSend(QualType returnType,
                                                 const CallArgList &args) {
  auto argTypes = getArgTypesForCall(Context, args);
  FunctionType::ExtInfo einfo;

  return arrangeLLVMFunctionInfo(
      GetReturnType(returnType), /*instanceMethod=*/false,
      /*chainCall=*/false, argTypes, einfo, {}, RequiredArgs::All);
}

const CGFunctionInfo &
CodeGenTypes::arrangeGlobalDeclaration(GlobalDecl GD) {
  // FIXME: Do we need to handle ObjCMethodDecl?
  const FunctionDecl *FD = cast<FunctionDecl>(GD.getDecl());

  if (isa<CXXConstructorDecl>(GD.getDecl()) ||
      isa<CXXDestructorDecl>(GD.getDecl()))
    return arrangeCXXStructorDeclaration(GD);

  return arrangeFunctionDeclaration(FD);
}

/// Arrange a thunk that takes 'this' as the first parameter followed by
/// varargs.  Return a void pointer, regardless of the actual return type.
/// The body of the thunk will end in a musttail call to a function of the
/// correct type, and the caller will bitcast the function to the correct
/// prototype.
const CGFunctionInfo &
CodeGenTypes::arrangeUnprototypedMustTailThunk(const CXXMethodDecl *MD) {
  assert(MD->isVirtual() && "only methods have thunks");
  CanQual<FunctionProtoType> FTP = GetFormalType(MD);
  CanQualType ArgTys[] = {DeriveThisType(MD->getParent(), MD)};
  return arrangeLLVMFunctionInfo(Context.VoidTy, /*instanceMethod=*/false,
                                 /*chainCall=*/false, ArgTys,
                                 FTP->getExtInfo(), {}, RequiredArgs(1));
}

const CGFunctionInfo &
CodeGenTypes::arrangeMSCtorClosure(const CXXConstructorDecl *CD,
                                   CXXCtorType CT) {
  assert(CT == Ctor_CopyingClosure || CT == Ctor_DefaultClosure);

  CanQual<FunctionProtoType> FTP = GetFormalType(CD);
  SmallVector<CanQualType, 2> ArgTys;
  const CXXRecordDecl *RD = CD->getParent();
  ArgTys.push_back(DeriveThisType(RD, CD));
  if (CT == Ctor_CopyingClosure)
    ArgTys.push_back(*FTP->param_type_begin());
  if (RD->getNumVBases() > 0)
    ArgTys.push_back(Context.IntTy);
  CallingConv CC = Context.getDefaultCallingConvention(
      /*IsVariadic=*/false, /*IsCXXMethod=*/true);
  return arrangeLLVMFunctionInfo(Context.VoidTy, /*instanceMethod=*/true,
                                 /*chainCall=*/false, ArgTys,
                                 FunctionType::ExtInfo(CC), {},
                                 RequiredArgs::All);
}

/// Arrange a call as unto a free function, except possibly with an
/// additional number of formal parameters considered required.
static const CGFunctionInfo &
arrangeFreeFunctionLikeCall(CodeGenTypes &CGT,
                            CodeGenModule &CGM,
                            const CallArgList &args,
                            const FunctionType *fnType,
                            unsigned numExtraRequiredArgs,
                            bool chainCall) {
  assert(args.size() >= numExtraRequiredArgs);

  llvm::SmallVector<FunctionProtoType::ExtParameterInfo, 16> paramInfos;

  // In most cases, there are no optional arguments.
  RequiredArgs required = RequiredArgs::All;

  // If we have a variadic prototype, the required arguments are the
  // extra prefix plus the arguments in the prototype.
  if (const FunctionProtoType *proto = dyn_cast<FunctionProtoType>(fnType)) {
    if (proto->isVariadic())
      required = RequiredArgs::forPrototypePlus(proto, numExtraRequiredArgs);

    if (proto->hasExtParameterInfos())
      addExtParameterInfosForCall(paramInfos, proto, numExtraRequiredArgs,
                                  args.size());

  // If we don't have a prototype at all, but we're supposed to
  // explicitly use the variadic convention for unprototyped calls,
  // treat all of the arguments as required but preserve the nominal
  // possibility of variadics.
  } else if (CGM.getTargetCodeGenInfo()
                .isNoProtoCallVariadic(args,
                                       cast<FunctionNoProtoType>(fnType))) {
    required = RequiredArgs(args.size());
  }

  // FIXME: Kill copy.
  SmallVector<CanQualType, 16> argTypes;
  for (const auto &arg : args)
    argTypes.push_back(CGT.getContext().getCanonicalParamType(arg.Ty));
  return CGT.arrangeLLVMFunctionInfo(GetReturnType(fnType->getReturnType()),
                                     /*instanceMethod=*/false, chainCall,
                                     argTypes, fnType->getExtInfo(), paramInfos,
                                     required);
}

/// Figure out the rules for calling a function with the given formal
/// type using the given arguments.  The arguments are necessary
/// because the function might be unprototyped, in which case it's
/// target-dependent in crazy ways.
const CGFunctionInfo &
CodeGenTypes::arrangeFreeFunctionCall(const CallArgList &args,
                                      const FunctionType *fnType,
                                      bool chainCall) {
  return arrangeFreeFunctionLikeCall(*this, CGM, args, fnType,
                                     chainCall ? 1 : 0, chainCall);
}

/// A block function is essentially a free function with an
/// extra implicit argument.
const CGFunctionInfo &
CodeGenTypes::arrangeBlockFunctionCall(const CallArgList &args,
                                       const FunctionType *fnType) {
  return arrangeFreeFunctionLikeCall(*this, CGM, args, fnType, 1,
                                     /*chainCall=*/false);
}

const CGFunctionInfo &
CodeGenTypes::arrangeBlockFunctionDeclaration(const FunctionProtoType *proto,
                                              const FunctionArgList &params) {
  auto paramInfos = getExtParameterInfosForCall(proto, 1, params.size());
  auto argTypes = getArgTypesForDeclaration(Context, params);

  return arrangeLLVMFunctionInfo(GetReturnType(proto->getReturnType()),
                                 /*instanceMethod*/ false, /*chainCall*/ false,
                                 argTypes, proto->getExtInfo(), paramInfos,
                                 RequiredArgs::forPrototypePlus(proto, 1));
}

const CGFunctionInfo &
CodeGenTypes::arrangeBuiltinFunctionCall(QualType resultType,
                                         const CallArgList &args) {
  // FIXME: Kill copy.
  SmallVector<CanQualType, 16> argTypes;
  for (const auto &Arg : args)
    argTypes.push_back(Context.getCanonicalParamType(Arg.Ty));
  return arrangeLLVMFunctionInfo(
      GetReturnType(resultType), /*instanceMethod=*/false,
      /*chainCall=*/false, argTypes, FunctionType::ExtInfo(),
      /*paramInfos=*/ {}, RequiredArgs::All);
}

const CGFunctionInfo &
CodeGenTypes::arrangeBuiltinFunctionDeclaration(QualType resultType,
                                                const FunctionArgList &args) {
  auto argTypes = getArgTypesForDeclaration(Context, args);

  return arrangeLLVMFunctionInfo(
      GetReturnType(resultType), /*instanceMethod=*/false, /*chainCall=*/false,
      argTypes, FunctionType::ExtInfo(), {}, RequiredArgs::All);
}

const CGFunctionInfo &
CodeGenTypes::arrangeBuiltinFunctionDeclaration(CanQualType resultType,
                                              ArrayRef<CanQualType> argTypes) {
  return arrangeLLVMFunctionInfo(
      resultType, /*instanceMethod=*/false, /*chainCall=*/false,
      argTypes, FunctionType::ExtInfo(), {}, RequiredArgs::All);
}

/// Arrange a call to a C++ method, passing the given arguments.
///
/// numPrefixArgs is the number of ABI-specific prefix arguments we have. It
/// does not count `this`.
const CGFunctionInfo &
CodeGenTypes::arrangeCXXMethodCall(const CallArgList &args,
                                   const FunctionProtoType *proto,
                                   RequiredArgs required,
                                   unsigned numPrefixArgs) {
  assert(numPrefixArgs + 1 <= args.size() &&
         "Emitting a call with less args than the required prefix?");
  // Add one to account for `this`. It's a bit awkward here, but we don't count
  // `this` in similar places elsewhere.
  auto paramInfos =
    getExtParameterInfosForCall(proto, numPrefixArgs + 1, args.size());

  // FIXME: Kill copy.
  auto argTypes = getArgTypesForCall(Context, args);

  FunctionType::ExtInfo info = proto->getExtInfo();
  return arrangeLLVMFunctionInfo(
      GetReturnType(proto->getReturnType()), /*instanceMethod=*/true,
      /*chainCall=*/false, argTypes, info, paramInfos, required);
}

const CGFunctionInfo &CodeGenTypes::arrangeNullaryFunction() {
  return arrangeLLVMFunctionInfo(
      getContext().VoidTy, /*instanceMethod=*/false, /*chainCall=*/false,
      None, FunctionType::ExtInfo(), {}, RequiredArgs::All);
}

const CGFunctionInfo &
CodeGenTypes::arrangeCall(const CGFunctionInfo &signature,
                          const CallArgList &args) {
  assert(signature.arg_size() <= args.size());
  if (signature.arg_size() == args.size())
    return signature;

  SmallVector<FunctionProtoType::ExtParameterInfo, 16> paramInfos;
  auto sigParamInfos = signature.getExtParameterInfos();
  if (!sigParamInfos.empty()) {
    paramInfos.append(sigParamInfos.begin(), sigParamInfos.end());
    paramInfos.resize(args.size());
  }

  auto argTypes = getArgTypesForCall(Context, args);

  assert(signature.getRequiredArgs().allowsOptionalArgs());
  return arrangeLLVMFunctionInfo(signature.getReturnType(),
                                 signature.isInstanceMethod(),
                                 signature.isChainCall(),
                                 argTypes,
                                 signature.getExtInfo(),
                                 paramInfos,
                                 signature.getRequiredArgs());
}

namespace clang {
namespace CodeGen {
void computeSPIRKernelABIInfo(CodeGenModule &CGM, CGFunctionInfo &FI);
}
}

/// Arrange the argument and result information for an abstract value
/// of a given function type.  This is the method which all of the
/// above functions ultimately defer to.
const CGFunctionInfo &
CodeGenTypes::arrangeLLVMFunctionInfo(CanQualType resultType,
                                      bool instanceMethod,
                                      bool chainCall,
                                      ArrayRef<CanQualType> argTypes,
                                      FunctionType::ExtInfo info,
                     ArrayRef<FunctionProtoType::ExtParameterInfo> paramInfos,
                                      RequiredArgs required) {
  assert(llvm::all_of(argTypes,
                      [](CanQualType T) { return T.isCanonicalAsParam(); }));

  // Lookup or create unique function info.
  llvm::FoldingSetNodeID ID;
  CGFunctionInfo::Profile(ID, instanceMethod, chainCall, info, paramInfos,
                          required, resultType, argTypes);

  void *insertPos = nullptr;
  CGFunctionInfo *FI = FunctionInfos.FindNodeOrInsertPos(ID, insertPos);
  if (FI)
    return *FI;

  unsigned CC = ClangCallConvToLLVMCallConv(info.getCC());

  // Construct the function info.  We co-allocate the ArgInfos.
  FI = CGFunctionInfo::create(CC, instanceMethod, chainCall, info,
                              paramInfos, resultType, argTypes, required);
  FunctionInfos.InsertNode(FI, insertPos);

  bool inserted = FunctionsBeingProcessed.insert(FI).second;
  (void)inserted;
  assert(inserted && "Recursively being processed?");

  // Compute ABI information.
  if (CC == llvm::CallingConv::SPIR_KERNEL) {
    // Force target independent argument handling for the host visible
    // kernel functions.
    computeSPIRKernelABIInfo(CGM, *FI);
  } else if (info.getCC() == CC_Swift) {
    swiftcall::computeABIInfo(CGM, *FI);
  } else {
    getABIInfo().computeInfo(*FI);
  }

  // Loop over all of the computed argument and return value info.  If any of
  // them are direct or extend without a specified coerce type, specify the
  // default now.
  ABIArgInfo &retInfo = FI->getReturnInfo();
  if (retInfo.canHaveCoerceToType() && retInfo.getCoerceToType() == nullptr)
    retInfo.setCoerceToType(ConvertType(FI->getReturnType()));

  for (auto &I : FI->arguments())
    if (I.info.canHaveCoerceToType() && I.info.getCoerceToType() == nullptr)
      I.info.setCoerceToType(ConvertType(I.type));

  bool erased = FunctionsBeingProcessed.erase(FI); (void)erased;
  assert(erased && "Not in set?");

  return *FI;
}

CGFunctionInfo *CGFunctionInfo::create(unsigned llvmCC,
                                       bool instanceMethod,
                                       bool chainCall,
                                       const FunctionType::ExtInfo &info,
                                       ArrayRef<ExtParameterInfo> paramInfos,
                                       CanQualType resultType,
                                       ArrayRef<CanQualType> argTypes,
                                       RequiredArgs required) {
  assert(paramInfos.empty() || paramInfos.size() == argTypes.size());
  assert(!required.allowsOptionalArgs() ||
         required.getNumRequiredArgs() <= argTypes.size());

  void *buffer =
    operator new(totalSizeToAlloc<ArgInfo,             ExtParameterInfo>(
                                  argTypes.size() + 1, paramInfos.size()));

  CGFunctionInfo *FI = new(buffer) CGFunctionInfo();
  FI->CallingConvention = llvmCC;
  FI->EffectiveCallingConvention = llvmCC;
  FI->ASTCallingConvention = info.getCC();
  FI->InstanceMethod = instanceMethod;
  FI->ChainCall = chainCall;
  FI->CmseNSCall = info.getCmseNSCall();
  FI->NoReturn = info.getNoReturn();
  FI->ReturnsRetained = info.getProducesResult();
  FI->NoCallerSavedRegs = info.getNoCallerSavedRegs();
  FI->NoCfCheck = info.getNoCfCheck();
  FI->Required = required;
  FI->HasRegParm = info.getHasRegParm();
  FI->RegParm = info.getRegParm();
  FI->ArgStruct = nullptr;
  FI->ArgStructAlign = 0;
  FI->NumArgs = argTypes.size();
  FI->HasExtParameterInfos = !paramInfos.empty();
  FI->getArgsBuffer()[0].type = resultType;
  for (unsigned i = 0, e = argTypes.size(); i != e; ++i)
    FI->getArgsBuffer()[i + 1].type = argTypes[i];
  for (unsigned i = 0, e = paramInfos.size(); i != e; ++i)
    FI->getExtParameterInfosBuffer()[i] = paramInfos[i];
  return FI;
}

/***/

namespace {
// ABIArgInfo::Expand implementation.

// Specifies the way QualType passed as ABIArgInfo::Expand is expanded.
struct TypeExpansion {
  enum TypeExpansionKind {
    // Elements of constant arrays are expanded recursively.
    TEK_ConstantArray,
    // Record fields are expanded recursively (but if record is a union, only
    // the field with the largest size is expanded).
    TEK_Record,
    // For complex types, real and imaginary parts are expanded recursively.
    TEK_Complex,
    // All other types are not expandable.
    TEK_None
  };

  const TypeExpansionKind Kind;

  TypeExpansion(TypeExpansionKind K) : Kind(K) {}
  virtual ~TypeExpansion() {}
};

struct ConstantArrayExpansion : TypeExpansion {
  QualType EltTy;
  uint64_t NumElts;

  ConstantArrayExpansion(QualType EltTy, uint64_t NumElts)
      : TypeExpansion(TEK_ConstantArray), EltTy(EltTy), NumElts(NumElts) {}
  static bool classof(const TypeExpansion *TE) {
    return TE->Kind == TEK_ConstantArray;
  }
};

struct RecordExpansion : TypeExpansion {
  SmallVector<const CXXBaseSpecifier *, 1> Bases;

  SmallVector<const FieldDecl *, 1> Fields;

  RecordExpansion(SmallVector<const CXXBaseSpecifier *, 1> &&Bases,
                  SmallVector<const FieldDecl *, 1> &&Fields)
      : TypeExpansion(TEK_Record), Bases(std::move(Bases)),
        Fields(std::move(Fields)) {}
  static bool classof(const TypeExpansion *TE) {
    return TE->Kind == TEK_Record;
  }
};

struct ComplexExpansion : TypeExpansion {
  QualType EltTy;

  ComplexExpansion(QualType EltTy) : TypeExpansion(TEK_Complex), EltTy(EltTy) {}
  static bool classof(const TypeExpansion *TE) {
    return TE->Kind == TEK_Complex;
  }
};

struct NoExpansion : TypeExpansion {
  NoExpansion() : TypeExpansion(TEK_None) {}
  static bool classof(const TypeExpansion *TE) {
    return TE->Kind == TEK_None;
  }
};
}  // namespace

static std::unique_ptr<TypeExpansion>
getTypeExpansion(QualType Ty, const ASTContext &Context) {
  if (const ConstantArrayType *AT = Context.getAsConstantArrayType(Ty)) {
    return std::make_unique<ConstantArrayExpansion>(
        AT->getElementType(), AT->getSize().getZExtValue());
  }
  if (const RecordType *RT = Ty->getAs<RecordType>()) {
    SmallVector<const CXXBaseSpecifier *, 1> Bases;
    SmallVector<const FieldDecl *, 1> Fields;
    const RecordDecl *RD = RT->getDecl();
    assert(!RD->hasFlexibleArrayMember() &&
           "Cannot expand structure with flexible array.");
    if (RD->isUnion()) {
      // Unions can be here only in degenerative cases - all the fields are same
      // after flattening. Thus we have to use the "largest" field.
      const FieldDecl *LargestFD = nullptr;
      CharUnits UnionSize = CharUnits::Zero();

      for (const auto *FD : RD->fields()) {
        if (FD->isZeroLengthBitField(Context))
          continue;
        assert(!FD->isBitField() &&
               "Cannot expand structure with bit-field members.");
        CharUnits FieldSize = Context.getTypeSizeInChars(FD->getType());
        if (UnionSize < FieldSize) {
          UnionSize = FieldSize;
          LargestFD = FD;
        }
      }
      if (LargestFD)
        Fields.push_back(LargestFD);
    } else {
      if (const auto *CXXRD = dyn_cast<CXXRecordDecl>(RD)) {
        assert(!CXXRD->isDynamicClass() &&
               "cannot expand vtable pointers in dynamic classes");
        for (const CXXBaseSpecifier &BS : CXXRD->bases())
          Bases.push_back(&BS);
      }

      for (const auto *FD : RD->fields()) {
        if (FD->isZeroLengthBitField(Context))
          continue;
        assert(!FD->isBitField() &&
               "Cannot expand structure with bit-field members.");
        Fields.push_back(FD);
      }
    }
    return std::make_unique<RecordExpansion>(std::move(Bases),
                                              std::move(Fields));
  }
  if (const ComplexType *CT = Ty->getAs<ComplexType>()) {
    return std::make_unique<ComplexExpansion>(CT->getElementType());
  }
  return std::make_unique<NoExpansion>();
}

static int getExpansionSize(QualType Ty, const ASTContext &Context) {
  auto Exp = getTypeExpansion(Ty, Context);
  if (auto CAExp = dyn_cast<ConstantArrayExpansion>(Exp.get())) {
    return CAExp->NumElts * getExpansionSize(CAExp->EltTy, Context);
  }
  if (auto RExp = dyn_cast<RecordExpansion>(Exp.get())) {
    int Res = 0;
    for (auto BS : RExp->Bases)
      Res += getExpansionSize(BS->getType(), Context);
    for (auto FD : RExp->Fields)
      Res += getExpansionSize(FD->getType(), Context);
    return Res;
  }
  if (isa<ComplexExpansion>(Exp.get()))
    return 2;
  assert(isa<NoExpansion>(Exp.get()));
  return 1;
}

void
CodeGenTypes::getExpandedTypes(QualType Ty,
                               SmallVectorImpl<llvm::Type *>::iterator &TI) {
  auto Exp = getTypeExpansion(Ty, Context);
  if (auto CAExp = dyn_cast<ConstantArrayExpansion>(Exp.get())) {
    for (int i = 0, n = CAExp->NumElts; i < n; i++) {
      getExpandedTypes(CAExp->EltTy, TI);
    }
  } else if (auto RExp = dyn_cast<RecordExpansion>(Exp.get())) {
    for (auto BS : RExp->Bases)
      getExpandedTypes(BS->getType(), TI);
    for (auto FD : RExp->Fields)
      getExpandedTypes(FD->getType(), TI);
  } else if (auto CExp = dyn_cast<ComplexExpansion>(Exp.get())) {
    llvm::Type *EltTy = ConvertType(CExp->EltTy);
    *TI++ = EltTy;
    *TI++ = EltTy;
  } else {
    assert(isa<NoExpansion>(Exp.get()));
    *TI++ = ConvertType(Ty);
  }
}

static void forConstantArrayExpansion(CodeGenFunction &CGF,
                                      ConstantArrayExpansion *CAE,
                                      Address BaseAddr,
                                      llvm::function_ref<void(Address)> Fn) {
  CharUnits EltSize = CGF.getContext().getTypeSizeInChars(CAE->EltTy);
  CharUnits EltAlign =
    BaseAddr.getAlignment().alignmentOfArrayElement(EltSize);

  for (int i = 0, n = CAE->NumElts; i < n; i++) {
    llvm::Value *EltAddr =
      CGF.Builder.CreateConstGEP2_32(nullptr, BaseAddr.getPointer(), 0, i);
    Fn(Address(EltAddr, EltAlign));
  }
}

void CodeGenFunction::ExpandTypeFromArgs(QualType Ty, LValue LV,
                                         llvm::Function::arg_iterator &AI) {
  assert(LV.isSimple() &&
         "Unexpected non-simple lvalue during struct expansion.");

  auto Exp = getTypeExpansion(Ty, getContext());
  if (auto CAExp = dyn_cast<ConstantArrayExpansion>(Exp.get())) {
    forConstantArrayExpansion(
        *this, CAExp, LV.getAddress(*this), [&](Address EltAddr) {
          LValue LV = MakeAddrLValue(EltAddr, CAExp->EltTy);
          ExpandTypeFromArgs(CAExp->EltTy, LV, AI);
        });
  } else if (auto RExp = dyn_cast<RecordExpansion>(Exp.get())) {
    Address This = LV.getAddress(*this);
    for (const CXXBaseSpecifier *BS : RExp->Bases) {
      // Perform a single step derived-to-base conversion.
      Address Base =
          GetAddressOfBaseClass(This, Ty->getAsCXXRecordDecl(), &BS, &BS + 1,
                                /*NullCheckValue=*/false, SourceLocation());
      LValue SubLV = MakeAddrLValue(Base, BS->getType());

      // Recurse onto bases.
      ExpandTypeFromArgs(BS->getType(), SubLV, AI);
    }
    for (auto FD : RExp->Fields) {
      // FIXME: What are the right qualifiers here?
      LValue SubLV = EmitLValueForFieldInitialization(LV, FD);
      ExpandTypeFromArgs(FD->getType(), SubLV, AI);
    }
  } else if (isa<ComplexExpansion>(Exp.get())) {
    auto realValue = &*AI++;
    auto imagValue = &*AI++;
    EmitStoreOfComplex(ComplexPairTy(realValue, imagValue), LV, /*init*/ true);
  } else {
    // Call EmitStoreOfScalar except when the lvalue is a bitfield to emit a
    // primitive store.
    assert(isa<NoExpansion>(Exp.get()));
    if (LV.isBitField())
      EmitStoreThroughLValue(RValue::get(&*AI++), LV);
    else
      EmitStoreOfScalar(&*AI++, LV);
  }
}

void CodeGenFunction::ExpandTypeToArgs(
    QualType Ty, CallArg Arg, llvm::FunctionType *IRFuncTy,
    SmallVectorImpl<llvm::Value *> &IRCallArgs, unsigned &IRCallArgPos) {
  auto Exp = getTypeExpansion(Ty, getContext());
  if (auto CAExp = dyn_cast<ConstantArrayExpansion>(Exp.get())) {
    Address Addr = Arg.hasLValue() ? Arg.getKnownLValue().getAddress(*this)
                                   : Arg.getKnownRValue().getAggregateAddress();
    forConstantArrayExpansion(
        *this, CAExp, Addr, [&](Address EltAddr) {
          CallArg EltArg = CallArg(
              convertTempToRValue(EltAddr, CAExp->EltTy, SourceLocation()),
              CAExp->EltTy);
          ExpandTypeToArgs(CAExp->EltTy, EltArg, IRFuncTy, IRCallArgs,
                           IRCallArgPos);
        });
  } else if (auto RExp = dyn_cast<RecordExpansion>(Exp.get())) {
    Address This = Arg.hasLValue() ? Arg.getKnownLValue().getAddress(*this)
                                   : Arg.getKnownRValue().getAggregateAddress();
    for (const CXXBaseSpecifier *BS : RExp->Bases) {
      // Perform a single step derived-to-base conversion.
      Address Base =
          GetAddressOfBaseClass(This, Ty->getAsCXXRecordDecl(), &BS, &BS + 1,
                                /*NullCheckValue=*/false, SourceLocation());
      CallArg BaseArg = CallArg(RValue::getAggregate(Base), BS->getType());

      // Recurse onto bases.
      ExpandTypeToArgs(BS->getType(), BaseArg, IRFuncTy, IRCallArgs,
                       IRCallArgPos);
    }

    LValue LV = MakeAddrLValue(This, Ty);
    for (auto FD : RExp->Fields) {
      CallArg FldArg =
          CallArg(EmitRValueForField(LV, FD, SourceLocation()), FD->getType());
      ExpandTypeToArgs(FD->getType(), FldArg, IRFuncTy, IRCallArgs,
                       IRCallArgPos);
    }
  } else if (isa<ComplexExpansion>(Exp.get())) {
    ComplexPairTy CV = Arg.getKnownRValue().getComplexVal();
    IRCallArgs[IRCallArgPos++] = CV.first;
    IRCallArgs[IRCallArgPos++] = CV.second;
  } else {
    assert(isa<NoExpansion>(Exp.get()));
    auto RV = Arg.getKnownRValue();
    assert(RV.isScalar() &&
           "Unexpected non-scalar rvalue during struct expansion.");

    // Insert a bitcast as needed.
    llvm::Value *V = RV.getScalarVal();
    if (IRCallArgPos < IRFuncTy->getNumParams() &&
        V->getType() != IRFuncTy->getParamType(IRCallArgPos))
      V = Builder.CreateBitCast(V, IRFuncTy->getParamType(IRCallArgPos));

    IRCallArgs[IRCallArgPos++] = V;
  }
}

/// Create a temporary allocation for the purposes of coercion.
static Address CreateTempAllocaForCoercion(CodeGenFunction &CGF, llvm::Type *Ty,
                                           CharUnits MinAlign) {
  // Don't use an alignment that's worse than what LLVM would prefer.
  auto PrefAlign = CGF.CGM.getDataLayout().getPrefTypeAlignment(Ty);
  CharUnits Align = std::max(MinAlign, CharUnits::fromQuantity(PrefAlign));

  return CGF.CreateTempAlloca(Ty, Align);
}

/// EnterStructPointerForCoercedAccess - Given a struct pointer that we are
/// accessing some number of bytes out of it, try to gep into the struct to get
/// at its inner goodness.  Dive as deep as possible without entering an element
/// with an in-memory size smaller than DstSize.
static Address
EnterStructPointerForCoercedAccess(Address SrcPtr,
                                   llvm::StructType *SrcSTy,
                                   uint64_t DstSize, CodeGenFunction &CGF) {
  // We can't dive into a zero-element struct.
  if (SrcSTy->getNumElements() == 0) return SrcPtr;

  llvm::Type *FirstElt = SrcSTy->getElementType(0);

  // If the first elt is at least as large as what we're looking for, or if the
  // first element is the same size as the whole struct, we can enter it. The
  // comparison must be made on the store size and not the alloca size. Using
  // the alloca size may overstate the size of the load.
  uint64_t FirstEltSize =
    CGF.CGM.getDataLayout().getTypeStoreSize(FirstElt);
  if (FirstEltSize < DstSize &&
      FirstEltSize < CGF.CGM.getDataLayout().getTypeStoreSize(SrcSTy))
    return SrcPtr;

  // GEP into the first element.
  SrcPtr = CGF.Builder.CreateStructGEP(SrcPtr, 0, "coerce.dive");

  // If the first element is a struct, recurse.
  llvm::Type *SrcTy = SrcPtr.getElementType();
  if (llvm::StructType *SrcSTy = dyn_cast<llvm::StructType>(SrcTy))
    return EnterStructPointerForCoercedAccess(SrcPtr, SrcSTy, DstSize, CGF);

  return SrcPtr;
}

/// CoerceIntOrPtrToIntOrPtr - Convert a value Val to the specific Ty where both
/// are either integers or pointers.  This does a truncation of the value if it
/// is too large or a zero extension if it is too small.
///
/// This behaves as if the value were coerced through memory, so on big-endian
/// targets the high bits are preserved in a truncation, while little-endian
/// targets preserve the low bits.
static llvm::Value *CoerceIntOrPtrToIntOrPtr(llvm::Value *Val,
                                             llvm::Type *Ty,
                                             CodeGenFunction &CGF) {
  if (Val->getType() == Ty)
    return Val;

  if (isa<llvm::PointerType>(Val->getType())) {
    // If this is Pointer->Pointer avoid conversion to and from int.
    if (isa<llvm::PointerType>(Ty))
      return CGF.Builder.CreateBitCast(Val, Ty, "coerce.val");

    // Convert the pointer to an integer so we can play with its width.
    Val = CGF.Builder.CreatePtrToInt(Val, CGF.IntPtrTy, "coerce.val.pi");
  }

  llvm::Type *DestIntTy = Ty;
  if (isa<llvm::PointerType>(DestIntTy))
    DestIntTy = CGF.IntPtrTy;

  if (Val->getType() != DestIntTy) {
    const llvm::DataLayout &DL = CGF.CGM.getDataLayout();
    if (DL.isBigEndian()) {
      // Preserve the high bits on big-endian targets.
      // That is what memory coercion does.
      uint64_t SrcSize = DL.getTypeSizeInBits(Val->getType());
      uint64_t DstSize = DL.getTypeSizeInBits(DestIntTy);

      if (SrcSize > DstSize) {
        Val = CGF.Builder.CreateLShr(Val, SrcSize - DstSize, "coerce.highbits");
        Val = CGF.Builder.CreateTrunc(Val, DestIntTy, "coerce.val.ii");
      } else {
        Val = CGF.Builder.CreateZExt(Val, DestIntTy, "coerce.val.ii");
        Val = CGF.Builder.CreateShl(Val, DstSize - SrcSize, "coerce.highbits");
      }
    } else {
      // Little-endian targets preserve the low bits. No shifts required.
      Val = CGF.Builder.CreateIntCast(Val, DestIntTy, false, "coerce.val.ii");
    }
  }

  if (isa<llvm::PointerType>(Ty))
    Val = CGF.Builder.CreateIntToPtr(Val, Ty, "coerce.val.ip");
  return Val;
}



/// CreateCoercedLoad - Create a load from \arg SrcPtr interpreted as
/// a pointer to an object of type \arg Ty, known to be aligned to
/// \arg SrcAlign bytes.
///
/// This safely handles the case when the src type is smaller than the
/// destination type; in this situation the values of bits which not
/// present in the src are undefined.
static llvm::Value *CreateCoercedLoad(Address Src, llvm::Type *Ty,
                                      CodeGenFunction &CGF) {
  llvm::Type *SrcTy = Src.getElementType();

  // If SrcTy and Ty are the same, just do a load.
  if (SrcTy == Ty)
    return CGF.Builder.CreateLoad(Src);

  uint64_t DstSize = CGF.CGM.getDataLayout().getTypeAllocSize(Ty);

  if (llvm::StructType *SrcSTy = dyn_cast<llvm::StructType>(SrcTy)) {
    Src = EnterStructPointerForCoercedAccess(Src, SrcSTy, DstSize, CGF);
    SrcTy = Src.getElementType();
  }

  uint64_t SrcSize = CGF.CGM.getDataLayout().getTypeAllocSize(SrcTy);

  // If the source and destination are integer or pointer types, just do an
  // extension or truncation to the desired type.
  if ((isa<llvm::IntegerType>(Ty) || isa<llvm::PointerType>(Ty)) &&
      (isa<llvm::IntegerType>(SrcTy) || isa<llvm::PointerType>(SrcTy))) {
    llvm::Value *Load = CGF.Builder.CreateLoad(Src);
    return CoerceIntOrPtrToIntOrPtr(Load, Ty, CGF);
  }

  // If load is legal, just bitcast the src pointer.
  if (SrcSize >= DstSize) {
    // Generally SrcSize is never greater than DstSize, since this means we are
    // losing bits. However, this can happen in cases where the structure has
    // additional padding, for example due to a user specified alignment.
    //
    // FIXME: Assert that we aren't truncating non-padding bits when have access
    // to that information.
    Src = CGF.Builder.CreateBitCast(Src,
                                    Ty->getPointerTo(Src.getAddressSpace()));
    return CGF.Builder.CreateLoad(Src);
  }

  // Otherwise do coercion through memory. This is stupid, but simple.
  Address Tmp = CreateTempAllocaForCoercion(CGF, Ty, Src.getAlignment());
  CGF.Builder.CreateMemCpy(Tmp.getPointer(), Tmp.getAlignment().getAsAlign(),
                           Src.getPointer(), Src.getAlignment().getAsAlign(),
                           llvm::ConstantInt::get(CGF.IntPtrTy, SrcSize));
  return CGF.Builder.CreateLoad(Tmp);
}

// Function to store a first-class aggregate into memory.  We prefer to
// store the elements rather than the aggregate to be more friendly to
// fast-isel.
// FIXME: Do we need to recurse here?
void CodeGenFunction::EmitAggregateStore(llvm::Value *Val, Address Dest,
                                         bool DestIsVolatile) {
  // Prefer scalar stores to first-class aggregate stores.
  if (llvm::StructType *STy = dyn_cast<llvm::StructType>(Val->getType())) {
    for (unsigned i = 0, e = STy->getNumElements(); i != e; ++i) {
      Address EltPtr = Builder.CreateStructGEP(Dest, i);
      llvm::Value *Elt = Builder.CreateExtractValue(Val, i);
      Builder.CreateStore(Elt, EltPtr, DestIsVolatile);
    }
  } else {
    Builder.CreateStore(Val, Dest, DestIsVolatile);
  }
}

/// CreateCoercedStore - Create a store to \arg DstPtr from \arg Src,
/// where the source and destination may have different types.  The
/// destination is known to be aligned to \arg DstAlign bytes.
///
/// This safely handles the case when the src type is larger than the
/// destination type; the upper bits of the src will be lost.
static void CreateCoercedStore(llvm::Value *Src,
                               Address Dst,
                               bool DstIsVolatile,
                               CodeGenFunction &CGF) {
  llvm::Type *SrcTy = Src->getType();
  llvm::Type *DstTy = Dst.getElementType();
  if (SrcTy == DstTy) {
    CGF.Builder.CreateStore(Src, Dst, DstIsVolatile);
    return;
  }

  uint64_t SrcSize = CGF.CGM.getDataLayout().getTypeAllocSize(SrcTy);

  if (llvm::StructType *DstSTy = dyn_cast<llvm::StructType>(DstTy)) {
    Dst = EnterStructPointerForCoercedAccess(Dst, DstSTy, SrcSize, CGF);
    DstTy = Dst.getElementType();
  }

  llvm::PointerType *SrcPtrTy = llvm::dyn_cast<llvm::PointerType>(SrcTy);
  llvm::PointerType *DstPtrTy = llvm::dyn_cast<llvm::PointerType>(DstTy);
  if (SrcPtrTy && DstPtrTy &&
      SrcPtrTy->getAddressSpace() != DstPtrTy->getAddressSpace()) {
    Src = CGF.Builder.CreatePointerBitCastOrAddrSpaceCast(Src, DstTy);
    CGF.Builder.CreateStore(Src, Dst, DstIsVolatile);
    return;
  }

  // If the source and destination are integer or pointer types, just do an
  // extension or truncation to the desired type.
  if ((isa<llvm::IntegerType>(SrcTy) || isa<llvm::PointerType>(SrcTy)) &&
      (isa<llvm::IntegerType>(DstTy) || isa<llvm::PointerType>(DstTy))) {
    Src = CoerceIntOrPtrToIntOrPtr(Src, DstTy, CGF);
    CGF.Builder.CreateStore(Src, Dst, DstIsVolatile);
    return;
  }

  uint64_t DstSize = CGF.CGM.getDataLayout().getTypeAllocSize(DstTy);

  // If store is legal, just bitcast the src pointer.
  if (SrcSize <= DstSize) {
    Dst = CGF.Builder.CreateElementBitCast(Dst, SrcTy);
    CGF.EmitAggregateStore(Src, Dst, DstIsVolatile);
  } else {
    // Otherwise do coercion through memory. This is stupid, but
    // simple.

    // Generally SrcSize is never greater than DstSize, since this means we are
    // losing bits. However, this can happen in cases where the structure has
    // additional padding, for example due to a user specified alignment.
    //
    // FIXME: Assert that we aren't truncating non-padding bits when have access
    // to that information.
    Address Tmp = CreateTempAllocaForCoercion(CGF, SrcTy, Dst.getAlignment());
    CGF.Builder.CreateStore(Src, Tmp);
    CGF.Builder.CreateMemCpy(Dst.getPointer(), Dst.getAlignment().getAsAlign(),
                             Tmp.getPointer(), Tmp.getAlignment().getAsAlign(),
                             llvm::ConstantInt::get(CGF.IntPtrTy, DstSize));
  }
}

static Address emitAddressAtOffset(CodeGenFunction &CGF, Address addr,
                                   const ABIArgInfo &info) {
  if (unsigned offset = info.getDirectOffset()) {
    addr = CGF.Builder.CreateElementBitCast(addr, CGF.Int8Ty);
    addr = CGF.Builder.CreateConstInBoundsByteGEP(addr,
                                             CharUnits::fromQuantity(offset));
    addr = CGF.Builder.CreateElementBitCast(addr, info.getCoerceToType());
  }
  return addr;
}

namespace {

/// Encapsulates information about the way function arguments from
/// CGFunctionInfo should be passed to actual LLVM IR function.
class ClangToLLVMArgMapping {
  static const unsigned InvalidIndex = ~0U;
  unsigned InallocaArgNo;
  unsigned SRetArgNo;
  unsigned TotalIRArgs;

  /// Arguments of LLVM IR function corresponding to single Clang argument.
  struct IRArgs {
    unsigned PaddingArgIndex;
    // Argument is expanded to IR arguments at positions
    // [FirstArgIndex, FirstArgIndex + NumberOfArgs).
    unsigned FirstArgIndex;
    unsigned NumberOfArgs;

    IRArgs()
        : PaddingArgIndex(InvalidIndex), FirstArgIndex(InvalidIndex),
          NumberOfArgs(0) {}
  };

  SmallVector<IRArgs, 8> ArgInfo;

public:
  ClangToLLVMArgMapping(const ASTContext &Context, const CGFunctionInfo &FI,
                        bool OnlyRequiredArgs = false)
      : InallocaArgNo(InvalidIndex), SRetArgNo(InvalidIndex), TotalIRArgs(0),
        ArgInfo(OnlyRequiredArgs ? FI.getNumRequiredArgs() : FI.arg_size()) {
    construct(Context, FI, OnlyRequiredArgs);
  }

  bool hasInallocaArg() const { return InallocaArgNo != InvalidIndex; }
  unsigned getInallocaArgNo() const {
    assert(hasInallocaArg());
    return InallocaArgNo;
  }

  bool hasSRetArg() const { return SRetArgNo != InvalidIndex; }
  unsigned getSRetArgNo() const {
    assert(hasSRetArg());
    return SRetArgNo;
  }

  unsigned totalIRArgs() const { return TotalIRArgs; }

  bool hasPaddingArg(unsigned ArgNo) const {
    assert(ArgNo < ArgInfo.size());
    return ArgInfo[ArgNo].PaddingArgIndex != InvalidIndex;
  }
  unsigned getPaddingArgNo(unsigned ArgNo) const {
    assert(hasPaddingArg(ArgNo));
    return ArgInfo[ArgNo].PaddingArgIndex;
  }

  /// Returns index of first IR argument corresponding to ArgNo, and their
  /// quantity.
  std::pair<unsigned, unsigned> getIRArgs(unsigned ArgNo) const {
    assert(ArgNo < ArgInfo.size());
    return std::make_pair(ArgInfo[ArgNo].FirstArgIndex,
                          ArgInfo[ArgNo].NumberOfArgs);
  }

private:
  void construct(const ASTContext &Context, const CGFunctionInfo &FI,
                 bool OnlyRequiredArgs);
};

void ClangToLLVMArgMapping::construct(const ASTContext &Context,
                                      const CGFunctionInfo &FI,
                                      bool OnlyRequiredArgs) {
  unsigned IRArgNo = 0;
  bool SwapThisWithSRet = false;
  const ABIArgInfo &RetAI = FI.getReturnInfo();

  if (RetAI.getKind() == ABIArgInfo::Indirect) {
    SwapThisWithSRet = RetAI.isSRetAfterThis();
    SRetArgNo = SwapThisWithSRet ? 1 : IRArgNo++;
  }

  unsigned ArgNo = 0;
  unsigned NumArgs = OnlyRequiredArgs ? FI.getNumRequiredArgs() : FI.arg_size();
  for (CGFunctionInfo::const_arg_iterator I = FI.arg_begin(); ArgNo < NumArgs;
       ++I, ++ArgNo) {
    assert(I != FI.arg_end());
    QualType ArgType = I->type;
    const ABIArgInfo &AI = I->info;
    // Collect data about IR arguments corresponding to Clang argument ArgNo.
    auto &IRArgs = ArgInfo[ArgNo];

    if (AI.getPaddingType())
      IRArgs.PaddingArgIndex = IRArgNo++;

    switch (AI.getKind()) {
    case ABIArgInfo::Extend:
    case ABIArgInfo::Direct: {
      // FIXME: handle sseregparm someday...
      llvm::StructType *STy = dyn_cast<llvm::StructType>(AI.getCoerceToType());
      if (AI.isDirect() && AI.getCanBeFlattened() && STy) {
        IRArgs.NumberOfArgs = STy->getNumElements();
      } else {
        IRArgs.NumberOfArgs = 1;
      }
      break;
    }
    case ABIArgInfo::Indirect:
    case ABIArgInfo::IndirectAliased:
      IRArgs.NumberOfArgs = 1;
      break;
    case ABIArgInfo::Ignore:
    case ABIArgInfo::InAlloca:
      // ignore and inalloca doesn't have matching LLVM parameters.
      IRArgs.NumberOfArgs = 0;
      break;
    case ABIArgInfo::CoerceAndExpand:
      IRArgs.NumberOfArgs = AI.getCoerceAndExpandTypeSequence().size();
      break;
    case ABIArgInfo::Expand:
      IRArgs.NumberOfArgs = getExpansionSize(ArgType, Context);
      break;
    }

    if (IRArgs.NumberOfArgs > 0) {
      IRArgs.FirstArgIndex = IRArgNo;
      IRArgNo += IRArgs.NumberOfArgs;
    }

    // Skip over the sret parameter when it comes second.  We already handled it
    // above.
    if (IRArgNo == 1 && SwapThisWithSRet)
      IRArgNo++;
  }
  assert(ArgNo == ArgInfo.size());

  if (FI.usesInAlloca())
    InallocaArgNo = IRArgNo++;

  TotalIRArgs = IRArgNo;
}
}  // namespace

/***/

bool CodeGenModule::ReturnTypeUsesSRet(const CGFunctionInfo &FI) {
  const auto &RI = FI.getReturnInfo();
  return RI.isIndirect() || (RI.isInAlloca() && RI.getInAllocaSRet());
}

bool CodeGenModule::ReturnSlotInterferesWithArgs(const CGFunctionInfo &FI) {
  return ReturnTypeUsesSRet(FI) &&
         getTargetCodeGenInfo().doesReturnSlotInterfereWithArgs();
}

bool CodeGenModule::ReturnTypeUsesFPRet(QualType ResultType) {
  if (const BuiltinType *BT = ResultType->getAs<BuiltinType>()) {
    switch (BT->getKind()) {
    default:
      return false;
    case BuiltinType::Float:
      return getTarget().useObjCFPRetForRealType(TargetInfo::Float);
    case BuiltinType::Double:
      return getTarget().useObjCFPRetForRealType(TargetInfo::Double);
    case BuiltinType::LongDouble:
      return getTarget().useObjCFPRetForRealType(TargetInfo::LongDouble);
    }
  }

  return false;
}

bool CodeGenModule::ReturnTypeUsesFP2Ret(QualType ResultType) {
  if (const ComplexType *CT = ResultType->getAs<ComplexType>()) {
    if (const BuiltinType *BT = CT->getElementType()->getAs<BuiltinType>()) {
      if (BT->getKind() == BuiltinType::LongDouble)
        return getTarget().useObjCFP2RetForComplexLongDouble();
    }
  }

  return false;
}

llvm::FunctionType *CodeGenTypes::GetFunctionType(GlobalDecl GD) {
  const CGFunctionInfo &FI = arrangeGlobalDeclaration(GD);
  return GetFunctionType(FI);
}

llvm::FunctionType *
CodeGenTypes::GetFunctionType(const CGFunctionInfo &FI) {

  bool Inserted = FunctionsBeingProcessed.insert(&FI).second;
  (void)Inserted;
  assert(Inserted && "Recursively being processed?");

  llvm::Type *resultType = nullptr;
  const ABIArgInfo &retAI = FI.getReturnInfo();
  switch (retAI.getKind()) {
  case ABIArgInfo::Expand:
  case ABIArgInfo::IndirectAliased:
    llvm_unreachable("Invalid ABI kind for return argument");

  case ABIArgInfo::Extend:
  case ABIArgInfo::Direct:
    resultType = retAI.getCoerceToType();
    break;

  case ABIArgInfo::InAlloca:
    if (retAI.getInAllocaSRet()) {
      // sret things on win32 aren't void, they return the sret pointer.
      QualType ret = FI.getReturnType();
      llvm::Type *ty = ConvertType(ret);
      unsigned addressSpace = Context.getTargetAddressSpace(ret);
      resultType = llvm::PointerType::get(ty, addressSpace);
    } else {
      resultType = llvm::Type::getVoidTy(getLLVMContext());
    }
    break;

  case ABIArgInfo::Indirect:
  case ABIArgInfo::Ignore:
    resultType = llvm::Type::getVoidTy(getLLVMContext());
    break;

  case ABIArgInfo::CoerceAndExpand:
    resultType = retAI.getUnpaddedCoerceAndExpandType();
    break;
  }

  ClangToLLVMArgMapping IRFunctionArgs(getContext(), FI, true);
  SmallVector<llvm::Type*, 8> ArgTypes(IRFunctionArgs.totalIRArgs());

  // Add type for sret argument.
  if (IRFunctionArgs.hasSRetArg()) {
    QualType Ret = FI.getReturnType();
    llvm::Type *Ty = ConvertType(Ret);
    unsigned AddressSpace = Context.getTargetAddressSpace(Ret);
    ArgTypes[IRFunctionArgs.getSRetArgNo()] =
        llvm::PointerType::get(Ty, AddressSpace);
  }

  // Add type for inalloca argument.
  if (IRFunctionArgs.hasInallocaArg()) {
    auto ArgStruct = FI.getArgStruct();
    assert(ArgStruct);
    ArgTypes[IRFunctionArgs.getInallocaArgNo()] = ArgStruct->getPointerTo();
  }

  // Add in all of the required arguments.
  unsigned ArgNo = 0;
  CGFunctionInfo::const_arg_iterator it = FI.arg_begin(),
                                     ie = it + FI.getNumRequiredArgs();
  for (; it != ie; ++it, ++ArgNo) {
    const ABIArgInfo &ArgInfo = it->info;

    // Insert a padding type to ensure proper alignment.
    if (IRFunctionArgs.hasPaddingArg(ArgNo))
      ArgTypes[IRFunctionArgs.getPaddingArgNo(ArgNo)] =
          ArgInfo.getPaddingType();

    unsigned FirstIRArg, NumIRArgs;
    std::tie(FirstIRArg, NumIRArgs) = IRFunctionArgs.getIRArgs(ArgNo);

    switch (ArgInfo.getKind()) {
    case ABIArgInfo::Ignore:
    case ABIArgInfo::InAlloca:
      assert(NumIRArgs == 0);
      break;

    case ABIArgInfo::Indirect: {
      assert(NumIRArgs == 1);
      // indirect arguments are always on the stack, which is alloca addr space.
      llvm::Type *LTy = ConvertTypeForMem(it->type);
      ArgTypes[FirstIRArg] = LTy->getPointerTo(
          CGM.getDataLayout().getAllocaAddrSpace());
      break;
    }
    case ABIArgInfo::IndirectAliased: {
      assert(NumIRArgs == 1);
      llvm::Type *LTy = ConvertTypeForMem(it->type);
      ArgTypes[FirstIRArg] = LTy->getPointerTo(ArgInfo.getIndirectAddrSpace());
      break;
    }
    case ABIArgInfo::Extend:
    case ABIArgInfo::Direct: {
      // Fast-isel and the optimizer generally like scalar values better than
      // FCAs, so we flatten them if this is safe to do for this argument.
      llvm::Type *argType = ArgInfo.getCoerceToType();
      llvm::StructType *st = dyn_cast<llvm::StructType>(argType);
      if (st && ArgInfo.isDirect() && ArgInfo.getCanBeFlattened()) {
        assert(NumIRArgs == st->getNumElements());
        for (unsigned i = 0, e = st->getNumElements(); i != e; ++i)
          ArgTypes[FirstIRArg + i] = st->getElementType(i);
      } else {
        assert(NumIRArgs == 1);
        ArgTypes[FirstIRArg] = argType;
      }
      break;
    }

    case ABIArgInfo::CoerceAndExpand: {
      auto ArgTypesIter = ArgTypes.begin() + FirstIRArg;
      for (auto EltTy : ArgInfo.getCoerceAndExpandTypeSequence()) {
        *ArgTypesIter++ = EltTy;
      }
      assert(ArgTypesIter == ArgTypes.begin() + FirstIRArg + NumIRArgs);
      break;
    }

    case ABIArgInfo::Expand:
      auto ArgTypesIter = ArgTypes.begin() + FirstIRArg;
      getExpandedTypes(it->type, ArgTypesIter);
      assert(ArgTypesIter == ArgTypes.begin() + FirstIRArg + NumIRArgs);
      break;
    }
  }

  bool Erased = FunctionsBeingProcessed.erase(&FI); (void)Erased;
  assert(Erased && "Not in set?");

  return llvm::FunctionType::get(resultType, ArgTypes, FI.isVariadic());
}

llvm::Type *CodeGenTypes::GetFunctionTypeForVTable(GlobalDecl GD) {
  const CXXMethodDecl *MD = cast<CXXMethodDecl>(GD.getDecl());
  const FunctionProtoType *FPT = MD->getType()->getAs<FunctionProtoType>();

  if (!isFuncTypeConvertible(FPT))
    return llvm::StructType::get(getLLVMContext());

  return GetFunctionType(GD);
}

static void AddAttributesFromFunctionProtoType(ASTContext &Ctx,
                                               llvm::AttrBuilder &FuncAttrs,
                                               const FunctionProtoType *FPT) {
  if (!FPT)
    return;

  if (!isUnresolvedExceptionSpec(FPT->getExceptionSpecType()) &&
      FPT->isNothrow())
    FuncAttrs.addAttribute(llvm::Attribute::NoUnwind);
}

void CodeGenModule::getDefaultFunctionAttributes(StringRef Name,
                                                 bool HasOptnone,
                                                 bool AttrOnCallSite,
                                               llvm::AttrBuilder &FuncAttrs) {
  // OptimizeNoneAttr takes precedence over -Os or -Oz. No warning needed.
  if (!HasOptnone) {
    if (CodeGenOpts.OptimizeSize)
      FuncAttrs.addAttribute(llvm::Attribute::OptimizeForSize);
    if (CodeGenOpts.OptimizeSize == 2)
      FuncAttrs.addAttribute(llvm::Attribute::MinSize);
  }

  if (CodeGenOpts.DisableRedZone)
    FuncAttrs.addAttribute(llvm::Attribute::NoRedZone);
  if (CodeGenOpts.IndirectTlsSegRefs)
    FuncAttrs.addAttribute("indirect-tls-seg-refs");
  if (CodeGenOpts.NoImplicitFloat)
    FuncAttrs.addAttribute(llvm::Attribute::NoImplicitFloat);

  if (AttrOnCallSite) {
    // Attributes that should go on the call site only.
    if (!CodeGenOpts.SimplifyLibCalls ||
        CodeGenOpts.isNoBuiltinFunc(Name.data()))
      FuncAttrs.addAttribute(llvm::Attribute::NoBuiltin);
    if (!CodeGenOpts.TrapFuncName.empty())
      FuncAttrs.addAttribute("trap-func-name", CodeGenOpts.TrapFuncName);
  } else {
    StringRef FpKind;
    switch (CodeGenOpts.getFramePointer()) {
    case CodeGenOptions::FramePointerKind::None:
      FpKind = "none";
      break;
    case CodeGenOptions::FramePointerKind::NonLeaf:
      FpKind = "non-leaf";
      break;
    case CodeGenOptions::FramePointerKind::All:
      FpKind = "all";
      break;
    }
    FuncAttrs.addAttribute("frame-pointer", FpKind);

    FuncAttrs.addAttribute("less-precise-fpmad",
                           llvm::toStringRef(CodeGenOpts.LessPreciseFPMAD));

    if (CodeGenOpts.NullPointerIsValid)
      FuncAttrs.addAttribute(llvm::Attribute::NullPointerIsValid);

    if (CodeGenOpts.FPDenormalMode != llvm::DenormalMode::getIEEE())
      FuncAttrs.addAttribute("denormal-fp-math",
                             CodeGenOpts.FPDenormalMode.str());
    if (CodeGenOpts.FP32DenormalMode != CodeGenOpts.FPDenormalMode) {
      FuncAttrs.addAttribute(
          "denormal-fp-math-f32",
          CodeGenOpts.FP32DenormalMode.str());
    }

    FuncAttrs.addAttribute("no-trapping-math",
                           llvm::toStringRef(LangOpts.getFPExceptionMode() ==
                                             LangOptions::FPE_Ignore));

    // Strict (compliant) code is the default, so only add this attribute to
    // indicate that we are trying to workaround a problem case.
    if (!CodeGenOpts.StrictFloatCastOverflow)
      FuncAttrs.addAttribute("strict-float-cast-overflow", "false");

    // TODO: Are these all needed?
    // unsafe/inf/nan/nsz are handled by instruction-level FastMathFlags.
    FuncAttrs.addAttribute("no-infs-fp-math",
                           llvm::toStringRef(LangOpts.NoHonorInfs));
    FuncAttrs.addAttribute("no-nans-fp-math",
                           llvm::toStringRef(LangOpts.NoHonorNaNs));
    FuncAttrs.addAttribute("unsafe-fp-math",
                           llvm::toStringRef(LangOpts.UnsafeFPMath));
    FuncAttrs.addAttribute("use-soft-float",
                           llvm::toStringRef(CodeGenOpts.SoftFloat));
    FuncAttrs.addAttribute("stack-protector-buffer-size",
                           llvm::utostr(CodeGenOpts.SSPBufferSize));
    FuncAttrs.addAttribute("no-signed-zeros-fp-math",
                           llvm::toStringRef(LangOpts.NoSignedZero));
    FuncAttrs.addAttribute(
        "correctly-rounded-divide-sqrt-fp-math",
        llvm::toStringRef(CodeGenOpts.CorrectlyRoundedDivSqrt));

    // TODO: Reciprocal estimate codegen options should apply to instructions?
    const std::vector<std::string> &Recips = CodeGenOpts.Reciprocals;
    if (!Recips.empty())
      FuncAttrs.addAttribute("reciprocal-estimates",
                             llvm::join(Recips, ","));

    if (!CodeGenOpts.PreferVectorWidth.empty() &&
        CodeGenOpts.PreferVectorWidth != "none")
      FuncAttrs.addAttribute("prefer-vector-width",
                             CodeGenOpts.PreferVectorWidth);

    if (CodeGenOpts.StackRealignment)
      FuncAttrs.addAttribute("stackrealign");
    if (CodeGenOpts.Backchain)
      FuncAttrs.addAttribute("backchain");
    if (CodeGenOpts.EnableSegmentedStacks)
      FuncAttrs.addAttribute("split-stack");

    if (CodeGenOpts.SpeculativeLoadHardening)
      FuncAttrs.addAttribute(llvm::Attribute::SpeculativeLoadHardening);
  }

  if (getLangOpts().assumeFunctionsAreConvergent()) {
    // Conservatively, mark all functions and calls in CUDA and OpenCL as
    // convergent (meaning, they may call an intrinsically convergent op, such
    // as __syncthreads() / barrier(), and so can't have certain optimizations
    // applied around them).  LLVM will remove this attribute where it safely
    // can.
    FuncAttrs.addAttribute(llvm::Attribute::Convergent);
  }

  if (getLangOpts().CUDA && getLangOpts().CUDAIsDevice) {
    // Exceptions aren't supported in CUDA device code.
    FuncAttrs.addAttribute(llvm::Attribute::NoUnwind);
  }

  for (StringRef Attr : CodeGenOpts.DefaultFunctionAttrs) {
    StringRef Var, Value;
    std::tie(Var, Value) = Attr.split('=');
    FuncAttrs.addAttribute(Var, Value);
  }
}

void CodeGenModule::addDefaultFunctionDefinitionAttributes(llvm::Function &F) {
  llvm::AttrBuilder FuncAttrs;
  getDefaultFunctionAttributes(F.getName(), F.hasOptNone(),
                               /* AttrOnCallSite = */ false, FuncAttrs);
  // TODO: call GetCPUAndFeaturesAttributes?
  F.addAttributes(llvm::AttributeList::FunctionIndex, FuncAttrs);
}

void CodeGenModule::addDefaultFunctionDefinitionAttributes(
                                                   llvm::AttrBuilder &attrs) {
  getDefaultFunctionAttributes(/*function name*/ "", /*optnone*/ false,
                               /*for call*/ false, attrs);
  GetCPUAndFeaturesAttributes(GlobalDecl(), attrs);
}

static void addNoBuiltinAttributes(llvm::AttrBuilder &FuncAttrs,
                                   const LangOptions &LangOpts,
                                   const NoBuiltinAttr *NBA = nullptr) {
  auto AddNoBuiltinAttr = [&FuncAttrs](StringRef BuiltinName) {
    SmallString<32> AttributeName;
    AttributeName += "no-builtin-";
    AttributeName += BuiltinName;
    FuncAttrs.addAttribute(AttributeName);
  };

  // First, handle the language options passed through -fno-builtin.
  if (LangOpts.NoBuiltin) {
    // -fno-builtin disables them all.
    FuncAttrs.addAttribute("no-builtins");
    return;
  }

  // Then, add attributes for builtins specified through -fno-builtin-<name>.
  llvm::for_each(LangOpts.NoBuiltinFuncs, AddNoBuiltinAttr);

  // Now, let's check the __attribute__((no_builtin("...")) attribute added to
  // the source.
  if (!NBA)
    return;

  // If there is a wildcard in the builtin names specified through the
  // attribute, disable them all.
  if (llvm::is_contained(NBA->builtinNames(), "*")) {
    FuncAttrs.addAttribute("no-builtins");
    return;
  }

  // And last, add the rest of the builtin names.
  llvm::for_each(NBA->builtinNames(), AddNoBuiltinAttr);
}

/// Construct the IR attribute list of a function or call.
///
/// When adding an attribute, please consider where it should be handled:
///
///   - getDefaultFunctionAttributes is for attributes that are essentially
///     part of the global target configuration (but perhaps can be
///     overridden on a per-function basis).  Adding attributes there
///     will cause them to also be set in frontends that build on Clang's
///     target-configuration logic, as well as for code defined in library
///     modules such as CUDA's libdevice.
///
///   - ConstructAttributeList builds on top of getDefaultFunctionAttributes
///     and adds declaration-specific, convention-specific, and
///     frontend-specific logic.  The last is of particular importance:
///     attributes that restrict how the frontend generates code must be
///     added here rather than getDefaultFunctionAttributes.
///
void CodeGenModule::ConstructAttributeList(
    StringRef Name, const CGFunctionInfo &FI, CGCalleeInfo CalleeInfo,
    llvm::AttributeList &AttrList, unsigned &CallingConv, bool AttrOnCallSite) {
  llvm::AttrBuilder FuncAttrs;
  llvm::AttrBuilder RetAttrs;

  // Collect function IR attributes from the CC lowering.
  // We'll collect the paramete and result attributes later.
  CallingConv = FI.getEffectiveCallingConvention();
  if (FI.isNoReturn())
    FuncAttrs.addAttribute(llvm::Attribute::NoReturn);
  if (FI.isCmseNSCall())
    FuncAttrs.addAttribute("cmse_nonsecure_call");

  // Collect function IR attributes from the callee prototype if we have one.
  AddAttributesFromFunctionProtoType(getContext(), FuncAttrs,
                                     CalleeInfo.getCalleeFunctionProtoType());

  const Decl *TargetDecl = CalleeInfo.getCalleeDecl().getDecl();

  bool HasOptnone = false;
  // The NoBuiltinAttr attached to the target FunctionDecl.
  const NoBuiltinAttr *NBA = nullptr;

  // Collect function IR attributes based on declaration-specific
  // information.
  // FIXME: handle sseregparm someday...
  if (TargetDecl) {
    if (TargetDecl->hasAttr<ReturnsTwiceAttr>())
      FuncAttrs.addAttribute(llvm::Attribute::ReturnsTwice);
    if (TargetDecl->hasAttr<NoThrowAttr>())
      FuncAttrs.addAttribute(llvm::Attribute::NoUnwind);
    if (TargetDecl->hasAttr<NoReturnAttr>())
      FuncAttrs.addAttribute(llvm::Attribute::NoReturn);
    if (TargetDecl->hasAttr<ColdAttr>())
      FuncAttrs.addAttribute(llvm::Attribute::Cold);
    if (TargetDecl->hasAttr<NoDuplicateAttr>())
      FuncAttrs.addAttribute(llvm::Attribute::NoDuplicate);
    if (TargetDecl->hasAttr<ConvergentAttr>())
      FuncAttrs.addAttribute(llvm::Attribute::Convergent);

    if (const FunctionDecl *Fn = dyn_cast<FunctionDecl>(TargetDecl)) {
      AddAttributesFromFunctionProtoType(
          getContext(), FuncAttrs, Fn->getType()->getAs<FunctionProtoType>());
      if (AttrOnCallSite && Fn->isReplaceableGlobalAllocationFunction()) {
        // A sane operator new returns a non-aliasing pointer.
        auto Kind = Fn->getDeclName().getCXXOverloadedOperator();
        if (getCodeGenOpts().AssumeSaneOperatorNew &&
            (Kind == OO_New || Kind == OO_Array_New))
          RetAttrs.addAttribute(llvm::Attribute::NoAlias);
      }
      const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(Fn);
      const bool IsVirtualCall = MD && MD->isVirtual();
      // Don't use [[noreturn]], _Noreturn or [[no_builtin]] for a call to a
      // virtual function. These attributes are not inherited by overloads.
      if (!(AttrOnCallSite && IsVirtualCall)) {
        if (Fn->isNoReturn())
          FuncAttrs.addAttribute(llvm::Attribute::NoReturn);
        NBA = Fn->getAttr<NoBuiltinAttr>();
      }
    }

    // 'const', 'pure' and 'noalias' attributed functions are also nounwind.
    if (TargetDecl->hasAttr<ConstAttr>()) {
      FuncAttrs.addAttribute(llvm::Attribute::ReadNone);
      FuncAttrs.addAttribute(llvm::Attribute::NoUnwind);
    } else if (TargetDecl->hasAttr<PureAttr>()) {
      FuncAttrs.addAttribute(llvm::Attribute::ReadOnly);
      FuncAttrs.addAttribute(llvm::Attribute::NoUnwind);
    } else if (TargetDecl->hasAttr<NoAliasAttr>()) {
      FuncAttrs.addAttribute(llvm::Attribute::ArgMemOnly);
      FuncAttrs.addAttribute(llvm::Attribute::NoUnwind);
    }
    if (TargetDecl->hasAttr<RestrictAttr>())
      RetAttrs.addAttribute(llvm::Attribute::NoAlias);
    if (TargetDecl->hasAttr<ReturnsNonNullAttr>() &&
        !CodeGenOpts.NullPointerIsValid)
      RetAttrs.addAttribute(llvm::Attribute::NonNull);
    if (TargetDecl->hasAttr<AnyX86NoCallerSavedRegistersAttr>())
      FuncAttrs.addAttribute("no_caller_saved_registers");
    if (TargetDecl->hasAttr<AnyX86NoCfCheckAttr>())
      FuncAttrs.addAttribute(llvm::Attribute::NoCfCheck);

    HasOptnone = TargetDecl->hasAttr<OptimizeNoneAttr>();
    if (auto *AllocSize = TargetDecl->getAttr<AllocSizeAttr>()) {
      Optional<unsigned> NumElemsParam;
      if (AllocSize->getNumElemsParam().isValid())
        NumElemsParam = AllocSize->getNumElemsParam().getLLVMIndex();
      FuncAttrs.addAllocSizeAttr(AllocSize->getElemSizeParam().getLLVMIndex(),
                                 NumElemsParam);
    }

    if (TargetDecl->hasAttr<OpenCLKernelAttr>()) {
      if (getLangOpts().OpenCLVersion <= 120) {
        // OpenCL v1.2 Work groups are always uniform
        FuncAttrs.addAttribute("uniform-work-group-size", "true");
      } else {
        // OpenCL v2.0 Work groups may be whether uniform or not.
        // '-cl-uniform-work-group-size' compile option gets a hint
        // to the compiler that the global work-size be a multiple of
        // the work-group size specified to clEnqueueNDRangeKernel
        // (i.e. work groups are uniform).
        FuncAttrs.addAttribute("uniform-work-group-size",
                               llvm::toStringRef(CodeGenOpts.UniformWGSize));
      }
    }
  }

  // Attach "no-builtins" attributes to:
  // * call sites: both `nobuiltin` and "no-builtins" or "no-builtin-<name>".
  // * definitions: "no-builtins" or "no-builtin-<name>" only.
  // The attributes can come from:
  // * LangOpts: -ffreestanding, -fno-builtin, -fno-builtin-<name>
  // * FunctionDecl attributes: __attribute__((no_builtin(...)))
  addNoBuiltinAttributes(FuncAttrs, getLangOpts(), NBA);

  // Collect function IR attributes based on global settiings.
  getDefaultFunctionAttributes(Name, HasOptnone, AttrOnCallSite, FuncAttrs);

  // Override some default IR attributes based on declaration-specific
  // information.
  if (TargetDecl) {
    if (TargetDecl->hasAttr<NoSpeculativeLoadHardeningAttr>())
      FuncAttrs.removeAttribute(llvm::Attribute::SpeculativeLoadHardening);
    if (TargetDecl->hasAttr<SpeculativeLoadHardeningAttr>())
      FuncAttrs.addAttribute(llvm::Attribute::SpeculativeLoadHardening);
    if (TargetDecl->hasAttr<NoSplitStackAttr>())
      FuncAttrs.removeAttribute("split-stack");

    // Add NonLazyBind attribute to function declarations when -fno-plt
    // is used.
    // FIXME: what if we just haven't processed the function definition
    // yet, or if it's an external definition like C99 inline?
    if (CodeGenOpts.NoPLT) {
      if (auto *Fn = dyn_cast<FunctionDecl>(TargetDecl)) {
        if (!Fn->isDefined() && !AttrOnCallSite) {
          FuncAttrs.addAttribute(llvm::Attribute::NonLazyBind);
        }
      }
    }
  }

  // Collect non-call-site function IR attributes from declaration-specific
  // information.
  if (!AttrOnCallSite) {
    if (TargetDecl && TargetDecl->hasAttr<CmseNSEntryAttr>())
      FuncAttrs.addAttribute("cmse_nonsecure_entry");

    // Whether tail calls are enabled.
    auto shouldDisableTailCalls = [&] {
      // Should this be honored in getDefaultFunctionAttributes?
      if (CodeGenOpts.DisableTailCalls)
        return true;

      if (!TargetDecl)
        return false;

      if (TargetDecl->hasAttr<DisableTailCallsAttr>() ||
          TargetDecl->hasAttr<AnyX86InterruptAttr>())
        return true;

      if (CodeGenOpts.NoEscapingBlockTailCalls) {
        if (const auto *BD = dyn_cast<BlockDecl>(TargetDecl))
          if (!BD->doesNotEscape())
            return true;
      }

      return false;
    };
    FuncAttrs.addAttribute("disable-tail-calls",
                           llvm::toStringRef(shouldDisableTailCalls()));

    // CPU/feature overrides.  addDefaultFunctionDefinitionAttributes
    // handles these separately to set them based on the global defaults.
    GetCPUAndFeaturesAttributes(CalleeInfo.getCalleeDecl(), FuncAttrs);
  }

  // Collect attributes from arguments and return values.
  ClangToLLVMArgMapping IRFunctionArgs(getContext(), FI);

  QualType RetTy = FI.getReturnType();
  const ABIArgInfo &RetAI = FI.getReturnInfo();
  switch (RetAI.getKind()) {
  case ABIArgInfo::Extend:
    if (RetAI.isSignExt())
      RetAttrs.addAttribute(llvm::Attribute::SExt);
    else
      RetAttrs.addAttribute(llvm::Attribute::ZExt);
    LLVM_FALLTHROUGH;
  case ABIArgInfo::Direct:
    if (RetAI.getInReg())
      RetAttrs.addAttribute(llvm::Attribute::InReg);
    break;
  case ABIArgInfo::Ignore:
    break;

  case ABIArgInfo::InAlloca:
  case ABIArgInfo::Indirect: {
    // inalloca and sret disable readnone and readonly
    FuncAttrs.removeAttribute(llvm::Attribute::ReadOnly)
      .removeAttribute(llvm::Attribute::ReadNone);
    break;
  }

  case ABIArgInfo::CoerceAndExpand:
    break;

  case ABIArgInfo::Expand:
  case ABIArgInfo::IndirectAliased:
    llvm_unreachable("Invalid ABI kind for return argument");
  }

  if (const auto *RefTy = RetTy->getAs<ReferenceType>()) {
    QualType PTy = RefTy->getPointeeType();
    if (!PTy->isIncompleteType() && PTy->isConstantSizeType())
      RetAttrs.addDereferenceableAttr(
          getMinimumObjectSize(PTy).getQuantity());
    if (getContext().getTargetAddressSpace(PTy) == 0 &&
        !CodeGenOpts.NullPointerIsValid)
      RetAttrs.addAttribute(llvm::Attribute::NonNull);
    if (PTy->isObjectType()) {
      llvm::Align Alignment =
          getNaturalPointeeTypeAlignment(RetTy).getAsAlign();
      RetAttrs.addAlignmentAttr(Alignment);
    }
  }

  bool hasUsedSRet = false;
  SmallVector<llvm::AttributeSet, 4> ArgAttrs(IRFunctionArgs.totalIRArgs());

  // Attach attributes to sret.
  if (IRFunctionArgs.hasSRetArg()) {
    llvm::AttrBuilder SRETAttrs;
    SRETAttrs.addAttribute(llvm::Attribute::StructRet);
    hasUsedSRet = true;
    if (RetAI.getInReg())
      SRETAttrs.addAttribute(llvm::Attribute::InReg);
    SRETAttrs.addAlignmentAttr(RetAI.getIndirectAlign().getQuantity());
    ArgAttrs[IRFunctionArgs.getSRetArgNo()] =
        llvm::AttributeSet::get(getLLVMContext(), SRETAttrs);
  }

  // Attach attributes to inalloca argument.
  if (IRFunctionArgs.hasInallocaArg()) {
    llvm::AttrBuilder Attrs;
    Attrs.addAttribute(llvm::Attribute::InAlloca);
    ArgAttrs[IRFunctionArgs.getInallocaArgNo()] =
        llvm::AttributeSet::get(getLLVMContext(), Attrs);
  }
  
  if (TargetDecl) {
    bool sr0 = 0 < ArgAttrs.size() && ArgAttrs[0].hasAttribute(llvm::Attribute::StructRet);
    auto sr1 = 1 < ArgAttrs.size() && ArgAttrs[1].hasAttribute(llvm::Attribute::StructRet);
    for(auto Attr: TargetDecl->attrs()) {
        if (isa<LLVMARGAttr>(Attr) || isa<LLVMRETAttr>(Attr) || isa<LLVMFNAttr>(Attr)) {
            std::pair<StringRef, StringRef> AttributeAndValue;
            int Index;

            if (auto RetAttr = dyn_cast<LLVMRETAttr>(Attr)) {
                AttributeAndValue = RetAttr->getAttrName().split('=');
                Index = llvm::AttributeList::ReturnIndex;
            } else if (auto ArgAttr = dyn_cast<LLVMARGAttr>(Attr)) {
                AttributeAndValue = ArgAttr->getAttrName().split('=');
                Index = llvm::AttributeList::FirstArgIndex + ArgAttr->getParamIndex();
                if (sr1 && Index>=1) Index++;
                if (sr0) Index++;
            } else if (auto ArgAttr = dyn_cast<LLVMFNAttr>(Attr)) {
                AttributeAndValue = ArgAttr->getAttrName().split('=');
                Index = -1;
            } else assert(0 && "must be llvm ret or arg attribute");
            
            llvm::Attribute::AttrKind AttrKind = llvm::Attribute::parseAttrKind(AttributeAndValue.first);
            if (AttrKind != llvm::Attribute::None) {
                assert(AttributeAndValue.second.size() == 0 && "Enum Attribute cannot have value");
                if (Index == -1) {
                  FuncAttrs.addAttribute(AttrKind);
                } else if (Index == llvm::AttributeList::ReturnIndex) {
                  RetAttrs.addAttribute(AttrKind);
                } else {
                  assert(Index - llvm::AttributeList::FirstArgIndex < ArgAttrs.size());
                  assert(Index - llvm::AttributeList::FirstArgIndex >= 0);
                  ArgAttrs[Index - llvm::AttributeList::FirstArgIndex] =
                    ArgAttrs[Index - llvm::AttributeList::FirstArgIndex].addAttribute(getLLVMContext(), AttrKind);
                }
            }
            else {
                if (Index == -1) {
                  FuncAttrs.addAttribute(AttributeAndValue.first, AttributeAndValue.second);
                } else if (Index == llvm::AttributeList::ReturnIndex) {
                  RetAttrs.addAttribute(AttributeAndValue.first, AttributeAndValue.second);
                } else {
                  assert(Index - llvm::AttributeList::FirstArgIndex < ArgAttrs.size());
                  assert(Index - llvm::AttributeList::FirstArgIndex >= 0);
                  ArgAttrs[Index - llvm::AttributeList::FirstArgIndex] = ArgAttrs[Index - llvm::AttributeList::FirstArgIndex].addAttribute(getLLVMContext(), AttributeAndValue.first, AttributeAndValue.second);
                }
            }
        }
    }
  }


  unsigned ArgNo = 0;
  for (CGFunctionInfo::const_arg_iterator I = FI.arg_begin(),
                                          E = FI.arg_end();
       I != E; ++I, ++ArgNo) {
    QualType ParamType = I->type;
    const ABIArgInfo &AI = I->info;
    llvm::AttrBuilder Attrs;

    // Add attribute for padding argument, if necessary.
    if (IRFunctionArgs.hasPaddingArg(ArgNo)) {
      if (AI.getPaddingInReg()) {
        ArgAttrs[IRFunctionArgs.getPaddingArgNo(ArgNo)] =
            llvm::AttributeSet::get(
                getLLVMContext(),
                llvm::AttrBuilder().addAttribute(llvm::Attribute::InReg));
      }
    }

    // 'restrict' -> 'noalias' is done in EmitFunctionProlog when we
    // have the corresponding parameter variable.  It doesn't make
    // sense to do it here because parameters are so messed up.
    switch (AI.getKind()) {
    case ABIArgInfo::Extend:
      if (AI.isSignExt())
        Attrs.addAttribute(llvm::Attribute::SExt);
      else
        Attrs.addAttribute(llvm::Attribute::ZExt);
      LLVM_FALLTHROUGH;
    case ABIArgInfo::Direct:
      if (ArgNo == 0 && FI.isChainCall())
        Attrs.addAttribute(llvm::Attribute::Nest);
      else if (AI.getInReg())
        Attrs.addAttribute(llvm::Attribute::InReg);
      break;

    case ABIArgInfo::Indirect: {
      if (AI.getInReg())
        Attrs.addAttribute(llvm::Attribute::InReg);

      if (AI.getIndirectByVal())
        Attrs.addByValAttr(getTypes().ConvertTypeForMem(ParamType));

      // TODO: We could add the byref attribute if not byval, but it would
      // require updating many testcases.

      CharUnits Align = AI.getIndirectAlign();

      // In a byval argument, it is important that the required
      // alignment of the type is honored, as LLVM might be creating a
      // *new* stack object, and needs to know what alignment to give
      // it. (Sometimes it can deduce a sensible alignment on its own,
      // but not if clang decides it must emit a packed struct, or the
      // user specifies increased alignment requirements.)
      //
      // This is different from indirect *not* byval, where the object
      // exists already, and the align attribute is purely
      // informative.
      assert(!Align.isZero());

      // For now, only add this when we have a byval argument.
      // TODO: be less lazy about updating test cases.
      if (AI.getIndirectByVal())
        Attrs.addAlignmentAttr(Align.getQuantity());

      // byval disables readnone and readonly.
      FuncAttrs.removeAttribute(llvm::Attribute::ReadOnly)
        .removeAttribute(llvm::Attribute::ReadNone);

      break;
    }
    case ABIArgInfo::IndirectAliased: {
      CharUnits Align = AI.getIndirectAlign();
      Attrs.addByRefAttr(getTypes().ConvertTypeForMem(ParamType));
      Attrs.addAlignmentAttr(Align.getQuantity());
      break;
    }
    case ABIArgInfo::Ignore:
    case ABIArgInfo::Expand:
    case ABIArgInfo::CoerceAndExpand:
      break;

    case ABIArgInfo::InAlloca:
      // inalloca disables readnone and readonly.
      FuncAttrs.removeAttribute(llvm::Attribute::ReadOnly)
          .removeAttribute(llvm::Attribute::ReadNone);
      continue;
    }

    if (const auto *RefTy = ParamType->getAs<ReferenceType>()) {
      QualType PTy = RefTy->getPointeeType();
      if (!PTy->isIncompleteType() && PTy->isConstantSizeType())
        Attrs.addDereferenceableAttr(
            getMinimumObjectSize(PTy).getQuantity());
      if (getContext().getTargetAddressSpace(PTy) == 0 &&
          !CodeGenOpts.NullPointerIsValid)
        Attrs.addAttribute(llvm::Attribute::NonNull);
      if (PTy->isObjectType()) {
        llvm::Align Alignment =
            getNaturalPointeeTypeAlignment(ParamType).getAsAlign();
        Attrs.addAlignmentAttr(Alignment);
      }
    }

    switch (FI.getExtParameterInfo(ArgNo).getABI()) {
    case ParameterABI::Ordinary:
      break;

    case ParameterABI::SwiftIndirectResult: {
      // Add 'sret' if we haven't already used it for something, but
      // only if the result is void.
      if (!hasUsedSRet && RetTy->isVoidType()) {
        Attrs.addAttribute(llvm::Attribute::StructRet);
        hasUsedSRet = true;
      }

      // Add 'noalias' in either case.
      Attrs.addAttribute(llvm::Attribute::NoAlias);

      // Add 'dereferenceable' and 'alignment'.
      auto PTy = ParamType->getPointeeType();
      if (!PTy->isIncompleteType() && PTy->isConstantSizeType()) {
        auto info = getContext().getTypeInfoInChars(PTy);
        Attrs.addDereferenceableAttr(info.first.getQuantity());
        Attrs.addAlignmentAttr(info.second.getAsAlign());
      }
      break;
    }

    case ParameterABI::SwiftErrorResult:
      Attrs.addAttribute(llvm::Attribute::SwiftError);
      break;

    case ParameterABI::SwiftContext:
      Attrs.addAttribute(llvm::Attribute::SwiftSelf);
      break;
    }

    if (FI.getExtParameterInfo(ArgNo).isNoEscape())
      Attrs.addAttribute(llvm::Attribute::NoCapture);

    if (Attrs.hasAttributes()) {
      unsigned FirstIRArg, NumIRArgs;
      std::tie(FirstIRArg, NumIRArgs) = IRFunctionArgs.getIRArgs(ArgNo);
      for (unsigned i = 0; i < NumIRArgs; i++)
        ArgAttrs[FirstIRArg + i] =
            llvm::AttributeSet::get(getLLVMContext(), Attrs);
    }
  }
  assert(ArgNo == FI.arg_size());

  AttrList = llvm::AttributeList::get(
      getLLVMContext(), llvm::AttributeSet::get(getLLVMContext(), FuncAttrs),
      llvm::AttributeSet::get(getLLVMContext(), RetAttrs), ArgAttrs);
}

/// An argument came in as a promoted argument; demote it back to its
/// declared type.
static llvm::Value *emitArgumentDemotion(CodeGenFunction &CGF,
                                         const VarDecl *var,
                                         llvm::Value *value) {
  llvm::Type *varType = CGF.ConvertType(var->getType());

  // This can happen with promotions that actually don't change the
  // underlying type, like the enum promotions.
  if (value->getType() == varType) return value;

  assert((varType->isIntegerTy() || varType->isFloatingPointTy())
         && "unexpected promotion type");

  if (isa<llvm::IntegerType>(varType))
    return CGF.Builder.CreateTrunc(value, varType, "arg.unpromote");

  return CGF.Builder.CreateFPCast(value, varType, "arg.unpromote");
}

/// Returns the attribute (either parameter attribute, or function
/// attribute), which declares argument ArgNo to be non-null.
static const NonNullAttr *getNonNullAttr(const Decl *FD, const ParmVarDecl *PVD,
                                         QualType ArgType, unsigned ArgNo) {
  // FIXME: __attribute__((nonnull)) can also be applied to:
  //   - references to pointers, where the pointee is known to be
  //     nonnull (apparently a Clang extension)
  //   - transparent unions containing pointers
  // In the former case, LLVM IR cannot represent the constraint. In
  // the latter case, we have no guarantee that the transparent union
  // is in fact passed as a pointer.
  if (!ArgType->isAnyPointerType() && !ArgType->isBlockPointerType())
    return nullptr;
  // First, check attribute on parameter itself.
  if (PVD) {
    if (auto ParmNNAttr = PVD->getAttr<NonNullAttr>())
      return ParmNNAttr;
  }
  // Check function attributes.
  if (!FD)
    return nullptr;
  for (const auto *NNAttr : FD->specific_attrs<NonNullAttr>()) {
    if (NNAttr->isNonNull(ArgNo))
      return NNAttr;
  }
  return nullptr;
}

namespace {
  struct CopyBackSwiftError final : EHScopeStack::Cleanup {
    Address Temp;
    Address Arg;
    CopyBackSwiftError(Address temp, Address arg) : Temp(temp), Arg(arg) {}
    void Emit(CodeGenFunction &CGF, Flags flags) override {
      llvm::Value *errorValue = CGF.Builder.CreateLoad(Temp);
      CGF.Builder.CreateStore(errorValue, Arg);
    }
  };
}

void CodeGenFunction::EmitFunctionProlog(const CGFunctionInfo &FI,
                                         llvm::Function *Fn,
                                         const FunctionArgList &Args) {
  if (CurCodeDecl && CurCodeDecl->hasAttr<NakedAttr>())
    // Naked functions don't have prologues.
    return;

  // If this is an implicit-return-zero function, go ahead and
  // initialize the return value.  TODO: it might be nice to have
  // a more general mechanism for this that didn't require synthesized
  // return statements.
  if (const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(CurCodeDecl)) {
    if (FD->hasImplicitReturnZero()) {
      QualType RetTy = FD->getReturnType().getUnqualifiedType();
      llvm::Type* LLVMTy = CGM.getTypes().ConvertType(RetTy);
      llvm::Constant* Zero = llvm::Constant::getNullValue(LLVMTy);
      Builder.CreateStore(Zero, ReturnValue);
    }
  }

  // FIXME: We no longer need the types from FunctionArgList; lift up and
  // simplify.

  ClangToLLVMArgMapping IRFunctionArgs(CGM.getContext(), FI);
  assert(Fn->arg_size() == IRFunctionArgs.totalIRArgs());

  // If we're using inalloca, all the memory arguments are GEPs off of the last
  // parameter, which is a pointer to the complete memory area.
  Address ArgStruct = Address::invalid();
  if (IRFunctionArgs.hasInallocaArg()) {
    ArgStruct = Address(Fn->getArg(IRFunctionArgs.getInallocaArgNo()),
                        FI.getArgStructAlignment());

    assert(ArgStruct.getType() == FI.getArgStruct()->getPointerTo());
  }

  // Name the struct return parameter.
  if (IRFunctionArgs.hasSRetArg()) {
    auto AI = Fn->getArg(IRFunctionArgs.getSRetArgNo());
    AI->setName("agg.result");
    AI->addAttr(llvm::Attribute::NoAlias);
  }

  // Track if we received the parameter as a pointer (indirect, byval, or
  // inalloca).  If already have a pointer, EmitParmDecl doesn't need to copy it
  // into a local alloca for us.
  SmallVector<ParamValue, 16> ArgVals;
  ArgVals.reserve(Args.size());

  // Create a pointer value for every parameter declaration.  This usually
  // entails copying one or more LLVM IR arguments into an alloca.  Don't push
  // any cleanups or do anything that might unwind.  We do that separately, so
  // we can push the cleanups in the correct order for the ABI.
  assert(FI.arg_size() == Args.size() &&
         "Mismatch between function signature & arguments.");
  unsigned ArgNo = 0;
  CGFunctionInfo::const_arg_iterator info_it = FI.arg_begin();
  for (FunctionArgList::const_iterator i = Args.begin(), e = Args.end();
       i != e; ++i, ++info_it, ++ArgNo) {
    const VarDecl *Arg = *i;
    const ABIArgInfo &ArgI = info_it->info;

    bool isPromoted =
      isa<ParmVarDecl>(Arg) && cast<ParmVarDecl>(Arg)->isKNRPromoted();
    // We are converting from ABIArgInfo type to VarDecl type directly, unless
    // the parameter is promoted. In this case we convert to
    // CGFunctionInfo::ArgInfo type with subsequent argument demotion.
    QualType Ty = isPromoted ? info_it->type : Arg->getType();
    assert(hasScalarEvaluationKind(Ty) ==
           hasScalarEvaluationKind(Arg->getType()));

    unsigned FirstIRArg, NumIRArgs;
    std::tie(FirstIRArg, NumIRArgs) = IRFunctionArgs.getIRArgs(ArgNo);

    switch (ArgI.getKind()) {
    case ABIArgInfo::InAlloca: {
      assert(NumIRArgs == 0);
      auto FieldIndex = ArgI.getInAllocaFieldIndex();
      Address V =
          Builder.CreateStructGEP(ArgStruct, FieldIndex, Arg->getName());
      if (ArgI.getInAllocaIndirect())
        V = Address(Builder.CreateLoad(V),
                    getContext().getTypeAlignInChars(Ty));
      ArgVals.push_back(ParamValue::forIndirect(V));
      break;
    }

    case ABIArgInfo::Indirect:
    case ABIArgInfo::IndirectAliased: {
      assert(NumIRArgs == 1);
      Address ParamAddr =
          Address(Fn->getArg(FirstIRArg), ArgI.getIndirectAlign());

      if (!hasScalarEvaluationKind(Ty)) {
        // Aggregates and complex variables are accessed by reference. All we
        // need to do is realign the value, if requested. Also, if the address
        // may be aliased, copy it to ensure that the parameter variable is
        // mutable and has a unique adress, as C requires.
        Address V = ParamAddr;
        if (ArgI.getIndirectRealign() || ArgI.isIndirectAliased()) {
          Address AlignedTemp = CreateMemTemp(Ty, "coerce");

          // Copy from the incoming argument pointer to the temporary with the
          // appropriate alignment.
          //
          // FIXME: We should have a common utility for generating an aggregate
          // copy.
          CharUnits Size = getContext().getTypeSizeInChars(Ty);
          Builder.CreateMemCpy(
              AlignedTemp.getPointer(), AlignedTemp.getAlignment().getAsAlign(),
              ParamAddr.getPointer(), ParamAddr.getAlignment().getAsAlign(),
              llvm::ConstantInt::get(IntPtrTy, Size.getQuantity()));
          V = AlignedTemp;
        }
        ArgVals.push_back(ParamValue::forIndirect(V));
      } else {
        // Load scalar value from indirect argument.
        llvm::Value *V =
            EmitLoadOfScalar(ParamAddr, false, Ty, Arg->getBeginLoc());

        if (isPromoted)
          V = emitArgumentDemotion(*this, Arg, V);
        ArgVals.push_back(ParamValue::forDirect(V));
      }
      break;
    }

    case ABIArgInfo::Extend:
    case ABIArgInfo::Direct: {
      auto AI = Fn->getArg(FirstIRArg);
      llvm::Type *LTy = ConvertType(Arg->getType());

      // Prepare parameter attributes. So far, only attributes for pointer
      // parameters are prepared. See
      // http://llvm.org/docs/LangRef.html#paramattrs.
      if (ArgI.getDirectOffset() == 0 && LTy->isPointerTy() &&
          ArgI.getCoerceToType()->isPointerTy()) {
        assert(NumIRArgs == 1);

        if (const ParmVarDecl *PVD = dyn_cast<ParmVarDecl>(Arg)) {
          // Set `nonnull` attribute if any.
          if (getNonNullAttr(CurCodeDecl, PVD, PVD->getType(),
                             PVD->getFunctionScopeIndex()) &&
              !CGM.getCodeGenOpts().NullPointerIsValid)
            AI->addAttr(llvm::Attribute::NonNull);

          QualType OTy = PVD->getOriginalType();
          if (const auto *ArrTy =
              getContext().getAsConstantArrayType(OTy)) {
            // A C99 array parameter declaration with the static keyword also
            // indicates dereferenceability, and if the size is constant we can
            // use the dereferenceable attribute (which requires the size in
            // bytes).
            if (ArrTy->getSizeModifier() == ArrayType::Static) {
              QualType ETy = ArrTy->getElementType();
              llvm::Align Alignment =
                  CGM.getNaturalTypeAlignment(ETy).getAsAlign();
              AI->addAttrs(llvm::AttrBuilder().addAlignmentAttr(Alignment));
              uint64_t ArrSize = ArrTy->getSize().getZExtValue();
              if (!ETy->isIncompleteType() && ETy->isConstantSizeType() &&
                  ArrSize) {
                llvm::AttrBuilder Attrs;
                Attrs.addDereferenceableAttr(
                    getContext().getTypeSizeInChars(ETy).getQuantity() *
                    ArrSize);
                AI->addAttrs(Attrs);
              } else if (getContext().getTargetInfo().getNullPointerValue(
                             ETy.getAddressSpace()) == 0 &&
                         !CGM.getCodeGenOpts().NullPointerIsValid) {
                AI->addAttr(llvm::Attribute::NonNull);
              }
            }
          } else if (const auto *ArrTy =
                     getContext().getAsVariableArrayType(OTy)) {
            // For C99 VLAs with the static keyword, we don't know the size so
            // we can't use the dereferenceable attribute, but in addrspace(0)
            // we know that it must be nonnull.
            if (ArrTy->getSizeModifier() == VariableArrayType::Static) {
              QualType ETy = ArrTy->getElementType();
              llvm::Align Alignment =
                  CGM.getNaturalTypeAlignment(ETy).getAsAlign();
              AI->addAttrs(llvm::AttrBuilder().addAlignmentAttr(Alignment));
              if (!getContext().getTargetAddressSpace(ETy) &&
                  !CGM.getCodeGenOpts().NullPointerIsValid)
                AI->addAttr(llvm::Attribute::NonNull);
            }
          }

          // Set `align` attribute if any.
          const auto *AVAttr = PVD->getAttr<AlignValueAttr>();
          if (!AVAttr)
            if (const auto *TOTy = dyn_cast<TypedefType>(OTy))
              AVAttr = TOTy->getDecl()->getAttr<AlignValueAttr>();
          if (AVAttr && !SanOpts.has(SanitizerKind::Alignment)) {
            // If alignment-assumption sanitizer is enabled, we do *not* add
            // alignment attribute here, but emit normal alignment assumption,
            // so the UBSAN check could function.
            llvm::ConstantInt *AlignmentCI =
                cast<llvm::ConstantInt>(EmitScalarExpr(AVAttr->getAlignment()));
            unsigned AlignmentInt =
                AlignmentCI->getLimitedValue(llvm::Value::MaximumAlignment);
            if (AI->getParamAlign().valueOrOne() < AlignmentInt) {
              AI->removeAttr(llvm::Attribute::AttrKind::Alignment);
              AI->addAttrs(llvm::AttrBuilder().addAlignmentAttr(
                  llvm::Align(AlignmentInt)));
            }
          }
        }

        // Set 'noalias' if an argument type has the `restrict` qualifier.
        if (Arg->getType().isRestrictQualified())
          AI->addAttr(llvm::Attribute::NoAlias);
      }

      // Prepare the argument value. If we have the trivial case, handle it
      // with no muss and fuss.
      if (!isa<llvm::StructType>(ArgI.getCoerceToType()) &&
          ArgI.getCoerceToType() == ConvertType(Ty) &&
          ArgI.getDirectOffset() == 0) {
        assert(NumIRArgs == 1);

        // LLVM expects swifterror parameters to be used in very restricted
        // ways.  Copy the value into a less-restricted temporary.
        llvm::Value *V = AI;
        if (FI.getExtParameterInfo(ArgNo).getABI()
              == ParameterABI::SwiftErrorResult) {
          QualType pointeeTy = Ty->getPointeeType();
          assert(pointeeTy->isPointerType());
          Address temp =
            CreateMemTemp(pointeeTy, getPointerAlign(), "swifterror.temp");
          Address arg = Address(V, getContext().getTypeAlignInChars(pointeeTy));
          llvm::Value *incomingErrorValue = Builder.CreateLoad(arg);
          Builder.CreateStore(incomingErrorValue, temp);
          V = temp.getPointer();

          // Push a cleanup to copy the value back at the end of the function.
          // The convention does not guarantee that the value will be written
          // back if the function exits with an unwind exception.
          EHStack.pushCleanup<CopyBackSwiftError>(NormalCleanup, temp, arg);
        }

        // Ensure the argument is the correct type.
        if (V->getType() != ArgI.getCoerceToType())
          V = Builder.CreateBitCast(V, ArgI.getCoerceToType());

        if (isPromoted)
          V = emitArgumentDemotion(*this, Arg, V);

        // Because of merging of function types from multiple decls it is
        // possible for the type of an argument to not match the corresponding
        // type in the function type. Since we are codegening the callee
        // in here, add a cast to the argument type.
        llvm::Type *LTy = ConvertType(Arg->getType());
        if (V->getType() != LTy)
          V = Builder.CreateBitCast(V, LTy);

        ArgVals.push_back(ParamValue::forDirect(V));
        break;
      }

      Address Alloca = CreateMemTemp(Ty, getContext().getDeclAlign(Arg),
                                     Arg->getName());

      // Pointer to store into.
      Address Ptr = emitAddressAtOffset(*this, Alloca, ArgI);

      // Fast-isel and the optimizer generally like scalar values better than
      // FCAs, so we flatten them if this is safe to do for this argument.
      llvm::StructType *STy = dyn_cast<llvm::StructType>(ArgI.getCoerceToType());
      if (ArgI.isDirect() && ArgI.getCanBeFlattened() && STy &&
          STy->getNumElements() > 1) {
        uint64_t SrcSize = CGM.getDataLayout().getTypeAllocSize(STy);
        llvm::Type *DstTy = Ptr.getElementType();
        uint64_t DstSize = CGM.getDataLayout().getTypeAllocSize(DstTy);

        Address AddrToStoreInto = Address::invalid();
        if (SrcSize <= DstSize) {
          AddrToStoreInto = Builder.CreateElementBitCast(Ptr, STy);
        } else {
          AddrToStoreInto =
            CreateTempAlloca(STy, Alloca.getAlignment(), "coerce");
        }

        assert(STy->getNumElements() == NumIRArgs);
        for (unsigned i = 0, e = STy->getNumElements(); i != e; ++i) {
          auto AI = Fn->getArg(FirstIRArg + i);
          AI->setName(Arg->getName() + ".coerce" + Twine(i));
          Address EltPtr = Builder.CreateStructGEP(AddrToStoreInto, i);
          Builder.CreateStore(AI, EltPtr);
        }

        if (SrcSize > DstSize) {
          Builder.CreateMemCpy(Ptr, AddrToStoreInto, DstSize);
        }

      } else {
        // Simple case, just do a coerced store of the argument into the alloca.
        assert(NumIRArgs == 1);
        auto AI = Fn->getArg(FirstIRArg);
        AI->setName(Arg->getName() + ".coerce");
        CreateCoercedStore(AI, Ptr, /*DstIsVolatile=*/false, *this);
      }

      // Match to what EmitParmDecl is expecting for this type.
      if (CodeGenFunction::hasScalarEvaluationKind(Ty)) {
        llvm::Value *V =
            EmitLoadOfScalar(Alloca, false, Ty, Arg->getBeginLoc());
        if (isPromoted)
          V = emitArgumentDemotion(*this, Arg, V);
        ArgVals.push_back(ParamValue::forDirect(V));
      } else {
        ArgVals.push_back(ParamValue::forIndirect(Alloca));
      }
      break;
    }

    case ABIArgInfo::CoerceAndExpand: {
      // Reconstruct into a temporary.
      Address alloca = CreateMemTemp(Ty, getContext().getDeclAlign(Arg));
      ArgVals.push_back(ParamValue::forIndirect(alloca));

      auto coercionType = ArgI.getCoerceAndExpandType();
      alloca = Builder.CreateElementBitCast(alloca, coercionType);

      unsigned argIndex = FirstIRArg;
      for (unsigned i = 0, e = coercionType->getNumElements(); i != e; ++i) {
        llvm::Type *eltType = coercionType->getElementType(i);
        if (ABIArgInfo::isPaddingForCoerceAndExpand(eltType))
          continue;

        auto eltAddr = Builder.CreateStructGEP(alloca, i);
        auto elt = Fn->getArg(argIndex++);
        Builder.CreateStore(elt, eltAddr);
      }
      assert(argIndex == FirstIRArg + NumIRArgs);
      break;
    }

    case ABIArgInfo::Expand: {
      // If this structure was expanded into multiple arguments then
      // we need to create a temporary and reconstruct it from the
      // arguments.
      Address Alloca = CreateMemTemp(Ty, getContext().getDeclAlign(Arg));
      LValue LV = MakeAddrLValue(Alloca, Ty);
      ArgVals.push_back(ParamValue::forIndirect(Alloca));

      auto FnArgIter = Fn->arg_begin() + FirstIRArg;
      ExpandTypeFromArgs(Ty, LV, FnArgIter);
      assert(FnArgIter == Fn->arg_begin() + FirstIRArg + NumIRArgs);
      for (unsigned i = 0, e = NumIRArgs; i != e; ++i) {
        auto AI = Fn->getArg(FirstIRArg + i);
        AI->setName(Arg->getName() + "." + Twine(i));
      }
      break;
    }

    case ABIArgInfo::Ignore:
      assert(NumIRArgs == 0);
      // Initialize the local variable appropriately.
      if (!hasScalarEvaluationKind(Ty)) {
        ArgVals.push_back(ParamValue::forIndirect(CreateMemTemp(Ty)));
      } else {
        llvm::Value *U = llvm::UndefValue::get(ConvertType(Arg->getType()));
        ArgVals.push_back(ParamValue::forDirect(U));
      }
      break;
    }
  }

  if (getTarget().getCXXABI().areArgsDestroyedLeftToRightInCallee()) {
    for (int I = Args.size() - 1; I >= 0; --I)
      EmitParmDecl(*Args[I], ArgVals[I], I + 1);
  } else {
    for (unsigned I = 0, E = Args.size(); I != E; ++I)
      EmitParmDecl(*Args[I], ArgVals[I], I + 1);
  }
}

static void eraseUnusedBitCasts(llvm::Instruction *insn) {
  while (insn->use_empty()) {
    llvm::BitCastInst *bitcast = dyn_cast<llvm::BitCastInst>(insn);
    if (!bitcast) return;

    // This is "safe" because we would have used a ConstantExpr otherwise.
    insn = cast<llvm::Instruction>(bitcast->getOperand(0));
    bitcast->eraseFromParent();
  }
}

/// Try to emit a fused autorelease of a return result.
static llvm::Value *tryEmitFusedAutoreleaseOfResult(CodeGenFunction &CGF,
                                                    llvm::Value *result) {
  // We must be immediately followed the cast.
  llvm::BasicBlock *BB = CGF.Builder.GetInsertBlock();
  if (BB->empty()) return nullptr;
  if (&BB->back() != result) return nullptr;

  llvm::Type *resultType = result->getType();

  // result is in a BasicBlock and is therefore an Instruction.
  llvm::Instruction *generator = cast<llvm::Instruction>(result);

  SmallVector<llvm::Instruction *, 4> InstsToKill;

  // Look for:
  //  %generator = bitcast %type1* %generator2 to %type2*
  while (llvm::BitCastInst *bitcast = dyn_cast<llvm::BitCastInst>(generator)) {
    // We would have emitted this as a constant if the operand weren't
    // an Instruction.
    generator = cast<llvm::Instruction>(bitcast->getOperand(0));

    // Require the generator to be immediately followed by the cast.
    if (generator->getNextNode() != bitcast)
      return nullptr;

    InstsToKill.push_back(bitcast);
  }

  // Look for:
  //   %generator = call i8* @objc_retain(i8* %originalResult)
  // or
  //   %generator = call i8* @objc_retainAutoreleasedReturnValue(i8* %originalResult)
  llvm::CallInst *call = dyn_cast<llvm::CallInst>(generator);
  if (!call) return nullptr;

  bool doRetainAutorelease;

  if (call->getCalledOperand() == CGF.CGM.getObjCEntrypoints().objc_retain) {
    doRetainAutorelease = true;
  } else if (call->getCalledOperand() ==
             CGF.CGM.getObjCEntrypoints().objc_retainAutoreleasedReturnValue) {
    doRetainAutorelease = false;

    // If we emitted an assembly marker for this call (and the
    // ARCEntrypoints field should have been set if so), go looking
    // for that call.  If we can't find it, we can't do this
    // optimization.  But it should always be the immediately previous
    // instruction, unless we needed bitcasts around the call.
    if (CGF.CGM.getObjCEntrypoints().retainAutoreleasedReturnValueMarker) {
      llvm::Instruction *prev = call->getPrevNode();
      assert(prev);
      if (isa<llvm::BitCastInst>(prev)) {
        prev = prev->getPrevNode();
        assert(prev);
      }
      assert(isa<llvm::CallInst>(prev));
      assert(cast<llvm::CallInst>(prev)->getCalledOperand() ==
             CGF.CGM.getObjCEntrypoints().retainAutoreleasedReturnValueMarker);
      InstsToKill.push_back(prev);
    }
  } else {
    return nullptr;
  }

  result = call->getArgOperand(0);
  InstsToKill.push_back(call);

  // Keep killing bitcasts, for sanity.  Note that we no longer care
  // about precise ordering as long as there's exactly one use.
  while (llvm::BitCastInst *bitcast = dyn_cast<llvm::BitCastInst>(result)) {
    if (!bitcast->hasOneUse()) break;
    InstsToKill.push_back(bitcast);
    result = bitcast->getOperand(0);
  }

  // Delete all the unnecessary instructions, from latest to earliest.
  for (auto *I : InstsToKill)
    I->eraseFromParent();

  // Do the fused retain/autorelease if we were asked to.
  if (doRetainAutorelease)
    result = CGF.EmitARCRetainAutoreleaseReturnValue(result);

  // Cast back to the result type.
  return CGF.Builder.CreateBitCast(result, resultType);
}

/// If this is a +1 of the value of an immutable 'self', remove it.
static llvm::Value *tryRemoveRetainOfSelf(CodeGenFunction &CGF,
                                          llvm::Value *result) {
  // This is only applicable to a method with an immutable 'self'.
  const ObjCMethodDecl *method =
    dyn_cast_or_null<ObjCMethodDecl>(CGF.CurCodeDecl);
  if (!method) return nullptr;
  const VarDecl *self = method->getSelfDecl();
  if (!self->getType().isConstQualified()) return nullptr;

  // Look for a retain call.
  llvm::CallInst *retainCall =
    dyn_cast<llvm::CallInst>(result->stripPointerCasts());
  if (!retainCall || retainCall->getCalledOperand() !=
                         CGF.CGM.getObjCEntrypoints().objc_retain)
    return nullptr;

  // Look for an ordinary load of 'self'.
  llvm::Value *retainedValue = retainCall->getArgOperand(0);
  llvm::LoadInst *load =
    dyn_cast<llvm::LoadInst>(retainedValue->stripPointerCasts());
  if (!load || load->isAtomic() || load->isVolatile() ||
      load->getPointerOperand() != CGF.GetAddrOfLocalVar(self).getPointer())
    return nullptr;

  // Okay!  Burn it all down.  This relies for correctness on the
  // assumption that the retain is emitted as part of the return and
  // that thereafter everything is used "linearly".
  llvm::Type *resultType = result->getType();
  eraseUnusedBitCasts(cast<llvm::Instruction>(result));
  assert(retainCall->use_empty());
  retainCall->eraseFromParent();
  eraseUnusedBitCasts(cast<llvm::Instruction>(retainedValue));

  return CGF.Builder.CreateBitCast(load, resultType);
}

/// Emit an ARC autorelease of the result of a function.
///
/// \return the value to actually return from the function
static llvm::Value *emitAutoreleaseOfResult(CodeGenFunction &CGF,
                                            llvm::Value *result) {
  // If we're returning 'self', kill the initial retain.  This is a
  // heuristic attempt to "encourage correctness" in the really unfortunate
  // case where we have a return of self during a dealloc and we desperately
  // need to avoid the possible autorelease.
  if (llvm::Value *self = tryRemoveRetainOfSelf(CGF, result))
    return self;

  // At -O0, try to emit a fused retain/autorelease.
  if (CGF.shouldUseFusedARCCalls())
    if (llvm::Value *fused = tryEmitFusedAutoreleaseOfResult(CGF, result))
      return fused;

  return CGF.EmitARCAutoreleaseReturnValue(result);
}

/// Heuristically search for a dominating store to the return-value slot.
static llvm::StoreInst *findDominatingStoreToReturnValue(CodeGenFunction &CGF) {
  // Check if a User is a store which pointerOperand is the ReturnValue.
  // We are looking for stores to the ReturnValue, not for stores of the
  // ReturnValue to some other location.
  auto GetStoreIfValid = [&CGF](llvm::User *U) -> llvm::StoreInst * {
    auto *SI = dyn_cast<llvm::StoreInst>(U);
    if (!SI || SI->getPointerOperand() != CGF.ReturnValue.getPointer())
      return nullptr;
    // These aren't actually possible for non-coerced returns, and we
    // only care about non-coerced returns on this code path.
    assert(!SI->isAtomic() && !SI->isVolatile());
    return SI;
  };
  // If there are multiple uses of the return-value slot, just check
  // for something immediately preceding the IP.  Sometimes this can
  // happen with how we generate implicit-returns; it can also happen
  // with noreturn cleanups.
  if (!CGF.ReturnValue.getPointer()->hasOneUse()) {
    llvm::BasicBlock *IP = CGF.Builder.GetInsertBlock();
    if (IP->empty()) return nullptr;
    llvm::Instruction *I = &IP->back();

    // Skip lifetime markers
    for (llvm::BasicBlock::reverse_iterator II = IP->rbegin(),
                                            IE = IP->rend();
         II != IE; ++II) {
      if (llvm::IntrinsicInst *Intrinsic =
              dyn_cast<llvm::IntrinsicInst>(&*II)) {
        if (Intrinsic->getIntrinsicID() == llvm::Intrinsic::lifetime_end) {
          const llvm::Value *CastAddr = Intrinsic->getArgOperand(1);
          ++II;
          if (II == IE)
            break;
          if (isa<llvm::BitCastInst>(&*II) && (CastAddr == &*II))
            continue;
        }
      }
      I = &*II;
      break;
    }

    return GetStoreIfValid(I);
  }

  llvm::StoreInst *store =
      GetStoreIfValid(CGF.ReturnValue.getPointer()->user_back());
  if (!store) return nullptr;

  // Now do a first-and-dirty dominance check: just walk up the
  // single-predecessors chain from the current insertion point.
  llvm::BasicBlock *StoreBB = store->getParent();
  llvm::BasicBlock *IP = CGF.Builder.GetInsertBlock();
  while (IP != StoreBB) {
    if (!(IP = IP->getSinglePredecessor()))
      return nullptr;
  }

  // Okay, the store's basic block dominates the insertion point; we
  // can do our thing.
  return store;
}

// Helper functions for EmitCMSEClearRecord

// Set the bits corresponding to a field having width `BitWidth` and located at
// offset `BitOffset` (from the least significant bit) within a storage unit of
// `Bits.size()` bytes. Each element of `Bits` corresponds to one target byte.
// Use little-endian layout, i.e.`Bits[0]` is the LSB.
static void setBitRange(SmallVectorImpl<uint64_t> &Bits, int BitOffset,
                        int BitWidth, int CharWidth) {
  assert(CharWidth <= 64);
  assert(static_cast<unsigned>(BitWidth) <= Bits.size() * CharWidth);

  int Pos = 0;
  if (BitOffset >= CharWidth) {
    Pos += BitOffset / CharWidth;
    BitOffset = BitOffset % CharWidth;
  }

  const uint64_t Used = (uint64_t(1) << CharWidth) - 1;
  if (BitOffset + BitWidth >= CharWidth) {
    Bits[Pos++] |= (Used << BitOffset) & Used;
    BitWidth -= CharWidth - BitOffset;
    BitOffset = 0;
  }

  while (BitWidth >= CharWidth) {
    Bits[Pos++] = Used;
    BitWidth -= CharWidth;
  }

  if (BitWidth > 0)
    Bits[Pos++] |= (Used >> (CharWidth - BitWidth)) << BitOffset;
}

// Set the bits corresponding to a field having width `BitWidth` and located at
// offset `BitOffset` (from the least significant bit) within a storage unit of
// `StorageSize` bytes, located at `StorageOffset` in `Bits`. Each element of
// `Bits` corresponds to one target byte. Use target endian layout.
static void setBitRange(SmallVectorImpl<uint64_t> &Bits, int StorageOffset,
                        int StorageSize, int BitOffset, int BitWidth,
                        int CharWidth, bool BigEndian) {

  SmallVector<uint64_t, 8> TmpBits(StorageSize);
  setBitRange(TmpBits, BitOffset, BitWidth, CharWidth);

  if (BigEndian)
    std::reverse(TmpBits.begin(), TmpBits.end());

  for (uint64_t V : TmpBits)
    Bits[StorageOffset++] |= V;
}

static void setUsedBits(CodeGenModule &, QualType, int,
                        SmallVectorImpl<uint64_t> &);

// Set the bits in `Bits`, which correspond to the value representations of
// the actual members of the record type `RTy`. Note that this function does
// not handle base classes, virtual tables, etc, since they cannot happen in
// CMSE function arguments or return. The bit mask corresponds to the target
// memory layout, i.e. it's endian dependent.
static void setUsedBits(CodeGenModule &CGM, const RecordType *RTy, int Offset,
                        SmallVectorImpl<uint64_t> &Bits) {
  ASTContext &Context = CGM.getContext();
  int CharWidth = Context.getCharWidth();
  const RecordDecl *RD = RTy->getDecl()->getDefinition();
  const ASTRecordLayout &ASTLayout = Context.getASTRecordLayout(RD);
  const CGRecordLayout &Layout = CGM.getTypes().getCGRecordLayout(RD);

  int Idx = 0;
  for (auto I = RD->field_begin(), E = RD->field_end(); I != E; ++I, ++Idx) {
    const FieldDecl *F = *I;

    if (F->isUnnamedBitfield() || F->isZeroLengthBitField(Context) ||
        F->getType()->isIncompleteArrayType())
      continue;

    if (F->isBitField()) {
      const CGBitFieldInfo &BFI = Layout.getBitFieldInfo(F);
      setBitRange(Bits, Offset + BFI.StorageOffset.getQuantity(),
                  BFI.StorageSize / CharWidth, BFI.Offset,
                  BFI.Size, CharWidth,
                  CGM.getDataLayout().isBigEndian());
      continue;
    }

    setUsedBits(CGM, F->getType(),
                Offset + ASTLayout.getFieldOffset(Idx) / CharWidth, Bits);
  }
}

// Set the bits in `Bits`, which correspond to the value representations of
// the elements of an array type `ATy`.
static void setUsedBits(CodeGenModule &CGM, const ConstantArrayType *ATy,
                        int Offset, SmallVectorImpl<uint64_t> &Bits) {
  const ASTContext &Context = CGM.getContext();

  QualType ETy = Context.getBaseElementType(ATy);
  int Size = Context.getTypeSizeInChars(ETy).getQuantity();
  SmallVector<uint64_t, 4> TmpBits(Size);
  setUsedBits(CGM, ETy, 0, TmpBits);

  for (int I = 0, N = Context.getConstantArrayElementCount(ATy); I < N; ++I) {
    auto Src = TmpBits.begin();
    auto Dst = Bits.begin() + Offset + I * Size;
    for (int J = 0; J < Size; ++J)
      *Dst++ |= *Src++;
  }
}

// Set the bits in `Bits`, which correspond to the value representations of
// the type `QTy`.
static void setUsedBits(CodeGenModule &CGM, QualType QTy, int Offset,
                        SmallVectorImpl<uint64_t> &Bits) {
  if (const auto *RTy = QTy->getAs<RecordType>())
    return setUsedBits(CGM, RTy, Offset, Bits);

  ASTContext &Context = CGM.getContext();
  if (const auto *ATy = Context.getAsConstantArrayType(QTy))
    return setUsedBits(CGM, ATy, Offset, Bits);

  int Size = Context.getTypeSizeInChars(QTy).getQuantity();
  if (Size <= 0)
    return;

  std::fill_n(Bits.begin() + Offset, Size,
              (uint64_t(1) << Context.getCharWidth()) - 1);
}

static uint64_t buildMultiCharMask(const SmallVectorImpl<uint64_t> &Bits,
                                   int Pos, int Size, int CharWidth,
                                   bool BigEndian) {
  assert(Size > 0);
  uint64_t Mask = 0;
  if (BigEndian) {
    for (auto P = Bits.begin() + Pos, E = Bits.begin() + Pos + Size; P != E;
         ++P)
      Mask = (Mask << CharWidth) | *P;
  } else {
    auto P = Bits.begin() + Pos + Size, End = Bits.begin() + Pos;
    do
      Mask = (Mask << CharWidth) | *--P;
    while (P != End);
  }
  return Mask;
}

// Emit code to clear the bits in a record, which aren't a part of any user
// declared member, when the record is a function return.
llvm::Value *CodeGenFunction::EmitCMSEClearRecord(llvm::Value *Src,
                                                  llvm::IntegerType *ITy,
                                                  QualType QTy) {
  assert(Src->getType() == ITy);
  assert(ITy->getScalarSizeInBits() <= 64);

  const llvm::DataLayout &DataLayout = CGM.getDataLayout();
  int Size = DataLayout.getTypeStoreSize(ITy);
  SmallVector<uint64_t, 4> Bits(Size);
  setUsedBits(CGM, QTy->getAs<RecordType>(), 0, Bits);

  int CharWidth = CGM.getContext().getCharWidth();
  uint64_t Mask =
      buildMultiCharMask(Bits, 0, Size, CharWidth, DataLayout.isBigEndian());

  return Builder.CreateAnd(Src, Mask, "cmse.clear");
}

// Emit code to clear the bits in a record, which aren't a part of any user
// declared member, when the record is a function argument.
llvm::Value *CodeGenFunction::EmitCMSEClearRecord(llvm::Value *Src,
                                                  llvm::ArrayType *ATy,
                                                  QualType QTy) {
  const llvm::DataLayout &DataLayout = CGM.getDataLayout();
  int Size = DataLayout.getTypeStoreSize(ATy);
  SmallVector<uint64_t, 16> Bits(Size);
  setUsedBits(CGM, QTy->getAs<RecordType>(), 0, Bits);

  // Clear each element of the LLVM array.
  int CharWidth = CGM.getContext().getCharWidth();
  int CharsPerElt =
      ATy->getArrayElementType()->getScalarSizeInBits() / CharWidth;
  int MaskIndex = 0;
  llvm::Value *R = llvm::UndefValue::get(ATy);
  for (int I = 0, N = ATy->getArrayNumElements(); I != N; ++I) {
    uint64_t Mask = buildMultiCharMask(Bits, MaskIndex, CharsPerElt, CharWidth,
                                       DataLayout.isBigEndian());
    MaskIndex += CharsPerElt;
    llvm::Value *T0 = Builder.CreateExtractValue(Src, I);
    llvm::Value *T1 = Builder.CreateAnd(T0, Mask, "cmse.clear");
    R = Builder.CreateInsertValue(R, T1, I);
  }

  return R;
}

void CodeGenFunction::EmitFunctionEpilog(const CGFunctionInfo &FI,
                                         bool EmitRetDbgLoc,
                                         SourceLocation EndLoc) {
  if (FI.isNoReturn()) {
    // Noreturn functions don't return.
    EmitUnreachable(EndLoc);
    return;
  }

  if (CurCodeDecl && CurCodeDecl->hasAttr<NakedAttr>()) {
    // Naked functions don't have epilogues.
    Builder.CreateUnreachable();
    return;
  }

  // Functions with no result always return void.
  if (!ReturnValue.isValid()) {
    Builder.CreateRetVoid();
    return;
  }

  llvm::DebugLoc RetDbgLoc;
  llvm::Value *RV = nullptr;
  QualType RetTy = FI.getReturnType();
  const ABIArgInfo &RetAI = FI.getReturnInfo();

  switch (RetAI.getKind()) {
  case ABIArgInfo::InAlloca:
    // Aggregrates get evaluated directly into the destination.  Sometimes we
    // need to return the sret value in a register, though.
    assert(hasAggregateEvaluationKind(RetTy));
    if (RetAI.getInAllocaSRet()) {
      llvm::Function::arg_iterator EI = CurFn->arg_end();
      --EI;
      llvm::Value *ArgStruct = &*EI;
      llvm::Value *SRet = Builder.CreateStructGEP(
          nullptr, ArgStruct, RetAI.getInAllocaFieldIndex());
      RV = Builder.CreateAlignedLoad(SRet, getPointerAlign(), "sret");
    }
    break;

  case ABIArgInfo::Indirect: {
    auto AI = CurFn->arg_begin();
    if (RetAI.isSRetAfterThis())
      ++AI;
    switch (getEvaluationKind(RetTy)) {
    case TEK_Complex: {
      ComplexPairTy RT =
        EmitLoadOfComplex(MakeAddrLValue(ReturnValue, RetTy), EndLoc);
      EmitStoreOfComplex(RT, MakeNaturalAlignAddrLValue(&*AI, RetTy),
                         /*isInit*/ true);
      break;
    }
    case TEK_Aggregate:
      // Do nothing; aggregrates get evaluated directly into the destination.
      break;
    case TEK_Scalar:
      EmitStoreOfScalar(Builder.CreateLoad(ReturnValue),
                        MakeNaturalAlignAddrLValue(&*AI, RetTy),
                        /*isInit*/ true);
      break;
    }
    break;
  }

  case ABIArgInfo::Extend:
  case ABIArgInfo::Direct:
    if (RetAI.getCoerceToType() == ConvertType(RetTy) &&
        RetAI.getDirectOffset() == 0) {
      // The internal return value temp always will have pointer-to-return-type
      // type, just do a load.

      // If there is a dominating store to ReturnValue, we can elide
      // the load, zap the store, and usually zap the alloca.
      if (llvm::StoreInst *SI =
              findDominatingStoreToReturnValue(*this)) {
        // Reuse the debug location from the store unless there is
        // cleanup code to be emitted between the store and return
        // instruction.
        if (EmitRetDbgLoc && !AutoreleaseResult)
          RetDbgLoc = SI->getDebugLoc();
        // Get the stored value and nuke the now-dead store.
        RV = SI->getValueOperand();
        SI->eraseFromParent();

      // Otherwise, we have to do a simple load.
      } else {
        RV = Builder.CreateLoad(ReturnValue);
      }
    } else {
      // If the value is offset in memory, apply the offset now.
      Address V = emitAddressAtOffset(*this, ReturnValue, RetAI);

      RV = CreateCoercedLoad(V, RetAI.getCoerceToType(), *this);
    }

    // In ARC, end functions that return a retainable type with a call
    // to objc_autoreleaseReturnValue.
    if (AutoreleaseResult) {
#ifndef NDEBUG
      // Type::isObjCRetainabletype has to be called on a QualType that hasn't
      // been stripped of the typedefs, so we cannot use RetTy here. Get the
      // original return type of FunctionDecl, CurCodeDecl, and BlockDecl from
      // CurCodeDecl or BlockInfo.
      QualType RT;

      if (auto *FD = dyn_cast<FunctionDecl>(CurCodeDecl))
        RT = FD->getReturnType();
      else if (auto *MD = dyn_cast<ObjCMethodDecl>(CurCodeDecl))
        RT = MD->getReturnType();
      else if (isa<BlockDecl>(CurCodeDecl))
        RT = BlockInfo->BlockExpression->getFunctionType()->getReturnType();
      else
        llvm_unreachable("Unexpected function/method type");

      assert(getLangOpts().ObjCAutoRefCount &&
             !FI.isReturnsRetained() &&
             RT->isObjCRetainableType());
#endif
      RV = emitAutoreleaseOfResult(*this, RV);
    }

    break;

  case ABIArgInfo::Ignore:
    break;

  case ABIArgInfo::CoerceAndExpand: {
    auto coercionType = RetAI.getCoerceAndExpandType();

    // Load all of the coerced elements out into results.
    llvm::SmallVector<llvm::Value*, 4> results;
    Address addr = Builder.CreateElementBitCast(ReturnValue, coercionType);
    for (unsigned i = 0, e = coercionType->getNumElements(); i != e; ++i) {
      auto coercedEltType = coercionType->getElementType(i);
      if (ABIArgInfo::isPaddingForCoerceAndExpand(coercedEltType))
        continue;

      auto eltAddr = Builder.CreateStructGEP(addr, i);
      auto elt = Builder.CreateLoad(eltAddr);
      results.push_back(elt);
    }

    // If we have one result, it's the single direct result type.
    if (results.size() == 1) {
      RV = results[0];

    // Otherwise, we need to make a first-class aggregate.
    } else {
      // Construct a return type that lacks padding elements.
      llvm::Type *returnType = RetAI.getUnpaddedCoerceAndExpandType();

      RV = llvm::UndefValue::get(returnType);
      for (unsigned i = 0, e = results.size(); i != e; ++i) {
        RV = Builder.CreateInsertValue(RV, results[i], i);
      }
    }
    break;
  }
  case ABIArgInfo::Expand:
  case ABIArgInfo::IndirectAliased:
    llvm_unreachable("Invalid ABI kind for return argument");
  }

  llvm::Instruction *Ret;
  if (RV) {
    if (CurFuncDecl && CurFuncDecl->hasAttr<CmseNSEntryAttr>()) {
      // For certain return types, clear padding bits, as they may reveal
      // sensitive information.
      // Small struct/union types are passed as integers.
      auto *ITy = dyn_cast<llvm::IntegerType>(RV->getType());
      if (ITy != nullptr && isa<RecordType>(RetTy.getCanonicalType()))
        RV = EmitCMSEClearRecord(RV, ITy, RetTy);
    }
    EmitReturnValueCheck(RV);
    Ret = Builder.CreateRet(RV);
  } else {
    Ret = Builder.CreateRetVoid();
  }

  if (RetDbgLoc)
    Ret->setDebugLoc(std::move(RetDbgLoc));
}

void CodeGenFunction::EmitReturnValueCheck(llvm::Value *RV) {
  // A current decl may not be available when emitting vtable thunks.
  if (!CurCodeDecl)
    return;

  // If the return block isn't reachable, neither is this check, so don't emit
  // it.
  if (ReturnBlock.isValid() && ReturnBlock.getBlock()->use_empty())
    return;

  ReturnsNonNullAttr *RetNNAttr = nullptr;
  if (SanOpts.has(SanitizerKind::ReturnsNonnullAttribute))
    RetNNAttr = CurCodeDecl->getAttr<ReturnsNonNullAttr>();

  if (!RetNNAttr && !requiresReturnValueNullabilityCheck())
    return;

  // Prefer the returns_nonnull attribute if it's present.
  SourceLocation AttrLoc;
  SanitizerMask CheckKind;
  SanitizerHandler Handler;
  if (RetNNAttr) {
    assert(!requiresReturnValueNullabilityCheck() &&
           "Cannot check nullability and the nonnull attribute");
    AttrLoc = RetNNAttr->getLocation();
    CheckKind = SanitizerKind::ReturnsNonnullAttribute;
    Handler = SanitizerHandler::NonnullReturn;
  } else {
    if (auto *DD = dyn_cast<DeclaratorDecl>(CurCodeDecl))
      if (auto *TSI = DD->getTypeSourceInfo())
        if (auto FTL = TSI->getTypeLoc().getAsAdjusted<FunctionTypeLoc>())
          AttrLoc = FTL.getReturnLoc().findNullabilityLoc();
    CheckKind = SanitizerKind::NullabilityReturn;
    Handler = SanitizerHandler::NullabilityReturn;
  }

  SanitizerScope SanScope(this);

  // Make sure the "return" source location is valid. If we're checking a
  // nullability annotation, make sure the preconditions for the check are met.
  llvm::BasicBlock *Check = createBasicBlock("nullcheck");
  llvm::BasicBlock *NoCheck = createBasicBlock("no.nullcheck");
  llvm::Value *SLocPtr = Builder.CreateLoad(ReturnLocation, "return.sloc.load");
  llvm::Value *CanNullCheck = Builder.CreateIsNotNull(SLocPtr);
  if (requiresReturnValueNullabilityCheck())
    CanNullCheck =
        Builder.CreateAnd(CanNullCheck, RetValNullabilityPrecondition);
  Builder.CreateCondBr(CanNullCheck, Check, NoCheck);
  EmitBlock(Check);

  // Now do the null check.
  llvm::Value *Cond = Builder.CreateIsNotNull(RV);
  llvm::Constant *StaticData[] = {EmitCheckSourceLocation(AttrLoc)};
  llvm::Value *DynamicData[] = {SLocPtr};
  EmitCheck(std::make_pair(Cond, CheckKind), Handler, StaticData, DynamicData);

  EmitBlock(NoCheck);

#ifndef NDEBUG
  // The return location should not be used after the check has been emitted.
  ReturnLocation = Address::invalid();
#endif
}

static bool isInAllocaArgument(CGCXXABI &ABI, QualType type) {
  const CXXRecordDecl *RD = type->getAsCXXRecordDecl();
  return RD && ABI.getRecordArgABI(RD) == CGCXXABI::RAA_DirectInMemory;
}

static AggValueSlot createPlaceholderSlot(CodeGenFunction &CGF,
                                          QualType Ty) {
  // FIXME: Generate IR in one pass, rather than going back and fixing up these
  // placeholders.
  llvm::Type *IRTy = CGF.ConvertTypeForMem(Ty);
  llvm::Type *IRPtrTy = IRTy->getPointerTo();
  llvm::Value *Placeholder = llvm::UndefValue::get(IRPtrTy->getPointerTo());

  // FIXME: When we generate this IR in one pass, we shouldn't need
  // this win32-specific alignment hack.
  CharUnits Align = CharUnits::fromQuantity(4);
  Placeholder = CGF.Builder.CreateAlignedLoad(IRPtrTy, Placeholder, Align);

  return AggValueSlot::forAddr(Address(Placeholder, Align),
                               Ty.getQualifiers(),
                               AggValueSlot::IsNotDestructed,
                               AggValueSlot::DoesNotNeedGCBarriers,
                               AggValueSlot::IsNotAliased,
                               AggValueSlot::DoesNotOverlap);
}

void CodeGenFunction::EmitDelegateCallArg(CallArgList &args,
                                          const VarDecl *param,
                                          SourceLocation loc) {
  // StartFunction converted the ABI-lowered parameter(s) into a
  // local alloca.  We need to turn that into an r-value suitable
  // for EmitCall.
  Address local = GetAddrOfLocalVar(param);

  QualType type = param->getType();

  if (isInAllocaArgument(CGM.getCXXABI(), type)) {
    CGM.ErrorUnsupported(param, "forwarded non-trivially copyable parameter");
  }

  // GetAddrOfLocalVar returns a pointer-to-pointer for references,
  // but the argument needs to be the original pointer.
  if (type->isReferenceType()) {
    args.add(RValue::get(Builder.CreateLoad(local)), type);

  // In ARC, move out of consumed arguments so that the release cleanup
  // entered by StartFunction doesn't cause an over-release.  This isn't
  // optimal -O0 code generation, but it should get cleaned up when
  // optimization is enabled.  This also assumes that delegate calls are
  // performed exactly once for a set of arguments, but that should be safe.
  } else if (getLangOpts().ObjCAutoRefCount &&
             param->hasAttr<NSConsumedAttr>() &&
             type->isObjCRetainableType()) {
    llvm::Value *ptr = Builder.CreateLoad(local);
    auto null =
      llvm::ConstantPointerNull::get(cast<llvm::PointerType>(ptr->getType()));
    Builder.CreateStore(null, local);
    args.add(RValue::get(ptr), type);

  // For the most part, we just need to load the alloca, except that
  // aggregate r-values are actually pointers to temporaries.
  } else {
    args.add(convertTempToRValue(local, type, loc), type);
  }

  // Deactivate the cleanup for the callee-destructed param that was pushed.
  if (hasAggregateEvaluationKind(type) && !CurFuncIsThunk &&
      type->castAs<RecordType>()->getDecl()->isParamDestroyedInCallee() &&
      param->needsDestruction(getContext())) {
    EHScopeStack::stable_iterator cleanup =
        CalleeDestructedParamCleanups.lookup(cast<ParmVarDecl>(param));
    assert(cleanup.isValid() &&
           "cleanup for callee-destructed param not recorded");
    // This unreachable is a temporary marker which will be removed later.
    llvm::Instruction *isActive = Builder.CreateUnreachable();
    args.addArgCleanupDeactivation(cleanup, isActive);
  }
}

static bool isProvablyNull(llvm::Value *addr) {
  return isa<llvm::ConstantPointerNull>(addr);
}

/// Emit the actual writing-back of a writeback.
static void emitWriteback(CodeGenFunction &CGF,
                          const CallArgList::Writeback &writeback) {
  const LValue &srcLV = writeback.Source;
  Address srcAddr = srcLV.getAddress(CGF);
  assert(!isProvablyNull(srcAddr.getPointer()) &&
         "shouldn't have writeback for provably null argument");

  llvm::BasicBlock *contBB = nullptr;

  // If the argument wasn't provably non-null, we need to null check
  // before doing the store.
  bool provablyNonNull = llvm::isKnownNonZero(srcAddr.getPointer(),
                                              CGF.CGM.getDataLayout());
  if (!provablyNonNull) {
    llvm::BasicBlock *writebackBB = CGF.createBasicBlock("icr.writeback");
    contBB = CGF.createBasicBlock("icr.done");

    llvm::Value *isNull =
      CGF.Builder.CreateIsNull(srcAddr.getPointer(), "icr.isnull");
    CGF.Builder.CreateCondBr(isNull, contBB, writebackBB);
    CGF.EmitBlock(writebackBB);
  }

  // Load the value to writeback.
  llvm::Value *value = CGF.Builder.CreateLoad(writeback.Temporary);

  // Cast it back, in case we're writing an id to a Foo* or something.
  value = CGF.Builder.CreateBitCast(value, srcAddr.getElementType(),
                                    "icr.writeback-cast");

  // Perform the writeback.

  // If we have a "to use" value, it's something we need to emit a use
  // of.  This has to be carefully threaded in: if it's done after the
  // release it's potentially undefined behavior (and the optimizer
  // will ignore it), and if it happens before the retain then the
  // optimizer could move the release there.
  if (writeback.ToUse) {
    assert(srcLV.getObjCLifetime() == Qualifiers::OCL_Strong);

    // Retain the new value.  No need to block-copy here:  the block's
    // being passed up the stack.
    value = CGF.EmitARCRetainNonBlock(value);

    // Emit the intrinsic use here.
    CGF.EmitARCIntrinsicUse(writeback.ToUse);

    // Load the old value (primitively).
    llvm::Value *oldValue = CGF.EmitLoadOfScalar(srcLV, SourceLocation());

    // Put the new value in place (primitively).
    CGF.EmitStoreOfScalar(value, srcLV, /*init*/ false);

    // Release the old value.
    CGF.EmitARCRelease(oldValue, srcLV.isARCPreciseLifetime());

  // Otherwise, we can just do a normal lvalue store.
  } else {
    CGF.EmitStoreThroughLValue(RValue::get(value), srcLV);
  }

  // Jump to the continuation block.
  if (!provablyNonNull)
    CGF.EmitBlock(contBB);
}

static void emitWritebacks(CodeGenFunction &CGF,
                           const CallArgList &args) {
  for (const auto &I : args.writebacks())
    emitWriteback(CGF, I);
}

static void deactivateArgCleanupsBeforeCall(CodeGenFunction &CGF,
                                            const CallArgList &CallArgs) {
  ArrayRef<CallArgList::CallArgCleanup> Cleanups =
    CallArgs.getCleanupsToDeactivate();
  // Iterate in reverse to increase the likelihood of popping the cleanup.
  for (const auto &I : llvm::reverse(Cleanups)) {
    CGF.DeactivateCleanupBlock(I.Cleanup, I.IsActiveIP);
    I.IsActiveIP->eraseFromParent();
  }
}

static const Expr *maybeGetUnaryAddrOfOperand(const Expr *E) {
  if (const UnaryOperator *uop = dyn_cast<UnaryOperator>(E->IgnoreParens()))
    if (uop->getOpcode() == UO_AddrOf)
      return uop->getSubExpr();
  return nullptr;
}

/// Emit an argument that's being passed call-by-writeback.  That is,
/// we are passing the address of an __autoreleased temporary; it
/// might be copy-initialized with the current value of the given
/// address, but it will definitely be copied out of after the call.
static void emitWritebackArg(CodeGenFunction &CGF, CallArgList &args,
                             const ObjCIndirectCopyRestoreExpr *CRE) {
  LValue srcLV;

  // Make an optimistic effort to emit the address as an l-value.
  // This can fail if the argument expression is more complicated.
  if (const Expr *lvExpr = maybeGetUnaryAddrOfOperand(CRE->getSubExpr())) {
    srcLV = CGF.EmitLValue(lvExpr);

  // Otherwise, just emit it as a scalar.
  } else {
    Address srcAddr = CGF.EmitPointerWithAlignment(CRE->getSubExpr());

    QualType srcAddrType =
      CRE->getSubExpr()->getType()->castAs<PointerType>()->getPointeeType();
    srcLV = CGF.MakeAddrLValue(srcAddr, srcAddrType);
  }
  Address srcAddr = srcLV.getAddress(CGF);

  // The dest and src types don't necessarily match in LLVM terms
  // because of the crazy ObjC compatibility rules.

  llvm::PointerType *destType =
    cast<llvm::PointerType>(CGF.ConvertType(CRE->getType()));

  // If the address is a constant null, just pass the appropriate null.
  if (isProvablyNull(srcAddr.getPointer())) {
    args.add(RValue::get(llvm::ConstantPointerNull::get(destType)),
             CRE->getType());
    return;
  }

  // Create the temporary.
  Address temp = CGF.CreateTempAlloca(destType->getElementType(),
                                      CGF.getPointerAlign(),
                                      "icr.temp");
  // Loading an l-value can introduce a cleanup if the l-value is __weak,
  // and that cleanup will be conditional if we can't prove that the l-value
  // isn't null, so we need to register a dominating point so that the cleanups
  // system will make valid IR.
  CodeGenFunction::ConditionalEvaluation condEval(CGF);

  // Zero-initialize it if we're not doing a copy-initialization.
  bool shouldCopy = CRE->shouldCopy();
  if (!shouldCopy) {
    llvm::Value *null =
      llvm::ConstantPointerNull::get(
        cast<llvm::PointerType>(destType->getElementType()));
    CGF.Builder.CreateStore(null, temp);
  }

  llvm::BasicBlock *contBB = nullptr;
  llvm::BasicBlock *originBB = nullptr;

  // If the address is *not* known to be non-null, we need to switch.
  llvm::Value *finalArgument;

  bool provablyNonNull = llvm::isKnownNonZero(srcAddr.getPointer(),
                                              CGF.CGM.getDataLayout());
  if (provablyNonNull) {
    finalArgument = temp.getPointer();
  } else {
    llvm::Value *isNull =
      CGF.Builder.CreateIsNull(srcAddr.getPointer(), "icr.isnull");

    finalArgument = CGF.Builder.CreateSelect(isNull,
                                   llvm::ConstantPointerNull::get(destType),
                                             temp.getPointer(), "icr.argument");

    // If we need to copy, then the load has to be conditional, which
    // means we need control flow.
    if (shouldCopy) {
      originBB = CGF.Builder.GetInsertBlock();
      contBB = CGF.createBasicBlock("icr.cont");
      llvm::BasicBlock *copyBB = CGF.createBasicBlock("icr.copy");
      CGF.Builder.CreateCondBr(isNull, contBB, copyBB);
      CGF.EmitBlock(copyBB);
      condEval.begin(CGF);
    }
  }

  llvm::Value *valueToUse = nullptr;

  // Perform a copy if necessary.
  if (shouldCopy) {
    RValue srcRV = CGF.EmitLoadOfLValue(srcLV, SourceLocation());
    assert(srcRV.isScalar());

    llvm::Value *src = srcRV.getScalarVal();
    src = CGF.Builder.CreateBitCast(src, destType->getElementType(),
                                    "icr.cast");

    // Use an ordinary store, not a store-to-lvalue.
    CGF.Builder.CreateStore(src, temp);

    // If optimization is enabled, and the value was held in a
    // __strong variable, we need to tell the optimizer that this
    // value has to stay alive until we're doing the store back.
    // This is because the temporary is effectively unretained,
    // and so otherwise we can violate the high-level semantics.
    if (CGF.CGM.getCodeGenOpts().OptimizationLevel != 0 &&
        srcLV.getObjCLifetime() == Qualifiers::OCL_Strong) {
      valueToUse = src;
    }
  }

  // Finish the control flow if we needed it.
  if (shouldCopy && !provablyNonNull) {
    llvm::BasicBlock *copyBB = CGF.Builder.GetInsertBlock();
    CGF.EmitBlock(contBB);

    // Make a phi for the value to intrinsically use.
    if (valueToUse) {
      llvm::PHINode *phiToUse = CGF.Builder.CreatePHI(valueToUse->getType(), 2,
                                                      "icr.to-use");
      phiToUse->addIncoming(valueToUse, copyBB);
      phiToUse->addIncoming(llvm::UndefValue::get(valueToUse->getType()),
                            originBB);
      valueToUse = phiToUse;
    }

    condEval.end(CGF);
  }

  args.addWriteback(srcLV, temp, valueToUse);
  args.add(RValue::get(finalArgument), CRE->getType());
}

void CallArgList::allocateArgumentMemory(CodeGenFunction &CGF) {
  assert(!StackBase);

  // Save the stack.
  llvm::Function *F = CGF.CGM.getIntrinsic(llvm::Intrinsic::stacksave);
  StackBase = CGF.Builder.CreateCall(F, {}, "inalloca.save");
}

void CallArgList::freeArgumentMemory(CodeGenFunction &CGF) const {
  if (StackBase) {
    // Restore the stack after the call.
    llvm::Function *F = CGF.CGM.getIntrinsic(llvm::Intrinsic::stackrestore);
    CGF.Builder.CreateCall(F, StackBase);
  }
}

void CodeGenFunction::EmitNonNullArgCheck(RValue RV, QualType ArgType,
                                          SourceLocation ArgLoc,
                                          AbstractCallee AC,
                                          unsigned ParmNum) {
  if (!AC.getDecl() || !(SanOpts.has(SanitizerKind::NonnullAttribute) ||
                         SanOpts.has(SanitizerKind::NullabilityArg)))
    return;

  // The param decl may be missing in a variadic function.
  auto PVD = ParmNum < AC.getNumParams() ? AC.getParamDecl(ParmNum) : nullptr;
  unsigned ArgNo = PVD ? PVD->getFunctionScopeIndex() : ParmNum;

  // Prefer the nonnull attribute if it's present.
  const NonNullAttr *NNAttr = nullptr;
  if (SanOpts.has(SanitizerKind::NonnullAttribute))
    NNAttr = getNonNullAttr(AC.getDecl(), PVD, ArgType, ArgNo);

  bool CanCheckNullability = false;
  if (SanOpts.has(SanitizerKind::NullabilityArg) && !NNAttr && PVD) {
    auto Nullability = PVD->getType()->getNullability(getContext());
    CanCheckNullability = Nullability &&
                          *Nullability == NullabilityKind::NonNull &&
                          PVD->getTypeSourceInfo();
  }

  if (!NNAttr && !CanCheckNullability)
    return;

  SourceLocation AttrLoc;
  SanitizerMask CheckKind;
  SanitizerHandler Handler;
  if (NNAttr) {
    AttrLoc = NNAttr->getLocation();
    CheckKind = SanitizerKind::NonnullAttribute;
    Handler = SanitizerHandler::NonnullArg;
  } else {
    AttrLoc = PVD->getTypeSourceInfo()->getTypeLoc().findNullabilityLoc();
    CheckKind = SanitizerKind::NullabilityArg;
    Handler = SanitizerHandler::NullabilityArg;
  }

  SanitizerScope SanScope(this);
  assert(RV.isScalar());
  llvm::Value *V = RV.getScalarVal();
  llvm::Value *Cond =
      Builder.CreateICmpNE(V, llvm::Constant::getNullValue(V->getType()));
  llvm::Constant *StaticData[] = {
      EmitCheckSourceLocation(ArgLoc), EmitCheckSourceLocation(AttrLoc),
      llvm::ConstantInt::get(Int32Ty, ArgNo + 1),
  };
  EmitCheck(std::make_pair(Cond, CheckKind), Handler, StaticData, None);
}

void CodeGenFunction::EmitCallArgs(
    CallArgList &Args, ArrayRef<QualType> ArgTypes,
    llvm::iterator_range<CallExpr::const_arg_iterator> ArgRange,
    AbstractCallee AC, unsigned ParamsToSkip, EvaluationOrder Order) {
  assert((int)ArgTypes.size() == (ArgRange.end() - ArgRange.begin()));

  // We *have* to evaluate arguments from right to left in the MS C++ ABI,
  // because arguments are destroyed left to right in the callee. As a special
  // case, there are certain language constructs that require left-to-right
  // evaluation, and in those cases we consider the evaluation order requirement
  // to trump the "destruction order is reverse construction order" guarantee.
  bool LeftToRight =
      CGM.getTarget().getCXXABI().areArgsDestroyedLeftToRightInCallee()
          ? Order == EvaluationOrder::ForceLeftToRight
          : Order != EvaluationOrder::ForceRightToLeft;

  auto MaybeEmitImplicitObjectSize = [&](unsigned I, const Expr *Arg,
                                         RValue EmittedArg) {
    if (!AC.hasFunctionDecl() || I >= AC.getNumParams())
      return;
    auto *PS = AC.getParamDecl(I)->getAttr<PassObjectSizeAttr>();
    if (PS == nullptr)
      return;

    const auto &Context = getContext();
    auto SizeTy = Context.getSizeType();
    auto T = Builder.getIntNTy(Context.getTypeSize(SizeTy));
    assert(EmittedArg.getScalarVal() && "We emitted nothing for the arg?");
    llvm::Value *V = evaluateOrEmitBuiltinObjectSize(Arg, PS->getType(), T,
                                                     EmittedArg.getScalarVal(),
                                                     PS->isDynamic());
    Args.add(RValue::get(V), SizeTy);
    // If we're emitting args in reverse, be sure to do so with
    // pass_object_size, as well.
    if (!LeftToRight)
      std::swap(Args.back(), *(&Args.back() - 1));
  };

  // Insert a stack save if we're going to need any inalloca args.
  bool HasInAllocaArgs = false;
  if (CGM.getTarget().getCXXABI().isMicrosoft()) {
    for (ArrayRef<QualType>::iterator I = ArgTypes.begin(), E = ArgTypes.end();
         I != E && !HasInAllocaArgs; ++I)
      HasInAllocaArgs = isInAllocaArgument(CGM.getCXXABI(), *I);
    if (HasInAllocaArgs) {
      assert(getTarget().getTriple().getArch() == llvm::Triple::x86);
      Args.allocateArgumentMemory(*this);
    }
  }

  // Evaluate each argument in the appropriate order.
  size_t CallArgsStart = Args.size();
  for (unsigned I = 0, E = ArgTypes.size(); I != E; ++I) {
    unsigned Idx = LeftToRight ? I : E - I - 1;
    CallExpr::const_arg_iterator Arg = ArgRange.begin() + Idx;
    unsigned InitialArgSize = Args.size();
    // If *Arg is an ObjCIndirectCopyRestoreExpr, check that either the types of
    // the argument and parameter match or the objc method is parameterized.
    assert((!isa<ObjCIndirectCopyRestoreExpr>(*Arg) ||
            getContext().hasSameUnqualifiedType((*Arg)->getType(),
                                                ArgTypes[Idx]) ||
            (isa<ObjCMethodDecl>(AC.getDecl()) &&
             isObjCMethodWithTypeParams(cast<ObjCMethodDecl>(AC.getDecl())))) &&
           "Argument and parameter types don't match");
    EmitCallArg(Args, *Arg, ArgTypes[Idx]);
    // In particular, we depend on it being the last arg in Args, and the
    // objectsize bits depend on there only being one arg if !LeftToRight.
    assert(InitialArgSize + 1 == Args.size() &&
           "The code below depends on only adding one arg per EmitCallArg");
    (void)InitialArgSize;
    // Since pointer argument are never emitted as LValue, it is safe to emit
    // non-null argument check for r-value only.
    if (!Args.back().hasLValue()) {
      RValue RVArg = Args.back().getKnownRValue();
      EmitNonNullArgCheck(RVArg, ArgTypes[Idx], (*Arg)->getExprLoc(), AC,
                          ParamsToSkip + Idx);
      // @llvm.objectsize should never have side-effects and shouldn't need
      // destruction/cleanups, so we can safely "emit" it after its arg,
      // regardless of right-to-leftness
      MaybeEmitImplicitObjectSize(Idx, *Arg, RVArg);
    }
  }

  if (!LeftToRight) {
    // Un-reverse the arguments we just evaluated so they match up with the LLVM
    // IR function.
    std::reverse(Args.begin() + CallArgsStart, Args.end());
  }
}

namespace {

struct DestroyUnpassedArg final : EHScopeStack::Cleanup {
  DestroyUnpassedArg(Address Addr, QualType Ty)
      : Addr(Addr), Ty(Ty) {}

  Address Addr;
  QualType Ty;

  void Emit(CodeGenFunction &CGF, Flags flags) override {
    QualType::DestructionKind DtorKind = Ty.isDestructedType();
    if (DtorKind == QualType::DK_cxx_destructor) {
      const CXXDestructorDecl *Dtor = Ty->getAsCXXRecordDecl()->getDestructor();
      assert(!Dtor->isTrivial());
      CGF.EmitCXXDestructorCall(Dtor, Dtor_Complete, /*for vbase*/ false,
                                /*Delegating=*/false, Addr, Ty);
    } else {
      CGF.callCStructDestructor(CGF.MakeAddrLValue(Addr, Ty));
    }
  }
};

struct DisableDebugLocationUpdates {
  CodeGenFunction &CGF;
  bool disabledDebugInfo;
  DisableDebugLocationUpdates(CodeGenFunction &CGF, const Expr *E) : CGF(CGF) {
    if ((disabledDebugInfo = isa<CXXDefaultArgExpr>(E) && CGF.getDebugInfo()))
      CGF.disableDebugInfo();
  }
  ~DisableDebugLocationUpdates() {
    if (disabledDebugInfo)
      CGF.enableDebugInfo();
  }
};

} // end anonymous namespace

RValue CallArg::getRValue(CodeGenFunction &CGF) const {
  if (!HasLV)
    return RV;
  LValue Copy = CGF.MakeAddrLValue(CGF.CreateMemTemp(Ty), Ty);
  CGF.EmitAggregateCopy(Copy, LV, Ty, AggValueSlot::DoesNotOverlap,
                        LV.isVolatile());
  IsUsed = true;
  return RValue::getAggregate(Copy.getAddress(CGF));
}

void CallArg::copyInto(CodeGenFunction &CGF, Address Addr) const {
  LValue Dst = CGF.MakeAddrLValue(Addr, Ty);
  if (!HasLV && RV.isScalar())
    CGF.EmitStoreOfScalar(RV.getScalarVal(), Dst, /*isInit=*/true);
  else if (!HasLV && RV.isComplex())
    CGF.EmitStoreOfComplex(RV.getComplexVal(), Dst, /*init=*/true);
  else {
    auto Addr = HasLV ? LV.getAddress(CGF) : RV.getAggregateAddress();
    LValue SrcLV = CGF.MakeAddrLValue(Addr, Ty);
    // We assume that call args are never copied into subobjects.
    CGF.EmitAggregateCopy(Dst, SrcLV, Ty, AggValueSlot::DoesNotOverlap,
                          HasLV ? LV.isVolatileQualified()
                                : RV.isVolatileQualified());
  }
  IsUsed = true;
}

void CodeGenFunction::EmitCallArg(CallArgList &args, const Expr *E,
                                  QualType type) {
  DisableDebugLocationUpdates Dis(*this, E);
  if (const ObjCIndirectCopyRestoreExpr *CRE
        = dyn_cast<ObjCIndirectCopyRestoreExpr>(E)) {
    assert(getLangOpts().ObjCAutoRefCount);
    return emitWritebackArg(*this, args, CRE);
  }

  assert(type->isReferenceType() == E->isGLValue() &&
         "reference binding to unmaterialized r-value!");

  if (E->isGLValue()) {
    assert(E->getObjectKind() == OK_Ordinary);
    return args.add(EmitReferenceBindingToExpr(E), type);
  }

  bool HasAggregateEvalKind = hasAggregateEvaluationKind(type);

  // In the Microsoft C++ ABI, aggregate arguments are destructed by the callee.
  // However, we still have to push an EH-only cleanup in case we unwind before
  // we make it to the call.
  if (HasAggregateEvalKind &&
      type->castAs<RecordType>()->getDecl()->isParamDestroyedInCallee()) {
    // If we're using inalloca, use the argument memory.  Otherwise, use a
    // temporary.
    AggValueSlot Slot;
    if (args.isUsingInAlloca())
      Slot = createPlaceholderSlot(*this, type);
    else
      Slot = CreateAggTemp(type, "agg.tmp");

    bool DestroyedInCallee = true, NeedsEHCleanup = true;
    if (const auto *RD = type->getAsCXXRecordDecl())
      DestroyedInCallee = RD->hasNonTrivialDestructor();
    else
      NeedsEHCleanup = needsEHCleanup(type.isDestructedType());

    if (DestroyedInCallee)
      Slot.setExternallyDestructed();

    EmitAggExpr(E, Slot);
    RValue RV = Slot.asRValue();
    args.add(RV, type);

    if (DestroyedInCallee && NeedsEHCleanup) {
      // Create a no-op GEP between the placeholder and the cleanup so we can
      // RAUW it successfully.  It also serves as a marker of the first
      // instruction where the cleanup is active.
      pushFullExprCleanup<DestroyUnpassedArg>(EHCleanup, Slot.getAddress(),
                                              type);
      // This unreachable is a temporary marker which will be removed later.
      llvm::Instruction *IsActive = Builder.CreateUnreachable();
      args.addArgCleanupDeactivation(EHStack.getInnermostEHScope(), IsActive);
    }
    return;
  }

  if (HasAggregateEvalKind && isa<ImplicitCastExpr>(E) &&
      cast<CastExpr>(E)->getCastKind() == CK_LValueToRValue) {
    LValue L = EmitLValue(cast<CastExpr>(E)->getSubExpr());
    assert(L.isSimple());
    args.addUncopiedAggregate(L, type);
    return;
  }

  args.add(EmitAnyExprToTemp(E), type);
}

QualType CodeGenFunction::getVarArgType(const Expr *Arg) {
  // System headers on Windows define NULL to 0 instead of 0LL on Win64. MSVC
  // implicitly widens null pointer constants that are arguments to varargs
  // functions to pointer-sized ints.
  if (!getTarget().getTriple().isOSWindows())
    return Arg->getType();

  if (Arg->getType()->isIntegerType() &&
      getContext().getTypeSize(Arg->getType()) <
          getContext().getTargetInfo().getPointerWidth(0) &&
      Arg->isNullPointerConstant(getContext(),
                                 Expr::NPC_ValueDependentIsNotNull)) {
    return getContext().getIntPtrType();
  }

  return Arg->getType();
}

// In ObjC ARC mode with no ObjC ARC exception safety, tell the ARC
// optimizer it can aggressively ignore unwind edges.
void
CodeGenFunction::AddObjCARCExceptionMetadata(llvm::Instruction *Inst) {
  if (CGM.getCodeGenOpts().OptimizationLevel != 0 &&
      !CGM.getCodeGenOpts().ObjCAutoRefCountExceptions)
    Inst->setMetadata("clang.arc.no_objc_arc_exceptions",
                      CGM.getNoObjCARCExceptionsMetadata());
}

/// Emits a call to the given no-arguments nounwind runtime function.
llvm::CallInst *
CodeGenFunction::EmitNounwindRuntimeCall(llvm::FunctionCallee callee,
                                         const llvm::Twine &name) {
  return EmitNounwindRuntimeCall(callee, None, name);
}

/// Emits a call to the given nounwind runtime function.
llvm::CallInst *
CodeGenFunction::EmitNounwindRuntimeCall(llvm::FunctionCallee callee,
                                         ArrayRef<llvm::Value *> args,
                                         const llvm::Twine &name) {
  llvm::CallInst *call = EmitRuntimeCall(callee, args, name);
  call->setDoesNotThrow();
  return call;
}

/// Emits a simple call (never an invoke) to the given no-arguments
/// runtime function.
llvm::CallInst *CodeGenFunction::EmitRuntimeCall(llvm::FunctionCallee callee,
                                                 const llvm::Twine &name) {
  return EmitRuntimeCall(callee, None, name);
}

// Calls which may throw must have operand bundles indicating which funclet
// they are nested within.
SmallVector<llvm::OperandBundleDef, 1>
CodeGenFunction::getBundlesForFunclet(llvm::Value *Callee) {
  SmallVector<llvm::OperandBundleDef, 1> BundleList;
  // There is no need for a funclet operand bundle if we aren't inside a
  // funclet.
  if (!CurrentFuncletPad)
    return BundleList;

  // Skip intrinsics which cannot throw.
  auto *CalleeFn = dyn_cast<llvm::Function>(Callee->stripPointerCasts());
  if (CalleeFn && CalleeFn->isIntrinsic() && CalleeFn->doesNotThrow())
    return BundleList;

  BundleList.emplace_back("funclet", CurrentFuncletPad);
  return BundleList;
}

/// Emits a simple call (never an invoke) to the given runtime function.
llvm::CallInst *CodeGenFunction::EmitRuntimeCall(llvm::FunctionCallee callee,
                                                 ArrayRef<llvm::Value *> args,
                                                 const llvm::Twine &name) {
  llvm::CallInst *call = Builder.CreateCall(
      callee, args, getBundlesForFunclet(callee.getCallee()), name);
  call->setCallingConv(getRuntimeCC());
  return call;
}

/// Emits a call or invoke to the given noreturn runtime function.
void CodeGenFunction::EmitNoreturnRuntimeCallOrInvoke(
    llvm::FunctionCallee callee, ArrayRef<llvm::Value *> args) {
  SmallVector<llvm::OperandBundleDef, 1> BundleList =
      getBundlesForFunclet(callee.getCallee());

  if (getInvokeDest()) {
    llvm::InvokeInst *invoke =
      Builder.CreateInvoke(callee,
                           getUnreachableBlock(),
                           getInvokeDest(),
                           args,
                           BundleList);
    invoke->setDoesNotReturn();
    invoke->setCallingConv(getRuntimeCC());
  } else {
    llvm::CallInst *call = Builder.CreateCall(callee, args, BundleList);
    call->setDoesNotReturn();
    call->setCallingConv(getRuntimeCC());
    Builder.CreateUnreachable();
  }
}

/// Emits a call or invoke instruction to the given nullary runtime function.
llvm::CallBase *
CodeGenFunction::EmitRuntimeCallOrInvoke(llvm::FunctionCallee callee,
                                         const Twine &name) {
  return EmitRuntimeCallOrInvoke(callee, None, name);
}

/// Emits a call or invoke instruction to the given runtime function.
llvm::CallBase *
CodeGenFunction::EmitRuntimeCallOrInvoke(llvm::FunctionCallee callee,
                                         ArrayRef<llvm::Value *> args,
                                         const Twine &name) {
  llvm::CallBase *call = EmitCallOrInvoke(callee, args, name);
  call->setCallingConv(getRuntimeCC());
  return call;
}

/// Emits a call or invoke instruction to the given function, depending
/// on the current state of the EH stack.
llvm::CallBase *CodeGenFunction::EmitCallOrInvoke(llvm::FunctionCallee Callee,
                                                  ArrayRef<llvm::Value *> Args,
                                                  const Twine &Name) {
  llvm::BasicBlock *InvokeDest = getInvokeDest();
  SmallVector<llvm::OperandBundleDef, 1> BundleList =
      getBundlesForFunclet(Callee.getCallee());

  llvm::CallBase *Inst;
  if (!InvokeDest)
    Inst = Builder.CreateCall(Callee, Args, BundleList, Name);
  else {
    llvm::BasicBlock *ContBB = createBasicBlock("invoke.cont");
    Inst = Builder.CreateInvoke(Callee, ContBB, InvokeDest, Args, BundleList,
                                Name);
    EmitBlock(ContBB);
  }

  // In ObjC ARC mode with no ObjC ARC exception safety, tell the ARC
  // optimizer it can aggressively ignore unwind edges.
  if (CGM.getLangOpts().ObjCAutoRefCount)
    AddObjCARCExceptionMetadata(Inst);

  return Inst;
}

void CodeGenFunction::deferPlaceholderReplacement(llvm::Instruction *Old,
                                                  llvm::Value *New) {
  DeferredReplacements.push_back(std::make_pair(Old, New));
}

namespace {

/// Specify given \p NewAlign as the alignment of return value attribute. If
/// such attribute already exists, re-set it to the maximal one of two options.
LLVM_NODISCARD llvm::AttributeList
maybeRaiseRetAlignmentAttribute(llvm::LLVMContext &Ctx,
                                const llvm::AttributeList &Attrs,
                                llvm::Align NewAlign) {
  llvm::Align CurAlign = Attrs.getRetAlignment().valueOrOne();
  if (CurAlign >= NewAlign)
    return Attrs;
  llvm::Attribute AlignAttr = llvm::Attribute::getWithAlignment(Ctx, NewAlign);
  return Attrs
      .removeAttribute(Ctx, llvm::AttributeList::ReturnIndex,
                       llvm::Attribute::AttrKind::Alignment)
      .addAttribute(Ctx, llvm::AttributeList::ReturnIndex, AlignAttr);
}

template <typename AlignedAttrTy> class AbstractAssumeAlignedAttrEmitter {
protected:
  CodeGenFunction &CGF;

  /// We do nothing if this is, or becomes, nullptr.
  const AlignedAttrTy *AA = nullptr;

  llvm::Value *Alignment = nullptr;      // May or may not be a constant.
  llvm::ConstantInt *OffsetCI = nullptr; // Constant, hopefully zero.

  AbstractAssumeAlignedAttrEmitter(CodeGenFunction &CGF_, const Decl *FuncDecl)
      : CGF(CGF_) {
    if (!FuncDecl)
      return;
    AA = FuncDecl->getAttr<AlignedAttrTy>();
  }

public:
  /// If we can, materialize the alignment as an attribute on return value.
  LLVM_NODISCARD llvm::AttributeList
  TryEmitAsCallSiteAttribute(const llvm::AttributeList &Attrs) {
    if (!AA || OffsetCI || CGF.SanOpts.has(SanitizerKind::Alignment))
      return Attrs;
    const auto *AlignmentCI = dyn_cast<llvm::ConstantInt>(Alignment);
    if (!AlignmentCI)
      return Attrs;
    // We may legitimately have non-power-of-2 alignment here.
    // If so, this is UB land, emit it via `@llvm.assume` instead.
    if (!AlignmentCI->getValue().isPowerOf2())
      return Attrs;
    llvm::AttributeList NewAttrs = maybeRaiseRetAlignmentAttribute(
        CGF.getLLVMContext(), Attrs,
        llvm::Align(
            AlignmentCI->getLimitedValue(llvm::Value::MaximumAlignment)));
    AA = nullptr; // We're done. Disallow doing anything else.
    return NewAttrs;
  }

  /// Emit alignment assumption.
  /// This is a general fallback that we take if either there is an offset,
  /// or the alignment is variable or we are sanitizing for alignment.
  void EmitAsAnAssumption(SourceLocation Loc, QualType RetTy, RValue &Ret) {
    if (!AA)
      return;
    CGF.emitAlignmentAssumption(Ret.getScalarVal(), RetTy, Loc,
                                AA->getLocation(), Alignment, OffsetCI);
    AA = nullptr; // We're done. Disallow doing anything else.
  }
};

/// Helper data structure to emit `AssumeAlignedAttr`.
class AssumeAlignedAttrEmitter final
    : public AbstractAssumeAlignedAttrEmitter<AssumeAlignedAttr> {
public:
  AssumeAlignedAttrEmitter(CodeGenFunction &CGF_, const Decl *FuncDecl)
      : AbstractAssumeAlignedAttrEmitter(CGF_, FuncDecl) {
    if (!AA)
      return;
    // It is guaranteed that the alignment/offset are constants.
    Alignment = cast<llvm::ConstantInt>(CGF.EmitScalarExpr(AA->getAlignment()));
    if (Expr *Offset = AA->getOffset()) {
      OffsetCI = cast<llvm::ConstantInt>(CGF.EmitScalarExpr(Offset));
      if (OffsetCI->isNullValue()) // Canonicalize zero offset to no offset.
        OffsetCI = nullptr;
    }
  }
};

/// Helper data structure to emit `AllocAlignAttr`.
class AllocAlignAttrEmitter final
    : public AbstractAssumeAlignedAttrEmitter<AllocAlignAttr> {
public:
  AllocAlignAttrEmitter(CodeGenFunction &CGF_, const Decl *FuncDecl,
                        const CallArgList &CallArgs)
      : AbstractAssumeAlignedAttrEmitter(CGF_, FuncDecl) {
    if (!AA)
      return;
    // Alignment may or may not be a constant, and that is okay.
    Alignment = CallArgs[AA->getParamIndex().getLLVMIndex()]
                    .getRValue(CGF)
                    .getScalarVal();
  }
};

} // namespace

RValue CodeGenFunction::EmitCall(const CGFunctionInfo &CallInfo,
                                 const CGCallee &Callee,
                                 ReturnValueSlot ReturnValue,
                                 const CallArgList &CallArgs,
                                 llvm::CallBase **callOrInvoke,
                                 SourceLocation Loc) {
  // FIXME: We no longer need the types from CallArgs; lift up and simplify.

  assert(Callee.isOrdinary() || Callee.isVirtual());

  // Handle struct-return functions by passing a pointer to the
  // location that we would like to return into.
  QualType RetTy = CallInfo.getReturnType();
  const ABIArgInfo &RetAI = CallInfo.getReturnInfo();

  llvm::FunctionType *IRFuncTy = getTypes().GetFunctionType(CallInfo);

  const Decl *TargetDecl = Callee.getAbstractInfo().getCalleeDecl().getDecl();
  if (const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(TargetDecl)) {
    // We can only guarantee that a function is called from the correct
    // context/function based on the appropriate target attributes,
    // so only check in the case where we have both always_inline and target
    // since otherwise we could be making a conditional call after a check for
    // the proper cpu features (and it won't cause code generation issues due to
    // function based code generation).
    if (TargetDecl->hasAttr<AlwaysInlineAttr>() &&
        TargetDecl->hasAttr<TargetAttr>())
      checkTargetFeatures(Loc, FD);

    // Some architectures (such as x86-64) have the ABI changed based on
    // attribute-target/features. Give them a chance to diagnose.
    CGM.getTargetCodeGenInfo().checkFunctionCallABI(
        CGM, Loc, dyn_cast_or_null<FunctionDecl>(CurCodeDecl), FD, CallArgs);
  }

#ifndef NDEBUG
  if (!(CallInfo.isVariadic() && CallInfo.getArgStruct())) {
    // For an inalloca varargs function, we don't expect CallInfo to match the
    // function pointer's type, because the inalloca struct a will have extra
    // fields in it for the varargs parameters.  Code later in this function
    // bitcasts the function pointer to the type derived from CallInfo.
    //
    // In other cases, we assert that the types match up (until pointers stop
    // having pointee types).
    llvm::Type *TypeFromVal;
    if (Callee.isVirtual())
      TypeFromVal = Callee.getVirtualFunctionType();
    else
      TypeFromVal =
          Callee.getFunctionPointer()->getType()->getPointerElementType();
    assert(IRFuncTy == TypeFromVal);
  }
#endif

  // 1. Set up the arguments.

  // If we're using inalloca, insert the allocation after the stack save.
  // FIXME: Do this earlier rather than hacking it in here!
  Address ArgMemory = Address::invalid();
  if (llvm::StructType *ArgStruct = CallInfo.getArgStruct()) {
    const llvm::DataLayout &DL = CGM.getDataLayout();
    llvm::Instruction *IP = CallArgs.getStackBase();
    llvm::AllocaInst *AI;
    if (IP) {
      IP = IP->getNextNode();
      AI = new llvm::AllocaInst(ArgStruct, DL.getAllocaAddrSpace(),
                                "argmem", IP);
    } else {
      AI = CreateTempAlloca(ArgStruct, "argmem");
    }
    auto Align = CallInfo.getArgStructAlignment();
    AI->setAlignment(Align.getAsAlign());
    AI->setUsedWithInAlloca(true);
    assert(AI->isUsedWithInAlloca() && !AI->isStaticAlloca());
    ArgMemory = Address(AI, Align);
  }

  ClangToLLVMArgMapping IRFunctionArgs(CGM.getContext(), CallInfo);
  SmallVector<llvm::Value *, 16> IRCallArgs(IRFunctionArgs.totalIRArgs());

  // If the call returns a temporary with struct return, create a temporary
  // alloca to hold the result, unless one is given to us.
  Address SRetPtr = Address::invalid();
  Address SRetAlloca = Address::invalid();
  llvm::Value *UnusedReturnSizePtr = nullptr;
  if (RetAI.isIndirect() || RetAI.isInAlloca() || RetAI.isCoerceAndExpand()) {
    if (!ReturnValue.isNull()) {
      SRetPtr = ReturnValue.getValue();
    } else {
      SRetPtr = CreateMemTemp(RetTy, "tmp", &SRetAlloca);
      if (HaveInsertPoint() && ReturnValue.isUnused()) {
        uint64_t size =
            CGM.getDataLayout().getTypeAllocSize(ConvertTypeForMem(RetTy));
        UnusedReturnSizePtr = EmitLifetimeStart(size, SRetAlloca.getPointer());
      }
    }
    if (IRFunctionArgs.hasSRetArg()) {
      IRCallArgs[IRFunctionArgs.getSRetArgNo()] = SRetPtr.getPointer();
    } else if (RetAI.isInAlloca()) {
      Address Addr =
          Builder.CreateStructGEP(ArgMemory, RetAI.getInAllocaFieldIndex());
      Builder.CreateStore(SRetPtr.getPointer(), Addr);
    }
  }

  Address swiftErrorTemp = Address::invalid();
  Address swiftErrorArg = Address::invalid();

  // When passing arguments using temporary allocas, we need to add the
  // appropriate lifetime markers. This vector keeps track of all the lifetime
  // markers that need to be ended right after the call.
  SmallVector<CallLifetimeEnd, 2> CallLifetimeEndAfterCall;

  // Translate all of the arguments as necessary to match the IR lowering.
  assert(CallInfo.arg_size() == CallArgs.size() &&
         "Mismatch between function signature & arguments.");
  unsigned ArgNo = 0;
  CGFunctionInfo::const_arg_iterator info_it = CallInfo.arg_begin();
  for (CallArgList::const_iterator I = CallArgs.begin(), E = CallArgs.end();
       I != E; ++I, ++info_it, ++ArgNo) {
    const ABIArgInfo &ArgInfo = info_it->info;

    // Insert a padding argument to ensure proper alignment.
    if (IRFunctionArgs.hasPaddingArg(ArgNo))
      IRCallArgs[IRFunctionArgs.getPaddingArgNo(ArgNo)] =
          llvm::UndefValue::get(ArgInfo.getPaddingType());

    unsigned FirstIRArg, NumIRArgs;
    std::tie(FirstIRArg, NumIRArgs) = IRFunctionArgs.getIRArgs(ArgNo);

    switch (ArgInfo.getKind()) {
    case ABIArgInfo::InAlloca: {
      assert(NumIRArgs == 0);
      assert(getTarget().getTriple().getArch() == llvm::Triple::x86);
      if (I->isAggregate()) {
        Address Addr = I->hasLValue()
                           ? I->getKnownLValue().getAddress(*this)
                           : I->getKnownRValue().getAggregateAddress();
        llvm::Instruction *Placeholder =
            cast<llvm::Instruction>(Addr.getPointer());

        if (!ArgInfo.getInAllocaIndirect()) {
          // Replace the placeholder with the appropriate argument slot GEP.
          CGBuilderTy::InsertPoint IP = Builder.saveIP();
          Builder.SetInsertPoint(Placeholder);
          Addr = Builder.CreateStructGEP(ArgMemory,
                                         ArgInfo.getInAllocaFieldIndex());
          Builder.restoreIP(IP);
        } else {
          // For indirect things such as overaligned structs, replace the
          // placeholder with a regular aggregate temporary alloca. Store the
          // address of this alloca into the struct.
          Addr = CreateMemTemp(info_it->type, "inalloca.indirect.tmp");
          Address ArgSlot = Builder.CreateStructGEP(
              ArgMemory, ArgInfo.getInAllocaFieldIndex());
          Builder.CreateStore(Addr.getPointer(), ArgSlot);
        }
        deferPlaceholderReplacement(Placeholder, Addr.getPointer());
      } else if (ArgInfo.getInAllocaIndirect()) {
        // Make a temporary alloca and store the address of it into the argument
        // struct.
        Address Addr = CreateMemTempWithoutCast(
            I->Ty, getContext().getTypeAlignInChars(I->Ty),
            "indirect-arg-temp");
        I->copyInto(*this, Addr);
        Address ArgSlot =
            Builder.CreateStructGEP(ArgMemory, ArgInfo.getInAllocaFieldIndex());
        Builder.CreateStore(Addr.getPointer(), ArgSlot);
      } else {
        // Store the RValue into the argument struct.
        Address Addr =
            Builder.CreateStructGEP(ArgMemory, ArgInfo.getInAllocaFieldIndex());
        unsigned AS = Addr.getType()->getPointerAddressSpace();
        llvm::Type *MemType = ConvertTypeForMem(I->Ty)->getPointerTo(AS);
        // There are some cases where a trivial bitcast is not avoidable.  The
        // definition of a type later in a translation unit may change it's type
        // from {}* to (%struct.foo*)*.
        if (Addr.getType() != MemType)
          Addr = Builder.CreateBitCast(Addr, MemType);
        I->copyInto(*this, Addr);
      }
      break;
    }

    case ABIArgInfo::Indirect:
    case ABIArgInfo::IndirectAliased: {
      assert(NumIRArgs == 1);
      if (!I->isAggregate()) {
        // Make a temporary alloca to pass the argument.
        Address Addr = CreateMemTempWithoutCast(
            I->Ty, ArgInfo.getIndirectAlign(), "indirect-arg-temp");
        IRCallArgs[FirstIRArg] = Addr.getPointer();

        I->copyInto(*this, Addr);
      } else {
        // We want to avoid creating an unnecessary temporary+copy here;
        // however, we need one in three cases:
        // 1. If the argument is not byval, and we are required to copy the
        //    source.  (This case doesn't occur on any common architecture.)
        // 2. If the argument is byval, RV is not sufficiently aligned, and
        //    we cannot force it to be sufficiently aligned.
        // 3. If the argument is byval, but RV is not located in default
        //    or alloca address space.
        Address Addr = I->hasLValue()
                           ? I->getKnownLValue().getAddress(*this)
                           : I->getKnownRValue().getAggregateAddress();
        llvm::Value *V = Addr.getPointer();
        CharUnits Align = ArgInfo.getIndirectAlign();
        const llvm::DataLayout *TD = &CGM.getDataLayout();

        assert((FirstIRArg >= IRFuncTy->getNumParams() ||
                IRFuncTy->getParamType(FirstIRArg)->getPointerAddressSpace() ==
                    TD->getAllocaAddrSpace()) &&
               "indirect argument must be in alloca address space");

        bool NeedCopy = false;

        if (Addr.getAlignment() < Align &&
            llvm::getOrEnforceKnownAlignment(V, Align.getAsAlign(), *TD) <
                Align.getAsAlign()) {
          NeedCopy = true;
        } else if (I->hasLValue()) {
          auto LV = I->getKnownLValue();
          auto AS = LV.getAddressSpace();

          if (!ArgInfo.getIndirectByVal() ||
              (LV.getAlignment() < getContext().getTypeAlignInChars(I->Ty))) {
            NeedCopy = true;
          }
          if (!getLangOpts().OpenCL) {
            if ((ArgInfo.getIndirectByVal() &&
                (AS != LangAS::Default &&
                 AS != CGM.getASTAllocaAddressSpace()))) {
              NeedCopy = true;
            }
          }
          // For OpenCL even if RV is located in default or alloca address space
          // we don't want to perform address space cast for it.
          else if ((ArgInfo.getIndirectByVal() &&
                    Addr.getType()->getAddressSpace() != IRFuncTy->
                      getParamType(FirstIRArg)->getPointerAddressSpace())) {
            NeedCopy = true;
          }
        }

        if (NeedCopy) {
          // Create an aligned temporary, and copy to it.
          Address AI = CreateMemTempWithoutCast(
              I->Ty, ArgInfo.getIndirectAlign(), "byval-temp");
          IRCallArgs[FirstIRArg] = AI.getPointer();

          // Emit lifetime markers for the temporary alloca.
          uint64_t ByvalTempElementSize =
              CGM.getDataLayout().getTypeAllocSize(AI.getElementType());
          llvm::Value *LifetimeSize =
              EmitLifetimeStart(ByvalTempElementSize, AI.getPointer());

          // Add cleanup code to emit the end lifetime marker after the call.
          if (LifetimeSize) // In case we disabled lifetime markers.
            CallLifetimeEndAfterCall.emplace_back(AI, LifetimeSize);

          // Generate the copy.
          I->copyInto(*this, AI);
        } else {
          // Skip the extra memcpy call.
          auto *T = V->getType()->getPointerElementType()->getPointerTo(
              CGM.getDataLayout().getAllocaAddrSpace());
          IRCallArgs[FirstIRArg] = getTargetHooks().performAddrSpaceCast(
              *this, V, LangAS::Default, CGM.getASTAllocaAddressSpace(), T,
              true);
        }
      }
      break;
    }

    case ABIArgInfo::Ignore:
      assert(NumIRArgs == 0);
      break;

    case ABIArgInfo::Extend:
    case ABIArgInfo::Direct: {
      if (!isa<llvm::StructType>(ArgInfo.getCoerceToType()) &&
          ArgInfo.getCoerceToType() == ConvertType(info_it->type) &&
          ArgInfo.getDirectOffset() == 0) {
        assert(NumIRArgs == 1);
        llvm::Value *V;
        if (!I->isAggregate())
          V = I->getKnownRValue().getScalarVal();
        else
          V = Builder.CreateLoad(
              I->hasLValue() ? I->getKnownLValue().getAddress(*this)
                             : I->getKnownRValue().getAggregateAddress());

        // Implement swifterror by copying into a new swifterror argument.
        // We'll write back in the normal path out of the call.
        if (CallInfo.getExtParameterInfo(ArgNo).getABI()
              == ParameterABI::SwiftErrorResult) {
          assert(!swiftErrorTemp.isValid() && "multiple swifterror args");

          QualType pointeeTy = I->Ty->getPointeeType();
          swiftErrorArg =
            Address(V, getContext().getTypeAlignInChars(pointeeTy));

          swiftErrorTemp =
            CreateMemTemp(pointeeTy, getPointerAlign(), "swifterror.temp");
          V = swiftErrorTemp.getPointer();
          cast<llvm::AllocaInst>(V)->setSwiftError(true);

          llvm::Value *errorValue = Builder.CreateLoad(swiftErrorArg);
          Builder.CreateStore(errorValue, swiftErrorTemp);
        }

        // We might have to widen integers, but we should never truncate.
        if (ArgInfo.getCoerceToType() != V->getType() &&
            V->getType()->isIntegerTy())
          V = Builder.CreateZExt(V, ArgInfo.getCoerceToType());

        // If the argument doesn't match, perform a bitcast to coerce it.  This
        // can happen due to trivial type mismatches.
        if (FirstIRArg < IRFuncTy->getNumParams() &&
            V->getType() != IRFuncTy->getParamType(FirstIRArg))
          V = Builder.CreateBitCast(V, IRFuncTy->getParamType(FirstIRArg));

        IRCallArgs[FirstIRArg] = V;
        break;
      }

      // FIXME: Avoid the conversion through memory if possible.
      Address Src = Address::invalid();
      if (!I->isAggregate()) {
        Src = CreateMemTemp(I->Ty, "coerce");
        I->copyInto(*this, Src);
      } else {
        Src = I->hasLValue() ? I->getKnownLValue().getAddress(*this)
                             : I->getKnownRValue().getAggregateAddress();
      }

      // If the value is offset in memory, apply the offset now.
      Src = emitAddressAtOffset(*this, Src, ArgInfo);

      // Fast-isel and the optimizer generally like scalar values better than
      // FCAs, so we flatten them if this is safe to do for this argument.
      llvm::StructType *STy =
            dyn_cast<llvm::StructType>(ArgInfo.getCoerceToType());
      if (STy && ArgInfo.isDirect() && ArgInfo.getCanBeFlattened()) {
        llvm::Type *SrcTy = Src.getElementType();
        uint64_t SrcSize = CGM.getDataLayout().getTypeAllocSize(SrcTy);
        uint64_t DstSize = CGM.getDataLayout().getTypeAllocSize(STy);

        // If the source type is smaller than the destination type of the
        // coerce-to logic, copy the source value into a temp alloca the size
        // of the destination type to allow loading all of it. The bits past
        // the source value are left undef.
        if (SrcSize < DstSize) {
          Address TempAlloca
            = CreateTempAlloca(STy, Src.getAlignment(),
                               Src.getName() + ".coerce");
          Builder.CreateMemCpy(TempAlloca, Src, SrcSize);
          Src = TempAlloca;
        } else {
          Src = Builder.CreateBitCast(Src,
                                      STy->getPointerTo(Src.getAddressSpace()));
        }

        assert(NumIRArgs == STy->getNumElements());
        for (unsigned i = 0, e = STy->getNumElements(); i != e; ++i) {
          Address EltPtr = Builder.CreateStructGEP(Src, i);
          llvm::Value *LI = Builder.CreateLoad(EltPtr);
          IRCallArgs[FirstIRArg + i] = LI;
        }
      } else {
        // In the simple case, just pass the coerced loaded value.
        assert(NumIRArgs == 1);
        llvm::Value *Load =
            CreateCoercedLoad(Src, ArgInfo.getCoerceToType(), *this);

        if (CallInfo.isCmseNSCall()) {
          // For certain parameter types, clear padding bits, as they may reveal
          // sensitive information.
          // Small struct/union types are passed as integer arrays.
          auto *ATy = dyn_cast<llvm::ArrayType>(Load->getType());
          if (ATy != nullptr && isa<RecordType>(I->Ty.getCanonicalType()))
            Load = EmitCMSEClearRecord(Load, ATy, I->Ty);
        }
        IRCallArgs[FirstIRArg] = Load;
      }

      break;
    }

    case ABIArgInfo::CoerceAndExpand: {
      auto coercionType = ArgInfo.getCoerceAndExpandType();
      auto layout = CGM.getDataLayout().getStructLayout(coercionType);

      llvm::Value *tempSize = nullptr;
      Address addr = Address::invalid();
      Address AllocaAddr = Address::invalid();
      if (I->isAggregate()) {
        addr = I->hasLValue() ? I->getKnownLValue().getAddress(*this)
                              : I->getKnownRValue().getAggregateAddress();

      } else {
        RValue RV = I->getKnownRValue();
        assert(RV.isScalar()); // complex should always just be direct

        llvm::Type *scalarType = RV.getScalarVal()->getType();
        auto scalarSize = CGM.getDataLayout().getTypeAllocSize(scalarType);
        auto scalarAlign = CGM.getDataLayout().getPrefTypeAlignment(scalarType);

        // Materialize to a temporary.
        addr = CreateTempAlloca(
            RV.getScalarVal()->getType(),
            CharUnits::fromQuantity(std::max(
                (unsigned)layout->getAlignment().value(), scalarAlign)),
            "tmp",
            /*ArraySize=*/nullptr, &AllocaAddr);
        tempSize = EmitLifetimeStart(scalarSize, AllocaAddr.getPointer());

        Builder.CreateStore(RV.getScalarVal(), addr);
      }

      addr = Builder.CreateElementBitCast(addr, coercionType);

      unsigned IRArgPos = FirstIRArg;
      for (unsigned i = 0, e = coercionType->getNumElements(); i != e; ++i) {
        llvm::Type *eltType = coercionType->getElementType(i);
        if (ABIArgInfo::isPaddingForCoerceAndExpand(eltType)) continue;
        Address eltAddr = Builder.CreateStructGEP(addr, i);
        llvm::Value *elt = Builder.CreateLoad(eltAddr);
        IRCallArgs[IRArgPos++] = elt;
      }
      assert(IRArgPos == FirstIRArg + NumIRArgs);

      if (tempSize) {
        EmitLifetimeEnd(tempSize, AllocaAddr.getPointer());
      }

      break;
    }

    case ABIArgInfo::Expand: {
      unsigned IRArgPos = FirstIRArg;
      ExpandTypeToArgs(I->Ty, *I, IRFuncTy, IRCallArgs, IRArgPos);
      assert(IRArgPos == FirstIRArg + NumIRArgs);
      break;
    }
    }
  }

  const CGCallee &ConcreteCallee = Callee.prepareConcreteCallee(*this);
  llvm::Value *CalleePtr = ConcreteCallee.getFunctionPointer();

  // If we're using inalloca, set up that argument.
  if (ArgMemory.isValid()) {
    llvm::Value *Arg = ArgMemory.getPointer();
    if (CallInfo.isVariadic()) {
      // When passing non-POD arguments by value to variadic functions, we will
      // end up with a variadic prototype and an inalloca call site.  In such
      // cases, we can't do any parameter mismatch checks.  Give up and bitcast
      // the callee.
      unsigned CalleeAS = CalleePtr->getType()->getPointerAddressSpace();
      CalleePtr =
          Builder.CreateBitCast(CalleePtr, IRFuncTy->getPointerTo(CalleeAS));
    } else {
      llvm::Type *LastParamTy =
          IRFuncTy->getParamType(IRFuncTy->getNumParams() - 1);
      if (Arg->getType() != LastParamTy) {
#ifndef NDEBUG
        // Assert that these structs have equivalent element types.
        llvm::StructType *FullTy = CallInfo.getArgStruct();
        llvm::StructType *DeclaredTy = cast<llvm::StructType>(
            cast<llvm::PointerType>(LastParamTy)->getElementType());
        assert(DeclaredTy->getNumElements() == FullTy->getNumElements());
        for (llvm::StructType::element_iterator DI = DeclaredTy->element_begin(),
                                                DE = DeclaredTy->element_end(),
                                                FI = FullTy->element_begin();
             DI != DE; ++DI, ++FI)
          assert(*DI == *FI);
#endif
        Arg = Builder.CreateBitCast(Arg, LastParamTy);
      }
    }
    assert(IRFunctionArgs.hasInallocaArg());
    IRCallArgs[IRFunctionArgs.getInallocaArgNo()] = Arg;
  }

  // 2. Prepare the function pointer.

  // If the callee is a bitcast of a non-variadic function to have a
  // variadic function pointer type, check to see if we can remove the
  // bitcast.  This comes up with unprototyped functions.
  //
  // This makes the IR nicer, but more importantly it ensures that we
  // can inline the function at -O0 if it is marked always_inline.
  auto simplifyVariadicCallee = [](llvm::FunctionType *CalleeFT,
                                   llvm::Value *Ptr) -> llvm::Function * {
    if (!CalleeFT->isVarArg())
      return nullptr;

    // Get underlying value if it's a bitcast
    if (llvm::ConstantExpr *CE = dyn_cast<llvm::ConstantExpr>(Ptr)) {
      if (CE->getOpcode() == llvm::Instruction::BitCast)
        Ptr = CE->getOperand(0);
    }

    llvm::Function *OrigFn = dyn_cast<llvm::Function>(Ptr);
    if (!OrigFn)
      return nullptr;

    llvm::FunctionType *OrigFT = OrigFn->getFunctionType();

    // If the original type is variadic, or if any of the component types
    // disagree, we cannot remove the cast.
    if (OrigFT->isVarArg() ||
        OrigFT->getNumParams() != CalleeFT->getNumParams() ||
        OrigFT->getReturnType() != CalleeFT->getReturnType())
      return nullptr;

    for (unsigned i = 0, e = OrigFT->getNumParams(); i != e; ++i)
      if (OrigFT->getParamType(i) != CalleeFT->getParamType(i))
        return nullptr;

    return OrigFn;
  };

  if (llvm::Function *OrigFn = simplifyVariadicCallee(IRFuncTy, CalleePtr)) {
    CalleePtr = OrigFn;
    IRFuncTy = OrigFn->getFunctionType();
  }

  // 3. Perform the actual call.

  // Deactivate any cleanups that we're supposed to do immediately before
  // the call.
  if (!CallArgs.getCleanupsToDeactivate().empty())
    deactivateArgCleanupsBeforeCall(*this, CallArgs);

  // Assert that the arguments we computed match up.  The IR verifier
  // will catch this, but this is a common enough source of problems
  // during IRGen changes that it's way better for debugging to catch
  // it ourselves here.
#ifndef NDEBUG
  assert(IRCallArgs.size() == IRFuncTy->getNumParams() || IRFuncTy->isVarArg());
  for (unsigned i = 0; i < IRCallArgs.size(); ++i) {
    // Inalloca argument can have different type.
    if (IRFunctionArgs.hasInallocaArg() &&
        i == IRFunctionArgs.getInallocaArgNo())
      continue;
    if (i < IRFuncTy->getNumParams())
      assert(IRCallArgs[i]->getType() == IRFuncTy->getParamType(i));
  }
#endif

  // Update the largest vector width if any arguments have vector types.
  for (unsigned i = 0; i < IRCallArgs.size(); ++i) {
    if (auto *VT = dyn_cast<llvm::VectorType>(IRCallArgs[i]->getType()))
      LargestVectorWidth =
          std::max((uint64_t)LargestVectorWidth,
                   VT->getPrimitiveSizeInBits().getKnownMinSize());
  }

  // Compute the calling convention and attributes.
  unsigned CallingConv;
  llvm::AttributeList Attrs;
  CGM.ConstructAttributeList(CalleePtr->getName(), CallInfo,
                             Callee.getAbstractInfo(), Attrs, CallingConv,
                             /*AttrOnCallSite=*/true);

  if (const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(CurFuncDecl))
    if (FD->usesFPIntrin())
      // All calls within a strictfp function are marked strictfp
      Attrs =
        Attrs.addAttribute(getLLVMContext(), llvm::AttributeList::FunctionIndex,
                           llvm::Attribute::StrictFP);

  // Add call-site nomerge attribute if exists.
  if (InNoMergeAttributedStmt)
    Attrs =
      Attrs.addAttribute(getLLVMContext(), llvm::AttributeList::FunctionIndex,
                         llvm::Attribute::NoMerge);

  // Apply some call-site-specific attributes.
  // TODO: work this into building the attribute set.

  // Apply always_inline to all calls within flatten functions.
  // FIXME: should this really take priority over __try, below?
  if (CurCodeDecl && CurCodeDecl->hasAttr<FlattenAttr>() &&
      !(TargetDecl && TargetDecl->hasAttr<NoInlineAttr>())) {
    Attrs =
        Attrs.addAttribute(getLLVMContext(), llvm::AttributeList::FunctionIndex,
                           llvm::Attribute::AlwaysInline);
  }

  // Disable inlining inside SEH __try blocks.
  if (isSEHTryScope()) {
    Attrs =
        Attrs.addAttribute(getLLVMContext(), llvm::AttributeList::FunctionIndex,
                           llvm::Attribute::NoInline);
  }

  // Decide whether to use a call or an invoke.
  bool CannotThrow;
  if (currentFunctionUsesSEHTry()) {
    // SEH cares about asynchronous exceptions, so everything can "throw."
    CannotThrow = false;
  } else if (isCleanupPadScope() &&
             EHPersonality::get(*this).isMSVCXXPersonality()) {
    // The MSVC++ personality will implicitly terminate the program if an
    // exception is thrown during a cleanup outside of a try/catch.
    // We don't need to model anything in IR to get this behavior.
    CannotThrow = true;
  } else {
    // Otherwise, nounwind call sites will never throw.
    CannotThrow = Attrs.hasFnAttribute(llvm::Attribute::NoUnwind);

    if (auto *FPtr = dyn_cast<llvm::Function>(CalleePtr))
      if (FPtr->hasFnAttribute(llvm::Attribute::NoUnwind))
        CannotThrow = true;
  }

  // If we made a temporary, be sure to clean up after ourselves. Note that we
  // can't depend on being inside of an ExprWithCleanups, so we need to manually
  // pop this cleanup later on. Being eager about this is OK, since this
  // temporary is 'invisible' outside of the callee.
  if (UnusedReturnSizePtr)
    pushFullExprCleanup<CallLifetimeEnd>(NormalEHLifetimeMarker, SRetAlloca,
                                         UnusedReturnSizePtr);

  llvm::BasicBlock *InvokeDest = CannotThrow ? nullptr : getInvokeDest();

  SmallVector<llvm::OperandBundleDef, 1> BundleList =
      getBundlesForFunclet(CalleePtr);

  if (const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(CurFuncDecl))
    if (FD->usesFPIntrin())
      // All calls within a strictfp function are marked strictfp
      Attrs =
        Attrs.addAttribute(getLLVMContext(), llvm::AttributeList::FunctionIndex,
                           llvm::Attribute::StrictFP);

  AssumeAlignedAttrEmitter AssumeAlignedAttrEmitter(*this, TargetDecl);
  Attrs = AssumeAlignedAttrEmitter.TryEmitAsCallSiteAttribute(Attrs);

  AllocAlignAttrEmitter AllocAlignAttrEmitter(*this, TargetDecl, CallArgs);
  Attrs = AllocAlignAttrEmitter.TryEmitAsCallSiteAttribute(Attrs);

  // Emit the actual call/invoke instruction.
  llvm::CallBase *CI;
  if (!InvokeDest) {
    CI = Builder.CreateCall(IRFuncTy, CalleePtr, IRCallArgs, BundleList);
  } else {
    llvm::BasicBlock *Cont = createBasicBlock("invoke.cont");
    CI = Builder.CreateInvoke(IRFuncTy, CalleePtr, Cont, InvokeDest, IRCallArgs,
                              BundleList);
    EmitBlock(Cont);
  }
  if (callOrInvoke)
    *callOrInvoke = CI;

  // If this is within a function that has the guard(nocf) attribute and is an
  // indirect call, add the "guard_nocf" attribute to this call to indicate that
  // Control Flow Guard checks should not be added, even if the call is inlined.
  if (const auto *FD = dyn_cast_or_null<FunctionDecl>(CurFuncDecl)) {
    if (const auto *A = FD->getAttr<CFGuardAttr>()) {
      if (A->getGuard() == CFGuardAttr::GuardArg::nocf && !CI->getCalledFunction())
        Attrs = Attrs.addAttribute(
            getLLVMContext(), llvm::AttributeList::FunctionIndex, "guard_nocf");
    }
  }

  // Apply the attributes and calling convention.
  CI->setAttributes(Attrs);
  CI->setCallingConv(static_cast<llvm::CallingConv::ID>(CallingConv));

  // Apply various metadata.

  if (!CI->getType()->isVoidTy())
    CI->setName("call");

  // Update largest vector width from the return type.
  if (auto *VT = dyn_cast<llvm::VectorType>(CI->getType()))
    LargestVectorWidth =
        std::max((uint64_t)LargestVectorWidth,
                 VT->getPrimitiveSizeInBits().getKnownMinSize());

  // Insert instrumentation or attach profile metadata at indirect call sites.
  // For more details, see the comment before the definition of
  // IPVK_IndirectCallTarget in InstrProfData.inc.
  if (!CI->getCalledFunction())
    PGO.valueProfile(Builder, llvm::IPVK_IndirectCallTarget,
                     CI, CalleePtr);

  // In ObjC ARC mode with no ObjC ARC exception safety, tell the ARC
  // optimizer it can aggressively ignore unwind edges.
  if (CGM.getLangOpts().ObjCAutoRefCount)
    AddObjCARCExceptionMetadata(CI);

  // Suppress tail calls if requested.
  if (llvm::CallInst *Call = dyn_cast<llvm::CallInst>(CI)) {
    if (TargetDecl && TargetDecl->hasAttr<NotTailCalledAttr>())
      Call->setTailCallKind(llvm::CallInst::TCK_NoTail);
  }

  // Add metadata for calls to MSAllocator functions
  if (getDebugInfo() && TargetDecl &&
      TargetDecl->hasAttr<MSAllocatorAttr>())
    getDebugInfo()->addHeapAllocSiteMetadata(CI, RetTy->getPointeeType(), Loc);

  // 4. Finish the call.

  // If the call doesn't return, finish the basic block and clear the
  // insertion point; this allows the rest of IRGen to discard
  // unreachable code.
  if (CI->doesNotReturn()) {
    if (UnusedReturnSizePtr)
      PopCleanupBlock();

    // Strip away the noreturn attribute to better diagnose unreachable UB.
    if (SanOpts.has(SanitizerKind::Unreachable)) {
      // Also remove from function since CallBase::hasFnAttr additionally checks
      // attributes of the called function.
      if (auto *F = CI->getCalledFunction())
        F->removeFnAttr(llvm::Attribute::NoReturn);
      CI->removeAttribute(llvm::AttributeList::FunctionIndex,
                          llvm::Attribute::NoReturn);

      // Avoid incompatibility with ASan which relies on the `noreturn`
      // attribute to insert handler calls.
      if (SanOpts.hasOneOf(SanitizerKind::Address |
                           SanitizerKind::KernelAddress)) {
        SanitizerScope SanScope(this);
        llvm::IRBuilder<>::InsertPointGuard IPGuard(Builder);
        Builder.SetInsertPoint(CI);
        auto *FnType = llvm::FunctionType::get(CGM.VoidTy, /*isVarArg=*/false);
        llvm::FunctionCallee Fn =
            CGM.CreateRuntimeFunction(FnType, "__asan_handle_no_return");
        EmitNounwindRuntimeCall(Fn);
      }
    }

    EmitUnreachable(Loc);
    Builder.ClearInsertionPoint();

    // FIXME: For now, emit a dummy basic block because expr emitters in
    // generally are not ready to handle emitting expressions at unreachable
    // points.
    EnsureInsertPoint();

    // Return a reasonable RValue.
    return GetUndefRValue(RetTy);
  }

  // Perform the swifterror writeback.
  if (swiftErrorTemp.isValid()) {
    llvm::Value *errorResult = Builder.CreateLoad(swiftErrorTemp);
    Builder.CreateStore(errorResult, swiftErrorArg);
  }

  // Emit any call-associated writebacks immediately.  Arguably this
  // should happen after any return-value munging.
  if (CallArgs.hasWritebacks())
    emitWritebacks(*this, CallArgs);

  // The stack cleanup for inalloca arguments has to run out of the normal
  // lexical order, so deactivate it and run it manually here.
  CallArgs.freeArgumentMemory(*this);

  // Extract the return value.
  RValue Ret = [&] {
    switch (RetAI.getKind()) {
    case ABIArgInfo::CoerceAndExpand: {
      auto coercionType = RetAI.getCoerceAndExpandType();

      Address addr = SRetPtr;
      addr = Builder.CreateElementBitCast(addr, coercionType);

      assert(CI->getType() == RetAI.getUnpaddedCoerceAndExpandType());
      bool requiresExtract = isa<llvm::StructType>(CI->getType());

      unsigned unpaddedIndex = 0;
      for (unsigned i = 0, e = coercionType->getNumElements(); i != e; ++i) {
        llvm::Type *eltType = coercionType->getElementType(i);
        if (ABIArgInfo::isPaddingForCoerceAndExpand(eltType)) continue;
        Address eltAddr = Builder.CreateStructGEP(addr, i);
        llvm::Value *elt = CI;
        if (requiresExtract)
          elt = Builder.CreateExtractValue(elt, unpaddedIndex++);
        else
          assert(unpaddedIndex == 0);
        Builder.CreateStore(elt, eltAddr);
      }
      // FALLTHROUGH
      LLVM_FALLTHROUGH;
    }

    case ABIArgInfo::InAlloca:
    case ABIArgInfo::Indirect: {
      RValue ret = convertTempToRValue(SRetPtr, RetTy, SourceLocation());
      if (UnusedReturnSizePtr)
        PopCleanupBlock();
      return ret;
    }

    case ABIArgInfo::Ignore:
      // If we are ignoring an argument that had a result, make sure to
      // construct the appropriate return value for our caller.
      return GetUndefRValue(RetTy);

    case ABIArgInfo::Extend:
    case ABIArgInfo::Direct: {
      llvm::Type *RetIRTy = ConvertType(RetTy);
      if (RetAI.getCoerceToType() == RetIRTy && RetAI.getDirectOffset() == 0) {
        switch (getEvaluationKind(RetTy)) {
        case TEK_Complex: {
          llvm::Value *Real = Builder.CreateExtractValue(CI, 0);
          llvm::Value *Imag = Builder.CreateExtractValue(CI, 1);
          return RValue::getComplex(std::make_pair(Real, Imag));
        }
        case TEK_Aggregate: {
          Address DestPtr = ReturnValue.getValue();
          bool DestIsVolatile = ReturnValue.isVolatile();

          if (!DestPtr.isValid()) {
            DestPtr = CreateMemTemp(RetTy, "agg.tmp");
            DestIsVolatile = false;
          }
          EmitAggregateStore(CI, DestPtr, DestIsVolatile);
          return RValue::getAggregate(DestPtr);
        }
        case TEK_Scalar: {
          // If the argument doesn't match, perform a bitcast to coerce it.  This
          // can happen due to trivial type mismatches.
          llvm::Value *V = CI;
          if (V->getType() != RetIRTy)
            V = Builder.CreateBitCast(V, RetIRTy);
          return RValue::get(V);
        }
        }
        llvm_unreachable("bad evaluation kind");
      }

      Address DestPtr = ReturnValue.getValue();
      bool DestIsVolatile = ReturnValue.isVolatile();

      if (!DestPtr.isValid()) {
        DestPtr = CreateMemTemp(RetTy, "coerce");
        DestIsVolatile = false;
      }

      // If the value is offset in memory, apply the offset now.
      Address StorePtr = emitAddressAtOffset(*this, DestPtr, RetAI);
      CreateCoercedStore(CI, StorePtr, DestIsVolatile, *this);

      return convertTempToRValue(DestPtr, RetTy, SourceLocation());
    }

    case ABIArgInfo::Expand:
    case ABIArgInfo::IndirectAliased:
      llvm_unreachable("Invalid ABI kind for return argument");
    }

    llvm_unreachable("Unhandled ABIArgInfo::Kind");
  } ();

  // Emit the assume_aligned check on the return value.
  if (Ret.isScalar() && TargetDecl) {
    AssumeAlignedAttrEmitter.EmitAsAnAssumption(Loc, RetTy, Ret);
    AllocAlignAttrEmitter.EmitAsAnAssumption(Loc, RetTy, Ret);
  }

  // Explicitly call CallLifetimeEnd::Emit just to re-use the code even though
  // we can't use the full cleanup mechanism.
  for (CallLifetimeEnd &LifetimeEnd : CallLifetimeEndAfterCall)
    LifetimeEnd.Emit(*this, /*Flags=*/{});

  if (!ReturnValue.isExternallyDestructed() &&
      RetTy.isDestructedType() == QualType::DK_nontrivial_c_struct)
    pushDestroy(QualType::DK_nontrivial_c_struct, Ret.getAggregateAddress(),
                RetTy);

  return Ret;
}

CGCallee CGCallee::prepareConcreteCallee(CodeGenFunction &CGF) const {
  if (isVirtual()) {
    const CallExpr *CE = getVirtualCallExpr();
    return CGF.CGM.getCXXABI().getVirtualFunctionPointer(
        CGF, getVirtualMethodDecl(), getThisAddress(), getVirtualFunctionType(),
        CE ? CE->getBeginLoc() : SourceLocation());
  }

  return *this;
}

/* VarArg handling */

Address CodeGenFunction::EmitVAArg(VAArgExpr *VE, Address &VAListAddr) {
  VAListAddr = VE->isMicrosoftABI()
                 ? EmitMSVAListRef(VE->getSubExpr())
                 : EmitVAListRef(VE->getSubExpr());
  QualType Ty = VE->getType();
  if (VE->isMicrosoftABI())
    return CGM.getTypes().getABIInfo().EmitMSVAArg(*this, VAListAddr, Ty);
  return CGM.getTypes().getABIInfo().EmitVAArg(*this, VAListAddr, Ty);
}
