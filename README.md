# The LLVM Compiler Infrastructure - 

This directory and its sub-directories contain source code for LLVM,
a toolkit for the construction of highly optimized compilers,
optimizers, and run-time environments.

Specifically, this repository contains modifications for "Cross-Translation Unit Optimization via Annotated Headers" an LLVM GSoC project which has a paper in submission to the LLVM Developer's meeting.

## Abstract

LLVM automatically derives facts that are only used while the respective translation unit, or LLVM module, is processed (i.e. constant function, error-throwing, etc). This is true both in standard
compilation but also link-time-optimization (LTO) in which the
module is (partially) merged with others in the same project at link
time. LTO is able to take advantage of this to optimize functions
calls to outside the translation unit. However, LTO doesn’t solve
the problem for two reasons of practicality: LTO comes with a nontrivial compile-time investment; and many libraries upon which a
program could depend, do not ship with LTO information, simply
headers and binaries. In this extended abstract, we solve the problem by generating annotated versions of the source code that also
include this derived information. Such an approach has the benefits of both worlds: allowing optimizations previously limited to
LTO without running LTO and only requiring C/C++-compatible
headers. Our modified Clang understands three custom attributes
that encode arbitrary LLVM-IR attributes and it can emit C/C++-
compatible headers with the aforementioned attribute embedded
based on the information available in the LLVM-IR. We test the
approach experimentally on the DOE RSBench proxy application
and verify that it provides the expected speedups.

In this extended abstract, we propose solving the problem by generating at compile-time, annotated versions of the source code that
also include derived information about the functions compiled.
This allows us to largely get the benefits of both worlds: we can
run many performance-enhancing optimizations previously limited
to LTO, while still only providing headers and not running LTO.

## Implementation

Our prototype is an extended versions of both LLVM and Clang.

```c
#File: annotations.h
__attribute__((fn_attr("readnone"),
fn_attr("nounwind"), ...))
Complex fast_cexp(Complex);
```
Figure: Annotated declaration of the fast cexp function
in the RSBench proxy application. Several LLVM-IR attributes were deduced and annotated, including readnone (aka.
attribute ((const))) and nounwind (similar to noexcept).


First, we extended Clang to understand arbitrary LLVM attributes
not available in standard C/C++. Specifically, we added three new
attributes for C/C++ function declarations: fn_attr("attr"),
arg_attr(arg, "attr"), and ret_attr("attr"). The first attaches "attr" to the function, the second to the argument arg, and
the third to the return value of the function. These attributes are exemplary shown in the above Figure.

Second, we extended LLVM to emit the annotated headers.
These headers contain conforming C declarations3 with annotations
for attributes deduced for the function, arguments, and return value.

To use these headers, we exploit the fact that C allows to redeclare a function. The annotated headers can be included at the start
of each translation unit (via -include header.h). To deal with
recursive and custom types that are used in the function declaration, we forward declare any non-builtin types (as opaque types)
to ensure it is legal to make the declaration.
For similar reasons,
we also desugar any typedefs into their actual type. At this point
it is important to note that the annotated headers are not meant for
human consumption nor as a replacement for existing headers.

### Limitations and Future Work
* Multiple definitions with the same name are not handled yet
and will most likely cause problems. We expect to implement a
detection and blacklisting scheme for such definitions.
* We want to provide tooling support to verify existing annotations, manually or automatic generated, such that the need for
annotated header regeneration can be determined automatically.
* We want to generate existing C/C++ annotations whenever
possible to allow other compilers to benefit from the annotated headers as well. As an example, the readnone annotation in Figure could be replaced by the widely supported
attribute ((const)).

### Patches
[WIP] Create a clang attribute that lets users specify LLVM attributes.
Available from: https://reviews.llvm.org/D63845.
[WIP] LLVM Optimization Remark for Attributes. Available from:
https://reviews.llvm.org/D65169.
