# Zesu contract validation

This directory tests the handwritten Lean meanings against the pinned Zesu source and the independent
SSZ specification. These finite checks can expose a wrong contract before it is used in a machine-code
proof. They are supporting evidence, not premises of the compliance theorem; the build rejects imports
of `Validation` from production proof modules.

The same expected examples are checked in two places:

1. The [host Zig probe](../../../verification-target/zesu/probe/README.md) calls the real source
   functions and compares their values, errors, and allocation events with the expected results.
2. [SourceFunctionMeaningVectors.lean](SourceFunctionMeaningVectors.lean) evaluates the corresponding
   handwritten Lean meanings against those results with `native_decide`.

Together, these checks compare each source function with its Lean meaning without turning a test result
into a theorem assumption. [MeaningAgreement.lean](MeaningAgreement.lean) checks the small whole-input
corpus against the independent SSZ specification. [ContractRunner.lean](ContractRunner.lean) exposes
that specification as a command-line program so the external agreement test can cover inputs that are
too large to evaluate conveniently with `native_decide`.

[GeneratedCorpus.lean](GeneratedCorpus.lean) and
[GeneratedSourceFunctionVectors.lean](GeneratedSourceFunctionVectors.lean) contain the committed,
deterministically generated examples. Their headers identify the generating commands; edit the generators under
[verification-target/zesu/tests](../../../verification-target/zesu/tests/README.md), not these files.
