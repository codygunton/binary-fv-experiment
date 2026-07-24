# Source-contract validation

This directory checks that the handwritten Lean meanings agree with the pinned Zesu source. It is a
test and falsification layer, not part of the compliance theorem: production proof modules are
forbidden from importing `Validation`.

The validation uses the same expected routine vectors in two ways:

1. The [host Zig probe](../../../../targets/ssz/zesu/probe/README.md) calls the real source
   routines and compares their values, errors, and allocation events with the expected vectors.
2. [RoutineMeaningVectors.lean](RoutineMeaningVectors.lean) evaluates the corresponding handwritten
   Lean `meaning` definitions against those expectations with `native_decide`.

Together, those checks compare each source routine with its Lean meaning without making test results
an assumption of the theorem. [MeaningAgreement.lean](MeaningAgreement.lean) checks the small
whole-input corpus against the independent SSZ oracle.
[ContractRunner.lean](ContractRunner.lean) is the executable oracle used by the external agreement
driver for cases that are impractical to reduce inside Lean's kernel.

Row C adds checks against execution of the unchanged production ELF:

[GeneratedCorpus.lean](GeneratedCorpus.lean) and
[GeneratedRoutineVectors.lean](GeneratedRoutineVectors.lean) are deterministic generator outputs.
Their headers identify the generating commands; edit the generators under
[targets/ssz/zesu/tests](../../../../targets/ssz/zesu/tests/README.md), not these files.

- [BinaryFunctionInstanceCheck.lean](BinaryFunctionInstanceCheck.lean) checks one optional decoder function instance
  and its three child readers as a small end-to-end example.
- [ScaleFunctionInstanceCheck.lean](ScaleFunctionInstanceCheck.lean) checks reduced evidence for all 141 compiled
  function instances. Its outcomes distinguish passes, failures, and explicit gaps.
- [BinaryFunctionInstanceTypes.lean](BinaryFunctionInstanceTypes.lean) and
  [ScaleFunctionInstanceTypes.lean](ScaleFunctionInstanceTypes.lean) define the corresponding evidence formats.
- [GeneratedBinaryEvidence.lean](GeneratedBinaryEvidence.lean) and
  [GeneratedScaleEvidence.lean](GeneratedScaleEvidence.lean) are deterministic outputs of the Row C
  trace reducers and must not be edited by hand.

The [trace README](../../../../targets/ssz/zesu/trace/README.md) explains capture and reduction before
these Lean checks consume the evidence.
