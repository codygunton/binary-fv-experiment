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

[GeneratedCorpus.lean](GeneratedCorpus.lean) and
[GeneratedRoutineVectors.lean](GeneratedRoutineVectors.lean) are deterministic generator outputs.
Their headers identify the generating commands; edit the generators under
[targets/ssz/zesu/tests](../../../../targets/ssz/zesu/tests/README.md), not these files.
