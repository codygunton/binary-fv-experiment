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

`ObserverMutation.lean` checks the value observer from the other side. The correspondence proof says
the observer reads back whatever the representation holds, which cannot catch an observer that
ignores a field; so this corrupts one byte per layout family in the memory a real accepted decode
left behind and checks each corruption moves the observation. Its control is the payload of an
*absent* optional, which must not move it.

Row D adds the strongest check in this directory, `RunnerExecution.lean`: it *runs the pinned RISC-V
binary in the Sail model* — entry state, machine steps to the return sentinel, both exported
accessors, and the full value observation — and compares the result with the same SSZ oracle. On the
corpus's accepted cases that comparison is field for field, through the canonical value render. Its
other checks pin the failure modes a corpus cannot express: a short budget is fuel exhaustion, a
misplaced observer is a malformed result, and a refused *second* call is a bad return rather than a
rejection.

Row C adds checks against execution of the unchanged production ELF:

[GeneratedCorpus.lean](GeneratedCorpus.lean) and
[GeneratedRoutineVectors.lean](GeneratedRoutineVectors.lean) are deterministic generator outputs.
Their headers identify the generating commands; edit the generators under
[targets/ssz/zesu/tests](../../../../targets/ssz/zesu/tests/README.md), not these files.

- [BinaryOccurrenceCheck.lean](BinaryOccurrenceCheck.lean) checks one optional decoder occurrence
  and its three child readers as a small end-to-end example.
- [ScaleOccurrenceCheck.lean](ScaleOccurrenceCheck.lean) checks reduced evidence for all 141 compiled
  occurrences. Its outcomes distinguish passes, failures, and explicit gaps.
- [BinaryOccurrenceTypes.lean](BinaryOccurrenceTypes.lean) and
  [ScaleOccurrenceTypes.lean](ScaleOccurrenceTypes.lean) define the corresponding evidence formats.
- [GeneratedBinaryEvidence.lean](GeneratedBinaryEvidence.lean) and
  [GeneratedScaleEvidence.lean](GeneratedScaleEvidence.lean) are deterministic outputs of the Row C
  trace reducers and must not be edited by hand.

The [trace README](../../../../targets/ssz/zesu/trace/README.md) explains capture and reduction before
these Lean checks consume the evidence.
