# Source-contract validation

This directory checks that the handwritten Lean meanings agree with the pinned Zesu source. It is a
test and falsification layer, not part of the compliance theorem: production proof modules are
forbidden from importing `Validation`.

The validation uses one shared set of examples in two ways:

1. The host Zig probe calls the real source routines and compares their exact values, errors, and
   allocation events with the expected vectors.
2. `RoutineMeaningVectors.lean` evaluates the corresponding handwritten Lean `meaning` definitions
   against those same expectations with `native_decide`.

Together, those checks compare each source routine with its Lean meaning without making test results
an assumption of the theorem. `MeaningAgreement.lean` adds an end-to-end acceptance check against the
independent SSZ oracle. `ContractRunner.lean` is the small executable used for large cases that are
impractical to evaluate inside `native_decide`.

Files named `Generated*.lean` are deterministic outputs of the corpus/vector generators and should
not be edited by hand.

Row C adds checks against execution of the unchanged production ELF:

- `BinaryOccurrenceCheck.lean` is a small end-to-end example for one optional decoder and its three
  child readers.
- `ScaleOccurrenceCheck.lean` checks reduced evidence for all 141 compiled occurrences.
- the corresponding `*Types.lean` files define the deterministic evidence format.

The capture and reduction tools live in `targets/ssz/zesu/trace/`; see its README before changing an
evidence field or interpreting a pass, failure, or gap.
