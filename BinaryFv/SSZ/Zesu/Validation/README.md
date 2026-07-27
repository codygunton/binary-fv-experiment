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

[ObserverMutation.lean](ObserverMutation.lean) checks the value observer from the other side. The
correspondence proof says
the observer reads back whatever the representation holds, which cannot catch an observer that
ignores a field; so this corrupts one byte per layout family in the memory a real accepted decode
left behind and checks each corruption moves the observation. Its control is the payload of an
*absent* optional, which must not move it.

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

Row D adds [RunnerExecution.lean](RunnerExecution.lean), which runs the pinned RISC-V binary in the
Sail model: it builds the entry state, steps to the return sentinel, executes both exported
accessors, observes the full value, and compares the result with the same SSZ oracle. Accepted corpus
cases are compared field for field through the canonical value rendering. Additional cases establish
that a short budget is fuel exhaustion, a misplaced observer is a malformed result, and a refused
second call is a bad return rather than a rejection.

Row D½ measures what the conditional local premise actually says:

- [BoundarySatisfiability.lean](BoundarySatisfiability.lean) and
  [ContractGroundTruth.lean](ContractGroundTruth.lean) provide structural and captured-run evidence.
  The latter now decides the universal `WritesOnlyWithinOwnRecord` clause exactly by a
  quotient-lifted direct hash-map fold; its Boolean–Prop equivalence and outside/inside mutations
  expose a fifth scalar-post refutation that the old partial checker hid.
- [RepairBlastRadius.lean](RepairBlastRadius.lean) pins the populations behind the three human
  rulings without changing the extractor or contracts: 108 occurrence-local offset bindings, the
  exact loss and residue of entry-PC deduplication/removal/relocation, the 46/73/8 inline-start and
  82/45 inline-finish partitions, their exact cross-product, and checked paths for all eight
  ancestor-entry pairs whose borrowed PCs lie outside the old parent scopes. It preserves the old
  inventory-only counts, demonstrates that empty `InlineBoundary.entries` were accepted and
  operationally unused, and pins the remaining 180/173/7 resolved-call split and common `memcpy`
  tail-call target. It also measures the 3.315× instruction-occurrence cost of proving every nested
  appearance again with `ownStep`; [LocalObligationLedger.lean](LocalObligationLedger.lean) checks
  that the seven tail-call exits are reported but deliberately excluded from structural blockers.
- [EntryPcPlacement.lean](EntryPcPlacement.lean) proves that every source-selected entry predicate
  ignores `PC`, then joins that fact to the trace consumer's fixed-entry requirement and
  per-instance pre-satisfiability. The result is an exact pre-repair blast radius: all 141 closed
  obligations are false. For local obligations it proves only the conditional join and retains the
  ledger's 0/28/16/97 provable/false/vacuous/unknown split; a private PC-sensitive mutation is the
  negative control for the measurement.
- [LocalObligationRefutations.lean](LocalObligationRefutations.lean) joins both hypothesis layers and
  proves 28 individual local obligations false: 16 with no callees and 12 whose `bytesAt`/`readU32`
  callee exits make the outer premise inhabitable. It also proves that the copy contracts admit a
  pre-state from which no post-state can preserve both copied bytes and `CodeIntact`; this makes the
  outer premise impossible for 13 parents with a `memcpy` or `memmove` callee, and proves those
  obligations only by vacuity. Three further parents are vacuous because unconstrained result bases
  make accepted `forkConfig`, `optionalU64`, and `optionalBlobSchedule` representations conflict
  with file-backed code.
- [LocalObligationLedger.lean](LocalObligationLedger.lean) classifies all 141 instances without
  treating gaps as passes. Its committed
  [Markdown ledger](../../../../targets/ssz/zesu/trace/LOCAL_OBLIGATION_LEDGER.md) is regenerated and
  byte-diffed by `nix/proof.nix`.
