import BinaryFv.RiscV.Proof.RunnerCorrespondence
import BinaryFv.SSZ.SpecBridge.Decode
import BinaryFv.SSZ.Zesu.Artifact.Symbols
import BinaryFv.SSZ.Zesu.MemoryRepresentation.Result
import BinaryFv.SSZ.Zesu.Contracts.ProgramCorrectness
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Runner

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open BinaryFv.Binary.Elfling
open LeanRV64DExecutable.Functions Register

set_option maxRecDepth 10000

/-- The concrete state at which the public `zesu_decode_raw` call begins.

The remaining ABI arguments will be added here as their entry contracts are proved; unlike a
root-level equality, this predicate gives those contracts a single visible home. -/
structure DecodeEntryRep (state : State) (inputBase : Nat) (input : ByteArray)
    (sentinel : BitVec 64) where
  entryPC : Nat
  entryResolved : ∃ entry, Artifact.zesuDecodeRaw = .ok entry ∧ entry.value = entryPC
  pc : state.regs.get? PC = some (BitVec.ofNat 64 entryPC)
  returnAddress : state.regs.get? x1 = some sentinel
  program : Artifact.programImage.matchesMemory state.mem
  inputMemory : MemoryBytes state inputBase input

/-! ## What a complete run of the exported wrapper looks like

These two witnesses are stated in the **runner's** terms, not the internal decoder's. Every address
is the pinned one — the builder's own entry state, `sentinelWord`, `canonicalRunnerLayout.inputBase`,
`canonicalResultBuffer` — and the result is read from the wrapper's own globals and its two exported
accessors. The earlier versions carried a free `inputBase`/`resultBase`/`sentinel` and observed the
*internal* `zesu_result` status word, which is a different calling convention: the wrapper stores its
outcome in an inline optional and reports its status through `zesu_raw_error`, so a witness phrased
against the internal slot could not be consumed by the runner at all.

`Runner.lean`'s `executeDecode_accepted_of_run` / `executeDecode_rejected_of_run` consume exactly
these fields, which is what lets `BinaryFv/SSZ/Root.lean` conclude the public answer without
reconstructing any machine detail.

The `TraceToSentinel` field is where the existing exact-PC retirements and block traces connect:
`ParserBlocks` supplies primitive decoding fragments, `Analysis.ResultLayout` supplies the current
chain-config/blob-schedule fragment, and the remaining function/loop proofs must compose them into
this one live trace. -/

/-- A complete successful run of the exported wrapper, ending with the accepted value represented in
the canonical result buffer and both accessors agreeing. -/
structure SuccessfulRun (input : ByteArray) (value : SszBridge.RawV4) where
  /-- The state the builder produces from `initialState`. -/
  entryState : State
  /-- The state the decode call returns in. -/
  finalState : State
  /-- The state after both accessor calls have run. -/
  afterAccessors : State
  /-- Retirements from the entry to the sentinel. -/
  stepCount : Nat
  builds : Runs (buildZesuEntryState input) initialState entryState ()
  trace : TraceToSentinel sentinelWord 0 stepCount entryState finalState
  /-- The exported function instance contract's own bound; the runner's fuel strictly exceeds it. -/
  withinStepBound : stepCount ≤ entryStepBound input.size
  returnCode : observeReturnCode? finalState = some 1
  storedPresent : observeOptionTag? finalState storedResultDiscriminantAddr = some true
  inputPreserved : MemoryBytes finalState canonicalRunnerLayout.inputBase input
  storedValue : RawV4Rep finalState canonicalRunnerLayout.inputBase input
    Elfling.canonicalResultBuffer value
  /-- `zesu_raw_result` returns the canonical buffer and `zesu_raw_error` the `ok` status. -/
  accessors : Runs (runAccessorsIfReached resolvedSymbols (.reached stepCount))
    finalState afterAccessors
    (.returned Elfling.canonicalResultBuffer, .returned Contracts.DecodeStatus.ok.code)

/-- A complete run which the specification also rejects: the wrapper returns `0`, stores nothing,
and records a status the specification itself can produce. -/
structure RejectedRun (input : ByteArray) where
  entryState : State
  finalState : State
  afterAccessors : State
  stepCount : Nat
  /-- The recorded `DecodeStatus` code. -/
  status : Nat
  builds : Runs (buildZesuEntryState input) initialState entryState ()
  trace : TraceToSentinel sentinelWord 0 stepCount entryState finalState
  withinStepBound : stepCount ≤ entryStepBound input.size
  returnCode : observeReturnCode? finalState = some 0
  storedAbsent : observeOptionTag? finalState storedResultDiscriminantAddr = some false
  /-- Not merely "nonzero": an exhausted arena and a refused second call are also nonzero, and
  neither is a rejection. -/
  specRejection : statusCategory status = .specRejection
  /-- `zesu_raw_result` returns null and `zesu_raw_error` the recorded status. -/
  accessors : Runs (runAccessorsIfReached resolvedSymbols (.reached stepCount))
    finalState afterAccessors (.returned 0, .returned status)

/-- Authorized navigation scaffold: an accepted SizzLean input has a canonical generated Elfling
program that satisfies the whole compliance obligation, together with a complete live Sail execution
whose final state represents the same value.

Bundling the program obligation into the witness of this theorem is what makes the root theorem
descend through Elfling program correctness rather than bypass it: the successful trace cannot be
produced without also producing `sszComplianceObligations`, so the eventual proof owes it. -/
theorem successful_trace_of_spec_accepts (input : ByteArray)
    (inputBound : input.size < 2 * 1024 * 1024) (value : SszBridge.RawV4)
    (specAccepts : SszSpec.decode input = .accepted value) :
    ∃ program : Program,
      Contracts.IsCanonicalGeneratedProgram program ∧
      Contracts.sszComplianceObligations program ∧
      Nonempty (SuccessfulRun input value) := by
  sorry

/-- Authorized navigation scaffold: a rejected SizzLean input likewise has the canonical program
obligation and a classified live Sail path recording a spec-producible rejection status. -/
theorem rejected_trace_of_spec_rejects (input : ByteArray)
    (inputBound : input.size < 2 * 1024 * 1024)
    (specRejects : SszSpec.decode input = .rejected) :
    ∃ program : Program,
      Contracts.IsCanonicalGeneratedProgram program ∧
      Contracts.sszComplianceObligations program ∧
      Nonempty (RejectedRun input) := by
  sorry

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
