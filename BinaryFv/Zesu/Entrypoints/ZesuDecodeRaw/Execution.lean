import BinaryFv.RiscV.Proof.RunnerCorrespondence
import BinaryFv.Specs.SSZ.Decode
import BinaryFv.Zesu.Artifacts.Symbols
import BinaryFv.Zesu.MemoryRepresentation.Result
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Runner

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.RiscV
open BinaryFv.Zesu
open BinaryFv.Zesu.MemoryRepresentation
open BinaryFv.Binary.Elfling
open LeanRV64DExecutable.Functions Register

set_option maxRecDepth 10000

/-- The concrete state at which the public `zesu_decode_raw` call begins.

The remaining ABI arguments will be added here as their entry contracts are proved; unlike a
root-level equality, this predicate gives those contracts a single visible home. -/
structure DecodeEntryRep (state : State) (inputBase : Nat) (input : ByteArray)
    (sentinel : BitVec 64) where
  entryPC : Nat
  entryResolved : ∃ entry, Artifacts.zesuDecodeRaw = .ok entry ∧ entry.value = entryPC
  pc : state.regs.get? PC = some (BitVec.ofNat 64 entryPC)
  returnAddress : state.regs.get? x1 = some sentinel
  program : Artifacts.programImage.matchesMemory state.mem
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
these fields, which is what lets `BinaryFv/Zesu/Root.lean` conclude the public answer without
reconstructing any machine detail.

The `TraceToSentinel` field is where the existing exact-PC retirements and block traces connect:
`ParserBlocks` supplies primitive decoding fragments, `Analysis.ResultLayout` supplies the current
chain-config/blob-schedule fragment, and the remaining function/loop proofs must compose them into
this one live trace. -/

/-- A complete successful run of the exported wrapper, ending with the accepted value represented in
the canonical result buffer and both accessors agreeing. -/
structure SuccessfulRun (input : ByteArray) (value : BinaryFv.Specs.SSZ.StatelessInput) where
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
  /-- The exported function instance contract's own bound, **plus the one retirement that reaches the
  sentinel**; the runner's fuel strictly exceeds it.

  The `+ 1` is forced, not slack taken for comfort. The contract bounds the wrapper's *own*
  retirements by `entryStepBound`, and its `EnteredFunctionTrace` stops **on** the exit instruction —
  the sentinel is reached only by the `ret` that follows it, so
  `Elfling.traceToSentinel_of_functionTrace` yields a trace of length `count + 1`. Stated at
  `≤ entryStepBound` this field was unsatisfiable from any contract: no function-instance obligation
  could ever supply it.

  It read as correct for as long as it did because **nothing in the tree constructed a
  `TraceToSentinel`** — a hypothesis nothing supplies is never tested, so the tightness never bound
  anything. It became a contradiction the moment the first constructor existed.

  `zesuFuel = entryStepBound + 2` was already sized for exactly this: its own docstring reads "one
  slack step to retire the return that lands on the sentinel, and one to make the budget *strictly*
  exceed the composed trace length". The design always accounted for the retirement; this field did
  not. The accessor side carries the same `stepBound + 1` shape for the same reason
  (`Accessors.AccessorReachesSentinel`). -/
  withinStepBound : stepCount ≤ entryStepBound input.size + 1
  returnCode : observeReturnCode? finalState = some 1
  storedPresent : observeOptionTag? finalState storedResultDiscriminantAddr = some true
  inputPreserved : MemoryBytes finalState canonicalRunnerLayout.inputBase input
  storedValue : StatelessInputRep finalState canonicalRunnerLayout.inputBase input
    Elflings.canonicalResultBuffer value
  /-- `zesu_raw_result` returns the canonical buffer and `zesu_raw_error` the `ok` status. -/
  accessors : Runs (runAccessorsIfReached resolvedSymbols (.reached stepCount))
    finalState afterAccessors
    (.returned Elflings.canonicalResultBuffer, .returned Contracts.DecodeStatus.ok.code)

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
  withinStepBound : stepCount ≤ entryStepBound input.size + 1
  returnCode : observeReturnCode? finalState = some 0
  storedAbsent : observeOptionTag? finalState storedResultDiscriminantAddr = some false
  /-- Not merely "nonzero": an exhausted arena and a refused second call are also nonzero, and
  neither is a rejection. -/
  specRejection : statusCategory status = .specRejection
  /-- `zesu_raw_result` returns null and `zesu_raw_error` the recorded status. -/
  accessors : Runs (runAccessorsIfReached resolvedSymbols (.reached stepCount))
    finalState afterAccessors (.returned 0, .returned status)

/-! ## What used to be here

Two old `sorry`-carrying scaffolds asserted machine runs directly from specification outcomes. They
remain deleted: `ExportedContractExecution.lean` constructs those runs only from the explicit exported-contract seam.
Keeping an unconditional route alongside it would make the root's real premises unclear. -/

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
