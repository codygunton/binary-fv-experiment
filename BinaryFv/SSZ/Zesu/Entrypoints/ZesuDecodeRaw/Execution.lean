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

Two `sorry`-carrying scaffolds — `successful_trace_of_spec_accepts` and
`rejected_trace_of_spec_rejects` — each asserting that a specification outcome has a corresponding
live run of the machine, bundled with the canonical program and its compliance obligation.

They are **deleted**, not weakened: `Assembly.lean`'s `successfulRun_of_locals` and
`rejectedRun_of_locals` prove exactly those runs from `LocalContractAssumptions`, and
`CatalogSatisfiability.lean`'s `canonicalProgram_and_obligations_of_residue` proves the other two
conjuncts from the same premise. Keeping the scaffolds alongside would leave a second, unconditional
route to the root, which is the shape a reader could not distinguish from progress. -/

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
