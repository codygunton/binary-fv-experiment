import BinaryFv.RiscV.Proof.RunnerCorrespondence
import BinaryFv.SSZ.SpecBridge.Decode
import BinaryFv.SSZ.Zesu.Artifact.Symbols
import BinaryFv.SSZ.Zesu.MemoryRepresentation.Result

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.MemoryRepresentation
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

/-- A complete successful machine execution, from the public decoder entry to its return sentinel,
whose final memory represents the accepted `RawV4`.

The `TraceToSentinel` field is where the existing exact-PC retirements and block traces connect:
`ParserBlocks` supplies primitive decoding fragments, `Analysis.ResultLayout` supplies the current
chain-config/blob-schedule fragment, and the remaining function/loop proofs must compose them into
this one live trace. -/
structure SuccessfulTraceWitness (input : ByteArray) (value : SszBridge.RawV4) where
  inputBase : Nat
  resultBase : Nat
  sentinel : BitVec 64
  stepCount : Nat
  initialState : State
  finalState : State
  entry : DecodeEntryRep initialState inputBase input sentinel
  trace : TraceToSentinel sentinel 0 stepCount initialState finalState
  finalInputMemory : MemoryBytes finalState inputBase input
  result : RawV4SuccessResultRep finalState inputBase input resultBase value

/-- A complete machine execution which returns a nonzero decoder status and therefore normalizes to
the public `rejected` outcome. -/
structure RejectedTraceWitness (input : ByteArray) where
  inputBase : Nat
  resultBase : Nat
  sentinel : BitVec 64
  stepCount : Nat
  status : Nat
  initialState : State
  finalState : State
  entry : DecodeEntryRep initialState inputBase input sentinel
  trace : TraceToSentinel sentinel 0 stepCount initialState finalState
  statusNonzero : status ≠ 0
  resultStatus : observeResultStatus? finalState resultBase = some status

/-- Authorized navigation scaffold: accepted SizzLean inputs have a complete live Sail execution
whose final state represents the same value. -/
theorem successful_trace_of_spec_accepts (input : ByteArray)
    (inputBound : input.size < 2 * 1024 * 1024) (value : SszBridge.RawV4)
    (specAccepts : SszSpec.decode input = .accepted value) :
    Nonempty (SuccessfulTraceWitness input value) := by
  sorry

/-- Authorized navigation scaffold: rejected SizzLean inputs follow a classified live Sail path to
a nonzero Zesu result status. -/
theorem rejected_trace_of_spec_rejects (input : ByteArray)
    (inputBound : input.size < 2 * 1024 * 1024)
    (specRejects : SszSpec.decode input = .rejected) :
    Nonempty (RejectedTraceWitness input) := by
  sorry

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
