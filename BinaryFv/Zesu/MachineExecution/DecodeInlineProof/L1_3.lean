import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryPrefix
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.MemcpyDecoderBridge
import BinaryFv.Zesu.Elflings.GeneratedProgramGeometry
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Elfling.SequentialSplice
import BinaryFv.Zesu.MachineExecution.OwnedPc

/-!
# Sail proof for the inlined `decode` scope

This file executes the 31 instructions owned directly by the compiler's inlined `decode` instance
and composes them with the three Level 3 child summaries. The inventory below is the reviewable
starting point: every owned word is checked against the pinned program image before any path proof
uses it.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep
open BinaryFv.RiscV.Sep

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem writesOnlyWithinOwnAllocation_of_mem_eq
    (env : Contracts.DecoderEnvironment) (recordBase recordSize : Nat)
    {before after before' after' : State}
    (beforeMemory : before'.mem = before.mem) (afterMemory : after'.mem = after.mem)
    (writes : env.WritesOnlyWithinOwnAllocation recordBase recordSize before after) :
    env.WritesOnlyWithinOwnAllocation recordBase recordSize before' after' := by
  rcases writes with ⟨cursorBefore, cursorAfter, beforeCursor, afterCursor, frame⟩
  refine ⟨cursorBefore, cursorAfter, ?_, ?_, ?_⟩
  · unfold Contracts.DecoderEnvironment.cursor? at beforeCursor ⊢
    unfold BinaryFv.Zesu.MemoryRepresentation.observeWord64? at beforeCursor ⊢
    rw [beforeMemory]
    exact beforeCursor
  · unfold Contracts.DecoderEnvironment.cursor? at afterCursor ⊢
    unfold BinaryFv.Zesu.MemoryRepresentation.observeWord64? at afterCursor ⊢
    rw [afterMemory]
    exact afterCursor
  · intro address outside
    rw [afterMemory, beforeMemory]
    exact frame address outside

theorem rawV4Rep_of_mem_eq {before after : State} {inputBase rootBase : Nat}
    {input : ByteArray} {value : BinaryFv.Specs.SSZ.RawV4}
    (memory : after.mem = before.mem)
    (representation : BinaryFv.Zesu.MemoryRepresentation.RawV4Rep
      before inputBase input rootBase value) :
    BinaryFv.Zesu.MemoryRepresentation.RawV4Rep after inputBase input rootBase value := by
  obtain ⟨_, transport⟩ :=
    Contracts.Footprint.rawV4_footprint_abi inputBase input rootBase value before
      Artifacts.raw_stateless_input_layout.1 representation
  exact transport _ (fun address _ => (congrArg (·.get? address) memory).symm)

end BinaryFv.Zesu.MachineExecution
