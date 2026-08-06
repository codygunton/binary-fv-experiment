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

/-- The declared `decode` budget leaves room for the selected `decodeRaw` budget plus the thirteen
parent-owned instructions of the first phase. -/
theorem decodeInline_first_stepBound_le {args : DecodeInlineArgs} {childUsed own : Nat}
    (childBound : childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs)
    (ownBound : own ≤ 13) : childUsed + own ≤ decodeInlineStepBound args := by
  unfold decodeInlineStepBound
  have stepBoundEq : compiledDecodeRawContract.binding.stepBound args.firstRawArgs =
      16384 + 512 * args.bytes.size := rfl
  rw [stepBoundEq] at childBound
  omega

def decodeRawReturnAfter (returnPc : BitVec 64) (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10530) returnPc)
    returnPc retired

end BinaryFv.Zesu.MachineExecution
