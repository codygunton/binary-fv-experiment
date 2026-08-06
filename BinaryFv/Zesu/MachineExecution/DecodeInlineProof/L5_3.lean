import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryPrefix
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.MemcpyDecoderBridge
import BinaryFv.Zesu.Elflings.GeneratedProgramGeometry
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Elfling.SequentialSplice
import BinaryFv.Zesu.MachineExecution.OwnedPc
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_4
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_5
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_6
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_7
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_8
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_9
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_10
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_11
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_12
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_13
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_14
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_15
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_16
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_17
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_18
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_19
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_20
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_21
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_4
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_5
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_6
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_7
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_8
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_9
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_4
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L4_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L4_2

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

/-- Close the short-input retry arm at the selected `0x10394` exit. The outgoing branch belongs to
the Level 2 wrapper, so this Level 3 trace stops before executing it. -/
theorem decodeInline_retry_short_reaches_post (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (short : args.bytes.size < 4) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep used state after ∧
      DecodeInlinePost args state after ∧
      DecodeInlineMachinePost state after ∧
      DecodeInlineOutgoingFrame args after := by
  obtain ⟨childUsed, childAfter, childBound, parentPrefix, childPost, agree, counter, -, -, -,
    childGlobals, _childStatus, code, memory⟩ :=
    decodeInline_retry_uses_length_gate fromStep args state pre phase
  have prefixFalse : Contracts.meaningHasExactErePrefix args.bytes = false :=
    meaningHasExactErePrefix_false_of_size_lt_four args.bytes short
  have atExit : childAfter.regs.get? PC = some (BitVec.ofNat 64 0x10394) := by
    simpa [HasExactErePrefixInlinePost] using childPost.1
  have selectedExit : DecodeInlineExit args (BitVec.ofNat 64 0x10394) := by
    simp [DecodeInlineExit, phase, prefixFalse, short]
  have tail : ScopedTrace decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (4 + childUsed)) 0
      childAfter childAfter :=
    ScopedTrace.exitAt _ childAfter (BitVec.ofNat 64 0x10394) atExit selectedExit
  have trace := parentPrefix 0 childAfter tail
  have rawInvalid : Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz :=
    (pre.retryReason phase).1
  have resultInvalid : Contracts.meaningDecode args.bytes = .error .invalidSsz := by
    simp [Contracts.meaningDecode, rawInvalid, prefixFalse]
  refine ⟨4 + childUsed, childAfter, ?_, ?_, ?_,
    ⟨agree, counter, code, childGlobals.trans pre.globalsValue.symm⟩, ?_⟩
  · unfold decodeInlineStepBound
    have lengthBound : hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } = 12 := rfl
    rw [lengthBound] at childBound
    omega
  · simpa using trace
  · simp [DecodeInlinePost, phase, DecodeInlineRetryPost, prefixFalse, resultInvalid, atExit,
      short]
  · simp [DecodeInlineOutgoingFrame, phase, prefixFalse, short]
    exact ⟨childPost.2.1, childPost.2.2⟩

end BinaryFv.Zesu.MachineExecution
