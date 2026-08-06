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
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L6_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L6_2

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

/-- The complete first-phase arm of the Level 3 contract. This is the single scope showing the
conditional `decodeRaw` summary stitched to all parent-owned Sail execution and the selected semantic
postcondition. No other child condition is used on this phase. -/
theorem decodeInline_first_level3_relation (contract : CompiledDecodeRawInstanceContract)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) (phase : args.phase = .first) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep used before after ∧
      DecodeInlinePost args before after ∧
      DecodeInlineMachinePost before after ∧
      DecodeInlineOutgoingFrame args after := by
  cases resultEq : Contracts.meaningDecodeRaw args.bytes with
  | ok value =>
      obtain ⟨childUsed, final, childBound, exit, post, trace, machinePost, outgoingStack⟩ :=
        decodeInline_first_success_reaches_post contract fromStep args before pre phase value resultEq
      refine ⟨childUsed + 13, final, ?_, trace, ?_, machinePost, ?_⟩
      · exact decodeInline_first_stepBound_le childBound (by omega)
      · simpa [DecodeInlinePost, phase] using post
      · simpa [DecodeInlineOutgoingFrame, phase] using outgoingStack.1
  | error error =>
      obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, childBound, transfer,
        tagRun, exit, post, trace, machinePost, -, -, outgoingStack⟩ :=
        decodeInline_first_error_reaches_post contract fromStep args before pre phase error resultEq
      refine ⟨childUsed + 8,
        afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))), ?_, trace, ?_,
          machinePost, by simpa [DecodeInlineOutgoingFrame, phase] using outgoingStack.1⟩
      · exact decodeInline_first_stepBound_le childBound (by omega)
      · simpa [DecodeInlinePost, phase] using post

/-- Close the four-or-more-byte prefix-mismatch arm at the selected outgoing branch source. The
branch itself transfers to wrapper code and is therefore executed by the Level 2 proof. -/
theorem decodeInline_retry_prefix_mismatch_reaches_post (fromStep : Nat)
    (args : DecodeInlineArgs) (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (fourBytes : 4 ≤ args.bytes.size)
    (notExact : Contracts.meaningHasExactErePrefix args.bytes = false) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep used state after ∧
      DecodeInlinePost args state after ∧
      DecodeInlineMachinePost state after ∧
      DecodeInlineOutgoingFrame args after := by
  obtain ⟨lengthUsed, prefixUsed, beforeOr, lengthBound, prefixBound, parentPrefix, prefixPost,
    beforeAgree, beforeCounter, _beforeStack, inputPointer, inputLength, beforeGlobals,
    beforeCode, beforeMemory⟩ :=
    decodeInline_retry_uses_prefix_bytes fromStep args state pre phase fourBytes
  obtain ⟨orRetired, orRun, orPc, orPreserves, orCounter, orMemory⟩ :=
    decodeInline_retry_prefix_or_step (fromStep + (5 + lengthUsed + prefixUsed)) args state
      beforeOr pre beforeAgree beforeCounter beforeCode prefixPost.1
      (BitVec.ofNat 64 (prefixLow16 args.bytes))
      (BitVec.ofNat 64 (prefixHigh16 args.bytes)) prefixPost.2.1 prefixPost.2.2.1
  let after := afterRegisterWrite beforeOr (BitVec.ofNat 64 0x103c0) orRetired x10
    (BitVec.ofNat 64 (prefixHigh16 args.bytes) |||
      BitVec.ofNat 64 (prefixLow16 args.bytes))
  have orNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x103c0) := by
    simp [DecodeInlineExit, phase, notExact, show ¬ args.bytes.size < 4 by omega]
  have orPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (5 + lengthUsed + prefixUsed)) 1
      beforeOr after :=
    ConfinedPrefix.ownStep' prefixPost.1 (by simpa [after] using orRun) (notExit := orNotExit)
  have completePrefix := ConfinedPrefix.trans parentPrefix orPrefix
  have selectedExit : DecodeInlineExit args (BitVec.ofNat 64 0x103c4) := by
    simp [DecodeInlineExit, phase, notExact, show ¬ args.bytes.size < 4 by omega]
  have tail : ScopedTrace decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (5 + lengthUsed + prefixUsed + 1)) 0 after after :=
    ScopedTrace.exitAt _ after (BitVec.ofNat 64 0x103c4) (by simpa [after] using orPc)
      selectedExit
  have trace := completePrefix 0 after tail
  have rawInvalid : Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz :=
    (pre.retryReason phase).1
  have resultInvalid : Contracts.meaningDecode args.bytes = .error .invalidSsz := by
    simp [Contracts.meaningDecode, rawInvalid, notExact]
  have afterAgree : Agree decoderPreserved state after := beforeAgree.trans orPreserves
  have afterCode : Contracts.canonicalContractParams.env.CodeIntact after := by
    rw [Contracts.DecoderEnvironment.CodeIntact, orMemory, beforeMemory]
    exact pre.code
  have wOr : WritesOnlyRegs _ beforeOr after := afterRegisterWrite_writes _ _ _ _ _
  have afterGlobals : after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  refine ⟨6 + lengthUsed + prefixUsed, after, ?_, ?_, ?_,
    ⟨afterAgree, orCounter, afterCode, afterGlobals.trans pre.globalsValue.symm⟩, ?_⟩
  · unfold decodeInlineStepBound
    have prefixBoundValue : prefixUsed ≤ 12 := by
      simpa [hasExactErePrefixInlineStepBound] using prefixBound
    have lengthBoundValue : lengthUsed ≤ 12 := by
      simpa [hasExactErePrefixInlineStepBound] using lengthBound
    omega
  · have countEq : 5 + lengthUsed + prefixUsed + 1 = 6 + lengthUsed + prefixUsed := by omega
    rw [← countEq]
    simpa using trace
  · simp [DecodeInlinePost, phase, DecodeInlineRetryPost, notExact, resultInvalid,
      show ¬ args.bytes.size < 4 by omega, after, orPc]
  · simp only [DecodeInlineOutgoingFrame, phase, notExact, Bool.false_eq_true, ↓reduceIte,
      show ¬ args.bytes.size < 4 by omega]
    constructor
    · simp [after, afterRegisterWrite, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
    · simpa [after, afterRegisterWrite, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using prefixPost.2.2.2

/-! ## Exact-prefix second-call setup -/

end BinaryFv.Zesu.MachineExecution
