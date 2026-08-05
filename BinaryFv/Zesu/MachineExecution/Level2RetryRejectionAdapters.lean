import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.Zesu.MachineExecution.OwnedPc

/-! Save-area companions for the two typed retry-rejection exits. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure RetryShortRejectionEdgeResult (args : DecodeInlineArgs) (fromStep used : Nat)
    (before after handoff : State) (link s0 s1 s2 : BitVec 64) : Prop where
  bound : used ≤ decodeInlineStepBound args
  child : level3DecodeChildSummary
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
    fromStep used before after
  childTrace : ScopedTrace
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
    (DecodeInlineExit args) Level3ChildSummary fromStep used before after
  post : DecodeInlinePost args before after
  machine : DecodeInlineMachinePost before after
  outgoing : DecodeInlineOutgoingFrame args after
  saveArea : DecodeInlineCallerSaveArea args before after
  status : after.regs.get? x11 = some (BitVec.ofNat 64 2)
  savedFrame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 after
  branch : Runs (try_step (fromStep + used) false) after handoff false
  branchPrefix : ConfinedPrefix decodeRawExecutionPcs decodeRawExit
    Level2ChildSummary (fromStep + used) 1 after handoff
  handoffFrame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 handoff
  handoffRetired : RetiredCounterPresent handoff
  handoffCode : canonicalContractParams.env.CodeIntact handoff
  handoffMemory : handoff.mem = after.mem
  handoffAgree : Agree decoderPreserved before handoff
  handoffStack : handoff.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)
  handoffGlobals : handoff.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  branchPc : handoff.regs.get? PC = some (BitVec.ofNat 64 0x10420)

/-- The short-input rejection preserves the wrapper's concrete 32-byte save area. -/
theorem decodeInline_retry_short_reaches_post_save_area (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (short : args.bytes.size < 4) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep used state after ∧
      DecodeInlinePost args state after ∧ DecodeInlineMachinePost state after ∧
      DecodeInlineOutgoingFrame args after ∧ DecodeInlineCallerSaveArea args state after ∧
      after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 2) := by
  have childRun := decodeInline_retry_uses_length_gate fromStep args state pre phase
  let childUsed := Classical.choose childRun
  have childUsedPayload := Classical.choose_spec childRun
  let after := Classical.choose childUsedPayload
  have childPayload := Classical.choose_spec childUsedPayload
  have childBound := childPayload.1
  have parentPrefix := childPayload.2.1
  have childPost := childPayload.2.2.1
  have agree := childPayload.2.2.2.1
  have counter := childPayload.2.2.2.2.1
  have childStack := childPayload.2.2.2.2.2.1
  have childGlobals := childPayload.2.2.2.2.2.2.2.2.1
  have childStatus := childPayload.2.2.2.2.2.2.2.2.2.1
  have code := childPayload.2.2.2.2.2.2.2.2.2.2.1
  have memory := childPayload.2.2.2.2.2.2.2.2.2.2.2
  have prefixFalse : Contracts.meaningHasExactErePrefix args.bytes = false :=
    meaningHasExactErePrefix_false_of_size_lt_four args.bytes short
  have atExit : after.regs.get? PC = some (BitVec.ofNat 64 0x10394) := by
    simpa [after, HasExactErePrefixInlinePost] using childPost.1
  have selectedExit : DecodeInlineExit args (BitVec.ofNat 64 0x10394) := by
    simp [DecodeInlineExit, phase, prefixFalse, short]
  have tail : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (4 + childUsed)) 0 after after :=
    ScopedTrace.exitAt _ after (BitVec.ofNat 64 0x10394) atExit selectedExit
  have rawInvalid : Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz :=
    (pre.retryReason phase).1
  have resultInvalid : Contracts.meaningDecode args.bytes = .error .invalidSsz := by
    simp [Contracts.meaningDecode, rawInvalid, prefixFalse]
  refine ⟨4 + childUsed, after, ?_, ?_, ?_,
    ⟨agree, counter, code, childGlobals.trans pre.globalsValue.symm⟩, ?_, ?_, ?_, ?_⟩
  · unfold decodeInlineStepBound
    have childBound' : childUsed ≤ 12 := by
      simpa [childUsed, hasExactErePrefixInlineStepBound] using childBound
    omega
  · simpa [childUsed, after] using parentPrefix 0 (Classical.choose childUsedPayload) tail
  · simp [DecodeInlinePost, phase, DecodeInlineRetryPost, prefixFalse, resultInvalid, atExit, short]
  · simp [DecodeInlineOutgoingFrame, phase, prefixFalse, short]
    exact ⟨childPost.2.1, childPost.2.2⟩
  · intro index bound
    rw [memory]
  · simpa [after] using childStack
  · simpa [after] using childStatus

/-- The four-byte prefix-mismatch rejection preserves the wrapper's concrete 32-byte save area. -/
theorem decodeInline_retry_prefix_mismatch_reaches_post_save_area (fromStep : Nat)
    (args : DecodeInlineArgs) (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (fourBytes : 4 ≤ args.bytes.size)
    (notExact : Contracts.meaningHasExactErePrefix args.bytes = false) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep used state after ∧
      DecodeInlinePost args state after ∧ DecodeInlineMachinePost state after ∧
      DecodeInlineOutgoingFrame args after ∧ DecodeInlineCallerSaveArea args state after := by
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
    (BitVec.ofNat 64 (prefixHigh16 args.bytes) ||| BitVec.ofNat 64 (prefixLow16 args.bytes))
  have orNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x103c0) := by
    simp [DecodeInlineExit, phase, notExact, show ¬ args.bytes.size < 4 by omega]
  have orPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (5 + lengthUsed + prefixUsed)) 1
      beforeOr after :=
    ConfinedPrefix.ownStep' prefixPost.1 (by simpa [after] using orRun)
      (GeneratedWordStep.regionPc _) orNotExit
  have selectedExit : DecodeInlineExit args (BitVec.ofNat 64 0x103c4) := by
    simp [DecodeInlineExit, phase, notExact, show ¬ args.bytes.size < 4 by omega]
  have tail : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (5 + lengthUsed + prefixUsed + 1)) 0 after after :=
    ScopedTrace.exitAt _ after (BitVec.ofNat 64 0x103c4) (by simpa [after] using orPc) selectedExit
  have rawInvalid : Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz :=
    (pre.retryReason phase).1
  have resultInvalid : Contracts.meaningDecode args.bytes = .error .invalidSsz := by
    simp [Contracts.meaningDecode, rawInvalid, notExact]
  have afterAgree : Agree decoderPreserved state after := beforeAgree.trans orPreserves
  have afterCode : Contracts.canonicalContractParams.env.CodeIntact after := by
    simpa [after, afterRegisterWrite_mem] using beforeCode
  have orWrites : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x10)) beforeOr after :=
    afterRegisterWrite_writes beforeOr (BitVec.ofNat 64 0x103c0) orRetired x10
      (BitVec.ofNat 64 (prefixHigh16 args.bytes) ||| BitVec.ofNat 64 (prefixLow16 args.bytes))
  have afterGlobals : after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (orWrites.get x18 (by decide)).trans beforeGlobals
  have afterMemory : after.mem = state.mem := by
    simpa [after] using orMemory.trans beforeMemory
  refine ⟨6 + lengthUsed + prefixUsed, after, ?_, ?_, ?_,
    ⟨afterAgree, orCounter, afterCode, afterGlobals.trans pre.globalsValue.symm⟩, ?_, ?_⟩
  · unfold decodeInlineStepBound
    have prefixBoundValue : prefixUsed ≤ 12 := by
      simpa [hasExactErePrefixInlineStepBound] using prefixBound
    have lengthBoundValue : lengthUsed ≤ 12 := by
      simpa [hasExactErePrefixInlineStepBound] using lengthBound
    omega
  · have countEq : 5 + lengthUsed + prefixUsed + 1 = 6 + lengthUsed + prefixUsed := by omega
    rw [← countEq]
    simpa using ConfinedPrefix.trans parentPrefix orPrefix 0 after tail
  · simp [DecodeInlinePost, phase, DecodeInlineRetryPost, notExact, resultInvalid,
      show ¬ args.bytes.size < 4 by omega, after, orPc]
  · simp only [DecodeInlineOutgoingFrame, phase, notExact, Bool.false_eq_true, ↓reduceIte,
      show ¬ args.bytes.size < 4 by omega]
    refine ⟨afterRegisterWrite_destination beforeOr (BitVec.ofNat 64 0x103c0) orRetired x10 _
        (by decide) (by decide),
      (orWrites.get x13 (by decide)).trans prefixPost.2.2.2⟩
  · intro index bound
    rw [afterMemory]

theorem retry_short_rejection_edge (fromStep : Nat) (args : DecodeInlineArgs) (before : State)
    (pre : DecodeInlinePre args before) (phase : args.phase = .retryAfterInvalidSsz)
    (short : args.bytes.size < 4) (link s0 s1 s2 : BitVec 64)
    (saved : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 before) :
    ∃ used after handoff, RetryShortRejectionEdgeResult args fromStep used before after
      handoff link s0 s1 s2 := by
  obtain ⟨used, after, bound, childTrace, post, machine, outgoing, saveArea, stack, status⟩ :=
    decodeInline_retry_short_reaches_post_save_area fromStep args before pre phase short
  have prefixFalse : Contracts.meaningHasExactErePrefix args.bytes = false :=
    meaningHasExactErePrefix_false_of_size_lt_four args.bytes short
  have atPc : after.regs.get? PC = some (BitVec.ofNat 64 0x10394) := by
    simp [DecodeInlinePost, DecodeInlineRetryPost, phase, prefixFalse, short] at post
    exact post.2
  obtain ⟨handoff, branch, seg⟩ :=
    retry_short_length_branch_step (childSummary := Level2ChildSummary) (fromStep + used) args
      before after pre machine outgoing phase short atPc
  have handoffMemory : handoff.mem = after.mem := seg.memEq noMemory_empty
  have handoffCode : canonicalContractParams.env.CodeIntact handoff := by
    rw [DecoderEnvironment.CodeIntact, handoffMemory]
    exact machine.code
  have child : level3DecodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      fromStep used before after := ⟨rfl, args, pre, bound, childTrace, post, machine, outgoing⟩
  exact ⟨used, after, handoff, bound, child, childTrace, post, machine, outgoing, saveArea, status,
    WrapperSavedRegisterFrame.of_decode_inline_caller_save_area saved saveArea, branch, seg.confined,
    WrapperSavedRegisterFrame.of_mem_eq
      (WrapperSavedRegisterFrame.of_decode_inline_caller_save_area saved saveArea) handoffMemory,
    seg.retired, handoffCode, handoffMemory,
    machine.agree.trans (seg.agree (platformPreserved_disjoint.weaken (fun _ pres => pres.2))),
    (seg.get x2 (by decide)).trans stack,
    (seg.get x18 (by decide)).trans (machine.globalsValue.trans pre.globalsValue), seg.atPc⟩

end BinaryFv.Zesu.MachineExecution
