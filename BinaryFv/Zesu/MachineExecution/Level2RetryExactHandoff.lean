import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame

/-!
# Exact-prefix retry tag handoff

This module joins the selected Level 3 exact-prefix retry body to the one wrapper-owned result-tag
load at `0x103f8`.  It intentionally stops at the dispatch instruction `0x103fc`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The lossless Level 2 boundary after the exact-prefix retry's wrapper-owned result-tag load.
It retains the retry payload facts for tag zero while leaving all dispatch routes unexecuted. -/
structure RetryExactTagHandoffResult (args : DecodeInlineArgs) (fromStep used : Nat)
    (before childAfter after : State) (link s0 s1 s2 : BitVec 64) : Prop where
  bound : used ≤ decodeInlineStepBound args
  child : level3DecodeChildSummary
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
    fromStep used before childAfter
  childTrace : ScopedTrace
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
    (DecodeInlineExit args) Level3ChildSummary fromStep used before childAfter
  post : DecodeInlinePost args before childAfter
  retrySuccess : DecodeInlineRetrySuccessPost args before childAfter
  outgoing : DecodeInlineOutgoingFrame args childAfter
  saveArea : DecodeInlineCallerSaveArea args before childAfter
  tagStep : Runs (try_step (fromStep + used) false) childAfter after false
  scopedTrace : ScopedTrace
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw)
    (fun pc => pc = BitVec.ofNat 64 0x103fc) Level2ChildSummary fromStep (used + 1) before after
  semanticTag : after.regs.get? x10 = some
    (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes)))
  dispatchPc : after.regs.get? PC = some (BitVec.ofNat 64 0x103fc)
  machineAgree : Agree decoderPreserved before after
  code : canonicalContractParams.env.CodeIntact after
  retired : RetiredCounterPresent after
  memory : after.mem = childAfter.mem
  stack : after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)
  globals : after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  savedFrame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 after
  sourcePayload : ∃ contents, contents.size = 832 ∧
    MemoryRepresentation.MemoryBytes after args.retryRawArgs.resultBase contents
  finalPayload : ∃ contents, contents.size = 832 ∧
    MemoryRepresentation.MemoryBytes after args.finalResultBase contents

/-- Compose the exact-prefix Level 3 retry child with the actual `lhu a0, -1552(a0)` Sail step.
The scoped trace is deliberately endpoint-local at `0x103fc`; dispatch remains a later phase. -/
theorem retry_exact_tag_handoff
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (pre : DecodeInlinePre args before)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true)
    (link s0 s1 s2 : BitVec 64)
    (saved : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 before) :
    ∃ used childAfter after,
      RetryExactTagHandoffResult args fromStep used before childAfter after link s0 s1 s2 := by
  obtain ⟨used, childAfter, bound, childTrace, post, machine, outgoing, saveArea⟩ :=
    decodeInline_retry_success_level3_save_area contract fromStep args before pre phase exactPrefix
  have childPc : childAfter.regs.get? PC = some (BitVec.ofNat 64 0x103f8) := by
    simp [DecodeInlinePost, DecodeInlineRetryPost, phase, exactPrefix] at post
    exact post.2
  have retrySuccess : DecodeInlineRetrySuccessPost args before childAfter := by
    simp [DecodeInlinePost, DecodeInlineRetryPost, phase, exactPrefix] at post
    exact post.1
  obtain ⟨retired, tagStep⟩ := retry_exact_result_tag_step (fromStep + used) args before childAfter
    pre machine outgoing phase exactPrefix childPc
  let after := afterRegisterWrite childAfter (BitVec.ofNat 64 0x103f8) retired x10
    (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes)))
  have dispatchPc : after.regs.get? PC = some (BitVec.ofNat 64 0x103fc) := by
    simpa [after] using afterRegisterWrite_pc childAfter (BitVec.ofNat 64 0x103f8) retired x10
      (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes)))
  have semanticTag : after.regs.get? x10 = some
      (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes))) := by
    simp [after, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  have machineAgree : Agree decoderPreserved before after :=
    machine.agree.trans (afterRegisterWrite_agree_of (P := decoderPreserved)
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have code : canonicalContractParams.env.CodeIntact after := by
    simpa [after, afterRegisterWrite_mem] using machine.code
  have retiredPresent : RetiredCounterPresent after := by
    exact afterRegisterWrite_retired_present childAfter (BitVec.ofNat 64 0x103f8) retired x10
      (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes)))
  have memory : after.mem = childAfter.mem := by
    simp [after, afterRegisterWrite_mem]
  have stack : after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    have outgoingExact : childAfter.regs.get? x10 = some
        (BitVec.ofNat 64 (args.stackBase + 0x1000)) ∧
        childAfter.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
        MemoryRepresentation.ResultStatusLERep childAfter (args.stackBase + 0x9f0)
          (decodeInternalResultTag (meaningDecode args.bytes)) := by
      simpa [DecodeInlineOutgoingFrame, phase, exactPrefix] using outgoing
    have childStack : childAfter.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
      exact outgoingExact.2.1
    simpa [after] using (afterRegisterWrite_register childAfter (BitVec.ofNat 64 0x103f8)
      retired x10 x2 (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes)))
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans childStack
  have globals : after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    have childGlobals : childAfter.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
      machine.globalsValue.trans pre.globalsValue
    simpa [after] using (afterRegisterWrite_register childAfter (BitVec.ofNat 64 0x103f8)
      retired x10 x18 (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes)))
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans childGlobals
  have savedFrame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 after :=
    WrapperSavedRegisterFrame.of_mem_eq
      (WrapperSavedRegisterFrame.of_decode_inline_caller_save_area saved saveArea) memory
  obtain ⟨decoded, contents, decodedPost, contentsSize, decodedSource, copyFrame, sourcePayload,
    finalPayload, retryCode, noAllocation⟩ := retrySuccess
  have endpoint : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (fun pc => pc = BitVec.ofNat 64 0x103fc) Level2ChildSummary (fromStep + used + 1) 0 after
      after :=
    ScopedTrace.exitAt _ after (BitVec.ofNat 64 0x103fc) dispatchPc rfl
  have tagScoped : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (fun pc => pc = BitVec.ofNat 64 0x103fc) Level2ChildSummary (fromStep + used) 1 childAfter
      after :=
    ScopedTrace.ownStep (fromStep + used) 0 (BitVec.ofNat 64 0x103f8) childAfter after after
      childPc (by
        apply functionInstanceExecutionPcs_iff_ranges.mpr
        apply RegionPcs.iff_inRanges.mpr
        native_decide) (by simp) (by simpa [after] using tagStep) endpoint
  have scopedTrace : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (fun pc => pc = BitVec.ofNat 64 0x103fc) Level2ChildSummary fromStep (used + 1) before
      after := by
    exact ScopedTrace.childBody fromStep used 1
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id before
      childAfter after
      (Level2ChildSummary.decode ⟨rfl, args, pre, bound, childTrace, post, machine, outgoing⟩)
      (by simpa [Nat.add_assoc] using tagScoped)
  refine ⟨used, childAfter, after, ?_⟩
  exact ⟨bound, ⟨rfl, args, pre, bound, childTrace, post, machine, outgoing⟩, childTrace, post,
    ⟨decoded, contents, decodedPost, contentsSize, decodedSource, copyFrame, sourcePayload,
      finalPayload, retryCode, noAllocation⟩, outgoing, saveArea, by simpa [after] using tagStep,
    scopedTrace, semanticTag,
    dispatchPc, machineAgree, code, retiredPresent, memory, stack, globals, savedFrame,
    ⟨contents, contentsSize, by simpa [after, memory] using sourcePayload⟩,
    ⟨contents, contentsSize, by simpa [after, memory] using finalPayload⟩⟩

end BinaryFv.Zesu.MachineExecution
