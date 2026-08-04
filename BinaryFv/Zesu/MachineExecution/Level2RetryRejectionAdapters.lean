import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps

/-! Save-area companions for the two typed retry-rejection exits. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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
      DecodeInlineOutgoingFrame args after ∧ DecodeInlineCallerSaveArea args state after := by
  obtain ⟨childUsed, after, childBound, parentPrefix, childPost, agree, counter, -, -, -,
    childGlobals, code, memory⟩ := decodeInline_retry_uses_length_gate fromStep args state pre phase
  have prefixFalse : Contracts.meaningHasExactErePrefix args.bytes = false :=
    meaningHasExactErePrefix_false_of_size_lt_four args.bytes short
  have atExit : after.regs.get? PC = some (BitVec.ofNat 64 0x10394) := by
    simpa [HasExactErePrefixInlinePost] using childPost.1
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
    ⟨agree, counter, code, childGlobals.trans pre.globalsValue.symm⟩, ?_, ?_⟩
  · unfold decodeInlineStepBound
    have lengthBound : hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } = 12 := rfl
    rw [lengthBound] at childBound
    omega
  · simpa using parentPrefix 0 after tail
  · simp [DecodeInlinePost, phase, DecodeInlineRetryPost, prefixFalse, resultInvalid, atExit, short]
  · simp [DecodeInlineOutgoingFrame, phase, prefixFalse, short]
    exact ⟨childPost.2.1, childPost.2.2⟩
  · intro index bound
    rw [memory]

end BinaryFv.Zesu.MachineExecution
