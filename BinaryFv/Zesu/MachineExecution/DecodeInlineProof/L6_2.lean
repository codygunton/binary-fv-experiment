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

/-- An unsuccessful first `decodeRaw` stops at the outcome-selected generated exit `0x10324`.
The tag-load instruction is executed; the outgoing branch itself is not part of this path. -/
theorem decodeInline_first_error_reaches_post
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first)
    (error : Contracts.DecodeError)
    (failed : Contracts.meaningDecodeRaw args.bytes = .error error) :
    ∃ beforeCall childUsed resumed tagRetired,
      Trace fromStep 5 state beforeCall ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      Nonempty (CallTransfer decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        functionInstance_ssz_raw_decodeRaw (fromStep + 5) childUsed beforeCall resumed) ∧
      Runs (try_step (fromStep + 7 + childUsed) false) resumed
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) false ∧
      DecodeInlineExit args (BitVec.ofNat 64 0x10324) ∧
      DecodeInlineFirstPost args state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) ∧
      ScopedTrace decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep (childUsed + 8) state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) ∧
      DecodeInlineMachinePost state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
        (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))).regs.get? x8 =
          some (BitVec.ofNat 64 args.inputBase) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
        (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))).regs.get? x9 =
          some (BitVec.ofNat 64 args.bytes.size) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
        (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))).regs.get? x2 =
          some (BitVec.ofNat 64 args.stackBase) ∧
      DecodeInlineCallerSaveArea args state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) := by
  obtain ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, parentPrefix, bound, transfer,
    tagRun, tagPc, tagCode, tagAgree, tagCounter, tagStackRaw, tagInputBase, tagInputLength, tagValue,
    tagGlobals, tagPost, tagSaveArea⟩ :=
    decodeInline_first_through_result_tag contract fromStep args state pre phase
  -- Select the error outcome once. Every retained fact is stated about the tagged state, so a
  -- single rewrite puts all twelve into the exact form this theorem's conclusion asks for.
  rw [failed] at tagRun tagPc tagCode tagAgree tagCounter tagStackRaw
  rw [failed] at tagInputBase tagInputLength tagValue tagGlobals tagPost tagSaveArea
  have exit : DecodeInlineExit args (BitVec.ofNat 64 0x10324) := by
    simp [DecodeInlineExit, phase, failed]
  have post : DecodeInlineFirstPost args state
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
        (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) := by
    simp only [DecodeInlineFirstPost, failed]
    exact ⟨tagPost, tagPc, tagValue⟩
  obtain ⟨callTransfer⟩ := transfer
  have resumePc : resumed.regs.get? PC = some (BitVec.ofNat 64 0x10320) := by
    have returnPcEq : callTransfer.returnPc = BitVec.ofNat 64 0x10320 := by
      apply BitVec.eq_of_toNat_eq
      simpa [decodeRawFirstAttemptCall] using callTransfer.returnMatches
    simpa [returnPcEq] using callTransfer.atResume
  have tagRegion := decodeInline_owned_in_execution_region (0x10320, 0x6a015503)
    (by simp [decodeInlineOwnedInstructionWords])
  have tagNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10320) := by
    simp [DecodeInlineExit, phase, failed]
  let afterTag := afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
    (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))
  have tail : ScopedTrace decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 7 + childUsed) 1 resumed afterTag := by
    apply ScopedTrace.ownStep (fromStep + 7 + childUsed) 0 (BitVec.ofNat 64 0x10320)
      resumed afterTag afterTag resumePc tagRegion tagNotExit
    · simpa [afterTag] using tagRun
    · exact ScopedTrace.exitAt (fromStep + 7 + childUsed + 1) afterTag
        (BitVec.ofNat 64 0x10324) (by simpa [afterTag] using tagPc) exit
  have fromCall : ScopedTrace decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 5) (childUsed + 3)
      beforeCall afterTag := by
    have shiftedTail : ScopedTrace decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
        (fromStep + 5 + 1 + childUsed + 1) 1 resumed afterTag := by
      have stepEq : fromStep + 5 + 1 + childUsed + 1 = fromStep + 7 + childUsed := by
        omega
      rw [stepEq]
      exact tail
    have callTrace := ScopedTrace.callStep (fromStep + 5) childUsed 1
      decodeRawFirstAttemptCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_ssz_raw_decodeRaw beforeCall resumed afterTag callTransfer
      shiftedTail
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using callTrace
  have completeTrace := parentPrefix (childUsed + 3) afterTag fromCall
  have scopedFinal : ScopedTrace decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary fromStep (childUsed + 8) state afterTag := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completeTrace
  exact ⟨beforeCall, childUsed, resumed, tagRetired, parentTrace, bound, ⟨callTransfer⟩,
    tagRun, exit, post, by simpa [afterTag] using scopedFinal,
    ⟨tagAgree, tagCounter, tagCode, tagGlobals.trans pre.globalsValue.symm⟩,
    tagInputBase, tagInputLength, tagStackRaw, tagSaveArea⟩

/-- Consume the proved ten-instruction prefix-byte child after the length branch. The resulting
state is at `0x103c0`, where the parent still owns the final `or`. -/
theorem decodeInline_retry_uses_prefix_bytes (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (fourBytes : 4 ≤ args.bytes.size) :
    ∃ lengthUsed prefixUsed after,
      lengthUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      prefixUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } ∧
      ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary fromStep
          (5 + lengthUsed + prefixUsed) state after ∧
      HasExactErePrefixInlinePost
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } after ∧
      Agree decoderPreserved state after ∧
      RetiredCounterPresent after ∧
      after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      after.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      after.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Contracts.canonicalContractParams.env.CodeIntact after ∧
      after.mem = state.mem := by
  obtain ⟨lengthUsed, childEntry, lengthBound, parentPrefix, childPre, parentAgree, parentCounter,
    parentStackPointer, parentGlobals, parentCode, parentMemory⟩ :=
    decodeInline_retry_reaches_prefix_bytes fromStep args state pre phase fourBytes
  let childArgs : HasExactErePrefixInlineArgs :=
    { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes }
  have childPre' : HasExactErePrefixInlinePre childArgs childEntry := by
    change HasExactErePrefixInlinePre childArgs childEntry at childPre
    exact childPre
  obtain ⟨after, childTrace, childPost, childAgree, childCounter, childStackFrame,
    childInputPointer, childInputLength, childGlobals, childMemory⟩ :=
    hasExactErePrefix_prefix_segment (fromStep + (5 + lengthUsed)) childArgs childEntry
      childPre' rfl
  have childStackPointer : after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    childStackFrame.trans parentStackPointer
  let prefixUsed := 10
  have childBound : prefixUsed ≤ hasExactErePrefixInlineStepBound childArgs := by
    simp [prefixUsed, hasExactErePrefixInlineStepBound]
  have exactSummary : hasExactErePrefixInlineSummary
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
      (fromStep + (5 + lengthUsed)) prefixUsed childEntry after :=
    ⟨rfl, childArgs, childPre', childBound, childTrace, childPost⟩
  have selectedSummary : Level3ChildSummary
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
      (fromStep + (5 + lengthUsed)) prefixUsed childEntry after :=
    .hasExactErePrefix exactSummary
  have childPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (5 + lengthUsed)) prefixUsed
      childEntry after := by
    intro count final rest
    exact ScopedTrace.childBody _ prefixUsed count _ childEntry after final selectedSummary rest
  have completePrefix := ConfinedPrefix.trans parentPrefix childPrefix
  have completeAgree := Agree.trans parentAgree childAgree
  have completeMemory : after.mem = state.mem := childMemory.trans parentMemory
  have completeCode : Contracts.canonicalContractParams.env.CodeIntact after := by
    rw [Contracts.DecoderEnvironment.CodeIntact, completeMemory]
    exact pre.code
  refine ⟨lengthUsed, prefixUsed, after, lengthBound, ?_, ?_, ?_, completeAgree, childCounter,
    childStackPointer, childInputPointer, childInputLength, childGlobals, completeCode, completeMemory⟩
  · simpa [childArgs] using childBound
  · simpa [Nat.add_assoc] using completePrefix
  · simpa [childArgs] using childPost

end BinaryFv.Zesu.MachineExecution
