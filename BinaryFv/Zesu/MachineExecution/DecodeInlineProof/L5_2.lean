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

/-- Consume the first Level 3 `decodeRaw` condition, return from the emitted function, and then
execute the parent-owned result-tag load. This is the first composed path where a child contract
directly enables a following instruction of the inlined parent. -/
theorem decodeInline_first_through_result_tag
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ beforeCall childUsed resumed retired,
      Trace fromStep 5 state beforeCall ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep 5 state beforeCall ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      Nonempty (CallTransfer decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        functionInstance_ssz_raw_decodeRaw (fromStep + 5) childUsed beforeCall resumed) ∧
      Runs (try_step (fromStep + 7 + childUsed) false) resumed
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) false ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))).regs.get?
        PC = some (BitVec.ofNat 64 0x10324) ∧
      Contracts.canonicalContractParams.env.CodeIntact
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) ∧
      Agree decoderPreserved state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) ∧
      RetiredCounterPresent
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))).regs.get?
        x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))).regs.get?
        x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))).regs.get?
        x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))).regs.get?
        x10 = some (BitVec.ofNat 64
          (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes))) ∧
      (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))).regs.get?
        x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
        Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes) state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) ∧
      DecodeInlineCallerSaveArea args state
        (afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10
          (BitVec.ofNat 64
            (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) := by
  obtain ⟨beforeCall, childUsed, resumed, parentTrace, parentPrefix, bound, transfer, status, code,
    resumedAgree, resumedRetired, resumedStack, resumedInputBase, resumedInputLength, resumedGlobals,
    resumedPost, resumedSaveArea⟩ :=
    decodeInline_first_call_transfer contract fromStep args state pre phase
  obtain ⟨callTransfer⟩ := transfer
  have resumePc : resumed.regs.get? PC = some (BitVec.ofNat 64 0x10320) := by
    have returnPcEq : callTransfer.returnPc = BitVec.ofNat 64 0x10320 := by
      apply BitVec.eq_of_toNat_eq
      simpa [decodeRawFirstAttemptCall] using callTransfer.returnMatches
    simpa [returnPcEq] using callTransfer.atResume
  obtain ⟨retired, tagRun⟩ := decodeInline_first_result_tag_step
    (fromStep + 7 + childUsed) args state resumed pre status code resumedAgree resumedRetired
      resumedStack resumedGlobals resumePc
  let tagValue := BitVec.ofNat 64
    (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes))
  let afterTag := afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) retired x10 tagValue
  have tagAgree : Agree decoderPreserved resumed afterTag := by
    apply afterRegisterWrite_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  have afterCode : Contracts.canonicalContractParams.env.CodeIntact afterTag := by
    simpa [afterTag, tagValue, afterRegisterWrite_mem] using code
  have afterX10 : afterTag.regs.get? x10 = some tagValue := by
    simp [afterTag, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have wTag : WritesOnlyRegs _ resumed afterTag := afterRegisterWrite_writes _ _ _ _ _
  have afterStack : afterTag.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have afterInputBase : afterTag.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by grind
  have afterInputLength : afterTag.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by grind
  have afterGlobals : afterTag.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have afterPost : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
      state afterTag := by
    apply canonicalPostEntry_of_mem_eq args.firstRawArgs (Contracts.meaningDecodeRaw args.bytes)
      rfl (afterRegisterWrite_mem resumed (BitVec.ofNat 64 0x10320) retired x10 tagValue)
    exact resumedPost
  have afterSaveArea : DecodeInlineCallerSaveArea args state afterTag := by
    simpa [afterTag, afterRegisterWrite_mem] using resumedSaveArea
  refine ⟨beforeCall, childUsed, resumed, retired, parentTrace, parentPrefix, bound, ⟨callTransfer⟩,
    by simpa [afterTag, tagValue] using tagRun, ?_, afterCode,
    Agree.trans resumedAgree tagAgree, ?_, afterStack, afterInputBase, afterInputLength, afterX10,
    afterGlobals,
    afterPost, afterSaveArea⟩
  · simpa [afterTag, tagValue] using
      afterRegisterWrite_pc resumed (BitVec.ofNat 64 0x10320) retired x10 tagValue
  · simpa [afterTag, tagValue] using
      afterRegisterWrite_retired_present resumed (BitVec.ofNat 64 0x10320) retired x10 tagValue

/-- Splice the proved length child and parent-owned `bltu`, producing the complete machine entry for
the ten-instruction prefix-byte child. -/
theorem decodeInline_retry_reaches_prefix_bytes (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) (fourBytes : 4 ≤ args.bytes.size) :
    ∃ lengthUsed childEntry,
      lengthUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep (5 + lengthUsed) state childEntry ∧
      HasExactErePrefixInlinePre
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } childEntry ∧
      Agree decoderPreserved state childEntry ∧
      RetiredCounterPresent childEntry ∧
      childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      childEntry.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Contracts.canonicalContractParams.env.CodeIntact childEntry ∧
      childEntry.mem = state.mem := by
  obtain ⟨lengthUsed, lengthAfter, lengthBound, lengthPrefix, lengthPost, lengthAgree,
    lengthCounter, lengthStackPointer, lengthInputPointer, lengthInputLength, lengthGlobals,
    _lengthStatus, lengthCode, lengthMemory⟩ :=
    decodeInline_retry_uses_length_gate fromStep args state pre phase
  have prefixFalseAtLength : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10394) := by
    simp [DecodeInlineExit, phase, show ¬ args.bytes.size < 4 by omega]
  obtain ⟨branchRetired, branchRun, branchPc, branchPreserves, branchCounter, branchMemory⟩ :=
    decodeInline_retry_length_branch_step (fromStep + (4 + lengthUsed)) args state lengthAfter
      pre lengthAgree lengthCounter lengthCode lengthPost.1 lengthPost.2.1 lengthPost.2.2
      fourBytes
  let childEntry := decodeInlineRetryLengthBranchAfter lengthAfter branchRetired
  have branchPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + (4 + lengthUsed)) 1
      lengthAfter childEntry :=
    ConfinedPrefix.ownStep' lengthPost.1 (by simpa [childEntry] using branchRun)
      (notExit := prefixFalseAtLength)
  have completePrefix := ConfinedPrefix.trans lengthPrefix branchPrefix
  have childAgree : Agree decoderPreserved state childEntry :=
    Agree.trans lengthAgree (by simpa [childEntry] using branchPreserves)
  have childMemory : childEntry.mem = state.mem := by
    have branchMemory' : childEntry.mem = lengthAfter.mem := by
      simpa [childEntry] using branchMemory
    exact branchMemory'.trans lengthMemory
  have childCode : Contracts.canonicalContractParams.env.CodeIntact childEntry := by
    rw [Contracts.DecoderEnvironment.CodeIntact, childMemory]
    exact pre.code
  have childStackPointer : childEntry.regs.get? x2 =
      some (BitVec.ofNat 64 args.stackBase) :=
    ((fallThroughRetirement_writes _ _ _ _).get x2 (by decide)).trans lengthStackPointer
  have childGlobals : childEntry.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    ((fallThroughRetirement_writes _ _ _ _).get x18 (by decide)).trans lengthGlobals
  let childArgs : HasExactErePrefixInlineArgs :=
    { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes }
  have parentMachine : DecodeInlineMachinePre args childEntry :=
    pre.machine.mono childAgree (by simpa [childEntry] using branchCounter)
  have childMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
      childArgs.machineArgs childEntry := by
    simpa [childArgs, HasExactErePrefixInlineArgs.machineArgs, DecodeInlineArgs.machineArgs] using
      parentMachine.restrict hasExactErePrefix_executionPcs_subset_decode
  have childPre : HasExactErePrefixInlinePre childArgs childEntry := by
    refine ⟨?_, ?_, ?_, childGlobals, ?_, childCode, pre.inputFits, pre.rootInputBound, ?_, ?_, childMachine⟩
    · simpa [childArgs, HasExactErePrefixInlineArgs.entryPc] using branchPc
    · exact ((fallThroughRetirement_writes _ _ _ _).get x8 (by decide)).trans lengthInputPointer
    · exact ((fallThroughRetirement_writes _ _ _ _).get x9 (by decide)).trans lengthInputLength
    · intro index bound
      rw [childMemory]
      exact pre.inputMemory index bound
    · simp [childArgs]
    · intro _
      exact fourBytes
  refine ⟨lengthUsed, childEntry, lengthBound, ?_, ?_, childAgree, ?_, childStackPointer, childGlobals,
    childCode, childMemory⟩
  · have steps : 4 + lengthUsed + 1 = 5 + lengthUsed := by omega
    rw [← steps]
    exact completePrefix
  · change HasExactErePrefixInlinePre childArgs childEntry
    exact childPre
  · change RetiredCounterPresent childEntry at branchCounter
    exact branchCounter

end BinaryFv.Zesu.MachineExecution
