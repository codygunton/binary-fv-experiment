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
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L4_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L6_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L7_1

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

/-- Companion result for the first Level 3 outcome.  It retains the wrapper save frame proved by
the selected `decodeRaw` call while leaving `decodeInline_first_level3_relation`'s existing
semantic interface unchanged. -/
theorem decodeInline_first_level3_save_area (contract : CompiledDecodeRawInstanceContract)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) (phase : args.phase = .first) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep used before after ∧
      DecodeInlinePost args before after ∧
      DecodeInlineMachinePost before after ∧
      DecodeInlineOutgoingFrame args after ∧
      DecodeInlineCallerSaveArea args before after := by
  cases resultEq : Contracts.meaningDecodeRaw args.bytes with
  | ok value =>
      obtain ⟨childUsed, final, childBound, _, post, trace, machinePost, outgoing⟩ :=
        decodeInline_first_success_reaches_post contract fromStep args before pre phase value resultEq
      refine ⟨childUsed + 13, final, ?_, trace, ?_, machinePost, ?_, outgoing.2⟩
      · exact decodeInline_first_stepBound_le childBound (by omega)
      · simpa [DecodeInlinePost, phase] using post
      · simpa [DecodeInlineOutgoingFrame, phase] using outgoing.1
  | error error =>
      obtain ⟨_, childUsed, resumed, tagRetired, _, childBound, _, _, _, post, trace, machinePost,
        _, _, outgoing⟩ :=
        decodeInline_first_error_reaches_post contract fromStep args before pre phase error resultEq
      refine ⟨childUsed + 8,
        afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
          (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))), ?_, trace, ?_,
          machinePost, ?_, outgoing.2⟩
      · exact decodeInline_first_stepBound_le childBound (by omega)
      · simpa [DecodeInlinePost, phase] using post
      · simpa [DecodeInlineOutgoingFrame, phase] using outgoing.1

/-! ## Retry phase: mandatory entry branch -/

/-- Consume the second `decodeRaw` contract only after the exact-prefix path has executed the real
call setup. The child receives the four-byte-stripped input region, then its real `ret` returns to
`0x103dc`. -/
theorem decodeInline_retry_call_transfer
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true) :
    ∃ lengthUsed prefixUsed childUsed beforeCall resumed,
      lengthUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      prefixUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.retryRawArgs ∧
      ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary fromStep
          (11 + lengthUsed + prefixUsed) state beforeCall ∧
      Nonempty (CallTransfer decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary decodeRawRetryCall generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        functionInstance_ssz_raw_decodeRaw (fromStep + (11 + lengthUsed + prefixUsed))
          childUsed beforeCall resumed) ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.retryRawArgs
        Contracts.canonicalContractParams.repRawV4
        (Contracts.meaningDecodeRaw args.retryRawArgs.bytes) state resumed ∧
      Agree decoderPreserved state resumed ∧
      RetiredCounterPresent resumed ∧
      resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      DecodeRawResultPayloadInitialized args.retryRawArgs resumed ∧
      Contracts.canonicalContractParams.env.CodeIntact resumed ∧
      DecodeInlineCallerSaveArea args state resumed := by
  obtain ⟨lengthUsed, prefixUsed, beforeCall, lengthBound, prefixBound, parentPrefix, callPc,
    callBase, resultPointer, allocatorPointer, inputPointer, inputLength, beforeStack,
    beforeGlobals, beforeAgree, beforeCounter, beforeCode, beforeMemory⟩ :=
    decodeInline_retry_before_second_decodeRaw_call fromStep args state pre phase exactPrefix
  obtain ⟨callRetired, callRun, childPc, childLink, childResult, childAllocator, childInput,
    childLength, callAgree, callMemory, childCounter⟩ :=
    decodeInline_retry_decodeRaw_call_step
      (fromStep + (11 + lengthUsed + prefixUsed)) args state beforeCall pre beforeAgree
      beforeMemory beforeCounter callPc callBase resultPointer allocatorPointer inputPointer
      inputLength
  let childEntry := decodeInlineRetryCallAfter beforeCall callRetired
  have childAgree : Agree decoderPreserved state childEntry := Agree.trans beforeAgree callAgree
  have childMemory : childEntry.mem = state.mem := callMemory.trans beforeMemory
  have childStack : childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    ((callRetirement_writes _ _ _ _ _ _).get x2 (by decide)).trans beforeStack
  have childGlobals : childEntry.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    ((callRetirement_writes _ _ _ _ _ _).get x18 (by decide)).trans beforeGlobals
  have fourBytes : 4 ≤ args.bytes.size := by
    rw [Contracts.meaningHasExactErePrefix] at exactPrefix
    split at exactPrefix <;> simp_all
  have tailSize : args.retryRawArgs.bytes.size = args.bytes.size - 4 := by
    simp [DecodeInlineArgs.retryRawArgs, ByteArray.size_extract]
  have childMachineAtParentExtent : DecodeInlineMachinePre args childEntry :=
    pre.machine.mono childAgree childCounter
  have readableSubset : ∀ address,
      DecoderReadableByte (entryMachineArgs args.retryRawArgs) address →
        DecoderReadableByte args.machineArgs address := by
    intro address readable
    rcases readable with image | input | stack | allocator | arena
    · exact Or.inl image
    · exact Or.inr (Or.inl ⟨by
        simp only [entryMachineArgs, DecodeInlineArgs.retryRawArgs] at input
        simp only [DecodeInlineArgs.machineArgs]
        omega, by
        simp only [entryMachineArgs, DecodeInlineArgs.retryRawArgs] at input
        simp only [DecodeInlineArgs.machineArgs]
        have right := input.2
        simp only [ByteArray.size_extract] at right
        omega⟩)
    · exact Or.inr (Or.inr (Or.inl stack))
    · exact Or.inr (Or.inr (Or.inr (Or.inl allocator)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr arena)))
  have childMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (entryMachineArgs args.retryRawArgs) childEntry :=
    (childMachineAtParentExtent.narrowInput readableSubset).restrict
      decodeRaw_executionPcs_subset_decodeInline
  have childSourceEntry : Contracts.preEntry Contracts.canonicalContractParams.env
      args.retryRawArgs childEntry := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro index bound
      have originalBound : 4 + index < args.bytes.size := by
        rw [tailSize] at bound
        omega
      rw [childMemory]
      have original := pre.inputMemory (4 + index) originalBound
      simpa [DecodeInlineArgs.retryRawArgs, Nat.add_assoc,
        ByteArray.getElem_extract] using original
    · change Contracts.canonicalContractParams.env.image.fileBytesMatchMemory childEntry.mem
      rw [childMemory]
      exact pre.code
    · simpa [DecodeInlineArgs.retryRawArgs] using childResult
    · simpa [DecodeInlineArgs.retryRawArgs] using childAllocator
    · simpa [DecodeInlineArgs.retryRawArgs] using childInput
    · simpa [DecodeInlineArgs.retryRawArgs, tailSize] using childLength
  have childPre : compiledDecodeRawContract.binding.entry args.retryRawArgs childEntry :=
    ⟨childSourceEntry, childPc, childMachine⟩
  obtain ⟨childUsed, childExit, childBound, childTrace, childPost⟩ :=
    contract args.retryRawArgs (fromStep + (12 + lengthUsed + prefixUsed)) childEntry childPre
  obtain ⟨returnRetired, returnRun, atResume⟩ :=
    decodeRaw_return_step (fromStep + (12 + lengthUsed + prefixUsed + childUsed))
      args.retryRawArgs (BitVec.ofNat 64 0x103dc) childEntry childExit (by decide) (by decide)
      childPre childTrace childLink childPost
  let resumed := decodeRawReturnAfter (BitVec.ofNat 64 0x103dc) childExit returnRetired
  rcases childPost with ⟨sourcePost, childFrame, childExitCounter, childPayload, childSaveArea⟩
  rcases sourcePost with ⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩
  have childFrameDecoder : Agree decoderPreserved childEntry childExit :=
    Agree.weaken (fun _ preserved => Or.inl preserved.2) childFrame
  have resumedAgree : Agree decoderPreserved state resumed := Agree.trans childAgree
    (Agree.trans childFrameDecoder (by
      simpa [resumed] using
        decodeRawReturnAfter_agree (BitVec.ofNat 64 0x103dc) childExit returnRetired))
  have wReturn : WritesOnlyRegs _ childExit resumed := jumpRetirement_writes _ _ _ _
  have exitStack : childExit.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (childFrame x2 (by simp [decodeRawCallerPreserved])).trans childStack
  have exitGlobals : childExit.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (childFrame x18 (by simp [decodeRawCallerPreserved])).trans childGlobals
  have resumedStack : resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have resumedGlobals : resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have resumedPost : Contracts.postEntry Contracts.canonicalContractParams.env args.retryRawArgs
      Contracts.canonicalContractParams.repRawV4
      (Contracts.meaningDecodeRaw args.retryRawArgs.bytes) state resumed := by
    apply canonicalPostEntry_of_mem_eq args.retryRawArgs
      (Contracts.meaningDecodeRaw args.retryRawArgs.bytes) childMemory.symm
      (decodeRawReturnAfter_mem (BitVec.ofNat 64 0x103dc) childExit returnRetired)
    exact ⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩
  have transfer := decodeRawRetryCallTransfer
    (fromStep + (11 + lengthUsed + prefixUsed)) childUsed args phase exactPrefix beforeCall
      childEntry childExit resumed callPc (by simpa [childEntry] using callRun) childPre childBound
      (by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using childTrace)
      ⟨⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩,
        childFrame, childExitCounter, childPayload, childSaveArea⟩
      (by simpa [resumed, Nat.add_assoc] using returnRun) (by simpa [resumed] using atResume)
  have resumedCode : Contracts.canonicalContractParams.env.CodeIntact resumed := by
    simpa [resumed, decodeRawReturnAfter] using childCode
  have resumedPayload : DecodeRawResultPayloadInitialized args.retryRawArgs resumed := by
    obtain ⟨contents, contentsSize, contentsMemory⟩ := childPayload
    exact ⟨contents, contentsSize, by
      intro index bound
      rw [decodeRawReturnAfter_mem (BitVec.ofNat 64 0x103dc) childExit returnRetired]
      exact contentsMemory index bound⟩
  have resumedSaveArea : DecodeInlineCallerSaveArea args state resumed := by
    intro index bound
    rw [decodeRawReturnAfter_mem (BitVec.ofNat 64 0x103dc) childExit returnRetired]
    calc
      childExit.mem.get? (args.stackBase + 0xa00 + index) =
          childEntry.mem.get? (args.stackBase + 0xa00 + index) := by
        simpa [DecodeInlineCallerSaveArea, DecodeRawCallerSaveArea,
          DecodeInlineArgs.retryRawArgs, DecodeInlineArgs.allocatorBase, Nat.add_assoc] using
          childSaveArea index bound
      _ = state.mem.get? (args.stackBase + 0xa00 + index) := by rw [childMemory]
  exact ⟨lengthUsed, prefixUsed, childUsed, beforeCall, resumed, lengthBound, prefixBound,
    childBound, parentPrefix, ⟨transfer⟩, resumedPost, resumedAgree,
    decodeRawReturnAfter_retired (BitVec.ofNat 64 0x103dc) childExit returnRetired,
    resumedStack, resumedGlobals, resumedPayload, resumedCode, resumedSaveArea⟩

/-! ## Retry payload copy -/

end BinaryFv.Zesu.MachineExecution
