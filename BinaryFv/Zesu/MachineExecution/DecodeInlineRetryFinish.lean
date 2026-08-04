import BinaryFv.Zesu.MachineExecution.DecodeInlineProof

/-!
# Level 3 retry-success composition

This module keeps the final composition separate from the large per-instruction proof. It consumes
the second `decodeRaw` condition, executes the payload-copy setup, consumes the proved emitted
`memcpy`, executes its real return, and executes the two remaining decoder-owned instructions.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.RiscV.Sep
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The exact-prefix retry path, with every parent instruction executed through Sail and both
selected calls represented by checked call transfers. -/
theorem decodeInline_retry_success_reaches_post
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
        (DecodeInlineExit args) Level3ChildSummary fromStep used state after ∧
      DecodeInlinePost args state after ∧
      DecodeInlineMachinePost state after ∧
      DecodeInlineOutgoingFrame args after := by
  obtain ⟨lengthUsed, prefixUsed, rawUsed, rawCall, decoded,
    lengthBound, prefixBound, rawBound, prefixToRawCall, ⟨rawTransfer⟩, decodedPost,
    decodedAgree, decodedCounter, decodedStack, decodedPayload, decodedCode⟩ :=
    decodeInline_retry_call_transfer contract fromStep args state pre phase exactPrefix
  let copyStart := fromStep + (13 + lengthUsed + prefixUsed + rawUsed)
  have decodedPc : decoded.regs.get? PC = some (BitVec.ofNat 64 0x103dc) := by
    have returnPcEq : rawTransfer.returnPc = BitVec.ofNat 64 0x103dc := by
      apply BitVec.eq_of_toNat_eq
      simpa [decodeRawRetryCall] using rawTransfer.returnMatches
    simpa [returnPcEq] using rawTransfer.atResume
  obtain ⟨contents, memcpyCall, contentsSize, copySetup, memcpyAtCall, memcpyCallBase,
    memcpyDestination, memcpySource, memcpyLength, memcpyStack, sourceMemory, memcpyCallAgree,
    memcpyCallCounter, memcpyCallCode, memcpyCallMemory⟩ :=
    decodeInline_retry_copy_setup copyStart args state decoded pre phase exactPrefix decodedAgree
      decodedCounter decodedStack decodedCode decodedPc
      decodedPayload
  obtain ⟨callRetired, memcpyUsed, childEntry, childExit, childEntryEq, callRun, childPre,
    memcpyBound, childTrace, childPost⟩ :=
    decodeInline_retry_uses_memcpy (copyStart + 4) args contents state memcpyCall pre contentsSize
      sourceMemory memcpyCallAgree memcpyCallCounter memcpyCallCode memcpyAtCall memcpyCallBase
      memcpyDestination memcpySource
      memcpyLength
  have childLink : childEntry.regs.get? x1 = some (BitVec.ofNat 64 0x103f0) := by
    subst childEntry
    simp [decodeInlineMemcpyCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, callLinkState, Std.ExtDHashMap.get?_insert]
  obtain ⟨returnRetired, returnRun, returnedPc⟩ :=
    memcpy_return_step (copyStart + 5 + memcpyUsed) (decodeInlineRetryCopyArgs args contents)
      (BitVec.ofNat 64 0x103f0) childEntry childExit (by decide) (by decide) childPre childTrace
      childLink childPost
  let returned := memcpyReturnAfter (BitVec.ofNat 64 0x103f0) childExit returnRetired
  have memcpyTransfer : CallTransfer
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary memcpyRetryCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_memcpy (copyStart + 4) memcpyUsed memcpyCall returned :=
    memcpyRetryCallTransfer (copyStart + 4) memcpyUsed args phase exactPrefix contents memcpyCall
      childEntry childExit returned memcpyAtCall callRun childPre memcpyBound childTrace childPost
      (by simpa [returned, Nat.add_assoc] using returnRun) (by simpa [returned] using returnedPc)

  rcases childPost with ⟨copyPost, machinePost⟩
  rcases copyPost with ⟨copiedCode, noAllocation, copyWrites, copyFrame,
    sourceAfter, destinationAfter⟩
  have childEntryAgree : Agree decoderPreserved state childEntry := by
    subst childEntry
    exact Agree.trans memcpyCallAgree (by
      apply jalrCallAfterRetired_agree_of
      all_goals simp [decoderPreserved, platformPreserved])
  have childExitAgree : Agree decoderPreserved state childExit := Agree.trans childEntryAgree
    (Agree.weaken (fun register preserved => by
      rcases preserved with ⟨notLink, platform⟩
      rcases platform with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [NonW]) machinePost.frame)
  have returnedAgree : Agree decoderPreserved state returned := Agree.trans childExitAgree (by
    intro register preserved
    rcases preserved with ⟨notLink, platform⟩
    rcases platform with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [returned, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState, Std.ExtDHashMap.get?_insert])
  have returnedCounter : RetiredCounterPresent returned := ⟨Sail.BitVec.addInt returnRetired 1, by
    simp [returned, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]⟩
  have returnedCode : Contracts.canonicalContractParams.env.CodeIntact returned := by
    simpa [returned, memcpyReturnAfter] using copiedCode
  have childEntryStack : childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    rw [childEntryEq]
    simp [decodeInlineMemcpyCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, callLinkState, controlFlowJumpState,
      tryStepControlFlowAfterIncrement, coreControlFlowNextState,
      Std.ExtDHashMap.get?_insert, memcpyStack]
  have childExitStack : childExit.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (machinePost.frame x2 (by simp [NonW])).trans childEntryStack
  have returnedStack : returned.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [returned, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState, Std.ExtDHashMap.get?_insert, childExitStack]

  obtain ⟨pageRetired, pageRun⟩ := decodeInline_retry_final_page_step
    (copyStart + 6 + memcpyUsed) args state returned pre returnedAgree returnedCounter returnedCode
      (by simpa [returned] using returnedPc)
  let pageState := afterRegisterWrite returned (BitVec.ofNat 64 0x103f0) pageRetired x10
    (BitVec.ofNat 64 0x1000)
  have pageAgree : Agree decoderPreserved state pageState := Agree.trans returnedAgree
    (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved]))
  have pagePc : pageState.regs.get? PC = some (BitVec.ofNat 64 0x103f4) := by
    simpa [pageState] using afterRegisterWrite_pc returned (BitVec.ofNat 64 0x103f0)
      pageRetired x10 (BitVec.ofNat 64 0x1000)
  have pageStack : pageState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simp [pageState, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, returnedStack]
  have pageValue : pageState.regs.get? x10 = some (BitVec.ofNat 64 0x1000) := by
    simp [pageState, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  have pageCode : Contracts.canonicalContractParams.env.CodeIntact pageState := by
    simpa [pageState, afterRegisterWrite_mem] using returnedCode
  obtain ⟨pointerRetired, pointerRun⟩ := decodeInline_retry_final_pointer_step
    (copyStart + 7 + memcpyUsed) args state pageState pre pageAgree
      (afterRegisterWrite_retired_present returned (BitVec.ofNat 64 0x103f0) pageRetired x10
        (BitVec.ofNat 64 0x1000)) pageCode pagePc pageStack pageValue
  let after := afterRegisterWrite pageState (BitVec.ofNat 64 0x103f4) pointerRetired x10
    (BitVec.ofNat 64 (args.stackBase + 0x1000))
  have afterPc : after.regs.get? PC = some (BitVec.ofNat 64 0x103f8) := by
    simpa [after] using afterRegisterWrite_pc pageState (BitVec.ofNat 64 0x103f4)
      pointerRetired x10 (BitVec.ofNat 64 (args.stackBase + 0x1000))

  have rawPrefix := ConfinedPrefix.trans prefixToRawCall (ConfinedPrefix.ofCall rawTransfer)
  have rawPrefixAtCopy : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary fromStep
      (13 + lengthUsed + prefixUsed + rawUsed) state decoded := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rawPrefix
  have throughSetup := ConfinedPrefix.trans rawPrefixAtCopy copySetup
  have throughMemcpy := ConfinedPrefix.trans throughSetup (ConfinedPrefix.ofCall memcpyTransfer)
  have throughMemcpyAtPage : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary fromStep
      (19 + lengthUsed + prefixUsed + rawUsed + memcpyUsed) state returned := by
    simpa [copyStart, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using throughMemcpy
  have pagePrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (copyStart + 6 + memcpyUsed) 1
      returned pageState := ConfinedPrefix.ownStep (by simpa [returned] using returnedPc)
    (decodeInline_owned_in_execution_region (0x103f0, 0x00001537)
      (by simp [decodeInlineOwnedInstructionWords]))
    (by simp [DecodeInlineExit, phase, exactPrefix]) (by simpa [pageState] using pageRun)
  have pointerPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (copyStart + 7 + memcpyUsed) 1
      pageState after := ConfinedPrefix.ownStep pagePc
    (decodeInline_owned_in_execution_region (0x103f4, 0x00a10533)
      (by simp [decodeInlineOwnedInstructionWords]))
    (by simp [DecodeInlineExit, phase, exactPrefix]) (by simpa [after] using pointerRun)
  have pagePrefixAtEnd : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (19 + lengthUsed + prefixUsed + rawUsed + memcpyUsed)) 1
      returned pageState := by
    simpa [copyStart, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using pagePrefix
  have pointerPrefixAtEnd : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (19 + lengthUsed + prefixUsed + rawUsed + memcpyUsed + 1)) 1
      pageState after := by
    simpa [copyStart, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using pointerPrefix
  have completePrefix := ConfinedPrefix.trans
    (ConfinedPrefix.trans throughMemcpyAtPage pagePrefixAtEnd) pointerPrefixAtEnd
  have selectedExit : DecodeInlineExit args (BitVec.ofNat 64 0x103f8) := by
    simp [DecodeInlineExit, phase, exactPrefix]
  have tailAtCopyEnd : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary (copyStart + 8 + memcpyUsed) 0 after after :=
    ScopedTrace.exitAt (copyStart + 8 + memcpyUsed) after
      (BitVec.ofNat 64 0x103f8) afterPc selectedExit
  have tail : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (19 + lengthUsed + prefixUsed + rawUsed + memcpyUsed + 1 + 1))
      0 after after := by
    simpa [copyStart, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tailAtCopyEnd
  have trace := completePrefix 0 after tail

  have meaningEq : Contracts.meaningDecode args.bytes =
      Contracts.meaningDecodeRaw args.retryRawArgs.bytes := by
    have rawInvalid := (pre.retryReason phase).1
    simp [Contracts.meaningDecode, rawInvalid, exactPrefix, DecodeInlineArgs.retryRawArgs]
  have decodedPost' : Contracts.postEntry Contracts.canonicalContractParams.env args.retryRawArgs
      Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecode args.bytes)
      state decoded := by simpa [meaningEq] using decodedPost
  have decodedToChildEntry : childEntry.mem = decoded.mem := by
    rw [childEntryEq]
    simpa [decodeInlineMemcpyCallAfter] using memcpyCallMemory
  have childExitToAfter : after.mem = childExit.mem := by
    rfl
  have sourceDecoded : MemoryRepresentation.MemoryBytes decoded
      args.retryRawArgs.resultBase contents := by
    intro index bound
    rw [← memcpyCallMemory]
    exact sourceMemory index bound
  have finalFrame : Contracts.CopyDestinationFrame (decodeInlineRetryCopyArgs args contents)
      decoded after := by
    intro address outside
    rw [childExitToAfter, copyFrame address outside, decodedToChildEntry]
  have sourceFinal : MemoryRepresentation.MemoryBytes after args.retryRawArgs.resultBase contents := by
    intro index bound
    rw [childExitToAfter]
    exact sourceAfter index bound
  have destinationFinal : MemoryRepresentation.MemoryBytes after args.finalResultBase contents := by
    intro index bound
    rw [childExitToAfter]
    exact destinationAfter index bound
  have codeFinal : Contracts.canonicalContractParams.env.CodeIntact after := by
    simpa [after, pageState, returned, memcpyReturnAfter, afterRegisterWrite_mem] using copiedCode
  have noAllocationFinal : Contracts.canonicalContractParams.env.NoAllocation decoded after := by
    intro address allocatorState
    rw [childExitToAfter, noAllocation address allocatorState, decodedToChildEntry]
  have retryPost : DecodeInlinePost args state after := by
    simp only [DecodeInlinePost, phase, DecodeInlineRetryPost, exactPrefix, if_true]
    refine ⟨?_, afterPc⟩
    exact ⟨decoded, contents, decodedPost', contentsSize, sourceDecoded, finalFrame, sourceFinal,
      destinationFinal, codeFinal, noAllocationFinal⟩
  have afterAgree : Agree decoderPreserved state after := pageAgree.trans
    (afterRegisterWrite_agree_of
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have afterCounter : RetiredCounterPresent after :=
    afterRegisterWrite_retired_present pageState (BitVec.ofNat 64 0x103f4) pointerRetired x10
      (BitVec.ofNat 64 (args.stackBase + 0x1000))
  have afterStack : after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    simpa [after] using
      (afterRegisterWrite_register pageState (BitVec.ofNat 64 0x103f4) pointerRetired x10 x2
        (BitVec.ofNat 64 (args.stackBase + 0x1000)) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans pageStack
  have tagOffset : Contracts.canonicalContractParams.env.record.entryResultTagOffset = 832 := by
    have pinned := congrArg (fun record => record.entryResultTagOffset)
      Contracts.canonicalRecordSizes_pinned
    simpa [Contracts.canonicalContractParams, Contracts.canonicalEnvironment] using pinned
  have statusFinal : MemoryRepresentation.ResultStatusLERep after
      (args.stackBase + 0x9f0)
      (Contracts.decodeInternalResultTag (Contracts.meaningDecode args.bytes)) := by
    rcases decodedPost.2.2.2.1 with ⟨tagBound, low, high⟩
    refine ⟨by simpa [meaningEq] using tagBound, ?_, ?_⟩
    · rw [finalFrame _ (Or.inr (by
        simp [decodeInlineRetryCopyArgs, DecodeInlineArgs.retryRawArgs, tagOffset]
        omega))]
      simpa [DecodeInlineArgs.retryRawArgs, tagOffset, meaningEq] using low
    · rw [finalFrame _ (Or.inr (by
        simp [decodeInlineRetryCopyArgs, DecodeInlineArgs.retryRawArgs, tagOffset]
        omega))]
      simpa [DecodeInlineArgs.retryRawArgs, tagOffset, meaningEq] using high
  refine ⟨19 + lengthUsed + prefixUsed + rawUsed + memcpyUsed + 1 + 1,
    after, ?_, ?_, retryPost, ⟨afterAgree, afterCounter, codeFinal⟩, ?_⟩
  · unfold decodeInlineStepBound
    have lengthBoundValue : lengthUsed ≤ 12 := by
      simpa [hasExactErePrefixInlineStepBound] using lengthBound
    have prefixBoundValue : prefixUsed ≤ 12 := by
      simpa [hasExactErePrefixInlineStepBound] using prefixBound
    have rawBoundValue : rawUsed ≤
        16384 + 512 * args.retryRawArgs.bytes.size := by
      simpa [compiledDecodeRawContract, Contracts.contractDecodeRaw] using rawBound
    have retrySize : args.retryRawArgs.bytes.size ≤ args.bytes.size := by
      simp [DecodeInlineArgs.retryRawArgs, ByteArray.size_extract]
    have memcpyBoundValue : memcpyUsed ≤ 64 + 8 * 832 := by
      simpa [compiledMemcpyContract, Contracts.contractMemcpy, decodeInlineRetryCopyArgs,
        contentsSize] using memcpyBound
    omega
  · simpa [copyStart, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using trace
  · simp [DecodeInlineOutgoingFrame, phase, exactPrefix, afterStack, statusFinal]

/-- A non-`invalidSsz` first error selects the outgoing edge at the second inline entry. The child
summary is therefore a zero-step selected exit; Level 2 retires the real branch to `0x103fc`. -/
theorem decodeInline_propagate_error_reaches_post (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (pre : DecodeInlinePre args before) (error : Contracts.DecodeError)
    (phase : args.phase = .propagateError error) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
        ScopedTrace
          (functionInstanceExecutionPcs generatedProgram
            functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
          (DecodeInlineExit args) Level3ChildSummary fromStep used before after ∧
        DecodeInlinePost args before after ∧
        DecodeInlineMachinePost before after ∧
        DecodeInlineOutgoingFrame args after := by
  obtain ⟨notInvalid, rawResult, tagA0, tagA1⟩ := pre.propagateReason error phase
  have result : Contracts.meaningDecode args.bytes = .error error := by
    cases error with
    | invalidSsz => exact False.elim (notInvalid rfl)
    | unknownFork => simp [Contracts.meaningDecode, rawResult]
    | outOfMemory => simp [Contracts.meaningDecode, rawResult]
  have atExit : before.regs.get? PC = some (BitVec.ofNat 64 0x10380) := by
    simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry
  have selectedExit : DecodeInlineExit args (BitVec.ofNat 64 0x10380) := by
    simp [DecodeInlineExit, phase]
  refine ⟨0, before, by simp, ScopedTrace.exitAt fromStep before
    (BitVec.ofNat 64 0x10380) atExit selectedExit, ?_,
    ⟨Agree.refl before, pre.machine.retiredCounter, pre.code⟩, ?_⟩
  · simp [DecodeInlinePost, phase, notInvalid, rawResult, result, atExit]
  · simp [DecodeInlineOutgoingFrame, phase, tagA0, tagA1]

/-- The complete Level 3 theorem. It assumes only the selected compiled `decodeRaw` contract;
the two prefix segments and emitted `memcpy` are discharged by their Sail proofs. Every phase and
semantic outcome is closed by one of the three parent-execution arguments above. -/
theorem level3DecodeInlineContract
    (decodeRaw : CompiledDecodeRawInstanceContract) : Level3DecodeInlineContract := by
  intro args fromStep before pre
  cases phaseEq : args.phase with
  | first =>
      exact decodeInline_first_level3_relation decodeRaw args fromStep before pre phaseEq
  | retryAfterInvalidSsz =>
      by_cases exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true
      · exact decodeInline_retry_success_reaches_post decodeRaw fromStep args before pre phaseEq
          exactPrefix
      · have prefixFalse : Contracts.meaningHasExactErePrefix args.bytes = false :=
          by cases prefixEq : Contracts.meaningHasExactErePrefix args.bytes <;> simp_all
        by_cases short : args.bytes.size < 4
        · exact decodeInline_retry_short_reaches_post fromStep args before pre phaseEq short
        · exact decodeInline_retry_prefix_mismatch_reaches_post fromStep args before pre phaseEq
            (by omega) prefixFalse
  | propagateError error =>
      exact decodeInline_propagate_error_reaches_post fromStep args before pre error phaseEq

end BinaryFv.Zesu.MachineExecution
