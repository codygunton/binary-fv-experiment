import BinaryFv.Zesu.MachineExecution.DecodeInlineProof
import BinaryFv.Zesu.MachineExecution.OwnedPc

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
    (contract : CompiledDecodeRawInstanceContract)
    (prefixContract : HasExactErePrefixInlineContract)
    (memcpy : CompiledMemcpyInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep used state after ∧
      DecodeInlinePost args state after ∧
      DecodeInlineMachinePost state after ∧
      DecodeInlineOutgoingFrame args after ∧
      DecodeInlineCallerSaveArea args state after ∧
      DecodeInlineRetrySuccessAllocationFrame args state after ∧
      used ≤ 16384 + 512 * args.retryRawArgs.bytes.size + 6765 := by
  obtain ⟨lengthUsed, prefixUsed, rawUsed, rawCall, decoded,
    lengthBound, prefixBound, rawBound, prefixToRawCall, ⟨rawTransfer⟩, decodedPost,
    decodedAgree, decodedCallerFrame, decodedCounter, decodedStack, _decodedInputBase, _decodedInputLength,
    decodedGlobals, decodedPayload, decodedCode,
    decodedSaveArea, decodedAllocation, decodedProvenance⟩ :=
    decodeInline_retry_call_transfer contract prefixContract fromStep args state pre phase exactPrefix
  let copyStart := fromStep + (13 + lengthUsed + prefixUsed + rawUsed)
  have decodedPc : decoded.regs.get? PC = some (BitVec.ofNat 64 0x103dc) := by
    have returnPcEq : rawTransfer.returnPc = BitVec.ofNat 64 0x103dc := by
      apply BitVec.eq_of_toNat_eq
      simpa [decodeRawRetryCall] using rawTransfer.returnMatches
    simpa [returnPcEq] using rawTransfer.atResume
  obtain ⟨contents, memcpyCall, contentsSize, copySetup, memcpyAtCall, memcpyCallBase,
    memcpyDestination, memcpySource, memcpyLength, memcpyStack, memcpyGlobals, sourceMemory, memcpyCallAgree,
    memcpyCallCallerFrame, memcpyCallCounter, memcpyCallCode, memcpyCallMemory⟩ :=
    decodeInline_retry_copy_setup copyStart args state decoded pre phase exactPrefix decodedAgree decodedCallerFrame
      decodedCounter decodedStack decodedGlobals decodedCode decodedPc
      decodedPayload
  obtain ⟨callRetired, memcpyUsed, childEntry, childExit, childEntryEq, childEntryPreservesGlobals, callRun, childPre,
    memcpyBound, childTrace, childPost⟩ :=
    decodeInline_retry_uses_memcpy memcpy (copyStart + 4) args contents state memcpyCall pre
      contentsSize
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
  have memcpyTransfer : CallTransfer decodeInlineOwnPcs
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
  have childEntryCallerFrame : Agree decodeRawCalleeSaved state childEntry := by
    subst childEntry
    exact memcpyCallCallerFrame.trans (by
      apply jalrCallAfterRetired_agree_of
      all_goals simp [decodeRawCalleeSaved])
  have childExitAgree : Agree decoderPreserved state childExit := Agree.trans childEntryAgree
    (Agree.weaken (fun register preserved => by
      rcases preserved with ⟨notLink, platform⟩
      rcases platform with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [NonW]) machinePost.frame)
  have childExitCallerFrame : Agree decodeRawCalleeSaved state childExit :=
    childEntryCallerFrame.trans (Agree.weaken (by
      intro register saved
      rcases saved with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [NonW])
      machinePost.frame)
  have returnedAgree : Agree decoderPreserved state returned :=
    Agree.trans childExitAgree (Agree.weaken (fun _ preserved => preserved.2)
      ((jumpRetirement_writes _ _ _ _).agree platformPreserved_disjoint))
  have returnedCallerFrame : Agree decodeRawCalleeSaved state returned :=
    childExitCallerFrame.trans ((jumpRetirement_writes _ _ _ _).agree decodeRawCalleeSaved_disjoint)
  have returnedCounter : RetiredCounterPresent returned := ⟨Sail.BitVec.addInt returnRetired 1, by
    simp [returned, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]⟩
  have returnedCode : Contracts.canonicalContractParams.env.CodeIntact returned := by
    simpa [returned, memcpyReturnAfter] using copiedCode
  have childEntryStack : childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    rw [childEntryEq]
    exact ((callRetirement_writes _ _ _ _ _ _).get x2 (by decide)).trans memcpyStack
  have childEntryGlobals : childEntry.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    childEntryPreservesGlobals.trans memcpyGlobals
  have childExitStack : childExit.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (machinePost.frame x2 (by simp [NonW])).trans childEntryStack
  have returnedStack : returned.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    ((jumpRetirement_writes _ _ _ _).get x2 (by decide)).trans childExitStack
  have childExitGlobals : childExit.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (machinePost.frame x18 (by simp [NonW])).trans childEntryGlobals
  have returnedGlobals : returned.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    ((jumpRetirement_writes _ _ _ _).get x18 (by decide)).trans childExitGlobals

  obtain ⟨pageRetired, pageRun⟩ := decodeInline_retry_final_page_step
    (copyStart + 6 + memcpyUsed) args state returned pre returnedAgree returnedCounter returnedCode
      (by simpa [returned] using returnedPc)
  let pageState := afterRegisterWrite returned (BitVec.ofNat 64 0x103f0) pageRetired x10
    (BitVec.ofNat 64 0x1000)
  have pageAgree : Agree decoderPreserved state pageState := Agree.trans returnedAgree
    (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved]))
  have pageCallerFrame : Agree decodeRawCalleeSaved state pageState := returnedCallerFrame.trans
    (afterRegisterWrite_agree_of (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved]))
  have pagePc : pageState.regs.get? PC = some (BitVec.ofNat 64 0x103f4) := by
    simpa [pageState] using afterRegisterWrite_pc returned (BitVec.ofNat 64 0x103f0)
      pageRetired x10 (BitVec.ofNat 64 0x1000)
  have pageStack : pageState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans returnedStack
  have pageValue : pageState.regs.get? x10 = some (BitVec.ofNat 64 0x1000) := by
    simp [pageState, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  have pageGlobals : pageState.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x18 (by decide)).trans returnedGlobals
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
  have rawPrefixAtCopy : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary fromStep
      (13 + lengthUsed + prefixUsed + rawUsed) state decoded := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rawPrefix
  have throughSetup := ConfinedPrefix.trans rawPrefixAtCopy copySetup
  have throughMemcpy := ConfinedPrefix.trans throughSetup (ConfinedPrefix.ofCall memcpyTransfer)
  have throughMemcpyAtPage : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary fromStep
      (19 + lengthUsed + prefixUsed + rawUsed + memcpyUsed) state returned := by
    simpa [copyStart, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using throughMemcpy
  have pagePrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (copyStart + 6 + memcpyUsed) 1
      returned pageState :=
    ConfinedPrefix.ownStep' (by simpa [returned] using returnedPc)
      (by simpa [pageState] using pageRun)
      (notExit := by simp [DecodeInlineExit, phase, exactPrefix])
  have pointerPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (copyStart + 7 + memcpyUsed) 1
      pageState after :=
    ConfinedPrefix.ownStep' pagePc (by simpa [after] using pointerRun)
      (notExit := by simp [DecodeInlineExit, phase, exactPrefix])
  have pagePrefixAtEnd : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (19 + lengthUsed + prefixUsed + rawUsed + memcpyUsed)) 1
      returned pageState := by
    simpa [copyStart, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using pagePrefix
  have pointerPrefixAtEnd : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (19 + lengthUsed + prefixUsed + rawUsed + memcpyUsed + 1)) 1
      pageState after := by
    simpa [copyStart, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using pointerPrefix
  have completePrefix := ConfinedPrefix.trans
    (ConfinedPrefix.trans throughMemcpyAtPage pagePrefixAtEnd) pointerPrefixAtEnd
  have selectedExit : DecodeInlineExit args (BitVec.ofNat 64 0x103f8) := by
    simp [DecodeInlineExit, phase, exactPrefix]
  have tailAtCopyEnd : ScopedTrace decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (copyStart + 8 + memcpyUsed) 0 after after :=
    ScopedTrace.exitAt (copyStart + 8 + memcpyUsed) after
      (BitVec.ofNat 64 0x103f8) afterPc selectedExit
  have tail : ScopedTrace decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (19 + lengthUsed + prefixUsed + rawUsed + memcpyUsed + 1 + 1))
      0 after after := by
    simpa [copyStart, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tailAtCopyEnd
  have trace := completePrefix 0 after tail

  have meaningEq : Contracts.meaningDecode args.bytes =
      Contracts.meaningDecodeRaw args.retryRawArgs.bytes := by
    have rawInvalid := (pre.retryReason phase).1
    simp [Contracts.meaningDecode, rawInvalid, exactPrefix, DecodeInlineArgs.retryRawArgs]
  have decodedPost' : Contracts.postEntry Contracts.canonicalContractParams.env args.retryRawArgs
      Contracts.canonicalContractParams.repStatelessInput (Contracts.meaningDecode args.bytes)
      state decoded := by simpa [meaningEq] using decodedPost
  have decodedToChildEntry : childEntry.mem = decoded.mem := by
    rw [childEntryEq]
    simpa [decodeInlineMemcpyCallAfter] using memcpyCallMemory
  have childExitToAfter : after.mem = childExit.mem := by
    rfl
  have afterSaveArea : DecodeInlineCallerSaveArea args state after := by
    intro index bound
    rw [childExitToAfter]
    rw [copyFrame (args.stackBase + 0xa00 + index) (Or.inr (by
      simp [decodeInlineRetryCopyArgs, DecodeInlineArgs.finalResultBase]
      omega))]
    rw [decodedToChildEntry]
    exact decodedSaveArea index bound
  have sourceDecoded : DecodedValue.MemoryBytes decoded
      args.retryRawArgs.resultBase contents := by
    intro index bound
    rw [← memcpyCallMemory]
    exact sourceMemory index bound
  have finalFrame : Contracts.CopyDestinationFrame (decodeInlineRetryCopyArgs args contents)
      decoded after := by
    intro address outside
    rw [childExitToAfter, copyFrame address outside, decodedToChildEntry]
  have sourceFinal : DecodedValue.MemoryBytes after args.retryRawArgs.resultBase contents := by
    intro index bound
    rw [childExitToAfter]
    exact sourceAfter index bound
  have destinationFinal : DecodedValue.MemoryBytes after args.finalResultBase contents := by
    intro index bound
    rw [childExitToAfter]
    exact destinationAfter index bound
  have codeFinal : Contracts.canonicalContractParams.env.CodeIntact after := by
    simpa [after, pageState, returned, memcpyReturnAfter, afterRegisterWrite_mem] using copiedCode
  have noAllocationFinal : Contracts.canonicalContractParams.env.NoAllocation decoded after := by
    intro address allocatorState
    rw [childExitToAfter, noAllocation address allocatorState, decodedToChildEntry]
  have allocationFrame : DecodeInlineRetrySuccessAllocationFrame args state after := by
    intro _ _
    exact ⟨decoded, contents, decodedPost', contentsSize, sourceDecoded, finalFrame, sourceFinal,
      destinationFinal, codeFinal, noAllocationFinal, decodedAllocation, decodedProvenance⟩
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
  have afterCallerFrame : Agree decodeRawCalleeSaved state after := pageCallerFrame.trans
    (afterRegisterWrite_agree_of (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved]))
  have afterCounter : RetiredCounterPresent after :=
    afterRegisterWrite_retired_present pageState (BitVec.ofNat 64 0x103f4) pointerRetired x10
      (BitVec.ofNat 64 (args.stackBase + 0x1000))
  have afterStack : after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans pageStack
  have afterPointer : after.regs.get? x10 =
      some (BitVec.ofNat 64 (args.stackBase + 0x1000)) := by
    simp [after, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  have afterGlobals : after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x18 (by decide)).trans pageGlobals
  have statusFinal : DecodedValue.ResultStatusLERep after
      (args.stackBase + 0x9f0)
      (Contracts.decodeInternalResultTag (Contracts.meaningDecode args.bytes)) := by
    rcases decodedPost.2.2.2.1 with ⟨tagBound, low, high⟩
    refine ⟨by simpa [meaningEq] using tagBound, ?_, ?_⟩
    · rw [finalFrame _ (Or.inr (by
        simp [decodeInlineRetryCopyArgs, DecodeInlineArgs.retryRawArgs,
          DecodeInlineArgs.finalResultBase]))]
      simpa [DecodeInlineArgs.retryRawArgs, meaningEq] using low
    · rw [finalFrame _ (Or.inr (by
        simp [decodeInlineRetryCopyArgs, DecodeInlineArgs.retryRawArgs,
          DecodeInlineArgs.finalResultBase]))]
      simpa [DecodeInlineArgs.retryRawArgs, meaningEq] using high
  refine ⟨19 + lengthUsed + prefixUsed + rawUsed + memcpyUsed + 1 + 1,
    after, ?_, ?_, retryPost,
    ⟨afterAgree, afterCallerFrame, afterCounter, codeFinal, afterGlobals.trans pre.globalsValue.symm⟩, ?_,
    afterSaveArea, allocationFrame, ?_⟩
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
  · simp [DecodeInlineOutgoingFrame, phase, exactPrefix, afterPointer, afterStack, statusFinal]
  · have lengthBoundValue : lengthUsed ≤ 12 := by
      simpa [hasExactErePrefixInlineStepBound] using lengthBound
    have prefixBoundValue : prefixUsed ≤ 12 := by
      simpa [hasExactErePrefixInlineStepBound] using prefixBound
    have rawBoundValue : rawUsed ≤ 16384 + 512 * args.retryRawArgs.bytes.size := by
      simpa [compiledDecodeRawContract, Contracts.contractDecodeRaw] using rawBound
    have memcpyBoundValue : memcpyUsed ≤ 64 + 8 * 832 := by
      simpa [compiledMemcpyContract, Contracts.contractMemcpy, decodeInlineRetryCopyArgs,
        contentsSize] using memcpyBound
    omega

/-- Companion result for the exact-prefix retry outcome.  Its save-frame conclusion follows the
second `decodeRaw` return through the real emitted `memcpy` frame and the two final Sail steps. -/
theorem decodeInline_retry_success_level3_save_area
    (contract : CompiledDecodeRawInstanceContract)
    (prefixContract : HasExactErePrefixInlineContract)
    (memcpy : CompiledMemcpyInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
      ScopedTrace decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep used state after ∧
      DecodeInlinePost args state after ∧
      DecodeInlineMachinePost state after ∧
      DecodeInlineOutgoingFrame args after ∧
      DecodeInlineCallerSaveArea args state after ∧
      DecodeInlineRetrySuccessAllocationFrame args state after ∧
      used ≤ 16384 + 512 * args.retryRawArgs.bytes.size + 6765 :=
  decodeInline_retry_success_reaches_post contract prefixContract memcpy fromStep args state pre
    phase exactPrefix

/-- A non-`invalidSsz` first error selects the outgoing edge at the second inline entry. The child
summary is therefore a zero-step selected exit; Level 2 retires the real branch to `0x103fc`. -/
theorem decodeInline_propagate_error_reaches_post (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (pre : DecodeInlinePre args before) (error : Contracts.DecodeError)
    (phase : args.phase = .propagateError error) :
    ∃ used after,
      used ≤ decodeInlineStepBound args ∧
        ScopedTrace decodeInlineOwnPcs
          (DecodeInlineExit args) Level3ChildSummary fromStep used before after ∧
        DecodeInlinePost args before after ∧
        DecodeInlineMachinePost before after ∧
        DecodeInlineOutgoingFrame args after ∧
        used = 0 := by
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
    ⟨Agree.refl before, Agree.refl before, pre.machine.retiredCounter, pre.code, rfl⟩, ?_, rfl⟩
  · simp [DecodeInlinePost, phase, notInvalid, rawResult, result, atExit]
  · simp [DecodeInlineOutgoingFrame, phase, tagA0, tagA1]

/-- The complete Level 3 theorem consumes the selected compiled `decodeRaw`, inlined prefix, and
emitted `memcpy` contracts. Every phase and semantic outcome is closed by one of the three
parent-execution arguments above. -/
theorem level3DecodeInlineContract
    (decodeRaw : CompiledDecodeRawInstanceContract)
    (prefixContract : HasExactErePrefixInlineContract)
    (memcpy : CompiledMemcpyInstanceContract) : Level3DecodeInlineContract := by
  intro args fromStep before pre
  cases phaseEq : args.phase with
  | first =>
      cases resultEq : Contracts.meaningDecodeRaw args.bytes with
      | ok value =>
          obtain ⟨childUsed, after, childBound, _, firstPost, scopedTrace, machine, stack,
            saveArea, allocation⟩ :=
            decodeInline_first_success_reaches_post decodeRaw fromStep args before pre phaseEq value
              resultEq
          have childBound' : childUsed ≤ 16384 + 512 * args.bytes.size := by
            simpa [compiledDecodeRawContract, Contracts.contractDecodeRaw,
              DecodeInlineArgs.firstRawArgs] using childBound
          have bound : childUsed + 13 ≤ decodeInlineStepBound args := by
            unfold decodeInlineStepBound
            omega
          have post : DecodeInlinePost args before after := by
            simpa [DecodeInlinePost, phaseEq] using firstPost
          exact ⟨childUsed + 13, after, bound, scopedTrace,
            scopedTrace.toFunctionTrace (level3ChildSummary_composes_decode args), post, machine,
            by simpa [DecodeInlineOutgoingFrame, phaseEq] using stack, saveArea,
            by simp [DecodeInlineFirstInvalidInputFrame, phaseEq, resultEq],
            by simp [DecodeInlineFirstErrorInputFrame, phaseEq, resultEq],
            by intro _; exact allocation,
            (by
              intro _ actualValue success
              rw [resultEq] at success
              cases success
              exact by simpa [resultEq] using firstPost.2.1),
            by simp [DecodeInlineRetrySuccessAllocationFrame, phaseEq],
            by intro _ _ _; omega,
            (by
              intro _ invalid
              cases invalid),
            (by
              intro retryPhase
              simp [phaseEq] at retryPhase),
            by intro retryPhase _ _; simp [phaseEq] at retryPhase,
            by intro retryPhase _ _; simp [phaseEq] at retryPhase,
            by intro _ propagation; simp [phaseEq] at propagation⟩
      | error error =>
          cases error with
          | invalidSsz =>
              obtain ⟨used, after, bound, scopedTrace, post, machine, outgoing, saveArea,
                inputValue, lengthValue, allocation, tightBound⟩ :=
                decodeInline_first_invalidSsz_level3_save_area decodeRaw args fromStep before pre
                  phaseEq (by simpa [resultEq])
              exact ⟨used, after, bound, scopedTrace,
                scopedTrace.toFunctionTrace (level3ChildSummary_composes_decode args), post,
                machine, outgoing, saveArea,
                by intro _ _; exact ⟨inputValue, lengthValue⟩,
                by intro _ _ _; exact ⟨inputValue, lengthValue⟩,
                by intro _; exact allocation,
                by simp [DecodeInlineFirstSuccessProvenanceFrame, phaseEq, resultEq],
                by simp [DecodeInlineRetrySuccessAllocationFrame, phaseEq],
                (by
                  intro _ _ success
                  cases success),
                (by
                  intro _ _
                  exact tightBound),
                (by
                  intro retryPhase
                  simp [phaseEq] at retryPhase),
                by intro retryPhase _ _; simp [phaseEq] at retryPhase,
                by intro retryPhase _ _; simp [phaseEq] at retryPhase,
                by intro _ propagation; simp [phaseEq] at propagation⟩
          | unknownFork =>
              obtain ⟨_, childUsed, resumed, tagRetired, _, childBound, _, _, _, _, firstPost,
                scopedTrace, machine, inputBase, inputLength, outgoing, saveArea, allocation⟩ :=
                decodeInline_first_error_reaches_post decodeRaw fromStep args before pre phaseEq .unknownFork
                  (by simpa [resultEq])
              let after := afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
                (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error .unknownFork)))
              have bound : childUsed + 8 ≤ decodeInlineStepBound args :=
                by
                  have childBound' : childUsed ≤ 16384 + 512 * args.bytes.size := by
                    simpa [compiledDecodeRawContract, Contracts.contractDecodeRaw,
                      DecodeInlineArgs.firstRawArgs] using childBound
                  unfold decodeInlineStepBound
                  omega
              have post : DecodeInlinePost args before after := by
                simpa [DecodeInlinePost, phaseEq, after] using firstPost
              have outgoing : DecodeInlineOutgoingFrame args after := by
                simpa [DecodeInlineOutgoingFrame, phaseEq, after] using outgoing
              exact ⟨childUsed + 8, after, bound, scopedTrace,
                scopedTrace.toFunctionTrace (level3ChildSummary_composes_decode args), post,
                machine, outgoing, saveArea,
                by simp [DecodeInlineFirstInvalidInputFrame, phaseEq, resultEq],
                by intro _ _ _; exact ⟨by simpa [after] using inputBase,
                  by simpa [after] using inputLength⟩,
                by intro _; simpa [after] using allocation,
                by simp [DecodeInlineFirstSuccessProvenanceFrame, phaseEq, resultEq],
                by simp [DecodeInlineRetrySuccessAllocationFrame, phaseEq],
                (by
                  intro _ _ success
                  cases success),
                (by
                  intro _ invalid
                  cases invalid),
                (by
                  intro retryPhase
                  simp [phaseEq] at retryPhase),
                by intro retryPhase _ _; simp [phaseEq] at retryPhase,
                by intro retryPhase _ _; simp [phaseEq] at retryPhase,
                by intro _ propagation; simp [phaseEq] at propagation⟩
          | outOfMemory =>
              obtain ⟨_, childUsed, resumed, tagRetired, _, childBound, _, _, _, _, firstPost,
                scopedTrace, machine, inputBase, inputLength, outgoing, saveArea, allocation⟩ :=
                decodeInline_first_error_reaches_post decodeRaw fromStep args before pre phaseEq .outOfMemory
                  (by simpa [resultEq])
              let after := afterRegisterWrite resumed (BitVec.ofNat 64 0x10320) tagRetired x10
                (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error .outOfMemory)))
              have bound : childUsed + 8 ≤ decodeInlineStepBound args :=
                by
                  have childBound' : childUsed ≤ 16384 + 512 * args.bytes.size := by
                    simpa [compiledDecodeRawContract, Contracts.contractDecodeRaw,
                      DecodeInlineArgs.firstRawArgs] using childBound
                  unfold decodeInlineStepBound
                  omega
              have post : DecodeInlinePost args before after := by
                simpa [DecodeInlinePost, phaseEq, after] using firstPost
              have outgoing : DecodeInlineOutgoingFrame args after := by
                simpa [DecodeInlineOutgoingFrame, phaseEq, after] using outgoing
              exact ⟨childUsed + 8, after, bound, scopedTrace,
                scopedTrace.toFunctionTrace (level3ChildSummary_composes_decode args), post,
                machine, outgoing, saveArea,
                by simp [DecodeInlineFirstInvalidInputFrame, phaseEq, resultEq],
                by intro _ _ _; exact ⟨by simpa [after] using inputBase,
                  by simpa [after] using inputLength⟩,
                by intro _; simpa [after] using allocation,
                by simp [DecodeInlineFirstSuccessProvenanceFrame, phaseEq, resultEq],
                by simp [DecodeInlineRetrySuccessAllocationFrame, phaseEq],
                (by
                  intro _ _ success
                  cases success),
                (by
                  intro _ invalid
                  cases invalid),
                (by
                  intro retryPhase
                  simp [phaseEq] at retryPhase),
                by intro retryPhase _ _; simp [phaseEq] at retryPhase,
                by intro retryPhase _ _; simp [phaseEq] at retryPhase,
                by intro _ propagation; simp [phaseEq] at propagation⟩
  | retryAfterInvalidSsz =>
      by_cases exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true
      · obtain ⟨used, after, bound, scopedTrace, post, machine, outgoing, saveArea, allocation,
          retryTightBound⟩ :=
          decodeInline_retry_success_level3_save_area decodeRaw prefixContract memcpy fromStep args
            before pre phaseEq exactPrefix
        exact ⟨used, after, bound, scopedTrace,
          scopedTrace.toFunctionTrace (level3ChildSummary_composes_decode args), post, machine,
          outgoing, saveArea, by simp [DecodeInlineFirstInvalidInputFrame, phaseEq],
          by simp [DecodeInlineFirstErrorInputFrame, phaseEq],
          by intro firstPhase; simp [phaseEq] at firstPhase,
          by simp [DecodeInlineFirstSuccessProvenanceFrame, phaseEq],
          allocation, by intro firstPhase; simp [phaseEq] at firstPhase,
          by intro firstPhase; simp [phaseEq] at firstPhase,
          by intro _ _; exact retryTightBound,
          by intro _ exactFalse _; simp_all,
          by intro _ exactFalse _; simp_all,
          by intro _ propagation; simp [phaseEq] at propagation⟩
      · have prefixFalse : Contracts.meaningHasExactErePrefix args.bytes = false :=
          by cases prefixEq : Contracts.meaningHasExactErePrefix args.bytes <;> simp_all
        by_cases short : args.bytes.size < 4
        · obtain ⟨used, after, bound, scopedTrace, post, machine, outgoing, saveArea, shortBound⟩ :=
            decodeInline_retry_short_reaches_post prefixContract fromStep args before pre phaseEq
              short
          exact ⟨used, after, bound, scopedTrace,
            scopedTrace.toFunctionTrace (level3ChildSummary_composes_decode args), post, machine,
            outgoing, saveArea, by simp [DecodeInlineFirstInvalidInputFrame, phaseEq],
            by simp [DecodeInlineFirstErrorInputFrame, phaseEq],
            by intro firstPhase; simp [phaseEq] at firstPhase,
            by simp [DecodeInlineFirstSuccessProvenanceFrame, phaseEq],
            by simp [DecodeInlineRetrySuccessAllocationFrame, phaseEq, exactPrefix],
            by intro firstPhase; simp [phaseEq] at firstPhase,
            by intro firstPhase; simp [phaseEq] at firstPhase,
            by intro _ exact; exact False.elim (exactPrefix exact),
            by intro _ _ _; exact shortBound,
            by intro _ _ fourBytes; omega,
            by intro _ propagation; simp [phaseEq] at propagation⟩
        · obtain ⟨used, after, bound, scopedTrace, post, machine, outgoing, saveArea, prefixBound⟩ :=
            decodeInline_retry_prefix_mismatch_reaches_post prefixContract fromStep args before pre
              phaseEq (by omega) prefixFalse
          exact ⟨used, after, bound, scopedTrace,
            scopedTrace.toFunctionTrace (level3ChildSummary_composes_decode args), post, machine,
            outgoing, saveArea, by simp [DecodeInlineFirstInvalidInputFrame, phaseEq],
            by simp [DecodeInlineFirstErrorInputFrame, phaseEq],
            by intro firstPhase; simp [phaseEq] at firstPhase,
            by simp [DecodeInlineFirstSuccessProvenanceFrame, phaseEq],
            by simp [DecodeInlineRetrySuccessAllocationFrame, phaseEq, exactPrefix],
            by intro firstPhase; simp [phaseEq] at firstPhase,
            by intro firstPhase; simp [phaseEq] at firstPhase,
            by intro _ exact; exact False.elim (exactPrefix exact),
            by intro _ _ short; omega,
            by intro _ _ _; exact prefixBound,
            by intro _ propagation; simp [phaseEq] at propagation⟩
  | propagateError error =>
      obtain ⟨used, after, bound, scopedTrace, post, machine, outgoing, usedZero⟩ :=
        decodeInline_propagate_error_reaches_post fromStep args before pre error phaseEq
      have post' := post
      simp only [DecodeInlinePost, phaseEq] at post'
      have same : after = before := post'.2.2.2.2
      exact ⟨used, after, bound, scopedTrace,
        scopedTrace.toFunctionTrace (level3ChildSummary_composes_decode args), post, machine,
        outgoing, by intro index bound; rw [same],
        by simp [DecodeInlineFirstInvalidInputFrame, phaseEq],
        by simp [DecodeInlineFirstErrorInputFrame, phaseEq],
        by intro firstPhase; simp [phaseEq] at firstPhase,
        by simp [DecodeInlineFirstSuccessProvenanceFrame, phaseEq],
        by simp [DecodeInlineRetrySuccessAllocationFrame, phaseEq],
        by intro firstPhase; simp [phaseEq] at firstPhase,
        by intro firstPhase; simp [phaseEq] at firstPhase,
        by intro retryPhase; simp [phaseEq] at retryPhase,
        by intro retryPhase _ _; simp [phaseEq] at retryPhase,
        by intro retryPhase _ _; simp [phaseEq] at retryPhase,
        by intro _ _; exact usedZero⟩

end BinaryFv.Zesu.MachineExecution
