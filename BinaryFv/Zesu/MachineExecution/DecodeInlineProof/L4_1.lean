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

/-- The first six decoder-owned instructions execute through Sail and establish the exact entry
predicate consumed by the selected `decodeRaw` child contract. -/
theorem decodeInline_first_enters_decodeRaw (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ childEntry, Trace fromStep 6 state childEntry ∧
      compiledDecodeRawContract.binding.entry args.firstRawArgs childEntry ∧
      childEntry.regs.get? x1 = some (BitVec.ofNat 64 0x10320) := by
  obtain ⟨beforeCall, beforeTrace, -, callPc, callBase, resultPointer, allocatorPointer,
    inputPointer, inputLength, -, beforeInputBase, beforeInputLength, beforeGlobals, beforeAgree, beforeMemory,
    beforeRetired⟩ :=
    decodeInline_first_before_decodeRaw_call fromStep args state pre phase
  obtain ⟨retired, callRun, childPc, childLink, childResult, childAllocator, childInput,
    childLength, -, -, -, callAgree, callMemory, childRetired⟩ :=
    decodeInline_first_decodeRaw_call_step (fromStep + 5) args state beforeCall pre
      beforeAgree beforeMemory beforeRetired callPc callBase resultPointer allocatorPointer
      inputPointer inputLength beforeInputBase beforeInputLength beforeGlobals
  let childEntry := decodeInlineFirstCallAfter beforeCall retired
  have childTrace : Trace fromStep 6 state childEntry :=
    Trace.snoc beforeTrace (by simpa [childEntry] using callRun)
  have childAgree : Agree decoderPreserved state childEntry :=
    Agree.trans beforeAgree callAgree
  have childMemory : childEntry.mem = state.mem := callMemory.trans beforeMemory
  have childMachineAtParentExtent : DecodeInlineMachinePre args childEntry :=
    pre.machine.mono childAgree childRetired
  have childMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (entryMachineArgs args.firstRawArgs) childEntry := by
    simpa [DecodeInlineArgs.machineArgs, entryMachineArgs, DecodeInlineArgs.firstRawArgs] using
      childMachineAtParentExtent.restrict decodeRaw_executionPcs_subset_decodeInline
  have sourceEntry :
      (Contracts.contractDecodeRaw Contracts.canonicalContractParams.env
        Contracts.canonicalContractParams.repRawV4).toFunctionInstance.binding.entry
        args.firstRawArgs childEntry := by
    change Contracts.preEntry Contracts.canonicalContractParams.env args.firstRawArgs childEntry
    refine ⟨?_, ?_, childResult, childAllocator, childInput, childLength⟩
    · intro index bound
      rw [childMemory]
      exact pre.inputMemory index bound
    · change Contracts.canonicalContractParams.env.image.fileBytesMatchMemory childEntry.mem
      rw [childMemory]
      exact pre.code
  exact ⟨childEntry, childTrace, ⟨sourceEntry, childPc, childMachine⟩, childLink⟩

theorem decodeInline_first_call_transfer
    (contract : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ beforeCall childUsed resumed,
      Trace fromStep 5 state beforeCall ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep 5 state beforeCall ∧
      childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs ∧
      Nonempty (CallTransfer decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        functionInstance_ssz_raw_decodeRaw (fromStep + 5) childUsed beforeCall resumed) ∧
      BinaryFv.Zesu.MemoryRepresentation.ResultStatusLERep resumed
        (args.firstTemporaryResultBase +
          Contracts.canonicalContractParams.env.record.entryResultTagOffset)
        (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)) ∧
      Contracts.canonicalContractParams.env.CodeIntact resumed ∧
      Agree decoderPreserved state resumed ∧
      RetiredCounterPresent resumed ∧
      resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      resumed.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      resumed.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
        Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
        state resumed ∧
      DecodeInlineCallerSaveArea args state resumed := by
  obtain ⟨beforeCall, parentTrace, parentPrefix, callPc, callBase, resultPointer, allocatorPointer,
    inputPointer, inputLength, beforeStack, beforeInputBase, beforeInputLength, beforeGlobals, beforeAgree,
    beforeMemory, beforeRetired⟩ :=
    decodeInline_first_before_decodeRaw_call fromStep args state pre phase
  obtain ⟨callRetired, callRun, childPc, childLink, childResult, childAllocator, childInput,
    childLength, childInputBase, childInputLength, childGlobals, callAgree, callMemory, childRetired⟩ :=
    decodeInline_first_decodeRaw_call_step (fromStep + 5) args state beforeCall pre
      beforeAgree beforeMemory beforeRetired callPc callBase resultPointer allocatorPointer
      inputPointer inputLength beforeInputBase beforeInputLength beforeGlobals
  let childEntry := decodeInlineFirstCallAfter beforeCall callRetired
  have childStack : childEntry.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    ((callRetirement_writes _ _ _ _ _ _).get x2 (by decide)).trans beforeStack
  have childAgree : Agree decoderPreserved state childEntry :=
    Agree.trans beforeAgree callAgree
  have childMachineAtParentExtent : DecodeInlineMachinePre args childEntry :=
    pre.machine.mono childAgree childRetired
  have childMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (entryMachineArgs args.firstRawArgs) childEntry := by
    simpa [DecodeInlineArgs.machineArgs, entryMachineArgs, DecodeInlineArgs.firstRawArgs] using
      childMachineAtParentExtent.restrict decodeRaw_executionPcs_subset_decodeInline
  have childMemory : childEntry.mem = state.mem := callMemory.trans beforeMemory
  have childSourceEntry : Contracts.preEntry Contracts.canonicalContractParams.env
      args.firstRawArgs childEntry := by
    refine ⟨?_, ?_, childResult, childAllocator, childInput, childLength⟩
    · intro index bound
      rw [childMemory]
      exact pre.inputMemory index bound
    · change Contracts.canonicalContractParams.env.image.fileBytesMatchMemory childEntry.mem
      rw [childMemory]
      exact pre.code
  have childPre : compiledDecodeRawContract.binding.entry args.firstRawArgs childEntry :=
    ⟨childSourceEntry, childPc, childMachine⟩
  obtain ⟨childUsed, childExit, bound, childTrace, childPost⟩ :=
    contract args.firstRawArgs (fromStep + 6) childEntry childPre
  obtain ⟨returnRetired, returnRun, atResume⟩ :=
    decodeRaw_return_step (fromStep + 6 + childUsed) args.firstRawArgs
      (BitVec.ofNat 64 0x10320) childEntry childExit (by decide) (by decide)
      childPre childTrace childLink childPost
  let resumed := decodeRawReturnAfter (BitVec.ofNat 64 0x10320) childExit returnRetired
  rcases childPost with ⟨sourcePost, childFrame, childCounter, childPayload, childSaveArea⟩
  rcases sourcePost with ⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩
  have resumedStatus : BinaryFv.Zesu.MemoryRepresentation.ResultStatusLERep resumed
      (args.firstTemporaryResultBase +
        Contracts.canonicalContractParams.env.record.entryResultTagOffset)
      (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)) := by
    simpa [resumed, DecodeInlineArgs.firstRawArgs] using childStatus
  have resumedCode : Contracts.canonicalContractParams.env.CodeIntact resumed := by
    simpa [resumed, decodeRawReturnAfter] using childCode
  have childFrameDecoder : Agree decoderPreserved childEntry childExit :=
    Agree.weaken (fun _ preserved => Or.inl preserved.2) childFrame
  have resumedAgree : Agree decoderPreserved state resumed :=
    Agree.trans childAgree
      (Agree.trans childFrameDecoder (by
        simpa [resumed] using
          (decodeRawReturnAfter_agree (BitVec.ofNat 64 0x10320) childExit returnRetired)))
  have wReturn : WritesOnlyRegs _ childExit resumed := jumpRetirement_writes _ _ _ _
  have exitStack : childExit.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (childFrame x2 (by simp [decodeRawCallerPreserved])).trans childStack
  have exitInputBase : childExit.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) :=
    (childFrame x8 (by simp [decodeRawCallerPreserved])).trans childInputBase
  have exitInputLength : childExit.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) :=
    (childFrame x9 (by simp [decodeRawCallerPreserved])).trans childInputLength
  have exitGlobals : childExit.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (childFrame x18 (by simp [decodeRawCallerPreserved])).trans childGlobals
  have resumedStack : resumed.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have resumedInputBase : resumed.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by grind
  have resumedInputLength : resumed.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by grind
  have resumedGlobals : resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have resumedPost : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
      state resumed := by
    apply canonicalPostEntry_of_mem_eq args.firstRawArgs (Contracts.meaningDecodeRaw args.bytes)
      childMemory.symm
        (decodeRawReturnAfter_mem (BitVec.ofNat 64 0x10320) childExit returnRetired)
    exact ⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩
  have resumedSaveArea : DecodeInlineCallerSaveArea args state resumed := by
    intro index bound
    rw [decodeRawReturnAfter_mem (BitVec.ofNat 64 0x10320) childExit returnRetired]
    calc
      childExit.mem.get? (args.stackBase + 0xa00 + index) =
          childEntry.mem.get? (args.stackBase + 0xa00 + index) := by
        simpa [DecodeInlineCallerSaveArea, DecodeRawCallerSaveArea,
          DecodeInlineArgs.firstRawArgs, DecodeInlineArgs.allocatorBase, Nat.add_assoc] using
          childSaveArea index bound
      _ = state.mem.get? (args.stackBase + 0xa00 + index) := by rw [childMemory]
  have transfer : CallTransfer decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_ssz_raw_decodeRaw (fromStep + 5) childUsed beforeCall resumed := by
    apply decodeRawFirstCallTransfer (fromStep + 5) childUsed args phase beforeCall childEntry
      childExit resumed callPc
    · simpa [childEntry] using callRun
    · exact childPre
    · exact bound
    · simpa only [Nat.add_assoc] using childTrace
    · exact ⟨⟨childInputMemory, childCode, childWrites, childStatus, childOutcome⟩,
        childFrame, childCounter, childPayload, childSaveArea⟩
    · simpa [resumed, Nat.add_assoc] using returnRun
    · simpa [resumed] using atResume
  exact ⟨beforeCall, childUsed, resumed, parentTrace, parentPrefix, bound, ⟨transfer⟩, resumedStatus,
    resumedCode, resumedAgree, by simpa [resumed] using
      decodeRawReturnAfter_retired (BitVec.ofNat 64 0x10320) childExit returnRetired,
      resumedStack, resumedInputBase, resumedInputLength, resumedGlobals, resumedPost, resumedSaveArea⟩

/-! ## First result dispatch -/

/-- Consume the proved one-instruction prefix length segment after the four parent-owned retry
instructions. The result remains at the outgoing `bltu` for the enclosing `decode` proof to execute. -/
theorem decodeInline_retry_uses_length_gate (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) :
    ∃ childUsed childAfter,
      childUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep (4 + childUsed) state childAfter ∧
      HasExactErePrefixInlinePost
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } childAfter ∧
      Agree decoderPreserved state childAfter ∧
      RetiredCounterPresent childAfter ∧
      childAfter.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      childAfter.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      childAfter.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      childAfter.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      childAfter.regs.get? x11 = some (BitVec.ofNat 64 2) ∧
      Contracts.canonicalContractParams.env.CodeIntact childAfter ∧
      childAfter.mem = state.mem := by
  obtain ⟨childEntry, parentPrefix, entryPc, x10Constant, x12Constant, parentAgree,
    parentCounter, parentStackPointer, parentStatus, parentCode, parentMemory, childPre⟩ :=
    decodeInline_retry_reaches_length_gate fromStep args state pre phase
  let childArgs : HasExactErePrefixInlineArgs :=
    { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes }
  have childPre' : HasExactErePrefixInlinePre childArgs childEntry := by
    simpa [childArgs] using childPre
  obtain ⟨childAfter, childTrace, childPost, childAgree, childCounter, childStackFrame,
    childInputPointer, childInputLength, childGlobals, childStatusEq, childMemory⟩ :=
    hasExactErePrefix_length_segment (fromStep + 4) childArgs childEntry childPre' rfl
  have childStatus : childAfter.regs.get? x11 = some (BitVec.ofNat 64 2) :=
    childStatusEq.trans parentStatus
  have childStackPointer : childAfter.regs.get? x2 =
      some (BitVec.ofNat 64 args.stackBase) := childStackFrame.trans parentStackPointer
  let childUsed := 1
  have childBound : childUsed ≤ hasExactErePrefixInlineStepBound childArgs := by
    simp [childUsed, hasExactErePrefixInlineStepBound]
  have exactSummary : hasExactErePrefixInlineSummary
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
      (fromStep + 4) childUsed childEntry childAfter :=
    ⟨rfl, childArgs, childPre', childBound, childTrace, childPost⟩
  have selectedSummary : Level3ChildSummary
      functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id
      (fromStep + 4) childUsed childEntry childAfter :=
    .hasExactErePrefix exactSummary
  have childPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 4) childUsed childEntry childAfter := by
    intro count final rest
    exact ScopedTrace.childBody (fromStep + 4) childUsed count _ childEntry childAfter final
      selectedSummary rest
  have completePrefix := ConfinedPrefix.trans parentPrefix childPrefix
  have completeAgree : Agree decoderPreserved state childAfter :=
    Agree.trans parentAgree childAgree
  have childCode : Contracts.canonicalContractParams.env.CodeIntact childAfter := by
    rw [Contracts.DecoderEnvironment.CodeIntact, childMemory]
    exact parentCode
  refine ⟨childUsed, childAfter, ?_, ?_, ?_, completeAgree, childCounter, childStackPointer,
    childInputPointer, childInputLength, childGlobals, childStatus, childCode,
    childMemory.trans parentMemory⟩
  · simpa [childArgs] using childBound
  · simpa [Nat.add_assoc] using completePrefix
  · simpa [childArgs] using childPost

end BinaryFv.Zesu.MachineExecution
