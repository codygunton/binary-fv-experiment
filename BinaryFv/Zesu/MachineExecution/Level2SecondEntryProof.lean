import BinaryFv.Zesu.MachineExecution.Level2WrapperProof
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.MachineExecution.Level2OutgoingBranchSteps

/-!
# Level 2 handoff to the second inlined `decode` entry

After the first inlined decoder reports `invalidSsz`, this module retires the wrapper's actual
branch and `li a1, 2`, rebuilds the retry entry facts at `0x10380`, and consumes the second
Level 3 decoder contract.  It stops before the second decoder's outgoing instruction.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem decodeInline_executionPcs_subset_wrapper (pc : BitVec 64)
    (inside : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 pc) :
    functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw pc := by
  have parentMember : functionInstance_raw_decoder_root_zesu_decode_raw ∈
      generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨1, by native_decide, rfl⟩
  have childMember : functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
      generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨3, by native_decide, rfl⟩
  have childIsCallee :
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
        BinaryFv.RiscV.Elfling.calleeFunctionInstances generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw := by
    apply Array.mem_filter.mpr
    exact ⟨childMember, by native_decide⟩
  exact BinaryFv.Zesu.Elflings.Validation.generated_program_geometry.calleeWithinExecution
    functionInstance_raw_decoder_root_zesu_decode_raw parentMember
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 childIsCallee
    pc inside

/-- Transfer a first `invalidSsz` result through the two wrapper-owned instructions to the retry
entry, then visibly consume the second Level 3 `decode` contract. -/
theorem wrapper_second_retry_decode_entry
    (decodeRaw : CompiledDecodeRawInstanceContract) (fromStep used : Nat) (args : DecodeInlineArgs)
    (before state : State) (pre : DecodeInlinePre args before)
    (body : level3DecodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      fromStep used before state)
    (frame : DecodeInlineMachinePost before state)
    (wrapperMachine : DecoderMachinePre decodeRawExecutionPcs args.machineArgs before)
    (phase : args.phase = .first)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10324))
    (tagRead : state.regs.get? x10 = some (BitVec.ofNat 64 2))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase))
    (inputValue : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase))
    (lengthValue : state.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size))
    (inputMemory : MemoryRepresentation.MemoryBytes state args.inputBase args.bytes)
    (invalid : Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz) :
    ∃ branchRetired retryRetired secondUsed secondAfter,
      Nonempty (InlineTransfer decodeRawExecutionPcs decodeRawExit
        Level2ChildSummary decodeInlineBoundary generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        fromStep used before (wrapperAfterDecodeFirstErrorBranch state branchRetired)) ∧
      Runs (try_step (fromStep + used + 1) false)
        (wrapperAfterDecodeFirstErrorBranch state branchRetired)
        (afterRegisterWrite (wrapperAfterDecodeFirstErrorBranch state branchRetired)
          (BitVec.ofNat 64 0x1037c) retryRetired x11 (BitVec.ofNat 64 2)) false ∧
      level3DecodeChildSummary
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
        (fromStep + used + 2) secondUsed
        (afterRegisterWrite (wrapperAfterDecodeFirstErrorBranch state branchRetired)
          (BitVec.ofNat 64 0x1037c) retryRetired x11 (BitVec.ofNat 64 2)) secondAfter := by
  obtain ⟨branchRetired, transfer⟩ := wrapper_decode_first_error_inlineTransfer fromStep used args
    before state pre body frame .invalidSsz phase atPc (by simpa [Contracts.decodeInternalResultTag] using tagRead)
  let branchState := wrapperAfterDecodeFirstErrorBranch state branchRetired
  have branchWrites : WritesOnlyRegs stepBookkeeping state branchState :=
    wrapperAfterDecodeFirstErrorBranch_writes state branchRetired
  have branchPc : branchState.regs.get? PC = some (BitVec.ofNat 64 0x1037c) :=
    tryStepControlFlowAfterRetired_pc _ (BitVec.ofNat 64 0x1037c) branchRetired
  have beforeToBranch : Agree decoderPreserved before branchState :=
    frame.agree.trans (wrapperAfterDecodeFirstErrorBranch_agree state branchRetired)
  have branchCounter := wrapperAfterDecodeFirstErrorBranch_retired state branchRetired
  have branchMachine := wrapperMachine.mono beforeToBranch branchCounter
  have branchCode := wrapperAfterDecodeFirstErrorBranch_code state branchRetired frame.code
  obtain ⟨retryRetired, retryRun⟩ := wrapper_retry_reason_step branchMachine (Agree.refl branchState)
    branchCounter branchCode (fromStep + used + 1) branchPc
  let secondState := afterRegisterWrite branchState (BitVec.ofNat 64 0x1037c) retryRetired x11
    (BitVec.ofNat 64 2)
  have secondPc : secondState.regs.get? PC = some (BitVec.ofNat 64 0x10380) := by
    simpa [secondState] using afterRegisterWrite_pc branchState (BitVec.ofNat 64 0x1037c)
      retryRetired x11 (BitVec.ofNat 64 2)
  have secondWrites : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x11))
      branchState secondState :=
    afterRegisterWrite_writes branchState (BitVec.ofNat 64 0x1037c) retryRetired x11
      (BitVec.ofNat 64 2)
  have branchStack : branchState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (branchWrites.get x2 (by decide)).trans stackValue
  have secondStack : secondState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (secondWrites.get x2 (by decide)).trans branchStack
  have branchInput : branchState.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) :=
    (branchWrites.get x8 (by decide)).trans inputValue
  have secondInput : secondState.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) :=
    (secondWrites.get x8 (by decide)).trans branchInput
  have branchLength : branchState.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) :=
    (branchWrites.get x9 (by decide)).trans lengthValue
  have secondLength : secondState.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) :=
    (secondWrites.get x9 (by decide)).trans branchLength
  have stateGlobals : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    frame.globalsValue.trans pre.globalsValue
  have branchGlobals : branchState.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (branchWrites.get x18 (by decide)).trans stateGlobals
  have secondGlobals : secondState.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (secondWrites.get x18 (by decide)).trans branchGlobals
  have secondMemory : MemoryRepresentation.MemoryBytes secondState args.inputBase args.bytes := by
    apply inputMemory.of_mem_eq
    simp [secondState, branchState, afterRegisterWrite_mem, wrapperAfterDecodeFirstErrorBranch,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement]
  have secondCode : canonicalContractParams.env.CodeIntact secondState := by
    simpa [secondState, afterRegisterWrite_mem] using branchCode
  have secondAgree : Agree decoderPreserved before secondState :=
    frame.agree.trans (wrapperAfterDecodeFirstErrorBranch_agree state branchRetired) |>.trans
      (afterRegisterWrite_agree_of
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved]))
  have secondMachine : DecodeInlineMachinePre
      { phase := .retryAfterInvalidSsz, stackBase := args.stackBase, inputBase := args.inputBase,
        bytes := args.bytes } secondState := by
    apply DecoderMachinePre.restrict decodeInline_executionPcs_subset_wrapper
    exact wrapperMachine.mono secondAgree
      (afterRegisterWrite_retired_present branchState (BitVec.ofNat 64 0x1037c) retryRetired x11
        (BitVec.ofNat 64 2))
  let secondArgs : DecodeInlineArgs :=
    { phase := .retryAfterInvalidSsz, stackBase := args.stackBase, inputBase := args.inputBase,
      bytes := args.bytes }
  have secondPre : DecodeInlinePre secondArgs secondState :=
    { atEntry := by simpa [secondArgs] using secondPc
      stackValue := by simpa [secondArgs] using secondStack
      inputValue := by simpa [secondArgs] using secondInput
      lengthValue := by simpa [secondArgs] using secondLength
      globalsValue := by simpa [secondArgs] using secondGlobals
      inputMemory := by simpa [secondArgs] using secondMemory
      code := secondCode
      inputFits := pre.inputFits
      rootInputBound := pre.rootInputBound
      stackAligned := pre.stackAligned
      stackObjectsFit := pre.stackObjectsFit
      stackObjectsReadable := pre.stackObjectsReadable
      machine := by simpa [secondArgs] using secondMachine
      retryReason := by
        intro _
        exact ⟨invalid,
          (secondWrites.get x10 (by decide)).trans ((branchWrites.get x10 (by decide)).trans tagRead),
          afterRegisterWrite_destination branchState (BitVec.ofNat 64 0x1037c) retryRetired x11
            (BitVec.ofNat 64 2) (by decide) (by decide)⟩
      propagateReason := by intro error impossible; simp [secondArgs] at impossible }
  obtain ⟨secondUsed, secondAfter, bound, trace, post, machinePost, outgoing⟩ :=
    level3DecodeInlineContract decodeRaw secondArgs (fromStep + used + 2) secondState secondPre
  refine ⟨branchRetired, retryRetired, secondUsed, secondAfter, transfer, ?_, ?_⟩
  · simpa [branchState, secondState] using retryRun
  · exact ⟨rfl, secondArgs, secondPre, bound, trace, post, machinePost, outgoing⟩

/-- At the same second entry, a non-`invalidSsz` first result builds the propagation phase and
consumes the zero-step Level 3 exit before Level 2 owns the outgoing branch. -/
theorem wrapper_second_propagate_decode_entry
    (decodeRaw : CompiledDecodeRawInstanceContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (branchState : State)
    (wrapperMachine : DecoderMachinePre decodeRawExecutionPcs args.machineArgs branchState)
    (atPc : branchState.regs.get? PC = some (BitVec.ofNat 64 0x1037c))
    (stackValue : branchState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase))
    (inputValue : branchState.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase))
    (lengthValue : branchState.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size))
    (globalsValue : branchState.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
    (inputMemory : MemoryRepresentation.MemoryBytes branchState args.inputBase args.bytes)
    (code : canonicalContractParams.env.CodeIntact branchState)
    (inputFits : args.inputBase + args.bytes.size ≤ 2 ^ 64)
    (rootInputBound : args.bytes.size < 2 * 1024 * 1024)
    (stackAligned : args.stackBase % 16 = 0)
    (stackObjectsFit : args.stackBase + 0x6b0 + canonicalContractParams.env.record.entryResult ≤ 2 ^ 64)
    (stackObjectsReadable : ∀ index,
      index < 0x6b0 + canonicalContractParams.env.record.entryResult →
        canonicalContractParams.env.stack (args.stackBase + index))
    (error : Contracts.DecodeError) (notInvalid : error ≠ .invalidSsz)
    (rawResult : Contracts.meaningDecodeRaw args.bytes = .error error)
    (tagRead : branchState.regs.get? x10 =
      some (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) :
    ∃ retryRetired secondUsed secondAfter,
      Runs (try_step fromStep false) branchState
        (afterRegisterWrite branchState (BitVec.ofNat 64 0x1037c) retryRetired x11
          (BitVec.ofNat 64 2)) false ∧
      level3DecodeChildSummary
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
        (fromStep + 1) secondUsed
        (afterRegisterWrite branchState (BitVec.ofNat 64 0x1037c) retryRetired x11
          (BitVec.ofNat 64 2)) secondAfter := by
  obtain ⟨retryRetired, retryRun⟩ := wrapper_retry_reason_step wrapperMachine (Agree.refl branchState)
    wrapperMachine.retiredCounter code fromStep atPc
  let secondState := afterRegisterWrite branchState (BitVec.ofNat 64 0x1037c) retryRetired x11
    (BitVec.ofNat 64 2)
  have secondPc : secondState.regs.get? PC = some (BitVec.ofNat 64 0x10380) := by
    simpa [secondState] using afterRegisterWrite_pc branchState (BitVec.ofNat 64 0x1037c)
      retryRetired x11 (BitVec.ofNat 64 2)
  have secondWrites : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x11))
      branchState secondState :=
    afterRegisterWrite_writes branchState (BitVec.ofNat 64 0x1037c) retryRetired x11
      (BitVec.ofNat 64 2)
  have secondStack : secondState.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    (secondWrites.get x2 (by decide)).trans stackValue
  have secondInput : secondState.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) :=
    (secondWrites.get x8 (by decide)).trans inputValue
  have secondLength : secondState.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) :=
    (secondWrites.get x9 (by decide)).trans lengthValue
  have secondGlobals : secondState.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (secondWrites.get x18 (by decide)).trans globalsValue
  have secondTag : secondState.regs.get? x10 =
      some (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))) :=
    (secondWrites.get x10 (by decide)).trans tagRead
  have secondMemory : MemoryRepresentation.MemoryBytes secondState args.inputBase args.bytes := by
    apply inputMemory.of_mem_eq
    simp [secondState, afterRegisterWrite_mem]
  have secondCode : canonicalContractParams.env.CodeIntact secondState := by
    simpa [secondState, afterRegisterWrite_mem] using code
  have secondMachine : DecodeInlineMachinePre
      { phase := .propagateError error, stackBase := args.stackBase, inputBase := args.inputBase,
        bytes := args.bytes } secondState := by
    apply DecoderMachinePre.restrict decodeInline_executionPcs_subset_wrapper
    exact wrapperMachine.mono
      (afterRegisterWrite_agree_of
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved]))
      (afterRegisterWrite_retired_present branchState (BitVec.ofNat 64 0x1037c) retryRetired x11
        (BitVec.ofNat 64 2))
  let secondArgs : DecodeInlineArgs :=
    { phase := .propagateError error, stackBase := args.stackBase, inputBase := args.inputBase,
      bytes := args.bytes }
  have secondPre : DecodeInlinePre secondArgs secondState :=
    { atEntry := by simpa [secondArgs] using secondPc
      stackValue := by simpa [secondArgs] using secondStack
      inputValue := by simpa [secondArgs] using secondInput
      lengthValue := by simpa [secondArgs] using secondLength
      globalsValue := by simpa [secondArgs] using secondGlobals
      inputMemory := by simpa [secondArgs] using secondMemory
      code := secondCode
      inputFits := inputFits
      rootInputBound := rootInputBound
      stackAligned := stackAligned
      stackObjectsFit := stackObjectsFit
      stackObjectsReadable := stackObjectsReadable
      machine := by simpa [secondArgs] using secondMachine
      retryReason := by intro impossible; simp [secondArgs] at impossible
      propagateReason := by
        intro selected selectedPhase
        simp [secondArgs] at selectedPhase
        subst selected
        exact ⟨notInvalid, rawResult, secondTag,
          afterRegisterWrite_destination branchState (BitVec.ofNat 64 0x1037c) retryRetired x11
            (BitVec.ofNat 64 2) (by decide) (by decide)⟩ }
  obtain ⟨secondUsed, secondAfter, bound, trace, post, machinePost, outgoing⟩ :=
    level3DecodeInlineContract decodeRaw secondArgs (fromStep + 1) secondState secondPre
  exact ⟨retryRetired, secondUsed, secondAfter, by simpa [secondState] using retryRun,
    ⟨rfl, secondArgs, secondPre, bound, trace, post, machinePost, outgoing⟩⟩

end BinaryFv.Zesu.MachineExecution
