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

/-- The selected emitted `decodeRaw` region is contained in its enclosing inlined `decode` region.
This is checked from the generated call relation, not handwritten address bounds. -/
theorem decodeRaw_executionPcs_subset_decodeInline (pc : BitVec 64)
    (pcIn : functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw pc) :
    decodeInlineOwnPcs pc := by
  have parentMember :
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
        generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨3, by native_decide, rfl⟩
  have childMember : functionInstance_ssz_raw_decodeRaw ∈
      generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨6, by native_decide, rfl⟩
  have childIsCallee : functionInstance_ssz_raw_decodeRaw ∈
      BinaryFv.RiscV.Elfling.calleeFunctionInstances generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 := by
    apply Array.mem_filter.mpr
    exact ⟨childMember, by native_decide⟩
  exact BinaryFv.Zesu.Elflings.Validation.generated_program_geometry.calleeWithinExecution
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
    parentMember functionInstance_ssz_raw_decodeRaw childIsCallee pc pcIn

theorem decodeRawReturnAfter_agree (returnPc : BitVec 64) (state : State)
    (retired : BitVec 64) :
    Agree decoderPreserved state (decodeRawReturnAfter returnPc state retired) :=
  Agree.weaken (fun _ preserved => preserved.2)
    ((jumpRetirement_writes _ _ _ _).agree platformPreserved_disjoint)

theorem decodeRawReturnAfter_mem (returnPc : BitVec 64) (state : State) (retired : BitVec 64) :
    (decodeRawReturnAfter returnPc state retired).mem = state.mem := rfl

theorem decodeRawReturnAfter_retired (returnPc : BitVec 64) (state : State)
    (retired : BitVec 64) :
    RetiredCounterPresent (decodeRawReturnAfter returnPc state retired) := by
  refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
  simp [decodeRawReturnAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]

/-- Execute the selected emitted child's real `ret` after its strengthened contract establishes the
link and machine frame required by that instruction. -/
theorem decodeRaw_return_step (stepNo : Nat) (rawArgs : Contracts.EntryArgs)
    (returnPc : BitVec 64) (childEntry childExit : State) {childFrom childUsed : Nat}
    (returnTarget : Sail.BitVec.update returnPc 0 0#1 = returnPc)
    (returnBit1 : Sail.BitVec.access returnPc 1 = 0#1)
    (childPre : compiledDecodeRawContract.binding.entry rawArgs childEntry)
    (childTrace : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)
      (Contracts.functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
      childFrom childUsed childEntry childExit)
    (entryLink : childEntry.regs.get? x1 = some returnPc)
    (childPost : compiledDecodeRawContract.binding.exit rawArgs
      (compiledDecodeRawContract.spec.meaning rawArgs) childEntry childExit) :
    ∃ retired,
      Runs (try_step stepNo false) childExit
        (decodeRawReturnAfter returnPc childExit retired) false ∧
      (decodeRawReturnAfter returnPc childExit retired).regs.get? PC = some returnPc := by
  rcases childPost with ⟨sourcePost, childFrame, childRetired, childPayload, _childSaveArea⟩
  rcases sourcePost with ⟨-, code, -, -⟩
  have machineAtExit : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (entryMachineArgs rawArgs) childExit :=
    childPre.2.2.mono
      (Agree.weaken (fun _ preserved => Or.inl preserved.2) childFrame) childRetired
  have atExit := decodeRaw_trace_exit_pc childTrace
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContextOfDecoderAgree machineAtExit (Agree.refl childExit)
  have exitLink : childExit.regs.get? x1 = some returnPc :=
    (childFrame x1 (by simp [decodeRawCallerPreserved, platformPreserved])).trans entryLink
  obtain ⟨retired, run⟩ : ∃ retired, Runs (try_step stepNo false) childExit
      (decodeRawReturnAfter returnPc childExit retired) false :=
    decoderRetStep machineAtExit (Agree.refl childExit) childRetired code
      stepNo 0x10530 0x67 0x80 0x00 0x00 1#5 returnPc returnPc atExit
      (rX_bits_run_x1 _ _ (decoderExecuteState_get? exitLink))
  refine ⟨retired, run, ?_⟩
  simp [decodeRawReturnAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    Std.ExtDHashMap.get?_insert]

/-- On a successful first `decodeRaw`, execute the real `bne a0, x0, 0x1037c` at `0x10324` as a
not-taken branch and continue to the success-copy setup at `0x10328`. -/
theorem decodeInline_first_success_branch_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10324))
    (successTag : state.regs.get? x10 = some (0#64)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (decodeInlineFirstSuccessBranchAfter state retired) false ∧
      (decodeInlineFirstSuccessBranchAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10328) := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  obtain ⟨retired, run⟩ := decoderBranchNotTakenStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10324 0x63 0x1c 0x05 0x04 0x58#13 0#5 10#5 .BNE atPc
    (by unfold bTypeTaken
        refine Runs.bind (rX_bits_run_x10 _ (0#64) (decoderExecuteState_get? successTag)) ?_
        refine Runs.bind (rX_x0_run _) ?_
        rfl)
  refine ⟨retired, ?_, ?_⟩
  · simpa [decodeInlineFirstSuccessBranchAfter] using run
  · simp [decodeInlineFirstSuccessBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]

end BinaryFv.Zesu.MachineExecution
