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
