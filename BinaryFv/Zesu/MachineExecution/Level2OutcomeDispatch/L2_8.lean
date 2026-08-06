import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.Level2TerminalRouteFrame
import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_1
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_2
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_3
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_4
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_5
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_6
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_7
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_8
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_9

/-!
# Level 2 result-tag dispatch

The wrapper owns the instructions after either inlined `decode` segment reaches `0x103fc`.
These Sail proofs distinguish the internal result tags before entering the shared wrapper tail.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The tag-two rejection tail records status `2`. -/
theorem wrapper_dispatch_tag2_status_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10418)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10418) retired x11 (BitVec.ofNat 64 2)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10418) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10418) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10418) 0x93#8 0x05#8 0x20#8 0x00#8 :=
    fetchFileInstruction state 0x10418 0x93 0x05 0x20 0x00
      (hasExactErePrefix_programImage_of_codeIntact code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have afterIncrementAgree : Agree platformPreserved base (tryStepControlFlowAfterIncrement state) :=
    agree.trans (agree_afterIncrement state)
  have privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine :=
    (afterIncrementAgree cur_privilege (by simp [platformPreserved])).trans machine.normal.2.1
  obtain ⟨mseccfgBits, mseccfgRead, -⟩ := machine.mseccfg
  have mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits :=
    (afterIncrementAgree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x20#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
    change Runs (ext_decode (0x00200593 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10418)
  have execute : Runs (execute (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 2) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x002#12 (0#64) = BitVec.ofNat 64 2 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x002#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 2))
  exact wrapper_dispatch_register_constant_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10418) fetchPc atPc 0x93#8 0x05#8 0x20#8 0x00#8
    (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) fetchBytes decode execute
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide) (by decide)

/-- The tag-two tail jumps into the shared wrapper rejection continuation at `0x1035c`. -/
theorem wrapper_dispatch_tag2_to_rejection_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1041c)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x1041c) (BitVec.ofNat 64 0x1035c))
        (BitVec.ofNat 64 0x1035c) retired) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x1041c) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x1041c) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1041c) 0x6f#8 0xf0#8 0x1f#8 0xf4#8 :=
    fetchFileInstruction state 0x1041c 0x6f 0xf0 0x1f 0xf4
      (hasExactErePrefix_programImage_of_codeIntact code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have afterIncrementAgree : Agree platformPreserved base (tryStepControlFlowAfterIncrement state) :=
    agree.trans (agree_afterIncrement state)
  have privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine :=
    (afterIncrementAgree cur_privilege (by simp [platformPreserved])).trans machine.normal.2.1
  obtain ⟨mseccfgBits, mseccfgRead, -⟩ := machine.mseccfg
  have mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits :=
    (afterIncrementAgree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have decode : Runs (ext_decode (fetchWord 0x6f#8 0xf0#8 0x1f#8 0xf4#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1fff40#21, zreg)) := by
    change Runs (ext_decode (0xf41ff06f : BitVec 32)) _ _ _
    decode_run
  have targetEq : BitVec.ofNat 64 0x1041c + sign_extend (m := 64) (0x1fff40#21) =
      BitVec.ofNat 64 0x1035c := by decide
  exact wrapper_dispatch_jump_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x1041c) (BitVec.ofNat 64 0x1035c) (0x1fff40#21) fetchPc atPc
    0x6f#8 0xf0#8 0x1f#8 0xf4#8 fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    targetEq (by decide) (by decide)

end BinaryFv.Zesu.MachineExecution
