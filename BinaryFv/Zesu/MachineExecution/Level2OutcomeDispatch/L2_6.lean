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

/-- Any tag other than one falls through the second comparison to `0x1040c`. -/
theorem wrapper_dispatch_tag1_miss_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10408))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 tagValue))
    (comparison : state.regs.get? x11 = some (BitVec.ofNat 64 1))
    (notTag1 : BitVec.ofNat 64 tagValue ≠ BitVec.ofNat 64 1) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10408))
        (BitVec.ofNat 64 0x1040c) retired) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10408) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10408) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10408) 0x63#8 0x00#8 0xb5#8 0x02#8 :=
    fetchFileInstruction state 0x10408 0x63 0x00 0xb5 0x02
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
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x00#8 0xb5#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x20#13, .Regidx 11#5, .Regidx 10#5, .BEQ)) := by
    change Runs (ext_decode (0x02b50063 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10408)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 tagValue) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tag]
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 1) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, comparison]
  have condition : Runs (bTypeTaken (.Regidx 11#5) (.Regidx 10#5) .BEQ)
      executeState executeState false := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    refine Runs.bind (rX_bits_run_x11 executeState _ x11AtExecute) ?_
    have comparisonFalse : (BitVec.ofNat 64 tagValue == BitVec.ofNat 64 1) = false := by
      cases equal : (BitVec.ofNat 64 tagValue == BitVec.ofNat 64 1) with
      | false => rfl
      | true => exact False.elim (notTag1 (beq_iff_eq.mp equal))
    rw [comparisonFalse]
    rfl
  exact wrapper_dispatch_branch_not_taken_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10408) (0x20#13) (.Regidx 11#5) (.Regidx 10#5) .BEQ fetchPc atPc
    0x63#8 0x00#8 0xb5#8 0x02#8 fetchBytes (by unfold BaseInstructionEncoding; decide) decode condition

/-- The third dispatch instruction writes the tag-two comparison constant. -/
theorem wrapper_dispatch_tag2_constant_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1040c)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1040c) retired x11 (BitVec.ofNat 64 2)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x1040c) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x1040c) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1040c) 0x93#8 0x05#8 0x20#8 0x00#8 :=
    fetchFileInstruction state 0x1040c 0x93 0x05 0x20 0x00
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
    (BitVec.ofNat 64 0x1040c)
  have execute : Runs (execute (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 2) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x002#12 (0#64) = BitVec.ofNat 64 2 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x002#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 2))
  exact wrapper_dispatch_register_constant_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x1040c) fetchPc atPc 0x93#8 0x05#8 0x20#8 0x00#8
    (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) fetchBytes decode execute
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide) (by decide)

end BinaryFv.Zesu.MachineExecution
