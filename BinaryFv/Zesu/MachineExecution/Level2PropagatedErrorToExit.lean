import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch

/-! The tag-three wrapper dispatch owns five concrete instructions before the shared status store. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The shared first dispatch instruction is owned by the wrapper and writes comparison tag three. -/
theorem wrapper_dispatch_tag3_constant_confined {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retired : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (pc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc)) :
    ∃ after, ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary stepNo 1 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x10400) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 3) ∧
      Agree platformPreserved base after ∧ canonicalContractParams.env.CodeIntact after ∧
      RetiredCounterPresent after ∧ after.mem = state.mem ∧
      after.regs.get? x10 = state.regs.get? x10 ∧ after.regs.get? x2 = state.regs.get? x2 ∧
      after.regs.get? x18 = state.regs.get? x18 := by
  obtain ⟨r, run⟩ := wrapper_dispatch_tag3_constant_step machine agree retired code stepNo pc
  let after := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r x11 (BitVec.ofNat 64 3)
  refine ⟨after, ConfinedPrefix.ownStep pc (by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide) (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
    (by simpa [after] using run), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [after] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103fc) r x11 (BitVec.ofNat 64 3)
  · simp [after, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · exact agree.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  · simpa [after, afterRegisterWrite_mem] using code
  · exact afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103fc) r x11 (BitVec.ofNat 64 3)
  · rfl
  · exact afterRegisterWrite_register state (BitVec.ofNat 64 0x103fc) r x11 x10
      (BitVec.ofNat 64 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact afterRegisterWrite_register state (BitVec.ofNat 64 0x103fc) r x11 x2
      (BitVec.ofNat 64 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact afterRegisterWrite_register state (BitVec.ofNat 64 0x103fc) r x11 x18
      (BitVec.ofNat 64 3) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem tag3_branch_agree (state : State) (retired : BitVec 64) :
    Agree platformPreserved state (wrapperDispatchTag3BranchAfter state retired) := by
  intro register preserved
  have notRetired : minstret ≠ register := by
    intro equal; subst register; simp [platformPreserved] at preserved
  have notPc : PC ≠ register := by
    intro equal; subst register; simp [platformPreserved] at preserved
  have notNextPc : nextPC ≠ register := by
    intro equal; subst register; simp [platformPreserved] at preserved
  have notIncrement : minstret_increment ≠ register := by
    intro equal; subst register; simp [platformPreserved] at preserved
  simp [wrapperDispatchTag3BranchAfter, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
    tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, notRetired, notPc,
    notNextPc, notIncrement]

private theorem tag3_jump_agree (state : State) (pc target retired : BitVec 64) :
    Agree platformPreserved state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target) target retired) := by
  intro register preserved
  have notRetired : minstret ≠ register := by
    intro equal; subst register; simp [platformPreserved] at preserved
  have notPc : PC ≠ register := by
    intro equal; subst register; simp [platformPreserved] at preserved
  have notNextPc : nextPC ≠ register := by
    intro equal; subst register; simp [platformPreserved] at preserved
  have notIncrement : minstret_increment ≠ register := by
    intro equal; subst register; simp [platformPreserved] at preserved
  simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    notRetired, notPc, notNextPc, notIncrement]

/-- The tag-three dispatch is five wrapper-owned Sail steps from `0x103fc` to the common status
store.  This companion retains the confined ownership evidence and the terminal frame required by
the common status-store/epilogue phase. -/
theorem wrapper_dispatch_tag3_confined {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 3)) :
    ∃ after,
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary stepNo 5 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x1035c) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 0) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 3) ∧
      Agree platformPreserved base after ∧ canonicalContractParams.env.CodeIntact after ∧
      RetiredCounterPresent after ∧ after.mem = state.mem ∧
      after.regs.get? x18 = state.regs.get? x18 ∧ after.regs.get? x2 = state.regs.get? x2 := by
  obtain ⟨r1, run1⟩ := wrapper_dispatch_tag3_constant_step machine agree retiredPresent code stepNo atPc
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have agree1 : Agree platformPreserved base s1 := agree.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired1 := afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103fc) r1 x11
    (BitVec.ofNat 64 3)
  have code1 : canonicalContractParams.env.CodeIntact s1 := by simpa [s1, afterRegisterWrite_mem] using code
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x10400) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have tag1 : s1.regs.get? x10 = some (BitVec.ofNat 64 3) := by
    simpa [s1] using (afterRegisterWrite_register state (BitVec.ofNat 64 0x103fc) r1 x11 x10
      (BitVec.ofNat 64 3) (by decide) (by decide) (by decide) (by decide) (by decide)).trans tag
  have comparison1 : s1.regs.get? x11 = some (BitVec.ofNat 64 3) := by
    simp [s1, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r2, run2, -⟩ := wrapper_dispatch_tag3_branch_step machine agree1 retired1 code1
    (stepNo + 1) pc1 tag1 comparison1
  let s2 := wrapperDispatchTag3BranchAfter s1 r2
  have agree2 : Agree platformPreserved base s2 := agree1.trans (tag3_branch_agree s1 r2)
  have retired2 : RetiredCounterPresent s2 := ⟨Sail.BitVec.addInt r2 1, by
    simp [s2, wrapperDispatchTag3BranchAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  have code2 : canonicalContractParams.env.CodeIntact s2 := by simpa [s2, wrapperDispatchTag3BranchAfter] using code1
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10434) := by
    simp [s2, wrapperDispatchTag3BranchAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r3, run3⟩ := wrapper_dispatch_tag3_clear_result_step machine agree2 retired2 code2 (stepNo + 2) pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10434) r3 x10 (BitVec.ofNat 64 0)
  have agree3 : Agree platformPreserved base s3 := agree2.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired3 := afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10434) r3 x10 (BitVec.ofNat 64 0)
  have code3 : canonicalContractParams.env.CodeIntact s3 := by simpa [s3, afterRegisterWrite_mem] using code2
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10438) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10434) r3 x10 (BitVec.ofNat 64 0)
  obtain ⟨r4, run4⟩ := wrapper_dispatch_tag3_status_step machine agree3 retired3 code3 (stepNo + 3) pc3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x10438) r4 x11 (BitVec.ofNat 64 3)
  have agree4 : Agree platformPreserved base s4 := agree3.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired4 := afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x10438) r4 x11 (BitVec.ofNat 64 3)
  have code4 : canonicalContractParams.env.CodeIntact s4 := by simpa [s4, afterRegisterWrite_mem] using code3
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x1043c) := by
    simpa [s4] using afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x10438) r4 x11 (BitVec.ofNat 64 3)
  obtain ⟨r5, run5⟩ := wrapper_dispatch_tag3_to_rejection_step machine agree4 retired4 code4 (stepNo + 4) pc4
  let s5 := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x1043c)
      (BitVec.ofNat 64 0x1035c)) (BitVec.ofNat 64 0x1035c) r5
  have own1 : functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
      (BitVec.ofNat 64 0x103fc) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr; apply RegionPcs.iff_inRanges.mpr; native_decide
  have own2 : functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
      (BitVec.ofNat 64 0x10400) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr; apply RegionPcs.iff_inRanges.mpr; native_decide
  have own3 : functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
      (BitVec.ofNat 64 0x10434) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr; apply RegionPcs.iff_inRanges.mpr; native_decide
  have own4 : functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
      (BitVec.ofNat 64 0x10438) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr; apply RegionPcs.iff_inRanges.mpr; native_decide
  have own5 : functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
      (BitVec.ofNat 64 0x1043c) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr; apply RegionPcs.iff_inRanges.mpr; native_decide
  have p1 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary stepNo 1 state s1 :=
    ConfinedPrefix.ownStep atPc own1 (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s1] using run1)
  have p2 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (stepNo + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep pc1 own2 (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s1, s2] using run2)
  have p3 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (stepNo + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep pc2 own3 (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s2, s3] using run3)
  have p4 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (stepNo + 3) 1 s3 s4 :=
    ConfinedPrefix.ownStep pc3 own4 (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s3, s4] using run4)
  have p5 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (stepNo + 4) 1 s4 s5 :=
    ConfinedPrefix.ownStep pc4 own5 (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s4, s5] using run5)
  refine ⟨s5, by simpa [Nat.add_assoc] using ConfinedPrefix.trans (ConfinedPrefix.trans
    (ConfinedPrefix.trans (ConfinedPrefix.trans p1 p2) p3) p4) p5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [s5, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · simp [s3, s4, s5, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · simp [s4, s5, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · exact agree4.trans (tag3_jump_agree s4 (BitVec.ofNat 64 0x1043c)
      (BitVec.ofNat 64 0x1035c) r5)
  · simpa [s5, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code4
  · exact ⟨Sail.BitVec.addInt r5 1, by simp [s5, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  · rfl
  · simp [s1, s2, s3, s4, s5, afterRegisterWrite, wrapperDispatchTag3BranchAfter,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · simp [s1, s2, s3, s4, s5, afterRegisterWrite, wrapperDispatchTag3BranchAfter,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

end BinaryFv.Zesu.MachineExecution
