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
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_1
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_2
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_3
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_4
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_5
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_6
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_7
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_8
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_9
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_10
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_11
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_12

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

/-- Executes the tag-one rejection-result phase after the comparison branch. -/
theorem wrapper_dispatch_tag1_suffix {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10428)) :
    Tag1SuffixPath base stepNo state := by
  obtain ⟨r5, run5⟩ := wrapper_dispatch_tag1_clear_result_step machine agree retiredPresent code
    stepNo atPc
  let s5 := afterRegisterWrite state (BitVec.ofNat 64 0x10428) r5 x10 (BitVec.ofNat 64 0)
  have agree5 : Agree platformPreserved base s5 := agree.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired5 := afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10428) r5 x10
    (BitVec.ofNat 64 0)
  have code5 : canonicalContractParams.env.CodeIntact s5 := by
    simpa [s5, afterRegisterWrite_mem] using code
  have pc5 : s5.regs.get? PC = some (BitVec.ofNat 64 0x1042c) := by
    simpa [s5] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10428) r5 x10 (BitVec.ofNat 64 0)
  obtain ⟨r6, run6⟩ := wrapper_dispatch_tag1_status_step machine agree5 retired5 code5
    (stepNo + 1) pc5
  let s6 := afterRegisterWrite s5 (BitVec.ofNat 64 0x1042c) r6 x11 (BitVec.ofNat 64 4)
  have agree6 : Agree platformPreserved base s6 := agree5.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired6 := afterRegisterWrite_retired_present s5 (BitVec.ofNat 64 0x1042c) r6 x11
    (BitVec.ofNat 64 4)
  have code6 : canonicalContractParams.env.CodeIntact s6 := by
    change canonicalContractParams.env.image.fileBytesMatchMemory s6.mem
    change canonicalContractParams.env.image.fileBytesMatchMemory s5.mem at code5
    rw [show s6.mem = s5.mem from rfl]
    exact code5
  have pc6 : s6.regs.get? PC = some (BitVec.ofNat 64 0x10430) := by
    simpa [s6] using afterRegisterWrite_pc s5 (BitVec.ofNat 64 0x1042c) r6 x11 (BitVec.ofNat 64 4)
  obtain ⟨r7, run7⟩ := wrapper_dispatch_tag1_to_rejection_step machine agree6 retired6 code6
    (stepNo + 2) pc6
  let s7 := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s6)
      (BitVec.ofNat 64 0x10430) (BitVec.ofNat 64 0x1035c))
    (BitVec.ofNat 64 0x1035c) r7
  have p5 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary stepNo 1 state s5 :=
    ConfinedPrefix.ownStep atPc (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s5] using run5)
  have p6 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (stepNo + 1) 1 s5 s6 :=
    ConfinedPrefix.ownStep pc5 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s5, s6] using run6)
  have p7 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (stepNo + 2) 1 s6 s7 :=
    ConfinedPrefix.ownStep pc6 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s6] using run7)
  have suffixPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary stepNo 3 state s7 := by
    simpa using ConfinedPrefix.trans (ConfinedPrefix.trans p5 p6) p7
  refine ⟨⟨s7, Trace.step stepNo 2 state s5 s7 (by simpa [s5] using run5)
    (Trace.step (stepNo + 1) 1 s5 s6 s7 (by simpa [s5, s6] using run6)
    (Trace.step (stepNo + 2) 0 s6 s7 s7 (by simpa [s6] using run7)
      (Trace.refl (stepNo + 3) s7))), suffixPrefix, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [s7, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · have x10s5 : s5.regs.get? x10 = some (BitVec.ofNat 64 0) := by
      simp [s5, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        wrapperDispatchTag1BranchAfter, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert]
    have x10s6 : s6.regs.get? x10 = some (BitVec.ofNat 64 0) := by
      simpa [s6] using (afterRegisterWrite_register s5 (BitVec.ofNat 64 0x1042c) r6 x11 x10
        (BitVec.ofNat 64 4) (by decide) (by decide) (by decide) (by decide) (by decide)).trans x10s5
    exact tryStepControlFlowAfterRetired_preserves_register
      (controlFlowJumpState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10430)
        (BitVec.ofNat 64 0x1035c)) (BitVec.ofNat 64 0x1035c) r7 x10 (BitVec.ofNat 64 0)
      (by simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using x10s6) (by decide) (by decide)
  · have x11s6 : s6.regs.get? x11 = some (BitVec.ofNat 64 4) := by
      simp [s6, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert]
    apply tryStepControlFlowAfterRetired_preserves_register
    · simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using x11s6
    · decide
    · decide
  · exact ⟨Sail.BitVec.addInt r7 1, by
      simp [s7, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  · calc
      s7.mem = s6.mem := rfl
      _ = s5.mem := rfl
      _ = state.mem := rfl
  · exact agree6.trans (wrapperDispatchJumpAfter_agree s6 (BitVec.ofNat 64 0x10430)
      (BitVec.ofNat 64 0x1035c) r7)
  · simpa [s7, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code6
  · simp [s5, s6, s7, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- The tag-three route reaches the shared rejection continuation with `(a0, a1) = (0, 3)`. -/
theorem wrapper_dispatch_tag3_owned_path {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 3)) :
    Tag3OwnedPath base stepNo state := by
  obtain ⟨r1, run1⟩ := wrapper_dispatch_tag3_constant_step machine agree retiredPresent code stepNo atPc
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have agree1 : Agree platformPreserved base s1 := agree.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired1 := afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103fc) r1 x11
    (BitVec.ofNat 64 3)
  have code1 : canonicalContractParams.env.CodeIntact s1 := by
    simpa [s1, afterRegisterWrite_mem] using code
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
  have agree2 : Agree platformPreserved base s2 := agree1.trans
    (wrapperDispatchTag3BranchAfter_agree s1 r2)
  have retired2 : RetiredCounterPresent s2 := ⟨Sail.BitVec.addInt r2 1, by
    simp [s2, wrapperDispatchTag3BranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]⟩
  have code2 : canonicalContractParams.env.CodeIntact s2 := by
    simpa [s2, wrapperDispatchTag3BranchAfter] using code1
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10434) := by
    simp [s2, wrapperDispatchTag3BranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r3, run3⟩ := wrapper_dispatch_tag3_clear_result_step machine agree2 retired2 code2
    (stepNo + 2) pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10434) r3 x10 (BitVec.ofNat 64 0)
  have agree3 : Agree platformPreserved base s3 := agree2.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired3 := afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10434) r3 x10
    (BitVec.ofNat 64 0)
  have code3 : canonicalContractParams.env.CodeIntact s3 := by
    simpa [s3, afterRegisterWrite_mem] using code2
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10438) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10434) r3 x10 (BitVec.ofNat 64 0)
  obtain ⟨r4, run4⟩ := wrapper_dispatch_tag3_status_step machine agree3 retired3 code3
    (stepNo + 3) pc3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x10438) r4 x11 (BitVec.ofNat 64 3)
  have agree4 : Agree platformPreserved base s4 := agree3.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired4 := afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x10438) r4 x11
    (BitVec.ofNat 64 3)
  have code4 : canonicalContractParams.env.CodeIntact s4 :=
    codeIntact_of_mem_eq
      (afterRegisterWrite_mem s3 (BitVec.ofNat 64 0x10438) r4 x11 (BitVec.ofNat 64 3)) code3
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x1043c) := by
    simpa [s4] using afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x10438) r4 x11 (BitVec.ofNat 64 3)
  obtain ⟨r5, run5⟩ := wrapper_dispatch_tag3_to_rejection_step machine agree4 retired4 code4
    (stepNo + 4) pc4
  let s5 := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s4)
      (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c))
    (BitVec.ofNat 64 0x1035c) r5
  have confined : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary stepNo 5 state s5 := by
    have p1 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary stepNo 1 state s1 := ConfinedPrefix.ownStep atPc (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s1] using run1)
    have p2 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (stepNo + 1) 1 s1 s2 := ConfinedPrefix.ownStep pc1 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s1, s2] using run2)
    have p3 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (stepNo + 2) 1 s2 s3 := ConfinedPrefix.ownStep pc2 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s2, s3] using run3)
    have p4 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (stepNo + 3) 1 s3 s4 := ConfinedPrefix.ownStep pc3 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s3, s4] using run4)
    have p5 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (stepNo + 4) 1 s4 s5 := ConfinedPrefix.ownStep pc4 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by simpa [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s4] using run5)
    simpa [Nat.add_assoc] using ConfinedPrefix.trans (ConfinedPrefix.trans
      (ConfinedPrefix.trans (ConfinedPrefix.trans p1 p2) p3) p4) p5
  let trace : Trace stepNo 5 state s5 := Trace.step stepNo 4 state s1 s5 (by simpa [s1] using run1)
    (Trace.step (stepNo + 1) 3 s1 s2 s5 (by simpa [s1, s2] using run2)
    (Trace.step (stepNo + 2) 2 s2 s3 s5 (by simpa [s2, s3] using run3)
    (Trace.step (stepNo + 3) 1 s3 s4 s5 (by simpa [s3, s4] using run4)
    (Trace.step (stepNo + 4) 0 s4 s5 s5 (by simpa [s4] using run5)
      (Trace.refl (stepNo + 5) s5)))))
  let terminal : WrapperDispatchRouteFrame base state s5 stepNo 5
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 3) := by
    refine
      { trace := trace
        atTerminal := ?_
        resultValue := ?_
        statusValue := ?_
        memory := ?_
        platform := ?_
        code := ?_
        retired := ?_
        savedS2 := ?_
        savedStack := ?_ }
    · simp [s5, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
    · have x10s3 : s3.regs.get? x10 = some (BitVec.ofNat 64 0) := by
        simp [s3, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
          wrapperDispatchTag3BranchAfter, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
          Std.ExtDHashMap.get?_insert]
      have x10s4 : s4.regs.get? x10 = some (BitVec.ofNat 64 0) := by
        simpa [s4] using (afterRegisterWrite_register s3 (BitVec.ofNat 64 0x10438) r4 x11 x10
          (BitVec.ofNat 64 3) (by decide) (by decide) (by decide) (by decide) (by decide)).trans x10s3
      exact tryStepControlFlowAfterRetired_preserves_register
        (controlFlowJumpState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x1043c)
          (BitVec.ofNat 64 0x1035c)) (BitVec.ofNat 64 0x1035c) r5 x10 (BitVec.ofNat 64 0)
        (by simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
          Std.ExtDHashMap.get?_insert] using x10s4) (by decide) (by decide)
    · have x11s4 : s4.regs.get? x11 = some (BitVec.ofNat 64 3) := by
        simp [s4, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
          coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
      apply tryStepControlFlowAfterRetired_preserves_register
      · simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
          Std.ExtDHashMap.get?_insert] using x11s4
      · decide
      · decide
    · simp [s1, s2, s3, s4, s5, afterRegisterWrite_mem, wrapperDispatchTag3BranchAfter,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement]
    · exact agree4.trans (wrapperDispatchJumpAfter_agree s4 (BitVec.ofNat 64 0x1043c)
      (BitVec.ofNat 64 0x1035c) r5)
    · simpa [s5, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code4
    · exact ⟨Sail.BitVec.addInt r5 1, by
      simp [s5, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
    · simp [s1, s2, s3, s4, s5, wrapperDispatchTag3BranchAfter, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
    · simp [s1, s2, s3, s4, s5, wrapperDispatchTag3BranchAfter, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  exact ⟨s5, terminal, confined⟩

end BinaryFv.Zesu.MachineExecution
