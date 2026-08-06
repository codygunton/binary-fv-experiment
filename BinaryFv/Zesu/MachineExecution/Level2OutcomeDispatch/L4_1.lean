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
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L3_1
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L3_2

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

/-- The zero-result route reaches the success continuation with `(a0, a1) = (0, 2)`. -/
theorem wrapper_dispatch_tag0_success_path {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 0)) :
    DispatchPath base stepNo 6 state (BitVec.ofNat 64 0x1033c) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 2) := by
  obtain ⟨r1, r2, r3, r4, r5, run1, run2, run3, run4, run5, pc5, tag5, comparison5⟩ :=
    wrapper_dispatch_non_three_non_one_prefix machine agree retiredPresent code stepNo 0 atPc tag
      (by decide) (by decide)
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  let s2 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10400))
    (BitVec.ofNat 64 0x10404) r2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
  let s4 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10408))
    (BitVec.ofNat 64 0x1040c) r4
  let s5 := afterRegisterWrite s4 (BitVec.ofNat 64 0x1040c) r5 x11 (BitVec.ofNat 64 2)
  have agree1 : Agree platformPreserved base s1 := agree.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have agree2 : Agree platformPreserved base s2 := agree1.trans
    (wrapperDispatchBranchNotTakenAfter_agree s1 (BitVec.ofNat 64 0x10400) r2)
  have agree3 : Agree platformPreserved base s3 := agree2.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have agree4 : Agree platformPreserved base s4 := agree3.trans
    (wrapperDispatchBranchNotTakenAfter_agree s3 (BitVec.ofNat 64 0x10408) r4)
  have agree5 : Agree platformPreserved base s5 := agree4.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired5 : RetiredCounterPresent s5 := ⟨Sail.BitVec.addInt r5 1, by
    simp [s5, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  have code5 : canonicalContractParams.env.CodeIntact s5 := by
    simpa [s1, s2, s3, s4, s5, afterRegisterWrite_mem, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code
  obtain ⟨r6, run6⟩ := wrapper_dispatch_tag0_success_step machine agree5 retired5 code5
    (stepNo + 5) (by simpa [s1, s2, s3, s4, s5] using pc5)
    (by simpa [s1, s2, s3, s4, s5] using tag5)
    (by simpa [s1, s2, s3, s4, s5] using comparison5)
  let s6 := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s5)
      (BitVec.ofNat 64 0x10410) (BitVec.ofNat 64 0x1033c))
    (BitVec.ofNat 64 0x1033c) r6
  refine ⟨⟨s6,
    Trace.step stepNo 5 state s1 s6 run1
      (Trace.step (stepNo + 1) 4 s1 s2 s6 run2
        (Trace.step (stepNo + 2) 3 s2 s3 s6 run3
          (Trace.step (stepNo + 3) 2 s3 s4 s6 run4
            (Trace.step (stepNo + 4) 1 s4 s5 s6 run5
              (Trace.step (stepNo + 5) 0 s5 s6 s6 (by simpa [s6] using run6)
                (Trace.refl (stepNo + 6) s6)))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [s6, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · apply tryStepControlFlowAfterRetired_preserves_register
    · simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using tag5
    · decide
    · decide
  · apply tryStepControlFlowAfterRetired_preserves_register
    · simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using comparison5
    · decide
    · decide
  · exact ⟨Sail.BitVec.addInt r6 1, by
      simp [s6, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  · simp [s1, s2, s3, s4, s5, s6, afterRegisterWrite_mem, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement]
  · exact agree5.trans (wrapperDispatchJumpAfter_agree s5 (BitVec.ofNat 64 0x10410)
      (BitVec.ofNat 64 0x1033c) r6)
  · simpa [s6, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code5
  · simp [s1, s2, s3, s4, s5, s6, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- The tag-two route reaches the shared rejection continuation with `(a0, a1) = (0, 2)`. -/
theorem wrapper_dispatch_tag2_path {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 2)) :
    DispatchPath base stepNo 9 state (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 2) := by
  obtain ⟨r1, r2, r3, r4, r5, run1, run2, run3, run4, run5, pc5, tag5, comparison5⟩ :=
    wrapper_dispatch_non_three_non_one_prefix machine agree retiredPresent code stepNo 2 atPc tag
      (by decide) (by decide)
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  let s2 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10400))
    (BitVec.ofNat 64 0x10404) r2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
  let s4 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10408))
    (BitVec.ofNat 64 0x1040c) r4
  let s5 := afterRegisterWrite s4 (BitVec.ofNat 64 0x1040c) r5 x11 (BitVec.ofNat 64 2)
  have agree1 : Agree platformPreserved base s1 := agree.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have agree2 : Agree platformPreserved base s2 := agree1.trans
    (wrapperDispatchBranchNotTakenAfter_agree s1 (BitVec.ofNat 64 0x10400) r2)
  have agree3 : Agree platformPreserved base s3 := agree2.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have agree4 : Agree platformPreserved base s4 := agree3.trans
    (wrapperDispatchBranchNotTakenAfter_agree s3 (BitVec.ofNat 64 0x10408) r4)
  have agree5 : Agree platformPreserved base s5 := agree4.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired5 : RetiredCounterPresent s5 := ⟨Sail.BitVec.addInt r5 1, by
    simp [s5, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  have code5 : canonicalContractParams.env.CodeIntact s5 := by
    simpa [s1, s2, s3, s4, s5, afterRegisterWrite_mem, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code
  obtain ⟨r6, run6⟩ := wrapper_dispatch_tag2_branch_step machine agree5 retired5 code5
    (stepNo + 5) (by simpa [s1, s2, s3, s4, s5] using pc5)
    (by simpa [s1, s2, s3, s4, s5] using tag5)
    (by simpa [s1, s2, s3, s4, s5] using comparison5)
  let s6 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10410))
    (BitVec.ofNat 64 0x10414) r6
  have agree6 : Agree platformPreserved base s6 := agree5.trans
    (wrapperDispatchBranchNotTakenAfter_agree s5 (BitVec.ofNat 64 0x10410) r6)
  have retired6 : RetiredCounterPresent s6 := ⟨Sail.BitVec.addInt r6 1, by
    simp [s6, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  have code6 : canonicalContractParams.env.CodeIntact s6 := by
    simpa [s6, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code5
  have pc6 : s6.regs.get? PC = some (BitVec.ofNat 64 0x10414) := by
    simp [s6, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r7, run7⟩ := wrapper_dispatch_tag2_clear_result_step machine agree6 retired6 code6
    (stepNo + 6) pc6
  let s7 := afterRegisterWrite s6 (BitVec.ofNat 64 0x10414) r7 x10 (BitVec.ofNat 64 0)
  have agree7 : Agree platformPreserved base s7 := agree6.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired7 := afterRegisterWrite_retired_present s6 (BitVec.ofNat 64 0x10414) r7 x10
    (BitVec.ofNat 64 0)
  have code7 : canonicalContractParams.env.CodeIntact s7 :=
    codeIntact_of_mem_eq
      (afterRegisterWrite_mem s6 (BitVec.ofNat 64 0x10414) r7 x10 (BitVec.ofNat 64 0)) code6
  have pc7 : s7.regs.get? PC = some (BitVec.ofNat 64 0x10418) := by
    simpa [s7] using afterRegisterWrite_pc s6 (BitVec.ofNat 64 0x10414) r7 x10 (BitVec.ofNat 64 0)
  obtain ⟨r8, run8⟩ := wrapper_dispatch_tag2_status_step machine agree7 retired7 code7
    (stepNo + 7) pc7
  let s8 := afterRegisterWrite s7 (BitVec.ofNat 64 0x10418) r8 x11 (BitVec.ofNat 64 2)
  have agree8 : Agree platformPreserved base s8 := agree7.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired8 := afterRegisterWrite_retired_present s7 (BitVec.ofNat 64 0x10418) r8 x11
    (BitVec.ofNat 64 2)
  have code8 : canonicalContractParams.env.CodeIntact s8 :=
    codeIntact_of_mem_eq
      (afterRegisterWrite_mem s7 (BitVec.ofNat 64 0x10418) r8 x11 (BitVec.ofNat 64 2)) code7
  have pc8 : s8.regs.get? PC = some (BitVec.ofNat 64 0x1041c) := by
    simpa [s8] using afterRegisterWrite_pc s7 (BitVec.ofNat 64 0x10418) r8 x11 (BitVec.ofNat 64 2)
  obtain ⟨r9, run9⟩ := wrapper_dispatch_tag2_to_rejection_step machine agree8 retired8 code8
    (stepNo + 8) pc8
  let s9 := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s8)
      (BitVec.ofNat 64 0x1041c) (BitVec.ofNat 64 0x1035c))
    (BitVec.ofNat 64 0x1035c) r9
  refine ⟨⟨s9, Trace.step stepNo 8 state s1 s9 run1
    (Trace.step (stepNo + 1) 7 s1 s2 s9 run2
    (Trace.step (stepNo + 2) 6 s2 s3 s9 run3
    (Trace.step (stepNo + 3) 5 s3 s4 s9 run4
    (Trace.step (stepNo + 4) 4 s4 s5 s9 run5
    (Trace.step (stepNo + 5) 3 s5 s6 s9 (by simpa [s6] using run6)
    (Trace.step (stepNo + 6) 2 s6 s7 s9 (by simpa [s6, s7] using run7)
    (Trace.step (stepNo + 7) 1 s7 s8 s9 (by simpa [s7, s8] using run8)
    (Trace.step (stepNo + 8) 0 s8 s9 s9 (by simpa [s8] using run9)
      (Trace.refl (stepNo + 9) s9))))))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [s9, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · have x10s7 : s7.regs.get? x10 = some (BitVec.ofNat 64 0) := by
      simp [s7, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
    have x10s8 : s8.regs.get? x10 = some (BitVec.ofNat 64 0) := by
      simpa [s8] using (afterRegisterWrite_register s7 (BitVec.ofNat 64 0x10418) r8 x11 x10
        (BitVec.ofNat 64 2) (by decide) (by decide) (by decide) (by decide) (by decide)).trans x10s7
    exact tryStepControlFlowAfterRetired_preserves_register
      (controlFlowJumpState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x1041c)
        (BitVec.ofNat 64 0x1035c)) (BitVec.ofNat 64 0x1035c) r9 x10 (BitVec.ofNat 64 0)
      (by simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using x10s8) (by decide) (by decide)
  · have x11s8 : s8.regs.get? x11 = some (BitVec.ofNat 64 2) := by
      simp [s8, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
    exact tryStepControlFlowAfterRetired_preserves_register
      (controlFlowJumpState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x1041c)
        (BitVec.ofNat 64 0x1035c)) (BitVec.ofNat 64 0x1035c) r9 x11 (BitVec.ofNat 64 2)
      (by simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using x11s8) (by decide) (by decide)
  · exact ⟨Sail.BitVec.addInt r9 1, by
      simp [s9, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, afterRegisterWrite_mem,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement]
  · exact agree8.trans (wrapperDispatchJumpAfter_agree s8 (BitVec.ofNat 64 0x1041c)
      (BitVec.ofNat 64 0x1035c) r9)
  · simpa [s9, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code8
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

end BinaryFv.Zesu.MachineExecution
