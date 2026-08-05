import BinaryFv.Zesu.MachineExecution.Level2Epilogue
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch
import BinaryFv.Zesu.MachineExecution.Level2OutgoingBranchSteps
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.MachineExecution.Level2Capstone
import BinaryFv.Zesu.MachineExecution.Level2WrapperRestoreAddresses

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
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retired : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (pc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc)) :
    ∃ after, WrapperPrefix stepNo 1 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x10400) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 3) ∧
      Agree platformPreserved base after ∧ canonicalContractParams.env.CodeIntact after ∧
      RetiredCounterPresent after ∧ after.mem = state.mem ∧
      after.regs.get? x10 = state.regs.get? x10 ∧ after.regs.get? x2 = state.regs.get? x2 ∧
      after.regs.get? x18 = state.regs.get? x18 := by
  obtain ⟨r, run⟩ := wrapper_dispatch_tag3_constant_step machine agree retired code stepNo pc
  let after := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r x11 (BitVec.ofNat 64 3)
  refine ⟨after, ConfinedPrefix.ownStep' pc (by simpa [after] using run), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [after] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103fc) r x11 (BitVec.ofNat 64 3)
  · exact afterRegisterWrite_destination state (BitVec.ofNat 64 0x103fc) r x11
      (BitVec.ofNat 64 3) (by decide) (by decide)
  · exact agree.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  · simpa [after, afterRegisterWrite_mem] using code
  · exact afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103fc) r x11 (BitVec.ofNat 64 3)
  · rfl
  · exact (afterRegisterWrite_writes state (BitVec.ofNat 64 0x103fc) r x11
      (BitVec.ofNat 64 3)).get x10 (by decide)
  · exact (afterRegisterWrite_writes state (BitVec.ofNat 64 0x103fc) r x11
      (BitVec.ofNat 64 3)).get x2 (by decide)
  · exact (afterRegisterWrite_writes state (BitVec.ofNat 64 0x103fc) r x11
      (BitVec.ofNat 64 3)).get x18 (by decide)

private theorem tag3_miss_agree (state : State) (retired : BitVec 64) :
    Agree platformPreserved state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10400))
        (BitVec.ofNat 64 0x10404) retired) :=
  (fallThroughRetirement_writes state _ _ retired).agree platformPreserved_disjoint

/-- Tag one falls through the tag-three comparison at `0x10400`. -/
theorem wrapper_dispatch_tag1_after_tag3_miss {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retired : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (pc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 1)) :
    ∃ after, WrapperPrefix stepNo 2 state after ∧ after.regs.get? PC = some (BitVec.ofNat 64 0x10404) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 1) ∧ after.regs.get? x2 = state.regs.get? x2 ∧
      after.regs.get? x18 = state.regs.get? x18 ∧ after.mem = state.mem ∧
      Agree platformPreserved base after ∧ canonicalContractParams.env.CodeIntact after ∧
      RetiredCounterPresent after := by
  obtain ⟨s1, p1, pc1, cmp1, ag1, code1, ret1, mem1, tag1, stack1, globals1⟩ :=
    wrapper_dispatch_tag3_constant_confined machine agree retired code stepNo pc
  obtain ⟨r2, run2⟩ := wrapper_dispatch_tag3_miss_step machine ag1 ret1 code1 (stepNo + 1)
    pc1 (tag1.trans tag) cmp1 (by decide)
  let after := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10400))
    (BitVec.ofNat 64 0x10404) r2
  refine ⟨after, p1.trans' 2 (ConfinedPrefix.ownStep' pc1 (by simpa [after] using run2)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tryStepControlFlowAfterRetired_pc _ (BitVec.ofNat 64 0x10404) r2
  · exact ((fallThroughRetirement_writes s1 _ _ r2).get x10 (by decide)).trans (tag1.trans tag)
  · exact ((fallThroughRetirement_writes s1 _ _ r2).get x2 (by decide)).trans stack1
  · exact ((fallThroughRetirement_writes s1 _ _ r2).get x18 (by decide)).trans globals1
  · exact mem1
  · exact ag1.trans (tag3_miss_agree s1 r2)
  · simpa [after, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code1
  · exact tryStepControlFlowAfterRetired_retired_present _ (BitVec.ofNat 64 0x10404) r2

/-- The tag-one comparison constant is written at `0x10404`. -/
theorem wrapper_dispatch_tag1_constant_confined {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retired : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (pc : state.regs.get? PC = some (BitVec.ofNat 64 0x10404))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 1)) :
    ∃ after, WrapperPrefix stepNo 1 state after ∧ after.regs.get? PC = some (BitVec.ofNat 64 0x10408) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 1) ∧ after.regs.get? x11 = some (BitVec.ofNat 64 1) ∧
      after.regs.get? x2 = state.regs.get? x2 ∧ after.regs.get? x18 = state.regs.get? x18 ∧
      after.mem = state.mem ∧ Agree platformPreserved base after ∧
      canonicalContractParams.env.CodeIntact after ∧ RetiredCounterPresent after := by
  obtain ⟨r, run⟩ := wrapper_dispatch_tag1_constant_step machine agree retired code stepNo pc
  let after := afterRegisterWrite state (BitVec.ofNat 64 0x10404) r x11 (BitVec.ofNat 64 1)
  refine ⟨after, ConfinedPrefix.ownStep' pc (by simpa [after] using run),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [after] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10404) r x11 (BitVec.ofNat 64 1)
  · exact ((afterRegisterWrite_writes state (BitVec.ofNat 64 0x10404) r x11
      (BitVec.ofNat 64 1)).get x10 (by decide)).trans tag
  · exact afterRegisterWrite_destination state (BitVec.ofNat 64 0x10404) r x11
      (BitVec.ofNat 64 1) (by decide) (by decide)
  · exact (afterRegisterWrite_writes state (BitVec.ofNat 64 0x10404) r x11
      (BitVec.ofNat 64 1)).get x2 (by decide)
  · exact (afterRegisterWrite_writes state (BitVec.ofNat 64 0x10404) r x11
      (BitVec.ofNat 64 1)).get x18 (by decide)
  · rfl
  · exact agree.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  · simpa [after, afterRegisterWrite_mem] using code
  · exact afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10404) r x11 (BitVec.ofNat 64 1)

private theorem tag1_branch_agree (state : State) (retired : BitVec 64) :
    Agree platformPreserved state (wrapperDispatchTag1BranchAfter state retired) :=
  (jumpRetirement_writes state _ _ retired).agree platformPreserved_disjoint

/-- Tag one takes the checked comparison branch at `0x10408`. -/
theorem wrapper_dispatch_tag1_branch_confined {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retired : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (pc : state.regs.get? PC = some (BitVec.ofNat 64 0x10408))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 1))
    (comparison : state.regs.get? x11 = some (BitVec.ofNat 64 1)) :
    ∃ after, WrapperPrefix stepNo 1 state after ∧ after.regs.get? PC = some (BitVec.ofNat 64 0x10428) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 1) ∧ after.regs.get? x11 = some (BitVec.ofNat 64 1) ∧
      after.regs.get? x2 = state.regs.get? x2 ∧ after.regs.get? x18 = state.regs.get? x18 ∧
      after.mem = state.mem ∧ Agree platformPreserved base after ∧
      canonicalContractParams.env.CodeIntact after ∧ RetiredCounterPresent after := by
  obtain ⟨r, run⟩ := wrapper_dispatch_tag1_branch_step machine agree retired code stepNo pc tag comparison
  let after := wrapperDispatchTag1BranchAfter state r
  refine ⟨after, ConfinedPrefix.ownStep' pc (by simpa [after, wrapperDispatchTag1BranchAfter] using run),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jumpRetirement_pc state _ _ r
  · exact ((jumpRetirement_writes state _ _ r).get x10 (by decide)).trans tag
  · exact ((jumpRetirement_writes state _ _ r).get x11 (by decide)).trans comparison
  · exact (jumpRetirement_writes state _ _ r).get x2 (by decide)
  · exact (jumpRetirement_writes state _ _ r).get x18 (by decide)
  · rfl
  · exact agree.trans (tag1_branch_agree state r)
  · simpa [after, wrapperDispatchTag1BranchAfter] using code
  · exact jumpRetirement_retired_present state _ _ r

/-- The complete tag-one dispatch route owns all seven wrapper instructions through the common
status store. -/
theorem wrapper_dispatch_tag1_confined {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base) (agree : Agree platformPreserved base state)
    (retired : RetiredCounterPresent state) (code : canonicalContractParams.env.CodeIntact state)
    (stepNo : Nat) (pc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 1)) :
    ∃ after, WrapperPrefix stepNo 7 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x1035c) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 0) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 4) ∧
      RetiredCounterPresent after ∧ after.mem = state.mem ∧
      Agree platformPreserved base after ∧ canonicalContractParams.env.CodeIntact after ∧
      after.regs.get? x2 = state.regs.get? x2 ∧
      after.regs.get? x18 = state.regs.get? x18 := by
  obtain ⟨s2, p12, pc2, tag2, stack2, globals2, memory2, agree2, code2, retired2⟩ :=
    wrapper_dispatch_tag1_after_tag3_miss machine agree retired code stepNo pc tag
  obtain ⟨s3, p3, pc3, tag3, comparison3, stack3, globals3, memory3, agree3, code3,
    retired3⟩ :=
    wrapper_dispatch_tag1_constant_confined machine agree2 retired2 code2 (stepNo + 2) pc2 tag2
  obtain ⟨s4, p4, pc4, _tag4, _comparison4, stack4, globals4, memory4, agree4, code4,
    retired4⟩ :=
    wrapper_dispatch_tag1_branch_confined machine agree3 retired3 code3 (stepNo + 3) pc3 tag3
      comparison3
  obtain ⟨after, _trace, tailPrefix, finalPc, result, status, finalRetired, tailMemory,
    finalAgree, finalCode, tailGlobals, tailStack⟩ :=
    wrapper_dispatch_tag1_suffix_frame machine agree4 retired4 code4 (stepNo + 4) pc4
  have complete : WrapperPrefix stepNo 7 state after := by
    confined_steps [p12, p3, p4, tailPrefix]
  exact ⟨after, complete, finalPc, result, status, finalRetired,
    tailMemory.trans (memory4.trans (memory3.trans memory2)), finalAgree, finalCode,
    tailStack.trans (stack4.trans (stack3.trans stack2)),
    tailGlobals.trans (globals4.trans (globals3.trans globals2))⟩

private theorem tag3_branch_agree (state : State) (retired : BitVec 64) :
    Agree platformPreserved state (wrapperDispatchTag3BranchAfter state retired) :=
  (jumpRetirement_writes state _ _ retired).agree platformPreserved_disjoint

private theorem tag3_jump_agree (state : State) (pc target retired : BitVec 64) :
    Agree platformPreserved state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target) target retired) :=
  (jumpRetirement_writes state pc target retired).agree platformPreserved_disjoint

/-- The tag-three dispatch is five wrapper-owned Sail steps from `0x103fc` to the common status
store.  This companion retains the confined ownership evidence and the terminal frame required by
the common status-store/epilogue phase. -/
theorem wrapper_dispatch_tag3_confined {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 3)) :
    ∃ after,
      WrapperPrefix stepNo 5 state after ∧
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
  have tag1 : s1.regs.get? x10 = some (BitVec.ofNat 64 3) :=
    ((afterRegisterWrite_writes state (BitVec.ofNat 64 0x103fc) r1 x11
      (BitVec.ofNat 64 3)).get x10 (by decide)).trans tag
  have comparison1 : s1.regs.get? x11 = some (BitVec.ofNat 64 3) :=
    afterRegisterWrite_destination state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
      (by decide) (by decide)
  obtain ⟨r2, run2, -⟩ := wrapper_dispatch_tag3_branch_step machine agree1 retired1 code1
    (stepNo + 1) pc1 tag1 comparison1
  let s2 := wrapperDispatchTag3BranchAfter s1 r2
  have agree2 : Agree platformPreserved base s2 := agree1.trans (tag3_branch_agree s1 r2)
  have retired2 : RetiredCounterPresent s2 :=
    jumpRetirement_retired_present s1 (BitVec.ofNat 64 0x10400) (BitVec.ofNat 64 0x10434) r2
  have code2 : canonicalContractParams.env.CodeIntact s2 := by simpa [s2, wrapperDispatchTag3BranchAfter] using code1
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10434) :=
    jumpRetirement_pc s1 (BitVec.ofNat 64 0x10400) (BitVec.ofNat 64 0x10434) r2
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
  have p1 : WrapperPrefix stepNo 1 state s1 :=
    ConfinedPrefix.ownStep' atPc (by simpa [s1] using run1)
  have p2 : WrapperPrefix (stepNo + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep' pc1 (by simpa [s1, s2] using run2)
  have p3 : WrapperPrefix (stepNo + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep' pc2 (by simpa [s2, s3] using run3)
  have p4 : WrapperPrefix (stepNo + 3) 1 s3 s4 :=
    ConfinedPrefix.ownStep' pc3 (by simpa [s3, s4] using run4)
  have p5 : WrapperPrefix (stepNo + 4) 1 s4 s5 :=
    ConfinedPrefix.ownStep' pc4 (by simpa [s4, s5] using run5)
  have routeFrame :=
    ((((afterRegisterWrite_writes state (BitVec.ofNat 64 0x103fc) r1 x11
            (BitVec.ofNat 64 3)).trans
          (jumpRetirement_writes s1 (BitVec.ofNat 64 0x10400) (BitVec.ofNat 64 0x10434) r2)).trans
        (afterRegisterWrite_writes s2 (BitVec.ofNat 64 0x10434) r3 x10 (BitVec.ofNat 64 0))).trans
      (afterRegisterWrite_writes s3 (BitVec.ofNat 64 0x10438) r4 x11 (BitVec.ofNat 64 3))).trans
      (jumpRetirement_writes s4 (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c) r5)
  refine ⟨s5, by confined_steps [p1, p2, p3, p4, p5], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jumpRetirement_pc s4 (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c) r5
  · exact (((jumpRetirement_writes s4 (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c) r5).get x10
        (by decide)).trans ((afterRegisterWrite_writes s3 (BitVec.ofNat 64 0x10438) r4 x11
        (BitVec.ofNat 64 3)).get x10 (by decide))).trans
      (afterRegisterWrite_destination s2 (BitVec.ofNat 64 0x10434) r3 x10 (BitVec.ofNat 64 0)
        (by decide) (by decide))
  · exact ((jumpRetirement_writes s4 (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c) r5).get x11
      (by decide)).trans (afterRegisterWrite_destination s3 (BitVec.ofNat 64 0x10438) r4 x11
        (BitVec.ofNat 64 3) (by decide) (by decide))
  · exact agree4.trans (tag3_jump_agree s4 (BitVec.ofNat 64 0x1043c)
      (BitVec.ofNat 64 0x1035c) r5)
  · simpa [s5, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code4
  · exact jumpRetirement_retired_present s4 (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c) r5
  · rfl
  · exact routeFrame.get x18 (by decide)
  · exact routeFrame.get x2 (by decide)

/-- Lossless Level 2 handoff from a propagated non-`invalidSsz` decoder error to result dispatch. -/
structure PropagatedErrorEdgeResult (args : DecodeInlineArgs) (error : Contracts.DecodeError)
    (fromStep used : Nat) (before after dispatch : State) (link s0 s1 s2 : BitVec 64) : Prop where
  bound : used ≤ decodeInlineStepBound args
  child : level3DecodeChildSummary
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
    fromStep used before after
  childTrace : ScopedTrace
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
    (DecodeInlineExit args) Level3ChildSummary fromStep used before after
  post : DecodeInlinePost args before after
  machine : DecodeInlineMachinePost before after
  outgoing : DecodeInlineOutgoingFrame args after
  branch : Runs (try_step (fromStep + used) false) after dispatch false
  branchPrefix : WrapperPrefix (fromStep + used) 1 after dispatch
  dispatchTag : dispatch.regs.get? x10 =
    some (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))
  dispatchStatus : dispatch.regs.get? x11 = some (BitVec.ofNat 64 2)
  dispatchPc : dispatch.regs.get? PC = some (BitVec.ofNat 64 0x103fc)
  dispatchPlatform : Agree platformPreserved before dispatch
  dispatchDecoder : Agree decoderPreserved before dispatch
  dispatchCode : canonicalContractParams.env.CodeIntact dispatch
  dispatchRetired : RetiredCounterPresent dispatch
  dispatchMemory : dispatch.mem = before.mem
  dispatchStack : dispatch.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)
  dispatchGlobals : dispatch.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  frame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 dispatch

theorem propagated_error_edge (fromStep : Nat) (args : DecodeInlineArgs) (before : State)
    (pre : DecodeInlinePre args before) (error : Contracts.DecodeError)
    (phase : args.phase = .propagateError error) (link s0 s1 s2 : BitVec 64)
    (saved : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 before) :
    ∃ used after retired, PropagatedErrorEdgeResult args error fromStep used before after
      (decodeInlinePropagateErrorBranchAfter after retired) link s0 s1 s2 := by
  obtain ⟨used, after, bound, childTrace, post, machine, outgoing⟩ :=
    decodeInline_propagate_error_reaches_post fromStep args before pre error phase
  have child : level3DecodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      fromStep used before after := ⟨rfl, args, pre, bound, childTrace, post, machine, outgoing⟩
  have identity : after = before := by
    simp [DecodeInlinePost, phase] at post
    exact post.2.2.2.2
  subst after
  obtain ⟨retired, branch, dispatchPc⟩ :=
    decodeInline_propagate_error_branch_step (fromStep + used) args before pre error phase
  have atPc : before.regs.get? PC = some (BitVec.ofNat 64 0x10380) := by
    simp [DecodeInlinePost, phase] at post
    exact post.2.2.2
  have branchPrefix : WrapperPrefix (fromStep + used) 1 before
        (decodeInlinePropagateErrorBranchAfter before retired) :=
    ConfinedPrefix.ownStep' atPc branch
  have branchWrites : WritesOnlyRegs stepBookkeeping before
      (decodeInlinePropagateErrorBranchAfter before retired) :=
    jumpRetirement_writes before (BitVec.ofNat 64 0x10380) (BitVec.ofNat 64 0x103fc) retired
  have dispatchPlatform : Agree platformPreserved before
      (decodeInlinePropagateErrorBranchAfter before retired) :=
    branchWrites.agree platformPreserved_disjoint
  have dispatchDecoder : Agree decoderPreserved before
      (decodeInlinePropagateErrorBranchAfter before retired) :=
    Agree.weaken (fun _ preserved => preserved.2) dispatchPlatform
  have dispatchCode : canonicalContractParams.env.CodeIntact
      (decodeInlinePropagateErrorBranchAfter before retired) := by
    simpa [decodeInlinePropagateErrorBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement] using machine.code
  have dispatchRetired : RetiredCounterPresent
      (decodeInlinePropagateErrorBranchAfter before retired) :=
    jumpRetirement_retired_present before (BitVec.ofNat 64 0x10380) (BitVec.ofNat 64 0x103fc) retired
  have dispatchStack : (decodeInlinePropagateErrorBranchAfter before retired).regs.get? x2 =
      some (BitVec.ofNat 64 args.stackBase) :=
    (branchWrites.get x2 (by decide)).trans pre.stackValue
  have dispatchGlobals : (decodeInlinePropagateErrorBranchAfter before retired).regs.get? x18 =
      some (BitVec.ofNat 64 0x4215020) :=
    (branchWrites.get x18 (by decide)).trans pre.globalsValue
  have dispatchTag : (decodeInlinePropagateErrorBranchAfter before retired).regs.get? x10 =
      some (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))) := by
    obtain ⟨-, -, tagA0, -⟩ := pre.propagateReason error phase
    exact (branchWrites.get x10 (by decide)).trans tagA0
  have dispatchStatus : (decodeInlinePropagateErrorBranchAfter before retired).regs.get? x11 =
      some (BitVec.ofNat 64 2) := by
    obtain ⟨-, -, -, tagA1⟩ := pre.propagateReason error phase
    exact (branchWrites.get x11 (by decide)).trans tagA1
  exact ⟨used, before, retired, bound, child, childTrace, post, machine, outgoing, branch,
    branchPrefix, dispatchTag, dispatchStatus, dispatchPc, dispatchPlatform, dispatchDecoder,
    dispatchCode, dispatchRetired, rfl, dispatchStack, dispatchGlobals,
    WrapperSavedRegisterFrame.of_mem_eq saved (by rfl)⟩

/-- A non-retry decoder error reaches the generated wrapper exit after its selected dispatch route. -/
structure PropagatedErrorToExitResult (args : DecodeInlineArgs) (error : Contracts.DecodeError)
    (fromStep used : Nat) (entry base before childAfter dispatch routeAfter afterStore after : State)
    (link s0 s1 s2 : BitVec 64) : Prop where
  edge : PropagatedErrorEdgeResult args error fromStep used before childAfter dispatch link s0 s1 s2
  route : WrapperOwnedTerminalRouteFrame base dispatch routeAfter (fromStep + used + 1)
    (if error = .outOfMemory then 7 else 5) (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 (Contracts.statusOfResult (.error error)).code)
  store : Runs (try_step (fromStep + used + 1 + (if error = .outOfMemory then 7 else 5)) false)
    routeAfter afterStore false
  epilogue : WrapperEpilogueExitResult
    (fromStep + used + 1 + (if error = .outOfMemory then 7 else 5) + 1) base afterStore after
    link s0 s1 s2 (BitVec.ofNat 64 (args.stackBase + 0xa20)) (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 (Contracts.statusOfResult (.error error)).code)
  trace : Trace (fromStep + used) (1 + (if error = .outOfMemory then 7 else 5) + 7) childAfter after
  confined : ConfinedPrefix
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary (fromStep + used) (1 + (if error = .outOfMemory then 7 else 5) + 7)
    childAfter after
  scopedTrace : ScopedTrace
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary fromStep (used + 1 + (if error = .outOfMemory then 7 else 5) + 7) before after
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  a0 : after.regs.get? x10 = some (BitVec.ofNat 64 0)
  a1 : after.regs.get? x11 = some (BitVec.ofNat 64 (Contracts.statusOfResult (.error error)).code)
  sp : after.regs.get? x2 = some (BitVec.ofNat 64 (args.stackBase + 0xa20))
  globals : after.regs.get? x18 = some s2
  savedFrame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 routeAfter
  memory : after.mem = afterStore.mem
  code : canonicalContractParams.env.CodeIntact after
  retired : RetiredCounterPresent after

private theorem propagated_error_to_exit_of_route
    {args : DecodeInlineArgs} {error : Contracts.DecodeError} {fromStep used : Nat}
    {entry before childAfter dispatch : State} {link s0 s1 s2 : BitVec 64}
    (machineEntry : ZesuDecodeRawMachinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry)
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      args.machineArgs before)
    (edge : PropagatedErrorEdgeResult args error fromStep used before childAfter dispatch link s0 s1 s2)
    (routeSteps : Nat) (status : BitVec 64)
    (route : WrapperOwnedTerminalRouteFrame before dispatch routeAfter (fromStep + used + 1) routeSteps
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) status)
    (statusEq : status = BitVec.ofNat 64 (Contracts.statusOfResult (.error error)).code)
    (stepsEq : routeSteps = if error = .outOfMemory then 7 else 5) :
    ∃ afterStore after,
      PropagatedErrorToExitResult args error fromStep used entry before before childAfter dispatch routeAfter
        afterStore after link s0 s1 s2 := by
  have stackNat : (BitVec.ofNat 64 args.stackBase).toNat = args.stackBase := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have fits := machineEntry.stackFrameFits
    omega
  have routeStack : routeAfter.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    exact route.route.savedStack.trans edge.dispatchStack
  have routeGlobals : routeAfter.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    exact route.route.savedS2.trans edge.dispatchGlobals
  have routeFrame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 routeAfter :=
    WrapperSavedRegisterFrame.of_mem_eq edge.frame route.route.memory
  let restore := wrapperRestoreAddresses_of_machinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry machineEntry
  obtain ⟨afterStore, after, store, trace, epilogue⟩ :=
    wrapper_dispatch_route_through_exit machine (fromStep + used + 1) routeSteps (BitVec.ofNat 64 0)
      status link s0 s1 s2 (BitVec.ofNat 64 args.stackBase) (BitVec.ofNat 64 (args.stackBase + 0xa20))
      route.route.terminal (by simpa [stackNat] using routeFrame)
      (by simpa [stackNat] using machineEntry.stackAvoidsStatusGlobals) routeGlobals routeStack
      restore.raAddress restore.s0Address restore.s1Address restore.s2Address restore.raAddressEq
      restore.s0AddressEq restore.s1AddressEq restore.s2AddressEq restore.raAddressNat restore.s0AddressNat
      restore.s1AddressNat restore.s2AddressNat restore.raAligned restore.s0Aligned restore.s1Aligned
      restore.s2Aligned restore.raAllowed restore.s0Allowed restore.s1Allowed restore.s2Allowed
      (by simpa using wrapper_final_stack_address args.stackBase)
  have storeConfined : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + used + 1 + routeSteps) 1 routeAfter afterStore :=
    ConfinedPrefix.ownStep route.route.atTerminal (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr; apply RegionPcs.iff_inRanges.mpr; native_decide)
      (by simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) store
  have finalExit : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + used + 1 + routeSteps + 7) 0 after after :=
    ScopedTrace.exitAt _ after (BitVec.ofNat 64 0x10378) epilogue.pc (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw])
  have epilogueScoped := epilogue.confined 0 after (by simpa [Nat.add_assoc] using finalExit)
  have suffixScoped := storeConfined 6 after (by simpa [Nat.add_assoc] using epilogueScoped)
  have routeScoped := route.confined 7 after (by simpa [Nat.add_assoc] using suffixScoped)
  have branchScoped := edge.branchPrefix (routeSteps + 7) after (by simpa [Nat.add_assoc] using routeScoped)
  have fullScoped := ScopedTrace.childBody fromStep used (1 + routeSteps + 7)
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id before childAfter after
    (Level2ChildSummary.decode edge.child) (by simpa [Nat.add_assoc] using branchScoped)
  have suffixConfined := ConfinedPrefix.trans storeConfined epilogue.confined
  have routeConfined := ConfinedPrefix.trans route.confined (by simpa [Nat.add_assoc] using suffixConfined)
  have allConfined := ConfinedPrefix.trans edge.branchPrefix (by simpa [Nat.add_assoc] using routeConfined)
  refine ⟨afterStore, after, ?_⟩
  subst status
  subst routeSteps
  exact ⟨edge, route, store, epilogue,
    by simpa [Nat.add_assoc] using Trace.append (Trace.one (fromStep + used) childAfter dispatch edge.branch) trace,
    by simpa [Nat.add_assoc] using allConfined, by simpa [Nat.add_assoc] using fullScoped,
    epilogue.pc, epilogue.a0, epilogue.a1, epilogue.sp, epilogue.s2, routeFrame,
    epilogue.memory, epilogue.code, epilogue.retired⟩

/-- Compose a propagated non-`invalidSsz` error through its real wrapper branch and selected route. -/
theorem propagated_error_to_exit
    {args : DecodeInlineArgs} {fromStep : Nat} {entry before : State}
    (machineEntry : ZesuDecodeRawMachinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry)
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      args.machineArgs before)
    (pre : DecodeInlinePre args before) (error : Contracts.DecodeError)
    (phase : args.phase = .propagateError error) (link s0 s1 s2 : BitVec 64)
    (saved : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 before) :
    ∃ used childAfter dispatch routeAfter afterStore after,
      PropagatedErrorToExitResult args error fromStep used entry before before childAfter dispatch routeAfter
        afterStore after link s0 s1 s2 := by
  obtain ⟨used, childAfter, retired, edge⟩ := propagated_error_edge fromStep args before pre error phase link s0 s1 s2 saved
  obtain ⟨notInvalid, -, -, -⟩ := pre.propagateReason error phase
  cases error with
  | invalidSsz => exact False.elim (notInvalid rfl)
  | unknownFork =>
    obtain ⟨routeAfter, route⟩ := wrapper_dispatch_tag3_owned_terminal_route machine edge.dispatchPlatform
      edge.dispatchRetired edge.dispatchCode (fromStep + used + 1) edge.dispatchPc (by simpa using edge.dispatchTag)
    obtain ⟨afterStore, after, result⟩ := propagated_error_to_exit_of_route machineEntry machine edge 5
      (BitVec.ofNat 64 3) route (by decide) (by decide)
    exact ⟨used, childAfter, decodeInlinePropagateErrorBranchAfter childAfter retired, routeAfter, afterStore, after, result⟩
  | outOfMemory =>
    obtain ⟨routeAfter, route⟩ := wrapper_dispatch_tag1_owned_terminal_route machine edge.dispatchPlatform
      edge.dispatchRetired edge.dispatchCode (fromStep + used + 1) edge.dispatchPc (by simpa using edge.dispatchTag)
    obtain ⟨afterStore, after, result⟩ := propagated_error_to_exit_of_route machineEntry machine edge 7
      (BitVec.ofNat 64 4) route (by decide) (by decide)
    exact ⟨used, childAfter, decodeInlinePropagateErrorBranchAfter childAfter retired, routeAfter, afterStore, after, result⟩

end BinaryFv.Zesu.MachineExecution
