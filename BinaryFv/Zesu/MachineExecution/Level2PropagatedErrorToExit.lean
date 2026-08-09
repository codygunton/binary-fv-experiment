import BinaryFv.Zesu.MachineExecution.Level2Epilogue
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryFinish
import BinaryFv.Zesu.MachineExecution.Level2OutgoingBranchSteps
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.MachineExecution.Level2Capstone
import BinaryFv.Zesu.MachineExecution.Level2WrapperRestoreAddresses
import BinaryFv.Zesu.MachineExecution.OwnedPc
import BinaryFv.Zesu.MachineExecution.Level2SecondEntryProof

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
  obtain ⟨after, route⟩ :=
    wrapper_dispatch_tag3_owned_terminal_route machine agree retiredPresent code stepNo atPc tag
  exact ⟨after, route.confined, route.route.atTerminal, route.route.resultValue,
    route.route.statusValue, route.route.platform, route.route.code, route.route.retired,
    route.route.memory, route.route.savedS2, route.route.savedStack⟩

/-- Lossless Level 2 handoff from a propagated non-`invalidSsz` decoder error to result dispatch. -/
structure PropagatedErrorEdgeResult (args : DecodeInlineArgs) (error : Contracts.DecodeError)
    (fromStep used : Nat) (before after dispatch : State) (link s0 s1 s2 : BitVec 64) : Prop where
  bound : used ≤ decodeInlineStepBound args
  usedZero : used = 0
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
  obtain ⟨used, after, bound, childTrace, post, machine, outgoing, usedZero⟩ :=
    decodeInline_propagate_error_reaches_post fromStep args before pre error phase
  have child : level3DecodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      fromStep used before after := ⟨rfl, args, pre, bound, childTrace,
        childTrace.toFunctionTrace (level3ChildSummary_composes_decode args), post, machine, outgoing⟩
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
  exact ⟨used, before, retired, bound, usedZero, child, childTrace, post, machine, outgoing, branch,
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
  statusWord : Word32LERep after Elflings.canonicalDecoderGlobalsLayout.status
    (Contracts.statusOfResult (.error error)).code
  globalsFrame : DecoderGlobalsBoundaryFrame routeAfter after
  exitGlobals : WrapperExitGlobals routeAfter after
    (BitVec.ofNat 64 (Contracts.statusOfResult (.error error)).code)
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
  obtain ⟨afterStore, after, store, trace, epilogue, exitGlobals⟩ :=
    wrapper_dispatch_route_through_exit_with_globals machine (fromStep + used + 1) routeSteps (BitVec.ofNat 64 0)
      status link s0 s1 s2 (BitVec.ofNat 64 args.stackBase) (BitVec.ofNat 64 (args.stackBase + 0xa20))
      route.route.terminal (by simpa [stackNat] using routeFrame)
      (by simpa [stackNat] using machineEntry.stackAvoidsStatusGlobals) routeGlobals routeStack
      restore.raAddress restore.s0Address restore.s1Address restore.s2Address restore.raAddressEq
      restore.s0AddressEq restore.s1AddressEq restore.s2AddressEq restore.facts.raAddressNat restore.facts.s0AddressNat
      restore.facts.s1AddressNat restore.facts.s2AddressNat restore.facts.raAligned restore.facts.s0Aligned restore.facts.s1Aligned
      restore.facts.s2Aligned restore.facts.raAllowed restore.facts.s0Allowed restore.facts.s1Allowed restore.facts.s2Allowed
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
    epilogue.memory, by
      cases error <;>
        simpa [Contracts.statusOfResult, Contracts.DecodeStatus.code, BitVec.toNat_ofNat] using
          exitGlobals.statusWord,
    exitGlobals.boundaryFrame, exitGlobals, epilogue.code, epilogue.retired⟩

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

/-- The complete exported-entry route for a first `unknownFork` or `outOfMemory` result. The
second `decode` entry is the source-selected zero-step propagation exit; all wrapper dispatch and
exit instructions remain in the route's `ScopedTrace`. -/
structure FirstPropagatedErrorToExitResult (args : ZesuDecodeRawArgs) (stackBase fromStep : Nat)
    (entry atDecode firstAfter branch retryBefore childAfter dispatch routeAfter afterStore after : State)
    (firstUsed propagatedUsed : Nat) (error : Contracts.DecodeError)
    (branchRetired retryRetired link s0 s1 s2 : BitVec 64) : Prop where
  rawResult : meaningDecodeRaw args.bytes = .error error
  semanticResult : meaningDecode args.bytes = .error error
  firstBound : firstUsed ≤ 2 * (16384 + 512 * args.bytes.size)
  propagatedZero : propagatedUsed = 0
  propagated : PropagatedErrorToExitResult
    { phase := .propagateError error, stackBase := stackBase, inputBase := args.inputBase,
      bytes := args.bytes }
    error (fromStep + 19 + firstUsed + 2) propagatedUsed entry retryBefore retryBefore childAfter
    dispatch routeAfter afterStore after link s0 s1 s2
  scopedTrace : WrapperScopedTrace fromStep
    (19 + firstUsed + 2 + (propagatedUsed + 1 +
      (if error = .outOfMemory then 7 else 5) + 7)) entry after
  exitPc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  exitResult : after.regs.get? x10 = some (BitVec.ofNat 64 0)
  exitStatus : after.regs.get? x11 = some
    (BitVec.ofNat 64 (Contracts.statusOfResult (.error error)).code)
  inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes
  code : canonicalContractParams.env.CodeIntact after
  platform : Agree platformPreserved entry after
  retired : RetiredCounterPresent after
  attempted : FlagRep after Elflings.canonicalDecoderGlobalsLayout.attempted true
  statusWord : Word32LERep after Elflings.canonicalDecoderGlobalsLayout.status
    (Contracts.statusOfResult (.error error)).code
  storedTag : DecodedValue.OptionTagRep after
    (Elflings.canonicalDecoderGlobalsLayout.storedResult +
      Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) false

theorem first_propagated_error_to_exit
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    (fromStep : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (error : Contracts.DecodeError) (notInvalid : error ≠ .invalidSsz)
    (rawResult : meaningDecodeRaw args.bytes = .error error) :
    ∃ atDecode firstAfter branch retryBefore childAfter dispatch routeAfter afterStore after
      firstUsed propagatedUsed branchRetired retryRetired link s0 s1 s2,
      FirstPropagatedErrorToExitResult args stackBase fromStep entry atDecode firstAfter branch retryBefore
        childAfter dispatch routeAfter afterStore after firstUsed propagatedUsed error branchRetired
        retryRetired link s0 s1 s2 := by
  obtain ⟨atDecode, wrapperTrace, wrapperPrefix, firstArgs, firstArgsEq, firstPre, entryAgree,
    attemptedAtDecode, storedAtDecode, firstUsed, firstAfter, firstChild, firstLevel3, firstBound, firstSuccessBound,
    firstTrace, firstFlat, firstPost, firstMachine, firstOutgoing, firstSaveArea, firstAllocation,
    firstError, firstGlobals, savedFrame⟩ :=
    wrapper_reaches_decode_first_contract allocator decode fromStep args stackBase entry source machine
  have firstPhase : firstArgs.phase = .first := by simp [firstArgsEq]
  have rawResult' : meaningDecodeRaw firstArgs.bytes = .error error := by
    simpa [firstArgsEq] using rawResult
  obtain ⟨firstInputValue, firstLengthValue⟩ := firstError firstPhase error rawResult'
  have firstDetails := firstPost
  simp only [DecodeInlinePost, firstPhase, DecodeInlineFirstPost] at firstDetails
  rw [rawResult'] at firstDetails
  have firstExit : firstAfter.regs.get? PC = some (BitVec.ofNat 64 0x10324) :=
    firstDetails.2.2.1
  have firstTag : firstAfter.regs.get? x10 = some
      (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))) := by
    simpa [Contracts.decodeInternalResultTag] using firstDetails.2.2.2
  have firstStack : firstAfter.regs.get? x2 = some (BitVec.ofNat 64 firstArgs.stackBase) := by
    simpa [DecodeInlineOutgoingFrame, firstPhase] using firstOutgoing
  have firstInput : DecodedValue.MemoryBytes firstAfter firstArgs.inputBase firstArgs.bytes := by
    simpa [DecodeInlineArgs.firstRawArgs] using firstDetails.1.1
  have firstWrapperMachine : DecoderMachinePre decodeRawExecutionPcs firstArgs.machineArgs atDecode := by
    simpa [firstArgsEq, DecodeInlineArgs.machineArgs, zesuDecodeRawMachineArgs] using
      machine.machine.mono entryAgree firstPre.machine.retiredCounter
  obtain ⟨branchRetired, transfer⟩ := wrapper_decode_first_error_inlineTransfer
    (fromStep + 19) firstUsed firstArgs atDecode firstAfter firstPre firstLevel3 firstMachine error
    firstPhase firstExit firstTag
  let branch := wrapperAfterDecodeFirstErrorBranch firstAfter branchRetired
  have branchPc : branch.regs.get? PC = some (BitVec.ofNat 64 0x1037c) := by
    simpa [branch, wrapperAfterDecodeFirstErrorBranch] using
      tryStepControlFlowAfterRetired_pc
        (controlFlowJumpState (tryStepControlFlowAfterIncrement firstAfter)
          (BitVec.ofNat 64 0x10324) (BitVec.ofNat 64 0x1037c))
        (BitVec.ofNat 64 0x1037c) branchRetired
  have branchWrites : WritesOnlyRegs stepBookkeeping firstAfter branch := by
    simpa [branch] using wrapperAfterDecodeFirstErrorBranch_writes firstAfter branchRetired
  have branchStack : branch.regs.get? x2 = some (BitVec.ofNat 64 firstArgs.stackBase) :=
    (branchWrites.get x2 (by decide)).trans firstStack
  have branchInput : branch.regs.get? x8 = some (BitVec.ofNat 64 firstArgs.inputBase) := by
    exact (branchWrites.get x8 (by decide)).trans firstInputValue
  have branchLength : branch.regs.get? x9 = some (BitVec.ofNat 64 firstArgs.bytes.size) := by
    exact (branchWrites.get x9 (by decide)).trans firstLengthValue
  have branchGlobals : branch.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    have outgoingGlobals : firstAfter.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
      firstMachine.globalsValue.trans firstPre.globalsValue
    exact (branchWrites.get x18 (by decide)).trans outgoingGlobals
  have branchInputMemory : DecodedValue.MemoryBytes branch firstArgs.inputBase firstArgs.bytes := by
    intro index bound
    rw [wrapperAfterDecodeFirstErrorBranch_mem firstAfter branchRetired]
    exact firstInput index bound
  have branchCode : canonicalContractParams.env.CodeIntact branch := by
    simpa [branch, wrapperAfterDecodeFirstErrorBranch, afterRegisterWrite_mem] using firstMachine.code
  have branchAgree : Agree decoderPreserved atDecode branch :=
    firstMachine.agree.trans (wrapperAfterDecodeFirstErrorBranch_agree firstAfter branchRetired)
  have branchMachine : DecoderMachinePre decodeRawExecutionPcs firstArgs.machineArgs branch :=
    firstWrapperMachine.mono branchAgree
      (wrapperAfterDecodeFirstErrorBranch_retired firstAfter branchRetired)
  have branchTag : branch.regs.get? x10 = some
      (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))) :=
    (branchWrites.get x10 (by decide)).trans firstTag
  rcases savedFrame with ⟨link, s0, s1, s2, entryLink, s0AtEntry, s1AtEntry, s2AtEntry,
    savedAtDecode⟩
  have savedAtFirst : WrapperSavedRegisterFrame stackBase link s0 s1 s2 firstAfter := by
    have savedAtDecode' : WrapperSavedRegisterFrame firstArgs.stackBase link s0 s1 s2 atDecode := by
      simpa [firstArgsEq] using savedAtDecode
    simpa [firstArgsEq] using
      WrapperSavedRegisterFrame.of_decode_inline_caller_save_area savedAtDecode' firstSaveArea
  have savedAtBranch : WrapperSavedRegisterFrame stackBase link s0 s1 s2 branch :=
    WrapperSavedRegisterFrame.of_mem_eq savedAtFirst (wrapperAfterDecodeFirstErrorBranch_mem _ _)
  obtain ⟨retryRetired, secondArgs, propagatedUsed, childAfter, secondArgsEq, retryRun, secondPre,
    secondChild⟩ := wrapper_second_propagate_decode_entry decode (fromStep + 19 + firstUsed + 1)
      firstArgs branch branchMachine branchPc branchStack branchInput branchLength branchGlobals
      branchInputMemory branchCode firstPre.inputFits firstPre.rootInputBound firstPre.stackAligned
      firstPre.stackObjectsFit firstPre.stackObjectsReadable firstPre.inputAvoidsCanonicalStack
      firstPre.stackFrameWritable firstPre.rawFrameWritable firstPre.rawPrologueFrameWritable
      firstPre.nestedCallFrameWritable firstPre.nestedCallFrameFits
      error notInvalid rawResult' branchTag
  have secondPhase : secondArgs.phase = .propagateError error := by simp [secondArgsEq]
  let retryBefore := afterRegisterWrite branch (BitVec.ofNat 64 0x1037c) retryRetired x11
    (BitVec.ofNat 64 2)
  have retryMachine : DecoderMachinePre decodeRawExecutionPcs secondArgs.machineArgs retryBefore := by
    have writes := afterRegisterWrite_writes branch (BitVec.ofNat 64 0x1037c) retryRetired x11
      (BitVec.ofNat 64 2)
    simpa [secondArgsEq, firstArgsEq, retryBefore] using branchMachine.mono
      (afterRegisterWrite_agree_of
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved]))
      (afterRegisterWrite_retired_present branch (BitVec.ofNat 64 0x1037c) retryRetired x11
        (BitVec.ofNat 64 2))
  have savedAtRetry : WrapperSavedRegisterFrame secondArgs.stackBase link s0 s1 s2 retryBefore := by
    simpa [secondArgsEq, firstArgsEq, retryBefore] using
      WrapperSavedRegisterFrame.of_mem_eq savedAtBranch (by rfl)
  obtain ⟨propagatedUsed, childAfter, dispatch, routeAfter, afterStore, after, propagated⟩ :=
    propagated_error_to_exit (entry := entry) (before := retryBefore)
      (by simpa [secondArgsEq, firstArgsEq] using machine) retryMachine secondPre error secondPhase link s0 s1 s2
      savedAtRetry
  have scopedTrace : WrapperScopedTrace fromStep
      (19 + firstUsed + 2 + (propagatedUsed + 1 +
        (if error = .outOfMemory then 7 else 5) + 7)) entry after := by
    rcases transfer with ⟨firstTransfer⟩
    have resumePc : firstTransfer.resumePc = BitVec.ofNat 64 0x1037c := by
      apply Option.some.inj
      exact firstTransfer.atResume.symm.trans branchPc
    have firstTailPrefix : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (fromStep + 19) (firstUsed + 2) atDecode retryBefore := by
      intro tailUsed after tail
      have retryPrefix : WrapperPrefix (fromStep + 19 + firstUsed + 1) 1 branch retryBefore :=
        ConfinedPrefix.ownStep' firstTransfer.atResume
          (by simpa [branch, retryBefore] using retryRun)
          (by rw [resumePc]; owned_pc) (by rw [resumePc]; owned_pc)
      have retryTailRaw : ScopedTrace decodeRawExecutionPcs decodeRawExit Level2ChildSummary
          (fromStep + 19 + firstUsed + 1) (1 + tailUsed) branch after := by
        simpa [decodeRawExecutionPcs, decodeRawExit] using retryPrefix tailUsed after tail
      have firstExitTailRaw : ScopedTrace decodeRawExecutionPcs decodeRawExit Level2ChildSummary
          (fromStep + 19 + firstUsed) (1 + (1 + tailUsed)) firstTransfer.sExit after := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          ScopedTrace.ownStep (fromStep + 19 + firstUsed) (1 + tailUsed)
            firstTransfer.childExitPc firstTransfer.sExit branch after firstTransfer.atExit
            firstTransfer.exitInRegion firstTransfer.exitNotExit firstTransfer.doExit retryTailRaw
      simpa [decodeRawExecutionPcs, decodeRawExit, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ScopedTrace.childBody (fromStep + 19) firstUsed (1 + (1 + tailUsed))
          functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
          atDecode firstTransfer.sExit after firstTransfer.body firstExitTailRaw
    have routePrefix : WrapperPrefix fromStep (19 + firstUsed + 2) entry retryBefore :=
      ConfinedPrefix.trans' (19 + firstUsed + 2) wrapperPrefix firstTailPrefix
    exact routePrefix _ after (by simpa [Nat.add_assoc] using propagated.scopedTrace)
  have inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes := by
    have inputAtFirst : DecodedValue.MemoryBytes firstAfter args.inputBase args.bytes := by
      simpa [firstArgsEq] using firstInput
    intro index indexBound
    rw [propagated.exitGlobals.memoryOutsideStatus (args.inputBase + index) (by
      rcases machine.inputAvoidsDecoderGlobals with inputBefore | globalsBefore
      · left
        have statusInGlobals : Elflings.GeneratedDecoderGlobals.bssBase ≤ 0x4215024 := by native_decide
        omega
      · right
        have statusEndInGlobals : 0x4215028 ≤ Elflings.GeneratedDecoderGlobals.bssBase +
            Elflings.GeneratedDecoderGlobals.bssSize := by native_decide
        omega)]
    rw [propagated.route.route.memory, propagated.edge.dispatchMemory]
    simpa [retryBefore, branch, afterRegisterWrite_mem,
      wrapperAfterDecodeFirstErrorBranch] using inputAtFirst index indexBound
  have decoderAgree : Agree decoderPreserved entry after := by
    have retryAgree : Agree decoderPreserved entry retryBefore :=
      entryAgree.trans firstMachine.agree |>.trans
        (wrapperAfterDecodeFirstErrorBranch_agree firstAfter branchRetired) |>.trans
        (afterRegisterWrite_agree_of
          (by simp [decoderPreserved, platformPreserved])
          (by simp [decoderPreserved, platformPreserved])
          (by simp [decoderPreserved, platformPreserved])
          (by simp [decoderPreserved, platformPreserved])
          (by simp [decoderPreserved, platformPreserved]))
    exact retryAgree.trans propagated.epilogue.agree
  have platform : Agree platformPreserved entry after := by
    intro register preserved
    rcases preserved with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact propagated.epilogue.ra.trans entryLink.symm
    all_goals exact decoderAgree _ ⟨by decide, by simp [platformPreserved]⟩
  have attempted : FlagRep after Elflings.canonicalDecoderGlobalsLayout.attempted true := by
    unfold FlagRep
    rw [propagated.exitGlobals.boundaryFrame.1, propagated.route.route.memory,
      propagated.edge.dispatchMemory]
    simpa [retryBefore, branch, afterRegisterWrite_mem, wrapperAfterDecodeFirstErrorBranch] using
      firstGlobals.1.trans attemptedAtDecode
  have storedTag : DecodedValue.OptionTagRep after
      (Elflings.canonicalDecoderGlobalsLayout.storedResult +
        Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) false := by
    unfold DecodedValue.OptionTagRep
    rw [propagated.exitGlobals.boundaryFrame.2, propagated.route.route.memory,
      propagated.edge.dispatchMemory]
    simpa [retryBefore, branch, afterRegisterWrite_mem, wrapperAfterDecodeFirstErrorBranch] using
      firstGlobals.2.trans (storedAtDecode.trans source.2.2.2.2.2.1)
  have semanticResult : meaningDecode args.bytes = .error error := by
    simp [Contracts.meaningDecode, rawResult]
  refine ⟨atDecode, firstAfter, branch, retryBefore, childAfter, dispatch, routeAfter,
    afterStore, after, firstUsed, propagatedUsed, branchRetired, retryRetired, link, s0, s1, s2, ?_⟩
  exact ⟨rawResult, semanticResult, by simpa [firstArgsEq] using firstBound,
    propagated.edge.usedZero, by simpa [secondArgsEq, firstArgsEq, Nat.add_assoc] using propagated,
    scopedTrace, propagated.pc, propagated.a0, propagated.a1, inputMemory, propagated.code, platform,
    propagated.retired, attempted, propagated.statusWord, storedTag⟩

end BinaryFv.Zesu.MachineExecution
