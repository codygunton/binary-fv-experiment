import BinaryFv.Zesu.MachineExecution.Level2RetryExactHandoff
import BinaryFv.Zesu.MachineExecution.Level2FirstInvalidRetryEntry
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch
import BinaryFv.Zesu.MachineExecution.Level2Tag0CopyToExit
import BinaryFv.Zesu.MachineExecution.Level2WrapperRestoreAddresses
import BinaryFv.Zesu.MachineExecution.Level2Capstone
import BinaryFv.Zesu.MachineExecution.OwnedPc

/-!
# Exact-prefix retry routes

The exact-prefix retry reads its real result tag at `0x103f8` and dispatches at `0x103fc`.
This module handles nonzero tags through the generated status-store and epilogue exit, and tag zero
through the real stored-result copy beginning at `0x1033c`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

/-- The exact retry's nonzero internal tag selects one of the three rejection routes. -/
def retryExactErrorRouteSteps : Contracts.DecodeError → Nat
  | .outOfMemory => 7
  | .invalidSsz => 9
  | .unknownFork => 5

/-- The wrapper status selected after the exact retry's internal result tag. -/
def retryExactErrorStatus (error : Contracts.DecodeError) : Nat :=
  (statusOfResult (.error error)).code

/-- One complete nonzero exact-retry route: the Level 3 child and tag load, its selected dispatch
route, the concrete status store, and the generated wrapper exit. -/
structure RetryExactErrorToExitResult (args : DecodeInlineArgs) (fromStep used : Nat)
    (entry before childAfter dispatch routeAfter afterStore after : State) (error : Contracts.DecodeError)
    (link s0 s1 s2 : BitVec 64) : Prop where
  handoff : RetryExactTagHandoffResult args fromStep used before childAfter dispatch link s0 s1 s2
  semanticResult : meaningDecode args.bytes = .error error
  route : WrapperOwnedTerminalRouteFrame dispatch dispatch routeAfter (fromStep + used + 1)
    (retryExactErrorRouteSteps error) (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 (retryExactErrorStatus error))
  store : Runs (try_step (fromStep + used + 1 + retryExactErrorRouteSteps error) false)
    routeAfter afterStore false
  epilogue : WrapperEpilogueExitResult
    (fromStep + used + 1 + retryExactErrorRouteSteps error + 1) dispatch afterStore after link s0 s1 s2
    (BitVec.ofNat 64 (args.stackBase + 0xa20)) (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 (retryExactErrorStatus error))
  scopedTrace : ScopedTrace
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw) Level2ChildSummary
    fromStep (used + 8 + retryExactErrorRouteSteps error) before after
  exitPc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  exitResult : after.regs.get? x10 = some (BitVec.ofNat 64 0)
  exitStatus : after.regs.get? x11 = some (BitVec.ofNat 64 (retryExactErrorStatus error))
  statusWord : Word32LERep after Elflings.canonicalDecoderGlobalsLayout.status
    (retryExactErrorStatus error)
  globalsFrame : DecoderGlobalsBoundaryFrame routeAfter after
  exitGlobals : WrapperExitGlobals routeAfter after
    (BitVec.ofNat 64 (retryExactErrorStatus error))

private theorem retry_exact_error_route_to_exit
    {args : DecodeInlineArgs} {fromStep used : Nat} {entry before childAfter dispatch routeAfter : State}
    (machineEntry : ZesuDecodeRawMachinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry)
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      args.machineArgs before)
    (handoff : RetryExactTagHandoffResult args fromStep used before childAfter dispatch link s0 s1 s2)
    (error : Contracts.DecodeError) (route : WrapperOwnedTerminalRouteFrame dispatch dispatch routeAfter
      (fromStep + used + 1) (retryExactErrorRouteSteps error) (BitVec.ofNat 64 0x1035c)
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 (retryExactErrorStatus error))) :
    ∃ afterStore after,
      Runs (try_step (fromStep + used + 1 + retryExactErrorRouteSteps error) false)
        routeAfter afterStore false ∧
      WrapperEpilogueExitResult (fromStep + used + 1 + retryExactErrorRouteSteps error + 1) dispatch
        afterStore after link s0 s1 s2 (BitVec.ofNat 64 (args.stackBase + 0xa20)) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 (retryExactErrorStatus error)) ∧
      ScopedTrace
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw) Level2ChildSummary
        (fromStep + used + 1) (7 + retryExactErrorRouteSteps error) dispatch after ∧
      WrapperExitGlobals routeAfter after (BitVec.ofNat 64 (retryExactErrorStatus error)) := by
  have dispatchMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      args.machineArgs dispatch := machine.mono handoff.machineAgree handoff.retired
  have routeFrame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 routeAfter :=
    WrapperSavedRegisterFrame.of_mem_eq handoff.savedFrame route.route.memory
  have routeStack : routeAfter.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) :=
    route.route.savedStack.trans handoff.stack
  have routeGlobals : routeAfter.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    route.route.savedS2.trans handoff.globals
  have stackNat : (BitVec.ofNat 64 args.stackBase).toNat = args.stackBase := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have fits := machineEntry.stackFrameFits
    omega
  let restore := wrapperRestoreAddresses_of_machinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry
    machineEntry
  obtain ⟨afterStore, after, store, trace, epilogue, exitGlobals⟩ :=
    wrapper_dispatch_route_through_exit_with_globals dispatchMachine (fromStep + used + 1)
      (retryExactErrorRouteSteps error) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 (retryExactErrorStatus error)) link s0 s1 s2
      (BitVec.ofNat 64 args.stackBase) (BitVec.ofNat 64 (args.stackBase + 0xa20))
      route.route.terminal (by simpa [stackNat] using routeFrame)
      (by simpa [stackNat] using machineEntry.stackAvoidsStatusGlobals) routeGlobals routeStack
      restore.raAddress restore.s0Address
      restore.s1Address restore.s2Address restore.raAddressEq restore.s0AddressEq restore.s1AddressEq
      restore.s2AddressEq restore.facts.raAddressNat restore.facts.s0AddressNat restore.facts.s1AddressNat
      restore.facts.s2AddressNat restore.facts.raAligned restore.facts.s0Aligned restore.facts.s1Aligned
      restore.facts.s2Aligned restore.facts.raAllowed restore.facts.s0Allowed restore.facts.s1Allowed
      restore.facts.s2Allowed (by simpa using wrapper_final_stack_address args.stackBase)
  have statusConfined : WrapperPrefix (fromStep + used + 1 + retryExactErrorRouteSteps error) 1
      routeAfter afterStore := ConfinedPrefix.ownStep' route.route.atTerminal store
  have finalExit : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw) Level2ChildSummary
      (fromStep + used + 1 + retryExactErrorRouteSteps error + 1 + 6) 0 after after :=
    ScopedTrace.exitAt _ after (BitVec.ofNat 64 0x10378) epilogue.pc (by
        simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
          functionInstance_raw_decoder_root_zesu_decode_raw])
  have epilogueScoped : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw) Level2ChildSummary
      (fromStep + used + 1 + retryExactErrorRouteSteps error + 1) 6 afterStore after :=
    epilogue.confined 0 after (by simpa [Nat.add_assoc] using finalExit)
  have routeScoped : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw) Level2ChildSummary
      (fromStep + used + 1) (retryExactErrorRouteSteps error + 7) dispatch after := by
    have afterStatus : ScopedTrace
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw) Level2ChildSummary
        (fromStep + used + 1 + retryExactErrorRouteSteps error) 7 routeAfter after :=
      statusConfined 6 after (by simpa [Nat.add_assoc] using epilogueScoped)
    exact route.confined 7 after (by simpa [Nat.add_assoc] using afterStatus)
  exact ⟨afterStore, after, store, epilogue,
    by simpa [Nat.add_assoc, Nat.add_comm] using routeScoped, exitGlobals⟩

private theorem retry_exact_handoff_to_exit_scoped
    {args : DecodeInlineArgs} {fromStep used : Nat} {before childAfter dispatch after : State}
    {link s0 s1 s2 : BitVec 64}
    (handoff : RetryExactTagHandoffResult args fromStep used before childAfter dispatch link s0 s1 s2)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true) (routeSteps : Nat)
    (routeTrace : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw) Level2ChildSummary
      (fromStep + used + 1) (7 + routeSteps) dispatch after) :
    ScopedTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw) Level2ChildSummary
      fromStep (used + 8 + routeSteps) before after := by
  have childPc : childAfter.regs.get? PC = some (BitVec.ofNat 64 0x103f8) := by
    have post := handoff.post
    simp [DecodeInlinePost, DecodeInlineRetryPost, phase, exactPrefix] at post
    exact post.2
  have tagTrace : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw) Level2ChildSummary
      (fromStep + used) (7 + routeSteps + 1) childAfter after :=
    ScopedTrace.ownStep (fromStep + used) (7 + routeSteps) (BitVec.ofNat 64 0x103f8)
      childAfter dispatch after childPc (by owned_pc) (by owned_pc) handoff.tagStep routeTrace
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (ScopedTrace.childBody fromStep used (7 + routeSteps + 1)
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id before childAfter after
      (Level2ChildSummary.decode handoff.child) tagTrace)

/-- Extend a supplied exact-prefix retry handoff through its selected nonzero dispatch route.
Keeping the handoff explicit lets the first-attempt wrapper proof retain its already-consumed Level
3 child. -/
theorem retry_exact_error_handoff_to_exit
    {args : DecodeInlineArgs} {fromStep used : Nat} {entry before childAfter dispatch : State}
    (machineEntry : ZesuDecodeRawMachinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry)
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      args.machineArgs before)
    (handoff : RetryExactTagHandoffResult args fromStep used before childAfter dispatch link s0 s1 s2)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true) (error : Contracts.DecodeError)
    (semanticResult : meaningDecode args.bytes = .error error) :
    ∃ routeAfter afterStore after,
      RetryExactErrorToExitResult args fromStep used entry before childAfter dispatch routeAfter afterStore
        after error link s0 s1 s2 := by
  have dispatchMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      args.machineArgs dispatch := machine.mono handoff.machineAgree handoff.retired
  cases error with
  | outOfMemory =>
      obtain ⟨routeAfter, route⟩ := wrapper_dispatch_tag1_owned_terminal_route dispatchMachine (Agree.refl _)
        handoff.retired handoff.code (fromStep + used + 1) handoff.dispatchPc (by
          simpa [semanticResult, decodeInternalResultTag] using handoff.semanticTag)
      obtain ⟨afterStore, after, store, epilogue, scopedTrace, exitGlobals⟩ :=
        retry_exact_error_route_to_exit machineEntry machine handoff .outOfMemory route
      exact ⟨routeAfter, afterStore, after,
        ⟨handoff, semanticResult, route, store, epilogue,
          retry_exact_handoff_to_exit_scoped handoff phase exactPrefix 7 scopedTrace,
          epilogue.pc, epilogue.a0, epilogue.a1,
          by simpa using exitGlobals.statusWord, exitGlobals.boundaryFrame, exitGlobals⟩⟩
  | invalidSsz =>
      obtain ⟨routeAfter, route⟩ := wrapper_dispatch_tag2_owned_terminal_route dispatchMachine (Agree.refl _)
        handoff.retired handoff.code (fromStep + used + 1) handoff.dispatchPc (by
          simpa [semanticResult, decodeInternalResultTag] using handoff.semanticTag)
      obtain ⟨afterStore, after, store, epilogue, scopedTrace, exitGlobals⟩ :=
        retry_exact_error_route_to_exit machineEntry machine handoff .invalidSsz route
      exact ⟨routeAfter, afterStore, after,
        ⟨handoff, semanticResult, route, store, epilogue,
          retry_exact_handoff_to_exit_scoped handoff phase exactPrefix 9 scopedTrace,
          epilogue.pc, epilogue.a0, epilogue.a1,
          by simpa using exitGlobals.statusWord, exitGlobals.boundaryFrame, exitGlobals⟩⟩
  | unknownFork =>
      obtain ⟨routeAfter, route⟩ := wrapper_dispatch_tag3_owned_terminal_route dispatchMachine (Agree.refl _)
        handoff.retired handoff.code (fromStep + used + 1) handoff.dispatchPc (by
          simpa [semanticResult, decodeInternalResultTag] using handoff.semanticTag)
      obtain ⟨afterStore, after, store, epilogue, scopedTrace, exitGlobals⟩ :=
        retry_exact_error_route_to_exit machineEntry machine handoff .unknownFork route
      exact ⟨routeAfter, afterStore, after,
          ⟨handoff, semanticResult, route, store, epilogue,
          retry_exact_handoff_to_exit_scoped handoff phase exactPrefix 5 scopedTrace,
          epilogue.pc, epilogue.a0, epilogue.a1,
          by simpa using exitGlobals.statusWord, exitGlobals.boundaryFrame, exitGlobals⟩⟩

/-- Exact-prefix retry failures execute their selected nonzero dispatch path through the real status
store and wrapper epilogue.  The route is selected by the proved retry result, not by a synthetic
tag-exhaustiveness premise. -/
theorem retry_exact_error_to_exit
    {args : DecodeInlineArgs} {fromStep : Nat} {entry before : State}
    (decode : Level3DecodeInlineContract)
    (machineEntry : ZesuDecodeRawMachinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry)
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      args.machineArgs before)
    (pre : DecodeInlinePre args before) (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true) (error : Contracts.DecodeError)
    (semanticResult : meaningDecode args.bytes = .error error) (link s0 s1 s2 : BitVec 64)
    (saved : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 before) :
    ∃ used childAfter dispatch routeAfter afterStore after,
      RetryExactErrorToExitResult args fromStep used entry before childAfter dispatch routeAfter afterStore
        after error link s0 s1 s2 := by
  obtain ⟨used, childAfter, dispatch, handoff⟩ :=
    retry_exact_tag_handoff decode fromStep args machineEntry before pre phase exactPrefix link s0 s1 s2 saved
  obtain ⟨routeAfter, afterStore, after, result⟩ :=
    retry_exact_error_handoff_to_exit machineEntry machine handoff phase exactPrefix error semanticResult
  exact ⟨used, childAfter, dispatch, routeAfter, afterStore, after, result⟩

/-- The exact-prefix retry's successful result takes the real tag-zero dispatch route, copies the
832-byte final result into the wrapper's stored-result buffer, and reaches the wrapper exit. -/
structure RetryExactSuccessToExitResult (args : DecodeInlineArgs) (fromStep used : Nat)
    (entry before childAfter dispatch copyStart callState afterCopy routeAfter afterStore after : State)
    (value : BinaryFv.Specs.SSZ.StatelessInput) (contents : ByteArray)
    (link s0 s1 s2 : BitVec 64) (copyUsed : Nat) : Prop where
  handoff : RetryExactTagHandoffResult args fromStep used before childAfter dispatch link s0 s1 s2
  semanticSuccess : meaningDecode args.bytes = .ok value
  dispatchRoute : WrapperDispatchRouteFrame dispatch dispatch copyStart (fromStep + used + 1) 6
    (BitVec.ofNat 64 0x1033c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 2)
  copy : Tag0CopyToExitResult ⟨args.inputBase, args.bytes⟩ value args.stackBase entry copyStart callState
    afterCopy routeAfter afterStore after contents link s0 s1 s2 (fromStep + used + 7) copyUsed
  scopedTrace : WrapperScopedTrace fromStep (used + 23 + copyUsed) before after
  exitPc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  exitResult : after.regs.get? x10 = some (BitVec.ofNat 64 1)
  exitStatus : after.regs.get? x11 = some (BitVec.ofNat 64 1)
  statusWord : Word32LERep after Elflings.canonicalDecoderGlobalsLayout.status 1
  globalsFrame : DecoderGlobalsBoundaryFrame routeAfter after

/-- The retry child writes only its checked stack result, canonical allocator interval, allocator
state, and canonical stack. The wrapper entry's input placement excludes each of those regions, so
the paired Level 3 retry witness transports the original input intact to the child exit. -/
theorem retry_exact_original_input_at_child
    {args : DecodeInlineArgs} {fromStep used : Nat} {entry before childAfter dispatch : State}
    {link s0 s1 s2 : BitVec 64}
    (machineEntry : ZesuDecodeRawMachinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry)
    (handoff : RetryExactTagHandoffResult args fromStep used before childAfter dispatch link s0 s1 s2)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true) :
    DecodedValue.MemoryBytes childAfter args.inputBase args.bytes := by
  obtain ⟨decoded, contents, decodedPost, contentsSize, decodedSource, copyFrame, sourceFinal,
    destinationFinal, codeFinal, noAllocation, allocation, _⟩ :=
    handoff.retryAllocation phase exactPrefix
  have decodedInput : DecodedValue.MemoryBytes decoded args.inputBase args.bytes := by
    apply handoff.inputMemory.of_mem_eq
    intro index indexBound
    apply writesOnlyWithinOwnAllocation_preserves_byte decodedPost.2.2.1
    intro cursorBefore cursorAfter beforeCursor afterCursor
    obtain ⟨allocationBefore, allocationAfter, beforeAllocation, afterAllocation, arenaBase,
      cursorOrder, cursorBound⟩ := allocation
    have beforeEq : cursorBefore = allocationBefore :=
      Option.some.inj (beforeCursor.symm.trans beforeAllocation)
    have afterEq : cursorAfter = allocationAfter :=
      Option.some.inj (afterCursor.symm.trans afterAllocation)
    subst cursorBefore
    subst cursorAfter
    apply retryRawOwnedRegion_outside_input ⟨args.inputBase, args.bytes⟩ args.stackBase machineEntry
      arenaBase cursorBound
    change args.inputBase ≤ args.inputBase + index ∧
      args.inputBase + index < args.inputBase + args.bytes.size
    constructor <;> omega
  apply decodedInput.of_mem_eq
  intro index indexBound
  apply copyFrame
  by_cases beforeDestination : args.inputBase + index < args.finalResultBase
  · exact Or.inl beforeDestination
  · right
    have notInside : ¬ args.inputBase + index < args.finalResultBase + 832 := by
      intro inside
      have addressInStack : canonicalContractParams.env.stack (args.inputBase + index) := by
        have addressPastStack : args.stackBase ≤ args.inputBase + index := by
          simp [DecodeInlineArgs.finalResultBase] at beforeDestination
          omega
        have addressInFrame : args.inputBase + index - args.stackBase < 0xa20 := by
          simp [DecodeInlineArgs.finalResultBase] at inside
          omega
        simpa [Nat.add_sub_of_le addressPastStack] using
          machineEntry.stackFrameWritable (args.inputBase + index - args.stackBase) addressInFrame
      have inputAvoidsStack : args.inputBase + args.bytes.size ≤ args.inputBase + index ∨
          args.inputBase + index < args.inputBase := by
        simpa using machineEntry.inputAvoidsCanonicalStack _ addressInStack
      rcases inputAvoidsStack with beforeStack | afterStack <;> omega
    simp [DecodeInlineArgs.finalResultBase] at notInside ⊢
    omega

/-- Compose the exact-prefix retry success through the selected tag-zero dispatch and existing
stored-result-copy suffix.  The dispatch frame supplies the machine-preservation edge required by
the copy precondition; no second dispatch route is reconstructed here. -/
theorem retry_exact_success_handoff_to_exit
    {args : DecodeInlineArgs} {fromStep used : Nat} {entry before childAfter dispatch : State}
    (machineEntry : ZesuDecodeRawMachinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry)
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      args.machineArgs before)
    (link s0 s1 s2 : BitVec 64)
    (handoff : RetryExactTagHandoffResult args fromStep used before childAfter dispatch link s0 s1 s2)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true)
    (value : BinaryFv.Specs.SSZ.StatelessInput)
    (semanticSuccess : meaningDecode args.bytes = .ok value) :
    ∃ copyStart contents copyUsed callState afterCopy routeAfter afterStore after,
      RetryExactSuccessToExitResult args fromStep used entry before childAfter dispatch copyStart callState
        afterCopy routeAfter afterStore after value contents link s0 s1 s2 copyUsed := by
  have dispatchMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      args.machineArgs dispatch := machine.mono handoff.machineAgree handoff.retired
  obtain ⟨copyStart, dispatchRoute, dispatchAgree, dispatchPrefix⟩ :=
    wrapper_dispatch_tag0_route_frame_decoder dispatchMachine (Agree.refl _) handoff.retired handoff.code
      (fromStep + used + 1) handoff.dispatchPc (by
        simpa [semanticSuccess, decodeInternalResultTag] using handoff.semanticTag)
  obtain ⟨contents, contentsSize, finalPayload⟩ := handoff.finalPayload
  have copyMachine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (zesuDecodeRawMachineArgs ⟨args.inputBase, args.bytes⟩) copyStart := by
    simpa [DecodeInlineArgs.machineArgs, zesuDecodeRawMachineArgs] using
      dispatchMachine.mono dispatchAgree dispatchRoute.retired
  have copyFrame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 copyStart :=
    WrapperSavedRegisterFrame.of_mem_eq handoff.savedFrame dispatchRoute.memory
  have childInputMemory : DecodedValue.MemoryBytes childAfter args.inputBase args.bytes :=
    retry_exact_original_input_at_child machineEntry handoff phase exactPrefix
  have dispatchInputMemory : DecodedValue.MemoryBytes dispatch args.inputBase args.bytes :=
    childInputMemory.of_mem_eq (by simpa [handoff.memory])
  have copyInputMemory : DecodedValue.MemoryBytes copyStart args.inputBase args.bytes :=
    dispatchInputMemory.of_mem_eq (by simpa [dispatchRoute.memory])
  obtain ⟨allocationDecoded, allocationContents, allocationPost, allocationContentsSize,
    allocationSource, allocationCopy, allocationRetry, allocationFinal, allocationCode,
    allocationNoAllocation, allocation, allocationProvenance⟩ :=
    handoff.retryAllocation phase exactPrefix
  have rawSuccess : Contracts.meaningDecodeRaw args.retryRawArgs.bytes = .ok value := by
    rw [Contracts.meaningDecode, handoff.retryReason, if_pos exactPrefix] at semanticSuccess
    exact semanticSuccess
  have provenance : DecodeRawSuccessAllocationProvenance args.retryRawArgs (.ok value)
      before allocationDecoded := by
    rw [Contracts.meaningDecode, handoff.retryReason, if_pos exactPrefix] at allocationProvenance
    have rawSuccess' : Contracts.meaningDecodeRaw (args.bytes.extract 4 args.bytes.size) = .ok value := by
      simpa [DecodeInlineArgs.retryRawArgs] using rawSuccess
    rw [rawSuccess'] at allocationProvenance
    exact allocationProvenance
  obtain ⟨allocationCursorBefore, allocationCursorAfter, beforeAllocation, afterAllocation,
    arenaBase, cursorOrder, cursorBound⟩ := allocation
  rcases provenance with ⟨cursorBefore, cursorAfter, beforeCursor, afterCursor,
    sourceRepresentation⟩
  have cursorAfterEq : cursorAfter = allocationCursorAfter :=
    Option.some.inj (afterCursor.symm.trans afterAllocation)
  have originalRepresentation : StatelessInputRepInHeapInterval allocationDecoded args.inputBase args.bytes
      args.retryRawArgs.resultBase value cursorBefore cursorAfter := by
    simpa [DecodeInlineArgs.retryRawArgs] using
      sourceRepresentation.reindex_extract_suffix (inputBase := args.inputBase) (start := 4)
  have representationAfter : StatelessInputRepInHeapInterval childAfter args.inputBase args.bytes
      args.retryRawArgs.resultBase value cursorBefore cursorAfter := by
    exact originalRepresentation.survives_copy
      (decodeInlineRetryCopyArgs args allocationContents) allocationCopy
      (by
        intro address root
        dsimp [Contracts.range, DecodeInlineArgs.retryRawArgs] at root
        right
        simp [decodeInlineRetryCopyArgs, DecodeInlineArgs.retryRawArgs,
          DecodeInlineArgs.finalResultBase]
        omega)
      (by
        intro address interval
        dsimp [Contracts.interval] at interval
        left
        have stackAddress := machineEntry.stackObjectsReadable 0x20 (by omega)
        have notBelow : ¬ args.stackBase + 0x20 < Elflings.canonicalHeapLimit := by
          intro below
          exact canonicalArena_not_in_stack (args.stackBase + 0x20) below
            (by simpa [canonicalContractParams, canonicalEnvironment] using stackAddress)
        have heapLimitBelowStack : Elflings.canonicalHeapLimit ≤ args.stackBase + 0x20 := by omega
        have cursorBelowStack : cursorAfter ≤ args.stackBase + 0x20 := by
          rw [cursorAfterEq]
          omega
        dsimp [decodeInlineRetryCopyArgs, DecodeInlineArgs.finalResultBase]
        omega)
  have destinationRepresentation : StatelessInputRepInHeapInterval childAfter args.inputBase args.bytes
      args.finalResultBase value cursorBefore cursorAfter :=
    representationAfter.rebase_root (by
      have resultSize : canonicalContractParams.env.record.entryResult = 848 := by native_decide
      have fits := machineEntry.stackObjectsFit
      rw [resultSize] at fits
      simp [DecodeInlineArgs.retryRawArgs, DecodeInlineArgs.finalResultBase]
      omega)
      (by
        intro index bound
        exact (allocationFinal index (by simpa [allocationContentsSize] using bound)).trans
          (allocationRetry index (by simpa [decodeInlineRetryCopyArgs, allocationContentsSize] using bound)).symm)
  have copyRepresentation : StatelessInputRepInHeapInterval copyStart args.inputBase args.bytes
      args.finalResultBase value cursorBefore cursorAfter :=
    destinationRepresentation.of_mem_eq (by rw [dispatchRoute.memory, handoff.memory])
  have copyPre : Tag0StoredResultCopyPre ⟨args.inputBase, args.bytes⟩ value args.stackBase entry copyStart
      contents link s0 s1 s2 :=
    { machineEntry := machineEntry
      atCopyStart := dispatchRoute.atTerminal
      machine := copyMachine
      retired := dispatchRoute.retired
      code := dispatchRoute.code
      stack := dispatchRoute.savedStack.trans handoff.stack
      globals := dispatchRoute.savedS2.trans handoff.globals
      savedFrame := copyFrame
      sourceBytes := by
        simpa [DecodeInlineArgs.finalResultBase] using
          finalPayload.of_mem_eq (fun _ _ => by rw [dispatchRoute.memory])
      contentsSize := contentsSize
      sourceRepresentation := ⟨cursorBefore, cursorAfter, copyRepresentation, by
        have afterEq : allocationCursorAfter = cursorAfter :=
          Option.some.inj (afterAllocation.symm.trans afterCursor)
        exact afterEq ▸ cursorBound⟩
      inputMemory := copyInputMemory }
  obtain ⟨copyUsed, callState, afterCopy, copyPhase⟩ :=
    tag0_stored_result_copy_phase contents link s0 s1 s2 copyPre (fromStep + used + 7)
  obtain ⟨routeAfter, afterStore, after, copy⟩ :=
    tag0_copy_to_exit contents link s0 s1 s2 copyPhase
  have dispatchTail : WrapperScopedTrace (fromStep + used + 1) (6 + (16 + copyUsed)) dispatch after :=
    dispatchPrefix (16 + copyUsed) after (by
      simpa [Nat.add_assoc] using copy.scopedTrace)
  have scopedTrace : WrapperScopedTrace fromStep (used + 23 + copyUsed) before after := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      retry_exact_handoff_to_exit_scoped handoff phase exactPrefix (15 + copyUsed) (by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using dispatchTail)
  exact ⟨copyStart, contents, copyUsed, callState, afterCopy, routeAfter,
    afterStore, after, ⟨handoff, semanticSuccess, dispatchRoute, copy, scopedTrace,
      copy.epilogue.pc, copy.epilogue.a0, copy.epilogue.a1,
      copy.statusWord, copy.globalsFrame⟩⟩

/-- Compatibility wrapper that produces the selected retry child before delegating the remaining
tag-zero dispatch, stored-result copy, and wrapper-exit proof to the supplied-handoff edge. -/
theorem retry_exact_success_to_exit
    {args : DecodeInlineArgs} {fromStep : Nat} {entry before : State}
    (decode : Level3DecodeInlineContract)
    (machineEntry : ZesuDecodeRawMachinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry)
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      args.machineArgs before)
    (pre : DecodeInlinePre args before) (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true)
    (value : BinaryFv.Specs.SSZ.StatelessInput) (semanticSuccess : meaningDecode args.bytes = .ok value)
    (link s0 s1 s2 : BitVec 64) (saved : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 before) :
    ∃ used childAfter dispatch copyStart contents copyUsed callState afterCopy routeAfter afterStore after,
      RetryExactSuccessToExitResult args fromStep used entry before childAfter dispatch copyStart callState
        afterCopy routeAfter afterStore after value contents link s0 s1 s2 copyUsed := by
  obtain ⟨used, childAfter, dispatch, handoff⟩ :=
    retry_exact_tag_handoff decode fromStep args machineEntry before pre phase exactPrefix link s0 s1 s2 saved
  obtain ⟨copyStart, contents, copyUsed, callState, afterCopy, routeAfter, afterStore, after, result⟩ :=
    retry_exact_success_handoff_to_exit machineEntry machine link s0 s1 s2 handoff phase exactPrefix
      value semanticSuccess
  exact ⟨used, childAfter, dispatch, copyStart, contents, copyUsed, callState, afterCopy, routeAfter,
    afterStore, after, result⟩

end BinaryFv.Zesu.MachineExecution
