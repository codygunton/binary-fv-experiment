import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryFinish
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame

/-!
# Exact-prefix retry tag handoff

This module joins the selected Level 3 exact-prefix retry body to the one wrapper-owned result-tag
load at `0x103f8`.  It intentionally stops at the dispatch instruction `0x103fc`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The lossless Level 2 boundary after the exact-prefix retry's wrapper-owned result-tag load.
It retains the retry payload facts for tag zero while leaving all dispatch routes unexecuted. -/
structure RetryExactTagHandoffResult (args : DecodeInlineArgs) (fromStep used : Nat)
    (before childAfter after : State) (link s0 s1 s2 : BitVec 64) : Prop where
  bound : used ≤ decodeInlineStepBound args
  child : level3DecodeChildSummary
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
    fromStep used before childAfter
  childTrace : ScopedTrace
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
    (DecodeInlineExit args) Level3ChildSummary fromStep used before childAfter
  post : DecodeInlinePost args before childAfter
  retrySuccess : DecodeInlineRetrySuccessPost args before childAfter
  retryAllocation : DecodeInlineRetrySuccessAllocationFrame args before childAfter
  retryExactBound : used ≤ 16384 + 512 * args.retryRawArgs.bytes.size + 6765
  retryReason : Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz
  inputMemory : DecodedValue.MemoryBytes before args.inputBase args.bytes
  outgoing : DecodeInlineOutgoingFrame args childAfter
  saveArea : DecodeInlineCallerSaveArea args before childAfter
  tagStep : Runs (try_step (fromStep + used) false) childAfter after false
  scopedTrace : ScopedTrace
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw)
    (fun pc => pc = BitVec.ofNat 64 0x103fc) Level2ChildSummary fromStep (used + 1) before after
  semanticTag : after.regs.get? x10 = some
    (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes)))
  dispatchPc : after.regs.get? PC = some (BitVec.ofNat 64 0x103fc)
  machineAgree : Agree decoderPreserved before after
  code : canonicalContractParams.env.CodeIntact after
  retired : RetiredCounterPresent after
  memory : after.mem = childAfter.mem
  globalsFrame : DecoderGlobalsBoundaryFrame before after
  stack : after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)
  globals : after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  savedFrame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 after
  sourcePayload : ∃ contents, contents.size = 832 ∧
    DecodedValue.MemoryBytes after args.retryRawArgs.resultBase contents
  finalPayload : ∃ contents, contents.size = 832 ∧
    DecodedValue.MemoryBytes after args.finalResultBase contents

/-- The exact-prefix retry `decodeRaw` may write its retry stack result, allocator interval,
allocator state, and canonical stack. None contains the generated decoder globals. -/
theorem retryRawOwnedRegion_outside_decoderGlobals (args : DecodeInlineArgs)
    {entry : State} (machine : ZesuDecodeRawMachinePre
      { inputBase := args.inputBase, bytes := args.bytes } args.stackBase entry)
    {cursorBefore cursorAfter address : Nat}
    (cursorBound : cursorAfter ≤ Elflings.canonicalHeapLimit)
    (global : DecoderGlobalsByte address) :
    ¬ canonicalContractParams.env.ownedRegion args.retryRawArgs.resultBase
      canonicalContractParams.env.record.entryResult cursorBefore cursorAfter address := by
  have globalBelow : address < Entrypoints.ZesuDecodeRaw.globalsCeiling := by
    simpa [DecoderGlobalsByte, Entrypoints.ZesuDecodeRaw.globalsCeiling] using global.2
  intro owned
  change
    (Contracts.allocatedRegion args.retryRawArgs.resultBase
      canonicalContractParams.env.record.entryResult cursorBefore cursorAfter address ∨
      (canonicalContractParams.env.allocatorState address ∨ canonicalContractParams.env.stack address))
      at owned
  rcases owned with (record | allocation) | allocator | stack
  · have recordIndex : address - args.retryRawArgs.resultBase <
      canonicalContractParams.env.record.entryResult := by
      dsimp [Contracts.range, DecodeInlineArgs.retryRawArgs] at record
      change address - (args.stackBase + 0x6b0) < canonicalContractParams.env.record.entryResult
      omega
    have resultBase : args.retryRawArgs.resultBase = args.stackBase + 0x6b0 := rfl
    have recordAddress : args.stackBase +
        (0x6b0 + (address - args.retryRawArgs.resultBase)) = address := by
      rw [resultBase]
      dsimp [Contracts.range, DecodeInlineArgs.retryRawArgs] at record
      omega
    change args.stackBase + 0x6b0 ≤ address ∧
      address < args.stackBase + 0x6b0 + canonicalContractParams.env.record.entryResult at record
    have recordInStack : canonicalContractParams.env.stack address := by
      rw [← recordAddress]
      exact machine.stackObjectsReadable _ (by
        have := recordIndex
        omega)
    exact (canonicalStack_disjoint_from_globals address globalBelow)
      (by simpa [canonicalContractParams, canonicalEnvironment] using recordInStack)
  · exact decodeRawAllocationInterval_outside_decoderGlobals cursorBound global allocation
  · have heapTopBelowGlobals : Elflings.canonicalHeapTopAddr + 8 ≤
      Elflings.GeneratedDecoderGlobals.bssBase := by native_decide
    have heapPosBelowGlobals : Elflings.canonicalHeapPosAddr + 8 ≤
      Elflings.GeneratedDecoderGlobals.bssBase := by native_decide
    change Elflings.canonicalAllocatorState address at allocator
    rcases global with ⟨globalBase, _⟩
    rcases allocator with allocator | allocator <;> omega
  · exact (canonicalStack_disjoint_from_globals address globalBelow)
      (by simpa [canonicalContractParams, canonicalEnvironment] using stack)

/-- Extend a supplied exact-prefix retry child with the actual `lhu a0, -1552(a0)` Sail step.
The caller supplies the child facts so a Level 2 composition retains the one selected child rather
than invoking the conditional Level 3 theorem again. -/
theorem retry_exact_tag_handoff_of_child
    (fromStep : Nat) (args : DecodeInlineArgs)
    (machineEntry : ZesuDecodeRawMachinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry)
    (before : State) (pre : DecodeInlinePre args before)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true)
    (link s0 s1 s2 : BitVec 64)
    {used : Nat} {childAfter : State}
    (bound : used ≤ decodeInlineStepBound args)
    (childTrace : ScopedTrace decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep used before childAfter)
    (flat : FunctionTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (DecodeInlineExit args) fromStep used before childAfter)
    (post : DecodeInlinePost args before childAfter)
    (machine : DecodeInlineMachinePost before childAfter)
    (outgoing : DecodeInlineOutgoingFrame args childAfter)
    (saveArea : DecodeInlineCallerSaveArea args before childAfter)
    (retryAllocation : DecodeInlineRetrySuccessAllocationFrame args before childAfter)
    (retryExactBound : used ≤ 16384 + 512 * args.retryRawArgs.bytes.size + 6765)
    (inputMemory : DecodedValue.MemoryBytes before args.inputBase args.bytes)
    (saved : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 before) :
    ∃ after, RetryExactTagHandoffResult args fromStep used before childAfter after link s0 s1 s2 := by
  have childPc : childAfter.regs.get? PC = some (BitVec.ofNat 64 0x103f8) := by
    simp [DecodeInlinePost, DecodeInlineRetryPost, phase, exactPrefix] at post
    exact post.2
  have retrySuccess : DecodeInlineRetrySuccessPost args before childAfter := by
    simp [DecodeInlinePost, DecodeInlineRetryPost, phase, exactPrefix] at post
    exact post.1
  have retryReason : Contracts.meaningDecodeRaw args.bytes = .error .invalidSsz :=
    (pre.retryReason phase).1
  obtain ⟨retired, tagStep⟩ := retry_exact_result_tag_step (fromStep + used) args before childAfter
    pre machine outgoing phase exactPrefix childPc
  let after := afterRegisterWrite childAfter (BitVec.ofNat 64 0x103f8) retired x10
    (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes)))
  have dispatchPc : after.regs.get? PC = some (BitVec.ofNat 64 0x103fc) := by
    simpa [after] using afterRegisterWrite_pc childAfter (BitVec.ofNat 64 0x103f8) retired x10
      (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes)))
  have semanticTag : after.regs.get? x10 = some
      (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes))) := by
    simp [after, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  have machineAgree : Agree decoderPreserved before after :=
    machine.agree.trans (afterRegisterWrite_agree_of (P := decoderPreserved)
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have code : canonicalContractParams.env.CodeIntact after := by
    simpa [after, afterRegisterWrite_mem] using machine.code
  have retiredPresent : RetiredCounterPresent after := by
    exact afterRegisterWrite_retired_present childAfter (BitVec.ofNat 64 0x103f8) retired x10
      (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes)))
  have memory : after.mem = childAfter.mem := by
    simp [after, afterRegisterWrite_mem]
  have stack : after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
    have outgoingExact : childAfter.regs.get? x10 = some
        (BitVec.ofNat 64 (args.stackBase + 0x1000)) ∧
        childAfter.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
        DecodedValue.ResultStatusLERep childAfter (args.stackBase + 0x9f0)
          (decodeInternalResultTag (meaningDecode args.bytes)) := by
      simpa [DecodeInlineOutgoingFrame, phase, exactPrefix] using outgoing
    have childStack : childAfter.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by
      exact outgoingExact.2.1
    simpa [after] using (afterRegisterWrite_register childAfter (BitVec.ofNat 64 0x103f8)
      retired x10 x2 (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes)))
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans childStack
  have globals : after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    have childGlobals : childAfter.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
      machine.globalsValue.trans pre.globalsValue
    simpa [after] using (afterRegisterWrite_register childAfter (BitVec.ofNat 64 0x103f8)
      retired x10 x18 (BitVec.ofNat 64 (decodeInternalResultTag (meaningDecode args.bytes)))
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans childGlobals
  have savedFrame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 after :=
    WrapperSavedRegisterFrame.of_mem_eq
      (WrapperSavedRegisterFrame.of_decode_inline_caller_save_area saved saveArea) memory
  obtain ⟨decoded, contents, decodedPost, contentsSize, decodedSource, copyFrame, sourcePayload,
    finalPayload, retryCode, noAllocation⟩ := retrySuccess
  obtain ⟨allocationDecoded, allocationContents, allocationPost, allocationContentsSize,
    allocationSource, allocationCopy, allocationRetry, allocationFinal, allocationCode,
    allocationNoAllocation, allocation, allocationProvenance⟩ := retryAllocation phase exactPrefix
  have globalsAtChild : DecoderGlobalsBoundaryFrame before childAfter := by
    have globalOutsideFinalDestination : ∀ address, DecoderGlobalsByte address →
        address < args.finalResultBase ∨ args.finalResultBase + 832 ≤ address := by
      intro address global
      by_cases beforeDestination : address < args.finalResultBase
      · exact Or.inl beforeDestination
      · right
        apply Nat.le_of_not_gt
        intro inside
        have inFinalResult : args.finalResultBase ≤ address ∧
            address < args.finalResultBase + 832 := by omega
        have inStack : canonicalContractParams.env.stack address := by
          have addressPastStack : args.stackBase ≤ address := by
            simp [DecodeInlineArgs.finalResultBase] at inFinalResult
            omega
          have addressInFrame : address - args.stackBase < 0xa20 := by
            simp [DecodeInlineArgs.finalResultBase] at inFinalResult
            omega
          simpa [Nat.add_sub_of_le addressPastStack] using
            machineEntry.stackFrameWritable (address - args.stackBase) addressInFrame
        exact (canonicalStack_disjoint_from_globals address (by
          simpa [DecoderGlobalsByte, Entrypoints.ZesuDecodeRaw.globalsCeiling] using global.2))
          (by simpa [canonicalContractParams, canonicalEnvironment] using inStack)
    constructor
    · have atDecoded : allocationDecoded.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted =
          before.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted := by
        apply writesOnlyWithinOwnAllocation_preserves_byte allocationPost.2.2.1
        intro cursorBefore cursorAfter beforeCursor afterCursor
        obtain ⟨allocationBefore, allocationAfter, beforeAllocation, afterAllocation, arenaBase,
          cursorOrder, cursorBound⟩ := allocation
        have beforeEq : cursorBefore = allocationBefore :=
          Option.some.inj (beforeCursor.symm.trans beforeAllocation)
        have afterEq : cursorAfter = allocationAfter :=
          Option.some.inj (afterCursor.symm.trans afterAllocation)
        subst cursorBefore
        subst cursorAfter
        exact retryRawOwnedRegion_outside_decoderGlobals args machineEntry cursorBound
          (by unfold DecoderGlobalsByte; native_decide)
      have attemptedGlobal : DecoderGlobalsByte Elflings.canonicalDecoderGlobalsLayout.attempted := by
        unfold DecoderGlobalsByte
        native_decide
      rw [allocationCopy Elflings.canonicalDecoderGlobalsLayout.attempted
        (globalOutsideFinalDestination _ attemptedGlobal)]
      exact atDecoded
    · have atDecoded : allocationDecoded.mem.get?
          (Elflings.canonicalDecoderGlobalsLayout.storedResult +
            Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) =
          before.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
            Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) := by
        apply writesOnlyWithinOwnAllocation_preserves_byte allocationPost.2.2.1
        intro cursorBefore cursorAfter beforeCursor afterCursor
        obtain ⟨allocationBefore, allocationAfter, beforeAllocation, afterAllocation, arenaBase,
          cursorOrder, cursorBound⟩ := allocation
        have beforeEq : cursorBefore = allocationBefore :=
          Option.some.inj (beforeCursor.symm.trans beforeAllocation)
        have afterEq : cursorAfter = allocationAfter :=
          Option.some.inj (afterCursor.symm.trans afterAllocation)
        subst cursorBefore
        subst cursorAfter
        exact retryRawOwnedRegion_outside_decoderGlobals args machineEntry cursorBound
          (by unfold DecoderGlobalsByte; native_decide)
      have storedGlobal : DecoderGlobalsByte
          (Elflings.canonicalDecoderGlobalsLayout.storedResult +
            Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) := by
        unfold DecoderGlobalsByte
        native_decide
      rw [allocationCopy
        (Elflings.canonicalDecoderGlobalsLayout.storedResult +
          Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset)
        (globalOutsideFinalDestination _ storedGlobal)]
      exact atDecoded
  have endpoint : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (fun pc => pc = BitVec.ofNat 64 0x103fc) Level2ChildSummary (fromStep + used + 1) 0 after
      after :=
    ScopedTrace.exitAt _ after (BitVec.ofNat 64 0x103fc) dispatchPc rfl
  have tagScoped : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (fun pc => pc = BitVec.ofNat 64 0x103fc) Level2ChildSummary (fromStep + used) 1 childAfter
      after :=
    ScopedTrace.ownStep (fromStep + used) 0 (BitVec.ofNat 64 0x103f8) childAfter after after
      childPc (by
        apply functionInstanceExecutionPcs_iff_ranges.mpr
        apply RegionPcs.iff_inRanges.mpr
        native_decide) (by simp) (by simpa [after] using tagStep) endpoint
  have scopedTrace : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (fun pc => pc = BitVec.ofNat 64 0x103fc) Level2ChildSummary fromStep (used + 1) before
      after := by
    exact ScopedTrace.childBody fromStep used 1
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id before
      childAfter after
      (Level2ChildSummary.decode ⟨rfl, args, pre, bound, childTrace, flat, post, machine, outgoing⟩)
      (by simpa [Nat.add_assoc] using tagScoped)
  have globalsFrame : DecoderGlobalsBoundaryFrame before after := by
    constructor
    · rw [memory]
      exact globalsAtChild.1
    · rw [memory]
      exact globalsAtChild.2
  refine ⟨after, ?_⟩
  exact ⟨bound, ⟨rfl, args, pre, bound, childTrace, flat, post, machine, outgoing⟩, childTrace, post,
    ⟨decoded, contents, decodedPost, contentsSize, decodedSource, copyFrame, sourcePayload,
      finalPayload, retryCode, noAllocation⟩, retryAllocation, retryExactBound, retryReason, inputMemory, outgoing, saveArea,
    by simpa [after] using tagStep,
    scopedTrace, semanticTag,
    dispatchPc, machineAgree, code, retiredPresent, memory, globalsFrame, stack, globals, savedFrame,
    ⟨contents, contentsSize, by simpa [after, memory] using sourcePayload⟩,
    ⟨contents, contentsSize, by simpa [after, memory] using finalPayload⟩⟩

/-- Obtain the selected exact-prefix retry child from its conditional Level 3 contract, then
extend it through the wrapper-owned tag load. -/
theorem retry_exact_tag_handoff
    (decode : Level3DecodeInlineContract) (fromStep : Nat) (args : DecodeInlineArgs)
    (machineEntry : ZesuDecodeRawMachinePre ⟨args.inputBase, args.bytes⟩ args.stackBase entry)
    (before : State) (pre : DecodeInlinePre args before)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true)
    (link s0 s1 s2 : BitVec 64)
    (saved : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 before) :
    ∃ used childAfter after,
      RetryExactTagHandoffResult args fromStep used before childAfter after link s0 s1 s2 := by
  obtain ⟨used, childAfter, bound, childTrace, flat, post, machine, outgoing, saveArea, _, _, _, _,
    retryAllocation, _, _, retryExactBound, _, _, _⟩ :=
    decode args fromStep before pre
  obtain ⟨after, handoff⟩ :=
    retry_exact_tag_handoff_of_child fromStep args machineEntry before pre phase exactPrefix link s0 s1 s2
      bound childTrace flat post machine outgoing saveArea retryAllocation
      (retryExactBound phase exactPrefix) pre.inputMemory saved
  exact ⟨used, childAfter, after, handoff⟩

end BinaryFv.Zesu.MachineExecution
