import BinaryFv.Zesu.MachineExecution.Level2SecondEntryProof
import BinaryFv.Zesu.MachineExecution.OwnedPc

/-! The shared exported-entry prefix for every first-attempt `invalidSsz` retry route. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- The real first decoder error edge and wrapper retry instruction, including the trace from the
exported wrapper entry to the retry decoder entry.  `retryPre.globalsValue` transports the initial
decoder-globals address; a retry suffix owns the later status-store representation. -/
structure FirstInvalidRetryEntryResult (args : ZesuDecodeRawArgs) (stackBase fromStep : Nat)
    (entry atDecode firstAfter branch retryBefore : State) (firstUsed : Nat)
    (branchRetired retryRetired : BitVec 64) (secondArgs : DecodeInlineArgs) : Prop where
  firstInvalid : meaningDecodeRaw args.bytes = .error .invalidSsz
  firstInvalidBound : firstUsed ≤ 5927 + 512 * args.bytes.size
  secondArgsEq : secondArgs =
    { phase := .retryAfterInvalidSsz, stackBase := stackBase,
      inputBase := args.inputBase, bytes := args.bytes }
  wrapperTrace : Trace fromStep 19 entry atDecode
  wrapperPrefix : ConfinedPrefix
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary fromStep 19 entry atDecode
  firstTransfer : Nonempty (InlineTransfer decodeRawExecutionPcs decodeRawExit Level2ChildSummary
    decodeInlineBoundary generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
    (fromStep + 19) firstUsed atDecode branch)
  retryReason : Runs (try_step (fromStep + 19 + firstUsed + 1) false) branch retryBefore false
  retryPre : DecodeInlinePre secondArgs retryBefore
  retryWrapperMachine : DecoderMachinePre decodeRawExecutionPcs secondArgs.machineArgs retryBefore
  decoderAgree : Agree decoderPreserved entry retryBefore
  inputMemory : DecodedValue.MemoryBytes retryBefore args.inputBase args.bytes
  attempted : retryBefore.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted = some (1#8)
  storedDiscriminant : retryBefore.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
      Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) =
      entry.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
        Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset)
  savedFrame : ∃ link s0 s1 s2,
    entry.regs.get? x1 = some link ∧
    WrapperSavedRegisterFrame stackBase link s0 s1 s2 retryBefore
  routePrefix : ConfinedPrefix
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary fromStep (19 + firstUsed + 2) entry retryBefore

/-- Every byte of the original borrowed input lies outside the retry `decodeRaw` ownership region.
The four exclusions correspond exactly to `ownedRegion`: the retry result record is in the local
wrapper frame, allocation bytes stay in the canonical arena, and allocator/stack permissions use
their separate authoritative entry-placement frames. -/
theorem retryRawOwnedRegion_outside_input (args : ZesuDecodeRawArgs) (stackBase : Nat)
    {entry : State} (machine : ZesuDecodeRawMachinePre args stackBase entry)
    {cursorBefore cursorAfter address : Nat}
    (cursorBase : canonicalContractParams.env.arenaBase ≤ cursorBefore)
    (cursorBound : cursorAfter ≤ Elflings.canonicalHeapLimit)
    (inputByte : args.inputBase ≤ address ∧ address < args.inputBase + args.bytes.size) :
    ¬ canonicalContractParams.env.ownedRegion
      ({ phase := .retryAfterInvalidSsz, stackBase := stackBase, inputBase := args.inputBase,
          bytes := args.bytes } : DecodeInlineArgs).retryRawArgs.resultBase
      canonicalContractParams.env.record.entryResult cursorBefore cursorAfter address := by
  intro owned
  change
    (Contracts.allocatedRegion
        ({ phase := .retryAfterInvalidSsz, stackBase := stackBase, inputBase := args.inputBase,
            bytes := args.bytes } : DecodeInlineArgs).retryRawArgs.resultBase
        canonicalContractParams.env.record.entryResult cursorBefore cursorAfter address ∨
      (canonicalContractParams.env.allocatorState address ∨ canonicalContractParams.env.stack address))
      at owned
  rcases owned with (record | allocation) | allocator | stack
  · have resultSize : canonicalContractParams.env.record.entryResult = 848 := by native_decide
    change stackBase + 0x6b0 ≤ address ∧
      address < stackBase + 0x6b0 + canonicalContractParams.env.record.entryResult at record
    rcases machine.inputAvoidsStack with inputBefore | stackBeforeInput <;> omega
  · rcases machine.inputAvoidsCanonicalArena with inputBeforeArena | arenaBeforeInput
    · rcases allocation with ⟨beforeAddress, _⟩
      omega
    · rcases allocation with ⟨_, addressBefore⟩
      omega
  · rcases machine.inputAvoidsAllocatorState address allocator with inputBefore | allocatorBefore
    all_goals omega
  · rcases machine.inputAvoidsCanonicalStack address stack with inputBefore | stackBefore
    all_goals omega

/-- Enter the first inlined decoder, take its actual `invalidSsz` edge, and execute the wrapper's
retry-reason instruction.  This deliberately stops before selecting any retry outcome path. -/
theorem first_invalid_to_retry_entry
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    (fromStep : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (firstInvalid : meaningDecodeRaw args.bytes = .error .invalidSsz) :
    ∃ atDecode firstAfter branch retryBefore firstUsed branchRetired retryRetired secondArgs,
      FirstInvalidRetryEntryResult args stackBase fromStep entry atDecode firstAfter branch retryBefore
        firstUsed branchRetired retryRetired secondArgs := by
  obtain ⟨atDecode, wrapperTrace, wrapperPrefix, firstArgs, firstArgsEq, firstPre, entryAgree,
    attemptedAtDecode, firstUsed, firstAfter, -, firstChild, -, firstInvalidBound, firstTrace, firstFlat, firstPost, firstMachine,
    firstOutgoing, firstSaveArea, firstInput, firstLength, firstAttempted, firstStored, savedFrame⟩ :=
    wrapper_reaches_decode_first_invalid_contract allocator decode fromStep args stackBase entry source
      machine firstInvalid
  have firstPhase : firstArgs.phase = .first := by simp [firstArgsEq]
  have firstInvalid' : meaningDecodeRaw firstArgs.bytes = .error .invalidSsz := by
    simpa [firstArgsEq] using firstInvalid
  have firstDetails := firstPost
  simp only [DecodeInlinePost, firstPhase, DecodeInlineFirstPost] at firstDetails
  rw [firstInvalid'] at firstDetails
  have firstExit : firstAfter.regs.get? PC = some (BitVec.ofNat 64 0x10324) := firstDetails.2.2.1
  have firstTag : firstAfter.regs.get? x10 = some (BitVec.ofNat 64 2) := by
    simpa [decodeInternalResultTag] using firstDetails.2.2.2
  have firstStack : firstAfter.regs.get? x2 = some (BitVec.ofNat 64 firstArgs.stackBase) := by
    simpa [DecodeInlineOutgoingFrame, firstPhase] using firstOutgoing
  have firstInputMemory : DecodedValue.MemoryBytes firstAfter firstArgs.inputBase firstArgs.bytes := by
    simpa [DecodeInlineArgs.firstRawArgs] using firstDetails.1.1
  have firstWrapperMachine : DecoderMachinePre decodeRawExecutionPcs firstArgs.machineArgs atDecode := by
    simpa [firstArgsEq, DecodeInlineArgs.machineArgs, zesuDecodeRawMachineArgs] using
      machine.machine.mono entryAgree firstPre.machine.retiredCounter
  obtain ⟨branchRetired, retryRetired, secondArgs, retryEntry⟩ :=
    first_invalid_to_retry_decode_entry (fromStep + 19) firstUsed firstArgs atDecode firstAfter
      firstPre firstChild firstMachine firstWrapperMachine firstPhase firstExit firstTag
      firstStack firstInput firstLength firstInputMemory firstInvalid'
  let branch := wrapperAfterDecodeFirstErrorBranch firstAfter branchRetired
  let retryBefore := afterRegisterWrite branch (BitVec.ofNat 64 0x1037c) retryRetired x11
    (BitVec.ofNat 64 2)
  have retryAgree : Agree decoderPreserved entry retryBefore :=
    (entryAgree.trans firstMachine.agree).trans
      (wrapperAfterDecodeFirstErrorBranch_agree firstAfter branchRetired) |>.trans
      (afterRegisterWrite_agree_of
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved]))
  have retryRetiredPresent : RetiredCounterPresent retryBefore := by
    simpa [retryBefore, branch] using
      afterRegisterWrite_retired_present branch (BitVec.ofNat 64 0x1037c) retryRetired x11
        (BitVec.ofNat 64 2)
  have retryWrapperMachine : DecoderMachinePre decodeRawExecutionPcs secondArgs.machineArgs retryBefore := by
    simpa [retryBefore, branch, retryEntry.secondArgsEq, firstArgsEq, DecodeInlineArgs.machineArgs,
      zesuDecodeRawMachineArgs] using machine.machine.mono retryAgree retryRetiredPresent
  have retryAttempted : retryBefore.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted =
      some (1#8) := by
    simpa [retryBefore, branch, wrapperAfterDecodeFirstErrorBranch, afterRegisterWrite_mem] using
      firstAttempted
  have retryStored : retryBefore.mem.get?
      (Elflings.canonicalDecoderGlobalsLayout.storedResult +
        Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) =
      entry.mem.get? (Elflings.canonicalDecoderGlobalsLayout.storedResult +
        Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) := by
    simpa [retryBefore, branch, wrapperAfterDecodeFirstErrorBranch, afterRegisterWrite_mem] using
      firstStored
  rcases savedFrame with ⟨link, s0, s1, s2, linkAtEntry, s0AtEntry, s1AtEntry, s2AtEntry,
    savedAtDecode⟩
  have savedAtDecode' : WrapperSavedRegisterFrame firstArgs.stackBase link s0 s1 s2 atDecode := by
    simpa [firstArgsEq] using savedAtDecode
  have savedAtFirst : WrapperSavedRegisterFrame stackBase link s0 s1 s2 firstAfter :=
    by simpa [firstArgsEq] using
      WrapperSavedRegisterFrame.of_decode_inline_caller_save_area savedAtDecode' firstSaveArea
  have savedAtBranch : WrapperSavedRegisterFrame stackBase link s0 s1 s2 branch :=
    WrapperSavedRegisterFrame.of_mem_eq savedAtFirst (wrapperAfterDecodeFirstErrorBranch_mem _ _)
  have savedAtRetry : WrapperSavedRegisterFrame stackBase link s0 s1 s2 retryBefore := by
    apply WrapperSavedRegisterFrame.of_mem_eq savedAtBranch
    simp [retryBefore, afterRegisterWrite_mem]
  have branchPc : branch.regs.get? PC = some (BitVec.ofNat 64 0x1037c) := by
    simpa [branch, wrapperAfterDecodeFirstErrorBranch] using
      tryStepControlFlowAfterRetired_pc
        (controlFlowJumpState (tryStepControlFlowAfterIncrement firstAfter)
          (BitVec.ofNat 64 0x10324) (BitVec.ofNat 64 0x1037c))
        (BitVec.ofNat 64 0x1037c) branchRetired
  rcases retryEntry.firstTransfer with ⟨firstTransfer⟩
  have resumePc : firstTransfer.resumePc = BitVec.ofNat 64 0x1037c := by
    apply Option.some.inj
    exact firstTransfer.atResume.symm.trans branchPc
  have retryPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + 19 + firstUsed + 1) 1 branch retryBefore :=
    ConfinedPrefix.ownStep' firstTransfer.atResume
      (by simpa [branch, retryBefore] using retryEntry.retryReason)
      (by rw [resumePc]; owned_pc) (by rw [resumePc]; owned_pc)
  have firstTailPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + 19) (firstUsed + 2) atDecode retryBefore := by
    intro tailUsed after tail
    have retryTail := retryPrefix tailUsed after tail
    have retryTailRaw : ScopedTrace decodeRawExecutionPcs decodeRawExit Level2ChildSummary
        (fromStep + 19 + firstUsed + 1) (1 + tailUsed) branch after := by
      simpa [decodeRawExecutionPcs, decodeRawExit] using retryTail
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
  have routePrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep (19 + firstUsed + 2) entry retryBefore :=
    by exact ConfinedPrefix.trans' (19 + firstUsed + 2) wrapperPrefix firstTailPrefix
  refine ⟨atDecode, firstAfter, branch, retryBefore, firstUsed, branchRetired, retryRetired, secondArgs, ?_⟩
  exact
    { firstInvalid := firstInvalid
      firstInvalidBound := by simpa [firstArgsEq] using firstInvalidBound
      secondArgsEq := by simpa [firstArgsEq] using retryEntry.secondArgsEq
      wrapperTrace := wrapperTrace
      wrapperPrefix := wrapperPrefix
      firstTransfer := ⟨firstTransfer⟩
      retryReason := by simpa [branch, retryBefore] using retryEntry.retryReason
      retryPre := by simpa [branch, retryBefore] using retryEntry.retryPre
      retryWrapperMachine := retryWrapperMachine
      decoderAgree := retryAgree
      inputMemory := by
        simpa [retryBefore, branch, retryEntry.secondArgsEq, firstArgsEq] using
          retryEntry.retryPre.inputMemory
      attempted := retryAttempted
      storedDiscriminant := retryStored
      savedFrame := ⟨link, s0, s1, s2, linkAtEntry, savedAtRetry⟩
      routePrefix := routePrefix }

end BinaryFv.Zesu.MachineExecution
