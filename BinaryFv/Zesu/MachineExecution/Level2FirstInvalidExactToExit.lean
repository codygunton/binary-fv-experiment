import BinaryFv.Zesu.MachineExecution.Level2FirstInvalidRetryEntry
import BinaryFv.Zesu.MachineExecution.Level2RetryExactToExit

/-! The first `invalidSsz` retry route through an exact-prefix nonzero result. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- The complete first-attempt `invalidSsz` route: the first decoder child takes its real error
edge, the wrapper enters the retry child, and that supplied child reaches the selected nonzero
exact-prefix exit. -/
structure FirstInvalidExactErrorToExitResult (args : ZesuDecodeRawArgs) (stackBase fromStep : Nat)
    (entry atDecode firstAfter branch retryBefore childAfter dispatch routeAfter afterStore after : State)
    (firstUsed retryUsed : Nat) (error : Contracts.DecodeError) (link s0 s1 s2 : BitVec 64) : Prop where
  firstInvalid : meaningDecodeRaw args.bytes = .error .invalidSsz
  semanticResult : meaningDecode args.bytes = .error error
  wrapperTrace : Trace fromStep 19 entry atDecode
  wrapperPrefix : WrapperPrefix fromStep 19 entry atDecode
  firstTransfer : Nonempty (InlineTransfer decodeRawExecutionPcs decodeRawExit Level2ChildSummary
    decodeInlineBoundary generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
    (fromStep + 19) firstUsed atDecode branch)
  retryReason : Runs (try_step (fromStep + 19 + firstUsed + 1) false) branch retryBefore false
  retryExit : RetryExactErrorToExitResult
    { phase := .retryAfterInvalidSsz, stackBase := stackBase, inputBase := args.inputBase,
      bytes := args.bytes }
    (fromStep + 19 + firstUsed + 2) retryUsed entry retryBefore childAfter dispatch routeAfter
    afterStore after error link s0 s1 s2
  firstInvalidBound : firstUsed ≤ 16392 + 512 * args.bytes.size
  retryExactBound : retryUsed ≤ 16384 + 512 * (args.bytes.extract 4 args.bytes.size).size + 6765
  exactPrefix : meaningHasExactErePrefix args.bytes = true
  scopedTrace : WrapperScopedTrace fromStep
    (19 + firstUsed + 2 + (retryUsed + 8 + retryExactErrorRouteSteps error)) entry after
  exitPc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  exitResult : after.regs.get? x10 = some (BitVec.ofNat 64 0)
  exitStatus : after.regs.get? x11 = some (BitVec.ofNat 64 (retryExactErrorStatus error))
  inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes
  code : canonicalContractParams.env.CodeIntact after
  platform : Agree platformPreserved entry after
  retired : RetiredCounterPresent after
  attempted : FlagRep after Elflings.canonicalDecoderGlobalsLayout.attempted true
  statusWord : Word32LERep after Elflings.canonicalDecoderGlobalsLayout.status
    (retryExactErrorStatus error)
  storedTag : DecodedValue.OptionTagRep after
    (Elflings.canonicalDecoderGlobalsLayout.storedResult +
      Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) false

/-- Compose the first decoder's actual `0x10324 → 0x1037c` error edge with the retry reason at
`0x1037c`, then consume the already-proved retry child through its selected nonzero exit route. -/
theorem first_invalid_exact_error_to_exit
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    (fromStep : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (firstInvalid : meaningDecodeRaw args.bytes = .error .invalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true) (error : Contracts.DecodeError)
    (semanticResult : meaningDecode args.bytes = .error error) :
    ∃ atDecode firstAfter branch retryBefore childAfter dispatch routeAfter afterStore after firstUsed
      retryUsed link s0 s1 s2,
      FirstInvalidExactErrorToExitResult args stackBase fromStep entry atDecode firstAfter branch
        retryBefore childAfter dispatch routeAfter afterStore after firstUsed retryUsed error link s0 s1 s2 := by
  obtain ⟨atDecode, firstAfter, branch, retryBefore, firstUsed, branchRetired, retryRetired, secondArgs,
    retryEntry⟩ := first_invalid_to_retry_entry allocator decode fromStep args stackBase entry source
      machine firstInvalid
  have secondArgsEq := retryEntry.secondArgsEq
  have firstTransfer := retryEntry.firstTransfer
  have retryReason := retryEntry.retryReason
  have secondPre := retryEntry.retryPre
  have retryMachine := retryEntry.retryWrapperMachine
  rcases retryEntry.savedFrame with ⟨link, s0, s1, s2, entryLink, savedAtRetry⟩
  have retryExact : meaningHasExactErePrefix secondArgs.bytes = true := by
    simpa [secondArgsEq] using exactPrefix
  have retryPhase : secondArgs.phase = .retryAfterInvalidSsz := by simp [secondArgsEq]
  have retrySemantic : meaningDecode secondArgs.bytes = .error error := by
    simpa [secondArgsEq] using semanticResult
  have savedAtRetry' : WrapperSavedRegisterFrame secondArgs.stackBase link s0 s1 s2 retryBefore := by
    simpa [secondArgsEq] using savedAtRetry
  have retryMachineEntry : ZesuDecodeRawMachinePre
      ⟨secondArgs.inputBase, secondArgs.bytes⟩ secondArgs.stackBase entry := by
    simpa [secondArgsEq] using machine
  obtain ⟨retryUsed, childAfter, dispatch, handoff⟩ :=
    retry_exact_tag_handoff decode (fromStep + 19 + firstUsed + 2) secondArgs retryMachineEntry retryBefore
      secondPre retryPhase retryExact link s0 s1 s2 savedAtRetry'
  obtain ⟨routeAfter, afterStore, after, retryExit⟩ :=
    retry_exact_error_handoff_to_exit retryMachineEntry retryMachine handoff retryPhase retryExact error retrySemantic
  have scopedTrace : WrapperScopedTrace fromStep
      (19 + firstUsed + 2 + (retryUsed + 8 + retryExactErrorRouteSteps error)) entry after := by
    exact retryEntry.routePrefix _ after (by simpa [Nat.add_assoc] using retryExit.scopedTrace)
  have childInput : DecodedValue.MemoryBytes childAfter args.inputBase args.bytes := by
    simpa [secondArgsEq] using
      retry_exact_original_input_at_child retryMachineEntry retryExit.handoff retryPhase retryExact
  have dispatchInput : DecodedValue.MemoryBytes dispatch args.inputBase args.bytes :=
    childInput.of_mem_eq (by simpa [retryExit.handoff.memory])
  have routeInput : DecodedValue.MemoryBytes routeAfter args.inputBase args.bytes :=
    dispatchInput.of_mem_eq (by simpa [retryExit.route.route.memory])
  have inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes := by
    intro index indexBound
    rw [retryExit.exitGlobals.memoryOutsideStatus (args.inputBase + index) (by
      rcases machine.inputAvoidsDecoderGlobals with inputBefore | globalsBefore
      · left
        have statusInGlobals : Elflings.GeneratedDecoderGlobals.bssBase ≤ 0x4215024 := by
          native_decide
        omega
      · right
        have statusEndInGlobals : 0x4215028 ≤ Elflings.GeneratedDecoderGlobals.bssBase +
            Elflings.GeneratedDecoderGlobals.bssSize := by native_decide
        omega)]
    exact routeInput index indexBound
  have decoderAgree : Agree decoderPreserved entry after :=
    retryEntry.decoderAgree.trans retryExit.handoff.machineAgree |>.trans retryExit.epilogue.agree
  have platform : Agree platformPreserved entry after := by
    intro register preserved
    rcases preserved with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact retryExit.epilogue.ra.trans entryLink.symm
    all_goals exact decoderAgree _ ⟨by decide, by simp [platformPreserved]⟩
  have attempted : FlagRep after Elflings.canonicalDecoderGlobalsLayout.attempted true := by
    unfold FlagRep
    rw [retryExit.exitGlobals.boundaryFrame.1, retryExit.route.route.memory,
      retryExit.handoff.globalsFrame.1]
    exact retryEntry.attempted
  have storedTag : DecodedValue.OptionTagRep after
      (Elflings.canonicalDecoderGlobalsLayout.storedResult +
        Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) false := by
    unfold DecodedValue.OptionTagRep
    rw [retryExit.exitGlobals.boundaryFrame.2, retryExit.route.route.memory,
      retryExit.handoff.globalsFrame.2, retryEntry.storedDiscriminant]
    exact source.2.2.2.2.2.1
  refine ⟨atDecode, firstAfter, branch, retryBefore, childAfter, dispatch, routeAfter, afterStore, after,
    firstUsed, retryUsed, link, s0, s1, s2, ?_⟩
  exact ⟨firstInvalid, semanticResult, retryEntry.wrapperTrace, retryEntry.wrapperPrefix,
    firstTransfer, retryReason,
    by simpa [secondArgsEq] using retryExit, retryEntry.firstInvalidBound,
    by simpa [secondArgsEq, DecodeInlineArgs.retryRawArgs] using retryExit.handoff.retryExactBound,
    exactPrefix, scopedTrace,
    retryExit.exitPc, retryExit.exitResult, retryExit.exitStatus, inputMemory, retryExit.epilogue.code,
    platform, retryExit.epilogue.retired, attempted, retryExit.statusWord, storedTag⟩

end BinaryFv.Zesu.MachineExecution
