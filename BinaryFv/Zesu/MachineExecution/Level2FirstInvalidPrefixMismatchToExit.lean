import BinaryFv.Zesu.MachineExecution.Level2FirstInvalidRetryEntry
import BinaryFv.Zesu.MachineExecution.Level2RetryPrefixMismatchToExit

/-! The full first-invalid, four-byte prefix-mismatch retry route through the wrapper exit. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

/-- The first failed raw decode, retry entry, four-byte prefix mismatch, and common wrapper exit
form one entry-to-exit scoped route. -/
structure FirstInvalidPrefixMismatchToExitResult (args : ZesuDecodeRawArgs) (stackBase fromStep : Nat)
    (entry atDecode firstAfter branch retryBefore childAfter handoff afterTail afterStore after : State)
    (firstUsed retryUsed : Nat) (branchRetired retryRetired link s0 s1 s2 : BitVec 64) : Prop where
  retryEntry : FirstInvalidRetryEntryResult args stackBase fromStep entry atDecode firstAfter branch
    retryBefore firstUsed branchRetired retryRetired
    { phase := .retryAfterInvalidSsz, stackBase := stackBase,
      inputBase := args.inputBase, bytes := args.bytes }
  retryExit : RetryPrefixMismatchRejectionToExitResult
    { phase := .retryAfterInvalidSsz, stackBase := stackBase,
      inputBase := args.inputBase, bytes := args.bytes }
    (fromStep + 19 + firstUsed + 2) retryUsed entry retryBefore childAfter handoff afterTail
    afterStore after link s0 s1 s2
  firstInvalidBound : firstUsed ≤ 5927 + 512 * args.bytes.size
  retryPrefixMismatchBound : retryUsed ≤ 30
  scopedTrace : WrapperScopedTrace fromStep (19 + firstUsed + 2 + (retryUsed + 10)) entry after
  entryPrefix : WrapperPrefix fromStep (19 + firstUsed + 2) entry retryBefore
  exitPc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  exitResult : after.regs.get? x10 = some (BitVec.ofNat 64 0)
  exitStatus : after.regs.get? x11 = some (BitVec.ofNat 64 2)
  semanticResult : meaningDecode args.bytes = .error .invalidSsz
  inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes
  code : canonicalContractParams.env.CodeIntact after
  platform : Agree platformPreserved entry after
  retired : RetiredCounterPresent after
  attempted : FlagRep after Elflings.canonicalDecoderGlobalsLayout.attempted true
  statusWord : Word32LERep after Elflings.canonicalDecoderGlobalsLayout.status 2
  storedTag : DecodedValue.OptionTagRep after
    (Elflings.canonicalDecoderGlobalsLayout.storedResult +
      Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) false

theorem first_invalid_prefix_mismatch_to_exit
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    (fromStep : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (firstInvalid : meaningDecodeRaw args.bytes = .error .invalidSsz)
    (fourBytes : 4 ≤ args.bytes.size) (notExact : meaningHasExactErePrefix args.bytes = false) :
    ∃ atDecode firstAfter branch retryBefore childAfter handoff afterTail afterStore after firstUsed retryUsed
      branchRetired retryRetired link s0 s1 s2,
      FirstInvalidPrefixMismatchToExitResult args stackBase fromStep entry atDecode firstAfter branch
        retryBefore childAfter handoff afterTail afterStore after firstUsed retryUsed branchRetired retryRetired link s0 s1 s2 := by
  obtain ⟨atDecode, firstAfter, branch, retryBefore, firstUsed, branchRetired, retryRetired, secondArgs,
    retryEntry⟩ := first_invalid_to_retry_entry allocator decode fromStep args stackBase entry source
      machine firstInvalid
  have secondArgsEq := retryEntry.secondArgsEq
  rcases retryEntry.savedFrame with ⟨link, s0, s1, s2, entryLink, savedAtRetry⟩
  have retryMachineEntry : ZesuDecodeRawMachinePre
      ⟨secondArgs.inputBase, secondArgs.bytes⟩ secondArgs.stackBase entry := by
    simpa [secondArgsEq] using machine
  have retryPhase : secondArgs.phase = .retryAfterInvalidSsz := by simp [secondArgsEq]
  have retryFourBytes : 4 ≤ secondArgs.bytes.size := by simpa [secondArgsEq] using fourBytes
  have retryNotExact : meaningHasExactErePrefix secondArgs.bytes = false := by
    simpa [secondArgsEq] using notExact
  have semanticResult : meaningDecode args.bytes = .error .invalidSsz := by
    rw [Contracts.meaningDecode, firstInvalid, notExact]
    rfl
  have savedAtRetry' : WrapperSavedRegisterFrame secondArgs.stackBase link s0 s1 s2 retryBefore := by
    simpa [secondArgsEq] using savedAtRetry
  obtain ⟨retryUsed, childAfter, handoff, afterTail, afterStore, after, retryExit⟩ :=
    retry_prefix_mismatch_rejection_to_exit retryMachineEntry retryEntry.retryWrapperMachine retryEntry.retryPre
      retryPhase retryFourBytes retryNotExact link s0 s1 s2 savedAtRetry'
  have scopedTrace : WrapperScopedTrace fromStep (19 + firstUsed + 2 + (retryUsed + 10)) entry after := by
    exact retryEntry.routePrefix _ after (by simpa [Nat.add_assoc] using retryExit.scopedTrace)
  have decoderAgree : Agree decoderPreserved entry after :=
    retryEntry.decoderAgree.trans retryExit.edge.handoffAgree |>.trans retryExit.suffix.epilogue.agree
  have platform : Agree platformPreserved entry after := by
    intro register preserved
    rcases preserved with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact retryExit.suffix.epilogue.ra.trans entryLink.symm
    all_goals exact decoderAgree _ ⟨by decide, by simp [platformPreserved]⟩
  have attempted : FlagRep after Elflings.canonicalDecoderGlobalsLayout.attempted true := by
    unfold FlagRep
    rw [show after.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted =
      retryBefore.mem.get? Elflings.canonicalDecoderGlobalsLayout.attempted from retryExit.globalsFrame.1]
    exact retryEntry.attempted
  have storedTag : DecodedValue.OptionTagRep after
      (Elflings.canonicalDecoderGlobalsLayout.storedResult +
        Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) false := by
    unfold DecodedValue.OptionTagRep
    rw [show after.mem.get?
        (Elflings.canonicalDecoderGlobalsLayout.storedResult +
          Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) =
        retryBefore.mem.get?
          (Elflings.canonicalDecoderGlobalsLayout.storedResult +
            Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) from
      retryExit.globalsFrame.2, retryEntry.storedDiscriminant]
    exact source.2.2.2.2.2.1
  refine ⟨atDecode, firstAfter, branch, retryBefore, childAfter, handoff, afterTail, afterStore, after,
    firstUsed, retryUsed, branchRetired, retryRetired, link, s0, s1, s2, ?_⟩
  exact ⟨by simpa [secondArgsEq] using retryEntry, by simpa [secondArgsEq, Nat.add_assoc] using retryExit,
    retryEntry.firstInvalidBound, retryExit.edge.prefixMismatchBound, scopedTrace, retryEntry.routePrefix,
    retryExit.pc, retryExit.a0, retryExit.a1, semanticResult,
    by simpa [secondArgsEq] using retryExit.inputMemory, retryExit.code, platform, retryExit.retired,
    attempted, retryExit.statusWord, storedTag⟩

end BinaryFv.Zesu.MachineExecution
