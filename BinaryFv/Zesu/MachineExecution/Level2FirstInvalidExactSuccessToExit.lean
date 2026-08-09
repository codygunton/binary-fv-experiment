import BinaryFv.Zesu.MachineExecution.Level2FirstInvalidRetryEntry
import BinaryFv.Zesu.MachineExecution.Level2FirstSuccessExportFrame
import BinaryFv.Zesu.MachineExecution.Level2RetryExactToExit

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

structure FirstInvalidExactSuccessToExitResult (args : ZesuDecodeRawArgs) (stackBase fromStep : Nat)
    (entry atDecode firstAfter branch retryBefore childAfter dispatch copyStart callState afterCopy routeAfter afterStore after : State)
    (firstUsed retryUsed copyUsed : Nat) (branchRetired retryRetired link s0 s1 s2 : BitVec 64)
    (value : BinaryFv.Specs.SSZ.StatelessInput) (contents : ByteArray) : Prop where
  retryEntry : FirstInvalidRetryEntryResult args stackBase fromStep entry atDecode firstAfter branch retryBefore
    firstUsed branchRetired retryRetired
      ⟨.retryAfterInvalidSsz, stackBase, args.inputBase, args.bytes⟩
  retryExit : RetryExactSuccessToExitResult
    ⟨.retryAfterInvalidSsz, stackBase, args.inputBase, args.bytes⟩
    (fromStep + 19 + firstUsed + 2) retryUsed entry retryBefore childAfter dispatch copyStart callState afterCopy
    routeAfter afterStore after value contents link s0 s1 s2 copyUsed
  firstInvalidBound : firstUsed ≤ 5927 + 512 * args.bytes.size
  retryExactBound : retryUsed ≤ 16384 + 512 * (args.bytes.extract 4 args.bytes.size).size + 6765
  exactPrefix : meaningHasExactErePrefix args.bytes = true
  copyBound : copyUsed ≤ 64 + 8 * 832
  scopedTrace : WrapperScopedTrace fromStep (19 + firstUsed + 2 + (retryUsed + 23 + copyUsed)) entry after
  exitPc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  exitResult : after.regs.get? x10 = some (BitVec.ofNat 64 1)
  exitStatus : after.regs.get? x11 = some (BitVec.ofNat 64 1)
  semanticResult : meaningDecode args.bytes = .ok value
  inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes
  code : canonicalContractParams.env.CodeIntact after
  platform : Agree platformPreserved entry after
  retired : RetiredCounterPresent after
  attempted : FlagRep after Elflings.canonicalDecoderGlobalsLayout.attempted true
  statusWord : Word32LERep after Elflings.canonicalDecoderGlobalsLayout.status 1
  storedTag : DecodedValue.OptionTagRep after
    (Elflings.canonicalDecoderGlobalsLayout.storedResult +
      Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset) true
  storedValue : canonicalContractParams.repStatelessInput args.inputBase args.bytes value after
    canonicalContractParams.resultBuffer
  exportFrame : FirstSuccessExportFrame args value entry after

theorem first_invalid_exact_success_to_exit
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    (memcpy : CompiledMemcpyInstanceContract) (fromStep : Nat)
    (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (firstInvalid : meaningDecodeRaw args.bytes = .error .invalidSsz)
    (exactPrefix : meaningHasExactErePrefix args.bytes = true) (value : BinaryFv.Specs.SSZ.StatelessInput)
    (semanticSuccess : meaningDecode args.bytes = .ok value) :
    ∃ atDecode firstAfter branch retryBefore childAfter dispatch copyStart contents copyUsed callState afterCopy routeAfter afterStore after
      firstUsed retryUsed branchRetired retryRetired link s0 s1 s2,
      FirstInvalidExactSuccessToExitResult args stackBase fromStep entry atDecode firstAfter branch retryBefore childAfter dispatch
        copyStart callState afterCopy routeAfter afterStore after firstUsed retryUsed copyUsed branchRetired retryRetired link s0 s1 s2 value contents := by
  obtain ⟨atDecode, firstAfter, branch, retryBefore, firstUsed, branchRetired, retryRetired, secondArgs, retryEntry⟩ :=
    first_invalid_to_retry_entry allocator decode fromStep args stackBase entry source machine firstInvalid
  have argsEq := retryEntry.secondArgsEq
  rcases retryEntry.savedFrame with ⟨link, s0, s1, s2, entryLink, saved⟩
  have phase : secondArgs.phase = .retryAfterInvalidSsz := by simp [argsEq]
  have exact : meaningHasExactErePrefix secondArgs.bytes = true := by simpa [argsEq] using exactPrefix
  have success : meaningDecode secondArgs.bytes = .ok value := by simpa [argsEq] using semanticSuccess
  have saved' : WrapperSavedRegisterFrame secondArgs.stackBase link s0 s1 s2 retryBefore := by simpa [argsEq] using saved
  have entryMachine : ZesuDecodeRawMachinePre ⟨secondArgs.inputBase, secondArgs.bytes⟩ secondArgs.stackBase entry := by simpa [argsEq] using machine
  obtain ⟨retryUsed, childAfter, dispatch, handoff⟩ :=
    retry_exact_tag_handoff decode (fromStep + 19 + firstUsed + 2) secondArgs entryMachine retryBefore
      retryEntry.retryPre phase exact link s0 s1 s2 saved'
  obtain ⟨copyStart, contents, copyUsed, callState, afterCopy, routeAfter, afterStore, after, retryExit⟩ :=
    retry_exact_success_handoff_to_exit memcpy entryMachine retryEntry.retryWrapperMachine link s0 s1
      s2 handoff phase exact value success
  have scopedTrace : WrapperScopedTrace fromStep (19 + firstUsed + 2 + (retryUsed + 23 + copyUsed)) entry after :=
    retryEntry.routePrefix _ after (by simpa [Nat.add_assoc] using retryExit.scopedTrace)
  have routeDecoder : Agree decoderPreserved dispatch copyStart := by
    intro register preserved
    exact retryExit.dispatchRoute.platform register preserved.2
  have decoderAgree : Agree decoderPreserved entry after :=
    retryEntry.decoderAgree.trans retryExit.handoff.machineAgree |>.trans routeDecoder |>.trans
      retryExit.copy.copy.platform |>.trans retryExit.copy.epilogue.agree
  have platform : Agree platformPreserved entry after := by
    intro register preserved
    rcases preserved with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact retryExit.copy.epilogue.ra.trans entryLink.symm
    all_goals exact decoderAgree _ ⟨by decide, by simp [platformPreserved]⟩
  have attempted : FlagRep after Elflings.canonicalDecoderGlobalsLayout.attempted true := by
    unfold FlagRep
    rw [retryExit.copy.attemptedFrame, retryExit.dispatchRoute.memory,
      retryExit.handoff.globalsFrame.1]
    exact retryEntry.attempted
  have inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes := by
    simpa [argsEq] using retryExit.copy.inputMemory
  have storedValue : canonicalContractParams.repStatelessInput args.inputBase args.bytes value after
      canonicalContractParams.resultBuffer := by
    obtain ⟨cursorBefore, cursorAfter, representation⟩ := retryExit.copy.representation
    simpa [argsEq] using representation.representation
  have exportFrame : FirstSuccessExportFrame args value entry after :=
    { inputMemory
      code := retryExit.copy.epilogue.code
      returnCode := retryExit.exitResult
      platform
      retired := retryExit.copy.epilogue.retired
      attempted
      status := retryExit.statusWord
      storedTag := retryExit.copy.storedTag
      storedValue }
  exact ⟨atDecode, firstAfter, branch, retryBefore, childAfter, dispatch, copyStart, contents, copyUsed, callState, afterCopy, routeAfter, afterStore, after,
    firstUsed, retryUsed, branchRetired, retryRetired, link, s0, s1, s2,
    ⟨by simpa [argsEq] using retryEntry, by simpa [argsEq] using retryExit,
      retryEntry.firstInvalidBound,
      by simpa [argsEq, DecodeInlineArgs.retryRawArgs] using retryExit.handoff.retryExactBound,
      exactPrefix, retryExit.copy.copy.copyBound, scopedTrace,
      retryExit.exitPc, retryExit.exitResult, retryExit.exitStatus, semanticSuccess, inputMemory,
      retryExit.copy.epilogue.code, platform, retryExit.copy.epilogue.retired, attempted,
      retryExit.statusWord, retryExit.copy.storedTag, storedValue, exportFrame⟩⟩

end BinaryFv.Zesu.MachineExecution
