import BinaryFv.Zesu.MachineExecution.Level2FirstMemcpyInlineAdapter
import BinaryFv.Zesu.MachineExecution.Level2FirstSuccessExportFrame
import BinaryFv.Zesu.MachineExecution.Level2Tag0CopyToExit
import BinaryFv.Zesu.MachineExecution.Level2WrapperDecodeEntry

/-! The complete first-success route from the wrapper entry to its generated exit. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual first-success Level 2 route, retaining every typed boundary result and the exact
symbolic step count through the generated wrapper exit. -/
structure FirstSuccessToExitResult (args : ZesuDecodeRawArgs) (stackBase fromStep : Nat)
    (entry atDecode atCall resumed callState afterCopy routeAfter afterStore after : State)
    (value : BinaryFv.Specs.SSZ.StatelessInput) (contents : ByteArray)
    (link savedS0 savedS1 savedS2 : BitVec 64) (childUsed calleeUsed copyUsed : Nat) : Prop where
  semanticSuccess : meaningDecodeRaw args.bytes = .ok value
  wrapperTrace : Trace fromStep 19 entry atDecode
  wrapperPrefix : WrapperPrefix fromStep 19 entry atDecode
  decodeBody : level3DecodeChildSummary
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
    (fromStep + 19) childUsed atDecode atCall
  firstMemcpy : FirstMemcpyTransferFrame (fromStep + 19 + childUsed)
    { phase := .first, stackBase := stackBase, inputBase := args.inputBase, bytes := args.bytes }
    contents atDecode atCall calleeUsed resumed
  inlineTransfer : Nonempty (InlineCallTransfer
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary decodeFirstMemcpyExit generatedProgram
    functionInstance_raw_decoder_root_zesu_decode_raw
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
    functionInstance_memcpy (fromStep + 19) childUsed calleeUsed atDecode resumed)
  tag0 : Tag0CopyToExitResult args value stackBase entry resumed callState afterCopy routeAfter afterStore
    after contents link savedS0 savedS1 savedS2
    (fromStep + 19 + childUsed + 1 + calleeUsed + 1) copyUsed
  decodeBound : childUsed ≤ 16384 + 512 * args.bytes.size + 13
  totalSteps : 19 + childUsed + 1 + calleeUsed + 1 + (16 + copyUsed) =
    37 + childUsed + calleeUsed + copyUsed
  scopedTrace : WrapperScopedTrace fromStep (37 + childUsed + calleeUsed + copyUsed) entry after
  exitPc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  exitResult : after.regs.get? x10 = some (BitVec.ofNat 64 1)
  exitStatus : after.regs.get? x11 = some (BitVec.ofNat 64 1)
  inputMemory : DecodedValue.MemoryBytes after args.inputBase args.bytes
  platform : Agree platformPreserved entry after
  exportFrame : FirstSuccessExportFrame args value entry after

/-- Compose the proved wrapper prefix, selected Level 3 success body, real `memcpy` transfer, and
tag-zero suffix. No address, ABI, link, PC, or frame fact is an extra premise. -/
theorem first_success_to_exit
    (allocator : AllocatorInlineContract) (decode : Level3DecodeInlineContract)
    (memcpy : CompiledMemcpyInstanceContract)
    (fromStep : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (value : BinaryFv.Specs.SSZ.StatelessInput)
    (success : meaningDecodeRaw args.bytes = .ok value) :
    ∃ atDecode atCall contents childUsed calleeUsed resumed link savedS0 savedS1 savedS2 copyUsed
      callState afterCopy routeAfter afterStore after,
      FirstSuccessToExitResult args stackBase fromStep entry atDecode atCall resumed callState
        afterCopy routeAfter afterStore after value contents link savedS0 savedS1 savedS2 childUsed
        calleeUsed copyUsed := by
  obtain ⟨atDecode, wrapperTrace, wrapperPrefix, decodeArgs, decodeArgsEq, pre, entryAgree,
    attemptedAtDecode, -, childUsed, atCall, -, decodeBody, -, firstSuccessBound, -, -, post, machinePost, outgoing, saveArea,
    firstSuccessAllocation, -, globalsAtCall, savedFrame⟩ :=
    wrapper_reaches_decode_first_contract allocator decode fromStep args stackBase entry source
      machine
  have phase : decodeArgs.phase = .first := by simp [decodeArgsEq]
  have firstPost : DecodeInlineFirstPost decodeArgs atDecode atCall := by
    simpa [DecodeInlinePost, phase] using post
  have success' : meaningDecodeRaw decodeArgs.bytes = .ok value := by
    simpa [decodeArgsEq] using success
  obtain ⟨contents, calleeUsed, resumed, firstMemcpy⟩ :=
    first_memcpy_transfer_frame_of_first_post memcpy (fromStep + 19 + childUsed) decodeArgs
      atDecode atCall pre value success' firstPost machinePost phase outgoing saveArea
      firstSuccessAllocation
  have inlineTransfer := decode_first_success_inlineCallTransfer decodeArgs contents pre phase
    decodeBody firstMemcpy
  obtain ⟨link, savedS0, savedS1, savedS2, entryLink, -, -, -, frame⟩ := savedFrame
  obtain ⟨copyUsed, callState, afterCopy, tag0Phase⟩ :=
    tag0_stored_result_copy_phase_of_first_success decodeArgs contents memcpy link savedS0 savedS1
      savedS2 machine decodeArgsEq success entryAgree firstMemcpy frame
      (fromStep + 19 + childUsed + 1 + calleeUsed + 1)
  obtain ⟨routeAfter, afterStore, after, tag0⟩ :=
    tag0_copy_to_exit contents link savedS0 savedS1 savedS2 tag0Phase
  have decodeStack : decodeArgs.stackBase = stackBase := by simp [decodeArgsEq]
  have attemptedAddress : Elflings.canonicalDecoderGlobalsLayout.attempted = 0x4215020 := by
    native_decide
  have storedTagAddress : Elflings.canonicalDecoderGlobalsLayout.storedResult +
      Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset = 0x4215370 := by
    native_decide
  have stackAboveGlobals : 0x4215028 ≤ stackBase → 0x4215380 ≤ stackBase := by
    intro stackAbove
    apply Nat.le_of_not_gt
    intro notAbove
    have stackByte : canonicalContractParams.env.stack stackBase :=
      machine.stackFrameWritable 0 (by omega)
    exact canonicalStack_disjoint_from_globals stackBase (by
      have globalsCeiling : Entrypoints.ZesuDecodeRaw.globalsCeiling = 0x4215380 := by native_decide
      rw [globalsCeiling]
      omega) (by simpa [canonicalContractParams, canonicalEnvironment] using stackByte)
  have firstMemcpyGlobals : DecoderGlobalsBoundaryFrame atCall resumed := by
    constructor
    · rw [firstMemcpy.copyFrame Elflings.canonicalDecoderGlobalsLayout.attempted (by
        rw [attemptedAddress]
        change 0x4215020 < decodeArgs.stackBase + 32 ∨ decodeArgs.stackBase + 32 + 832 ≤ 0x4215020
        rw [decodeStack]
        rcases machine.stackAvoidsStatusGlobals with stackBelow | stackAbove
        · right
          omega
        · left
          have aboveGlobals := stackAboveGlobals stackAbove
          omega)]
    · rw [firstMemcpy.copyFrame
        (Elflings.canonicalDecoderGlobalsLayout.storedResult +
          Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset)
        (by
          rw [storedTagAddress]
          change 0x4215370 < decodeArgs.stackBase + 32 ∨ decodeArgs.stackBase + 32 + 832 ≤ 0x4215370
          rw [decodeStack]
          rcases machine.stackAvoidsStatusGlobals with stackBelow | stackAbove
          · right
            omega
          · left
            have aboveGlobals := stackAboveGlobals stackAbove
            omega)]
  have tail : WrapperScopedTrace (fromStep + 19)
      (childUsed + 1 + calleeUsed + 1 + (16 + copyUsed)) atDecode after := by
    rcases inlineTransfer with ⟨transfer⟩
    exact ScopedTrace.inlineCallStep (fromStep + 19) childUsed calleeUsed (16 + copyUsed)
      decodeFirstMemcpyExit generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_memcpy atDecode resumed after transfer (by
        simpa [Nat.add_assoc] using tag0.scopedTrace)
  have scopedTrace : WrapperScopedTrace fromStep (37 + childUsed + calleeUsed + copyUsed)
      entry after := by
    have complete := wrapperPrefix
      (childUsed + 1 + calleeUsed + 1 + (16 + copyUsed)) after tail
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using complete
  have decoderAgree : Agree decoderPreserved entry after :=
    entryAgree.trans firstMemcpy.decoder |>.trans tag0.copy.platform |>.trans tag0.epilogue.agree
  have platform : Agree platformPreserved entry after := by
    intro register preserved
    rcases preserved with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tag0.epilogue.ra.trans entryLink.symm
    all_goals exact decoderAgree _ ⟨by decide, by simp [platformPreserved]⟩
  have attempted : FlagRep after Elflings.canonicalDecoderGlobalsLayout.attempted true := by
    unfold FlagRep
    rw [tag0.attemptedFrame, firstMemcpyGlobals.1, globalsAtCall.1]
    exact attemptedAtDecode
  have exportFrame : FirstSuccessExportFrame args value entry after :=
    { inputMemory := tag0.inputMemory
      code := tag0.epilogue.code
      returnCode := tag0.epilogue.a0
      platform
      retired := tag0.epilogue.retired
      attempted
      status := tag0.statusWord
      storedTag := tag0.storedTag
      storedValue := by
        obtain ⟨cursorBefore, cursorAfter, representation⟩ := tag0.representation
        exact representation.representation }
  refine ⟨atDecode, atCall, contents, childUsed, calleeUsed, resumed, link, savedS0, savedS1,
    savedS2, copyUsed, callState, afterCopy, routeAfter, afterStore, after, ?_⟩
  exact ⟨success, wrapperTrace, wrapperPrefix, decodeBody,
    by simpa [decodeArgsEq] using firstMemcpy, inlineTransfer, tag0,
    by simpa [decodeArgsEq] using firstSuccessBound value success', by omega, scopedTrace,
    tag0.epilogue.pc, tag0.epilogue.a0, tag0.epilogue.a1, tag0.inputMemory, platform, exportFrame⟩

end BinaryFv.Zesu.MachineExecution
