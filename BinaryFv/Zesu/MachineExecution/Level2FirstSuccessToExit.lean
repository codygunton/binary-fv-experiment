import BinaryFv.Zesu.MachineExecution.Level2FirstMemcpyInlineAdapter
import BinaryFv.Zesu.MachineExecution.Level2Tag0CopyToExit

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
    (value : BinaryFv.Specs.SSZ.RawV4) (contents : ByteArray)
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
  tag0 : Tag0CopyToExitResult args stackBase entry resumed callState afterCopy routeAfter afterStore
    after contents link savedS0 savedS1 savedS2
    (fromStep + 19 + childUsed + 1 + calleeUsed + 1) copyUsed
  totalSteps : 19 + childUsed + 1 + calleeUsed + 1 + (16 + copyUsed) =
    37 + childUsed + calleeUsed + copyUsed
  scopedTrace : WrapperScopedTrace fromStep (37 + childUsed + calleeUsed + copyUsed) entry after
  exitPc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  exitResult : after.regs.get? x10 = some (BitVec.ofNat 64 1)
  exitStatus : after.regs.get? x11 = some (BitVec.ofNat 64 1)

/-- Compose the proved wrapper prefix, selected Level 3 success body, real `memcpy` transfer, and
tag-zero suffix. No address, ABI, link, PC, or frame fact is an extra premise. -/
theorem first_success_to_exit
    (allocator : AllocatorInlineContract) (decodeRaw : CompiledDecodeRawInstanceContract)
    (fromStep : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (value : BinaryFv.Specs.SSZ.RawV4)
    (success : meaningDecodeRaw args.bytes = .ok value) :
    ∃ atDecode atCall contents childUsed calleeUsed resumed link savedS0 savedS1 savedS2 copyUsed
      callState afterCopy routeAfter afterStore after,
      FirstSuccessToExitResult args stackBase fromStep entry atDecode atCall resumed callState
        afterCopy routeAfter afterStore after value contents link savedS0 savedS1 savedS2 childUsed
        calleeUsed copyUsed := by
  obtain ⟨atDecode, wrapperTrace, wrapperPrefix, decodeArgs, decodeArgsEq, pre, entryAgree,
    childUsed, atCall, -, decodeBody, -, -, post, machinePost, outgoing, saveArea, savedFrame⟩ :=
    wrapper_reaches_decode_first_contract allocator decodeRaw fromStep args stackBase entry source
      machine
  have phase : decodeArgs.phase = .first := by simp [decodeArgsEq]
  have firstPost : DecodeInlineFirstPost decodeArgs atDecode atCall := by
    simpa [DecodeInlinePost, phase] using post
  have success' : meaningDecodeRaw decodeArgs.bytes = .ok value := by
    simpa [decodeArgsEq] using success
  obtain ⟨contents, calleeUsed, resumed, firstMemcpy⟩ :=
    first_memcpy_transfer_frame_of_first_post (fromStep + 19 + childUsed) decodeArgs atDecode atCall
      pre value success' firstPost machinePost phase outgoing saveArea
  have inlineTransfer := decode_first_success_inlineCallTransfer decodeArgs contents pre phase
    decodeBody firstMemcpy
  obtain ⟨link, savedS0, savedS1, savedS2, -, -, -, -, frame⟩ := savedFrame
  obtain ⟨copyUsed, callState, afterCopy, tag0Phase⟩ :=
    tag0_stored_result_copy_phase_of_first_success decodeArgs contents link savedS0 savedS1 savedS2
      machine decodeArgsEq entryAgree firstMemcpy frame
      (fromStep + 19 + childUsed + 1 + calleeUsed + 1)
  obtain ⟨routeAfter, afterStore, after, tag0⟩ :=
    tag0_copy_to_exit contents link savedS0 savedS1 savedS2 tag0Phase
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
  refine ⟨atDecode, atCall, contents, childUsed, calleeUsed, resumed, link, savedS0, savedS1,
    savedS2, copyUsed, callState, afterCopy, routeAfter, afterStore, after, ?_⟩
  exact ⟨success, wrapperTrace, wrapperPrefix, decodeBody,
    by simpa [decodeArgsEq] using firstMemcpy, inlineTransfer, tag0, by omega, scopedTrace,
    tag0.epilogue.pc, tag0.epilogue.a0, tag0.epilogue.a1⟩

end BinaryFv.Zesu.MachineExecution
