import BinaryFv.Zesu.MachineExecution.Level2FirstMemcpyTransfer
import BinaryFv.Zesu.MachineExecution.Level2Tag0Success

/-!
# First-success adapter for the tag-zero stored-result copy

This module connects the first inlined `decode` success through its real emitted `memcpy` return
to the wrapper-owned stored-result copy at `0x1033c`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Adapt the first-phase `decode` result and its actual first `memcpy` return into the precise
wrapper frame at `0x1033c` that begins the tag-zero stored-result copy. -/
theorem tag0_stored_result_copy_pre_of_first_success
    {args : ZesuDecodeRawArgs} {value : BinaryFv.Specs.SSZ.StatelessInput} {stackBase : Nat}
    {entry atDecode atCall resumed : State}
    {fromStep childUsed : Nat}
    (decodeArgs : DecodeInlineArgs) (contents : ByteArray)
    (link savedS0 savedS1 savedS2 : BitVec 64)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (decodeArgsFirst : decodeArgs =
      { phase := .first, stackBase := stackBase, inputBase := args.inputBase, bytes := args.bytes })
    (success : meaningDecodeRaw args.bytes = .ok value)
    (entryAgree : Agree decoderPreserved entry atDecode)
    (firstFrame : FirstMemcpyTransferFrame
      fromStep decodeArgs contents atDecode atCall childUsed resumed)
    (savedFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 atDecode) :
    Tag0StoredResultCopyPre args value stackBase entry resumed contents link savedS0 savedS1 savedS2 := by
  have parentMachine := machine.machine.mono (entryAgree.trans firstFrame.decoder)
    firstFrame.retiredCounter
  have resumedFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 resumed := by
    have savedFrameAtDecode :
        WrapperSavedRegisterFrame decodeArgs.stackBase link savedS0 savedS1 savedS2 atDecode := by
      simpa [decodeArgsFirst] using savedFrame
    have frameAfter := WrapperSavedRegisterFrame.of_decode_inline_caller_save_area savedFrameAtDecode
      firstFrame.callerSaveArea
    simpa [decodeArgsFirst] using frameAfter
  have decodeSuccess : meaningDecodeRaw decodeArgs.bytes = .ok value := by
    simpa [decodeArgsFirst] using success
  obtain ⟨frameValue, cursorBefore, cursorAfter, frameSuccess, representation, cursorBound⟩ :=
    firstFrame.destinationRepresentation
  have frameValueEq : frameValue = value :=
    Except.ok.inj (frameSuccess.symm.trans decodeSuccess)
  subst frameValue
  refine ⟨machine, firstFrame.atResume, ?_, firstFrame.retiredCounter, firstFrame.code,
    ?_, firstFrame.globalsValue, resumedFrame, ?_, firstFrame.contentsSize, ?_, ?_⟩
  · simpa [decodeArgsFirst, DecodeInlineArgs.machineArgs, zesuDecodeRawMachineArgs] using parentMachine
  · simpa [decodeArgsFirst] using firstFrame.stackValue
  · simpa [decodeArgsFirst, DecodeInlineArgs.finalResultBase] using firstFrame.destinationMemory
  · exact ⟨cursorBefore, cursorAfter,
      by simpa [decodeArgsFirst, DecodeInlineArgs.finalResultBase] using representation, cursorBound⟩
  · have inputAtCall : DecodedValue.MemoryBytes atCall args.inputBase args.bytes := by
      simpa [decodeArgsFirst] using firstFrame.inputAtCall
    apply inputAtCall.of_mem_eq
    intro index indexBound
    rw [firstFrame.copyFrame (args.inputBase + index) (by
      rcases machine.inputAvoidsStack with inputBefore | stackBefore
      · left
        simp [firstMemcpyCopyArgs, decodeArgsFirst, DecodeInlineArgs.finalResultBase]
        omega
      · right
        simp [firstMemcpyCopyArgs, decodeArgsFirst, DecodeInlineArgs.finalResultBase]
        omega)]

/-- Execute the exact tag-zero stored-result-copy phase immediately after adapting a first success. -/
theorem tag0_stored_result_copy_phase_of_first_success
    {args : ZesuDecodeRawArgs} {value : BinaryFv.Specs.SSZ.StatelessInput} {stackBase : Nat}
    {entry atDecode atCall resumed : State}
    {firstFromStep childUsed : Nat}
    (decodeArgs : DecodeInlineArgs) (contents : ByteArray)
    (memcpy : CompiledMemcpyInstanceContract)
    (link savedS0 savedS1 savedS2 : BitVec 64)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (decodeArgsFirst : decodeArgs =
      { phase := .first, stackBase := stackBase, inputBase := args.inputBase, bytes := args.bytes })
    (success : meaningDecodeRaw args.bytes = .ok value)
    (entryAgree : Agree decoderPreserved entry atDecode)
    (firstFrame : FirstMemcpyTransferFrame
      firstFromStep decodeArgs contents atDecode atCall childUsed resumed)
    (savedFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 atDecode)
    (fromStep : Nat) :
    ∃ used callState afterCopy,
      Tag0StoredResultCopyPhase args value stackBase entry resumed contents link savedS0 savedS1 savedS2
        fromStep used callState afterCopy :=
  tag0_stored_result_copy_phase memcpy contents link savedS0 savedS1 savedS2
    (tag0_stored_result_copy_pre_of_first_success decodeArgs contents link savedS0 savedS1 savedS2
      machine decodeArgsFirst success entryAgree firstFrame savedFrame)
    fromStep

end BinaryFv.Zesu.MachineExecution
