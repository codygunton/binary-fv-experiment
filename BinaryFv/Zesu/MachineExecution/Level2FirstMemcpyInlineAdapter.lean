import BinaryFv.Zesu.MachineExecution.Level2FirstMemcpyTransfer

/-!
# First `decode` success at its real `memcpy` exit

The first inlined `decode` segment stops at the emitted `memcpy` call.  This adapter preserves that
call and its return as an `InlineCallTransfer`; it does not invent a direct edge to `0x1033c`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

/-- A successful first Level 3 `decode` segment and its checked emitted `memcpy` call/return form
the Level 2 inline-call transfer at `decodeFirstMemcpyExit`. -/
theorem decode_first_success_inlineCallTransfer
    {fromStep childUsed calleeUsed : Nat} {before atCall resumed : State}
    (args : DecodeInlineArgs) (contents : ByteArray)
    (pre : DecodeInlinePre args before) (phase : args.phase = .first)
    (body : level3DecodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      fromStep childUsed before atCall)
    (firstFrame : FirstMemcpyTransferFrame (fromStep + childUsed) args contents before atCall
      calleeUsed resumed) :
    Nonempty (InlineCallTransfer
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary decodeFirstMemcpyExit generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_memcpy fromStep childUsed calleeUsed before resumed) := by
  rcases firstFrame.transfer with ⟨call⟩
  refine ⟨{
    valid := decodeFirstMemcpyExit_valid
    entryPc := args.entryPc
    atEntry := pre.atEntry
    entryAccepted := decodeInline_entry_accepted args
    entryInRegion := ?_
    entryNotExit := ?_
    sCallSite := atCall
    body := .decode body
    call := call }⟩
  · have entryInRegion : functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10308) := by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide
    simpa [DecodeInlineArgs.entryPc, phase] using entryInRegion
  · simp [DecodeInlineArgs.entryPc, phase, functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]

end BinaryFv.Zesu.MachineExecution
