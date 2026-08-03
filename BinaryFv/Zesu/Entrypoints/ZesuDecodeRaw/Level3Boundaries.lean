import GeneratedProgram
import BinaryFv.RiscV.Elfling.Boundary

/-!
# Level 3 machine boundaries inside inlined `decode`

These are the three ordinary calls crossed while proving the `decode` scope: two calls to the one
emitted `decodeRaw` instance and the retry-success call to emitted `memcpy`. The first-success
`memcpy` instruction is instead a generated exit of inlined `decode`, so its enclosing Level 2
transfer owns that call.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary.Elfling BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Elflings.Generated

def decodeRawFirstAttemptCall : CallSite where
  source := 0x1031c
  callee := functionInstance_ssz_raw_decodeRawId
  calleeEntry := 0x10444
  returnPc := 0x10320

theorem decodeRawFirstAttemptCall_valid :
    decodeRawFirstAttemptCall.validFor generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_ssz_raw_decodeRaw := by
  simp [decodeRawFirstAttemptCall, CallSite.validFor, programContainsEdge,
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31,
    functionInstance_ssz_raw_decodeRaw, FunctionInstance.containsAddress,
    BinaryFv.Binary.AddressRange.stop]
  <;> native_decide

def decodeRawRetryCall : CallSite where
  source := 0x103d8
  callee := functionInstance_ssz_raw_decodeRawId
  calleeEntry := 0x10444
  returnPc := 0x103dc

theorem decodeRawRetryCall_valid :
    decodeRawRetryCall.validFor generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_ssz_raw_decodeRaw := by
  simp [decodeRawRetryCall, CallSite.validFor, programContainsEdge,
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31,
    functionInstance_ssz_raw_decodeRaw, FunctionInstance.containsAddress,
    BinaryFv.Binary.AddressRange.stop]
  <;> native_decide

def memcpyRetryCall : CallSite where
  source := 0x103ec
  callee := functionInstance_memcpyId
  calleeEntry := 0x13eb8
  returnPc := 0x103f0

theorem memcpyRetryCall_valid :
    memcpyRetryCall.validFor generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_memcpy := by
  simp [memcpyRetryCall, CallSite.validFor, programContainsEdge,
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31,
    functionInstance_memcpy, FunctionInstance.containsAddress,
    BinaryFv.Binary.AddressRange.stop]
  <;> native_decide

/-- The inlined prefix helper is a real generated child of this exact `decode` instance. Its body
summaries are consumed by `ScopedTrace.childBody`; the parent then executes each outgoing branch. -/
theorem hasExactErePrefix_is_decode_child :
    functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35Id ∈
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31.children := by
  native_decide

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
