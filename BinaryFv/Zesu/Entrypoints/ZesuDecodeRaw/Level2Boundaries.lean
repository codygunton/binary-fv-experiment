import GeneratedProgram
import BinaryFv.RiscV.Elfling.Boundary

/-!
# Level 2 machine boundaries inside `zesu_decode_raw`

LLVM attributes two inlined source functions to the exported wrapper: `allocator` and `decode`.
Neither occupies one contiguous callable body. This file records every real edge by which execution
enters or leaves their attributed instructions. These are machine-code boundaries, not source ABIs.

The split matters immediately. The allocator occupies `0x102f0` and `0x102f8..0x10304`, separated
by the wrapper's store at `0x102f4`. The decoder likewise leaves and later re-enters its attributed
regions. A Level 2 proof must therefore summarize boundary-to-boundary segments; it may not pretend
that either inline instance is entered once and returns once.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Elflings.Generated

/-- Every crossing edge for the inlined allocator's two machine-code segments. -/
def allocatorInlineBoundary : InlineBoundary where
  child := functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41Id
  entries := #[⟨0x102ec, 0x102f0⟩, ⟨0x102f4, 0x102f8⟩]
  exits := #[⟨0x102f0, 0x102f4⟩, ⟨0x10304, 0x10308⟩]

/-- The allocator boundary agrees with the generated wrapper, child identity, and CFG edges. -/
theorem allocatorInlineBoundary_valid :
    allocatorInlineBoundary.validFor generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41 := by
  simp [allocatorInlineBoundary, InlineBoundary.validFor, InlineBoundary.acceptsEntry,
    programContainsEdge, FunctionInstance.containsAddress,
    BinaryFv.Binary.AddressRange.stop]
  <;> native_decide

/-- Both allocator segments are accepted entries; the second is not the source-level entry. -/
theorem allocatorInlineBoundary_entries :
    allocatorInlineBoundary.acceptsEntry
        functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
        0x102f0 ∧
      allocatorInlineBoundary.acceptsEntry
        functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
        0x102f8 := by
  simp [allocatorInlineBoundary, InlineBoundary.acceptsEntry]

/-- Every crossing edge for the two regions attributed to the inlined `decode`. -/
def decodeInlineBoundary : InlineBoundary where
  child := functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
  entries := #[⟨0x10304, 0x10308⟩, ⟨0x1037c, 0x10380⟩]
  exits := #[⟨0x10324, 0x1037c⟩, ⟨0x10380, 0x103fc⟩,
    ⟨0x10394, 0x10420⟩, ⟨0x103c4, 0x10420⟩, ⟨0x103f8, 0x103fc⟩]

/-- The decoder boundary agrees with the generated wrapper, child identity, and CFG edges. -/
theorem decodeInlineBoundary_valid :
    decodeInlineBoundary.validFor generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 := by
  simp [decodeInlineBoundary, InlineBoundary.validFor, InlineBoundary.acceptsEntry,
    programContainsEdge, FunctionInstance.containsAddress,
    BinaryFv.Binary.AddressRange.stop, functionInstance_raw_decoder_root_zesu_decode_raw,
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31]
  <;> native_decide

/-- Both decoder regions are accepted entries; the retry region is reached through a checked edge. -/
theorem decodeInlineBoundary_entries :
    decodeInlineBoundary.acceptsEntry
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 0x10308 ∧
      decodeInlineBoundary.acceptsEntry
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 0x10380 := by
  simp [decodeInlineBoundary, InlineBoundary.acceptsEntry]

/-! ## Calls to the one emitted Level 2 child

The compiled wrapper reaches the same emitted `memcpy` body at three call sites. Two call
instructions are attributed to inlined `decode`; the middle call is attributed directly to the
wrapper. Recording the actual owner at each site prevents the Level 2 proof from assigning all
three calls to whichever source-level nesting is most convenient.
-/

/-- Copy the first successful `decodeRaw` result into `decode`'s result slot. -/
def memcpyFirstDecodeResult : CallSite where
  source := 0x10338
  callee := functionInstance_memcpyId
  calleeEntry := 0x13eb8
  returnPc := 0x1033c

theorem memcpyFirstDecodeResult_valid :
    memcpyFirstDecodeResult.validFor generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_memcpy := by
  simp [memcpyFirstDecodeResult, CallSite.validFor, programContainsEdge,
    functionInstance_raw_decoder_root_zesu_decode_raw,
    functionInstance_memcpy, FunctionInstance.containsAddress, BinaryFv.Binary.AddressRange.stop]
  <;> native_decide

/-- The first `decode` segment can leave through the real `memcpy` call. The call and return are
not collapsed into the synthetic continuation edge `0x10338 → 0x1033c`. -/
def decodeFirstMemcpyExit : InlineCallBoundary where
  inline := decodeInlineBoundary
  call := memcpyFirstDecodeResult

theorem decodeFirstMemcpyExit_valid :
    decodeFirstMemcpyExit.validFor generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_memcpy := by
  refine ⟨decodeInlineBoundary_valid, memcpyFirstDecodeResult_valid, ?_, ?_⟩
  · native_decide
  · native_decide

/-- Copy `decode`'s successful result into the wrapper's private stored-result object. -/
def memcpyStoredResult : CallSite where
  source := 0x1034c
  callee := functionInstance_memcpyId
  calleeEntry := 0x13eb8
  returnPc := 0x10350

theorem memcpyStoredResult_valid :
    memcpyStoredResult.validFor generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_memcpy := by
  simp [memcpyStoredResult, CallSite.validFor, programContainsEdge,
    functionInstance_raw_decoder_root_zesu_decode_raw,
    functionInstance_memcpy, FunctionInstance.containsAddress, BinaryFv.Binary.AddressRange.stop]
  <;> native_decide

/-- Copy a successful ERE retry result into `decode`'s result slot. -/
def memcpyRetryDecodeResult : CallSite where
  source := 0x103ec
  callee := functionInstance_memcpyId
  calleeEntry := 0x13eb8
  returnPc := 0x103f0

theorem memcpyRetryDecodeResult_valid :
    memcpyRetryDecodeResult.validFor generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_memcpy := by
  simp [memcpyRetryDecodeResult, CallSite.validFor, programContainsEdge,
    functionInstance_raw_decoder_root_zesu_decode_raw,
    functionInstance_memcpy, FunctionInstance.containsAddress, BinaryFv.Binary.AddressRange.stop]
  <;> native_decide

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
