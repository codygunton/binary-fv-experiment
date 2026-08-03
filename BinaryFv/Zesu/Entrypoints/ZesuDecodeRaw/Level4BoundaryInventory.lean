import GeneratedProgram

/-!
# Exact Level 4 stopping boundaries

The next refinement of emitted `decodeRaw` stops at these eight *inlined* function instances.
They are not callable ABI boundaries.  This module deliberately records only facts supplied by the
pinned generated hierarchy: function identity, owner, entry, regions, and exits remain fields of
the selected `FunctionInstance` values.

The source-level contracts in `Contracts/Containers.lean` and
`Contracts/PrimitiveReadsAndSlices.lean` cannot yet be made instance contracts here: the
entry-state/result-record adapters, write sets, preserved registers, and per-instance bounds have
not been extracted.  Naming those clauses without that evidence would be a new assumption.

The existing production vectors do measure accepted/rejected exported outcomes, formatted values on
accepted cases, and entry into each specialized decoder.  They do *not* measure any selected
instance's result/error record, its exact writes, its preserved machine frame, its exit reached, or
its step bound.  A decoder-entry hit is therefore not evidence for those clauses.  This checkpoint
adds production-trace reachability for the four direct `readOffset` entries only; it intentionally
does not claim `readOffset` values or frame preservation.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary.Elfling
open BinaryFv.Zesu.Elflings.Generated

/-- The four direct `readOffset` occurrences in emitted `decodeRaw`, in source call order. -/
def decodeRawDirectReadOffsetInstances : List FunctionInstance :=
  [ functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_199_23
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_200_23
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_201_23
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_202_23
  ]

/-- The four direct specialized decoder occurrences in emitted `decodeRaw`, in source call order. -/
def decodeRawSpecializedDecoderInstances : List FunctionInstance :=
  [ functionInstance_ssz_raw_decodeNewPayloadRequest_in_ssz_raw_decodeRaw_at_207_61
  , functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48
  , functionInstance_ssz_raw_decodeChainConfig_in_ssz_raw_decodeRaw_at_211_48
  , functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46
  ]

/-- The exact selected children, with no nested reader occurrence included. -/
def level4BoundaryInstances : List FunctionInstance :=
  decodeRawDirectReadOffsetInstances ++ decodeRawSpecializedDecoderInstances

theorem decodeRawDirectReadOffsetInstances_count : decodeRawDirectReadOffsetInstances.length = 4 := rfl

theorem decodeRawSpecializedDecoderInstances_count :
    decodeRawSpecializedDecoderInstances.length = 4 := rfl

theorem level4BoundaryInstances_count : level4BoundaryInstances.length = 8 := rfl

theorem decodeRawDirectReadOffsetInstances_are_direct_children :
    decodeRawDirectReadOffsetInstances.map (·.parent?) =
      [some functionInstance_ssz_raw_decodeRawId, some functionInstance_ssz_raw_decodeRawId,
        some functionInstance_ssz_raw_decodeRawId, some functionInstance_ssz_raw_decodeRawId] := rfl

theorem decodeRawSpecializedDecoderInstances_are_direct_children :
    decodeRawSpecializedDecoderInstances.map (·.parent?) =
      [some functionInstance_ssz_raw_decodeRawId, some functionInstance_ssz_raw_decodeRawId,
        some functionInstance_ssz_raw_decodeRawId, some functionInstance_ssz_raw_decodeRawId] := rfl

/-- Pin the entries of the four `readOffset` instances. Their exit sets and regions remain on the
selected instances, so this does not hide their non-contiguous generated bodies. -/
theorem decodeRawDirectReadOffsetEntries :
    decodeRawDirectReadOffsetInstances.map (·.entryPc) = [0x10534, 0x10544, 0x10568, 0x105a0] := rfl

/-- Pin the entries of the four specialized decoder instances. -/
theorem decodeRawSpecializedDecoderEntries :
    decodeRawSpecializedDecoderInstances.map (·.entryPc) = [0x1060c, 0x12710, 0x1294c, 0x12ebc] := rfl

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
