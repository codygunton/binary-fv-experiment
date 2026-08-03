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

open BinaryFv.Binary
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

theorem decodeRawDirectReadOffsetInstances_count :
    decodeRawDirectReadOffsetInstances.length = 4 := rfl

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
    decodeRawSpecializedDecoderInstances.map (·.entryPc) =
      [0x1060c, 0x12710, 0x1294c, 0x12ebc] := rfl

/-- Exact generated code fragments, in the same order as `level4BoundaryInstances`.
These are ownership fragments, not a claim that the whole dynamic execution is contiguous. -/
theorem level4BoundaryRegions :
    level4BoundaryInstances.map (·.regions) =
      [ #[{ start := 0x10534, size := 16 }, { start := 0x10554, size := 20 },
            { start := 0x105c4, size := 4 }]
      , #[{ start := 0x10544, size := 16 }, { start := 0x10578, size := 12 },
            { start := 0x10590, size := 8 }, { start := 0x105c8, size := 4 }]
      , #[{ start := 0x10568, size := 16 }, { start := 0x10584, size := 12 },
            { start := 0x10598, size := 8 }, { start := 0x105cc, size := 4 }]
      , #[{ start := 0x105a0, size := 36 }, { start := 0x105d0, size := 4 }]
      , #[{ start := 0x1060c, size := 8 }, { start := 0x1061c, size := 28 },
            { start := 0x10644, size := 240 }, { start := 0x10760, size := 5188 },
            { start := 0x11bac, size := 2892 }, { start := 0x12744, size := 80 }]
      , #[{ start := 0x12710, size := 16 }, { start := 0x12728, size := 12 },
            { start := 0x127a0, size := 360 }, { start := 0x1290c, size := 24 },
            { start := 0x12ffc, size := 52 }]
      , #[{ start := 0x1294c, size := 4 }, { start := 0x1295c, size := 104 },
            { start := 0x129f8, size := 1132 }]
      , #[{ start := 0x12ebc, size := 212 }, { start := 0x12fac, size := 32 }]
      ] := rfl

/-- Exact generated exit PC sets, rather than a chosen success or error exit. -/
theorem level4BoundaryExitPcs :
    level4BoundaryInstances.map (·.exitPcs) =
      [ #[0x10540, 0x10564, 0x105c4]
      , #[0x10550, 0x10580, 0x10594, 0x105c8]
      , #[0x10574, 0x1058c, 0x1059c, 0x105cc]
      , #[0x105c0, 0x105d0]
      , #[0x10610, 0x10634, 0x1070c, 0x10730, 0x10838, 0x10844, 0x10860, 0x11558,
           0x11b68, 0x1204c, 0x12088, 0x126f4]
      , #[0x1271c, 0x12730, 0x12850, 0x12884, 0x12904, 0x12920, 0x1302c]
      , #[0x1294c, 0x129b4, 0x129c0, 0x12abc, 0x12b24, 0x12b30, 0x12bbc, 0x12be4,
           0x12c2c, 0x12c8c, 0x12e60]
      , #[0x12ebc, 0x12ec8, 0x12eec, 0x12f3c, 0x12f64, 0x12f8c, 0x12fc8]
      ] := rfl

/-- Total bytes in the exact owned fragments; this is not a dynamic instruction bound. -/
theorem level4BoundaryOwnedBytes :
    level4BoundaryInstances.map FunctionInstance.coveredBytes =
      [40, 40, 40, 40, 8436, 464, 1240, 244] := rfl

/-- Every selected instance has multiple generated fragments, hence no selected boundary is
represented as one contiguous code range. -/
theorem level4BoundaryInstances_are_fragmented :
    level4BoundaryInstances.map FunctionInstance.isFragmented =
      [true, true, true, true, true, true, true, true] := rfl

/- Extraction audit: `GeneratedProgram` contains no binding field, result-record location, or
caller-live register set for these inlined boundaries.  This module therefore makes no ABI-adapter
or source-binding claim; source-level return-register conventions must not be reused as instance
facts here. -/

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
