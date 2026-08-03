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
            { start := 67140, size := 240 }, { start := 67424, size := 5188 },
            { start := 72620, size := 2892 }, { start := 75588, size := 80 }]
      , #[{ start := 75536, size := 16 }, { start := 75560, size := 12 },
            { start := 75680, size := 360 }, { start := 76044, size := 24 },
            { start := 77820, size := 52 }]
      , #[{ start := 76108, size := 4 }, { start := 76124, size := 104 },
            { start := 76280, size := 1132 }]
      , #[{ start := 77500, size := 212 }, { start := 77740, size := 32 }]
      ] := rfl

/-- Exact generated exit PC sets, rather than a chosen success or error exit. -/
theorem level4BoundaryExitPcs :
    level4BoundaryInstances.map (·.exitPcs) =
      [ #[66880, 66916, 67012]
      , #[66896, 66944, 66964, 67016]
      , #[66932, 66956, 66972, 67020]
      , #[67008, 67024]
      , #[67088, 67124, 67340, 67376, 67640, 67652, 67680, 71000, 72552, 73804, 73864,
           75508]
      , #[75548, 75568, 75856, 75908, 76036, 76064, 77868]
      , #[76108, 76212, 76224, 76476, 76580, 76592, 76732, 76772, 76844, 76940, 77408]
      , #[77500, 77512, 77548, 77628, 77668, 77708, 77768]
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

/-- The generated manifest's source `offset` bindings for the direct readers.  `none` means
`callerProvided`, not that the offset is zero or absent. -/
def decodeRawDirectReadOffsetStaticOffsets : List (Option Nat) := [none, some 4, some 8, some 12]

/- Extraction audit: the pinned LLVM/ELF hierarchy exposes neither a result-record location nor
caller-live register sets for any of these inlined boundaries.  It therefore supplies no ABI adapter
fact; source-level return-register conventions must not be reused as instance facts here. -/

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
