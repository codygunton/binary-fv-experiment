import GeneratedProgram

/-!
# Level 4 displayed boundary inventory

The production call-hierarchy UI displays these rows immediately below emitted `ssz_raw.decodeRaw`.
They are immediate-dominator display rows, not a substitute for `FunctionInstance.children`.
Only the four `readOffset` instances have `decodeRaw` as their direct source-inline parent.
The four cleanup and stdlib rows remain `Program.ExcludedFunctionInstance` values, so no contract
can accidentally be assumed for them.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary.Elfling
open BinaryFv.Zesu.Elflings.Generated

/-- The fourteen displayed rows that are generated `FunctionInstance` values. -/
def level4DisplayedFunctionInstances : List FunctionInstance :=
  [ functionInstance_raw_decoder_root_allocatorFree
  , functionInstance_ssz_raw_requireU32Length_in_ssz_raw_decodeRaw_at_191_25
  , functionInstance_ssz_raw_decodeNewPayloadRequest_in_ssz_raw_decodeRaw_at_207_61
  , functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48
  , functionInstance_ssz_raw_decodeChainConfig_in_ssz_raw_decodeRaw_at_211_48
  , functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46
  , functionInstance_ssz_raw_decodeByteListList
  , functionInstance_ssz_raw_requireCanonicalOffsets
  , functionInstance_raw_decoder_root_allocatorAlloc
  , functionInstance_memmove
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_199_23
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_200_23
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_201_23
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_202_23
  ]

/-- The four displayed rows deliberately excluded from the function-contract inventory. -/
def level4DisplayedExcludedInstances : List Program.ExcludedFunctionInstance :=
  [ excludedFunctionInstance_ssz_raw_RawExecutionWitness_deinit
  , excludedFunctionInstance_mem_Allocator_free_anon_1214
  , excludedFunctionInstance_mem_Allocator_allocBytesWithAlignment_anon_1331
  , excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit
  ]

/-- The four direct `readOffset` occurrences, retained as distinct optimized inline boundaries. -/
def decodeRawDirectReadOffsetInstances : List FunctionInstance :=
  [ functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_199_23
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_200_23
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_201_23
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_202_23
  ]

/-- One source declaration per displayed family; the direct `readOffset` occurrences share one. -/
def level4DisplayedSourceFamilies : List SourceDeclaration :=
  [ functionInstance_raw_decoder_root_allocatorFree.id.function.declaration
  , functionInstance_ssz_raw_requireU32Length_in_ssz_raw_decodeRaw_at_191_25.id.function.declaration
  , functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_199_23.id.function.declaration
  , FunctionId.declaration
      functionInstance_ssz_raw_decodeNewPayloadRequest_in_ssz_raw_decodeRaw_at_207_61.id.function
  , FunctionId.declaration
      functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48.id.function
  , FunctionId.declaration
      functionInstance_ssz_raw_decodeChainConfig_in_ssz_raw_decodeRaw_at_211_48.id.function
  , functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46.id.function.declaration
  , excludedFunctionInstance_ssz_raw_RawExecutionWitness_deinit.id.function.declaration
  , excludedFunctionInstance_mem_Allocator_free_anon_1214.id.function.declaration
  , excludedFunctionInstance_mem_Allocator_allocBytesWithAlignment_anon_1331.id.function.declaration
  , excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.id.function.declaration
  , functionInstance_ssz_raw_decodeByteListList.id.function.declaration
  , functionInstance_ssz_raw_requireCanonicalOffsets.id.function.declaration
  , functionInstance_raw_decoder_root_allocatorAlloc.id.function.declaration
  , functionInstance_memmove.id.function.declaration
  ]

theorem level4DisplayedFunctionInstances_count : level4DisplayedFunctionInstances.length = 14 := rfl

theorem level4DisplayedExcludedInstances_count : level4DisplayedExcludedInstances.length = 4 := rfl

theorem decodeRawDirectReadOffsetInstances_count :
    decodeRawDirectReadOffsetInstances.length = 4 := rfl

theorem level4DisplayedBoundary_count :
    level4DisplayedFunctionInstances.length + level4DisplayedExcludedInstances.length = 18 := rfl

theorem level4DisplayedSourceFamilies_count : level4DisplayedSourceFamilies.length = 15 := rfl

theorem decodeRawDirectReadOffsetInstances_are_direct_children :
    decodeRawDirectReadOffsetInstances.map (·.parent?) =
      [ some functionInstance_ssz_raw_decodeRawId, some functionInstance_ssz_raw_decodeRawId
      , some functionInstance_ssz_raw_decodeRawId, some functionInstance_ssz_raw_decodeRawId
      ] := rfl

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
