import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4Contracts

namespace ZesuVerification

open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open BinaryFv.Zesu.Elflings.GeneratedLevel4Attribution

/-- The four adapters remain distinct optimized occurrences, rather than one source-level reader. -/
theorem level4_readOffset_adapters_match_inventory :
    [ readOffset199Interface.functionInstance.id, readOffset200Interface.functionInstance.id
    , readOffset201Interface.functionInstance.id, readOffset202Interface.functionInstance.id
    ] = decodeRawDirectReadOffsetInstances.map (·.id) := rfl

/-- Each reader's explicit continuation includes the final result-register instruction. -/
theorem level4_readOffset_continuation_bounds :
    ∀ args, readOffset199Interface.stepBound args = 65 ∧
      readOffset200Interface.stepBound args = 65 ∧
      readOffset201Interface.stepBound args = 65 ∧ readOffset202Interface.stepBound args = 65 := by
  intro args
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem level4_require_u32_continuation_pc :
    requireU32LengthContinuationPc = BitVec.ofNat 64 0x10490 := rfl

theorem level4_function_instance_contracts_match_inventory :
    level4FunctionInstanceContractIds = level4DisplayedFunctionInstances.map (·.id) :=
  level4FunctionInstanceContractIds_match_inventory

theorem level4_inline_region_contracts_match_inventory :
    level4InlineRegionContractIds = level4DisplayedExcludedInstances.map (·.id) :=
  level4InlineRegionContractIds_match_inventory

/-- The Level 4 selected bundle has the exact four direct readers and fills, rather than assumes,
the emitted `memcpy` contract. -/
theorem level4_selected_contracts_fill_memcpy (h : Level4ContractAssumptions) :
    (selectedContracts_of_level4 h).memcpy =
      BinaryFv.Zesu.MachineExecution.compiledMemcpyInstanceContract_proved := rfl

theorem level4_selected_summaries_fill_memcpy (h : Level4ContractAssumptions) :
    (selectedSummaries_of_level4 h).memcpy =
      BinaryFv.Zesu.MachineExecution.compiledMemcpyInstanceContract_proved := rfl

/-- The role-specific adapters retain the existing conservative bounds rather than replacing
them with unbounded traces. -/
theorem level4_specialized_decoder_bounds
    (container : BinaryFv.Zesu.Contracts.ContainerArgs)
    (chain : StackSliceContainerArgs) (keys : StackSliceCollectionArgs) :
    decodeNewPayloadRequestInterface.stepBound container = 8192 + 256 * container.bytes.size ∧
      decodeExecutionWitnessInterface.stepBound container = 1024 + 256 * container.bytes.size ∧
      decodeChainConfigInterface.stepBound chain = 2048 ∧
      decodePublicKeysInterface.stepBound keys = 128 + 128 *
        (keys.container.bytes.size / BinaryFv.Specs.SSZ.publicKeyBytes + 1) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Excluded cleanup/allocation regions carry concrete bounds and leave a nontrivial frame
obligation for the eventual Level 4-to-3 composition. -/
theorem level4_excluded_region_bounds :
    (∀ args, rawExecutionWitnessDeinitInterface.stepBound args = 1024) ∧
      (∀ args, allocatorFreeAnonInterface.stepBound args = 64) ∧
      (∀ args, allocBytesWithAlignmentAnonInterface.stepBound args = 1024) ∧
      (∀ args, rawNewPayloadRequestDeinitInterface.stepBound args = 1024) := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The fi95 handoff reaches 75572, but its source-reviewed semantic carrier is only reached by
the generated parent continuation at 75576. -/
theorem level4_fi95_handoff_requires_carrier_continuation :
    functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75568_75572.handoff.target = 75572 ∧
      functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75568_75572.carrierPcs = #[75576] ∧
      functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75568_75572.carrierPaths[0]? =
        some { carrierPc := 75576, pcs := #[75572, 75576] } := by
  exact ⟨rfl, rfl,
    functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoute_75568_75572_path_75576_exact⟩

end ZesuVerification
