import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4Contracts

namespace ZesuVerification

open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open BinaryFv.Zesu.Elflings.GeneratedLevel4Attribution
open LeanRV64DExecutable.Functions Register

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

/-- Regression checks for the generated `lbu`/`slli`/`or` transcription used by the four
interleaved reader contracts.  In particular, a reader fragment cannot be widened to permit
clobbering the saved-frame registers later restored by the raw-decoder epilogue. -/
theorem level4_readOffset_fragment_write_sets_are_exact :
    readOffsetFragmentWrites 0x10534 x10 ∧ readOffsetFragmentWrites 0x10534 x13 ∧
      ¬ readOffsetFragmentWrites 0x10534 x8 ∧
      readOffsetFragmentWrites 0x10544 x14 ∧ readOffsetFragmentWrites 0x10544 x17 ∧
      ¬ readOffsetFragmentWrites 0x10544 x9 ∧
      readOffsetFragmentWrites 0x10568 x5 ∧ readOffsetFragmentWrites 0x10568 x13 ∧
      ¬ readOffsetFragmentWrites 0x10568 x18 ∧
      readOffsetFragmentWrites 0x105a0 x16 ∧ readOffsetFragmentWrites 0x105a0 x6 ∧
      ¬ readOffsetFragmentWrites 0x105a0 x21 := by
  simp [readOffsetFragmentWrites, BinaryFv.RiscV.stepBookkeeping]

/-- Each final `or` has exactly one saved-register accumulator destination; the three rejected
alternatives make a widened or occurrence-swapped continuation fail this interface check. -/
theorem level4_readOffset_final_write_sets_are_exact :
    readOffsetFinalWrites readOffset199Interface.functionInstance x23 ∧
      ¬ readOffsetFinalWrites readOffset199Interface.functionInstance x25 ∧
      readOffsetFinalWrites readOffset200Interface.functionInstance x25 ∧
      ¬ readOffsetFinalWrites readOffset200Interface.functionInstance x24 ∧
      readOffsetFinalWrites readOffset201Interface.functionInstance x24 ∧
      ¬ readOffsetFinalWrites readOffset201Interface.functionInstance x19 ∧
      readOffsetFinalWrites readOffset202Interface.functionInstance x19 ∧
      ¬ readOffsetFinalWrites readOffset202Interface.functionInstance x23 := by
  simp [readOffsetFinalWrites, BinaryFv.RiscV.stepBookkeeping, readOffset199Interface,
    readOffset200Interface, readOffset201Interface, readOffset202Interface, readOffsetInlineInterface,
    functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_199_23,
    functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_200_23,
    functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_201_23,
    functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_202_23] <;> native_decide

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

/-- The carrier contract's expected PC list is not a target-only handoff: its exact-trace type
requires a retiring transition before the terminal carrier state. -/
theorem level4_fi95_carrier_path_has_two_pcs :
    (#[75572, 75576] : Array Nat).toList = [75572, 75576] := rfl

/-- fi95 cannot use the handoff target as a semantic exit; 75576 is its generated success exit. -/
theorem level4_fi95_carrier_pc_is_the_interface_exit :
    decodeExecutionWitnessInterface.terminal (BitVec.ofNat 64 75576) := by
  exact Or.inl rfl

theorem level4_fi95_handoff_target_is_not_the_interface_exit :
    ¬ decodeExecutionWitnessInterface.terminal (BitVec.ofNat 64 75572) := by
  change ¬ (BitVec.ofNat 64 75572 = BitVec.ofNat 64 0x12738 ∨
    BitVec.ofNat 64 75572 = BitVec.ofNat 64 0x11ba4)
  decide

/-- Both public-key handoff routes include the immediate 77712 terminal carrier.  Later generated
paths remain progress paths and are deliberately not required to satisfy the child exit predicate. -/
theorem level4_public_keys_routes_have_terminal_carrier :
    functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46_attributionBoundary_carrierRoute_77668_77712.carrierPaths[0]? =
      some { carrierPc := 77712, pcs := #[77712] } ∧
    functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46_attributionBoundary_carrierRoute_77708_77712.carrierPaths[0]? =
      some { carrierPc := 77712, pcs := #[77712] } ∧
    decodePublicKeysInterface.terminal (BitVec.ofNat 64 77712) := by
  exact ⟨functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46_attributionBoundary_carrierRoute_77668_77712_path_77712_exact,
    functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46_attributionBoundary_carrierRoute_77708_77712_path_77712_exact,
    Or.inl rfl⟩

theorem level4_public_keys_later_carrier_is_nonterminal :
    ¬ decodePublicKeysInterface.terminal (BitVec.ofNat 64 77716) := by
  change ¬ (BitVec.ofNat 64 77716 = BitVec.ofNat 64 0x12f90 ∨
    BitVec.ofNat 64 77716 = BitVec.ofNat 64 0x11ba4)
  decide

end ZesuVerification
