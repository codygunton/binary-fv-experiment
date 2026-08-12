import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level0Contract

/-!
# Zesu SSZ decoder compliance root

`root_compliance` is the unique public top of the proof. Its sole argument is the six immediate
Level 1 contracts selected for `ssz_decode_root.main`.
-/

namespace BinaryFv.Zesu

/-- Resolve the six reviewed Level 1 contracts into the complete Level 0 endpoint contract. -/
theorem exportedContracts_of_level1
    (hLevel1 : Level1ContractAssumptions) : ExportedContractAssumptions := by
  let contracts := hLevel1.resolve
  refine ⟨fun args => level0ResolvedStepBound contracts args.input.size, ?_⟩
  intro args fromStep before entry
  obtain ⟨used, after, outcome, trace, usedPositive, meaning, exit, bounded⟩ :=
    main_resolved_handoff contracts args fromStep before entry
  refine ⟨used, after, outcome, usedPositive, bounded, trace, ?_, meaning, exit⟩
  exact ⟨Elflings.zkvmExitTerminalPc, (by simpa [EndpointPc] using exit.1), by
    unfold pcInList
    native_decide⟩

/-- The shipped endpoint satisfies the fixed SSZ/RLP compliance relation if its six immediate
Level 1 machine contracts hold. -/
theorem root_compliance
    (hLevel1 : Level1ContractAssumptions) : ComplianceModulo knownBugs :=
  exportedContracts_of_level1 hLevel1

end BinaryFv.Zesu
