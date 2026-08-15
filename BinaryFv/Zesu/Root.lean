import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level0Contract
import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Refinement

/-!
# Zesu SSZ decoder compliance root

`root_compliance` is the unique public top of the proof. `hLevel2` contains only the unresolved
contracts for the selected Level 2 function instances. The explicit Level 2 refinement edge fills
the already-proved Level 1 leaves before deriving the exported endpoint contract.
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

/-- The sole public root of the compliance proof. Its only premise is the selected Level 2
contracts; the conclusion records the fixed reviewed divergences honestly. -/
theorem root_compliance (hLevel2 : Level2ContractAssumptions) : ComplianceModulo knownBugs :=
  exportedContracts_of_level1 (level1Contracts_of_level2 hLevel2)

/-- Exact compliance for one input whose domain and successful result avoid every reviewed bug. -/
theorem compliance_for_input_of_avoids_known_bugs (hLevel2 : Level2ContractAssumptions)
    (hAvoidKnownBugs : AvoidKnownBugs input) : ComplianceFor input :=
  complianceFor_of_modulo hAvoidKnownBugs (root_compliance hLevel2)

end BinaryFv.Zesu
