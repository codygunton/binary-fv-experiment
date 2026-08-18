import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level0Contract
import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Refinement
import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.InitialState
import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.ExecutableCorrectness

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

/-- Relational form retained for proofs that consume `ComplianceModulo` directly. -/
theorem complianceModulo_of_level2
    (hLevel2 : Level2ContractAssumptions) : ComplianceModulo knownBugs :=
  exportedContracts_of_level1 (level1Contracts_of_level2 hLevel2)

private theorem mainExecutionPc_ne_terminal {pc : BitVec 64} (inside : MainExecutionPc pc) :
    pc ≠ BitVec.ofNat 64 Elflings.zkvmExitTerminalPc := by
  rcases inside with inside | inside | inside | inside | inside | inside | inside
  · intro equal
    subst pc
    unfold mainGluePcs pcInRanges at inside
    revert inside
    native_decide
  · intro equal
    subst pc
    unfold pcInRanges at inside
    revert inside
    native_decide
  · intro equal
    subst pc
    unfold pcInRanges at inside
    revert inside
    native_decide
  · intro equal
    subst pc
    unfold DecodeExecutionPc pcInRanges at inside
    revert inside
    native_decide
  · intro equal
    subst pc
    unfold pcInRanges at inside
    revert inside
    native_decide
  · intro equal
    subst pc
    unfold pcInRanges at inside
    revert inside
    native_decide
  · exact inside.2

/-- Executing the pinned Zesu SSZ binary and the pinned EVM-Sail decoder gives the same canonical
outcome after exactly the seven reviewed Zesu divergences are normalized. -/
theorem root_compliance (hLevel2 : Level2ContractAssumptions) :
    ∀ input,
      input.size ≤ 64 * 1024 * 1024 →
      CanonicalOutcome.ofZesuKnownBugs input
          (RiscvSpec.execute zesuSszBinary input) =
        CanonicalOutcome.ofEvmSail input := by
  intro input inputBound
  let hLevel1 := level1Contracts_of_level2 hLevel2
  let contracts := hLevel1.resolve
  let args := canonicalMainArgs input
  obtain ⟨used, after, outcome, trace, usedPositive, meaning, exit, bounded⟩ :=
    main_resolved_handoff contracts args 0 (initialEndpointState input)
      (initialEndpointState_mainEntry input inputBound)
  have resolvedBound := level0ResolvedStepBound_lt_endpointFuel contracts input.size inputBound
  have bounded' : used ≤ level0ResolvedStepBound contracts input.size := by
    simpa [args, canonicalMainArgs] using bounded
  have fuelSuffices : used < 2 ^ 192 := by omega
  have ran : runEndpoint (2 ^ 192) 0 (initialEndpointState input) = finishEndpoint after :=
    runEndpoint_of_confinedTrace (fun pc inside => mainExecutionPc_ne_terminal inside)
      trace fuelSuffices (by simpa [EndpointPc] using exit.1)
  have observed : finishEndpoint after = ZesuDecodeOutcome.ofMainOutcome outcome :=
    finishEndpoint_of_mainExit exit
  have execution : RiscvSpec.execute zesuSszBinary input =
      ZesuDecodeOutcome.ofMainOutcome outcome := by
    unfold RiscvSpec.execute zesuSszBinary
    exact ran.trans observed
  rw [execution]
  exact (canonicalOutcome_eq_ofMainOutcome_iff args outcome).2 meaning

/-- Exact compliance for one input whose domain and successful result avoid every reviewed bug. -/
theorem compliance_for_input_of_avoids_known_bugs (hLevel2 : Level2ContractAssumptions)
    (hAvoidKnownBugs : AvoidKnownBugs input) : ComplianceFor input :=
  complianceFor_of_modulo hAvoidKnownBugs (complianceModulo_of_level2 hLevel2)

end BinaryFv.Zesu
