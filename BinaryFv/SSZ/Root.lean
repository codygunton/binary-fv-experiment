import BinaryFv.SSZ.Zesu.Artifact.Layout
import BinaryFv.SSZ.Zesu.Interface
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.HierarchicalContracts

namespace BinaryFv.SSZ

open BinaryFv.RiscV
open BinaryFv.Binary.Elfling

/-- The one canonical, Nix-built Zesu executable covered by the SSZ proof. -/
noncomputable def binary : RiscvSpec.ValidatedElf := {
  bytes := Zesu.Artifact.bytes
  elf := Zesu.Artifact.elf
  parsed_ok := by exact Zesu.Artifact.parsed_ok
  layout := Zesu.Artifact.elf_layout
}

/-!
## Navigation from the conditional root theorem

`root_compliance_of_exported_contracts` is the foundation's conditional product theorem. It assumes
the three exported machine contracts used by the runner, then derives the public Ethereum SSZ
agreement claim through the concrete runner and observers. Later refinement levels belong in stacked
PRs above this foundation.

The active spine is the concrete wrapper/accessor run assembly and the public execution classifier.
Canonical ELF and source-provenance checks remain available separately as decomposition-independent
evidence.
-/

/-- The proof's own binary passes the runner's canonicality gate — by definition, since `binary`'s
bytes *are* the artifact's. Stated once so the two lemmas below can open the gate without
re-evaluating an 86 KB byte comparison. -/
theorem binary_is_canonical :
    Zesu.Entrypoints.ZesuDecodeRaw.artifactIsCanonical binary = true :=
  decide_eq_true (show binary.bytes = Zesu.Artifact.bytes from rfl)

/-- **No failure mode becomes a rejection — proved at the layer where that is claimed.**

`RiscvSpec.execute`'s own docstring says "every failure mode keeps its own error; none of them
becomes a rejection". That claim is made about `execute`; until now the theorem backing it
(`executeDecode_rejected_forces_checks`) stopped one layer below, at `executeDecode`. The claim was
true — `execute` is `executeChecked` by `rfl`, and the preflight gate can only contribute
`.invalidArtifact` — but true-and-unproved-at-the-level-it-is-stated is the shape of every defect the
reachability pass turned up, so it is worth the twenty lines to close rather than to argue.

Stated over an arbitrary `ValidatedElf` rather than `binary`, so it constrains the public API itself
and not merely the proof's own instance of it.

**A second defect, found afterwards: this statement used to be strictly weaker than the theorem it
is derived from, and the loss was in the destructuring rather than anywhere a reader would look.**
`executeDecode_rejected_forces_checks` produces five things; the `obtain` here bound two of them to
`_htag` and `-` and the statement kept three. What went missing was the discriminant conjunct
(`observeOptionTag? final storedResultDiscriminantAddr = some false`) and the equation saying the
run *classified* as a rejection at all — which is also what pins `final`, `rawResult` and `rawError`
to a real run. Without it those three existentials were tied to nothing but each other, and the
statement said only "some state and some pair of accessor outcomes look like this", not "the run
that produced this answer looked like this".

`ZesuDecodeRaw.rejection_checks_without_discriminant_admit_a_non_rejection` measures the difference
rather than asserting it: the three retained conjuncts are satisfied by a state whose discriminant
reads *present* — the shape a refused second call leaves — on which the classifier answers
`.error .badReturn`. So neither dropped conjunct followed from what was kept.

**The acceptance twin below was not affected in the same way, and the asymmetry is real but smaller
than it looks.** It kept the discriminant conjunct, and it drops the same classification equation —
but there that equation is *derivable* from the conjuncts it does carry, as
`accepted_checks_determine_classification` below checks. On the rejection side, without the
discriminant, it was not. -/
theorem execute_rejected_forces_checks {b : RiscvSpec.ValidatedElf} {input : ByteArray}
    (h : RiscvSpec.execute b input = .ok .rejected) :
    Zesu.Entrypoints.ZesuDecodeRaw.preflight b input = .ok () ∧
      ∃ (final : BinaryFv.RiscV.State) (steps : Nat)
        (rawResult rawError : Zesu.Entrypoints.ZesuDecodeRaw.AccessorOutcome),
        Zesu.Entrypoints.ZesuDecodeRaw.observeReturnCode? final = some 0 ∧
        rawResult = Zesu.Entrypoints.ZesuDecodeRaw.AccessorOutcome.returned 0 ∧
        Zesu.MemoryRepresentation.observeOptionTag? final
          Zesu.Entrypoints.ZesuDecodeRaw.storedResultDiscriminantAddr = some false ∧
        (∃ status, rawError = Zesu.Entrypoints.ZesuDecodeRaw.AccessorOutcome.returned status ∧
          Zesu.Entrypoints.ZesuDecodeRaw.statusCategory status = .specRejection) ∧
        Zesu.Entrypoints.ZesuDecodeRaw.classifyWrapperRun
          Zesu.Entrypoints.ZesuDecodeRaw.observeDecodedValue
          Zesu.Entrypoints.ZesuDecodeRaw.storedResultDiscriminantAddr
          Zesu.Elfling.canonicalResultBuffer rawResult rawError (.reached steps) final
          = .ok .rejected := by
  rw [RiscvSpec.execute_eq_executeChecked] at h
  obtain ⟨hgate, hdec⟩ := Zesu.Entrypoints.ZesuDecodeRaw.executeChecked_rejected_forces_gate h
  obtain ⟨final, steps, rawResult, rawError, hcode, hnull, htag, hstatus, hclass⟩ :=
    Zesu.Entrypoints.ZesuDecodeRaw.executeDecode_rejected_forces_checks hdec
  exact ⟨hgate, final, steps, rawResult, rawError, hcode, hnull, htag, hstatus, hclass⟩

/-- **The public API never invents an acceptance, and the value it reports is the one memory held.**

The twin of `execute_rejected_forces_checks`, and the sharper of the two. Rejection has one shape, so
its converse mostly rules failure modes out. Acceptance carries a *value*, and `classifyWrapperRun`
takes that value from `observeDecodedValue final` — so without this, nothing at the public layer ties
the reported value to the observation. The final conjunct is that tie: an `accepted value` answer
forces `observeDecodedValue final = some value`, the same `value`.

Stated over an arbitrary `ValidatedElf`, like its twin. -/
theorem execute_accepted_forces_checks {b : RiscvSpec.ValidatedElf} {input : ByteArray}
    {value : SszBridge.RawV4} (h : RiscvSpec.execute b input = .ok (.accepted value)) :
    Zesu.Entrypoints.ZesuDecodeRaw.preflight b input = .ok () ∧
      ∃ (final : BinaryFv.RiscV.State)
        (rawResult rawError : Zesu.Entrypoints.ZesuDecodeRaw.AccessorOutcome),
        Zesu.Entrypoints.ZesuDecodeRaw.observeReturnCode? final = some 1 ∧
        rawError = Zesu.Entrypoints.ZesuDecodeRaw.AccessorOutcome.returned
          Zesu.Contracts.DecodeStatus.ok.code ∧
        rawResult = Zesu.Entrypoints.ZesuDecodeRaw.AccessorOutcome.returned
          Zesu.Elfling.canonicalResultBuffer ∧
        Zesu.MemoryRepresentation.observeOptionTag? final
          Zesu.Entrypoints.ZesuDecodeRaw.storedResultDiscriminantAddr = some true ∧
        Zesu.Entrypoints.ZesuDecodeRaw.observeDecodedValue final = some value := by
  rw [RiscvSpec.execute_eq_executeChecked] at h
  obtain ⟨hgate, hdec⟩ := Zesu.Entrypoints.ZesuDecodeRaw.executeChecked_accepted_forces_gate h
  obtain ⟨final, _steps, rawResult, rawError, hcode, herror, hnull, htag, hvalue, -⟩ :=
    Zesu.Entrypoints.ZesuDecodeRaw.executeDecode_accepted_forces_checks hdec
  exact ⟨hgate, final, rawResult, rawError, hcode, herror, hnull, htag, hvalue⟩

/-- **Why the acceptance twin does not also need to carry the classification equation.**

`execute_accepted_forces_checks` drops the same `classifyWrapperRun … = .ok (.accepted value)`
conjunct that `execute_rejected_forces_checks` was strengthened to keep, and that asymmetry is
deliberate: here the equation is recoverable from the conjuncts already stated, so keeping it would
add a longer statement and no information. This lemma is that recovery, so the claim is checked
rather than asserted — and so a future edit that weakens the acceptance conjuncts breaks a build
instead of quietly making the asymmetry unjustified.

Unlike its rejection counterpart it holds for *every* step count, not just the one the run took:
nothing in the classifier's success branch reads the step count.

**It is the one new declaration here that is not classical-only.** It needs
`canonicalResultBuffer_ne_zero`, a `native_decide`, so it carries the compiler pair — the same
inversion of the usual expectation the runner's provenance note records, from the other side: the
*forward* direction is the expensive one. The strengthened converse above and its independence
witness are `propext`/`Classical.choice`/`Quot.sound` only. -/
theorem accepted_checks_determine_classification {final : BinaryFv.RiscV.State}
    {value : SszBridge.RawV4} (steps : Nat)
    (hcode : Zesu.Entrypoints.ZesuDecodeRaw.observeReturnCode? final = some 1)
    (htag : Zesu.MemoryRepresentation.observeOptionTag? final
      Zesu.Entrypoints.ZesuDecodeRaw.storedResultDiscriminantAddr = some true)
    (hvalue : Zesu.Entrypoints.ZesuDecodeRaw.observeDecodedValue final = some value) :
    Zesu.Entrypoints.ZesuDecodeRaw.classifyWrapperRun
        Zesu.Entrypoints.ZesuDecodeRaw.observeDecodedValue
        Zesu.Entrypoints.ZesuDecodeRaw.storedResultDiscriminantAddr
        Zesu.Elfling.canonicalResultBuffer
        (.returned Zesu.Elfling.canonicalResultBuffer)
        (.returned Zesu.Contracts.DecodeStatus.ok.code) (.reached steps) final
      = .ok (.accepted value) :=
  Zesu.Entrypoints.ZesuDecodeRaw.classifyWrapperRun_accepted _ _ _ steps _ _ final value hcode rfl
    rfl Zesu.Entrypoints.ZesuDecodeRaw.canonicalResultBuffer_ne_zero htag hvalue

/-- The foundation's conditional root theorem. Its premise is exactly the three exported contracts
consumed by the concrete runner. Refinement PRs may prove or strengthen this premise without changing
the public statement. -/
theorem root_compliance_of_exported_contracts
    (contracts : Zesu.Entrypoints.ZesuDecodeRaw.ExportedContractAssumptions) :
    ∀ input : ByteArray,
      input.size < 2 * 1024 * 1024 →
        RiscvSpec.execute binary input = .ok (SszSpec.decode input) := by
  intro input inputBound
  cases specResult : SszSpec.decode input with
  | accepted value =>
      obtain ⟨execution⟩ :=
        Zesu.Entrypoints.ZesuDecodeRaw.successfulRun_of_exported contracts inputBound specResult
      rw [RiscvSpec.execute_eq_executeChecked,
        Zesu.Entrypoints.ZesuDecodeRaw.executeChecked_eq_executeDecode binary_is_canonical inputBound]
      exact Zesu.Entrypoints.ZesuDecodeRaw.executeDecode_accepted_of_run input value
        execution.builds execution.trace execution.withinStepBound execution.accessors
        execution.returnCode execution.storedPresent execution.inputPreserved execution.storedValue
  | rejected =>
      obtain ⟨execution⟩ :=
        Zesu.Entrypoints.ZesuDecodeRaw.rejectedRun_of_exported contracts inputBound specResult
      rw [RiscvSpec.execute_eq_executeChecked,
        Zesu.Entrypoints.ZesuDecodeRaw.executeChecked_eq_executeDecode binary_is_canonical inputBound]
      exact Zesu.Entrypoints.ZesuDecodeRaw.executeDecode_rejected_of_run input
        execution.builds execution.trace execution.withinStepBound execution.accessors
        execution.returnCode execution.specRejection execution.storedAbsent

/-- Level 1 restatement of the conditional root theorem: one exported decoder contract and its seven
reviewed immediate tail contracts imply the public Ethereum SSZ agreement statement. The five
non-accessor tail fields become proof inputs at the next refinement edge; this theorem uses the
exported wrapper/accessor projection needed by the concrete runner. -/
theorem root_compliance_of_level1_contracts
    (contracts : Zesu.Entrypoints.ZesuDecodeRaw.Level1ContractAssumptions) :
    ∀ input : ByteArray,
      input.size < 2 * 1024 * 1024 →
        RiscvSpec.execute binary input = .ok (SszSpec.decode input) :=
  root_compliance_of_exported_contracts contracts.toExportedContractAssumptions

end BinaryFv.SSZ
