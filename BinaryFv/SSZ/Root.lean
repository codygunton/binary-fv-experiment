import BinaryFv.SSZ.Zesu.Artifact.Layout
import BinaryFv.SSZ.Zesu.Interface
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Assembly
import BinaryFv.SSZ.Zesu.Contracts.ProgramCorrectness

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
## Navigation from the root theorem to the source-oriented catalog

`root_compliance` descends through the generated Elfling program's correctness rather than around it.
`root_compliance_of_local_contracts` *produces* a canonical generated program together with
`Zesu.Contracts.sszComplianceObligations program`, and the two runner/result theorems below *consume*
that program and obligation. So the spine is literal: the root claim is built only from witnesses, and
no witness is reachable without program correctness.

**This file contains exactly one `sorry`, in `assumedAllLocalContracts`**, and that is the whole of
what the SSZ proof assumes. `root_compliance_of_local_contracts` proves the public claim from it and
carries no `sorry` at all; `#print axioms` on the two differs by exactly `sorryAx`. Both halves the
root needs — the compliance obligation and a live run of the machine — now close on that one premise:
the obligation through `Entrypoints/ZesuDecodeRaw/CatalogSatisfiability.lean`, the run through
`Entrypoints/ZesuDecodeRaw/Assembly.lean`.

Read the spine outward from the root:

* `root_compliance` — the public claim.
* `Zesu.Contracts.sszComplianceObligations` — some canonical contract parameters make
  `sszProgramCorrectness` hold, plus the two recorded divergences.
* `Zesu.Contracts.sszProgramCorrectness` — canonical coverage, semantic correspondence, the
  per-function-instance dispatch asserting each function instance's `correctnessClaim`, precondition satisfiability,
  and the explicit local-to-global composition.
* `Zesu.Contracts.catalog` — the 43 live routines, address-free, matched by full identity.
* the generated Elfling program — canonical-ELF ranges, checked against the pinned bytes.

None of these is a `sorry`; they are named `Prop`s, so an unfinished obligation is stated exactly
without changing the `nix/proof.nix` hole count.
-/

/-- The proof's own binary passes the runner's canonicality gate — by definition, since `binary`'s
bytes *are* the artifact's. Stated once so the two lemmas below can open the gate without
re-evaluating an 86 KB byte comparison. -/
theorem binary_is_canonical :
    Zesu.Entrypoints.ZesuDecodeRaw.artifactIsCanonical binary = true :=
  decide_eq_true (show binary.bytes = Zesu.Artifact.bytes from rfl)

/-- A successful run of the exported wrapper gives the public acceptance.

`program` and `obligations` are genuine premises, not manufactured by the root: they are supplied by
`canonicalProgram_and_obligations_of_residue` and threaded in here. The machine reasoning itself is
entirely `executeDecode_accepted_of_run`'s — the root reconstructs none of it.

**`_canonical` and `_obligations` are deliberately unused, and the underscore is the honest form.**
Checked rather than assumed: the identical statement without them is provable, so they contribute
nothing to *this* proof. They are kept because they are what forces `root_compliance_of_local_contracts`
to produce program correctness at all — the run half no longer carries it, so dropping them here would
detach the obligation from the root's cone entirely, which `DependencyReport.lean`'s reachability check
would then report. What they are *not* is a dependency of the machine bridge, and a reader who inferred
one from the signature would be wrong; hence the rename rather than a comment. Same treatment, and same
reasoning, as the dead `before` binders on the four postconditions. -/
theorem execute_accepts_of_successful_trace (input : ByteArray)
    (inputBound : input.size < Zesu.Runtime.maximumInputBytes) (value : SszBridge.RawV4)
    (program : Program) (_canonical : Zesu.Contracts.IsCanonicalGeneratedProgram program)
    (_obligations : Zesu.Contracts.sszComplianceObligations program)
    (execution : Zesu.Entrypoints.ZesuDecodeRaw.SuccessfulRun input value) :
    RiscvSpec.execute binary input = .ok (.accepted value) := by
  rw [RiscvSpec.execute_eq_executeChecked,
    Zesu.Entrypoints.ZesuDecodeRaw.executeChecked_eq_executeDecode binary_is_canonical inputBound]
  exact Zesu.Entrypoints.ZesuDecodeRaw.executeDecode_accepted_of_run input value
    execution.builds execution.trace execution.withinStepBound execution.accessors
    execution.returnCode execution.storedPresent execution.inputPreserved execution.storedValue

/-- A run recording a spec-producible rejection status gives the public rejection, given the same
canonical program and obligation. `_canonical` and `_obligations` are dead here for the same reason,
and kept for the same reason, as in `execute_accepts_of_successful_trace` above. -/
theorem execute_rejects_of_rejected_trace (input : ByteArray)
    (inputBound : input.size < Zesu.Runtime.maximumInputBytes)
    (program : Program) (_canonical : Zesu.Contracts.IsCanonicalGeneratedProgram program)
    (_obligations : Zesu.Contracts.sszComplianceObligations program)
    (execution : Zesu.Entrypoints.ZesuDecodeRaw.RejectedRun input) :
    RiscvSpec.execute binary input = .ok .rejected := by
  rw [RiscvSpec.execute_eq_executeChecked,
    Zesu.Entrypoints.ZesuDecodeRaw.executeChecked_eq_executeDecode binary_is_canonical inputBound]
  exact Zesu.Entrypoints.ZesuDecodeRaw.executeDecode_rejected_of_run input
    execution.builds execution.trace execution.withinStepBound execution.accessors
    execution.returnCode execution.specRejection execution.storedAbsent

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

/-- **The Amsterdam V4 compliance statement, conditional on the local contract proofs and nothing
else.**

Read the hypothesis list, because the point of this theorem is what is *absent* from it. It does not
take `sszComplianceObligations`, a successful or rejected trace, a runner correspondence, or an
observation. Each of those was a premise of some earlier version of this claim and each is now
*derived*: the obligation from `canonicalProgram_and_obligations_of_residue`, the runs from
`Assembly.lean`'s two witnesses, and everything downstream of a run existing from the runner. What is
left is `LocalContractAssumptions` — the 141 per-function-instance trace obligations — which is Rows
E–I by design.

The spine is still literal rather than asserted. `execute_accepts_of_successful_trace` and its twin
take the canonical program and its compliance obligation as genuine premises, so this proof has to
produce them; `DependencyReport.lean` checks that `sszComplianceObligations` is reachable from
`root_compliance` and fails rather than passing if a restructure ever detaches it. -/
theorem root_compliance_of_local_contracts
    (locals : Zesu.Elfling.Validation.LocalContractAssumptions) :
    ∀ input : ByteArray,
      input.size < 2 * 1024 * 1024 →
        RiscvSpec.execute binary input = .ok (SszSpec.decode input) := by
  intro input inputBound
  obtain ⟨canonical, obligations⟩ :=
    Zesu.Entrypoints.ZesuDecodeRaw.canonicalProgram_and_obligations_of_residue locals
  cases specResult : SszSpec.decode input with
  | accepted value =>
      obtain ⟨execution⟩ :=
        Zesu.Entrypoints.ZesuDecodeRaw.successfulRun_of_locals locals inputBound specResult
      exact execute_accepts_of_successful_trace input inputBound value _ canonical obligations
        execution
  | rejected =>
      obtain ⟨execution⟩ :=
        Zesu.Entrypoints.ZesuDecodeRaw.rejectedRun_of_locals locals inputBound specResult
      exact execute_rejects_of_rejected_trace input inputBound _ canonical obligations execution

/-- **The one assumed obligation in the whole SSZ proof**, and the only `sorry` in the tree.

It is not a convenience: `LocalContractAssumptions` quantifies
`functionInstanceLocalTraceObligation` over all 141 generated function instances, and
`Elfling/ManifestCheck.lean`'s `localContractAssumptions_iff_manifest` proves it is the *same*
statement as the row-by-row backlog — so this cannot silently omit an instance the root needs, and
the backlog cannot silently list one it does not.

Every trust question about `root_compliance` reduces to this declaration. `AxiomHygiene.lean` pins it
as the only permitted `sorry` site over the whole environment, and `DependencyReport.lean` pins it as
the entire seam of the root's cone — so the day a second hole appears, or this one moves, the build
says so. -/
theorem assumedAllLocalContracts : Zesu.Elfling.Validation.LocalContractAssumptions := by
  sorry

/-- The final Amsterdam V4 compliance statement.  Its dependency spine is intentionally visible:
spec classification, the canonical Elfling program and its compliance obligation, live Sail traces,
runner/result observation, and the public execution API.

It is now literally the conditional theorem applied to the one assumed premise, so "what does the
root rest on" is answered by reading this line. -/
theorem root_compliance :
    forall input : ByteArray,
      input.size < 2 * 1024 * 1024 ->
        RiscvSpec.execute binary input = .ok (SszSpec.decode input) :=
  root_compliance_of_local_contracts assumedAllLocalContracts

end BinaryFv.SSZ
