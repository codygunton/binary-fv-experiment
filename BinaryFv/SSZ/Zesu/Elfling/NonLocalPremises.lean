import BinaryFv.SSZ.Zesu.Elfling.ManifestCheck
import BinaryFv.SSZ.Zesu.Contracts.SemanticObligations
import BinaryFv.SSZ.Zesu.SpecCorrespondence.EntryOffsets
import BinaryFv.SSZ.Zesu.SpecCorrespondence.ChainOffsets
import BinaryFv.SSZ.Zesu.SpecCorrespondence.ZeroOffsetAlias

/-!
# Assembling the non-local premises of the root obligation

`sszComplianceObligations generatedProgram` is **one of two things** the root theorem consumes, and
the distinction matters for reading this module. `root_compliance` descends through
`successful_trace_of_spec_accepts` / `rejected_trace_of_spec_rejects`, and each of those produces a
canonical program together with `sszComplianceObligations` *and* a `Nonempty` live run
(`SuccessfulRun` / `RejectedRun`). The run-existence half is the pair of authorized scaffolds in
`Entrypoints/ZesuDecodeRaw/Execution.lean` — the only two `sorry`s left in the SSZ proof — and it is
**not** reduced here. So the premise list below is Row D's remaining *obligation* scope, not the
whole of what stands between the project and an unconditional root theorem.

Within that scope, this module is the join. It collects the facts already discharged against the
generated data — coverage, canonical provenance, the address geometry, the acyclic rank, callee
resolution — and the facts about the canonical parameters themselves, and reduces
`sszProgramCorrectness` to exactly three residual premises:

* `catalogSemanticObligations` — what the contracts *claim* about the decoder's meaning;
* `catalogSatisfiability canonicalContractParams` — no cataloged precondition is impossible
  (discharged in `Entrypoints/ZesuDecodeRaw/CatalogSatisfiability.lean`, which sits above this
  module because its witness state comes from the runner's own builder);
* `LocalContractAssumptions` — the per-function-instance trace proofs, Rows E–I.

Anything the premises do not name is proved — with the live-run caveat above kept in view. The third
premise is deliberately left, because it is the whole point of the conditional capstone.

Nothing here re-derives a machine fact. Each component is imported from the module that established
it, so a regression shows up as a failure in that module rather than as a quietly weakened root.
-/

namespace BinaryFv.SSZ.Zesu.Elfling.Validation

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedProgram)

/-- **The canonical environment is the pinned one, and it is internally consistent.**

Both halves matter for different reasons. The image equality is what stops a proof from framing
against a convenient image — it is `rfl` only because `canonicalEnvironment` names
`Artifact.programImage` directly rather than an existentially chosen one. The validity half is
`canonical_environment_valid`, the reflected `?u64`/`?RawBlobSchedule` offsets being self-consistent,
and it is the antecedent every satisfiability obligation in the catalog shares.

The image equality is closed by *syntactic* projection (`simp only` on the two defining literals),
never by `rfl`: reducing `Artifact.programImage` to a normal form would force the ELF parse into the
elaborator. -/
theorem canonical_is_canonical_environment :
    IsCanonicalEnvironment canonicalContractParams.env := by
  refine ⟨?_, canonical_environment_valid⟩
  simp only [canonicalContractParams, canonicalEnvironment]

/-- **The composition premise, minus the local proofs.**

`LocalToGlobal` bundles five structural facts about the generated program with the local obligations
and the entry's grounding in the spec. Four of the five are decided on the generated data
(`generated_entry_is_exported`, `generated_callees_resolve`, `generated_call_graph_ranked`,
`generated_program_geometry`); the fifth is the local assumption, which stays a premise. So this
lemma is the composition premise with exactly the intended hole in it.

`catalogGroundsInSpec` is taken as a premise here rather than re-stated: it is already a conjunct of
`catalogSemanticObligations`, and threading the same proof into both places is what keeps the entry
contract tied to one grounding rather than two. -/
theorem generated_localToGlobal_of_locals (grounds : catalogGroundsInSpec)
    (locals : LocalContractAssumptions) :
    LocalToGlobal generatedProgram canonicalContractParams :=
  ⟨generated_entry_is_exported.1, generated_callees_resolve,
    ⟨generatedRank, generated_call_graph_ranked⟩, generated_program_geometry, locals, grounds⟩

/-- **Program correctness for the canonical program and the canonical parameters, reduced to its
residual premises.**

Three of `sszProgramCorrectness`'s six conjuncts are discharged outright here — the canonical
generated program, the canonical environment, and coverage. The other three are the premises. Note
what is *not* a premise: no runner fact, no observer fact, no validation evidence, and no
existentially chosen contract parameters. -/
theorem sszProgramCorrectness_of_locals (semantic : catalogSemanticObligations)
    (satisfiable : catalogSatisfiability canonicalContractParams)
    (locals : LocalContractAssumptions) :
    sszProgramCorrectness generatedProgram canonicalContractParams :=
  ⟨isCanonicalGeneratedProgram_holds, canonical_is_canonical_environment, coverage_holds,
    semantic, satisfiable, generated_localToGlobal_of_locals semantic.2.1 locals⟩

/-- **What the root theorem consumes, reduced to the same residue plus the two recorded
divergences.**

This is the statement Row D's capstone will discharge: given the semantic obligations, catalog
satisfiability, the recorded divergences, and the 141 local proofs, the canonical program satisfies
the compliance obligation the root theorem descends through. -/
theorem sszComplianceObligations_of_locals (semantic : catalogSemanticObligations)
    (satisfiable : catalogSatisfiability canonicalContractParams)
    (divergences : knownDivergences) (locals : LocalContractAssumptions) :
    sszComplianceObligations generatedProgram :=
  ⟨sszProgramCorrectness_of_locals semantic satisfiable locals, divergences⟩

/-- **Every function instance's closed obligation, from the same residue.** The composition is not restated
here — it is `sszProgramCorrectness_perFunctionInstance`, whose proof runs `global_of_local` over the
generated rank. Recording it at this layer makes the payoff visible: the local proofs plus the
generated structure entail that all 141 function instances implement their contracts. -/
theorem generated_function_instances_implement_of_locals (semantic : catalogSemanticObligations)
    (satisfiable : catalogSatisfiability canonicalContractParams)
    (locals : LocalContractAssumptions) :
    ∀ functionInstance ∈ generatedProgram.functionInstances,
      functionInstanceObligation canonicalContractParams generatedProgram functionInstance :=
  sszProgramCorrectness_perFunctionInstance (sszProgramCorrectness_of_locals semantic satisfiable locals)

/-- **The whole residue, in one signature.**

`Contracts.SemanticObligations` discharges sixteen of the twenty semantic conjuncts, so the premises
here are the complete list of what the root obligation still rests on. Read top to bottom they are:
**no oracle-agreement fact at all**, **no divergence premise either**, no cataloged precondition being
impossible, and the 141 local function instance proofs.

**`knownDivergences` has left the residue.** It used to be a premise here, recorded-and-intended
rather than outstanding; `Contracts.SemanticObligations.knownDivergences_holds` now proves it with no
hypotheses, so it is supplied in the term below instead of being asked for. Two premises remain:
`catalogSatisfiability`, discharged one layer up in `CatalogSatisfiability.lean`, and
`LocalContractAssumptions`, which is Rows E–I by design and the whole point of the conditional
capstone.

**All four of the original oracle-agreement premises are now PROVED rather than assumed**, and all
four are supplied here: `v3ShapeExcludesCanonicalV4_holds`,
`sourceShapedDecodeAgreesWithOracle_holds`, `sourceShapedContainersAgreeWithOracle_holds` — which
appears **twice** in the term below because it is consumed both directly and through the entry
agreement, and was therefore the single point of failure the whole story rested on — and
`zeroFirstOffsetAliasRejected_holds`.

That empties the oracle-agreement component of the residue. In other words the residue no longer
contains anything that was supposed to be proved here and was not.

The four are discharged at this layer rather than in `SemanticObligations` because their proofs
import that module, so the general lemma there stays parameterised and the top of the chain supplies
the facts.

Keeping this beside the coarser `sszComplianceObligations_of_locals` is deliberate: that one names
the *shape* of the obligation, this one names the *work*. When a premise disappears from here, that
is what progress on Row D looks like. (`catalogSatisfiability` is discharged one layer up, in
`CatalogSatisfiability.lean`, which restates this without it.) -/
theorem sszComplianceObligations_of_residue
    (satisfiable : catalogSatisfiability canonicalContractParams)
    (locals : LocalContractAssumptions) :
    sszComplianceObligations generatedProgram :=
  sszComplianceObligations_of_locals
    (catalogSemanticObligations_of_oracleAgreement
      (BinaryFv.SSZ.Zesu.SpecCorrespondence.sourceShapedDecodeAgreesWithOracle_holds
        BinaryFv.SSZ.Zesu.SpecCorrespondence.sourceShapedContainersAgreeWithOracle_holds
        retryTailNeverSchemaValid_holds)
      BinaryFv.SSZ.Zesu.SpecCorrespondence.sourceShapedContainersAgreeWithOracle_holds
      BinaryFv.SSZ.Zesu.SpecCorrespondence.v3ShapeExcludesCanonicalV4_holds
      BinaryFv.SSZ.Zesu.SpecCorrespondence.zeroFirstOffsetAliasRejected_holds)
    satisfiable knownDivergences_holds locals

/-- **Both obligation conjuncts of the D5 scaffolds, from the residue alone.**

`Entrypoints/ZesuDecodeRaw/Execution.lean`'s two scaffolds each claim three things: a canonical
generated program, `sszComplianceObligations` for it, and a live run. This is the first two of the
three, proved — so what those scaffolds still owe is *only* the run.

Worth stating separately from `sszComplianceObligations_of_residue` because the pairing is the part
that is easy to assume and was never written down: `isCanonicalGeneratedProgram_holds` is a conjunct
of `sszProgramCorrectness` and therefore already inside the obligation, so a reader could reasonably
believe the scaffold's first conjunct needs no separate proof. It does — the scaffold states it
*outside* the obligation as well — and this is it.

**It is not the whole scaffold and does not pretend to be.** The third conjunct,
`Nonempty (SuccessfulRun …)` / `Nonempty (RejectedRun …)`, is untouched here and is not reducible to
`locals` alone: constructing it needs a `TraceToSentinel`, which needs the exit `ret` to retire and `ra`
to still hold the sentinel at the exit.

*This paragraph used to end "and no contract in the catalog constrains a callee-saved register at all."
**That is no longer true**, and the correction is recorded rather than quietly deleted because the
sentence was the standing justification for treating the third conjunct as out of reach.* Three
postconditions now carry `Agree platformPreserved before after ∧ RetiredCounterPresent after`
(`Contracts/ExportedDecoder.lean`, `Contracts/Runtime.lean`; satisfiability exhibited first, in
`Contracts/ExportedDecoderAudit.lean`). The register clause is spelled as **preservation** rather than
`x1 = sentinelWord` precisely so the contract layer never names the runner's sentinel; it composes with
`buildZesuEntryState_entry_binding_abi`, which exposes the `x1 := sentinel` the builder always proved
and discarded.

*This paragraph twice said something that was true when written and false a commit later, so the history
is kept rather than smoothed over.* It first said no contract constrains a callee-saved register; then
that the three carry `x1` preservation plus `NormalExecutionState after`, with `minstret` still owed
"from the trace rather than from a contract". **Both intermediate readings were superseded**, and the
second was wrong about `minstret` in an instructive way: `minstret` is **not** preservable at all.
`tryStepControlFlowAfterRetired` (`RiscV/Step/ControlFlow.lean:140`) *is* `writeReg minstret
(retired + 1)` — the machine advances the counter on every retirement — so a clause saying the callee
left it unchanged would be **false of any routine that executes a single instruction**. That is why it is
carried as `RetiredCounterPresent after` (`∃ v, get? minstret = some v`), exactly the form `retiredRead`
consumes, and why the shape is two clauses rather than the one originally approved: the second exists
because the first would otherwise be a lie.

The eighteen registers in `platformPreserved` are `x1`, `NormalExecutionState`'s twelve, and `mstatus`,
`sig_meip`, `pma_regions`, `mseccfg`, `htif_tohost_base`. `pma_regions` is carried by **value**, not
presence, because `FetchPmaAllows` evaluates `matching_pma_region` over it; and the one `Agree` clause is
proved to cover the MMIO dispatch, since `within_clint`/`within_sig` read no register at all and
`within_htif_readable` reads only `htif_tohost_base`. -/
theorem canonicalProgram_and_obligations_of_residue
    (satisfiable : catalogSatisfiability canonicalContractParams)
    (locals : LocalContractAssumptions) :
    IsCanonicalGeneratedProgram generatedProgram ∧ sszComplianceObligations generatedProgram :=
  ⟨isCanonicalGeneratedProgram_holds,
    sszComplianceObligations_of_residue satisfiable locals⟩

end BinaryFv.SSZ.Zesu.Elfling.Validation
