import BinaryFv.SSZ.Zesu.Elfling.ManifestCheck

/-!
# Assembling the non-local premises of the root obligation

`sszComplianceObligations generatedProgram` is what the root theorem consumes. Row D's job is to
prove every part of it that is *not* one of the 141 local occurrence proofs, so that the only thing
the later rows still owe is `LocalContractAssumptions`.

This module is the join. It collects the facts already discharged against the generated data —
coverage, canonical provenance, the address geometry, the acyclic rank, callee resolution — and the
facts about the canonical parameters themselves, and reduces `sszProgramCorrectness` to exactly three
residual premises:

* `catalogSemanticObligations` — what the contracts *claim* about the decoder's meaning;
* `catalogSatisfiability canonicalContractParams` — no cataloged precondition is impossible;
* `LocalContractAssumptions` — the per-occurrence trace proofs, Rows E–I.

Reading the reduction is how you read Row D's remaining scope: anything a premise here does not name
is proved. The first two are D4's own remaining work and are discharged in their own modules; the
third is deliberately left, because it is the whole point of the conditional capstone.

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

/-- **Every occurrence's closed obligation, from the same residue.** The composition is not restated
here — it is `sszProgramCorrectness_perInstance`, whose proof runs `global_of_local` over the
generated rank. Recording it at this layer makes the payoff visible: the local proofs plus the
generated structure entail that all 141 occurrences implement their contracts. -/
theorem generated_instances_implement_of_locals (semantic : catalogSemanticObligations)
    (satisfiable : catalogSatisfiability canonicalContractParams)
    (locals : LocalContractAssumptions) :
    ∀ instance_ ∈ generatedProgram.instances,
      instanceObligation canonicalContractParams generatedProgram instance_ :=
  sszProgramCorrectness_perInstance (sszProgramCorrectness_of_locals semantic satisfiable locals)

end BinaryFv.SSZ.Zesu.Elfling.Validation
