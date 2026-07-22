import BinaryFv.SSZ.Zesu.Contracts.ProgramCorrectness

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.Binary.Elfling

/-!
# Structural audits of the catalog

The review's item-6 checks, compiled so the build fails if the catalog stops satisfying them.

The data checks over the immutable handwritten catalog use `native_decide`. That is the same
documented "small immutable-artifact checking" trust the repository already relies on for closed
facts about fixed artifacts (`Lean.ofReduceBool`, `Lean.trustCompiler`), and none of these audit
theorems is on `root_compliance`'s dependency spine, so its axiom set is unaffected. The two genuine
obligations (per-instance dispatch and the root dependency) are ordinary kernel proofs with no such
trust. -/

/-- Boolean: catalog identities are pairwise distinct. -/
def catalogIdentitiesNodup : Bool :=
  let ids := catalog.map (fun e => e.functionId)
  ids.toList.length == ids.toList.eraseDups.length

/-- Boolean: every catalog identity resolves through the dispatch lookup. -/
def everyIdentityDispatches : Bool :=
  catalog.all fun e => (catalogEntryFor e.functionId).isSome

/-- Boolean: two entries share a qualified name but differ in full identity (name-only would
conflate them). -/
def existsSameNameDistinctIdentity : Bool :=
  (catalog.flatMap fun e1 => catalog.map fun e2 =>
    (e1.functionId.declaration.qualifiedName == e2.functionId.declaration.qualifiedName) &&
      (e1.functionId != e2.functionId)).any id

/-- Boolean: every required `readArray` width is a live entry. -/
def allRequiredWidthsPresent : Bool :=
  requiredReadArrayWidths.all fun w =>
    catalog.any fun e => e.tag == RoutineTag.readArray && readArrayWidthOf e.functionId == w

/-- Boolean: no excluded routine shares an identity with a live one. -/
def exclusionsDisjoint : Bool :=
  excludedRoutines.all fun x => !catalog.any fun e => e.functionId == x.functionId

/-- Boolean: every excluded routine carries an exclusion reason. -/
def exclusionsAllClassified : Bool :=
  excludedRoutines.all fun x => match x.presence with | .absent _ => true | .live => false

/-- (1) Every catalog identity has exactly one contract dispatch. -/
theorem every_identity_dispatches : everyIdentityDispatches = true := by native_decide

/-- (1') Catalog identities are distinct, so the dispatch is single-valued. -/
theorem catalog_identities_distinct : catalogIdentitiesNodup = true := by native_decide

/-- (2) Every required concrete specialization is present. -/
theorem required_specializations_present : allRequiredWidthsPresent = true := by native_decide

/-- (3) Coverage is not name-only: two entries share a qualified name but differ in full identity. -/
theorem coverage_is_not_name_only : existsSameNameDistinctIdentity = true := by native_decide

/-- (4a) Exclusions never collide with coverage. -/
theorem exclusions_disjoint_from_catalog : exclusionsDisjoint = true := by native_decide

/-- (4b) Every excluded routine is classified with a machine-checkable reason. -/
theorem exclusions_all_classified : exclusionsAllClassified = true := by native_decide

/-- (5) `sszProgramCorrectness` genuinely references the per-instance implementation predicate:
program correctness entails that the occurrence at any cataloged identity implements its routine's
`correctnessClaim`. Ordinary kernel proof, no artifact trust. -/
theorem program_correctness_references_per_instance
    {program : Program} {p : ContractParams}
    (correct : sszProgramCorrectness program p)
    {instance_ : FunctionInstance} (mem : instance_ ∈ program.instances)
    {entry : CatalogEntry} (found : catalogEntryFor instance_.id.function = some entry) :
    routineObligation p instance_ entry.tag :=
  instance_implements_its_contract correct mem found

/-- (6) The runner/result theorems `root_compliance` is built from depend on
`sszComplianceObligations program`: it entails program correctness for the concrete
`canonicalContractParams` (which in particular witnesses the `∃ p` the old statement used). Ordinary
kernel proof. -/
theorem root_dependency_is_real :
    ∀ program : Program, sszComplianceObligations program → (∃ p, sszProgramCorrectness program p) :=
  fun _ obligations => ⟨canonicalContractParams, obligations.1⟩

end BinaryFv.SSZ.Zesu.Contracts
