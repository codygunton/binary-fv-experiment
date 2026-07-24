import BinaryFv.SSZ.Zesu.Contracts.ProgramCorrectness

/-!
# Examples that challenge local-to-global composition

`global_of_local` combines local occurrence proofs into closed machine traces. These examples show
why its graph, summary, and boundary premises are necessary. Each fixture changes one structural fact
and proves that the composition rejects it.

Four failure modes are covered.

* **Circular dependency.** A pair of occurrences that call each other, and an occurrence that calls
  itself, admit no `CallGraphRanked` witness at all — so the composition's induction cannot be run on
  them. This is the property that stops "A because B, B because A".
* **Rank inversion.** A rank that places a caller below its callee is rejected, so the rank cannot be
  chosen to make the induction go through in the wrong direction.
* **A missing child summary.** If the admitted relation contains no run for a callee whose entry
  binding is satisfiable, `ChildSummariesAvailable` is false: a local proof cannot be handed an empty
  relation and still be asked to splice.
- **A missing or wrong checked boundary.** A program in which a callee's extent contains one of its
  caller's exits that is not itself a callee exit fails `ProgramGeometry` — and it must, because the
  spliced callee could otherwise run straight through its caller's return.
-/

namespace BinaryFv.SSZ.Zesu.Contracts.CompositionTests

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts

/-! ## Fixtures

Minimal hand-written programs. They carry no catalog identity, because none of the checks below is
about which routine an occurrence implements — they are about the shape of the dependency graph and
the generated geometry. -/

private abbrev testProvenance : ExtractionProvenance :=
  { sidecarHash := "test", entryOffset := 0, extractorVersion := "composition-tests" }

private abbrev testDecl : DeclarationProvenance :=
  { sourceFileHash := "test", declSpan := { line := 1, column := 1 } }

private abbrev testId (name : String) : InstanceId :=
  { function := { declaration := { file := { path := "test.zig" }, qualifiedName := name }
                  specialization := #[] }
    inlineStack := [] }

private abbrev testInstance (name : String) (start size entryPc : Nat) (exitPcs : Array Nat)
    (children : Array InstanceId) : FunctionInstance :=
  { id := testId name, regions := #[{ start := start, size := size }], entryPc := entryPc
    exitPcs := exitPcs, parent? := none, children := children, externalCalls := #[]
    declProvenance := testDecl, provenance := testProvenance, symbol? := none }

private abbrev testProgram (instances : Array FunctionInstance) (entry : InstanceId) : Program :=
  { entry := entry, instances := instances, defects := #[], provenance := testProvenance }

/-! ## 1. Circular dependencies admit no rank -/

/-- `a` and `b` call each other. -/
abbrev mutualA : FunctionInstance := testInstance "a" 100 100 100 #[196] #[testId "b"]
abbrev mutualB : FunctionInstance := testInstance "b" 200 100 200 #[296] #[testId "a"]

abbrev mutualProgram : Program := testProgram #[mutualA, mutualB] (testId "a")

private theorem mutualA_mem : mutualA ∈ mutualProgram.instances :=
  Array.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩

private theorem mutualB_mem : mutualB ∈ mutualProgram.instances :=
  Array.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩

private theorem mutualB_callee : mutualB ∈ calleeInstances mutualProgram mutualA :=
  Array.mem_filter.mpr ⟨mutualB_mem, by simp⟩

private theorem mutualA_callee : mutualA ∈ calleeInstances mutualProgram mutualB :=
  Array.mem_filter.mpr ⟨mutualA_mem, by simp⟩

/-- **Mutual recursion has no rank.** Each of the two occurrences would have to rank strictly below
the other, so no `CallGraphRanked` witness exists and `global_of_local` cannot be applied at all. -/
theorem negative_mutual_cycle_has_no_rank :
    ¬ ∃ rank : FunctionInstance → Nat, CallGraphRanked mutualProgram rank := by
  rintro ⟨rank, ranked⟩
  have hab := ranked mutualA mutualA_mem mutualB mutualB_callee
  have hba := ranked mutualB mutualB_mem mutualA mutualA_callee
  omega

/-! ## 2. An occurrence in its own dependency set admits no rank -/

/-- A single occurrence naming itself as an inline child. -/
abbrev selfCaller : FunctionInstance := testInstance "self" 100 100 100 #[196] #[testId "self"]

abbrev selfProgram : Program := testProgram #[selfCaller] (testId "self")

private theorem selfCaller_mem : selfCaller ∈ selfProgram.instances :=
  Array.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩

private theorem selfCaller_callee : selfCaller ∈ calleeInstances selfProgram selfCaller :=
  Array.mem_filter.mpr ⟨selfCaller_mem, by simp⟩

/-- **An occurrence may not occur in its own dependency set.** If it does, it would have to rank
strictly below itself. This is the specific shape the old implication-only local obligation could not
rule out on its own, and the reason the composition is stated over a ranked graph. -/
theorem negative_self_dependency_has_no_rank :
    ¬ ∃ rank : FunctionInstance → Nat, CallGraphRanked selfProgram rank := by
  rintro ⟨rank, ranked⟩
  have h := ranked selfCaller selfCaller_mem selfCaller selfCaller_callee
  omega

/-! ## 3. A rank that puts a caller below its callee is rejected -/

/-- `caller` calls `leaf`; `leaf` calls nothing. This graph *is* rankable. -/
abbrev caller : FunctionInstance := testInstance "caller" 100 100 100 #[196] #[testId "leaf"]
abbrev leaf : FunctionInstance := testInstance "leaf" 200 100 200 #[296] #[]

abbrev rankedProgram : Program := testProgram #[caller, leaf] (testId "caller")

private theorem caller_mem : caller ∈ rankedProgram.instances :=
  Array.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩

private theorem leaf_mem : leaf ∈ rankedProgram.instances :=
  Array.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩

private theorem leaf_callee : leaf ∈ calleeInstances rankedProgram caller :=
  Array.mem_filter.mpr ⟨leaf_mem, by simp⟩

/-- The honest rank: the callee below its caller. -/
def goodRank (instance_ : FunctionInstance) : Nat :=
  if instance_.entryPc = 100 then 1 else 0

/-- The inverted rank: the caller below its callee. -/
def invertedRank (instance_ : FunctionInstance) : Nat :=
  if instance_.entryPc = 100 then 0 else 1

/-- The honest rank orders this edge, so the negative below is about the inversion and not about the
fixture being unrankable. -/
theorem positive_good_rank_orders_the_edge : goodRank leaf < goodRank caller := by decide

/-- **Lowering a caller's rank below its callee fails.** The rank is not a free parameter that can be
chosen to make the induction close. -/
theorem negative_inverted_rank_rejected : ¬ CallGraphRanked rankedProgram invertedRank := by
  intro ranked
  have h := ranked caller caller_mem leaf leaf_callee
  simp [invertedRank] at h

/-! ## 4. A missing child summary is not admissible -/

/-- **An empty summary relation cannot satisfy `ChildSummariesAvailable`** when a callee's entry
binding is satisfiable: the relation is required to *contain* a run, so deleting the child's summary
makes the local proof's premise false rather than making the local proof easier.

Stated in the general form — the relation must contain a witness — so it covers deletion of any one
child summary, not just the fixture's. -/
theorem negative_missing_child_summary
    {p : ContractParams} {program : Program} {instance_ callee : FunctionInstance}
    {entry : CatalogEntry}
    (hcallee : callee ∈ calleeInstances program instance_)
    (found : catalogEntryFor callee.id.function = some entry)
    (satisfiable : ∃ (args : (routineContract p callee.id.function entry.tag).Args) (s : BinaryFv.RiscV.State),
      (routineContract p callee.id.function entry.tag).contract.binding.entry args s)
    (available : ChildSummariesAvailable p program instance_ (fun _ _ _ _ _ => False)) :
    False := by
  obtain ⟨args, s, hpre⟩ := satisfiable
  obtain ⟨_, _, _, hfalse, _⟩ := available callee hcallee entry found args 0 s hpre
  exact hfalse

/-- The same fact positively: whatever relation a local proof is handed, a satisfiable callee
precondition forces that relation to contain an actual run of that callee. So the premise cannot be
satisfied by a relation that says nothing. -/
theorem childSummariesAvailable_not_vacuous
    {p : ContractParams} {program : Program} {instance_ callee : FunctionInstance}
    {entry : CatalogEntry}
    {childSummary : InstanceId → Nat → Nat → BinaryFv.RiscV.State → BinaryFv.RiscV.State → Prop}
    (hcallee : callee ∈ calleeInstances program instance_)
    (found : catalogEntryFor callee.id.function = some entry)
    (satisfiable : ∃ (args : (routineContract p callee.id.function entry.tag).Args) (s : BinaryFv.RiscV.State),
      (routineContract p callee.id.function entry.tag).contract.binding.entry args s)
    (available : ChildSummariesAvailable p program instance_ childSummary) :
    ∃ used s s', childSummary callee.id 0 used s s' := by
  obtain ⟨args, s, hpre⟩ := satisfiable
  obtain ⟨used, s', _, hsummary, _⟩ := available callee hcallee entry found args 0 s hpre
  exact ⟨used, s, s', hsummary⟩

/-! ## 5. A missing or wrong checked boundary fails the geometry -/

/-- `boundaryParent` returns at `150`, which lies inside the inlined `boundaryChild` — but `150` is
not one of the child's own exits. Splicing the child here would let it run through its parent's
return. -/
abbrev boundaryChild : FunctionInstance := testInstance "child" 140 20 140 #[156] #[]

abbrev boundaryParent : FunctionInstance :=
  testInstance "parent" 100 100 100 #[150] #[testId "child"]

abbrev boundaryProgram : Program := testProgram #[boundaryParent, boundaryChild] (testId "parent")

private theorem boundaryParent_mem : boundaryParent ∈ boundaryProgram.instances :=
  Array.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩

private theorem boundaryChild_mem : boundaryChild ∈ boundaryProgram.instances :=
  Array.mem_iff_getElem.mpr ⟨1, by decide, rfl⟩

private theorem boundaryChild_callee :
    boundaryChild ∈ calleeInstances boundaryProgram boundaryParent :=
  Array.mem_filter.mpr ⟨boundaryChild_mem, by simp⟩

/-- **A parent exit hiding inside a child's extent breaks the geometry.** `ProgramGeometry` is
therefore not a formality: it is exactly the fact that rules out a spliced child stepping past its
caller's return, and a program where a boundary is missing or misattributed fails it. -/
theorem negative_uncontained_exit_fails_geometry : ¬ ProgramGeometry boundaryProgram := by
  intro geom
  have hpc : instanceExecutionPcs boundaryProgram boundaryChild (BitVec.ofNat 64 150) :=
    Or.inl ⟨{ start := 140, size := 20 }, Array.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩,
      by decide, by decide⟩
  have hexit : instanceExitPred boundaryParent (BitVec.ofNat 64 150) := by
    simp [instanceExitPred, FunctionInstance.isExit]
  have h := geom.calleeExitContainment boundaryParent boundaryParent_mem boundaryChild
    boundaryChild_callee (BitVec.ofNat 64 150) hpc hexit
  simp [instanceExitPred, FunctionInstance.isExit] at h

/-! ## 6. An occurrence with no catalog dispatch cannot be discharged

`instanceObligation` and `instanceLocalTraceObligation` both fall to `False` when
`catalogEntryFor` returns `none`. So an occurrence whose identity is not in the catalog does not
get a vacuously-true obligation — it gets an *unprovable* one, and the closed composition simply
cannot be produced for a program containing it. On the real program `catalog_dispatch_total`
rules this out; here we exhibit that a missing dispatch is genuinely fatal rather than silently
accepted. -/

/-- The test fixtures use `test.zig` identities, which are not in the handwritten catalog. -/
theorem uncataloged_has_no_dispatch : catalogEntryFor leaf.id.function = none := by rfl

/-- **A missing dispatch makes the closed obligation `False`** — not `True`. An uncataloged
occurrence cannot be discharged, so a program is only accepted if every occurrence dispatches. -/
theorem negative_missing_dispatch_closed (p : ContractParams) :
    instanceObligation p rankedProgram leaf = False := by
  unfold instanceObligation; rw [uncataloged_has_no_dispatch]

/-- **A missing dispatch makes the local obligation `False`** too, so it cannot be smuggled in as an
easy local premise either. -/
theorem negative_missing_dispatch_local (p : ContractParams) :
    instanceLocalTraceObligation p rankedProgram leaf = False := by
  unfold instanceLocalTraceObligation; rw [uncataloged_has_no_dispatch]

end BinaryFv.SSZ.Zesu.Contracts.CompositionTests
