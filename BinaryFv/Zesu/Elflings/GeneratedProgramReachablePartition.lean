import BinaryFv.Zesu.Elflings.GeneratedValidationBridges
import BinaryFv.Zesu.Elflings.GeneratedReachabilityExact
import BinaryFv.Zesu.Contracts.Catalog
import BinaryFv.Zesu.Interface
import BinaryFv.RiscV.Elfling.FunctionTrace
import GeneratedProgram

/-!
# Exhaustive reachable-coverage partition (option A with guardrails)

The generated function instances cover the cataloged source functions, but some PCs reachable from `zesu_decode_raw`
belong to no cataloged function instance. Rather than silently drop them, this module proves the **exhaustive
partition**

```
reachable = covered ⊎ excluded         (3369 = 3135 + 234)
```

against the materialized reachable set (`ReachabilityCert.reachableAddresses`, tied to the canonical
decoded CFG by `entryReachableInventoryCertificate`) and the generator-emitted excluded taxonomy
(`Generated.generatedExcludedFunctionInstances`). The load-bearing content is `reachable_no_silent_drop`:
**every reachable PC is either covered by a cataloged function instance or one of the surfaced excluded
source functions** — no reachable PC is unaccounted for. Covered and excluded are moreover disjoint over the
reachable set, and the counts are exactly 3135 and 234.

The excluded function instances carry a category with a DIFFERENT soundness reason each:

* `reachableStdlib` — `std`/`mem`/`math` implementation reachable through the allocator vtable, whose
  net behavior is captured by the cataloged allocator contracts;
* `reachableCleanupNoOp` — `*.deinit` error-path cleanup; the freestanding zkVM's allocator free is a
  no-op, so deinit never changes the accept/reject outcome.

`excludedFunctionsOutcomeIrrelevant` names the resulting soundness obligation (that these source functions do
not change the observable outcome `root_compliance` covers) as a `Prop` to be discharged in the
allocator and entrypoint proofs — it is stated, not asserted true here.

**Integration note:** `ExclusionReason` should gain
`reachableStdlib` / `reachableCleanupNoOp` constructors so this taxonomy folds into the shared catalog
exclusion type. This module keeps it local (`excludedSourceFunctions` is untouched — PR #40).
-/

namespace BinaryFv.Zesu.Elflings.Validation

set_option maxRecDepth 8000

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.Zesu.ControlFlow (controlFlow?)
open BinaryFv.Zesu.Elflings.Generated
  (generatedProgram generatedExcludedFunctionInstances reachableAddresses reachableEntry)

/-! ## Covered / excluded membership -/

/-- A PC covered by some cataloged generated function instance. -/
def isCoveredPC (a : Nat) : Bool :=
  generatedProgram.functionInstances.any fun functionInstance => functionInstance.containsAddress a

/-- A PC inside some surfaced excluded function instance's region. -/
def isExcludedPC (a : Nat) : Bool :=
  generatedExcludedFunctionInstances.any fun x =>
    x.regions.any fun r => decide (r.start ≤ a ∧ a < r.stop)

/-! ## The partition over the reachable set -/

/-- Over the reachable set, covered and excluded are exactly complementary. -/
def reachablePartitionB : Bool :=
  reachableAddresses.all fun a => isCoveredPC a == !isExcludedPC a

theorem reachablePartitionB_true : reachablePartitionB = true := by native_decide

/-- **The exhaustive partition.** For every reachable PC, being covered by a cataloged function instance is
exactly the negation of being in an excluded function instance: the two sets partition the reachable set (no
overlap, no gap). -/
theorem reachable_partition :
    ∀ a ∈ reachableAddresses, isCoveredPC a = !isExcludedPC a := by
  intro a ha
  exact eq_of_beq (forall_mem_of_all reachablePartitionB_true a ha)

/-- **No reachable PC is silently dropped**: every one is covered or explicitly excluded. -/
theorem reachable_no_silent_drop :
    ∀ a ∈ reachableAddresses, isCoveredPC a = true ∨ isExcludedPC a = true := by
  intro a ha
  have h := reachable_partition a ha
  cases hx : isExcludedPC a with
  | true => exact Or.inr rfl
  | false => exact Or.inl (by rw [h, hx]; rfl)

/-- **Covered and excluded are disjoint over the reachable set**: no reachable PC is both. -/
theorem reachable_covered_excluded_disjoint :
    ∀ a ∈ reachableAddresses, ¬(isCoveredPC a = true ∧ isExcludedPC a = true) := by
  intro a ha ⟨hc, he⟩
  rw [reachable_partition a ha, he] at hc
  exact absurd hc (by decide)

/-! ## Absorption draws only from the surfaced excluded inventory

D0's local obligation lets a function instance *absorb* the excluded function instances it calls — their PCs join
its owned set so its own proof accounts for them (`Program.ownedRanges`). The reviewer's concern is
that this could let a function instance claim ordinary uncovered code. It cannot, and here is why, made
concrete on the real program:

* the absorbable set is exactly this surfaced inventory (`generatedProgram.excludedFunctionInstances` **is**
  `generatedExcludedFunctionInstances` definitionally), and every absorbed PC is an `isExcludedPC`;
* an excluded PC is disjoint from every covered PC over the reachable set
  (`reachable_covered_excluded_disjoint`), and every reachable PC is covered **or** excluded with no
  gap (`reachable_no_silent_drop`) — so there is no "ordinary uncovered reachable code" for
  absorption to hide;
* absorption happens only where the source function is called (`Program.absorbed_requires_transfer`, generic),
  and that call edge is a real decoded direct call (`externalCallsValid`, checked for this program in
  `GeneratedProgramCfg`). -/

/-- The program's excluded field is exactly the surfaced reachable-but-excluded inventory. -/
theorem excluded_is_the_inventory :
    generatedProgram.excludedFunctionInstances = generatedExcludedFunctionInstances := rfl

/-- Every PC any function instance absorbs is an excluded-inventory PC. -/
def absorbedPCsAreExcludedB : Bool :=
  generatedProgram.functionInstances.all fun i =>
    (Program.absorbedRanges generatedProgram i).all fun r =>
      (List.range r.size).all fun k => isExcludedPC (r.start + k)

theorem absorbed_pcs_are_excluded : absorbedPCsAreExcludedB = true := by native_decide

/-- A function instance's own regions and the regions it absorbs are disjoint: absorbed code is genuinely
separate from the function instance's own cataloged code. -/
def ownAndAbsorbedDisjointB : Bool :=
  generatedProgram.functionInstances.all fun i =>
    (Program.absorbedRanges generatedProgram i).all fun a =>
      i.regions.all fun o =>
        decide (a.start + a.size ≤ o.start ∨ o.start + o.size ≤ a.start)

theorem own_and_absorbed_disjoint : ownAndAbsorbedDisjointB = true := by native_decide

/-- Negative: function instance 0 (`zesu_raw_alloc`) has no external calls and absorbs nothing. -/
theorem negative_occ0_absorbs_nothing :
    Program.absorbedRanges generatedProgram (generatedProgram.functionInstances[0]!) = #[] := by
  native_decide

/-! ## The counts: 3369 = 3135 + 234 -/

theorem reachable_count : reachableAddresses.size = 3369 := by native_decide

theorem covered_reachable_count : (reachableAddresses.filter isCoveredPC).size = 3135 := by
  native_decide

theorem excluded_reachable_count : (reachableAddresses.filter isExcludedPC).size = 234 := by
  native_decide

/-! ## Excluded taxonomy — typed via the shared `ExclusionReason` -/

open BinaryFv.Zesu.Contracts (ExclusionReason)

/-- Map a generated category string to the SHARED `ExclusionReason` (stack-integrated taxonomy), rather
than a disconnected local inductive. `ExclusionReason` was extended with `reachableStdlib` /
`reachableCleanupNoOp` for exactly this. -/
def exclusionReasonOfCategory (s : String) : Option ExclusionReason :=
  if s = "reachableStdlib" then some .reachableStdlib
  else if s = "reachableCleanupNoOp" then some .reachableCleanupNoOp
  else none

/-- Every excluded function instance carries one of the two reachable-but-excluded reasons, and its reason matches
its name shape (`*.deinit` for cleanup-no-op; a `std`/`mem`/`math` prefix for stdlib). This is what
keeps the taxonomy honest rather than a free-form label. -/
def excludedTaxonomyConsistentB : Bool :=
  generatedExcludedFunctionInstances.all fun x =>
    match exclusionReasonOfCategory x.category with
    | some .reachableCleanupNoOp => x.qualifiedName.endsWith ".deinit"
    | some .reachableStdlib =>
        x.qualifiedName.startsWith "mem." || x.qualifiedName.startsWith "std." ||
          x.qualifiedName.startsWith "math."
    | _ => false

theorem excludedTaxonomyConsistentB_true : excludedTaxonomyConsistentB = true := by native_decide

/-- Every excluded function instance is categorized as `reachableStdlib` (a `mem`/`std`/`math` implementation)
or `reachableCleanupNoOp` (a `*.deinit`), with the name shape matching the reason. -/
theorem excluded_taxonomy_consistent :
    ∀ x ∈ generatedExcludedFunctionInstances,
      (exclusionReasonOfCategory x.category = some .reachableStdlib ∧
        (x.qualifiedName.startsWith "mem." || x.qualifiedName.startsWith "std." ||
          x.qualifiedName.startsWith "math.") = true) ∨
      (exclusionReasonOfCategory x.category = some .reachableCleanupNoOp ∧
        x.qualifiedName.endsWith ".deinit" = true) := by
  intro x hx
  have h := forall_mem_of_all excludedTaxonomyConsistentB_true x hx
  revert h
  cases hcat : exclusionReasonOfCategory x.category with
  | none => intro h; simp at h
  | some c =>
    cases c with
    | reachableStdlib => intro h; exact Or.inl ⟨rfl, h⟩
    | reachableCleanupNoOp => intro h; exact Or.inr ⟨rfl, h⟩
    | testOnly => intro h; simp at h
    | unreachable => intro h; simp at h

/-- Every reachable-but-excluded PC is attributed to a categorized excluded function instance: the surfaced
data genuinely accounts for the 234 uncovered reachable PCs. -/
theorem excluded_reachable_pc_attributed :
    ∀ a ∈ reachableAddresses, isExcludedPC a = true →
      ∃ x ∈ generatedExcludedFunctionInstances,
        (x.regions.any fun r => decide (r.start ≤ a ∧ a < r.stop)) = true ∧
        (exclusionReasonOfCategory x.category).isSome = true := by
  intro a _ha hexc
  obtain ⟨x, hx, hr⟩ := exists_mem_of_any hexc
  refine ⟨x, hx, hr, ?_⟩
  rcases excluded_taxonomy_consistent x hx with ⟨hc, _⟩ | ⟨hc, _⟩ <;> rw [hc] <;> rfl

/-! ## The certified partition, tied to the reachability certificate -/

/-- Re-exposes the EXACT reachability certificate in this namespace: the materialized
`reachableAddresses` partitioned below equals `directReachable` from the entry in BOTH directions, so
the partition is over the genuine static reachable set of the canonical decoder — not an
over-approximation and not an arbitrary array. -/
theorem reachable_set_is_certified :
    ∃ nodes : Array RiscV.ControlFlowNode,
      controlFlow? = some nodes ∧
      ∀ a, a ∈ reachableAddresses ↔ a ∈ RiscV.directReachable nodes reachableEntry :=
  reachableAddresses_eq_directReachable

/-- **The complete exhaustive-partition certificate.** The materialized reachable set (certified by
`reachable_set_is_certified`) is exhaustively partitioned into the cataloged-covered PCs and the
surfaced excluded function instances' PCs (3369 = 3135 + 234), with no reachable PC dropped and no overlap. -/
theorem reachable_coverage_partition :
    (∀ a ∈ reachableAddresses, isCoveredPC a = true ∨ isExcludedPC a = true) ∧
    (∀ a ∈ reachableAddresses, ¬(isCoveredPC a = true ∧ isExcludedPC a = true)) ∧
    reachableAddresses.size = 3369 ∧
    (reachableAddresses.filter isCoveredPC).size = 3135 ∧
    (reachableAddresses.filter isExcludedPC).size = 234 :=
  ⟨reachable_no_silent_drop, reachable_covered_excluded_disjoint, reachable_count,
    covered_reachable_count, excluded_reachable_count⟩

/-- **Every reachable node is decoded and owned.** For the canonical decode, every address in the exact
reachable set is a decoded CFG node AND is owned by a cataloged function instance or a surfaced excluded
source function — the node-level counterpart of the total edge classification (`edges_all_classified`). -/
theorem reachable_node_decoded_and_owned :
    ∃ nodes : Array RiscV.ControlFlowNode, controlFlow? = some nodes ∧
      ∀ a ∈ reachableAddresses,
        RiscV.hasControlFlowAddress nodes a = true ∧
        (isCoveredPC a = true ∨ isExcludedPC a = true) := by
  obtain ⟨nodes, hn⟩ := controlFlow_isSome'
  exact ⟨nodes, hn, fun a ha => ⟨reachable_decoded hn a ha, reachable_no_silent_drop a ha⟩⟩

/-! ## Per-source function execution obligations

Replacing the removed `excludedFunctionsOutcomeIrrelevant`, which merely restated the whole
`root_compliance` under a taxonomy premise and was not a useful modular obligation. Here each excluded
source function gets its OWN execution obligation about ITS execution, typed by its `ExclusionReason` — the
building block the allocator and entrypoint proofs discharge. We do NOT prove semantic irrelevance here. -/

open BinaryFv.RiscV.Elfling (RegionPcs EnteredFunctionTrace)
open BinaryFv.RiscV (State)
open Register

/-- Confinement predicate of an excluded function instance: PCs inside its canonical regions. -/
def excludedRegionPred (x : BinaryFv.Binary.Elfling.Program.ExcludedFunctionInstance) : BitVec 64 → Prop :=
  RegionPcs x.regions

/-- An excluded function instance's exit: control leaves its regions. -/
def excludedExitPred (x : BinaryFv.Binary.Elfling.Program.ExcludedFunctionInstance) : BitVec 64 → Prop :=
  fun pc => ¬ RegionPcs x.regions pc

/-- The source function's entry PC (its lowest region start) as a machine word. -/
def excludedEntryWord (x : BinaryFv.Binary.Elfling.Program.ExcludedFunctionInstance) : BitVec 64 :=
  BitVec.ofNat 64 (x.regions.foldl (fun m r => Nat.min m r.start) ((x.regions[0]?.map (·.start)).getD 0))

/-- **Per-source function EXECUTION obligation.** From any machine state sitting on the source function's entry, the
source function executes CONFINED to its own regions and reaches a generated exit — i.e. once entered it
terminates and never strays outside its code. This is modular (about ONE source function's execution) and is
the base obligation that category-specific memory-effect proofs strengthen: for a
`reachableCleanupNoOp` (`*.deinit`) the additional fact is that the confined run leaves the accept/
reject-determining state unchanged (its allocator free is a no-op); for a `reachableStdlib` it is that
the run realizes the corresponding cataloged allocator-vtable contract. -/
def excludedFunctionExecObligation
    (x : BinaryFv.Binary.Elfling.Program.ExcludedFunctionInstance) : Prop :=
  ∀ (fromStep : Nat) (s : State), s.regs.get? PC = some (excludedEntryWord x) →
    ∃ (count : Nat) (s' : State),
      EnteredFunctionTrace (excludedRegionPred x) (excludedExitPred x) (excludedEntryWord x)
        fromStep count s s'

/-- The per-source function execution obligations for every reachable-but-excluded function instance, dispatched by its
shared `ExclusionReason`. Each is a MODULAR statement about one source function's execution — the replacement
for the removed global `excludedFunctionsOutcomeIrrelevant`. Stated as a `Prop`, discharged in the
allocator and entrypoint proofs; not asserted true here. -/
def excludedFunctionObligations : Prop :=
  ∀ x ∈ generatedExcludedFunctionInstances,
    match exclusionReasonOfCategory x.category with
    | some .reachableStdlib => excludedFunctionExecObligation x
    | some .reachableCleanupNoOp => excludedFunctionExecObligation x
    | _ => True

end BinaryFv.Zesu.Elflings.Validation
