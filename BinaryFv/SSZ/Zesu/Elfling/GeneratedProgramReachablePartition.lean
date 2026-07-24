import BinaryFv.SSZ.Zesu.Elfling.GeneratedValidationBridges
import BinaryFv.SSZ.Zesu.Elfling.GeneratedReachabilityExact
import BinaryFv.SSZ.Zesu.Contracts.Catalog
import BinaryFv.SSZ.Zesu.Interface
import BinaryFv.RiscV.Elfling.FunctionTrace
import GeneratedProgram

/-!
# Exhaustive reachable-coverage partition (option A with guardrails)

The generated function instances cover the cataloged routines, but some PCs reachable from `zesu_decode_raw`
belong to no cataloged function instance. Rather than silently drop them, this module proves the **exhaustive
partition**

```
reachable = covered ⊎ excluded         (3369 = 3135 + 234)
```

against the materialized reachable set (`ReachabilityCert.reachableAddresses`, tied to the canonical
decoded CFG by `entryReachableInventoryCertificate`) and the generator-emitted excluded taxonomy
(`Generated.generatedExcludedFunctionInstances`). The load-bearing content is `reachable_no_silent_drop`:
**every reachable PC is either covered by a cataloged function instance or one of the surfaced excluded
routines** — no reachable PC is unaccounted for. Covered and excluded are moreover disjoint over the
reachable set, and the counts are exactly 3135 and 234.

The excluded routines carry a category with a DIFFERENT soundness reason each:

* `reachableStdlib` — `std`/`mem`/`math` implementation reachable through the allocator vtable, whose
  net behavior is captured by the cataloged allocator contracts;
* `reachableCleanupNoOp` — `*.deinit` error-path cleanup; the freestanding zkVM's allocator free is a
  no-op, so deinit never changes the accept/reject outcome.

`excludedRoutinesOutcomeIrrelevant` names the resulting soundness obligation (that these routines do
not change the observable outcome `root_compliance` covers) as a `Prop` to be discharged in the
allocator/entry rows — it is stated, not asserted true here.

**Integration note for row 1:** at stack integration, row-1's `ExclusionReason` should gain
`reachableStdlib` / `reachableCleanupNoOp` constructors so this taxonomy folds into the shared catalog
exclusion type. This row keeps it local (row-1's `excludedRoutines` is untouched — PR #40).
-/

namespace BinaryFv.SSZ.Zesu.Elfling.Validation

set_option maxRecDepth 8000

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.SSZ.Zesu.ControlFlow (controlFlow?)
open BinaryFv.SSZ.Zesu.Elfling.Generated
  (generatedProgram generatedExcludedFunctionInstances reachableAddresses reachableEntry)

/-! ## Covered / excluded membership -/

/-- A PC covered by some cataloged generated function instance. -/
def isCoveredPC (a : Nat) : Bool :=
  generatedProgram.functionInstances.any fun functionInstance => functionInstance.containsAddress a

/-- A PC inside some surfaced excluded routine's region. -/
def isExcludedPC (a : Nat) : Bool :=
  generatedExcludedFunctionInstances.any fun x =>
    x.regions.any fun r => decide (r.start ≤ a ∧ a < r.stop)

/-! ## The partition over the reachable set -/

/-- Over the reachable set, covered and excluded are exactly complementary. -/
def reachablePartitionB : Bool :=
  reachableAddresses.all fun a => isCoveredPC a == !isExcludedPC a

theorem reachablePartitionB_true : reachablePartitionB = true := by native_decide

/-- **The exhaustive partition.** For every reachable PC, being covered by a cataloged function instance is
exactly the negation of being in an excluded routine: the two sets partition the reachable set (no
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

/-! ## The counts: 3369 = 3135 + 234 -/

theorem reachable_count : reachableAddresses.size = 3369 := by native_decide

theorem covered_reachable_count : (reachableAddresses.filter isCoveredPC).size = 3135 := by
  native_decide

theorem excluded_reachable_count : (reachableAddresses.filter isExcludedPC).size = 234 := by
  native_decide

/-! ## Excluded taxonomy — typed via the shared `ExclusionReason` -/

open BinaryFv.SSZ.Zesu.Contracts (ExclusionReason)

/-- Map a generated category string to the SHARED `ExclusionReason` (stack-integrated taxonomy), rather
than a disconnected local inductive. The row-1 `ExclusionReason` was extended with `reachableStdlib` /
`reachableCleanupNoOp` for exactly this. -/
def exclusionReasonOfCategory (s : String) : Option ExclusionReason :=
  if s = "reachableStdlib" then some .reachableStdlib
  else if s = "reachableCleanupNoOp" then some .reachableCleanupNoOp
  else none

/-- Every excluded routine carries one of the two reachable-but-excluded reasons, and its reason matches
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

/-- Every excluded routine is categorized as `reachableStdlib` (a `mem`/`std`/`math` implementation)
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

/-- Every reachable-but-excluded PC is attributed to a categorized excluded routine: the surfaced
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
surfaced excluded routines' PCs (3369 = 3135 + 234), with no reachable PC dropped and no overlap. -/
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
routine — the node-level counterpart of the total edge classification (`edges_all_classified`). -/
theorem reachable_node_decoded_and_owned :
    ∃ nodes : Array RiscV.ControlFlowNode, controlFlow? = some nodes ∧
      ∀ a ∈ reachableAddresses,
        RiscV.hasControlFlowAddress nodes a = true ∧
        (isCoveredPC a = true ∨ isExcludedPC a = true) := by
  obtain ⟨nodes, hn⟩ := controlFlow_isSome'
  exact ⟨nodes, hn, fun a ha => ⟨reachable_decoded hn a ha, reachable_no_silent_drop a ha⟩⟩

/-! ## Per-routine execution obligations (modular; discharged in later rows)

Replacing the removed `excludedRoutinesOutcomeIrrelevant`, which merely restated the whole
`root_compliance` under a taxonomy premise and was not a useful modular obligation. Here each excluded
routine gets its OWN execution obligation about ITS execution, typed by its `ExclusionReason` — the
building block the allocator/entry rows discharge. We do NOT prove semantic irrelevance in this row. -/

open BinaryFv.RiscV.Elfling (RegionPcs EnteredFunctionTrace)
open BinaryFv.RiscV (State)
open Register

/-- Confinement predicate of an excluded routine: PCs inside its canonical regions. -/
def excludedRegionPred (x : Generated.ExcludedFunctionInstance) : BitVec 64 → Prop :=
  RegionPcs x.regions

/-- An excluded routine's exit: control leaves its regions. -/
def excludedExitPred (x : Generated.ExcludedFunctionInstance) : BitVec 64 → Prop :=
  fun pc => ¬ RegionPcs x.regions pc

/-- The routine's entry PC (its lowest region start) as a machine word. -/
def excludedEntryWord (x : Generated.ExcludedFunctionInstance) : BitVec 64 :=
  BitVec.ofNat 64 (x.regions.foldl (fun m r => Nat.min m r.start) ((x.regions[0]?.map (·.start)).getD 0))

/-- **Per-routine EXECUTION obligation.** From any machine state sitting on the routine's entry, the
routine executes CONFINED to its own regions and reaches a generated exit — i.e. once entered it
terminates and never strays outside its code. This is modular (about ONE routine's execution) and is
the base obligation the category-specific memory effect strengthens in later rows: for a
`reachableCleanupNoOp` (`*.deinit`) the additional fact is that the confined run leaves the accept/
reject-determining state unchanged (its allocator free is a no-op); for a `reachableStdlib` it is that
the run realizes the corresponding cataloged allocator-vtable contract. -/
def excludedRoutineExecObligation (x : Generated.ExcludedFunctionInstance) : Prop :=
  ∀ (fromStep : Nat) (s : State), s.regs.get? PC = some (excludedEntryWord x) →
    ∃ (count : Nat) (s' : State),
      EnteredFunctionTrace (excludedRegionPred x) (excludedExitPred x) (excludedEntryWord x)
        fromStep count s s'

/-- The per-routine execution obligations for every reachable-but-excluded routine, dispatched by its
shared `ExclusionReason`. Each is a MODULAR statement about one routine's execution — the replacement
for the removed global `excludedRoutinesOutcomeIrrelevant`. Stated as a `Prop`, discharged in the
allocator/entry rows; not asserted true here. -/
def excludedRoutineObligations : Prop :=
  ∀ x ∈ generatedExcludedFunctionInstances,
    match exclusionReasonOfCategory x.category with
    | some .reachableStdlib => excludedRoutineExecObligation x
    | some .reachableCleanupNoOp => excludedRoutineExecObligation x
    | _ => True

end BinaryFv.SSZ.Zesu.Elfling.Validation
