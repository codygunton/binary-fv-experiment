import BinaryFv.Zesu.Elflings.GeneratedValidationBridges
import BinaryFv.RiscV.Analysis.ReachabilityComplete
import BinaryFv.Zesu.ControlFlow.Decode
import GeneratedProgram

/-!
# The generated reachable set is EXACTLY `directReachable` (area #5, both directions)

The generator emits the reachable set `reachableAddresses` together with, per address, a BFS
`distance` from the entry and a `predecessor`. This module proves both inclusions against the
Sail-decoded `controlFlowNodes`, so the materialized set is the EXACT static reachable set — never a
mere over-approximation:

* **forward** (`directReachable ⊆ R`): `R` contains the entry and is closed under decoded direct
  successors, so the generic least-fixpoint lemma `directReachable_subset` places all of
  `directReachable` inside it;
* **reverse / minimality** (`R ⊆ directReachable`): every address in `R` carries a witness — a
  predecessor of strictly smaller distance with a REAL decoded edge into it — so an ordinary kernel
  induction on distance builds a genuine reachability path `DirectlyReaches`, and the generic
  completeness lemma `mem_directReachable_of_reaches` places it in `directReachable`.

The distance strictly decreasing along predecessors is what makes the witness graph acyclic and the
induction well-founded: a spurious witness for an unreachable address would need a predecessor of
smaller distance that is itself reachable, and no such chain to the entry exists. The per-address
witness/closure facts are `native_decide`d against the concrete data + decoded CFG (SSZ-layer
exception); the distance induction and the two inclusions are ordinary kernel proofs.
-/

namespace BinaryFv.Zesu.Elflings.Validation

set_option maxRecDepth 8000

open BinaryFv.RiscV
open BinaryFv.Zesu.ControlFlow (controlFlow?)
open BinaryFv.Zesu.Elflings.Generated (reachableWitness reachableEntry reachableAddresses ReachStep)

/-! ## The canonical decode -/

theorem controlFlow_isSome' : ∃ nodes, controlFlow? = some nodes :=
  Option.isSome_iff_exists.mp (by native_decide)

/-! ## Forward: `R` contains the entry and is closed under decoded successors -/

/-- `R` contains the (decoded) entry and every decoded direct successor of an `R` address stays in
`R`. Dispatched through `controlFlow?` so a decode failure is `false`. -/
def forwardClosedC : Bool :=
  (controlFlow?.map fun nodes =>
    hasControlFlowAddress nodes reachableEntry &&
    reachableAddresses.contains reachableEntry &&
    reachableAddresses.all fun a =>
      hasControlFlowAddress nodes a &&
      (directSuccessorsAt nodes a).all fun t => reachableAddresses.contains t).getD false

theorem forwardClosedC_true : forwardClosedC = true := by native_decide

/-! ## Reverse witnesses: each address has a smaller-distance predecessor with a real edge -/

/-- Every witness row is either the entry (distance 0) or has a predecessor row of distance one less
with a REAL decoded edge into it and a decoded target. Dispatched through `controlFlow?`. -/
def witnessValidC : Bool :=
  (controlFlow?.map fun nodes =>
    reachableWitness.all fun r =>
      (decide (r.addr = reachableEntry) && decide (r.distance = 0)) ||
      (reachableWitness.any (fun pr => decide (pr.addr = r.predecessor ∧ pr.distance + 1 = r.distance)) &&
        (directSuccessorsAt nodes r.predecessor).contains r.addr &&
        hasControlFlowAddress nodes r.addr)).getD false

theorem witnessValidC_true : witnessValidC = true := by native_decide

/-! ## Specialise the dispatched checks to explicit decoded nodes -/

theorem forwardClosed_some {nodes : Array ControlFlowNode} (hn : controlFlow? = some nodes) :
    hasControlFlowAddress nodes reachableEntry = true ∧
    reachableAddresses.contains reachableEntry = true ∧
    reachableAddresses.all (fun a => hasControlFlowAddress nodes a &&
      (directSuccessorsAt nodes a).all fun t => reachableAddresses.contains t) = true := by
  have h := forwardClosedC_true
  unfold forwardClosedC at h
  rw [hn] at h
  simp only [Option.map_some, Option.getD_some] at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem witnessValid_some {nodes : Array ControlFlowNode} (hn : controlFlow? = some nodes) :
    reachableWitness.all (fun r =>
      (decide (r.addr = reachableEntry) && decide (r.distance = 0)) ||
      (reachableWitness.any (fun pr => decide (pr.addr = r.predecessor ∧ pr.distance + 1 = r.distance)) &&
        (directSuccessorsAt nodes r.predecessor).contains r.addr &&
        hasControlFlowAddress nodes r.addr)) = true := by
  have h := witnessValidC_true
  unfold witnessValidC at h
  rw [hn] at h
  simpa only [Option.map_some, Option.getD_some] using h

/-! ## Reverse: build a reachability path for every witnessed address -/

/-- The entry is decoded. -/
theorem entry_decoded {nodes : Array ControlFlowNode} (hn : controlFlow? = some nodes) :
    hasControlFlowAddress nodes reachableEntry = true :=
  (forwardClosed_some hn).1

/-- Every reachable address is decoded. -/
theorem reachable_decoded {nodes : Array ControlFlowNode} (hn : controlFlow? = some nodes) :
    ∀ a ∈ reachableAddresses, hasControlFlowAddress nodes a = true := by
  intro a ha
  have h := forall_mem_of_all (forwardClosed_some hn).2.2 a ha
  rw [Bool.and_eq_true] at h
  exact h.1

/-- Every reachable address's decoded direct successors stay in `R`. -/
theorem reachable_closed {nodes : Array ControlFlowNode} (hn : controlFlow? = some nodes) :
    ∀ a ∈ reachableAddresses, ∀ t ∈ directSuccessorsAt nodes a,
      reachableAddresses.contains t = true := by
  intro a ha t ht
  have h := forall_mem_of_all (forwardClosed_some hn).2.2 a ha
  rw [Bool.and_eq_true] at h
  exact forall_mem_of_all h.2 t ht

/-- **Minimality core.** By strong induction on distance, every witness row's address is genuinely
reachable from the entry through decoded direct edges. -/
theorem reaches_of_witness {nodes : Array ControlFlowNode} (hn : controlFlow? = some nodes) :
    ∀ d, ∀ r ∈ reachableWitness, r.distance = d →
      DirectlyReaches nodes reachableEntry r.addr := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro r hr hrd
    have hrow := forall_mem_of_all (witnessValid_some hn) r hr
    rw [Bool.or_eq_true] at hrow
    rcases hrow with hbase | hstep
    · -- entry: distance 0
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hbase
      rw [hbase.1]
      exact DirectlyReaches.base
    · -- predecessor of smaller distance with a real edge
      rw [Bool.and_eq_true, Bool.and_eq_true] at hstep
      obtain ⟨pr, hpr, hpreq⟩ := exists_mem_of_any hstep.1.1
      rw [decide_eq_true_eq] at hpreq
      have hpr_dist : pr.distance = d - 1 := by omega
      have hpr_lt : pr.distance < d := by omega
      have hpred_reaches : DirectlyReaches nodes reachableEntry pr.addr :=
        ih pr.distance hpr_lt pr hpr rfl
      have hedge : r.addr ∈ directSuccessorsAt nodes r.predecessor :=
        Array.contains_iff_mem.mp hstep.1.2
      rw [← hpreq.1] at hedge
      exact DirectlyReaches.step hpred_reaches hedge hstep.2

/-- Every reachable address is `DirectlyReaches`-reachable from the entry. -/
theorem reachable_reaches {nodes : Array ControlFlowNode} (hn : controlFlow? = some nodes) :
    ∀ a ∈ reachableAddresses, DirectlyReaches nodes reachableEntry a := by
  intro a ha
  have : a ∈ reachableWitness.map (·.addr) := by simpa [reachableAddresses] using ha
  obtain ⟨r, hr, hra⟩ := Array.mem_map.mp this
  exact hra ▸ reaches_of_witness hn r.distance r hr rfl

/-! ## The exact-reachability theorem -/

/-- **`R = directReachable`, both directions.** The materialized `reachableAddresses` equals the exact
static reachable set of the decoded decoder from the entry: forward by the closure/least-fixpoint
lemma, reverse by the per-address witnesses and the generic completeness lemma. Stated as membership
equivalence against the canonical decode. -/
theorem reachableAddresses_eq_directReachable :
    ∃ nodes : Array ControlFlowNode,
      controlFlow? = some nodes ∧
      ∀ a, a ∈ reachableAddresses ↔ a ∈ directReachable nodes reachableEntry := by
  obtain ⟨nodes, hn⟩ := controlFlow_isSome'
  refine ⟨nodes, hn, fun a => ⟨?forward, ?reverse⟩⟩
  case reverse =>
    intro ha
    exact directReachable_subset nodes reachableEntry (· ∈ reachableAddresses)
      (fun x hx t ht => Array.contains_iff_mem.mp (reachable_closed hn x hx t ht))
      (fun _ => Array.contains_iff_mem.mp (forwardClosed_some hn).2.1) a ha
  case forward =>
    intro ha
    exact mem_directReachable_of_reaches nodes reachableEntry a (entry_decoded hn)
      (reachable_reaches hn a ha)

end BinaryFv.Zesu.Elflings.Validation
