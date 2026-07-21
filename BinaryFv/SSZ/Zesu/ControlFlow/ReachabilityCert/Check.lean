import BinaryFv.SSZ.Zesu.ControlFlow.FunctionWords
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Data
import BinaryFv.RiscV.Analysis.Reachability

/-!
# Chunked reachability certificate — per-chunk check

Each ≤128-address chunk of the materialized `reachableAddresses` is validated against the *actual*
decoded control-flow graph: every chunk address must index a decoded node, and every decoded direct
successor of it must stay inside `reachableAddresses`. Because the check dispatches through
`controlFlow?` (returning `false` on a parse/decode failure), a proof that a chunk check is `true`
also certifies that the canonical ELF decoded. These are small immutable-artifact checks
(`native_decide`, per the documented SSZ-layer exception); the composition that assembles them into
`entryReachableInventoryCertificate` is an ordinary kernel proof.
-/

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.ControlFlow

/-- Local validity of one chunk against explicit decoded `nodes`. -/
def sliceValid (nodes : Array ControlFlowNode) (slice : Array Nat) : Bool :=
  slice.all fun a =>
    hasControlFlowAddress nodes a &&
    (directSuccessorsAt nodes a).all (fun t => reachableAddresses.contains t)

/--
Chunk validity dispatched through the canonical decoded control flow.

Uses `Option.map`/`getD` rather than a `match` on `controlFlow?` deliberately: bridging a chunk's
`native_decide` fact to a kernel proof about the decoded `nodes` must *not* force the kernel to
reduce `controlFlow?` (the full ~3984-word ELF decode), which is ~22 s in the kernel reducer. With
`map`/`getD`, `sliceValidC_some` closes by `Option.map_some`/`getD_some` on the `some nodes` supplied
by the hypothesis, never unfolding the decode.
-/
def sliceValidC (slice : Array Nat) : Bool :=
  (controlFlow?.map (fun nodes => sliceValid nodes slice)).getD false

/-- The entry decoder address lies inside the materialized reachable set. Uses `Option.map`/`getD`
    (not `match`) for the same kernel-reduction reason as `sliceValidC`. -/
def entryContained : Bool :=
  (entryFunction?.map (fun entry => reachableAddresses.contains entry.value)).getD false

/--
Turn a chunk check into the two per-address facts it certifies. The successor fact is returned in
`Bool` `contains` form (not `∈`): forming `t ∈ reachableAddresses` for a *concrete* address forces
the kernel to reduce the Decidable-membership instance over the 3369-element set (~22 s). Callers
convert `contains → ∈` only under a binder, where the address stays symbolic and the conversion is
free.
-/
theorem sliceValid_elim {nodes : Array ControlFlowNode} {slice : Array Nat} {a : Nat}
    (h : sliceValid nodes slice = true) (ha : a ∈ slice) :
    hasControlFlowAddress nodes a = true ∧
      ∀ t, t ∈ directSuccessorsAt nodes a → reachableAddresses.contains t = true := by
  unfold sliceValid at h
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem ha
  have hp := Array.all_eq_true.mp h i hi
  rw [Bool.and_eq_true] at hp
  refine ⟨hp.1, ?_⟩
  intro t ht
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem ht
  exact Array.all_eq_true.mp hp.2 j hj

/-- Specialise a dispatched chunk check to explicit decoded `nodes`, without reducing the decode. -/
theorem sliceValidC_some {nodes : Array ControlFlowNode} {slice : Array Nat}
    (hn : controlFlow? = some nodes) (h : sliceValidC slice = true) :
    sliceValid nodes slice = true := by
  unfold sliceValidC at h
  rw [hn] at h
  simpa only [Option.map_some, Option.getD_some] using h

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
