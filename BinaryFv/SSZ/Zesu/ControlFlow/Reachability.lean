import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Entry
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk00
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk01
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk02
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk03
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk04
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk05
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk06
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk07
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk08
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk09
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk10
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk11
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk12
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk13
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk14
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk15
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk16
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk17
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk18
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk19
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk20
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk21
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk22
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk23
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk24
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk25
import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Chunk26

-- The materialized reachable set is a 27-fold `++` of 128-element literals; elaborating
-- membership/append rewrites over it exceeds the default recursion depth.
set_option maxRecDepth 8000

/-!
# The pinned SSZ decoder's static reachability certificate

Interim hand-chunked replacement for the former monolithic reachability `native_decide`
(which cost ~40 min single-core: the pathological `directReachable` fixpoint, not term
compilation). `reachableAddresses` is validated in 27 independent ≤128-address
`native_decide` chunk modules; this module composes them with an ordinary kernel proof and
connects the result to the actual algorithm via the generic
`BinaryFv.RiscV.directReachable_subset` least-fixpoint lemma, yielding
`directReachable nodes entry ⊆ reachableAddresses` — a sound over-approximation of the
decoder's static reachability. The reverse (minimality) needs per-address reachability
witnesses and is supplied by the deterministic generator's certificate (milestone 6), which
supersedes this module.
-/

namespace BinaryFv.SSZ.Zesu.ControlFlow

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- The canonical ELF decodes to some node array. -/
theorem controlFlow_isSome : ∃ nodes, controlFlow? = some nodes :=
  Option.isSome_iff_exists.mp controlFlow_isSome_bool

/-- The entry symbol resolves and its address is inside the reachable set (`Bool` form,
    keeping the concrete entry address out of a Decidable-membership reduction). -/
theorem entryFunction_isSome :
    ∃ entry, entryFunction? = some entry ∧ reachableAddresses.contains entry.value = true := by
  obtain ⟨entry, he⟩ := Option.isSome_iff_exists.mp entryFunction_isSome_bool
  refine ⟨entry, he, ?_⟩
  have h := entry_contained
  unfold entryContained at h
  -- targeted `rw` only (never `simp`, which would try to *evaluate* `contains` over the
  -- 3369-element set and blow up); these lemmas just peel `map`/`getD` on `some entry`.
  rw [he, Option.map_some, Option.getD_some] at h
  exact h

/-- Every materialized reachable address indexes a decoded node, and every decoded direct
    successor of it stays inside the reachable set (assembled from the 27 chunk checks). The
    successor fact is in `Bool` `contains` form so no concrete address membership is reduced. -/
theorem reachable_addr_props {nodes : Array ControlFlowNode}
    (hn : controlFlow? = some nodes) :
    ∀ a, a ∈ reachableAddresses →
      hasControlFlowAddress nodes a = true ∧
        ∀ t, t ∈ directSuccessorsAt nodes a → reachableAddresses.contains t = true := by
  intro a ha
  simp only [reachableAddresses, Array.mem_append, or_assoc] at ha
  rcases ha with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact sliceValid_elim (sliceValidC_some hn chunk_00) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_01) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_02) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_03) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_04) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_05) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_06) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_07) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_08) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_09) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_10) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_11) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_12) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_13) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_14) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_15) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_16) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_17) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_18) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_19) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_20) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_21) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_22) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_23) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_24) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_25) h
  · exact sliceValid_elim (sliceValidC_some hn chunk_26) h

/--
The exposed reachability certificate for the pinned SSZ decoder: the materialized
`reachableAddresses` contains the entry, every listed address indexes a decoded node, it is
closed under the decoded direct-successor relation, and it over-approximates the actual
`directReachable` search (`⊆`) via the generic least-fixpoint lemma. Interim hand-chunk;
superseded by the generator (milestone 6). `contains … = true` is `· ∈ reachableAddresses` in
`Bool` form; it is used for the concrete entry address to avoid a costly kernel reduction of
the Decidable-membership instance over the 3369-element set.
-/
theorem entryReachableInventoryCertificate :
    ∃ (nodes : Array ControlFlowNode) (entry : StaticSymbol),
      controlFlow? = some nodes ∧ entryFunction? = some entry ∧
      reachableAddresses.contains entry.value = true ∧
      (∀ a, a ∈ reachableAddresses → hasControlFlowAddress nodes a = true) ∧
      (∀ a, a ∈ reachableAddresses →
        ∀ t, t ∈ directSuccessorsAt nodes a → t ∈ reachableAddresses) ∧
      (∀ a, a ∈ directReachable nodes entry.value → a ∈ reachableAddresses) := by
  obtain ⟨nodes, hn⟩ := controlFlow_isSome
  obtain ⟨entry, he, hentry⟩ := entryFunction_isSome
  refine ⟨nodes, entry, hn, he, hentry, ?_, ?_, ?_⟩
  · intro a ha; exact (reachable_addr_props hn a ha).1
  · intro a ha t ht
    exact Array.contains_iff_mem.mp ((reachable_addr_props hn a ha).2 t ht)
  · intro a ha
    refine Array.contains_iff_mem.mp (directReachable_subset nodes entry.value
      (fun x => reachableAddresses.contains x = true) ?_ (fun _ => hentry) a ha)
    intro b hbC t ht
    exact (reachable_addr_props hn b (Array.contains_iff_mem.mp hbC)).2 t ht

end BinaryFv.SSZ.Zesu.ControlFlow
