import BinaryFv.RiscV.Analysis.Reachability

/-!
# Completeness (minimality) of `directReachable`

`Reachability.lean` gives the *forward* over-approximation: `directReachable` is contained in any set
that holds the entry and is closed under decoded successors. This file gives the *reverse*: every
address actually reachable from the entry (through decoded direct successors) is returned by
`directReachable`. Together they pin `directReachable` as EXACTLY the reachable set — so a materialized
candidate proved equal to it in both directions is the exact reachable set, never a mere
over-approximation.

The engine is that `directReachable nodes entry` is a genuine *fixpoint* of `expandDirectReachability`:
the bounded search (`nodes.size + 1` passes) is guaranteed to reach a pass that adds nothing, because
the accumulator stays duplicate-free and decoded, hence bounded by `nodes.size`, and a non-fixpoint
pass strictly grows it. A fixpoint is closed under decoded successors, and closure plus containing the
entry lets an ordinary induction over a reachability path place every reachable address in the result.

Everything here is an ordinary kernel proof — no compiled decision procedures, no axiom — as required
of the generic `BinaryFv.RiscV` layer.
-/

namespace BinaryFv.RiscV

open LeanRV64DExecutable.Functions

/-! ## Reachability through decoded direct successors -/

/-- `a` is reachable from `entry` through decoded direct successors: the entry reaches itself, and a
reached address's decoded direct successor is reached. `directSuccessorsAt` is the parser-owned decoded
direct-edge relation, so this is purely static direct reachability. -/
inductive DirectlyReaches (nodes : Array ControlFlowNode) (entry : Nat) : Nat → Prop
  | base : DirectlyReaches nodes entry entry
  | step {p a : Nat} : DirectlyReaches nodes entry p →
      a ∈ directSuccessorsAt nodes p → hasControlFlowAddress nodes a = true →
      DirectlyReaches nodes entry a

/-! ## `append`/`expand` grow, capture decoded candidates, and preserve nodup + decoded -/

/-- `appendKnownAddresses` only grows the accumulator. -/
theorem subset_appendKnownAddresses (nodes : Array ControlFlowNode) (known candidates : Array Nat) :
    ∀ x, x ∈ known → x ∈ appendKnownAddresses nodes known candidates := by
  intro x hx
  unfold appendKnownAddresses
  refine Array.foldl_induction (motive := fun _ acc => x ∈ acc) hx ?step
  intro i acc ih
  split
  · exact Array.mem_push.mpr (Or.inl ih)
  · exact ih

/-- Every decoded candidate ends up in `appendKnownAddresses`. -/
theorem mem_appendKnownAddresses_of_candidate (nodes : Array ControlFlowNode)
    (known candidates : Array Nat) :
    ∀ t, t ∈ candidates → hasControlFlowAddress nodes t = true →
      t ∈ appendKnownAddresses nodes known candidates := by
  intro t ht hdec
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem ht
  unfold appendKnownAddresses
  refine Array.foldl_induction
    (motive := fun n acc => ∀ j, (hj : j < candidates.size) → j < n →
      hasControlFlowAddress nodes candidates[j] = true → candidates[j] ∈ acc) ?base ?step
      i hi (by omega) hdec
  · intro j _ hj0 _; exact absurd hj0 (by omega)
  · intro n acc ih j hj hjn hjdec
    by_cases hlt : j < n.1
    · -- already captured; the step only grows the accumulator
      have := ih j hj hlt hjdec
      split
      · exact Array.mem_push.mpr (Or.inl this)
      · exact this
    · -- j = n; capture candidates[n]
      have hjn' : j = n.1 := by omega
      subst hjn'
      split
      · rename_i hcond
        exact Array.mem_push.mpr (Or.inr (by simp))
      · rename_i hcond
        rw [Bool.not_eq_true, Bool.and_eq_false_iff] at hcond
        rcases hcond with h | h
        · exact absurd hjdec (by simpa [Fin.getElem_fin] using h)
        · rw [Bool.not_eq_false', Array.any_eq_true] at h
          obtain ⟨k, hk, hbeq⟩ := h
          rw [beq_iff_eq] at hbeq
          exact hbeq ▸ Array.getElem_mem hk

/-- `expandDirectReachability` only grows the accumulator. -/
theorem subset_expandDirectReachability (nodes : Array ControlFlowNode) (known : Array Nat) :
    ∀ x, x ∈ known → x ∈ expandDirectReachability nodes known := by
  intro x hx
  unfold expandDirectReachability
  refine Array.foldl_induction (motive := fun _ acc => x ∈ acc) hx ?step
  intro i acc ih
  exact subset_appendKnownAddresses nodes acc _ x ih

/-- Every decoded direct successor of a known address is captured by one expansion pass. -/
theorem mem_expandDirectReachability_of_succ (nodes : Array ControlFlowNode) (known : Array Nat)
    (p t : Nat) (hp : p ∈ known) (ht : t ∈ directSuccessorsAt nodes p)
    (hdec : hasControlFlowAddress nodes t = true) :
    t ∈ expandDirectReachability nodes known := by
  obtain ⟨ip, hip, rfl⟩ := Array.getElem_of_mem hp
  unfold expandDirectReachability
  refine Array.foldl_induction (motive := fun n acc => ip < n → t ∈ acc) ?base ?step hip
  · intro h; exact absurd h (by omega)
  · intro n acc ih hlt
    by_cases hcase : ip < n.1
    · exact subset_appendKnownAddresses nodes acc _ t (ih hcase)
    · have hEq : ip = n.1 := by omega
      subst hEq
      exact mem_appendKnownAddresses_of_candidate nodes acc _ t ht hdec

/-! ## Nodup + decoded invariants -/

/-- `appendKnownAddresses` preserves duplicate-freeness. -/
theorem nodup_appendKnownAddresses (nodes : Array ControlFlowNode) (known candidates : Array Nat)
    (hnd : known.toList.Nodup) : (appendKnownAddresses nodes known candidates).toList.Nodup := by
  unfold appendKnownAddresses
  refine Array.foldl_induction (motive := fun (_ : Nat) (acc : Array Nat) => acc.toList.Nodup)
    hnd ?step
  intro i acc ih
  split
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    rw [Array.toList_push, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro x hx b hb heq
    have hbeq : b = candidates[i] := by simpa using hb
    rw [hbeq] at heq
    have hmem : acc.any (fun a => a == x) = true := Array.any_eq_true.mpr
      (by obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
          exact ⟨k, by simpa using hk, by simp⟩)
    rw [heq] at hmem
    rw [Bool.not_eq_true'] at hcond
    exact absurd hmem (by rw [hcond.2]; simp)
  · exact ih

/-- `appendKnownAddresses` keeps every accumulator element decoded, given the candidates come from a
decoded pool is not needed: it only ever pushes decoded candidates. -/
theorem decoded_appendKnownAddresses (nodes : Array ControlFlowNode) (known candidates : Array Nat)
    (hknown : ∀ x ∈ known, hasControlFlowAddress nodes x = true) :
    ∀ x ∈ appendKnownAddresses nodes known candidates, hasControlFlowAddress nodes x = true := by
  unfold appendKnownAddresses
  refine Array.foldl_induction
    (motive := fun _ acc => ∀ x ∈ acc, hasControlFlowAddress nodes x = true) hknown ?step
  intro i acc ih
  split
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    intro x hx
    rcases Array.mem_push.mp hx with h | h
    · exact ih x h
    · exact h ▸ hcond.1
  · exact ih

/-- `expandDirectReachability` preserves duplicate-freeness. -/
theorem nodup_expandDirectReachability (nodes : Array ControlFlowNode) (known : Array Nat)
    (hnd : known.toList.Nodup) : (expandDirectReachability nodes known).toList.Nodup := by
  unfold expandDirectReachability
  refine Array.foldl_induction (motive := fun (_ : Nat) (acc : Array Nat) => acc.toList.Nodup)
    hnd ?step
  intro i acc ih
  exact nodup_appendKnownAddresses nodes acc _ ih

/-- `expandDirectReachability` keeps every accumulator element decoded. -/
theorem decoded_expandDirectReachability (nodes : Array ControlFlowNode) (known : Array Nat)
    (hknown : ∀ x ∈ known, hasControlFlowAddress nodes x = true) :
    ∀ x ∈ expandDirectReachability nodes known, hasControlFlowAddress nodes x = true := by
  unfold expandDirectReachability
  refine Array.foldl_induction
    (motive := fun _ acc => ∀ x ∈ acc, hasControlFlowAddress nodes x = true) hknown ?step
  intro i acc ih
  exact decoded_appendKnownAddresses nodes acc _ ih

/-! ## The pigeonhole bound -/

/-- A duplicate-free list contained (element-wise) in another list is no longer than it. Proved by
peeling off the head and erasing its image from the containing list, so the tail (still duplicate-free
and contained) recurses into one element fewer. -/
theorem length_le_of_nodup_subset {l₁ l₂ : List Nat} (hnd : l₁.Nodup) (hsub : l₁ ⊆ l₂) :
    l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => exact Nat.zero_le _
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hat, hndt⟩ := hnd
    have ha : a ∈ l₂ := hsub List.mem_cons_self
    have ht : t ⊆ l₂.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => hat (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr (hsub (List.mem_cons_of_mem a hx))
    have hlen := ih hndt ht
    have herase : (l₂.erase a).length = l₂.length - 1 := List.length_erase_of_mem ha
    have hpos : 0 < l₂.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- A duplicate-free array of decoded addresses has at most `nodes.size` elements: every element is a
node address, and the node addresses number `nodes.size`. -/
theorem size_le_of_nodup_decoded (nodes : Array ControlFlowNode) (known : Array Nat)
    (hnd : known.toList.Nodup) (hdec : ∀ x ∈ known, hasControlFlowAddress nodes x = true) :
    known.size ≤ nodes.size := by
  have hsub : known.toList ⊆ (nodes.toList.map (·.word.encoded.address)) := by
    intro x hx
    have hx' : x ∈ known := by simpa using hx
    have := hdec x hx'
    unfold hasControlFlowAddress at this
    obtain ⟨n, hn, hbeq⟩ := Array.any_eq_true.mp this
    rw [beq_iff_eq] at hbeq
    exact List.mem_map.mpr ⟨nodes[n], by simp [Array.getElem_mem hn], hbeq⟩
  have hle := length_le_of_nodup_subset hnd hsub
  simpa using hle

/-! ## The fixpoint / closure of the bounded search -/

/-- A fixpoint pass (equal sizes) from a duplicate-free seed contains exactly the seed's elements:
the pigeonhole bound rules out gaining an element without losing one, since the seed already injects
into the pass. -/
theorem mem_expand_iff_of_size_eq (nodes : Array ControlFlowNode) (known : Array Nat)
    (hnd : known.toList.Nodup)
    (hsize : (expandDirectReachability nodes known).size = known.size) :
    ∀ x, x ∈ expandDirectReachability nodes known ↔ x ∈ known := by
  intro x
  refine ⟨fun hx => ?_, subset_expandDirectReachability nodes known x⟩
  by_cases hxk : x ∈ known
  · exact hxk
  exfalso
  have hsub' : known.toList ⊆ (expandDirectReachability nodes known).toList.erase x := by
    intro y hy
    have hy' : y ∈ known := Array.mem_toList_iff.mp hy
    have hyx : y ≠ x := fun h => hxk (h ▸ hy')
    exact (List.mem_erase_of_ne hyx).mpr
      (Array.mem_toList_iff.mpr (subset_expandDirectReachability nodes known y hy'))
  have hlen := length_le_of_nodup_subset hnd hsub'
  have hx' : x ∈ (expandDirectReachability nodes known).toList := Array.mem_toList_iff.mpr hx
  have herase : ((expandDirectReachability nodes known).toList.erase x).length =
      (expandDirectReachability nodes known).size - 1 :=
    List.length_erase_of_mem hx'
  have hpos : 0 < (expandDirectReachability nodes known).toList.length :=
    List.length_pos_of_mem hx'
  simp only [Array.length_toList] at hlen hpos
  omega

/-- If a pass is a fixpoint, the set is closed under decoded successors. -/
theorem closed_of_expand_eq (nodes : Array ControlFlowNode) (known : Array Nat)
    (hfix : ∀ x, x ∈ expandDirectReachability nodes known ↔ x ∈ known) :
    ∀ a ∈ known, ∀ t, t ∈ directSuccessorsAt nodes a → hasControlFlowAddress nodes t = true →
      t ∈ known := by
  intro a ha t ht hdec
  have := mem_expandDirectReachability_of_succ nodes known a t ha ht hdec
  exact (hfix t).mp this

/-- **The bounded search reaches a fixpoint.** With enough fuel (`fuel + known.size ≥ nodes.size + 1`)
and a duplicate-free decoded seed, `directReachableLoop` returns a set closed under decoded successors:
each non-fixpoint pass strictly grows a set bounded by `nodes.size`, so a fixpoint pass must occur. -/
theorem directReachableLoop_closed (nodes : Array ControlFlowNode) :
    ∀ fuel known, known.toList.Nodup → (∀ x ∈ known, hasControlFlowAddress nodes x = true) →
      nodes.size + 1 ≤ fuel + known.size →
      ∀ a ∈ directReachableLoop nodes fuel known, ∀ t,
        t ∈ directSuccessorsAt nodes a → hasControlFlowAddress nodes t = true →
        t ∈ directReachableLoop nodes fuel known := by
  intro fuel
  induction fuel with
  | zero =>
    intro known _ hdec hbound
    have := size_le_of_nodup_decoded nodes known (by assumption) hdec
    omega
  | succ f ih =>
    intro known hnd hdec hbound
    rw [directReachableLoop]
    split
    · -- fixpoint pass
      rename_i hsize
      have hfix := mem_expand_iff_of_size_eq nodes known hnd (by simpa using hsize)
      exact closed_of_expand_eq nodes known hfix
    · -- grew: recurse with the strictly larger, still-nodup/decoded set
      rename_i hsize
      have hne : (expandDirectReachability nodes known).size ≠ known.size := by simpa using hsize
      have hsub : known.toList ⊆ (expandDirectReachability nodes known).toList := by
        intro x hx
        exact Array.mem_toList_iff.mpr
          (subset_expandDirectReachability nodes known x (Array.mem_toList_iff.mp hx))
      have hle : known.size ≤ (expandDirectReachability nodes known).size := by
        simpa using length_le_of_nodup_subset hnd hsub
      have hgrow : known.size < (expandDirectReachability nodes known).size := by omega
      exact ih (expandDirectReachability nodes known)
        (nodup_expandDirectReachability nodes known hnd)
        (decoded_expandDirectReachability nodes known hdec)
        (by omega)

/-! ## Accumulation and the completeness theorem -/

/-- `directReachableLoop` only grows its seed. -/
theorem subset_directReachableLoop (nodes : Array ControlFlowNode) :
    ∀ fuel known, ∀ x ∈ known, x ∈ directReachableLoop nodes fuel known := by
  intro fuel
  induction fuel with
  | zero => intro known x hx; simpa [directReachableLoop] using hx
  | succ f ih =>
    intro known x hx
    rw [directReachableLoop]
    split
    · exact hx
    · exact ih _ x (subset_expandDirectReachability nodes known x hx)

/-- **Completeness of `directReachable`.** Every address reachable from a decoded entry through decoded
direct successors is returned by `directReachable`. This is the reverse inclusion that, with
`directReachable_subset`, makes `directReachable` the EXACT reachable set. -/
theorem mem_directReachable_of_reaches (nodes : Array ControlFlowNode) (entry a : Nat)
    (hentry : hasControlFlowAddress nodes entry = true)
    (hreach : DirectlyReaches nodes entry a) :
    a ∈ directReachable nodes entry := by
  unfold directReachable
  rw [if_pos hentry]
  have hnd : (#[entry] : Array Nat).toList.Nodup := by simp
  have hdec : ∀ x ∈ (#[entry] : Array Nat), hasControlFlowAddress nodes x = true := by
    intro x hx; rw [Array.mem_singleton] at hx; exact hx ▸ hentry
  have hclosed := directReachableLoop_closed nodes (nodes.size + 1) #[entry] hnd hdec (by simp)
  induction hreach with
  | base =>
    exact subset_directReachableLoop nodes (nodes.size + 1) #[entry] entry (Array.mem_singleton.mpr rfl)
  | step _ hedge hdeca ih =>
    exact hclosed _ ih _ hedge hdeca

end BinaryFv.RiscV
