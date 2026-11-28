import ZesuExec.Machine

/-!
# `std.sort.block.mergeInPlace`: the Lean model (programme plan S16)

`mergeInPlace(T, items, A, B, context, lessThan)` merges two adjacent sorted runs `items[A]` and
`items[B]` (`A.end = B.start`) in place: repeatedly it binary-searches B for the first element
not below `A[0]` (`binaryFirst`), rotates A in front of it (`mem.rotate`), and skips the elements
of the new A not above its first one (`binaryLast`) (`std/sort/block.zig`, Zig 0.16).

The model is the order-theoretic meaning of that: the output range is a sorted permutation of
the two inputs (`MergeOf`). The element order is `lt a b = lexLt (key a) (key b)`: Zig's
`std.mem.lessThan(u8, …)` on a byte-string key of each element (the element itself for
`__anon_7964`, the string an element points to for `__anon_11564`). `le a b := !lt b a` is a
total preorder; `Sorted` is pairwise `le`.

The algorithm lemmas (`Inv`, `inv_*`) are the outer loop's invariant over lists: a finished
prefix `P`, the runs `A` and `B` left, every element of `P` at most every element of `A ++ B`.
-/

namespace ZesuExec.Fn.MergeInPlace
open ZesuExec

/-! ## The element order -/

/-- `std.mem.lessThan(u8, a, b)`: the first differing byte decides, a proper prefix is less. -/
def lexLt : List Byte → List Byte → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then lexLt as bs else decide (a.toNat < b.toNat)

theorem lexLt_irrefl : ∀ a : List Byte, lexLt a a = false
  | [] => rfl
  | x :: xs => by simp [lexLt, lexLt_irrefl xs]

theorem lexLt_trans : ∀ {a b c : List Byte}, lexLt a b = true → lexLt b c = true → lexLt a c = true
  | [], [], _, h, _ => by simp [lexLt] at h
  | [], _ :: _, [], _, h => by simp [lexLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [lexLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLt] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [lexLt] at h1 h2 ⊢
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl] at h1
      by_cases hxz : x = z
      · subst hxz; rw [if_pos rfl] at h2 ⊢; exact lexLt_trans h1 h2
      · rw [if_neg hxz] at h2 ⊢; exact h2
    · rw [if_neg hxy] at h1
      have h1' : x.toNat < y.toNat := by simpa using h1
      by_cases hyz : y = z
      · subst hyz; rw [if_neg hxy]; simpa using h1'
      · rw [if_neg hyz] at h2
        have h2' : y.toNat < z.toNat := by simpa using h2
        have hxz : x ≠ z := fun h => by subst h; omega
        rw [if_neg hxz]; simp; omega

/-- Trichotomy. -/
theorem lexLt_total : ∀ a b : List Byte, lexLt a b = true ∨ a = b ∨ lexLt b a = true
  | [], [] => .inr (.inl rfl)
  | [], _ :: _ => .inl rfl
  | _ :: _, [] => .inr (.inr rfl)
  | x :: xs, y :: ys => by
    simp only [lexLt]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, if_pos rfl]
      rcases lexLt_total xs ys with h | h | h
      · exact .inl h
      · exact .inr (.inl (by rw [h]))
      · exact .inr (.inr h)
    · rw [if_neg hxy, if_neg (Ne.symm hxy)]
      have : x.toNat ≠ y.toNat := fun h => hxy (BitVec.eq_of_toNat_eq h)
      by_cases hl : x.toNat < y.toNat
      · exact .inl (by simpa using hl)
      · exact .inr (.inr (by simp; omega))

/-- The order of elements through a key. -/
def ltBy {α : Type} (key : α → List Byte) (a b : α) : Bool := lexLt (key a) (key b)

/-- `a` is not above `b`. -/
def leBy {α : Type} (key : α → List Byte) (a b : α) : Prop := ltBy key b a = false

section
variable {α : Type} {key : α → List Byte}

theorem leBy_refl (a : α) : leBy key a a := lexLt_irrefl _

theorem leBy_of_lt {a b : α} (h : ltBy key a b = true) : leBy key a b := by
  unfold leBy ltBy at *
  cases h' : lexLt (key b) (key a)
  · rfl
  · have := lexLt_trans h h'; rw [lexLt_irrefl] at this; exact absurd this (by simp)

theorem leBy_trans {a b c : α} (h1 : leBy key a b) (h2 : leBy key b c) : leBy key a c := by
  unfold leBy ltBy at *
  cases h : lexLt (key c) (key a)
  · rfl
  · exfalso
    rcases lexLt_total (key c) (key b) with h' | h' | h'
    · rw [h'] at h2; exact absurd h2 (by simp)
    · rw [← h'] at h1; rw [h] at h1; exact absurd h1 (by simp)
    · rw [lexLt_trans h' h] at h1; exact absurd h1 (by simp)

theorem leBy_total (a b : α) : leBy key a b ∨ leBy key b a := by
  unfold leBy ltBy
  rcases lexLt_total (key a) (key b) with h | h | h
  · left; cases h' : lexLt (key b) (key a)
    · rfl
    · have := lexLt_trans h h'; rw [lexLt_irrefl] at this; exact absurd this (by simp)
  · left; rw [h, lexLt_irrefl]
  · right; cases h' : lexLt (key a) (key b)
    · rfl
    · have := lexLt_trans h h'; rw [lexLt_irrefl] at this; exact absurd this (by simp)

/-- Not below and not above is not below, through a chain. -/
theorem lt_of_lt_le {a b c : α} (h1 : ltBy key a b = true) (h2 : leBy key b c) :
    ltBy key a c = true := by
  unfold leBy ltBy at *
  rcases lexLt_total (key a) (key c) with h | h | h
  · exact h
  · rw [← h] at h2; rw [h1] at h2; exact absurd h2 (by simp)
  · rw [lexLt_trans h h1] at h2; exact absurd h2 (by simp)

end

/-! ## The model -/

/-- Non-decreasing under `key`. -/
def Sorted {α : Type} (key : α → List Byte) (l : List α) : Prop := l.Pairwise (leBy key)

/-- **The model.** `zs` is a sorted permutation of `xs ++ ys`. -/
def MergeOf {α : Type} (key : α → List Byte) (xs ys zs : List α) : Prop :=
  zs.Perm (xs ++ ys) ∧ Sorted key zs

/-! ## The outer loop's invariant -/

section
variable {α : Type} {key : α → List Byte}

/-- After some rounds: the finished prefix `P`, the runs `A` and `B` left, a permutation of the
inputs `X ++ Y`. -/
def Inv (key : α → List Byte) (X Y P A B : List α) : Prop :=
  (P ++ A ++ B).Perm (X ++ Y) ∧ Sorted key P ∧ Sorted key A ∧ Sorted key B ∧
    ∀ p ∈ P, ∀ r ∈ A ++ B, leBy key p r

theorem inv_init {X Y : List α} (hX : Sorted key X) (hY : Sorted key Y) : Inv key X Y [] X Y :=
  ⟨by simp, List.Pairwise.nil, hX, hY, by simp⟩

/-- One run empty: the merge is done. -/
theorem inv_done {X Y P A B : List α} (h : Inv key X Y P A B) (hAB : A = [] ∨ B = []) :
    MergeOf key X Y (P ++ A ++ B) := by
  obtain ⟨hp, hP, hA, hB, hle⟩ := h
  refine ⟨hp, ?_⟩
  unfold Sorted
  rw [List.append_assoc, List.pairwise_append]
  refine ⟨hP, ?_, fun p hp r hr => hle p hp r hr⟩
  rcases hAB with rfl | rfl
  · simpa using hB
  · simpa using hA

/-- The elements of `B` below `A`'s first element move to the prefix (`binaryFirst` and the
rotation). -/
theorem inv_first {X Y P A B₁ B₂ : List α} {a₀ : α} (h : Inv key X Y P (a₀ :: A) (B₁ ++ B₂))
    (hB₁ : ∀ b ∈ B₁, ltBy key b a₀ = true) : Inv key X Y (P ++ B₁) (a₀ :: A) B₂ := by
  obtain ⟨hp, hP, hA, hB, hle⟩ := h
  have hB' := List.pairwise_append.mp hB
  refine ⟨?_, ?_, hA, hB'.2.1, ?_⟩
  · refine List.Perm.trans ?_ hp
    simp only [List.append_assoc]
    refine List.Perm.append_left P ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right B₂ List.perm_append_comm
  · unfold Sorted; rw [List.pairwise_append]
    exact ⟨hP, hB'.1, fun p hp b hb => hle p hp b (by simp [hb])⟩
  · intro p hp r hr
    rcases List.mem_append.mp hp with hp | hp
    · exact hle p hp r (by
        rcases List.mem_append.mp hr with hr | hr
        · exact List.mem_append_left _ hr
        · exact List.mem_append_right _ (List.mem_append_right _ hr))
    · rcases List.mem_append.mp hr with hr | hr
      · have h0 := hB₁ p hp
        rcases List.mem_cons.mp hr with rfl | hr
        · exact leBy_of_lt h0
        · exact leBy_of_lt (lt_of_lt_le h0 (List.rel_of_pairwise_cons hA hr))
      · exact hB'.2.2 p hp r hr

/-- The elements of `A` not above its first element move to the prefix (`binaryLast`), when
`B`'s first element is not below it. -/
theorem inv_last {X Y P A₁ A₂ B : List α} {a₀ b₀ : α}
    (h : Inv key X Y P (a₀ :: A₁ ++ A₂) (b₀ :: B))
    (hA₁ : ∀ a ∈ A₁, ltBy key a₀ a = false) (hb : leBy key a₀ b₀) :
    Inv key X Y (P ++ a₀ :: A₁) A₂ (b₀ :: B) := by
  obtain ⟨hp, hP, hA, hB, hle⟩ := h
  have hA' := List.pairwise_append.mp hA
  have ha₀b : ∀ a ∈ a₀ :: A₁, ∀ r ∈ b₀ :: B, leBy key a r := by
    intro a ha r hr
    have hab : leBy key a b₀ := by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hb
      · exact leBy_trans (hA₁ a ha) hb
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hab
    · exact leBy_trans hab (List.rel_of_pairwise_cons hB hr)
  refine ⟨by simpa [List.append_assoc] using hp, ?_, hA'.2.1, hB, ?_⟩
  · unfold Sorted; rw [List.pairwise_append]
    exact ⟨hP, hA'.1, fun p hp a ha => hle p hp a (List.mem_append_left _
      (List.mem_append_left _ ha))⟩
  · intro p hp r hr
    rcases List.mem_append.mp hp with hp | hp
    · exact hle p hp r (by
        rcases List.mem_append.mp hr with hr | hr
        · exact List.mem_append_left _ (List.mem_append_right _ hr)
        · exact List.mem_append_right _ hr)
    · rcases List.mem_append.mp hr with hr | hr
      · exact hA'.2.2 p hp r hr
      · exact ha₀b p hp r hr

end

end ZesuExec.Fn.MergeInPlace
