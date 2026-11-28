import ZesuExec.Fn.MergeInPlace.Spec

/-!
# `mergeInPlace` copies: windows of elements, the rotation, the searches

The machine-independent half of every copy's proof, over a byte function `G` (element `e`,
byte `o`) and the element order `key`:

* `win` algebra: `win_split`, `win_cons`, `win_congr`, `mem_win`, sorted windows (`sorted_le`,
  `sorted_sub`).
* the rotation: the three reversals `rev` (shared with `Fn/Rotate`) of `[lo, lo+n)` by `a` are
  `rot`, and `win_rot`: the window becomes `[lo+a, lo+n) ++ [lo, lo+a)`.
* the byte comparison: `lex_step` (one byte of `std.mem.lessThan`).
* the searches: `First`/`Last` (the loop invariants of `binaryFirst`/`binaryLast`) and their
  steps.
-/

namespace ZesuExec.Fn.MergeInPlace
open ZesuExec ZesuExec.Fn.Rotate

/-! ## Windows -/

section
variable {G G' : Nat → Nat → Byte}

theorem win_split {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    win G lo hi = win G lo mid ++ win G mid hi := by
  unfold win
  have : List.range' lo (hi - lo) = List.range' lo (mid - lo) ++ List.range' (lo + (mid - lo)) (hi - mid) := by
    rw [List.range'_append_1]; congr 1; omega
  rw [this, show lo + (mid - lo) = mid by omega, List.map_append]

theorem win_nil {lo hi : Nat} (h : hi ≤ lo) : win G lo hi = [] := by
  simp [win, show hi - lo = 0 by omega]

theorem win_cons {lo hi : Nat} (h : lo < hi) : win G lo hi = el G lo :: win G (lo + 1) hi := by
  unfold win
  rw [show hi - lo = (hi - (lo + 1)) + 1 by omega, List.range'_succ]
  simp

theorem win_one (lo : Nat) : win G lo (lo + 1) = [el G lo] := by
  rw [win_cons (by omega), win_nil (by omega)]

theorem mem_win {lo hi : Nat} {x : List Byte} :
    x ∈ win G lo hi ↔ ∃ e, lo ≤ e ∧ e < hi ∧ el G e = x := by
  simp only [win, List.mem_map, List.mem_range']
  constructor
  · rintro ⟨e, ⟨i, hi', rfl⟩, rfl⟩; exact ⟨_, by omega, by omega, rfl⟩
  · rintro ⟨e, h1, h2, rfl⟩; exact ⟨e, ⟨e - lo, by omega, by omega⟩, rfl⟩

theorem win_congr {lo hi : Nat} (h : ∀ e, lo ≤ e → e < hi → el G e = el G' e) :
    win G lo hi = win G' lo hi := by
  unfold win
  apply List.map_congr_left
  intro e he
  rw [List.mem_range'] at he
  obtain ⟨i, hi', rfl⟩ := he
  exact h _ (by omega) (by omega)

theorem el_congr {e : Nat} (h : ∀ o < 32, G e o = G' e o) : el G e = el G' e := by
  unfold el; apply List.map_congr_left; intro o ho; exact h o (List.mem_range.mp ho)

theorem el_eq {e e' : Nat} (h : ∀ o < 32, G e o = G' e' o) : el G e = el G' e' := by
  unfold el; apply List.map_congr_left; intro o ho; exact h o (List.mem_range.mp ho)

theorem length_win (lo hi : Nat) : (win G lo hi).length = hi - lo := by simp [win]

variable {key : List Byte → List Byte}

theorem sorted_sub {lo hi lo' hi' : Nat} (hs : Sorted key (win G lo hi)) (h1 : lo ≤ lo')
    (h2 : lo' ≤ hi') (h3 : hi' ≤ hi) : Sorted key (win G lo' hi') := by
  rw [win_split h1 (show lo' ≤ hi by omega), win_split h2 h3] at hs
  unfold Sorted at *
  exact (List.pairwise_append.mp (List.pairwise_append.mp hs).2.1).1

theorem sorted_le {lo hi i j : Nat} (hs : Sorted key (win G lo hi)) (h1 : lo ≤ i) (h2 : i ≤ j)
    (h3 : j < hi) : leBy key (el G i) (el G j) := by
  rcases Nat.lt_or_ge i j with hij | hij
  · rw [win_split (show lo ≤ j by omega) (show j ≤ hi by omega)] at hs
    exact (List.pairwise_append.mp hs).2.2 _ (mem_win.mpr ⟨i, h1, hij, rfl⟩) _
      (mem_win.mpr ⟨j, Nat.le_refl _, h3, rfl⟩)
  · rw [show j = i by omega]; exact leBy_refl _

end

/-! ## The rotation -/

/-- `[lo, lo+n)` rotated left by `a`: element `e` gets element `lo + (e - lo + a) % n`. -/
def rot (lo a n : Nat) (F : Nat → Nat → Byte) (e o : Nat) : Byte :=
  if lo ≤ e ∧ e < lo + n then F (lo + (e - lo + a) % n) o else F e o

/-- The three reversals of `mem.rotate` on `[lo, lo+n)` by `a`. -/
theorem rev3_rot {lo a n : Nat} (F : Nat → Nat → Byte) (ha : a ≤ n) :
    rev lo n (rev (lo + a) (n - a) (rev lo a F)) = rot lo a n F := by
  funext e o
  simp only [rot]
  by_cases he : lo ≤ e ∧ e < lo + n
  · rw [if_pos he]
    have hm : (e - lo + a) % n = if e - lo + a < n then e - lo + a else e - lo + a - n := by
      split
      · exact Nat.mod_eq_of_lt (by omega)
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hm]
    by_cases h : e - lo + a < n
    · rw [if_pos h]; simp only [rev]
      rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]; congr 1; omega
    · rw [if_neg h]; simp only [rev]
      rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]; congr 1; omega
  · rw [if_neg he]; simp only [rev]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem win_rot {lo a n : Nat} (F : Nat → Nat → Byte) (ha : a ≤ n) :
    win (rot lo a n F) lo (lo + n) = win F (lo + a) (lo + n) ++ win F lo (lo + a) := by
  apply List.ext_getElem
  · simp [length_win]; omega
  · intro i h1 h2
    simp only [length_win] at h1
    rw [List.getElem_append]
    simp only [win, List.getElem_map, List.getElem_range', List.length_map, List.length_range']
    split
    · apply el_eq; intro o _; simp only [rot]
      rw [if_pos (by omega)]; congr 1
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · apply el_eq; intro o _; simp only [rot]
      rw [if_pos (by omega)]; congr 1
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem el_rot_out {lo a n e : Nat} (F : Nat → Nat → Byte) (he : ¬ (lo ≤ e ∧ e < lo + n)) :
    el (rot lo a n F) e = el F e :=
  el_congr fun o _ => by simp only [rot]; rw [if_neg he]

/-! ## The byte comparison -/

/-- One byte of `std.mem.lessThan` on two element suffixes. -/
theorem lex_step (f g : Nat → Byte) (k n : Nat) :
    lexLt ((List.range' k (n + 1)).map f) ((List.range' k (n + 1)).map g) =
      if f k = g k then lexLt ((List.range' (k + 1) n).map f) ((List.range' (k + 1) n).map g)
      else decide ((f k).toNat < (g k).toNat) := by
  simp only [List.range'_succ, List.map_cons, lexLt]

theorem el_range' (G : Nat → Nat → Byte) (e : Nat) : el G e = (List.range' 0 32).map (G e) := by
  simp [el, List.range_eq_range']

/-! ## The searches -/

section
variable {key : List Byte → List Byte} {G : Nat → Nat → Byte}

/-- `binaryFirst(v, [lo, hi))` before a probe: everything below `curr` is below `v`, nothing from
`curr + size` on is. -/
def First (key : List Byte → List Byte) (G : Nat → Nat → Byte) (v : List Byte)
    (lo hi curr size : Nat) : Prop :=
  lo ≤ curr ∧ curr + size ≤ hi ∧ (∀ i, lo ≤ i → i < curr → ltBy key (el G i) v = true) ∧
    ∀ i, curr + size ≤ i → i < hi → ltBy key (el G i) v = false

/-- `binaryLast(v, [lo, hi))` before a probe: nothing below `curr` is above `v`, everything from
`curr + size` on is. -/
def Last (key : List Byte → List Byte) (G : Nat → Nat → Byte) (v : List Byte)
    (lo hi curr size : Nat) : Prop :=
  lo ≤ curr ∧ curr + size ≤ hi ∧ (∀ i, lo ≤ i → i < curr → ltBy key v (el G i) = false) ∧
    ∀ i, curr + size ≤ i → i < hi → ltBy key v (el G i) = true

theorem first_init {v : List Byte} {lo hi : Nat} (h : lo ≤ hi) : First key G v lo hi lo (hi - lo) :=
  ⟨Nat.le_refl _, by omega, fun i h1 h2 => absurd h2 (by omega), fun i h1 h2 => absurd h2 (by omega)⟩

theorem last_init {v : List Byte} {lo hi : Nat} (h : lo ≤ hi) : Last key G v lo hi lo (hi - lo) :=
  ⟨Nat.le_refl _, by omega, fun i h1 h2 => absurd h2 (by omega), fun i h1 h2 => absurd h2 (by omega)⟩

theorem lt_of_le_lt {a b c : List Byte} (h1 : leBy key a b) (h2 : ltBy key b c = true) :
    ltBy key a c = true := by
  cases h : ltBy key a c
  · exfalso
    have h3 : leBy key c a := h
    have := lt_of_lt_le h2 (leBy_trans h3 h1)
    rw [show ltBy key b b = false from leBy_refl b] at this; exact absurd this (by simp)
  · rfl

/-- A probe of `binaryFirst` at `curr + size/2` with result `r`. -/
theorem first_step {v : List Byte} {lo hi curr size : Nat} (hs : Sorted key (win G lo hi))
    (h : First key G v lo hi curr size) (hsz : 0 < size) :
    First key G v lo hi
      (if ltBy key (el G (curr + size / 2)) v then curr + size % 2 + size / 2 else curr) (size / 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hmid : curr + size / 2 < hi := by omega
  cases hr : ltBy key (el G (curr + size / 2)) v <;> simp only [Bool.false_eq_true, if_false, if_true]
  · refine ⟨h1, by omega, h3, fun i hi1 hi2 => ?_⟩
    cases h' : ltBy key (el G i) v
    · rfl
    · exfalso
      have := lt_of_le_lt (sorted_le hs (by omega) hi1 hi2) h'
      rw [hr] at this; exact absurd this (by simp)
  · refine ⟨by omega, by omega, fun i hi1 hi2 => ?_, fun i hi1 hi2 => h4 i (by omega) hi2⟩
    rcases Nat.lt_or_ge i curr with hc | hc
    · exact h3 i hi1 hc
    · exact lt_of_le_lt (sorted_le hs hi1 (by omega) hmid) hr

/-- A probe of `binaryLast` at `curr + size/2` with result `r`. -/
theorem last_step {v : List Byte} {lo hi curr size : Nat} (hs : Sorted key (win G lo hi))
    (h : Last key G v lo hi curr size) (hsz : 0 < size) :
    Last key G v lo hi
      (if ltBy key v (el G (curr + size / 2)) then curr else curr + size % 2 + size / 2) (size / 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hmid : curr + size / 2 < hi := by omega
  cases hr : ltBy key v (el G (curr + size / 2)) <;> simp only [Bool.false_eq_true, if_false, if_true]
  · refine ⟨by omega, by omega, fun i hi1 hi2 => ?_, fun i hi1 hi2 => h4 i (by omega) hi2⟩
    rcases Nat.lt_or_ge i curr with hc | hc
    · exact h3 i hi1 hc
    · cases h' : ltBy key v (el G i)
      · rfl
      · exfalso
        have := lt_of_lt_le h' (sorted_le hs (by omega) (show i ≤ curr + size / 2 by omega) hmid)
        rw [hr] at this; exact absurd this (by simp)
  · refine ⟨h1, by omega, h3, fun i hi1 hi2 => ?_⟩
    exact lt_of_lt_le hr (sorted_le hs (by omega) (by omega) hi2)

end

end ZesuExec.Fn.MergeInPlace
