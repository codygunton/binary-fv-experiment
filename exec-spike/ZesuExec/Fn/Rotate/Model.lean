import ZesuExec.Fn.Common

/-!
# `std.mem.rotate`: the byte model shared by every copy (programme plan S16)

Zig's `rotate(T, items, amount)` is `reverse(items[0..amount])`, `reverse(items[amount..])`,
`reverse(items)` (`std/mem.zig`, `rotate` and `reverse`); each `reverse` swaps element `i` with
element `L-1-i` for `i < L/2`, and the compiled copies swap an element byte by byte. The copies
differ in the element size `E` only, so this file states everything over `E`:

* `SliceIs E n p m G`: the `n` elements of `E` bytes at `p` hold `G e o` (byte `o` of element
  `e`).
* `rev lo L F`: elements `[lo, lo+L)` of `F` reversed. `revAt lo L i k F`: the same after `i`
  whole swaps and the first `k` bytes of swap `i` (the state at an inner loop head).
* `revAt_zero`, `revAt_next`, `revAt_full`: the loop heads' states chain into `rev`;
  `slice_swap` with `revAt_succ`: one byte swap moves `revAt … k` to `revAt … (k+1)`;
  `rev_rotate`: the three reversals are the rotation `e ↦ (e + amount) % n`.
-/

namespace ZesuExec.Fn.Rotate
open ZesuExec ZesuExec.Sym

/-- The `n` elements of `E` bytes at `p` in `m` hold `G`: byte `o` of element `e` at
`p + E·e + o`. -/
def SliceIs (E n : Nat) (p : Word) (m : Machine) (G : Nat → Nat → Byte) : Prop :=
  ∀ e < n, ∀ o < E, m.mem (p + BitVec.ofNat 64 (E * e + o)) = some (G e o)

/-- Elements `[lo, lo+L)` of `F` reversed. -/
def rev (lo L : Nat) (F : Nat → Nat → Byte) (e o : Nat) : Byte :=
  if lo ≤ e ∧ e < lo + L then F (lo + (L - 1 - (e - lo))) o else F e o

/-- `rev lo L F` after the swaps `0 … i-1` and bytes `0 … k-1` of swap `i`. -/
def revAt (lo L i k : Nat) (F : Nat → Nat → Byte) (e o : Nat) : Byte :=
  if lo ≤ e ∧ e < lo + L ∧
      (e - lo < i ∨ L - 1 - (e - lo) < i ∨
        ((e - lo = i ∨ L - 1 - (e - lo) = i) ∧ e - lo ≠ L - 1 - (e - lo) ∧ o < k)) then
    F (lo + (L - 1 - (e - lo))) o
  else F e o

/-- The entry memory of a slice as a byte function. -/
def bytesOf (E : Nat) (p : Word) (m : Machine) (e o : Nat) : Byte :=
  (m.mem (p + BitVec.ofNat 64 (E * e + o))).getD 0

theorem revAt_zero (lo L : Nat) (F : Nat → Nat → Byte) : revAt lo L 0 0 F = F := by
  funext e o
  simp only [revAt]
  rw [if_neg (by omega)]

/-- The last byte of swap `i` done is swap `i+1` not begun. -/
theorem revAt_next {lo L i E : Nat} (F : Nat → Nat → Byte) (hi : 2 * i + 2 ≤ L) {e o : Nat}
    (ho : o < E) : revAt lo L i E F e o = revAt lo L (i + 1) 0 F e o := by
  simp only [revAt]
  by_cases h : lo ≤ e ∧ e < lo + L ∧
      (e - lo < i ∨ L - 1 - (e - lo) < i ∨
        ((e - lo = i ∨ L - 1 - (e - lo) = i) ∧ e - lo ≠ L - 1 - (e - lo) ∧ o < E))
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- All `L/2` swaps done is the reversal. -/
theorem revAt_full (lo L : Nat) (F : Nat → Nat → Byte) : revAt lo L (L / 2) 0 F = rev lo L F := by
  funext e o
  simp only [revAt, rev]
  by_cases h : lo ≤ e ∧ e < lo + L
  · rw [if_pos h]
    by_cases h' : e - lo < L / 2 ∨ L - 1 - (e - lo) < L / 2
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega), show lo + (L - 1 - (e - lo)) = e by omega]
  · rw [if_neg h, if_neg (by omega)]

/-- One byte of swap `i`: `revAt … (k+1)` is `revAt … k` with byte `k` of elements `lo+i` and
`lo+L-1-i` exchanged. -/
theorem revAt_succ {lo L i k : Nat} (F : Nat → Nat → Byte) (hi : 2 * i + 2 ≤ L) (e o : Nat) :
    revAt lo L i (k + 1) F e o =
      if e = lo + i ∧ o = k then revAt lo L i k F (lo + (L - 1 - i)) k
      else if e = lo + (L - 1 - i) ∧ o = k then revAt lo L i k F (lo + i) k
      else revAt lo L i k F e o := by
  by_cases h1 : e = lo + i ∧ o = k
  · rw [if_pos h1]
    obtain ⟨rfl, rfl⟩ := h1
    simp only [revAt]
    rw [if_pos (by omega), if_neg (by omega), show lo + (L - 1 - (lo + i - lo)) = lo + (L - 1 - i) by omega]
  · rw [if_neg h1]
    by_cases h2 : e = lo + (L - 1 - i) ∧ o = k
    · rw [if_pos h2]
      obtain ⟨rfl, rfl⟩ := h2
      simp only [revAt]
      rw [if_pos (by omega), if_neg (by omega), show lo + (L - 1 - (lo + (L - 1 - i) - lo)) = lo + i by omega]
    · rw [if_neg h2]
      simp only [revAt]
      by_cases h : lo ≤ e ∧ e < lo + L ∧
          (e - lo < i ∨ L - 1 - (e - lo) < i ∨
            ((e - lo = i ∨ L - 1 - (e - lo) = i) ∧ e - lo ≠ L - 1 - (e - lo) ∧ o < k + 1))
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

theorem rev_short {lo L : Nat} (F : Nat → Nat → Byte) (h : L / 2 = 0) : rev lo L F = F := by
  rw [← revAt_full, h, revAt_zero]

/-- The three reversals of `rotate` move element `(e + a) % n` to `e`. -/
theorem rev_rotate {n a : Nat} (F : Nat → Nat → Byte) (ha : a ≤ n) {e : Nat} (he : e < n)
    (o : Nat) : rev 0 n (rev a (n - a) (rev 0 a F)) e o = F ((e + a) % n) o := by
  have hm : (e + a) % n = if e + a < n then e + a else e + a - n := by
    split
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hm]
  by_cases h : e + a < n
  · rw [if_pos h]; simp only [rev]
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]; congr 1; omega
  · rw [if_neg h]; simp only [rev]
    rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]; congr 1; omega

/-! ## Addresses of a slice -/

theorem elem_inj {E e e' o o' : Nat} (ho : o < E) (ho' : o' < E) (h : E * e + o = E * e' + o') :
    e = e' ∧ o = o' := by
  have hE : 0 < E := by omega
  have h1 : (E * e + o) / E = e := by rw [Nat.mul_add_div hE, Nat.div_eq_of_lt ho]; simp
  have h2 : (E * e' + o') / E = e' := by rw [Nat.mul_add_div hE, Nat.div_eq_of_lt ho']; simp
  have he : e = e' := by rw [← h1, ← h2, h]
  subst he
  exact ⟨rfl, by omega⟩

theorem elem_lt {E n e o : Nat} (he : e < n) (ho : o < E) : E * e + o < E * n := by
  have : E * (e + 1) ≤ E * n := Nat.mul_le_mul_left E he
  rw [Nat.mul_succ] at this; omega

/-- Distinct (element, offset) pairs of a slice that does not wrap have distinct addresses. -/
theorem addr_ne {E n : Nat} {p : Word} (hfit : p.toNat + E * n < 2 ^ 64) {e e' o o' : Nat}
    (he : e < n) (he' : e' < n) (ho : o < E) (ho' : o' < E) (hne : ¬ (e = e' ∧ o = o')) :
    p + BitVec.ofNat 64 (E * e + o) ≠ p + BitVec.ofNat 64 (E * e' + o') := by
  intro h
  have h1 := elem_lt he ho
  have h2 := elem_lt he' ho'
  have := congrArg BitVec.toNat h
  rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)] at this
  exact hne (elem_inj ho ho' (by omega))

/-- One byte exchanged between elements `e₁ ≠ e₂` at offset `k`, everything else kept. -/
theorem slice_swap {E n : Nat} {p : Word} {mh m' : Machine} {G : Nat → Nat → Byte}
    (hfit : p.toNat + E * n < 2 ^ 64) (hG : SliceIs E n p mh G) {e₁ e₂ k : Nat} (h₁ : e₁ < n)
    (h₂ : e₂ < n) (hk : k < E) (hne : e₁ ≠ e₂)
    (hw₁ : m'.mem (p + BitVec.ofNat 64 (E * e₁ + k)) = some (G e₂ k))
    (hw₂ : m'.mem (p + BitVec.ofNat 64 (E * e₂ + k)) = some (G e₁ k))
    (hrest : ∀ a, a ≠ p + BitVec.ofNat 64 (E * e₁ + k) → a ≠ p + BitVec.ofNat 64 (E * e₂ + k) →
      m'.mem a = mh.mem a) :
    SliceIs E n p m' fun e o =>
      if e = e₁ ∧ o = k then G e₂ k else if e = e₂ ∧ o = k then G e₁ k else G e o := by
  intro e he o ho
  dsimp only
  by_cases c1 : e = e₁ ∧ o = k
  · obtain ⟨rfl, rfl⟩ := c1; rw [if_pos ⟨rfl, rfl⟩]; exact hw₁
  · rw [if_neg c1]
    by_cases c2 : e = e₂ ∧ o = k
    · obtain ⟨rfl, rfl⟩ := c2; rw [if_pos ⟨rfl, rfl⟩]; exact hw₂
    · rw [if_neg c2, hrest _ (addr_ne hfit he h₁ ho hk c1) (addr_ne hfit he h₂ ho hk c2)]
      exact hG e he o ho

/-- `slice_swap` for a reversal: byte `k` of swap `i` moves `revAt … k` to `revAt … (k+1)`. -/
theorem slice_revAt_succ {E n lo L i k : Nat} {p : Word} {mh m' : Machine}
    {F : Nat → Nat → Byte} (hfit : p.toNat + E * n < 2 ^ 64)
    (hG : SliceIs E n p mh (revAt lo L i k F)) (hL : lo + L ≤ n) (hi : 2 * i + 2 ≤ L)
    (hk : k < E)
    (hw₁ : m'.mem (p + BitVec.ofNat 64 (E * (lo + i) + k)) =
      mh.mem (p + BitVec.ofNat 64 (E * (lo + (L - 1 - i)) + k)))
    (hw₂ : m'.mem (p + BitVec.ofNat 64 (E * (lo + (L - 1 - i)) + k)) =
      mh.mem (p + BitVec.ofNat 64 (E * (lo + i) + k)))
    (hrest : ∀ a, a ≠ p + BitVec.ofNat 64 (E * (lo + i) + k) →
      a ≠ p + BitVec.ofNat 64 (E * (lo + (L - 1 - i)) + k) → m'.mem a = mh.mem a) :
    SliceIs E n p m' (revAt lo L i (k + 1) F) := by
  have h := slice_swap hfit hG (e₁ := lo + i) (e₂ := lo + (L - 1 - i)) (by omega) (by omega) hk
    (by omega) (by rw [hw₁]; exact hG _ (by omega) _ hk) (by rw [hw₂]; exact hG _ (by omega) _ hk)
    hrest
  intro e he o ho
  rw [h e he o ho, revAt_succ F hi]

/-- The entry bytes as a `SliceIs`. -/
theorem slice_bytesOf {E n : Nat} {p : Word} {m : Machine}
    (h : ∀ j < E * n, (m.mem (p + BitVec.ofNat 64 j)).isSome) : SliceIs E n p m (bytesOf E p m) := by
  intro e he o ho
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h _ (elem_lt he ho))
  simp [bytesOf, hb]

/-- A slice is kept by a step that changes memory only outside it. -/
theorem SliceIs.keep {E n : Nat} {p : Word} {m m' : Machine} {G : Nat → Nat → Byte}
    (h : SliceIs E n p m G) (hk : ∀ e < n, ∀ o < E,
      m'.mem (p + BitVec.ofNat 64 (E * e + o)) = m.mem (p + BitVec.ofNat 64 (E * e + o))) :
    SliceIs E n p m' G :=
  fun e he o ho => by rw [hk e he o ho]; exact h e he o ho

theorem SliceIs.congr {E n : Nat} {p : Word} {m : Machine} {G G' : Nat → Nat → Byte}
    (h : SliceIs E n p m G) (hG : ∀ e < n, ∀ o < E, G e o = G' e o) : SliceIs E n p m G' :=
  fun e he o ho => by rw [← hG e he o ho]; exact h e he o ho

end ZesuExec.Fn.Rotate
