import ZesuExec.Sym.SmartLemmas

/-!
# Byte-level memory lemmas for `Machine.readBytes`, `Machine.writeBytes` and regions
-/

namespace ZesuExec.Sym
open ZesuExec.Machine

theorem toNat_add_ofNat {b : Word} {j : Nat} (h : b.toNat + j < 2 ^ 64) :
    (b + BitVec.ofNat 64 j).toNat = b.toNat + j := by
  simp [BitVec.toNat_add]; omega

theorem ofNat_toNat_add (b : Word) (j : Nat) :
    BitVec.ofNat 64 (b.toNat + j) = b + BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem ofNat_add_ofNat (b : Word) (i j : Nat) :
    b + BitVec.ofNat 64 i + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (i + j) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

theorem byteList_congr {f g : Nat → Byte} {k k' n : Nat}
    (h : ∀ t < n, f (k + t) = g (k' + t)) : byteList f k n = byteList g k' n := by
  induction n generalizing k k' with
  | zero => rfl
  | succ n ih =>
    simp only [byteList]
    congr 1
    · simpa using h 0 (by omega)
    · exact ih fun t ht => by
        have := h (t + 1) (by omega)
        simp only [Nat.add_right_comm _ 1 t]; simpa only [← Nat.add_assoc] using this

theorem byteList_length (f : Nat → Byte) (k n : Nat) : (byteList f k n).length = n := by
  induction n generalizing k <;> simp [byteList, *]

theorem readBytes_of {mem : Word → Option Byte} {a k n : Nat} {f : Nat → Byte}
    (h : ∀ t < n, mem (BitVec.ofNat 64 (a + t)) = some (f (k + t))) :
    readBytes mem a n = some (byteList f k n) := by
  induction n generalizing a k with
  | zero => rfl
  | succ n ih =>
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    have hr := ih (a := a + 1) (k := k + 1) fun t ht => by
      have := h (t + 1) (by omega)
      simp only [Nat.add_right_comm _ 1 t]; simpa only [← Nat.add_assoc] using this
    simp [readBytes, h0, hr, byteList]

theorem readBytes_isSome_of {mem : Word → Option Byte} {a n : Nat}
    (h : ∀ t < n, (mem (BitVec.ofNat 64 (a + t))).isSome) : (readBytes mem a n).isSome := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    have hr := ih (a := a + 1) fun t ht => by
      have := h (t + 1) (by omega)
      simp only [Nat.add_right_comm _ 1 t]; simpa only [← Nat.add_assoc] using this
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h0
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hr
    simp [readBytes, hb, hbs]

theorem byteOf_shift (v : Word) (t : Nat) : byteOf (v >>> 8) t = byteOf v (t + 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]
  congr 1; omega

theorem writeBytes_miss {mem : Word → Option Byte} {a : Nat} {v : Word} {n : Nat} {x : Word}
    (h : ∀ t < n, x ≠ BitVec.ofNat 64 (a + t)) : writeBytes mem a v n x = mem x := by
  induction n generalizing a v with
  | zero => rfl
  | succ n ih =>
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    simp only [writeBytes, h0, if_false]
    exact ih fun t ht => by
      have := h (t + 1) (by omega)
      simp only [Nat.add_right_comm _ 1 t]; simpa only [← Nat.add_assoc] using this

theorem ofNat_inj_of_lt {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : BitVec.ofNat 64 i = BitVec.ofNat 64 j) : i = j := by
  have := congrArg BitVec.toNat h
  simp at this
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

theorem writeBytes_hit {mem : Word → Option Byte} {a : Nat} {v : Word} {n t : Nat}
    (ht : t < n) (ha : a + n ≤ 2 ^ 64) :
    writeBytes mem a v n (BitVec.ofNat 64 (a + t)) = some (byteOf v t) := by
  induction n generalizing a v t with
  | zero => omega
  | succ n ih =>
    simp only [writeBytes]
    cases t with
    | zero => simp [byteOf]
    | succ t =>
      have hne : BitVec.ofNat 64 (a + (t + 1)) ≠ BitVec.ofNat 64 a := by
        intro h; have := ofNat_inj_of_lt (by omega) (by omega) h; omega
      rw [if_neg hne, show a + (t + 1) = a + 1 + t by omega,
        ih (a := a + 1) (by omega) (by omega), byteOf_shift]

/-- `writeBytes` as a case split on whether `x` is one of the written addresses. -/
theorem writeBytes_apply {mem : Word → Option Byte} {a : Nat} {v : Word} {n : Nat} {x : Word}
    (ha : a + n ≤ 2 ^ 64) :
    writeBytes mem a v n x =
      if a ≤ x.toNat ∧ x.toNat < a + n then some (byteOf v (x.toNat - a)) else mem x := by
  split
  · next h =>
    have hx : x = BitVec.ofNat 64 (a + (x.toNat - a)) := by
      rw [show a + (x.toNat - a) = x.toNat by omega]; simp
    rw [hx, writeBytes_hit (by omega) ha]
    congr 2
    have := x.isLt
    simp; omega
  · next h =>
    apply writeBytes_miss
    intro t ht hx
    subst hx
    simp at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

end ZesuExec.Sym
