import ZesuExec.Fn.F3.Regions
import ZesuExec.Fn.F2.Proof
import ZesuExec.Fn.Stage

/-!
# Lemmas for the F3 proof

Loads that succeed, words read back from bytes, struct views over any region, and facts about
`F2.decode` that `nextUint64` needs (header and payload bounds, the `0x80` case).
-/

namespace ZesuExec.Fn.F3
open ZesuExec ZesuExec.Sym ZesuExec.Machine

/-! ## Loads and bytes -/

theorem load_some {m : Machine} {a : Word} {n : Nat} (ha : a.toNat % n = 0)
    (hr : readable a.toNat n = true) (hp : ∀ t < n, (m.mem (a + BitVec.ofNat 64 t)).isSome) :
    ∃ v, m.load a n = some v := by
  have hs : (readBytes m.mem a.toNat n).isSome := readBytes_isSome_of fun t ht => by
    rw [ofNat_toNat_add]; exact hp t ht
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨ofBytesLE bs, by unfold Machine.load; rw [if_pos ⟨ha, hr⟩, hbs]; rfl⟩

theorem byteList_map (f : Nat → Byte) : ∀ a n, byteList f a n = (List.range n).map fun t => f (a + t)
  | _, 0 => rfl
  | a, n + 1 => by
    rw [byteList, byteList_map f (a + 1) n, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro t _
    simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 t]

theorem ofBytesLE_byteOf (w : Word) : ofBytesLE ((List.range 8).map (byteOf w)) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBytesLE _ i (by simp) hi]
  have h8 : i / 8 < 8 := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h8,
    Option.map_some, Option.getD_some, byteOf, BitVec.getLsbD_extractLsb']
  have : i % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [this, decide_true, Bool.true_and]
  congr 1; omega

/-- Eight bytes that are the bytes of `w` read back as `w`. -/
theorem word_of_bytes {f : Nat → Byte} {a : Nat} {w : Word} (h : ∀ t < 8, f (a + t) = byteOf w t) :
    ofBytesLE (byteList f a 8) = w := by
  rw [byteList_map, ← ofBytesLE_byteOf w]
  congr 1
  apply List.map_congr_left
  intro t ht
  exact h t (List.mem_range.mp ht)

theorem bytesAt_bytesOf {m : Machine} {a : Word} {n : Nat}
    (h : ∀ j < n, (m.mem (a + BitVec.ofNat 64 j)).isSome) : BytesAt m a (F2.bytesOf m a n) := by
  intro i hi
  simp only [F2.bytesOf, List.length_map, List.length_range] at hi
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h i hi)
  simp [F2.bytesOf, hb]

/-! ## Views of a region -/

/-- The `n` bytes of region `r` are as `v` says. -/
def viewOK (ws : List Write) (r n : Nat) (v : Nat → Option (Sym × Nat)) : Bool :=
  (List.range n).all fun j => F2.wview ws r j == v j

theorem memByte_view {env : Env} {ws : List Write} {r n : Nat} {v : Nat → Option (Sym × Nat)}
    (h : viewOK ws r n v = true) {j : Nat} (hj : j < n) :
    memByte env ws r j = match v j with
      | some (s, k) => byteOf (s.eval env) k
      | none => env.byte0 r j := by
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [beq_iff_eq] at this
  rw [F2.memByte_wview, this]
  rfl

/-- A word at offset 0 and a word at offset 8. -/
def twoWords (a b : Sym) (j : Nat) : Option (Sym × Nat) :=
  if j < 8 then some (a, j) else some (b, j - 8)

/-- A word at offset 0 and a zero halfword at offset 8; bytes 10..15 untouched. -/
def wordTag (a : Sym) (j : Nat) : Option (Sym × Nat) :=
  if j < 8 then some (a, j) else if j < 10 then some (.lit 0, j - 8) else none

/-! ## `decode` facts -/

theorem checked_success {len h p h' p' : Nat} {b b' : Bool}
    (hc : F2.checkedPayload len h p b = .success b' h' p') :
    h' = h ∧ p' = p ∧ (h + p) % 2 ^ 64 ≤ len := by
  unfold F2.checkedPayload at hc
  split at hc
  · cases hc; exact ⟨rfl, rfl, by assumption⟩
  · cases hc

/-- A success has a header of at most 9 bytes that fits the input with its payload (mod `2^64`),
and the empty string `0x80` is the only success whose input starts with `0x80`. -/
theorem decode_success {input : List Byte} {b : Bool} {h p : Nat}
    (hd : F2.decode input = .success b h p) :
    h ≤ 9 ∧ (h + p) % 2 ^ 64 ≤ input.length ∧ (input.head? = some 128 → p = 0) := by
  cases input with
  | nil => simp [F2.decode] at hd
  | cons c rest =>
    have hc := c.isLt
    simp only [F2.decode] at hd
    simp only [List.length_cons, List.head?_cons, Option.some.injEq]
    by_cases h1 : c.toNat ≤ 127
    · rw [if_pos h1] at hd; cases hd
      refine ⟨by omega, by simp only [Nat.reducePow]; omega, fun e => ?_⟩
      rw [e] at h1; simp at h1
    rw [if_neg h1] at hd
    by_cases h2 : c.toNat = 128
    · rw [if_pos h2] at hd; cases hd
      exact ⟨by omega, by simp only [Nat.reducePow]; omega, fun _ => rfl⟩
    rw [if_neg h2] at hd
    have hne : c ≠ 128 := fun e => h2 (by rw [e]; rfl)
    by_cases h3 : c.toNat ≤ 183
    · rw [if_pos h3] at hd
      obtain ⟨e1, e2, hl⟩ := checked_success hd
      clear hd; rw [e1, e2]
      exact ⟨by omega, hl, fun e => absurd e hne⟩
    rw [if_neg h3] at hd
    by_cases h4 : c.toNat ≤ 191
    · rw [if_pos h4] at hd
      split at hd
      · obtain ⟨e1, e2, hl⟩ := checked_success hd
        clear hd; rw [e1, e2]
        exact ⟨by omega, hl, fun e => absurd e hne⟩
      · cases hd
    rw [if_neg h4] at hd
    by_cases h5 : c.toNat ≤ 247
    · rw [if_pos h5] at hd
      obtain ⟨e1, e2, hl⟩ := checked_success hd
      clear hd; rw [e1, e2]
      exact ⟨by omega, hl, fun e => absurd e hne⟩
    rw [if_neg h5] at hd
    split at hd
    · obtain ⟨e1, e2, hl⟩ := checked_success hd
      clear hd; rw [e1, e2]
      exact ⟨by omega, hl, fun e => absurd e hne⟩
    · cases hd

end ZesuExec.Fn.F3
