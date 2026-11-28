import ZesuExec.Fn.MergeInPlace.Cuts

/-!
# `mergeInPlace` copies: elements that are byte slices

An element whose first 16 bytes are a Zig `[]const u8` (`ptr`, `len`, little-endian `u64`s) is
ordered by `std.mem.lessThan(u8, …)` on the bytes it points to: `sliceKey m x` reads them in the
machine `m` (the entry machine, for `Cfg.key`).

* `lexLt` over two byte functions on `range la` / `range lb`, in the steps the compiled byte loop
  takes: `lex_range_prefix` (drop an equal prefix), `lex_range'_step` (one more byte),
  `lex_range'_end` (a string exhausted: the lengths decide); together `lex_range_ne`,
  `lex_range_eq`, and `lex_same` (equal pointers: the lengths decide).
* `sliceKey_congr`: a slice's key only depends on its string bytes; `key_stable`: a string
  disjoint from the items and the frame (`StrOk`) keeps its key across a `Common` run.
* `SlicePre fs m`: every input element's string is present, readable and disjoint from the items
  and the frame (the `Cfg.pre` of a slice-keyed copy).
-/

namespace ZesuExec.Fn.MergeInPlace
open ZesuExec ZesuExec.Sym ZesuExec.Machine

/-! ## Slices -/

/-- The little-endian `u64` at byte `off` of `x`. -/
def leWord (x : List Byte) (off : Nat) : Word := ofBytesLE (byteList (fun j => x.getD j 0) off 8)

def slicePtr (x : List Byte) : Word := leWord x 0
def sliceLen (x : List Byte) : Nat := (leWord x 8).toNat

/-- Byte `j` of the string at `p` in `m`. -/
def strByte (m : Machine) (p : Word) (j : Nat) : Byte := (m.mem (p + w j)).getD 0

/-- The bytes the slice in `x` points to, read in `m`. -/
def sliceKey (m : Machine) (x : List Byte) : List Byte :=
  (List.range (sliceLen x)).map (strByte m (slicePtr x))

theorem byteList_congr {f g : Nat → Byte} : ∀ {k n : Nat}, (∀ t < n, f (k + t) = g (k + t)) →
    byteList f k n = byteList g k n
  | _, 0, _ => rfl
  | k, n + 1, h => by
    have h0 : f k = g k := by simpa using h 0 (by omega)
    have hr : byteList f (k + 1) n = byteList g (k + 1) n := byteList_congr fun t ht => by
      have := h (t + 1) (by omega)
      rw [show k + (t + 1) = k + 1 + t by omega] at this
      exact this
    simp only [byteList, h0, hr]

/-- The word at byte `off` of an element: its bytes as `byteList`. -/
theorem leWord_el (G : Nat → Nat → Byte) (e : Nat) {off : Nat} (h : off + 8 ≤ 32) :
    leWord (el G e) off = ofBytesLE (byteList (G e) off 8) := by
  unfold leWord
  congr 1
  apply byteList_congr
  intro t ht
  simp [el, List.getD_eq_getElem?_getD, List.getElem?_range (show off + t < 32 by omega)]

theorem slicePtr_el (G : Nat → Nat → Byte) (e : Nat) :
    slicePtr (el G e) = ofBytesLE (byteList (G e) 0 8) := leWord_el G e (by omega)

theorem sliceLen_el (G : Nat → Nat → Byte) (e : Nat) :
    sliceLen (el G e) = (ofBytesLE (byteList (G e) 8 8)).toNat := by
  unfold sliceLen; rw [leWord_el G e (by omega)]

/-! ## `lexLt` byte by byte -/

theorem lexLt_append (l : List Byte) (a b : List Byte) : lexLt (l ++ a) (l ++ b) = lexLt a b := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [lexLt, ih]

/-- An equal prefix of length `k` drops out. -/
theorem lex_range_prefix (f g : Nat → Byte) {k la lb : Nat} (hp : ∀ j < k, f j = g j)
    (ha : k ≤ la) (hb : k ≤ lb) :
    lexLt ((List.range la).map f) ((List.range lb).map g) =
      lexLt ((List.range' k (la - k)).map f) ((List.range' k (lb - k)).map g) := by
  have e1 : List.range la = List.range' 0 k ++ List.range' k (la - k) := by
    have := @List.range'_append_1 0 k (la - k)
    rw [Nat.zero_add, show k + (la - k) = la by omega] at this
    rw [List.range_eq_range', this]
  have e2 : List.range lb = List.range' 0 k ++ List.range' k (lb - k) := by
    have := @List.range'_append_1 0 k (lb - k)
    rw [Nat.zero_add, show k + (lb - k) = lb by omega] at this
    rw [List.range_eq_range', this]
  have e3 : (List.range' 0 k).map f = (List.range' 0 k).map g :=
    List.map_congr_left fun j hj => hp j (by simp [List.mem_range'] at hj; omega)
  rw [e1, e2, List.map_append, List.map_append, e3, lexLt_append]

/-- One byte of the loop: below both lengths, byte `k` decides unless equal. -/
theorem lex_range'_step (f g : Nat → Byte) {k la lb : Nat} (ha : k < la) (hb : k < lb) :
    lexLt ((List.range' k (la - k)).map f) ((List.range' k (lb - k)).map g) =
      if f k = g k then lexLt ((List.range' (k + 1) (la - (k + 1))).map f)
        ((List.range' (k + 1) (lb - (k + 1))).map g)
      else decide ((f k).toNat < (g k).toNat) := by
  rw [show la - k = (la - (k + 1)) + 1 by omega, show lb - k = (lb - (k + 1)) + 1 by omega]
  simp only [List.range'_succ, List.map_cons, lexLt]

/-- A string exhausted at `k`: the lengths decide. -/
theorem lex_range'_end (f g : Nat → Byte) {k la lb : Nat} (ha : k ≤ la) (hb : k ≤ lb)
    (hk : k = la ∨ k = lb) :
    lexLt ((List.range' k (la - k)).map f) ((List.range' k (lb - k)).map g) = decide (la < lb) := by
  rcases hk with rfl | rfl
  · rw [Nat.sub_self]
    rcases h : lb - k with _ | n
    · simp [lexLt]; omega
    · simp [List.range'_succ, lexLt]; omega
  · rw [Nat.sub_self]
    rcases h : la - k with _ | n
    · simp [lexLt]; omega
    · simp [List.range'_succ, lexLt]; omega

/-- The first difference below both lengths decides. -/
theorem lex_range_ne (f g : Nat → Byte) {k la lb : Nat} (ha : k < la) (hb : k < lb)
    (hp : ∀ j < k, f j = g j) (hne : f k ≠ g k) :
    lexLt ((List.range la).map f) ((List.range lb).map g) = decide ((f k).toNat < (g k).toNat) := by
  rw [lex_range_prefix f g hp (by omega) (by omega), lex_range'_step f g ha hb, if_neg hne]

/-- Equal below both lengths: the lengths decide. -/
theorem lex_range_eq (f g : Nat → Byte) {la lb : Nat} (hp : ∀ j < min la lb, f j = g j) :
    lexLt ((List.range la).map f) ((List.range lb).map g) = decide (la < lb) := by
  rw [lex_range_prefix f g hp (Nat.min_le_left _ _) (Nat.min_le_right _ _),
    lex_range'_end f g (Nat.min_le_left _ _) (Nat.min_le_right _ _) (by omega)]

/-- The same string function (equal pointers): the lengths decide. -/
theorem lex_same (f : Nat → Byte) (la lb : Nat) :
    lexLt ((List.range la).map f) ((List.range lb).map f) = decide (la < lb) :=
  lex_range_eq f f fun _ _ => rfl

theorem sliceKey_same_ptr (m : Machine) {x y : List Byte} (h : slicePtr x = slicePtr y) :
    lexLt (sliceKey m x) (sliceKey m y) = decide (sliceLen x < sliceLen y) := by
  unfold sliceKey; rw [h]; exact lex_same _ _ _

/-! ## Keys across a run -/

/-- A slice's key depends only on its string bytes. -/
theorem sliceKey_congr {m m' : Machine} {x : List Byte}
    (h : ∀ j < sliceLen x, m'.mem (slicePtr x + w j) = m.mem (slicePtr x + w j)) :
    sliceKey m' x = sliceKey m x := by
  unfold sliceKey
  apply List.map_congr_left
  intro j hj
  simp only [strByte, h j (List.mem_range.mp hj)]

/-- The string of `x` is present, readable, and disjoint from the items and the frame. -/
def StrOk (fs : Nat) (m : Machine) (x : List Byte) : Prop :=
  readable (slicePtr x).toNat (sliceLen x) = true ∧
  (∀ j < sliceLen x, (m.mem (slicePtr x + w j)).isSome) ∧
  Disjoint (slicePtr x, sliceLen x) (ptr m, 32 * bE m) ∧
  Disjoint (slicePtr x, sliceLen x) (m.reg 2 - w fs, fs)

/-- Every input element's string is `StrOk`. -/
def SlicePre (fs : Nat) (m : Machine) : Prop :=
  ∀ e, aS m ≤ e → e < bE m → StrOk fs m (el (items m (ptr m)) e)

theorem readable_le {a n : Nat} (h : readable a n = true) : a + n ≤ Layout.ramHi := by
  simp only [readable, inRange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold Layout.rodataHi Layout.inputHi Layout.ramHi at *
  omega

theorem str_addr {fs : Nat} {m : Machine} {x : List Byte} (hx : StrOk fs m x) {j : Nat}
    (hj : j < sliceLen x) : (slicePtr x + w j).toNat = (slicePtr x).toNat + j := by
  have := readable_le hx.1
  exact toNat_add_ofNat (by unfold Layout.ramHi at this; omega)

/-- A string byte is not written by the copy. -/
theorem str_not_writes {c : Cfg} {m : Machine} {x : List Byte} (h : Pre c m) (hx : StrOk c.fs m x)
    {j : Nat} (hj : j < sliceLen x) : ¬ Writes c m (slicePtr x + w j) := by
  have ha := str_addr hx hj
  obtain ⟨-, -, hdi, hdf⟩ := hx
  unfold Disjoint at hdi hdf; simp only at hdi hdf
  have hfit := pre_hfit h
  have hab : aS m ≤ bE m := by have := pre_runs h; omega
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · rw [ha, toNat_add_ofNat (by omega)] at h1 h2
    omega
  · rw [ha] at h1 h2
    have hf : (m.reg 2 - w c.fs).toNat = (m.reg 2).toNat - c.fs := (pre_frame h).1
    have hf' : (frame c m).toNat = (m.reg 2).toNat - c.fs := (pre_frame h).1
    rw [hf] at hdf; rw [hf'] at h1 h2
    omega

/-- A `StrOk` element's key in a `Common` machine is its key at entry. -/
theorem key_stable {c : Cfg} {m mh : Machine} {x : List Byte} (h : Pre c m) (hc : Common c m mh)
    (hx : StrOk c.fs m x) : sliceKey mh x = sliceKey m x :=
  sliceKey_congr fun _ hj => hc.2.2.2.2.2.2 _ (str_not_writes h hx hj)

end ZesuExec.Fn.MergeInPlace
