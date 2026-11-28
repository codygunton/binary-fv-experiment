import ZesuExec.Fn.MergeInPlace.Lemmas

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


/-- A string byte of a `StrOk` element in a `Common` machine is its entry byte. -/
theorem str_byte {c : Cfg} {m mh : Machine} {x : List Byte} (h : Pre c m) (hc : Common c m mh)
    (hx : StrOk c.fs m x) {j : Nat} (hj : j < sliceLen x) :
    mh.mem (slicePtr x + w j) = m.mem (slicePtr x + w j) :=
  hc.2.2.2.2.2.2 _ (str_not_writes h hx hj)

/-! ## Elements of a round are input elements -/

/-- The longest input string. -/
def Lmax (m : Machine) : Nat :=
  ((List.range' (aS m) (bE m - aS m)).map fun e => sliceLen (el (items m (ptr m)) e)).foldr max 0

theorem le_foldr_max : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.foldr max 0
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

theorem foldr_max_le : ∀ {l : List Nat} {B : Nat}, (∀ x ∈ l, x ≤ B) → l.foldr max 0 ≤ B
  | [], _, _ => Nat.zero_le _
  | x :: l, B, h => Nat.max_le.mpr ⟨h x (.head _), foldr_max_le fun y hy => h y (.tail _ hy)⟩

/-- Every element of a round's items is an input element. -/
theorem round_el {c : Cfg} {m : Machine} {G : Nat → Nat → Byte} {as ae e : Nat} (h : Pre c m)
    (hR : Round c m G as ae) (he : aS m ≤ e) (he' : e < bE m) :
    ∃ e₀, aS m ≤ e₀ ∧ e₀ < bE m ∧ el G e = el (items m (ptr m)) e₀ := by
  obtain ⟨h1, h2, h3, hinv⟩ := hR
  have hin : el G e ∈ win G (aS m) as ++ win G as ae ++ win G ae (bE m) := by
    rw [← win_split h1 h2, ← win_split (by omega) h3]; exact mem_win.mpr ⟨e, he, he', rfl⟩
  have := hinv.1.mem_iff.mp hin
  rw [← xy_win h] at this
  obtain ⟨e₀, h4, h5, h6⟩ := mem_win.mp this
  exact ⟨e₀, h4, h5, h6.symm⟩

theorem strOk_round {c : Cfg} {m : Machine} {G : Nat → Nat → Byte} {as ae e : Nat} (h : Pre c m)
    (hp : SlicePre c.fs m) (hR : Round c m G as ae) (he : aS m ≤ e) (he' : e < bE m) :
    StrOk c.fs m (el G e) := by
  obtain ⟨e₀, h1, h2, h3⟩ := round_el h hR he he'
  rw [h3]; exact hp e₀ h1 h2

theorem len_round {c : Cfg} {m : Machine} {G : Nat → Nat → Byte} {as ae e : Nat} (h : Pre c m)
    (hR : Round c m G as ae) (he : aS m ≤ e) (he' : e < bE m) : sliceLen (el G e) ≤ Lmax m := by
  obtain ⟨e₀, h1, h2, h3⟩ := round_el h hR he he'
  rw [h3]
  exact le_foldr_max (List.mem_map.mpr ⟨e₀, List.mem_range'.mpr ⟨e₀ - aS m, by omega, by omega⟩, rfl⟩)

theorem Lmax_le {fs : Nat} {m : Machine} (hp : SlicePre fs m) : Lmax m ≤ Layout.ramHi := by
  refine foldr_max_le fun x hx => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp he
  have := readable_le (hp (aS m + 1 * i) (by omega) (by omega)).1
  omega

/-! ## Loads of a slice and its string bytes -/

theorem w_sliceLen (x : List Byte) : w (sliceLen x) = leWord x 8 := by simp [sliceLen]

/-- An 8-byte load at `off` of an element region (base `p + 32e`) of an entry environment. -/
theorem init_el {m mh : Machine} {G : Nat → Nat → Byte} {regs : List (Word × Nat)} {k e off : Nat}
    (hb : (regs.getD k (0, 0)).1 = ptr m + w (32 * e)) (hs : Items m mh G) (he : e < bE m)
    (hoff : off + 8 ≤ 32) : (Sym.init k off 8).eval (entryEnv mh regs) = leWord (el G e) off := by
  rw [leWord_el G e hoff]
  simp only [Sym.eval]
  congr 1
  apply byteList_congr
  intro t ht
  simp only [Env.byte0, entryEnv, hb, items_add, hs e he (off + t) (by omega), Option.getD_some]

theorem readable_sub {a n k : Nat} (h : readable a n = true) (hk : k < n) :
    readable (a + k) 1 = true := by
  simp only [readable, inRange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  omega

/-- An `SC` cut on byte `k` of two strings at different addresses. -/
theorem cutCS_facts {c : Cfg} {m mh : Machine} {x y : List Byte} {a b k : Nat} (h : Pre c m)
    (hc : Common c m mh) (hx : StrOk c.fs m x) (hy : StrOk c.fs m y) (hkx : k < sliceLen x)
    (hky : k < sliceLen y) (hne : slicePtr x ≠ slicePtr y)
    (ha : mh.reg (Fin.ofNat 32 a) = slicePtr x + w k) (hb : mh.reg (Fin.ofNat 32 b) = slicePtr y + w k) :
    Env.WF (envC a b mh) (SC a b) ∧ Match (envC a b mh) (SC a b) mh := by
  have ax := str_addr hx hkx
  have ay := str_addr hy hky
  have hn : (slicePtr x).toNat ≠ (slicePtr y).toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
  refine ⟨?_, ?_⟩
  · have := entry_wf (m := mh) (ov := ovL [(a, .ptr 0 0), (b, .ptr 1 0)]) (ks := [])
      [((mh.reg (Fin.ofNat 32 a), 1), byteR), ((mh.reg (Fin.ofNat 32 b), 1), byteR)] ?_ ?_
    · exact this
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · refine ⟨by simp [byteR], by simp [byteR, Nat.mod_one], ?_⟩
        simp only [byteR, Bool.false_eq_true, if_false]; rw [ha, ax]
        exact readable_sub hx.1 hkx
      · refine ⟨by simp [byteR], by simp [byteR, Nat.mod_one], ?_⟩
        simp only [byteR, Bool.false_eq_true, if_false]; rw [hb, ay]
        exact readable_sub hy.1 hky
    · rw [List.map_cons, List.map_cons, List.map_nil, List.pairwise_pair]
      unfold Disjoint; simp only
      rw [ha, hb, ax, ay]; omega
  · refine match_ovL ?_ (fun r j hr hj => ?_) (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl) <;> simp [Sym.eval, entryEnv, Env.base]
    · simp at hr
      have hj0 : j = 0 := by
        rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;> simp [entryEnv, Env.size] at hj <;> omega
      subst hj0
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · simp only [entryEnv, Env.base, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        rw [ha, str_byte h hc hx hkx]; exact hx.2.1 k hkx
      · simp only [entryEnv, Env.base, List.getD_cons_succ, List.getD_cons_zero,
          BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        rw [hb, str_byte h hc hy hky]; exact hy.2.1 k hky

/-- The byte at register `x` of an `SC` cut on string byte `k`. -/
theorem envC_byte0 {c : Cfg} {m mh : Machine} {s : List Byte} {x y r k : Nat} (h : Pre c m)
    (hc : Common c m mh) (hs : StrOk c.fs m s) (hk : k < sliceLen s) (hr : r < 2)
    (hreg : mh.reg (Fin.ofNat 32 ([x, y].getD r 0)) = slicePtr s + w k) :
    (envC x y mh).byte0 r 0 = strByte m (slicePtr s) k := by
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
  · simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    simp only [List.getD_cons_zero] at hreg
    rw [hreg, str_byte h hc hs hk]; rfl
  · simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hreg
    rw [hreg, str_byte h hc hs hk]; rfl

/-! ## The comparison of two slice keys -/

theorem ltBy_slice_ne (m : Machine) {x y : List Byte} {k : Nat} (hkx : k < sliceLen x)
    (hky : k < sliceLen y) (hp : ∀ j < k, strByte m (slicePtr x) j = strByte m (slicePtr y) j)
    (hne : strByte m (slicePtr x) k ≠ strByte m (slicePtr y) k) :
    ltBy (sliceKey m) x y =
      decide ((strByte m (slicePtr x) k).toNat < (strByte m (slicePtr y) k).toNat) :=
  lex_range_ne _ _ hkx hky hp hne

theorem ltBy_slice_eq (m : Machine) {x y : List Byte}
    (hp : ∀ j < min (sliceLen x) (sliceLen y), strByte m (slicePtr x) j = strByte m (slicePtr y) j) :
    ltBy (sliceKey m) x y = decide (sliceLen x < sliceLen y) :=
  lex_range_eq _ _ hp

end ZesuExec.Fn.MergeInPlace
