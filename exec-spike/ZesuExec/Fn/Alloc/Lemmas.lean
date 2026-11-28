import ZesuExec.Fn.Alloc.Inv
import ZesuExec.Sym.Sound

/-!
# Lemmas for the allocator proofs

Generic facts about a leaf whose cut state is an entry state: words read at constant offsets
(`rd_cst`), bytes a run leaves alone (`written_only`), presence (`pres_of`); region placement
(`disjoint_of_avoid`); and the arithmetic of `sysAllocAligned`'s rounding (`round_up`).
-/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine

theorem wf_regions {env : Env} {S S' : SState} (h : Env.WF env S) (hr : S'.regions = S.regions) :
    Env.WF env S' where
  len := hr ▸ h.len
  disjoint := h.disjoint
  size r R s hR := h.size r R s (hr ▸ hR)
  align r R hR := h.align r R (hr ▸ hR)
  range r R hR := h.range r R (hr ▸ hR)

/-- The word at a constant offset of a region. -/
theorem rd_cst {env : Env} {S : SState} {m : Machine} (hwf : Env.WF env S) (hm : Match env S m)
    {r off : Nat} {R : Region} (hR : S.regions[r]? = some R) (hb : off + 8 ≤ env.size r) :
    rd m ((env.base r).toNat + off) = some ((readConst S r off 8).eval env) := by
  unfold rd
  rw [ofNat_toNat_add]
  exact load_cst hwf hm hR hb

/-- A run from a state without writes changes only the bytes it wrote. -/
theorem written_only {env : Env} {S S' : SState} {m m' : Machine} (hm : Match env S m)
    (hS : S.mem = []) (hm' : Match env S' m') (hr : S'.regions = S.regions)
    (hso : SameOutside (InWritable env S) m m') :
    SameOutside (fun a => ∃ w ∈ S'.mem, ∃ j, w.off ≤ j ∧ j < w.off + w.n ∧
      a = env.base w.r + BitVec.ofNat 64 j) m m' := by
  intro a ha
  by_cases hw : InWritable env S a
  · obtain ⟨r, R, j, hR, -, hj, rfl⟩ := hw
    have hlt : r < S.regions.length := (List.getElem?_eq_some_iff.mp hR).1
    rw [hm'.mem r j (hr ▸ hlt) hj, hm.mem r j hlt hj, hS]
    congr 1
    unfold memByte
    rw [List.find?_eq_none.mpr]
    · rfl
    · intro w hwm hc
      simp only [Write.covers, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      exact ha ⟨w, hwm, j, hc.1.2, hc.2, by rw [hc.1.1]⟩
  · exact hso a hw

theorem pres_of {env : Env} {S S' : SState} {m m' : Machine} (hm' : Match env S' m')
    (hr : S'.regions = S.regions) (hso : SameOutside (InWritable env S) m m') :
    ∀ a, (m.mem a).isSome → (m'.mem a).isSome := by
  intro a ha
  by_cases hw : InWritable env S a
  · obtain ⟨r, R, j, hR, -, hj, rfl⟩ := hw
    rw [hm'.mem r j (hr ▸ (List.getElem?_eq_some_iff.mp hR).1) hj]; rfl
  · rw [hso a hw]; exact ha

/-- Two ranges with no common address are disjoint. -/
theorem disjoint_of_avoid {b1 b2 : Word} {n1 n2 : Nat} (hn1 : 0 < n1) (hn2 : 0 < n2)
    (h : ∀ a, InRange b1 n1 a → ¬ InRange b2 n2 a) :
    Fn.Disjoint (b1, n1) (b2, n2) := by
  unfold Fn.Disjoint
  simp only
  refine Classical.byContradiction fun hc => ?_
  simp only [not_or, Nat.not_le] at hc
  by_cases hle : b1.toNat ≤ b2.toNat
  · exact h b2 ⟨hle, by omega⟩ ⟨Nat.le_refl _, by omega⟩
  · exact h b1 ⟨Nat.le_refl _, by omega⟩ ⟨by omega, by omega⟩

theorem rd_present {m : Machine} {a : Nat} {v : Word} (h : rd m a = some v) (ha : a < 2 ^ 64) :
    ∀ t < 8, (m.mem (BitVec.ofNat 64 (a + t))).isSome := by
  unfold rd Machine.load at h
  split at h
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at h
    exact readBytes_isSome_get (by cases hr : readBytes m.mem a 8 <;> simp_all)
  · simp at h

theorem toNat_ofNat_lt {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `sysAllocAligned`'s rounding: `x + al - (x & (al - 1))` when `x` is not a multiple of the
power of two `al`; it lies in `(x, x + al)` and stays below `ramHi` (a multiple of `2^24`). -/
theorem round_up {x A : Word} {j : Nat} (hj : j ≤ 24) (hA : A.toNat = 2 ^ j)
    (hx : x.toNat ≤ Layout.ramHi)
    (hr : x &&& (A + BitVec.ofNat 64 18446744073709551615) ≠ 0) :
    x.toNat ≤ (x + A - (x &&& (A + BitVec.ofNat 64 18446744073709551615))).toNat ∧
      (x + A - (x &&& (A + BitVec.ofNat 64 18446744073709551615))).toNat ≤ Layout.ramHi := by
  have hpow : 0 < 2 ^ j := Nat.pow_pos (by decide)
  have hp24 : 2 ^ j ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hj
  have hm1 : (A + BitVec.ofNat 64 18446744073709551615).toNat = 2 ^ j - 1 := by
    rw [BitVec.toNat_add, hA, toNat_ofNat_lt (by decide)]; omega
  have hand : (x &&& (A + BitVec.ofNat 64 18446744073709551615)).toNat = x.toNat % 2 ^ j := by
    rw [BitVec.toNat_and, hm1, Nat.and_two_pow_sub_one_eq_mod]
  have hr' : x.toNat % 2 ^ j ≠ 0 := fun h0 => hr (BitVec.eq_of_toNat_eq (by rw [hand, h0]; rfl))
  have hmod : x.toNat % 2 ^ j < 2 ^ j := Nat.mod_lt _ hpow
  have hdiv : Layout.ramHi % 2 ^ j = 0 := by
    have : Layout.ramHi = 2 ^ j * (2 ^ (24 - j) * 192) := by
      rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hj]; rfl
    rw [this, Nat.mul_mod_right]
  have hxlt : x.toNat < Layout.ramHi := by
    rcases Nat.lt_or_ge x.toNat Layout.ramHi with h | h
    · exact h
    · exfalso; apply hr'; rw [show x.toNat = Layout.ramHi by omega, hdiv]
  -- x + al - r = al * (x / al + 1) ≤ ramHi
  have hq := Nat.div_add_mod x.toNat (2 ^ j)
  have hle : 2 ^ j * (x.toNat / 2 ^ j + 1) ≤ Layout.ramHi := by
    have h1 : x.toNat / 2 ^ j < Layout.ramHi / 2 ^ j :=
      Nat.div_lt_div_of_lt_of_dvd (Nat.dvd_of_mod_eq_zero hdiv) hxlt
    have h2 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
    calc 2 ^ j * (x.toNat / 2 ^ j + 1) ≤ 2 ^ j * (Layout.ramHi / 2 ^ j) :=
          Nat.mul_le_mul_left _ h1
      _ = Layout.ramHi := by rw [Nat.mul_comm]; exact h2
  have hval : (x + A - (x &&& (A + BitVec.ofNat 64 18446744073709551615))).toNat =
      x.toNat + 2 ^ j - x.toNat % 2 ^ j := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, hA, hand]
    unfold Layout.ramHi at hxlt
    omega
  rw [hval]
  constructor
  · omega
  · have : x.toNat + 2 ^ j - x.toNat % 2 ^ j = 2 ^ j * (x.toNat / 2 ^ j + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    omega

/-- A non-null head is the first block of its class's list. -/
theorem pop_head {L : List (Word × Nat)} {m : Machine} (h : Heap L m) {k : Nat} (hk : k < 22)
    {v : Word} (hv : rd m (flBase + 8 * k) = some v) (hne : v ≠ 0) :
    ∃ st, Decode m st ∧ Good L st ∧ ∃ p t, st.fl k = p :: t ∧ v = BitVec.ofNat 64 p := by
  obtain ⟨st, hd, hg⟩ := h
  have hc := hd.chains k hk
  cases hfl : st.fl k with
  | nil => rw [hfl] at hc; simp only [Chain] at hc; rw [hc] at hv; cases hv; exact absurd rfl hne
  | cons p t =>
    rw [hfl] at hc
    obtain ⟨hp, -⟩ := hc
    rw [hp] at hv; cases hv
    exact ⟨st, hd, hg, p, t, hfl, rfl⟩

/-- An address in `[ofNat b, ofNat b + n)` is `ofNat (b + t)` for some `t < n`. -/
theorem inRange_lit {b n : Nat} {a : Word} (hb : b + n < 2 ^ 64)
    (h : InRange (BitVec.ofNat 64 b) n a) : ∃ t < n, a = BitVec.ofNat 64 (b + t) := by
  unfold InRange at h
  rw [toNat_ofNat_lt (by omega)] at h
  exact ⟨a.toNat - b, by omega, by
    apply BitVec.eq_of_toNat_eq; rw [toNat_ofNat_lt (by omega)]; omega⟩

theorem notOne : BitVec.ofNat 64 18446744073709551614 = ~~~(1 : Word) := by decide

theorem rd_mem {m m' : Machine} (h : m'.mem = m.mem) (a : Nat) : rd m' a = rd m a := by
  unfold rd Machine.load; rw [h]

/-- Every byte of a free block is private. -/
theorem free_blk_priv {L : List (Word × Nat)} {st : St} (hg : Good L st) {k p t : Nat}
    (hk : k < 22) (hp : p ∈ st.fl k) (ht : t < classBytes k) : Priv L (BitVec.ofNat 64 (p + t)) := by
  have hin := hg.free_in hk hp
  refine ⟨.inr ?_, fun ⟨b, hb, h1, h2⟩ => ?_⟩
  · rw [toNat_ofNat_lt (by unfold heapTop at hin; omega)]; unfold posAddr; unfold heapLo at hin
    unfold heapTop at *; omega
  · have hd := hg.free_live hk hp hb
    have hc := le_cap b.2
    simp only [NDisj] at hd
    rw [toNat_ofNat_lt (by unfold heapTop at hin; omega)] at h1 h2
    omega

/-- Bytes from the bump pointer up are private. -/
theorem bump_priv {L : List (Word × Nat)} {st : St} (hg : Good L st) {x : Nat}
    (hlo : st.pos ≤ x) (hhi : x < heapTop) : Priv L (BitVec.ofNat 64 x) := by
  have hpl := hg.pos_lo
  refine ⟨.inr ?_, fun ⟨b, hb, h1, h2⟩ => ?_⟩
  · rw [toNat_ofNat_lt (by unfold heapTop at hhi; omega)]; unfold posAddr; unfold heapLo at hpl
    omega
  · have := hg.live_in hb; have := le_cap b.2
    rw [toNat_ofNat_lt (by unfold heapTop at hhi; omega)] at h1 h2
    omega

theorem reg_var {env : Env} {S : SState} {m' : Machine} (hm : Match env S m') (i : Fin 32)
    (h : S.reg i.val = .var i.val) : m'.reg i = env.vars i.val := by
  rw [← hm.regs i, h]; rfl

theorem ofNat_add_nat {b j : Nat} : BitVec.ofNat 64 (b + j) = BitVec.ofNat 64 b + BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

end ZesuExec.Fn.Alloc
