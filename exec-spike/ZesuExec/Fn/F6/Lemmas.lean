import ZesuExec.Fn.F6.Regions
import ZesuExec.Fn.F3.Proof

/-!
# Lemmas for the F6 proof

The entry facts (`Entry`), the frame invariant every cut keeps (`Fr`), the environment of a cut
(`envC`), the step from a leaf back to `Fr` (`Fr.of_leaf`), the two callees as machine-level
steps (`dcall` for decodeItem, `ncall` for nextUint64), reading a decodeItem outcome or a
nextUint64 result back from the frame, and the walk's one-field steps.
-/

namespace ZesuExec.Fn.F6
open ZesuExec ZesuExec.Sym ZesuExec.Machine

set_option linter.unusedSimpArgs false

/-! ## Entry facts -/

structure Entry (m : Machine) : Prop where
  ro : RodataLoaded zesuImage m
  stack : StackOk m 512
  ra : RetAligned m
  inLo : Layout.inputLo ≤ (m.reg 11).toNat
  inHi : (m.reg 11).toNat + (m.reg 12).toNat ≤ Layout.inputHi
  inP : ∀ j < (m.reg 12).toNat, (m.mem (m.reg 11 + BitVec.ofNat 64 j)).isSome
  resW : Machine.writable (m.reg 10).toNat 80 = true
  resA : (m.reg 10).toNat % 8 = 0
  resP : ∀ j < 80, (m.mem (m.reg 10 + BitVec.ofNat 64 j)).isSome
  scrP : ∀ j < 8, (m.mem (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j)).isSome
  d1 : Disjoint (m.reg 10, 80) (m.reg 2 - 512, 512)
  d2 : Disjoint (BitVec.ofNat 64 Layout.extraParams, 8) (m.reg 10, 80)
  d3 : Disjoint (BitVec.ofNat 64 Layout.extraParams, 8) (m.reg 2 - 512, 512)
  fits : ∀ input, BytesAt m (m.reg 11) input → input.length = (m.reg 12).toNat → headerFits input

theorem Entry.of_pre {m : Machine} (h : Pre m) : Entry m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- The input bytes. -/
abbrev inputOf (m : Machine) : List Byte := F2.bytesOf m (m.reg 11) (m.reg 12).toNat

/-- The `r` input bytes from offset `o`. -/
def sl (m : Machine) (o r : Nat) : List Byte := ((inputOf m).drop o).take r

/-- Numeric facts of the entry. -/
structure Nums (m : Machine) : Prop where
  spLo : Layout.ramLo + 512 ≤ (m.reg 2).toNat
  spHi : (m.reg 2).toNat ≤ Layout.ramHi
  spA : (m.reg 2).toNat % 16 = 0
  inLo : Layout.inputLo ≤ (m.reg 11).toNat
  inHi : (m.reg 11).toNat + (m.reg 12).toNat ≤ Layout.inputHi
  resLo : Layout.ramLo ≤ (m.reg 10).toNat
  resHi : (m.reg 10).toNat + 80 ≤ Layout.ramHi
  resA : (m.reg 10).toNat % 8 = 0
  d1 : (m.reg 10).toNat + 80 ≤ (m.reg 2).toNat - 512 ∨ (m.reg 2).toNat ≤ (m.reg 10).toNat
  d2 : Layout.extraParams + 8 ≤ (m.reg 10).toNat ∨ (m.reg 10).toNat + 80 ≤ Layout.extraParams
  d3 : Layout.extraParams + 8 ≤ (m.reg 2).toNat - 512 ∨ (m.reg 2).toNat ≤ Layout.extraParams

theorem Entry.sp {m : Machine} (e : Entry m) {k : Nat} (hk : k ≤ 512) :
    (m.reg 2 - BitVec.ofNat 64 k).toNat = (m.reg 2).toNat - k := by
  have := e.stack.2.1
  unfold Layout.ramLo at this
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem Entry.nums {m : Machine} (e : Entry m) : Nums m := by
  have hw := e.resW
  simp only [Machine.writable, Machine.inRange, Bool.and_eq_true, decide_eq_true_eq] at hw
  have h1 := e.d1; have h2 := e.d2; have h3 := e.d3
  unfold Fn.Disjoint at h1 h2 h3
  dsimp only at h1 h2 h3
  have hs : (m.reg 2 - 512 : Word).toNat = (m.reg 2).toNat - 512 := e.sp (by decide)
  rw [hs] at h1 h3
  simp only [BitVec.toNat_ofNat, Layout.extraParams] at h2 h3
  refine ⟨e.stack.2.1, e.stack.2.2.1, e.stack.1, e.inLo, e.inHi, hw.1, hw.2, e.resA, ?_, ?_, ?_⟩
  · omega
  · simp only [Layout.extraParams]; omega
  · simp only [Layout.extraParams]; omega

/-- The frame base. -/
abbrev frB (m : Machine) : Word := m.reg 2 - 400

theorem Nums.fr {m : Machine} (n : Nums m) : (frB m).toNat = (m.reg 2).toNat - 400 := by
  have := n.spLo; unfold Layout.ramLo at this
  show (m.reg 2 - BitVec.ofNat 64 400).toNat = _
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem Nums.sp512 {m : Machine} (n : Nums m) : (m.reg 2 - 512).toNat = (m.reg 2).toNat - 512 := by
  have := n.spLo; unfold Layout.ramLo at this
  show (m.reg 2 - BitVec.ofNat 64 512).toNat = _
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem Nums.frj {m : Machine} (n : Nums m) {j : Nat} (hj : j ≤ 512) :
    (frB m + BitVec.ofNat 64 j).toNat = (m.reg 2).toNat - 400 + j := by
  have := n.spLo; have := n.spHi; unfold Layout.ramLo at *; unfold Layout.ramHi at *
  rw [toNat_add_ofNat (by rw [n.fr]; omega), n.fr]

theorem Nums.inj {m : Machine} (n : Nums m) {j : Nat} (hj : j ≤ (m.reg 12).toNat) :
    (m.reg 11 + BitVec.ofNat 64 j).toNat = (m.reg 11).toNat + j := by
  have := n.inHi; unfold Layout.inputHi at this
  exact toNat_add_ofNat (by omega)

theorem Nums.resj {m : Machine} (n : Nums m) {j : Nat} (hj : j ≤ 80) :
    (m.reg 10 + BitVec.ofNat 64 j).toNat = (m.reg 10).toNat + j := by
  have := n.resHi; unfold Layout.ramHi at this
  exact toNat_add_ofNat (by omega)

/-- An input address is not on the stack. -/
theorem Nums.in_not_stack {m : Machine} (n : Nums m) {j : Nat} (hj : j < (m.reg 12).toNat) :
    ¬ InRange (m.reg 2 - 512) 512 (m.reg 11 + BitVec.ofNat 64 j) := by
  have := n.inHi; have := n.spLo
  unfold Layout.inputHi at *; unfold Layout.ramLo at *
  unfold InRange; rw [n.sp512, n.inj (by omega)]; omega

theorem Nums.res_not_stack {m : Machine} (n : Nums m) {j : Nat} (hj : j < 80) :
    ¬ InRange (m.reg 2 - 512) 512 (m.reg 10 + BitVec.ofNat 64 j) := by
  have := n.d1; have := n.spLo; unfold Layout.ramLo at *
  unfold InRange; rw [n.sp512, n.resj (by omega)]; omega

/-- Two addresses are equal when their sums are, without wrap. -/
theorem addr_eq {a b : Word} {i j : Nat} (ha : a.toNat + i < 2 ^ 64) (hb : b.toNat + j < 2 ^ 64)
    (h : a.toNat + i = b.toNat + j) : a + BitVec.ofNat 64 i = b + BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_add_ofNat ha, toNat_add_ofNat hb, h]

/-- Frame byte `k` is stack byte `112 + k`. -/
theorem Nums.fr_stack {m : Machine} (n : Nums m) {k : Nat} (hk : k < 400) :
    frB m + BitVec.ofNat 64 k = m.reg 2 - 512 + BitVec.ofNat 64 (112 + k) := by
  have := n.spLo; have := n.spHi; unfold Layout.ramLo at *; unfold Layout.ramHi at *
  exact addr_eq (by rw [n.fr]; omega) (by rw [n.sp512]; omega) (by rw [n.fr, n.sp512]; omega)

theorem Nums.fr_in_stack {m : Machine} (n : Nums m) {k : Nat} (hk : k < 400) :
    InRange (m.reg 2 - 512) 512 (frB m + BitVec.ofNat 64 k) := by
  unfold InRange; rw [n.frj (by omega), n.sp512]; have := n.spLo; unfold Layout.ramLo at this
  omega

/-! ## Input slices -/

theorem inputOf_length (m : Machine) : (inputOf m).length = (m.reg 12).toNat := by
  simp [F2.bytesOf]

theorem sl_getElem? (m : Machine) {o r t : Nat} (hor : o + r ≤ (m.reg 12).toNat) (ht : t < r) :
    (sl m o r)[t]? = some ((m.mem (m.reg 11 + BitVec.ofNat 64 (o + t))).getD 0) := by
  simp [sl, F2.bytesOf, ht, show o + t < (m.reg 12).toNat by omega, List.getElem?_take]

theorem sl_length (m : Machine) {o r : Nat} (hor : o + r ≤ (m.reg 12).toNat) :
    (sl m o r).length = r := by
  simp [sl, inputOf_length]; omega

/-- A slice of the input read at its address. -/
theorem bytesOf_sl {m m' : Machine} {o r : Nat} (hor : o + r ≤ (m.reg 12).toNat)
    (hsame : ∀ j < (m.reg 12).toNat,
      m'.mem (m.reg 11 + BitVec.ofNat 64 j) = m.mem (m.reg 11 + BitVec.ofNat 64 j)) :
    F2.bytesOf m' (m.reg 11 + BitVec.ofNat 64 o) r = sl m o r := by
  apply List.ext_getElem?
  intro t
  by_cases ht : t < r
  · rw [sl_getElem? m hor ht]
    simp only [F2.bytesOf, List.getElem?_map, List.getElem?_range ht, Option.map_some]
    rw [ofNat_add_ofNat, hsame _ (by omega)]
  · rw [List.getElem?_eq_none (by simp [F2.bytesOf]; omega),
      List.getElem?_eq_none (by rw [sl_length m hor]; omega)]

theorem sl_drop (m : Machine) (o r c : Nat) : (sl m o r).drop c = sl m (o + c) (r - c) := by
  simp [sl, List.drop_take, List.drop_drop, Nat.add_comm]

theorem sl_nil {m : Machine} {o r : Nat} (hor : o + r ≤ (m.reg 12).toNat) :
    sl m o r = [] ↔ r = 0 := by
  rw [← List.length_eq_zero_iff, sl_length m hor]

/-! ## The environment at a cut -/

/-- The caller's register saved at frame offset `392 - 8 k`. -/
def savedVal (m : Machine) (k : Nat) : Word := m.reg (Fin.ofNat 32 (savedRegs.getD k 0))

/-- Environment at a cut: `var 32 = c`, `var (33 + k)` the saved registers. -/
def envC (m mh : Machine) (c : Word) : Env :=
  (entryEnv mh ((shape m).map (·.1))).setVars 32 fun k => if k = 0 then c else savedVal m (k - 1)

structure EnvFacts (m mh : Machine) (c : Word) : Prop where
  b0 : (envC m mh c).base 0 = frB m
  b1 : (envC m mh c).base 1 = m.reg 10
  b2 : (envC m mh c).base 2 = m.reg 11
  s0 : (envC m mh c).size 0 = 400
  s1 : (envC m mh c).size 1 = 80
  s2 : (envC m mh c).size 2 = (m.reg 12).toNat
  v32 : (envC m mh c).vars 32 = c
  vs : ∀ k < 10, (envC m mh c).vars (33 + k) = savedVal m k
  v : ∀ i : Fin 32, (envC m mh c).vars i.val = mh.reg i
  by0 : ∀ r j, (envC m mh c).byte0 r j = (mh.mem ((envC m mh c).base r + BitVec.ofNat 64 j)).getD 0

theorem envC_facts (m mh : Machine) (c : Word) : EnvFacts m mh c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun i => ?_, fun r j => rfl⟩
  · simp [envC, Env.setVars, Env.base, entryEnv, shape, shapeOf]
  · simp [envC, Env.setVars, Env.base, entryEnv, shape, shapeOf]
  · simp [envC, Env.setVars, Env.base, entryEnv, shape, shapeOf]
  · simp [envC, Env.setVars, Env.size, entryEnv, shape, shapeOf]
  · simp [envC, Env.setVars, Env.size, entryEnv, shape, shapeOf]
  · simp [envC, Env.setVars, Env.size, entryEnv, shape, shapeOf]
  · simp [envC, Env.setVars]
  · simp only [envC, Env.setVars]
    rw [if_pos (by omega), if_neg (by omega)]
    congr 1; omega
  · simp only [envC, Env.setVars]
    rw [if_neg (by omega)]
    exact entryEnv_var mh _ i

theorem eval_var_saved (m mh : Machine) (c : Word) (k : Nat) (hk : k < 10) :
    (Sym.var (33 + k)).eval (envC m mh c) = savedVal m k := (envC_facts m mh c).vs k hk

/-! ## Well-formedness -/

theorem Nums.wf {m : Machine} (n : Nums m) (mh : Machine) (c : Word) (ov : Nat → Option Sym)
    (ks : List Write) : Env.WF (envC m mh c) (entryState ov regionsR ks) := by
  have hf := n.fr
  have := n.spLo; have := n.spHi; have := n.inLo; have := n.inHi; have := n.resLo
  have := n.resHi; have := n.resA; have := n.spA; have := n.d1
  refine F2.setVars_wf (entry_wf (shape m) ?_ ?_) _ _
  · simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · refine ⟨by simp [frameR], by simp [frameR, hf]; omega, ?_⟩
      simp [frameR, Machine.writable, Machine.inRange, hf]
      simp [Layout.ramLo, Layout.ramHi] at *; omega
    · refine ⟨by simp [resR], by simpa [resR] using n.resA, ?_⟩
      simp [resR, Machine.writable, Machine.inRange]; simp [Layout.ramLo, Layout.ramHi] at *; omega
    · refine ⟨by simp [inputR], by simp [inputR, Nat.mod_one], ?_⟩
      simp [inputR, Machine.readable, Machine.inRange]
      simp [Layout.inputLo, Layout.inputHi] at *; omega
  · simp only [shape, shapeOf, List.map_cons, List.map_nil, List.pairwise_cons,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true, Fn.Disjoint, hf]
    simp [Layout.ramLo, Layout.ramHi, Layout.inputLo, Layout.inputHi] at *
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

theorem Nums.fit {m : Machine} (n : Nums m) : ∀ p ∈ shape m, p.1.1.toNat + p.1.2 < 2 ^ 64 := by
  have hf := n.fr
  have h1 := n.spHi; have h2 := n.inHi; have h3 := n.resHi; have h0 := n.spLo
  simp only [Layout.ramHi, Layout.inputHi, Layout.ramLo] at h0 h1 h2 h3
  simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl) <;> simp [hf] <;> omega

/-- The writable regions are the frame and the result. -/
theorem Nums.writable {m mh : Machine} (n : Nums m) {c : Word} {ov : Nat → Option Sym}
    {ks : List Write} {a : Word}
    (ha : InWritable (envC m mh c) (entryState ov regionsR ks) a) :
    InRange (frB m) 400 a ∨ InRange (m.reg 10) 80 a := by
  have ha' : InWritable (entryEnv mh ((shape m).map (·.1))) (entryState ov regionsR ks) a := by
    obtain ⟨r, R, j, h1, h2, h3, h4⟩ := ha
    exact ⟨r, R, j, h1, h2, h3, h4⟩
  obtain ⟨p, hp, hw, hin⟩ := inWritable_entry (shape := shape m) ha' n.fit
  simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact .inl hin
  · exact .inr hin
  · simp [inputR] at hw

/-! ## The frame invariant -/

/-- Offset of `knownR`'s `k`-th word. -/
theorem knownR_get (w : Write) (hw : w ∈ knownR) :
    ∃ k < 10, w = ⟨0, 392 - 8 * k, 8, .var (33 + k)⟩ := by
  simp only [knownR, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨7, by decide, rfl⟩
  · exact ⟨8, by decide, rfl⟩
  · exact ⟨9, by decide, rfl⟩

def calleeVars : List Nat := [25, 26, 27]

/-- What every cut keeps: `sp`, `s0`, `s1`, `s9..s11`, the saved registers in the frame, the
stack present, memory outside the stack as at entry. -/
structure Fr (m mh : Machine) : Prop where
  r2 : mh.reg 2 = frB m
  r8 : mh.reg 8 = m.reg 2
  r9 : mh.reg 9 = m.reg 10
  rk : ∀ i : Fin 32, i.val ∈ calleeVars → mh.reg i = m.reg i
  saved : ∀ k < 10, ∀ t < 8,
    mh.mem (frB m + BitVec.ofNat 64 (392 - 8 * k + t)) = some (byteOf (savedVal m k) t)
  pres : ∀ j < 512, (mh.mem (m.reg 2 - 512 + BitVec.ofNat 64 j)).isSome
  so : SameOutside (InRange (m.reg 2 - 512) 512) m mh

theorem Fr.frP {m mh : Machine} (n : Nums m) (hc : Fr m mh) {k : Nat} (hk : k < 400) :
    (mh.mem (frB m + BitVec.ofNat 64 k)).isSome := by
  rw [n.fr_stack hk]; exact hc.pres _ (by omega)

theorem Fr.init {m mh : Machine} (n : Nums m) (e : Entry m) (hc : Fr m mh) (c : Word) :
    ∀ r j, r < regionsR.length → j < (envC m mh c).size r →
      mh.mem ((envC m mh c).base r + BitVec.ofNat 64 j) = some ((envC m mh c).byte0 r j) := by
  have ef := envC_facts m mh c
  intro r j hr hj
  rw [ef.by0]
  suffices h : (mh.mem ((envC m mh c).base r + BitVec.ofNat 64 j)).isSome by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    rw [hx]; rfl
  simp only [regionsR, List.length_cons, List.length_nil] at hr
  have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hr3 with rfl | rfl | rfl
  · rw [ef.b0]; rw [ef.s0] at hj; exact hc.frP n hj
  · rw [ef.b1]; rw [ef.s1] at hj
    rw [hc.so _ (n.res_not_stack hj)]; exact e.resP j hj
  · rw [ef.b2]; rw [ef.s2] at hj
    rw [hc.so _ (n.in_not_stack hj)]; exact e.inP j hj

/-- The cut's symbolic state matches the machine. -/
theorem Fr.match {m mh : Machine} (n : Nums m) (e : Entry m) (hc : Fr m mh) {c : Word}
    {x : Nat → Option Sym}
    (hx : ∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 8 → i.val ≠ 9 → ∀ s, x i.val = some s →
      s.eval (envC m mh c) = mh.reg i) :
    Match (envC m mh c) (SC x) mh := by
  have hinit := hc.init n e c
  have ef := envC_facts m mh c
  refine F2.entry_match_vars (by decide) (fun i hi s hs => ?_)
    (fun r j hr hj => Option.isSome_iff_exists.mpr ⟨_, hinit r j hr hj⟩) (fun w hw t ht => ?_)
  · simp only [ovC] at hs
    by_cases e2 : i.val = 2
    · simp only [e2, if_true, Option.some.injEq] at hs; subst hs
      have : i = 2 := Fin.ext e2
      subst this
      show (Sym.ptr 0 0).eval (envC m mh c) = _
      simp [Sym.eval, ef.b0, hc.r2]
    by_cases e8 : i.val = 8
    · simp [e8] at hs; subst hs
      have : i = 8 := Fin.ext e8
      subst this
      show (Sym.ptr 0 400).eval (envC m mh c) = _
      simp [Sym.eval, ef.b0, hc.r8, frB, BitVec.sub_add_cancel]
    by_cases e9 : i.val = 9
    · simp [e9] at hs; subst hs
      have : i = 9 := Fin.ext e9
      subst this
      show (Sym.ptr 1 0).eval (envC m mh c) = _
      simp [Sym.eval, ef.b1, hc.r9]
    simp only [e2, e8, e9, if_false] at hs
    exact hx i e2 e8 e9 s hs
  · obtain ⟨k, hk, rfl⟩ := knownR_get w hw
    have hb0 : (entryEnv mh ((shape m).map (·.1))).base 0 = frB m := ef.b0
    show (mh.mem ((entryEnv mh ((shape m).map (·.1))).base 0 +
      BitVec.ofNat 64 (392 - 8 * k + t))).getD 0 = _
    rw [hb0, hc.saved k hk t ht]
    show _ = byteOf ((envC m mh c).vars (33 + k)) t
    rw [ef.vs k hk]; rfl

/-! ## Leaves -/

/-- No write of the list covers byte `j` of region `r`. -/
theorem memByte_nowrite {env : Env} {ws : List Write} {r j : Nat}
    (h : ∀ w ∈ ws, w.covers r j = false) : memByte env ws r j = env.byte0 r j := by
  have : ws.find? (·.covers r j) = none := List.find?_eq_none.mpr fun w hw => by simp [h w hw]
  simp [memByte, this]

/-- A leaf keeps the frame shape: `sp`, `s0`, `s1`, `s9..s11`, and writes only the frame below
the saved registers. -/
def keepOK (lS : SState) : Bool :=
  lS.reg 2 == .ptr 0 0 && lS.reg 8 == .ptr 0 400 && lS.reg 9 == .ptr 1 0 &&
    calleeVars.all (fun i => lS.reg i == .var i) &&
    lS.mem.all (fun w => w.r == 0 && w.off + w.n ≤ 320) && lS.regions == regionsR

theorem keepOK_regions {lS : SState} (h : keepOK lS = true) : lS.regions = regionsR := by
  simp only [keepOK, Bool.and_eq_true, beq_iff_eq] at h; exact h.2

theorem keepOK_nowrite {lS : SState} (h : keepOK lS = true) {r j : Nat} (hr : r ≠ 0 ∨ 320 ≤ j) :
    ∀ w ∈ lS.mem, w.covers r j = false := by
  simp only [keepOK, Bool.and_eq_true, beq_iff_eq] at h
  intro w hw
  have := List.all_eq_true.mp h.1.2 w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  simp only [Write.covers, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    decide_eq_false_iff_not, Nat.not_le, Nat.not_lt]
  omega

/-- After a leaf that keeps the frame shape. -/
theorem Fr.of_leaf {m mh m' : Machine} (n : Nums m) (e : Entry m) (hc : Fr m mh) {c : Word}
    {x : Nat → Option Sym} {lS : SState} (hm' : Match (envC m mh c) lS m')
    (hfr : SameOutside (InWritable (envC m mh c) (SC x)) mh m') (hk : keepOK lS = true) :
    Fr m m' ∧ (∀ j < 400, m'.mem (frB m + BitVec.ofNat 64 j) =
      some (memByte (envC m mh c) lS.mem 0 j)) ∧
    (∀ a, ¬ InRange (frB m) 400 a → m'.mem a = mh.mem a) := by
  have ef := envC_facts m mh c
  have hreg := keepOK_regions hk
  have hk' := hk
  simp only [keepOK, Bool.and_eq_true, beq_iff_eq] at hk'
  obtain ⟨⟨⟨⟨⟨k2, k8⟩, k9⟩, kv⟩, -⟩, -⟩ := hk'
  have g : ∀ i : Fin 32, m'.reg i = (lS.reg i.val).eval (envC m mh c) := fun i => (hm'.regs i).symm
  have hfm : ∀ j < 400, m'.mem (frB m + BitVec.ofNat 64 j) =
      some (memByte (envC m mh c) lS.mem 0 j) := fun j hj => by
    have := hm'.mem 0 j (by rw [hreg]; decide) (by rw [ef.s0]; exact hj)
    rwa [ef.b0] at this
  -- outside the frame, memory is as at `mh`
  have hout : ∀ a, ¬ InRange (frB m) 400 a → m'.mem a = mh.mem a := by
    intro a ha
    by_cases hw : InWritable (envC m mh c) (SC x) a
    · rcases n.writable hw with h | h
      · exact absurd h ha
      · obtain ⟨r, R, j, hR, -, hj, rfl⟩ := hw
        have hr := (List.getElem?_eq_some_iff.mp hR).1
        simp only [SC, entryState, regionsR, List.length_cons, List.length_nil] at hr
        rw [hm'.mem r j (by rw [hreg]; simp [regionsR]; omega) hj,
          memByte_nowrite (keepOK_nowrite hk (r := r) (j := j) (by
            rcases Nat.eq_zero_or_pos r with rfl | hr0
            · exfalso; apply ha
              rw [ef.b0]; rw [ef.s0] at hj
              unfold InRange; rw [n.frj (by omega), n.fr]; omega
            · exact .inl (by omega))),
          hc.init n e c r j (by simp [regionsR]; omega) hj]
    · exact hfr a hw
  refine ⟨⟨?_, ?_, ?_, fun i hi => ?_, fun k hk10 t ht => ?_, fun j hj => ?_, ?_⟩, hfm, hout⟩
  · rw [g 2]; show (lS.reg 2).eval _ = _; rw [k2]; simp [Sym.eval, ef.b0]
  · rw [g 8]; show (lS.reg 8).eval _ = _; rw [k8]; simp [Sym.eval, ef.b0, frB, BitVec.sub_add_cancel]
  · rw [g 9]; show (lS.reg 9).eval _ = _; rw [k9]; simp [Sym.eval, ef.b1]
  · rw [g i, eq_of_beq (List.all_eq_true.mp kv i.val hi)]
    exact (ef.v i).trans (hc.rk i hi)
  · rw [hfm _ (by omega), memByte_nowrite (keepOK_nowrite hk (.inr (by omega))), ef.by0, ef.b0,
      hc.saved k hk10 t ht]
    rfl
  · by_cases hj' : 112 ≤ j
    · have he : m.reg 2 - 512 + BitVec.ofNat 64 j = frB m + BitVec.ofNat 64 (j - 112) := by
        rw [n.fr_stack (by omega), show 112 + (j - 112) = j by omega]
      rw [he, hfm _ (by omega)]; rfl
    · have hhi := n.spHi; unfold Layout.ramHi at hhi
      have hlo := n.spLo; unfold Layout.ramLo at hlo
      have hj2 : (m.reg 2 - 512 + BitVec.ofNat 64 j).toNat = (m.reg 2).toNat - 512 + j := by
        rw [toNat_add_ofNat (by rw [n.sp512]; omega), n.sp512]
      have hf := n.fr
      rw [hout _ (by simp only [InRange, hf, hj2]; omega)]
      exact hc.pres j hj
  · intro a ha
    by_cases hf : InRange (frB m) 400 a
    · exfalso; apply ha
      unfold InRange at hf ⊢
      have h1 := n.fr; have h2 := n.sp512; have h3 := n.spLo; unfold Layout.ramLo at h3
      omega
    · rw [hout a hf]; exact hc.so a ha


/-! ## Rodata, presence, words -/

theorem rodata_lt : ∀ a b, zesuImage.rodataByte? a = some b → a < Layout.ramLo := by
  intro a b h
  have := zesu_rodata_range h; unfold Layout.rodataHi at this; unfold Layout.ramLo; omega

theorem Fr.ro {m mh : Machine} (n : Nums m) (e : Entry m) (hc : Fr m mh) :
    RodataLoaded zesuImage mh := by
  intro a b hab
  have ha := rodata_lt a b hab
  have hlo := n.spLo
  unfold Layout.ramLo at ha hlo
  rw [hc.so _ (by
    unfold InRange; rw [n.sp512, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)]
  exact e.ro a b hab

/-- An input byte is as at entry. -/
theorem Fr.inMem {m mh : Machine} (n : Nums m) (hc : Fr m mh) {j : Nat} (hj : j < (m.reg 12).toNat) :
    mh.mem (m.reg 11 + BitVec.ofNat 64 j) = m.mem (m.reg 11 + BitVec.ofNat 64 j) :=
  hc.so _ (n.in_not_stack hj)

/-- A word read back from its bytes. -/
theorem wordAt_of_bytes {m : Machine} {a w : Word} (_ha : a.toNat % 8 = 0)
    (hr : Machine.readable a.toNat 8 = true)
    (h : ∀ t < 8, m.mem (a + BitVec.ofNat 64 t) = some (byteOf w t)) : F3.wordAt m a = w := by
  have hb : readBytes m.mem a.toNat 8 = some (byteList (byteOf w) 0 8) :=
    readBytes_of fun t ht => by rw [ofNat_toNat_add, Nat.zero_add]; exact h t ht
  unfold F3.wordAt Machine.load
  rw [if_pos hr, hb]
  simp only [Option.map_some, Option.getD_some]
  exact F3.word_of_bytes fun t _ => by simp

/-! ## decodeItem from a cut -/

/-- A decodeItem call from the frame: outcome at frame offset `off`, input slice `(o, r)`. -/
theorem dcall {m m1 : Machine} (n : Nums m) (e : Entry m) (hc : Fr m m1)
    {off o r : Nat} (hoff : off + 40 ≤ 320) (hal : off % 8 = 0)
    (hor : o + r ≤ (m.reg 12).toNat)
    (h10 : m1.reg 10 = frB m + BitVec.ofNat 64 off) (h11 : m1.reg 11 = m.reg 11 + BitVec.ofNat 64 o)
    (h12 : m1.reg 12 = BitVec.ofNat 64 r) (h1 : RetAligned m1) :
    F2.Pre m1 ∧ ∀ m2, F2.Post m1 m2 → Preserved m1 m2 →
      Fr m m2 ∧ m2.pc = (m1.reg 1 &&& ~~~(1 : Word)) ∧ (∀ i ∈ calleeSaved, m2.reg i = m1.reg i) ∧
      (∃ before : List Byte, ∀ k < 40, m2.mem (frB m + BitVec.ofNat 64 (off + k)) =
        some (F2.resultByte (m.reg 11 + BitVec.ofNat 64 o) (sl m o r) before k)) ∧
      (∀ j < 400, (j < off ∨ off + 40 ≤ j) →
        m2.mem (frB m + BitVec.ofNat 64 j) = m1.mem (frB m + BitVec.ofNat 64 j)) := by
  have hf := n.fr; have h512 := n.sp512
  have hlo := n.spLo; have hhi := n.spHi; have hal16 := n.spA
  have hil := n.inLo; have hih := n.inHi
  unfold Layout.ramLo at hlo; unfold Layout.ramHi at hhi
  unfold Layout.inputLo at hil; unfold Layout.inputHi at hih
  have hr12 : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat]; omega
  have hout : (m1.reg 10).toNat = (m.reg 2).toNat - 400 + off := by rw [h10, n.frj (by omega)]
  have hfr16 : (m1.reg 2 - 16).toNat = (m.reg 2).toNat - 416 := by
    rw [hc.r2]; show (frB m - BitVec.ofNat 64 16).toNat = _
    rw [BitVec.toNat_sub, hf]; simp; omega
  have hfr16' : (m1.reg 2 - BitVec.ofNat 64 16).toNat = (m.reg 2).toNat - 416 := hfr16
  have hin : (m1.reg 11).toNat = (m.reg 11).toNat + o := by rw [h11, n.inj (by omega)]
  have hsame : ∀ j < (m.reg 12).toNat,
      m1.mem (m.reg 11 + BitVec.ofNat 64 j) = m.mem (m.reg 11 + BitVec.ofNat 64 j) :=
    fun j hj => hc.inMem n hj
  refine ⟨⟨hc.ro n e, ⟨?_, ?_, ?_, fun j hj => ?_⟩, h1, ?_, fun j hj => ?_, ?_, ?_,
    fun j hj => ?_, ?_, ?_, ?_⟩, fun m2 hpost hp2 => ?_⟩
  · rw [hc.r2, hf]; omega
  · rw [hc.r2, hf]; unfold Layout.ramLo; omega
  · rw [hc.r2, hf]; unfold Layout.ramHi; omega
  · have := hc.pres (96 + j) (by omega)
    rwa [addr_eq (a := m.reg 2 - 512) (b := m1.reg 2 - BitVec.ofNat 64 16) (i := 96 + j) (j := j)
      (by rw [h512]; omega) (by rw [hfr16']; omega) (by rw [h512, hfr16']; omega)] at this
  · rw [hin, h12, hr12]
    simp [Machine.readable, Machine.inRange, Layout.inputLo, Layout.inputHi]; omega
  · rw [h11, ofNat_add_ofNat, hsame _ (by rw [h12, hr12] at hj; omega)]
    exact e.inP _ (by rw [h12, hr12] at hj; omega)
  · simp [Machine.writable, Machine.inRange, hout, Layout.ramLo, Layout.ramHi]; omega
  · rw [hout]; omega
  · rw [h10, ofNat_add_ofNat]; exact hc.frP n (by omega)
  · unfold Fn.Disjoint; simp only [hin, h12, hr12, hout]; omega
  · unfold Fn.Disjoint; simp only [hin, h12, hr12, hfr16]; omega
  · unfold Fn.Disjoint; simp only [hout, hfr16]; omega
  -- after the call
  obtain ⟨hret, hso2, hres⟩ := hpost
  have hso2' : ∀ j < 400, (j < off ∨ off + 40 ≤ j) →
      m2.mem (frB m + BitVec.ofNat 64 j) = m1.mem (frB m + BitVec.ofNat 64 j) := by
    intro j hj hj'
    apply hso2
    rintro (h | h) <;> simp only [InRange, hout, hfr16, n.frj (show j ≤ 512 by omega)] at h <;> omega
  have hcs : ∀ i ∈ calleeSaved, m2.reg i = m1.reg i := hret.2
  refine ⟨⟨?_, ?_, ?_, fun i hi => ?_, fun k hk t ht => ?_, fun j hj => hp2.1 _ (hc.pres j hj),
    fun a ha => ?_⟩, hret.1, hcs, ?_, hso2'⟩
  · rw [hcs 2 (by decide), hc.r2]
  · rw [hcs 8 (by decide), hc.r8]
  · rw [hcs 9 (by decide), hc.r9]
  · have : i ∈ calleeSaved := by
      simp only [calleeVars, List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
      omega
    rw [hcs i this]; exact hc.rk i hi
  · rw [hso2' _ (by omega) (by omega)]; exact hc.saved k hk t ht
  · have hn : ¬ (InRange (m1.reg 10) 40 a ∨ InRange (m1.reg 2 - 16) 16 a) := by
      rintro (h | h) <;> apply ha <;> unfold InRange at h ⊢ <;> omega
    rw [hso2 a hn]; exact hc.so a ha
  · have hb := hres (sl m o r) (F2.bytesOf m1 (m1.reg 10) 40)
      (by rw [h11, ← bytesOf_sl hor hsame]
          exact F3.bytesAt_bytesOf fun j hj => by
            rw [ofNat_add_ofNat, hsame _ (by omega)]; exact e.inP _ (by omega))
      (by rw [sl_length m hor, h12, hr12])
      (F3.bytesAt_bytesOf fun j hj => by rw [h10, ofNat_add_ofNat]; exact hc.frP n (by omega))
      (by simp [F2.bytesOf])
    refine ⟨F2.bytesOf m1 (m1.reg 10) 40, fun k hk => ?_⟩
    have := hb k (by simp [F2.result40]; exact hk)
    rw [← ofNat_add_ofNat, ← h10, this, h11]
    simp [F2.result40]

/-! ## nextUint64 from a cut -/

/-- A nextUint64 call from the frame: result at frame offset `roff`, slice at frame offset 48
holding `(inp + o, r)`. -/
theorem ncall {m m1 : Machine} (n : Nums m) (e : Entry m) (hc : Fr m m1)
    {roff o r : Nat} (hr1 : 64 ≤ roff) (hr2 : roff + 16 ≤ 320) (hal : roff % 8 = 0)
    (hor : o + r ≤ (m.reg 12).toNat)
    (h10 : m1.reg 10 = frB m + BitVec.ofNat 64 roff) (h11 : m1.reg 11 = frB m + BitVec.ofNat 64 48)
    (hs0 : ∀ t < 8, m1.mem (frB m + BitVec.ofNat 64 (48 + t)) =
      some (byteOf (m.reg 11 + BitVec.ofNat 64 o) t))
    (hs1 : ∀ t < 8, m1.mem (frB m + BitVec.ofNat 64 (56 + t)) = some (byteOf (BitVec.ofNat 64 r) t))
    (h1 : RetAligned m1) :
    F3.Pre m1 ∧ ∀ m2, F3.Post m1 m2 → Preserved m1 m2 →
      Fr m m2 ∧ m2.pc = (m1.reg 1 &&& ~~~(1 : Word)) ∧ (∀ i ∈ calleeSaved, m2.reg i = m1.reg i) ∧
      (∀ j < 16, m2.mem (frB m + BitVec.ofNat 64 (roff + j)) =
        some (F3.resultByte (sl m o r) ((m1.mem (frB m + BitVec.ofNat 64 (roff + j))).getD 0) j)) ∧
      (∀ j < 16, m2.mem (frB m + BitVec.ofNat 64 (48 + j)) =
        some (F3.sliceByte (m.reg 11 + BitVec.ofNat 64 o) (BitVec.ofNat 64 r) (sl m o r)
          ((m1.mem (frB m + BitVec.ofNat 64 (48 + j))).getD 0) j)) ∧
      (∀ j < 400, (j < 48 ∨ (64 ≤ j ∧ j < roff) ∨ roff + 16 ≤ j) →
        m2.mem (frB m + BitVec.ofNat 64 j) = m1.mem (frB m + BitVec.ofNat 64 j)) := by
  have hf := n.fr; have h512 := n.sp512
  have hlo := n.spLo; have hhi := n.spHi; have hal16 := n.spA
  have hil := n.inLo; have hih := n.inHi
  unfold Layout.ramLo at hlo; unfold Layout.ramHi at hhi
  unfold Layout.inputLo at hil; unfold Layout.inputHi at hih
  have hr12 : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat]; omega
  have hres : (m1.reg 10).toNat = (m.reg 2).toNat - 400 + roff := by rw [h10, n.frj (by omega)]
  have hsl : (m1.reg 11).toNat = (m.reg 2).toNat - 400 + 48 := by rw [h11, n.frj (by omega)]
  have hst : (m1.reg 2 - 112).toNat = (m.reg 2).toNat - 512 := by
    rw [hc.r2]; show (frB m - BitVec.ofNat 64 112).toNat = _
    rw [BitVec.toNat_sub, hf]; simp; omega
  have hst' : (m1.reg 2 - BitVec.ofNat 64 112).toNat = (m.reg 2).toNat - 512 := hst
  have hsame : ∀ j < (m.reg 12).toNat,
      m1.mem (m.reg 11 + BitVec.ofNat 64 j) = m.mem (m.reg 11 + BitVec.ofNat 64 j) :=
    fun j hj => hc.inMem n hj
  have hw0 : F3.wordAt m1 (m1.reg 11) = m.reg 11 + BitVec.ofNat 64 o := by
    refine wordAt_of_bytes (by rw [hsl]; omega)
      (by rw [hsl]; simp [Machine.readable, Machine.inRange, Layout.ramLo, Layout.ramHi]; omega)
      fun t ht => ?_
    rw [h11, ofNat_add_ofNat]; exact hs0 t ht
  have h56 : m1.reg 11 + 8 = frB m + BitVec.ofNat 64 56 := by
    rw [h11, show (8 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]
  have hw1 : F3.wordAt m1 (m1.reg 11 + 8) = BitVec.ofNat 64 r := by
    rw [h56]
    refine wordAt_of_bytes (by rw [n.frj (by omega)]; omega)
      (by rw [n.frj (by omega)]; simp [Machine.readable, Machine.inRange, Layout.ramLo,
        Layout.ramHi]; omega) fun t ht => ?_
    rw [ofNat_add_ofNat]; exact hs1 t ht
  have hin : (m.reg 11 + BitVec.ofNat 64 o).toNat = (m.reg 11).toNat + o := n.inj (by omega)
  refine ⟨⟨hc.ro n e, ⟨?_, ?_, ?_, fun j hj => ?_⟩, h1, ?_, ?_, fun j hj => ?_, ?_, ?_,
    fun j hj => ?_, ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun m2 hpost hp2 => ?_⟩
  · rw [hc.r2, hf]; omega
  · rw [hc.r2, hf]; unfold Layout.ramLo; omega
  · rw [hc.r2, hf]; unfold Layout.ramHi; omega
  · have := hc.pres j (by omega)
    rwa [addr_eq (a := m.reg 2 - 512) (b := m1.reg 2 - BitVec.ofNat 64 112) (i := j) (j := j)
      (by rw [h512]; omega) (by rw [hst']; omega) (by rw [h512, hst'])] at this
  · simp [Machine.writable, Machine.inRange, hres, Layout.ramLo, Layout.ramHi]; omega
  · rw [hres]; omega
  · rw [h10, ofNat_add_ofNat]; exact hc.frP n (by omega)
  · simp [Machine.writable, Machine.inRange, hsl, Layout.ramLo, Layout.ramHi]; omega
  · rw [hsl]; omega
  · rw [h11, ofNat_add_ofNat]; exact hc.frP n (by omega)
  · show Machine.readable (F3.wordAt m1 (m1.reg 11)).toNat (F3.wordAt m1 (m1.reg 11 + 8)).toNat = true
    rw [hw0, hw1, hin, hr12]
    simp [Machine.readable, Machine.inRange, Layout.inputLo, Layout.inputHi]; omega
  · show (m1.mem (F3.wordAt m1 (m1.reg 11) + BitVec.ofNat 64 j)).isSome
    have hj' : j < r := by
      have : j < (F3.wordAt m1 (m1.reg 11 + 8)).toNat := hj
      rwa [hw1, hr12] at this
    rw [hw0, ofNat_add_ofNat, hsame _ (by omega)]; exact e.inP _ (by omega)
  all_goals try (unfold Fn.Disjoint; simp only [hw0, hw1, hin, hr12, hres, hsl, hst]; omega)
  -- after the call
  obtain ⟨hret, hso2, hrs⟩ := hpost
  have hso2' : ∀ j < 400, (j < 48 ∨ (64 ≤ j ∧ j < roff) ∨ roff + 16 ≤ j) →
      m2.mem (frB m + BitVec.ofNat 64 j) = m1.mem (frB m + BitVec.ofNat 64 j) := by
    intro j hj hj'
    apply hso2
    rintro (h | h | h) <;> simp only [InRange, hres, hsl, hst, n.frj (show j ≤ 512 by omega)] at h <;>
      omega
  have hcs : ∀ i ∈ calleeSaved, m2.reg i = m1.reg i := hret.2
  have hb := hrs (sl m o r)
    (by rw [hw0, ← bytesOf_sl hor hsame]
        exact F3.bytesAt_bytesOf fun j hj => by
          rw [ofNat_add_ofNat, hsame _ (by omega)]; exact e.inP _ (by omega))
    (by rw [sl_length m hor, hw1, hr12])
  rw [hw0, hw1] at hb
  refine ⟨⟨?_, ?_, ?_, fun i hi => ?_, fun k hk t ht => ?_, fun j hj => hp2.1 _ (hc.pres j hj),
    fun a ha => ?_⟩, hret.1, hcs, fun j hj => ?_, fun j hj => ?_, hso2'⟩
  · rw [hcs 2 (by decide), hc.r2]
  · rw [hcs 8 (by decide), hc.r8]
  · rw [hcs 9 (by decide), hc.r9]
  · have : i ∈ calleeSaved := by
      simp only [calleeVars, List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
      omega
    rw [hcs i this]; exact hc.rk i hi
  · rw [hso2' _ (by omega) (by omega)]; exact hc.saved k hk t ht
  · have hn : ¬ (InRange (m1.reg 10) 16 a ∨ InRange (m1.reg 11) 16 a ∨
        InRange (m1.reg 2 - 112) 112 a) := by
      rintro (h | h | h) <;> apply ha <;> unfold InRange at h ⊢ <;> omega
    rw [hso2 a hn]; exact hc.so a ha
  · have := hb.1 j hj
    rwa [h10, ofNat_add_ofNat] at this
  · have := hb.2 j hj
    rwa [h11, ofNat_add_ofNat] at this

/-! ## Reading callee results back from the frame -/

theorem byte0_of {m mh : Machine} {c : Word} {k : Nat} {b : Byte}
    (h : mh.mem (frB m + BitVec.ofNat 64 k) = some b) : (envC m mh c).byte0 0 k = b := by
  have ef := envC_facts m mh c
  rw [ef.by0, ef.b0, h]; rfl

/-- decodeItem's outcome for input `I` at `P` lies at offset `off` of the frame. -/
def Out (env : Env) (off : Nat) (P : Word) (I : List Byte) : Prop :=
  ∃ before : List Byte, ∀ k < 40, env.byte0 0 (off + k) = F2.resultByte P I before k

theorem out_of {m mh : Machine} {c : Word} {off : Nat} {P : Word} {I : List Byte}
    (h : ∃ before : List Byte, ∀ k < 40, mh.mem (frB m + BitVec.ofNat 64 (off + k)) =
      some (F2.resultByte P I before k)) : Out (envC m mh c) off P I := by
  obtain ⟨before, hb⟩ := h
  exact ⟨before, fun k hk => byte0_of (hb k hk)⟩

theorem init_word {env : Env} {r off : Nat} {w : Word}
    (h : ∀ t < 8, env.byte0 r (off + t) = byteOf w t) : (Sym.init r off 8).eval env = w := by
  simp only [Sym.eval]
  exact F3.word_of_bytes h

theorem out_err {env : Env} {off : Nat} {P : Word} {I : List Byte} (h : Out env off P I)
    (hd : F2.decode I = .error) : (Sym.init 0 (off + 32) 2).eval env = BitVec.ofNat 64 4 := by
  obtain ⟨before, hb⟩ := h
  have h0 := hb 32 (by decide)
  have h1 := hb 33 (by decide)
  simp only [F2.resultByte, hd, F2.errorByte] at h0 h1
  simp only [Sym.eval, byteList]
  rw [h0, show off + 32 + 1 = off + 33 by omega, h1]
  decide

theorem out_ok {env : Env} {off : Nat} {P : Word} {I : List Byte} (h : Out env off P I)
    {b : Bool} {hh p : Nat} (hd : F2.decode I = .success b hh p) :
    (Sym.init 0 (off + 32) 2).eval env = BitVec.ofNat 64 0 ∧
    (Sym.bin .and (.init 0 (off + 16) 1) (.lit 1)).eval env = BitVec.ofNat 64 (if b then 1 else 0) ∧
    (Sym.init 0 (off + 8) 8).eval env = BitVec.ofNat 64 p ∧
    (Sym.init 0 (off + 24) 8).eval env = BitVec.ofNat 64 (hh + p) ∧
    (Sym.init 0 off 8).eval env = (if I.head? = some 128 then 1 else P + BitVec.ofNat 64 hh) := by
  obtain ⟨before, hb⟩ := h
  have hr : ∀ k < 40, env.byte0 0 (off + k) = F2.successByte
      (if I.head? = some 128 then 1 else P + BitVec.ofNat 64 hh)
      (BitVec.ofNat 64 p) (BitVec.ofNat 64 (hh + p)) b before k := fun k hk => by
    rw [hb k hk, F2.resultByte, hd]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h0 := hr 32 (by decide)
    have h1 := hr 33 (by decide)
    simp [F2.successByte] at h0 h1
    simp only [Sym.eval, byteList]
    rw [h0, show off + 32 + 1 = off + 33 by omega, h1]
    decide
  · have h0 := hr 16 (by decide)
    simp [F2.successByte] at h0
    simp only [Sym.eval, byteList, BinOp.eval]
    rw [h0]
    cases b <;> decide
  · exact init_word fun t ht => by
      rw [show off + 8 + t = off + (8 + t) by omega, hr _ (by omega)]
      simp only [F2.successByte]
      rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega
  · exact init_word fun t ht => by
      rw [show off + 24 + t = off + (24 + t) by omega, hr _ (by omega)]
      simp only [F2.successByte]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)]; congr 1; omega
  · exact init_word fun t ht => by
      rw [hr _ (by omega)]
      simp only [F2.successByte]
      rw [if_pos (by omega)]

/-- nextUint64's result for input `I` lies at offset `roff` of the frame. -/
def NOut (env : Env) (roff : Nat) (I : List Byte) : Prop :=
  ∃ old : Nat → Byte, ∀ j < 16, env.byte0 0 (roff + j) = F3.resultByte I (old j) j

theorem nout_err {env : Env} {roff : Nat} {I : List Byte} (h : NOut env roff I)
    (hn : F3.nextUint64 I = none) : (Sym.init 0 (roff + 8) 2).eval env = BitVec.ofNat 64 3 := by
  obtain ⟨old, hb⟩ := h
  have h0 := hb 8 (by decide)
  have h1 := hb 9 (by decide)
  simp only [F3.resultByte, hn] at h0 h1
  simp only [Sym.eval, byteList]
  rw [h0, show roff + 8 + 1 = roff + 9 by omega, h1]
  decide

theorem nout_ok {env : Env} {roff : Nat} {I : List Byte} (h : NOut env roff I) {v : Word} {c : Nat}
    (hn : F3.nextUint64 I = some (v, c)) :
    (Sym.init 0 (roff + 8) 2).eval env = BitVec.ofNat 64 0 ∧ (Sym.init 0 roff 8).eval env = v := by
  obtain ⟨old, hb⟩ := h
  refine ⟨?_, init_word fun t ht => ?_⟩
  · have h0 := hb 8 (by decide)
    have h1 := hb 9 (by decide)
    simp [F3.resultByte, hn] at h0 h1
    simp only [Sym.eval, byteList]
    rw [h0, show roff + 8 + 1 = roff + 9 by omega, h1]
    decide
  · rw [hb t (by omega)]; simp only [F3.resultByte, hn, if_pos ht]

/-- The slice words after nextUint64 lie at offset 48 of the frame. -/
def SOut (env : Env) (P R : Word) (I : List Byte) : Prop :=
  ∃ old : Nat → Byte, ∀ j < 16, env.byte0 0 (48 + j) = F3.sliceByte P R I (old j) j

theorem sout_ok {env : Env} {P R : Word} {I : List Byte} (h : SOut env P R I) {v : Word} {c : Nat}
    (hn : F3.nextUint64 I = some (v, c)) :
    (Sym.init 0 48 8).eval env = P + BitVec.ofNat 64 c ∧
    (Sym.init 0 56 8).eval env = R - BitVec.ofNat 64 c := by
  obtain ⟨old, hb⟩ := h
  refine ⟨init_word fun t ht => ?_, init_word fun t ht => ?_⟩
  · rw [hb t (by omega)]; simp only [F3.sliceByte, hn, if_pos ht]
  · rw [show 56 + t = 48 + (8 + t) by omega, hb (8 + t) (by omega)]
    simp only [F3.sliceByte, hn, if_neg (show ¬ 8 + t < 8 by omega)]
    congr 1; omega

/-! ## Returns -/

def retT : Sym := .bin .and (.var 33) (.lit 18446744073709551614)

/-- Callee-saved registers at a return leaf: `sp = ptr 0 400`, `s0 .. s8` reloaded from the frame,
`s9 .. s11` their own variables. -/
def savedOK (lS : SState) : Bool :=
  lS.reg 2 == .ptr 0 400 && lS.reg 8 == .var 34 && lS.reg 9 == .var 35 && lS.reg 18 == .var 36 &&
    lS.reg 19 == .var 37 && lS.reg 20 == .var 38 && lS.reg 21 == .var 39 &&
    lS.reg 22 == .var 40 && lS.reg 23 == .var 41 && lS.reg 24 == .var 42 &&
    calleeVars.all (fun i => lS.reg i == .var i) && lS.regions == regionsR

theorem savedOK_regions {lS : SState} (h : savedOK lS = true) : lS.regions = regionsR := by
  simp only [savedOK, Bool.and_eq_true, beq_iff_eq] at h; exact h.2

theorem regs_saved {m mh mf : Machine} (hc : Fr m mh) {c : Word} {lS : SState}
    (hm' : Match (envC m mh c) lS mf) (hsv : savedOK lS = true) :
    ∀ i ∈ calleeSaved, mf.reg i = m.reg i := by
  have ef := envC_facts m mh c
  simp only [savedOK, Bool.and_eq_true, beq_iff_eq] at hsv
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨e2, e8⟩, e9⟩, e18⟩, e19⟩, e20⟩, e21⟩, e22⟩, e23⟩, e24⟩, eall⟩, -⟩ := hsv
  have ev : ∀ k ∈ calleeVars, lS.reg k = .var k :=
    fun k hk' => eq_of_beq (List.all_eq_true.mp eall k hk')
  have hv : ∀ k < 10, (Sym.var (33 + k)).eval (envC m mh c) = savedVal m k := ef.vs
  intro i hi
  rw [← hm'.regs i]
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show (lS.reg 2).eval _ = _; rw [e2]; simp [Sym.eval, ef.b0, frB, BitVec.sub_add_cancel]
  · show (lS.reg 8).eval _ = _; rw [e8]; exact hv 1 (by decide)
  · show (lS.reg 9).eval _ = _; rw [e9]; exact hv 2 (by decide)
  · show (lS.reg 18).eval _ = _; rw [e18]; exact hv 3 (by decide)
  · show (lS.reg 19).eval _ = _; rw [e19]; exact hv 4 (by decide)
  · show (lS.reg 20).eval _ = _; rw [e20]; exact hv 5 (by decide)
  · show (lS.reg 21).eval _ = _; rw [e21]; exact hv 6 (by decide)
  · show (lS.reg 22).eval _ = _; rw [e22]; exact hv 7 (by decide)
  · show (lS.reg 23).eval _ = _; rw [e23]; exact hv 8 (by decide)
  · show (lS.reg 24).eval _ = _; rw [e24]; exact hv 9 (by decide)
  all_goals
    rw [ev _ (by decide)]
    exact (ef.v _).trans (hc.rk _ (by decide))

theorem retT_eval (m mh : Machine) (c : Word) :
    retT.eval (envC m mh c) = (m.reg 1 &&& ~~~(1 : Word)) := by
  simp only [retT, Sym.eval, BinOp.eval, F2.notOne]
  rw [show (33 : Nat) = 33 + 0 from rfl, (envC_facts m mh c).vs 0 (by decide)]
  rfl

theorem retT_aligned {m : Machine} (e : Entry m) (mh : Machine) (c : Word) :
    Oblig.holds (envC m mh c) (.aligned retT 4) := by
  show (retT.eval (envC m mh c)).toNat % 4 = 0
  rw [retT_eval]; exact e.ra

/-- Memory after a leaf, outside the frame and the result. -/
theorem leaf_so {m mh mf : Machine} (n : Nums m) (hc : Fr m mh) {c : Word} {x : Nat → Option Sym}
    (hfr : SameOutside (InWritable (envC m mh c) (SC x)) mh mf) :
    SameOutside (fun a => InRange (m.reg 10) 80 a ∨ InRange (m.reg 2 - 512) 512 a ∨
      InRange (BitVec.ofNat 64 Layout.extraParams) 8 a) m mf := by
  intro a ha
  rw [hfr a fun h => ha (by
    rcases n.writable h with h | h
    · right; left
      have h1 := n.fr; have h2 := n.sp512; have h3 := n.spLo; unfold Layout.ramLo at h3
      unfold InRange at h ⊢; omega
    · exact .inl h)]
  exact hc.so a fun h => ha (.inr (.inl h))

theorem post_of {m mf : Machine} (hret : Returns m mf)
    (hso : SameOutside (fun a => InRange (m.reg 10) 80 a ∨ InRange (m.reg 2 - 512) 512 a ∨
      InRange (BitVec.ofNat 64 Layout.extraParams) 8 a) m mf)
    (hres : match walk (inputOf m) with
      | none => ErrorOK mf (m.reg 10)
      | some vals => ResultOK mf (m.reg 10) vals) : Post m mf := by
  refine ⟨hret, hso, fun input hi hl => ?_⟩
  have : input = inputOf m := by rw [F2.eq_bytesOf hi, hl]
  subst this
  exact hres

/-- A result byte the leaf wrote. -/
theorem res_byte {m mh mf : Machine} {c : Word} {lS : SState} (hm' : Match (envC m mh c) lS mf)
    (hreg : lS.regions = regionsR) {j k : Nat} {v : Sym} (hj : j < 80)
    (hv : F2.wview lS.mem 1 j = some (v, k)) :
    mf.mem (m.reg 10 + BitVec.ofNat 64 j) = some (byteOf (v.eval (envC m mh c)) k) := by
  have ef := envC_facts m mh c
  have := hm'.mem 1 j (by rw [hreg]; decide) (by rw [ef.s1]; exact hj)
  rw [ef.b1, F2.memByte_wview, hv] at this
  exact this

/-- A direct error return: tag `v = 3` written at result byte 72. -/
theorem err_exit {m mh mf : Machine} (n : Nums m) (hc : Fr m mh) {c : Word} {x : Nat → Option Sym}
    {lS : SState} (hm' : Match (envC m mh c) lS mf)
    (hfr : SameOutside (InWritable (envC m mh c) (SC x)) mh mf)
    (hex : mf.pc = retT.eval (envC m mh c)) (hsv : savedOK lS = true) {v : Sym}
    (h72 : F2.wview lS.mem 1 72 = some (v, 0)) (h73 : F2.wview lS.mem 1 73 = some (v, 1))
    (hv : v.eval (envC m mh c) = BitVec.ofNat 64 3) (hw : walk (inputOf m) = none) : Post m mf := by
  have hreg := savedOK_regions hsv
  refine post_of ⟨by rw [hex, retT_eval], regs_saved hc hm' hsv⟩ (leaf_so n hc hfr) ?_
  rw [hw]
  refine ⟨?_, ?_⟩
  · have := res_byte hm' hreg (by decide) h72
    rw [hv] at this; exact this
  · have := res_byte hm' hreg (by decide) h73
    rw [hv] at this; exact this

/-! ## The memcpy tail -/

def memcpyOK (lS : SState) : Bool :=
  savedOK lS && lS.reg 1 == .var 33 && lS.reg 10 == .ptr 1 0 && lS.reg 11 == .lit errConst &&
    lS.reg 12 == .lit 80 && lS.mem.all (fun w => w.r == 0)

theorem errConst_72 : zesuImage.rodataByte? (errConst + 72) = some 3 := by decide
theorem errConst_73 : zesuImage.rodataByte? (errConst + 73) = some 0 := by decide

theorem errConst_src : ∀ t < 80, (zesuImage.rodataByte? (errConst + t)).isSome := by decide

/-- The `memcpy` tail: its precondition at the jump, and `Post` for its result. -/
theorem memcpy_exit {m mh mf : Machine} (n : Nums m) (e : Entry m) (hc : Fr m mh) {c : Word}
    {x : Nat → Option Sym} {lS : SState} (hm' : Match (envC m mh c) lS mf)
    (hfr : SameOutside (InWritable (envC m mh c) (SC x)) mh mf) (hk : memcpyOK lS = true)
    (hw : walk (inputOf m) = none) : MemcpyPre mf ∧ ∀ m2, MemcpyPost mf m2 → Post m m2 := by
  have ef := envC_facts m mh c
  have hk' := hk
  simp only [memcpyOK, Bool.and_eq_true, beq_iff_eq] at hk'
  obtain ⟨⟨⟨⟨⟨hsv, r1⟩, r10⟩, r11⟩, r12⟩, hw0⟩ := hk'
  have hreg := savedOK_regions hsv
  have g : ∀ i : Fin 32, mf.reg i = (lS.reg i.val).eval (envC m mh c) := fun i => (hm'.regs i).symm
  have g1 : mf.reg 1 = m.reg 1 := by
    rw [g 1]; show (lS.reg 1).eval _ = _; rw [r1]
    exact (envC_facts m mh c).vs 0 (by decide)
  have g10 : mf.reg 10 = m.reg 10 := by
    rw [g 10]; show (lS.reg 10).eval _ = _; rw [r10]; simp [Sym.eval, ef.b1]
  have g11 : mf.reg 11 = BitVec.ofNat 64 errConst := by
    rw [g 11]; show (lS.reg 11).eval _ = _; rw [r11]; rfl
  have g12 : mf.reg 12 = BitVec.ofNat 64 80 := by
    rw [g 12]; show (lS.reg 12).eval _ = _; rw [r12]; rfl
  -- the result region was not written
  have hres : ∀ j < 80, mf.mem (m.reg 10 + BitVec.ofNat 64 j) = mh.mem (m.reg 10 + BitVec.ofNat 64 j) := by
    intro j hj
    have := hm'.mem 1 j (by rw [hreg]; decide) (by rw [ef.s1]; exact hj)
    rw [ef.b1, memByte_nowrite (fun w hw => by
      have := List.all_eq_true.mp hw0 w hw; simp only [beq_iff_eq] at this
      simp [Write.covers, this])] at this
    rw [this]
    have h2 := hc.init n e c 1 j (by decide) (by rw [ef.s1]; exact hj)
    rw [ef.b1] at h2; exact h2.symm
  have hso := leaf_so n hc hfr
  have hlo := n.resLo; have hhi := n.resHi; have hslo := n.spLo; have hd2 := n.d2; have hd3 := n.d3
  have h512 := n.sp512
  unfold Layout.ramLo at hlo hslo; unfold Layout.ramHi at hhi; unfold Layout.extraParams at hd2 hd3
  have hro : RodataLoaded zesuImage mf := by
    intro a b hab
    have ha := rodata_lt a b hab
    unfold Layout.ramLo at ha
    have hn : ¬ (InRange (m.reg 10) 80 (BitVec.ofNat 64 a) ∨ InRange (m.reg 2 - 512) 512 (BitVec.ofNat 64 a) ∨
        InRange (BitVec.ofNat 64 Layout.extraParams) 8 (BitVec.ofNat 64 a)) := by
      have : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
      simp only [InRange, this, h512, BitVec.toNat_ofNat, Layout.extraParams]; omega
    rw [hso _ hn]
    exact e.ro a b hab
  have hscr : ∀ t < 8, ¬ (InRange (m.reg 10) 80 (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 t) ∨
      InRange (m.reg 2 - 512) 512 (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 t)) := by
    intro t ht
    have : (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 t).toNat = 0xa0400f00 + t := by
      simp [BitVec.toNat_add, Layout.extraParams]; omega
    simp only [InRange, this, h512]; omega
  have hdom : MemcpyPre mf := by
    unfold MemcpyPre ziskMemcpyDomain
    simp only [g1, g10, g11, g12, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
    refine ⟨⟨⟨e.ra, by decide⟩, ?_⟩, .inr ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
    · refine readBytes_isSome_of fun t ht => ?_
      rw [BitVec.ofNat_add]
      have hf := n.fr
      rw [hfr _ (fun h => by
        rcases n.writable h with h | h
        · exact hscr t ht (.inr (by unfold InRange at h ⊢; omega))
        · exact hscr t ht (.inl h))]
      rw [hc.so _ (fun h => hscr t ht (.inr h))]
      exact e.scrP t ht
    · decide
    · refine readBytes_isSome_of fun t ht => ?_
      have ht' : t < 80 := by simpa using ht
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (errConst_src t ht')
      have : (BitVec.ofNat 64 errConst).toNat = errConst := by decide
      rw [this, hro _ _ hb]; rfl
    · simp [Machine.writable, Machine.inRange, Layout.ramLo, Layout.ramHi]; omega
    · refine readBytes_isSome_of fun t ht => ?_
      have ht' : t < 80 := by simpa using ht
      rw [ofNat_toNat_add, hres t ht']
      rw [hc.so _ (n.res_not_stack ht')]; exact e.resP t ht'
  refine ⟨hdom, fun m2 hm2 => ?_⟩
  have hz : ziskMemcpy mf = some m2 := hm2
  have hcs := regs_saved hc hm' hsv
  have hres2 : ∀ j, j = 72 ∨ j = 73 → m2.mem (m.reg 10 + BitVec.ofNat 64 j) =
      some (BitVec.ofNat 8 (if j = 72 then 3 else 0)) := by
    intro j hj
    have hj80 : j < 80 := by omega
    have := memcpy_dst hz (i := j) (by rw [g12]; simp; omega)
      (by rw [g10, g11]; intro h; have := congrArg BitVec.toNat h; simp [errConst] at this; omega)
      (by rw [g10, g12]; simp; omega) (by rw [g11, g12]; decide)
      (by rw [g11]; simp only [InRange, BitVec.toNat_add, BitVec.toNat_ofNat, Layout.extraParams,
        errConst]; omega)
    rw [g10] at this
    rw [this, g11, ← BitVec.ofNat_add]
    rcases hj with rfl | rfl
    · exact hro _ _ errConst_72
    · exact hro _ _ errConst_73
  refine post_of ⟨?_, fun i hi => ?_⟩ (fun a ha => ?_) ?_
  · rw [memcpy_eq hz]; simp only [g1]
  · rw [memcpy_reg hz]; exact hcs i hi
  · rw [memcpy_out hz (fun h => ha (.inl (by rwa [g10, g12] at h)))
      (fun h => ha (.inr (.inr h)))]
    exact hso a ha
  · rw [hw]
    exact ⟨hres2 72 (.inl rfl), hres2 73 (.inr rfl)⟩

/-! ## Success returns -/

/-- The result view of a success return: words `ws` at 0, 8, .., 64, the zero halfword at 72. -/
def succView (ws : List Sym) (j : Nat) : Option (Sym × Nat) :=
  if j < 72 then some (ws.getD (j / 8) (.lit 0), j % 8) else some (.lit 0, j - 72)

def succOK (lS : SState) (ws : List Sym) : Bool :=
  savedOK lS && (List.range 74).all (fun j => F2.wview lS.mem 1 j == succView ws j)

/-- An optional field's two words: tag byte and, when present, the value. -/
def OptSym (env : Env) (vs ts : Sym) (v : Option Nat) : Prop :=
  byteOf (ts.eval env) 0 = (if v.isSome then 1 else 0) ∧ ∀ k, v = some k → vs.eval env = BitVec.ofNat 64 k

theorem succ_exit {m mh mf : Machine} (n : Nums m) (hc : Fr m mh) {c : Word}
    {x : Nat → Option Sym} {lS : SState} (hm' : Match (envC m mh c) lS mf)
    (hfr : SameOutside (InWritable (envC m mh c) (SC x)) mh mf)
    (hex : mf.pc = retT.eval (envC m mh c)) {ws : List Sym} (hk : succOK lS ws = true)
    {vals : List Nat} (hw : walk (inputOf m) = some vals)
    (h0 : (ws.getD 0 (.lit 0)).eval (envC m mh c) = BitVec.ofNat 64 (vals.getD 0 0))
    (h1 : (ws.getD 1 (.lit 0)).eval (envC m mh c) = BitVec.ofNat 64 (vals.getD 1 0))
    (h2 : (ws.getD 2 (.lit 0)).eval (envC m mh c) = BitVec.ofNat 64 (vals.getD 2 0))
    (h3 : OptSym (envC m mh c) (ws.getD 3 (.lit 0)) (ws.getD 4 (.lit 0)) vals[3]?)
    (h4 : OptSym (envC m mh c) (ws.getD 5 (.lit 0)) (ws.getD 6 (.lit 0)) vals[4]?)
    (h5 : OptSym (envC m mh c) (ws.getD 7 (.lit 0)) (ws.getD 8 (.lit 0)) vals[5]?) :
    Post m mf := by
  simp only [succOK, Bool.and_eq_true] at hk
  obtain ⟨hsv, hv⟩ := hk
  have hreg := savedOK_regions hsv
  have hv' : ∀ j < 74, F2.wview lS.mem 1 j = succView ws j := fun j hj => by
    have := List.all_eq_true.mp hv j (List.mem_range.mpr hj); simpa using this
  have hb : ∀ j < 74, mf.mem (m.reg 10 + BitVec.ofNat 64 j) =
      some (if j < 72 then byteOf ((ws.getD (j / 8) (.lit 0)).eval (envC m mh c)) (j % 8) else 0) := by
    intro j hj
    by_cases h72 : j < 72
    · rw [if_pos h72]
      exact res_byte hm' hreg (by omega) ((hv' j hj).trans (by simp [succView, h72]))
    · rw [if_neg h72]
      have hvj : F2.wview lS.mem 1 j = some (.lit 0, j - 72) := (hv' j hj).trans (by simp [succView, h72])
      rw [res_byte hm' hreg (by omega) hvj]
      simp [Sym.eval]
  have word : ∀ q < 9, ∀ v : Nat, (ws.getD q (.lit 0)).eval (envC m mh c) = BitVec.ofNat 64 v →
      WordIs mf (m.reg 10 + BitVec.ofNat 64 (8 * q)) v := by
    intro q hq v hv t ht
    rw [ofNat_add_ofNat, hb _ (by omega), if_pos (by omega)]
    rw [show (8 * q + t) / 8 = q by omega, show (8 * q + t) % 8 = t by omega, hv]
  have tag : ∀ q < 9, ∀ b : Byte, byteOf ((ws.getD q (.lit 0)).eval (envC m mh c)) 0 = b →
      mf.mem (m.reg 10 + BitVec.ofNat 64 (8 * q)) = some b := by
    intro q hq b hb'
    rw [hb _ (by omega), if_pos (by omega), show 8 * q / 8 = q by omega,
      show 8 * q % 8 = 0 by omega, hb']
  refine post_of ⟨by rw [hex, retT_eval], regs_saved hc hm' hsv⟩ (leaf_so n hc hfr) ?_
  rw [hw]
  refine ⟨?_, ?_, ?_, ⟨tag 4 (by decide) _ h3.1, fun k hk => word 3 (by decide) k (h3.2 k hk)⟩,
    ⟨tag 6 (by decide) _ h4.1, fun k hk => word 5 (by decide) k (h4.2 k hk)⟩,
    ⟨tag 8 (by decide) _ h5.1, fun k hk => word 7 (by decide) k (h5.2 k hk)⟩, ?_, ?_⟩
  · have := word 0 (by decide) _ h0
    simpa using this
  · exact word 1 (by decide) _ h1
  · exact word 2 (by decide) _ h2
  · exact hb 72 (by decide)
  · exact hb 73 (by decide)

/-! ## Byte facts for optional tags -/

/-- Byte 0 of `cat lo hi 1` is byte 0 of `lo`. -/
theorem byteOf_cat1 (lo hi : Word) :
    byteOf ((lo &&& BitVec.ofNat 64 (2 ^ (8 * 1) - 1)) ||| (hi <<< (8 * 1))) 0 = byteOf lo 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [byteOf, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  have : (BitVec.ofNat 64 (2 ^ (8 * 1) - 1)).getLsbD (8 * 0 + k) = true := by
    revert k; decide
  rw [this]
  simp; omega

theorem byteOf_init {env : Env} {r off n : Nat} (hn : n ≤ 8) (h0 : 0 < n) :
    byteOf ((Sym.init r off n).eval env) 0 = env.byte0 r off := by
  simp only [Sym.eval]
  rw [byteOf_ofBytesLE _ (by rw [byteList_length]; exact hn) 0 (by rw [byteList_length]; exact h0)]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

/-! ## The walk, one field at a time -/

theorem fw_err {k : Kind} {later : List Kind} {rem : List Byte} {vals : List Nat} (hne : rem ≠ [])
    (hd : F2.decode rem = .error) : fieldWalk (k :: later) rem vals = none := by
  cases rem with
  | nil => exact absurd rfl hne
  | cons a l => simp only [fieldWalk]; rw [hd]

theorem fw_ok {k : Kind} {later : List Kind} {rem : List Byte} {vals : List Nat} (hne : rem ≠ [])
    {b : Bool} {h p : Nat} (hd : F2.decode rem = .success b h p) :
    fieldWalk (k :: later) rem vals =
      if k.isInt then
        (if b || 8 < p then none
         else fieldWalk later (rem.drop ((h + p) % 2 ^ 64)) (vals ++ [F2.bigEndian ((rem.drop h).take p)]))
      else fieldWalk later (rem.drop ((h + p) % 2 ^ 64)) vals := by
  cases rem with
  | nil => exact absurd rfl hne
  | cons a l => simp only [fieldWalk]; rw [hd]

theorem fw_nil (k : Kind) (later : List Kind) (vals : List Nat) :
    fieldWalk (k :: later) [] vals = if k.required then none else some vals := rfl

/-- `headerFits` bounds a decoded item inside the input. -/
theorem decode_fits {I : List Byte} (hf : headerFits I) {b : Bool} {h p : Nat}
    (hd : F2.decode I = .success b h p) : h + p ≤ I.length := by
  cases I with
  | nil => simp [F2.decode] at hd
  | cons c rest =>
    have hc := c.isLt
    simp only [headerFits] at hf
    simp only [F2.decode] at hd
    simp only [List.length_cons]
    have hmod : ∀ x y : Nat, x < 2 ^ 64 → x % 2 ^ 64 ≤ y → x ≤ y := fun x y hx h => by
      rwa [Nat.mod_eq_of_lt hx] at h
    by_cases h1 : c.toNat ≤ 127
    · rw [if_pos h1] at hd; cases hd; omega
    rw [if_neg h1] at hd
    by_cases h2 : c.toNat = 128
    · rw [if_pos h2] at hd; cases hd; omega
    rw [if_neg h2] at hd
    by_cases h3 : c.toNat ≤ 183
    · rw [if_pos h3] at hd
      obtain ⟨e1, e2, hl⟩ := F3.checked_success hd
      clear hd; rw [e1, e2]; exact hmod _ _ (by omega) hl
    rw [if_neg h3] at hd
    by_cases h4 : c.toNat ≤ 191
    · rw [if_pos h4] at hd
      have hw : longWidth c.toNat = c.toNat - 183 := by unfold longWidth; rw [if_pos ⟨by omega, h4⟩]
      rw [hw] at hf
      split at hd
      · obtain ⟨e1, e2, hl⟩ := F3.checked_success hd
        clear hd; rw [e1, e2]
        rcases hf with hf | hf | hf
        · omega
        · omega
        · exact hmod _ _ (by omega) hl
      · cases hd
    rw [if_neg h4] at hd
    by_cases h5 : c.toNat ≤ 247
    · rw [if_pos h5] at hd
      obtain ⟨e1, e2, hl⟩ := F3.checked_success hd
      clear hd; rw [e1, e2]; exact hmod _ _ (by omega) hl
    rw [if_neg h5] at hd
    have hw : longWidth c.toNat = c.toNat - 247 := by
      unfold longWidth; rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
    rw [hw] at hf
    split at hd
    · obtain ⟨e1, e2, hl⟩ := F3.checked_success hd
      clear hd; rw [e1, e2]
      rcases hf with hf | hf | hf
      · omega
      · omega
      · exact hmod _ _ (by omega) hl
    · cases hd

theorem walk_outer {I : List Byte} {h p : Nat} (hd : F2.decode I = .success true h p) (hp : 0 < p)
    (hfit : h + p ≤ I.length) : walk I = fieldWalk schedule ((I.drop h).take p) [] := by
  simp only [walk, hd]; rw [if_pos ⟨hp, hfit⟩]

theorem walk_outer_err {I : List Byte} (hd : F2.decode I = .error ∨
    (∃ h p, F2.decode I = .success false h p) ∨ ∃ h, F2.decode I = .success true h 0) :
    walk I = none := by
  rcases hd with hd | ⟨h, p, hd⟩ | ⟨h, hd⟩ <;> simp [walk, hd]

/-! ## Word arithmetic of the cursor -/

theorem adv_ptr (a : Word) (o x : Nat) :
    a + BitVec.ofNat 64 o + BitVec.ofNat 64 x = a + BitVec.ofNat 64 (o + x % 2 ^ 64) := by
  rw [ofNat_add_ofNat]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]

theorem adv_len {r x : Nat} (hr : r < 2 ^ 64) (hx : x % 2 ^ 64 ≤ r) :
    BitVec.ofNat 64 r - BitVec.ofNat 64 x = BitVec.ofNat 64 (r - x % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := Nat.mod_lt x (show 0 < 2 ^ 64 by decide)
  rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (show r - x % 2 ^ 64 < 2 ^ 64 by omega)]
  omega

theorem len_eq {r x : Nat} (hr : r < 2 ^ 64) :
    (BitVec.ofNat 64 r = BitVec.ofNat 64 x) ↔ r = x % 2 ^ 64 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa [Nat.mod_eq_of_lt hr] using this
  · intro h; apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt hr, h]

/-! ## Calls -/

/-- After decodeItem returned: the frame invariant and the outcome at `off` for the slice
`(o, r)`. -/
structure DSt (m mh : Machine) (off o r : Nat) : Prop where
  fr : Fr m mh
  fit : o + r ≤ (m.reg 12).toNat
  out : ∃ before : List Byte, ∀ k < 40, mh.mem (frB m + BitVec.ofNat 64 (off + k)) =
    some (F2.resultByte (m.reg 11 + BitVec.ofNat 64 o) (sl m o r) before k)

/-- A decodeItem call leaf: decodeItem's precondition, and the continuation at the return point
for every result. -/
theorem call_d {m mh m1 : Machine} (n : Nums m) (e : Entry m) (hc : Fr m mh) {c : Word}
    {x : Nat → Option Sym} {lS : SState} (hm' : Match (envC m mh c) lS m1)
    (hfr : SameOutside (InWritable (envC m mh c) (SC x)) mh m1) (hk : keepOK lS = true)
    {off o r ret : Nat} (hoff : off + 40 ≤ 320) (hal : off % 8 = 0)
    (hor : o + r ≤ (m.reg 12).toNat) (h1 : lS.reg 1 = .lit ret)
    (hra : (BitVec.ofNat 64 ret &&& ~~~(1 : Word)).toNat % 4 = 0)
    (hrp : (BitVec.ofNat 64 ret &&& ~~~(1 : Word)).toNat = ret)
    (h10 : (lS.reg 10).eval (envC m mh c) = frB m + BitVec.ofNat 64 off)
    (h11 : (lS.reg 11).eval (envC m mh c) = m.reg 11 + BitVec.ofNat 64 o)
    (h12 : (lS.reg 12).eval (envC m mh c) = BitVec.ofNat 64 r) {Q : Machine → Prop}
    (K : ∀ m2, DSt m m2 off o r → m2.pc.toNat = ret →
      (∀ i : Fin 32, i ∈ calleeSaved → m2.reg i = (lS.reg i.val).eval (envC m mh c)) →
      (∀ j < 400, (j < off ∨ off + 40 ≤ j) →
        m2.mem (frB m + BitVec.ofNat 64 j) = some (memByte (envC m mh c) lS.mem 0 j)) → Q m2) :
    F2.Pre m1 ∧ ∀ m2, F2.Post m1 m2 ∧ Preserved m1 m2 → Q m2 := by
  obtain ⟨hc1, hfm, -⟩ := Fr.of_leaf n e hc hm' hfr hk
  have g : ∀ i : Fin 32, m1.reg i = (lS.reg i.val).eval (envC m mh c) := fun i => (hm'.regs i).symm
  have g1 : m1.reg 1 = BitVec.ofNat 64 ret := by rw [g 1]; show (lS.reg 1).eval _ = _; rw [h1]; rfl
  obtain ⟨hpre, hpost⟩ := dcall n e hc1 hoff hal hor (by rw [g 10]; exact h10)
    (by rw [g 11]; exact h11) (by rw [g 12]; exact h12) (by unfold RetAligned; rw [g1]; exact hra)
  refine ⟨hpre, fun m2 ⟨hp, hpr⟩ => ?_⟩
  obtain ⟨hfr2, hpc2, hcs, hout, hsame⟩ := hpost m2 hp hpr
  exact K m2 ⟨hfr2, hor, hout⟩ (by rw [hpc2, g1]; exact hrp) (fun i hi => (hcs i hi).trans (g i))
    (fun j hj hj' => (hsame j hj hj').trans (hfm j hj))

/-- After nextUint64 returned: the frame invariant, its result at `roff` and the slice at 48 for
the input slice `(o, r)`. -/
structure NSt (m mh : Machine) (roff o r : Nat) : Prop where
  fr : Fr m mh
  fit : o + r ≤ (m.reg 12).toNat
  res : ∃ old : Nat → Byte, ∀ j < 16, mh.mem (frB m + BitVec.ofNat 64 (roff + j)) =
    some (F3.resultByte (sl m o r) (old j) j)
  slc : ∃ old : Nat → Byte, ∀ j < 16, mh.mem (frB m + BitVec.ofNat 64 (48 + j)) =
    some (F3.sliceByte (m.reg 11 + BitVec.ofNat 64 o) (BitVec.ofNat 64 r) (sl m o r) (old j) j)

/-- A nextUint64 call leaf: nextUint64's precondition, and the continuation at the return point
for every result. -/
theorem call_n {m mh m1 : Machine} (n : Nums m) (e : Entry m) (hc : Fr m mh) {c : Word}
    {x : Nat → Option Sym} {lS : SState} (hm' : Match (envC m mh c) lS m1)
    (hfr : SameOutside (InWritable (envC m mh c) (SC x)) mh m1) (hk : keepOK lS = true)
    {roff o r ret : Nat} (hr1 : 64 ≤ roff) (hr2 : roff + 16 ≤ 320)
    (hal : roff % 8 = 0) (hor : o + r ≤ (m.reg 12).toNat) (h1 : lS.reg 1 = .lit ret)
    (hra : (BitVec.ofNat 64 ret &&& ~~~(1 : Word)).toNat % 4 = 0)
    (hrp : (BitVec.ofNat 64 ret &&& ~~~(1 : Word)).toNat = ret)
    (h10 : lS.reg 10 = .ptr 0 roff) (h11 : lS.reg 11 = .ptr 0 48)
    (hs0 : ∀ t < 8, memByte (envC m mh c) lS.mem 0 (48 + t) = byteOf (m.reg 11 + BitVec.ofNat 64 o) t)
    (hs1 : ∀ t < 8, memByte (envC m mh c) lS.mem 0 (56 + t) = byteOf (BitVec.ofNat 64 r) t)
    {Q : Machine → Prop}
    (K : ∀ m2, NSt m m2 roff o r → m2.pc.toNat = ret →
      (∀ i : Fin 32, i ∈ calleeSaved → m2.reg i = (lS.reg i.val).eval (envC m mh c)) →
      (∀ j < 400, (j < 48 ∨ (64 ≤ j ∧ j < roff) ∨ roff + 16 ≤ j) →
        m2.mem (frB m + BitVec.ofNat 64 j) = some (memByte (envC m mh c) lS.mem 0 j)) → Q m2) :
    F3.Pre m1 ∧ ∀ m2, F3.Post m1 m2 ∧ Preserved m1 m2 → Q m2 := by
  have ef := envC_facts m mh c
  obtain ⟨hc1, hfm, -⟩ := Fr.of_leaf n e hc hm' hfr hk
  have g : ∀ i : Fin 32, m1.reg i = (lS.reg i.val).eval (envC m mh c) := fun i => (hm'.regs i).symm
  have g1 : m1.reg 1 = BitVec.ofNat 64 ret := by rw [g 1]; show (lS.reg 1).eval _ = _; rw [h1]; rfl
  have g10 : m1.reg 10 = frB m + BitVec.ofNat 64 roff := by
    rw [g 10]; show (lS.reg 10).eval _ = _; rw [h10]; simp [Sym.eval, ef.b0]
  have g11 : m1.reg 11 = frB m + BitVec.ofNat 64 48 := by
    rw [g 11]; show (lS.reg 11).eval _ = _; rw [h11]; simp [Sym.eval, ef.b0]
  obtain ⟨hpre, hpost⟩ := ncall n e hc1 hr1 hr2 hal hor g10 g11
    (fun t ht => by rw [hfm _ (by omega), hs0 t ht])
    (fun t ht => by rw [hfm _ (by omega), hs1 t ht])
    (by unfold RetAligned; rw [g1]; exact hra)
  refine ⟨hpre, fun m2 ⟨hp, hpr⟩ => ?_⟩
  obtain ⟨hfr2, hpc2, hcs, hres, hslc, hsame⟩ := hpost m2 hp hpr
  exact K m2 ⟨hfr2, hor, ⟨_, hres⟩, ⟨_, hslc⟩⟩ (by rw [hpc2, g1]; exact hrp)
    (fun i hi => (hcs i hi).trans (g i)) (fun j hj hj' => (hsame j hj hj').trans (hfm j hj))

end ZesuExec.Fn.F6
