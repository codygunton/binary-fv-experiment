import ZesuExec.Fn.F2.Lemmas

namespace ZesuExec.Fn.F2
open ZesuExec ZesuExec.Sym ZesuExec.Machine

sym_run runE := run zesuImage [loopHead1, loopHead2] 100 entry S0
sym_run runL1 := run zesuImage [loopHead1, loopHead2] 100 loopHead1 SL
sym_run runL2 := run zesuImage [loopHead1, loopHead2] 100 loopHead2 SL

set_option linter.unusedSimpArgs false

set_option hygiene false in
/-- A word computed from the first input byte, as a `Nat` equation. -/
macro "f2_word" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [↓eval_and_sext_init, Sym.eval, BinOp.eval, hb0]
  try simp [BitVec.toNat_and, BitVec.toNat_add, Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide : 256 < 2 ^ 64))]
  try simp only [land_255, land_127]
  try omega))

set_option hygiene false in
/-- `decode` of the input under the leaf's facts on the first byte and the length. -/
macro "f2_decode" : tactic => `(tactic| (
  rw [input_cons m (by omega)]
  simp (disch := omega) only [decode, checkedPayload, if_pos, if_neg, List.length_drop,
    bytesOf_length]))

set_option hygiene false in
/-- The obligations of a return leaf: the first byte is in bounds, the return is aligned. -/
macro "f2_obligs" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Oblig.holds, hs1]
  first | exact hal1 | exact ⟨by simp [Sym.eval]; omega, hal1⟩ | (simp [Sym.eval]; omega)))

/-! ## Facts from `Pre` -/

def envE (m : Machine) : Env := entryEnv m ((shape m).map (·.1))

theorem pre_sp {m : Machine} (hpre : Pre m) : (m.reg 2 - 16).toNat = (m.reg 2).toNat - 16 := by
  obtain ⟨-, ⟨-, hlo, -, -⟩, -⟩ := hpre
  have h16 : (16 : Word).toNat = 16 := rfl
  rw [BitVec.toNat_sub, h16]; unfold Layout.ramLo at hlo; omega

theorem pre_wf {m : Machine} (hpre : Pre m) (mh : Machine) (ov : Nat → Option Sym)
    (ks : List Write) : Env.WF (entryEnv mh ((shape m).map (·.1))) (entryState ov regionsR ks) := by
  have hsp := pre_sp hpre
  obtain ⟨-, ⟨hal, hlo, hhi, -⟩, -, hrd, -, hwr, hal8, -, hd1, hd2, hd3⟩ := hpre
  refine entry_wf (shape m) ?_ ?_
  · simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · refine ⟨by simp [frameR], by simp [frameR]; omega, ?_⟩
      simp [frameR, Machine.writable, Machine.inRange]
      simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
    · exact ⟨by simp [inputR], by simp [inputR, Nat.mod_one], by simpa [inputR] using hrd⟩
    · exact ⟨by simp [outR], by simpa [outR] using hal8, by simpa [outR] using hwr⟩
  · unfold Fn.Disjoint at hd1 hd2 hd3
    simp only [hsp] at hd1 hd2 hd3
    simp only [shape, shapeOf, List.map_cons, List.map_nil, List.pairwise_cons,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true, Fn.Disjoint, hsp]
    exact ⟨⟨by omega, by omega⟩, by omega, fun _ h => h.elim⟩

theorem pre_fit {m : Machine} (hpre : Pre m) : ∀ p ∈ shape m, p.1.1.toNat + p.1.2 < 2 ^ 64 := by
  have hsp := pre_sp hpre
  obtain ⟨-, ⟨-, hlo, hhi, -⟩, -, hrd, -, hwr, -⟩ := hpre
  simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false]
  simp [Machine.readable, Machine.writable, Machine.inRange, Layout.rodataLo, Layout.rodataHi,
    Layout.inputLo, Layout.inputHi, Layout.ramLo, Layout.ramHi] at hrd hwr hhi hlo
  rintro p (rfl | rfl | rfl) <;> simp <;> omega

/-- The writable regions are the outcome struct and the frame. -/
theorem pre_writable {m mh : Machine} (hpre : Pre m) {ov : Nat → Option Sym} {ks : List Write}
    {a : Word} (ha : InWritable (entryEnv mh ((shape m).map (·.1))) (entryState ov regionsR ks) a) :
    InRange (m.reg 10) 40 a ∨ InRange (m.reg 2 - 16) 16 a := by
  obtain ⟨p, hp, hw, hin⟩ := inWritable_entry (shape := shape m) ha (pre_fit hpre)
  simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact .inr hin
  · simp [inputR] at hw
  · exact .inl hin

theorem pre_notFrame_in {m : Machine} (hpre : Pre m) {j : Nat} (hj : j < (m.reg 12).toNat) :
    ¬ InRange (m.reg 2 - 16) 16 (m.reg 11 + BitVec.ofNat 64 j) := by
  have hsp := pre_sp hpre
  have hfit := pre_fit hpre ((m.reg 11, (m.reg 12).toNat), inputR) (by simp [shape, shapeOf])
  obtain ⟨-, ⟨-, hlo, -, -⟩, -, -, -, -, -, -, -, hd2, -⟩ := hpre
  unfold Fn.Disjoint at hd2
  simp only at hd2 hfit
  unfold InRange
  rw [hsp, toNat_add_ofNat (by omega)]
  rw [hsp] at hd2
  unfold Layout.ramLo at hlo
  omega

theorem pre_notFrame_out {m : Machine} (hpre : Pre m) {j : Nat} (hj : j < 40) :
    ¬ InRange (m.reg 2 - 16) 16 (m.reg 10 + BitVec.ofNat 64 j) := by
  have hsp := pre_sp hpre
  have hfit := pre_fit hpre ((m.reg 10, 40), outR) (by simp [shape, shapeOf])
  obtain ⟨-, ⟨-, hlo, -, -⟩, -, -, -, -, -, -, -, -, hd3⟩ := hpre
  unfold Fn.Disjoint at hd3
  simp only at hd3 hfit
  unfold InRange
  rw [hsp, toNat_add_ofNat (by omega)]
  rw [hsp] at hd3
  unfold Layout.ramLo at hlo
  omega

theorem pre_rodata {m : Machine} (hpre : Pre m) {a b : Nat}
    (h : zesuImage.rodataByte? a = some b) :
    ¬ InRange (m.reg 2 - 16) 16 (BitVec.ofNat 64 a) := by
  have hsp := pre_sp hpre
  obtain ⟨-, ⟨-, hlo, -, -⟩, -⟩ := hpre
  have ha : a < 0x80200000 := by
    simp [zesuImage, Image.rodataByte?, Gen.rodata_801136d8, RoSeg.byte?] at h
    have := (List.getElem?_eq_some_iff.mp h.2).1
    simp at this; omega
  simp only [InRange, hsp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega)]
  unfold Layout.ramLo at hlo
  omega

/-! ## Loops

Invariant at a loop head after `j` of the `w` length bytes: registers as the entry run leaves
them, the accumulator `a3` is the big-endian value of the first `j` length bytes, the cursor
`a5` points at length byte `j`, the frame holds the saved `ra` and `s0`, and memory outside
the frame is the entry memory. -/

def keepRegs : List Nat := [1, 9, 10, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- Registers a loop run leaves as their own variables. -/
def varRegs : List Nat := [1, 9, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

def Inv (m : Machine) (pre head w j : Nat) (mh : Machine) : Prop :=
  mh.pc.toNat = head ∧ j < w ∧ w ≤ 8 ∧ w < (m.reg 12).toNat ∧ (firstByte m).toNat = pre + w ∧
  (∀ i : Fin 32, i.val ∈ keepRegs → mh.reg i = m.reg i) ∧
  mh.reg 2 = m.reg 2 - 16 ∧ mh.reg 8 = m.reg 2 ∧
  mh.reg 11 = m.reg 11 + BitVec.ofNat 64 (w + 1) ∧ mh.reg 14 = BitVec.ofNat 64 (w + 1) ∧
  mh.reg 15 = m.reg 11 + BitVec.ofNat 64 (1 + j) ∧
  mh.reg 13 = BitVec.ofNat 64
    (bigEndian (((bytesOf m (m.reg 11) (m.reg 12).toNat).drop 1).take j)) ∧
  (∀ t < 8, mh.mem (m.reg 2 - 16 + BitVec.ofNat 64 (8 + t)) = some (byteOf (m.reg 1) t)) ∧
  (∀ t < 8, mh.mem (m.reg 2 - 16 + BitVec.ofNat 64 t) = some (byteOf (m.reg 8) t)) ∧
  SameOutside (InRange (m.reg 2 - 16) 16) m mh

/-- The loop-head environment: `var 32 = j`, `var 33` = the caller's `s0`. -/
def envL (m mh : Machine) (j : Nat) : Env :=
  (entryEnv mh ((shape m).map (·.1))).setVars 32
    fun k => if k = 0 then BitVec.ofNat 64 j else m.reg 8

def accSym : Sym := .bin .or (.bin .sll (.var 13) (.lit 8)) (.initx 1 1 (.var 32) 1 1)
def retT : Sym := .bin .and (.var 1) (.lit 18446744073709551614)
def endSym : Sym := .bin .add (.ptr 1 2) (.var 32)

/-- The back edge of a loop run. -/
abbrev BackOK (head : Nat) (l : Leaf) : Prop :=
  l.exit = .at head ∧ l.conds = [.ne endSym (.var 11)] ∧
  l.obligs = [.inBounds 1 1 (.var 32) 1 1] ∧ l.S.steps = 5 ∧ l.S.mem = [] ∧
  l.S.regions = regionsR ∧ l.S.reg 2 = .ptr 0 0 ∧ l.S.reg 8 = .ptr 0 16 ∧
  l.S.reg 10 = .ptr 2 0 ∧ l.S.reg 11 = .var 11 ∧ l.S.reg 14 = .var 14 ∧ l.S.reg 15 = endSym ∧
  l.S.reg 13 = accSym ∧ ∀ i ∈ varRegs, l.S.reg i = .var i

/-- A return of a loop run, with its last condition and outcome view. -/
abbrev ExitOK (l : Leaf) (c : SBool) (v : Nat → Option (Sym × Nat)) : Prop :=
  l.exit = .ret retT ∧ l.conds = [.eq endSym (.var 11), c] ∧
  l.obligs = [.inBounds 1 1 (.var 32) 1 1, .aligned retT 4] ∧ l.S.steps ≤ 17 ∧
  l.S.regions = regionsR ∧ savedOK l.S (.var 33) = true ∧ viewOK l.S.mem v = true

abbrev LoopLeaf (head : Nat) (lst : Bool) (l : Leaf) : Prop :=
  BackOK head l ∨ ExitOK l (.ltu (.var 12) (.bin .add accSym (.var 14))) errView ∨
  ExitOK l (.geu (.var 12) (.bin .add accSym (.var 14)))
    (succView (.var 11) accSym (.lit (if lst then 1 else 0)) (.bin .add accSym (.var 14)))

theorem leavesL1 : ∀ l ∈ runL1_leaves, LoopLeaf loopHead1 false l := by decide
theorem leavesL2 : ∀ l ∈ runL2_leaves, LoopLeaf loopHead2 true l := by decide

theorem envL_var {m mh : Machine} {j : Nat} (i : Fin 32) : (envL m mh j).vars i.val = mh.reg i := by
  simp only [envL, Env.setVars]
  rw [if_neg (by omega)]
  exact entryEnv_var mh _ i

theorem inv_init {m mh : Machine} (hpre : Pre m) {pre head w j : Nat}
    (hI : Inv m pre head w j mh) :
    ∀ r k, r < regionsR.length → k < (envL m mh j).size r →
      mh.mem ((envL m mh j).base r + BitVec.ofNat 64 k) = some ((envL m mh j).byte0 r k) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfra, hfrs, hso⟩ := hI
  have hinp := hpre.2.2.2.2.1
  have hout := hpre.2.2.2.2.2.2.2.1
  intro r k hr hk
  have hb : ∀ x, mh.mem ((envL m mh j).base r + BitVec.ofNat 64 k) = some x →
      mh.mem ((envL m mh j).base r + BitVec.ofNat 64 k) = some ((envL m mh j).byte0 r k) := by
    intro x hx
    rw [hx]
    simp [envL, Env.setVars, Env.byte0, Env.base, entryEnv] at hx ⊢
    simp [hx]
  simp only [regionsR, List.length_cons, List.length_nil] at hr
  have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hr3 with rfl | rfl | rfl
  · have hk : k < 16 := by simpa [envL, Env.setVars, Env.size, entryEnv, shape, shapeOf] using hk
    have hb0 : (envL m mh j).base 0 = m.reg 2 - 16 := by
      simp [envL, Env.setVars, Env.base, entryEnv, shape, shapeOf]
    rw [hb0] at hb ⊢
    by_cases h8 : k < 8
    · exact hb _ (hfrs k h8)
    · have := hfra (k - 8) (by omega)
      rw [show 8 + (k - 8) = k by omega] at this
      exact hb _ this
  · have hk : k < (m.reg 12).toNat := by
      simpa [envL, Env.setVars, Env.size, entryEnv, shape, shapeOf] using hk
    have hb1 : (envL m mh j).base 1 = m.reg 11 := by
      simp [envL, Env.setVars, Env.base, entryEnv, shape, shapeOf]
    rw [hb1] at hb ⊢
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hinp k hk)
    exact hb x (by rw [hso _ (pre_notFrame_in hpre hk)]; exact hx)
  · have hk : k < 40 := by simpa [envL, Env.setVars, Env.size, entryEnv, shape, shapeOf] using hk
    have hb2 : (envL m mh j).base 2 = m.reg 10 := by
      simp [envL, Env.setVars, Env.base, entryEnv, shape, shapeOf]
    rw [hb2] at hb ⊢
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hout k hk)
    exact hb x (by rw [hso _ (pre_notFrame_out hpre hk)]; exact hx)

theorem inv_match {m mh : Machine} (hpre : Pre m) {pre head w j : Nat}
    (hI : Inv m pre head w j mh) : Match (envL m mh j) SL mh := by
  have hinit := inv_init hpre hI
  obtain ⟨-, -, -, -, -, hkeep, h2, h8, -, -, h15, -, hfra, hfrs, -⟩ := hI
  refine entry_match_vars (by decide) (fun i hi s hs => ?_) (fun r k hr hk => ?_)
    (fun kw hkw t ht => ?_)
  · simp only [ovL] at hs
    by_cases e2 : i.val = 2
    · simp [e2] at hs; subst hs
      have : i = 2 := Fin.ext e2
      subst this
      rw [h2]; simp [Sym.eval, Env.setVars, Env.base, entryEnv, shape, shapeOf]
    by_cases e8 : i.val = 8
    · simp [e8] at hs; subst hs
      have : i = 8 := Fin.ext e8
      subst this
      rw [h8]; simp [Sym.eval, Env.setVars, Env.base, entryEnv, shape, shapeOf, BitVec.sub_add_cancel]
    by_cases e10 : i.val = 10
    · simp [e10] at hs; subst hs
      have : i = 10 := Fin.ext e10
      subst this
      rw [hkeep 10 (by decide)]; simp [Sym.eval, Env.setVars, Env.base, entryEnv, shape, shapeOf]
    by_cases e15 : i.val = 15
    · simp [e15] at hs; subst hs
      have : i = 15 := Fin.ext e15
      subst this
      rw [h15]
      simp only [Sym.eval, BinOp.eval, Env.setVars, Env.base, entryEnv, shape, shapeOf]
      simp only [Nat.le_refl, if_true, Nat.sub_self, List.map_cons, List.map_nil, List.getD_cons_succ,
        List.getD_cons_zero]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; omega
    simp [e2, e8, e10, e15] at hs
  · exact Option.isSome_iff_exists.mpr ⟨_, hinit r k hr hk⟩
  · simp only [knownL, List.mem_cons, List.not_mem_nil, or_false] at hkw
    rcases hkw with rfl | rfl
    · have := hfra t ht
      have e1 : mh.reg (Fin.ofNat 32 1) = m.reg 1 := hkeep 1 (by decide)
      simp only [Sym.eval, Env.setVars, Env.byte0, entryEnv, Env.base] at this ⊢
      rw [if_neg (by omega), e1]
      simp [shape, shapeOf] at this ⊢
      simp [this]
    · have := hfrs t ht
      simp only [Sym.eval, Env.setVars, Env.byte0, entryEnv, Env.base] at this ⊢
      simp [shape, shapeOf] at this ⊢
      simp [this]


theorem envL_facts {m mh : Machine} {j : Nat} :
    (envL m mh j).vars 32 = BitVec.ofNat 64 j ∧ (envL m mh j).vars 33 = m.reg 8 ∧
    (envL m mh j).base 0 = m.reg 2 - 16 ∧ (envL m mh j).base 1 = m.reg 11 ∧
    (envL m mh j).base 2 = m.reg 10 ∧ (envL m mh j).size 1 = (m.reg 12).toNat ∧
    (envL m mh j).size 2 = 40 := by
  simp [envL, Env.setVars, Env.base, Env.size, entryEnv, shape, shapeOf]

theorem ptr_eval {env : Env} {r : Nat} {k : Nat} : (Sym.ptr r k).eval env = env.base r + BitVec.ofNat 64 k := by
  simp [Sym.eval]

/-- One trip through a loop head: the back edge re-establishes `Inv` at `j + 1`; the exits
satisfy `Post`. -/
theorem loop_step {m : Machine} (hpre : Pre m) {pre head w j : Nat} {lst : Bool} {ls : List Leaf}
    {mh : Machine} {b : Nat}
    (hrun : run zesuImage [loopHead1, loopHead2] 100 head SL = some ls)
    (hls : ∀ l ∈ ls, LoopLeaf head lst l)
    (hpl : (pre = 183 ∧ lst = false) ∨ (pre = 247 ∧ lst = true))
    (hI : Inv m pre head w j mh) (hb : 17 ≤ b)
    (hnext : j + 1 < w → ∀ mh', Inv m pre head w (j + 1) mh' →
      Reaches zesuImage (b - 5) (Post m) mh') :
    Reaches zesuImage b (Post m) mh := by
  have hinit := inv_init hpre hI
  have hmL := inv_match hpre hI
  have hwfL : Env.WF (envL m mh j) SL := setVars_wf (pre_wf hpre mh ovL knownL) _ _
  have hsp := pre_sp hpre
  have hI' := hI
  obtain ⟨hpc, hjw, hw8, hwl, hfb, hkeep, h2, h8, h11, h14, h15, h13, hfra, hfrs, hso⟩ := hI'
  obtain ⟨hv32, hv33, hb0, hb1, hb2, hs1, hs2⟩ := envL_facts (m := m) (mh := mh) (j := j)
  have hro : RodataLoaded zesuImage mh := fun a v h => by
    rw [hso _ (pre_rodata hpre h)]; exact hpre.1 a v h
  have hv : ∀ i : Fin 32, (envL m mh j).vars i.val = mh.reg i := envL_var
  have hvk : ∀ i : Fin 32, i.val ∈ keepRegs → (envL m mh j).vars i.val = m.reg i :=
    fun i hi => (hv i).trans (hkeep i hi)
  have hv11 : (envL m mh j).vars 11 = m.reg 11 + BitVec.ofNat 64 (w + 1) := (hv 11).trans h11
  have hv14 : (envL m mh j).vars 14 = BitVec.ofNat 64 (w + 1) := (hv 14).trans h14
  have hv12 : (envL m mh j).vars 12 = m.reg 12 := hvk 12 (by decide)
  have hv1 : (envL m mh j).vars 1 = m.reg 1 := hvk 1 (by decide)
  -- length byte `j`
  have hdl : j < ((bytesOf m (m.reg 11) (m.reg 12).toNat).drop 1).length := by
    simp [bytesOf]; omega
  have hbyte : (envL m mh j).byte0 1 (1 + j) =
      ((bytesOf m (m.reg 11) (m.reg 12).toNat).drop 1)[j] := by
    have e := hinit 1 (1 + j) (by decide) (by rw [hs1]; omega)
    rw [hb1, ← hso _ (pre_notFrame_in hpre (by omega))] at e
    rw [bytesOf_drop_getElem _ _ _ _ (by omega), e]
    rfl
  have hacc : accSym.eval (envL m mh j) = BitVec.ofNat 64
      (bigEndian (((bytesOf m (m.reg 11) (m.reg 12).toNat).drop 1).take (j + 1))) := by
    rw [List.take_succ, List.getElem?_eq_getElem hdl, Option.toList_some, bigEndian_append]
    have hlt : bigEndian (((bytesOf m (m.reg 11) (m.reg 12).toNat).drop 1).take j) < 2 ^ 56 := by
      refine Nat.lt_of_lt_of_le (bigEndian_lt _) ?_
      have : (((bytesOf m (m.reg 11) (m.reg 12).toNat).drop 1).take j).length ≤ 7 := by
        simp; omega
      exact Nat.le_trans (Nat.pow_le_pow_right (by decide) this) (by decide)
    simp only [accSym, Sym.eval, BinOp.eval, ofBytes1, hv32, hv 13, h13]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.one_mul, hbyte]
    exact shl_or _ _ hlt
  have hend : endSym.eval (envL m mh j) = m.reg 11 + BitVec.ofNat 64 (j + 2) := by
    simp only [endSym, Sym.eval, BinOp.eval, hb1, hv32]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]; omega
  have hcmp : ∀ k, k ≤ 9 → (m.reg 11 + BitVec.ofNat 64 (j + 2) = m.reg 11 + BitVec.ofNat 64 k ↔
      j + 2 = k) := by
    intro k hk
    constructor
    · intro h
      have := congrArg (fun x => x - m.reg 11) h
      simp only [BitVec.add_sub_cancel_left] at this
      have := congrArg BitVec.toNat this
      simp at this; omega
    · intro h; rw [h]
  have hsp2 : (envL m mh j).base 0 + BitVec.ofInt 64 16 = m.reg 2 := by
    rw [hb0]; simp [BitVec.sub_add_cancel]
  have hrest : ((bytesOf m (m.reg 11) (m.reg 12).toNat).drop 1).length + 1 = (m.reg 12).toNat := by
    simp [bytesOf]; omega
  have hsoL : ∀ m', SameOutside (InWritable (envL m mh j) SL) mh m' →
      SameOutside (fun a => InRange (m.reg 10) 40 a ∨ InRange (m.reg 2 - 16) 16 a) m m' := by
    intro m' hfr a ha
    by_cases hw : InWritable (envL m mh j) SL a
    · exact absurd (pre_writable hpre (mh := mh) (ov := ovL) (ks := knownL) hw) ha
    · rw [hfr a hw]; exact hso a fun h => ha (.inr h)
  have hret : ∀ m' (lS : SState), Match (envL m mh j) lS m' →
      m'.pc = retT.eval (envL m mh j) → savedOK lS (.var 33) = true → Returns m m' :=
    fun m' lS hm' hpc' hok => returns_of hm' hpc' hv1 hok hsp2 hv33 fun i hi => hvk i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false]; omega)
  have hal1 : (retT.eval (envL m mh j)).toNat % 4 = 0 := by
    simpa [retT, Sym.eval, BinOp.eval, notOne, hv1] using hpre.2.2.1
  have hbE : ∀ k < 40, (envL m mh j).byte0 2 k = (bytesOf m (m.reg 10) 40).getD k 0 := by
    intro k hk
    have e := hinit 2 k (by decide) (by rw [hs2]; exact hk)
    rw [hb2, ← hso _ (pre_notFrame_out hpre hk)] at e
    rw [bytesOf_getD _ _ _ _ hk, e]; rfl
  have hhead : firstByte m ≠ 128 := fun h => by
    rw [h] at hfb; rcases hpl with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp at hfb <;> omega
  refine run_reaches hrun hwfL hmL hpc hro fun l hl hc => ?_
  rcases hls l hl with
    ⟨hex, hcs, hob, hst, hmem, hreg, r2, r8, r10, r11, r14, r15, r13, rv⟩ |
    ⟨hex, hcs, hob, hst, hreg, hsv, hview⟩ | ⟨hex, hcs, hob, hst, hreg, hsv, hview⟩
  · -- back edge
    rw [hcs] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, SBool.eval, hend, hv11,
      bne_iff_ne, ne_eq] at hc
    have hne : j + 2 ≠ w + 1 := fun h => hc (by rw [h])
    refine ⟨?_, by rw [hst]; show 5 - 0 ≤ b; omega, fun m' hm' hex' hfr => ?_⟩
    · rw [hob]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, Oblig.holds, Sym.eval, hv32,
        hs1, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]; omega
    · have hm'' : m'.mem = mh.mem := mem_eq_of_nowrite hm' hfr hmem (by rw [hreg]; rfl) hinit
      rw [hst]
      refine hnext (by omega) m' ⟨?_, by omega, hw8, hwl, hfb, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, fun t ht => by rw [hm'']; exact hfra t ht, fun t ht => by rw [hm'']; exact hfrs t ht,
        fun a ha => by rw [hm'']; exact hso a ha⟩
      · rw [hex] at hex'; exact hex'
      · rw [← hm'.regs i, ← hvk i hi]
        simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hi
        by_cases h10 : i.val = 10
        · rw [h10, r10, ptr_eval, hb2]; exact (hv 10).trans (hkeep 10 (by decide)) |>.symm
        · rw [rv i.val (by simp only [varRegs, List.mem_cons, List.not_mem_nil, or_false]; omega)]
          rfl
      · rw [← hm'.regs 2]; show (l.S.reg 2).eval _ = _
        rw [r2]; simp [Sym.eval, hb0]
      · rw [← hm'.regs 8]; show (l.S.reg 8).eval _ = _
        rw [r8]; simp [Sym.eval, hb0, BitVec.sub_add_cancel]
      · rw [← hm'.regs 11]; show (l.S.reg 11).eval _ = _
        rw [r11]; exact hv11
      · rw [← hm'.regs 14]; show (l.S.reg 14).eval _ = _
        rw [r14]; exact hv14
      · rw [← hm'.regs 15]; show (l.S.reg 15).eval _ = _
        rw [r15, hend]; congr 2; omega
      · rw [← hm'.regs 13]; show (l.S.reg 13).eval _ = _
        rw [r13]; exact hacc
  · -- error exit
    rw [hcs] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, SBool.eval,
      hend, hv11, beq_iff_eq] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hjw' : j + 1 = w := by have := (hcmp (w + 1) (by omega)).mp hc1; omega
    simp only [Sym.eval, BinOp.eval, hv12, hv14] at hc2
    rw [show Sym.eval (envL m mh j) (Sym.bin .or (.bin .sll (.var 13) (.lit 8))
      (.initx 1 1 (.var 32) 1 1)) = accSym.eval (envL m mh j) from rfl, hacc] at hc2
    simp [BitVec.ult, BitVec.toNat_add] at hc2
    refine ⟨?_, by rw [hst] at *; show l.S.steps - 0 ≤ b; omega, fun m' hm' hex' hfr => ?_⟩
    · rw [hob]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Oblig.holds, Sym.eval, hv32, hs1, BitVec.toNat_ofNat]
      refine ⟨?_, hal1⟩
      rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]; omega
    · rw [hex] at hex'
      have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .error := by
        rw [input_cons m (by omega), decode_long hpl hfb (by omega) hw8 (by omega), checkedPayload,
          if_neg]
        rw [hrest, ← hjw']
        omega
      exact Reaches.done (post_of (hret m' _ hm' hex' hsv) (hsoL m' hfr)
        (bytes_err hm' (by rw [hreg]; rfl) hb2 hs2 hview hdec))
  · -- success exit
    rw [hcs] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, SBool.eval,
      hend, hv11, beq_iff_eq] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hjw' : j + 1 = w := by have := (hcmp (w + 1) (by omega)).mp hc1; omega
    simp only [Sym.eval, BinOp.eval, hv12, hv14] at hc2
    rw [show Sym.eval (envL m mh j) (Sym.bin .or (.bin .sll (.var 13) (.lit 8))
      (.initx 1 1 (.var 32) 1 1)) = accSym.eval (envL m mh j) from rfl, hacc] at hc2
    simp [BitVec.ult, BitVec.toNat_add] at hc2
    refine ⟨?_, by rw [hst] at *; show l.S.steps - 0 ≤ b; omega, fun m' hm' hex' hfr => ?_⟩
    · rw [hob]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Oblig.holds, Sym.eval, hv32, hs1, BitVec.toNat_ofNat]
      refine ⟨?_, hal1⟩
      rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]; omega
    · rw [hex] at hex'
      have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .success lst (1 + w)
          (bigEndian (((bytesOf m (m.reg 11) (m.reg 12).toNat).drop 1).take (j + 1))) := by
        rw [input_cons m (by omega), decode_long hpl hfb (by omega) hw8 (by omega), checkedPayload,
          if_pos, hjw']
        rw [hrest, ← hjw']
        omega
      refine Reaches.done (post_of (hret m' _ hm' hex' hsv) (hsoL m' hfr)
        (bytes_succ hm' (by rw [hreg]; rfl) hb2 hs2 hview (by cases lst <;> rfl) hbE hdec ?_ hacc ?_))
      · rw [input_head m (by omega)]
        simp only [Sym.eval, hv11, Option.some.injEq, hhead, if_false]
        rw [Nat.add_comm]
      · simp only [Sym.eval, BinOp.eval, hv14]
        rw [show Sym.eval (envL m mh j) (Sym.bin .or (.bin .sll (.var 13) (.lit 8))
          (.initx 1 1 (.var 32) 1 1)) = accSym.eval (envL m mh j) from rfl, hacc]
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]; omega

theorem loop_reaches {m : Machine} (hpre : Pre m) {pre head w : Nat} {lst : Bool}
    {ls : List Leaf} (hrun : run zesuImage [loopHead1, loopHead2] 100 head SL = some ls)
    (hls : ∀ l ∈ ls, LoopLeaf head lst l)
    (hpl : (pre = 183 ∧ lst = false) ∨ (pre = 247 ∧ lst = true)) :
    ∀ μ j mh, j + μ + 1 = w → Inv m pre head w j mh →
      Reaches zesuImage (μ * 5 + 17) (Post m) mh := by
  intro μ
  induction μ with
  | zero =>
    intro j mh hj hI
    exact loop_step hpre hrun hls hpl hI (by omega) fun h => absurd h (by omega)
  | succ μ ih =>
    intro j mh hj hI
    refine loop_step hpre hrun hls hpl hI (by omega) fun _ mh' hI' => ?_
    rw [show (μ + 1) * 5 + 17 - 5 = μ * 5 + 17 by omega]
    exact ih (j + 1) mh' (by omega) hI'

-- MAIN
theorem f2_spec : Spec zesuImage entry bound Pre Post := by
  intro m hpc ⟨hro, ⟨hal, hlo, hhi, hfp⟩, hra, hrd, hinp, hwr, hal8, hout, hd1, hd2, hd3⟩
  have hsp : (m.reg 2 - 16).toNat = (m.reg 2).toNat - 16 := by
    have h16 : (16 : Word).toNat = 16 := rfl
    rw [BitVec.toNat_sub, h16]; unfold Layout.ramLo at hlo; omega
  have hwf : Env.WF (envE m) S0 := by
    refine entry_wf (shape m) ?_ ?_
    · simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl)
      · refine ⟨by simp [frameR], by simp [frameR]; omega, ?_⟩
        simp [frameR, Machine.writable, Machine.inRange]
        simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
      · exact ⟨by simp [inputR], by simp [inputR, Nat.mod_one], by simpa [inputR] using hrd⟩
      · exact ⟨by simp [outR], by simpa [outR] using hal8, by simpa [outR] using hwr⟩
    · unfold Fn.Disjoint at hd1 hd2 hd3
      simp only [hsp] at hd1 hd2 hd3
      simp only [shape, shapeOf, List.map_cons, List.map_nil, List.pairwise_cons,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, Fn.Disjoint, hsp]
      exact ⟨⟨by omega, by omega⟩, by omega, fun _ h => h.elim⟩
  have hm : Match (envE m) S0 m := by
    refine entry_match (fun i hi s hs => ?_) (fun r j hr hj => ?_) (by simp)
    · simp only [ov] at hs
      by_cases h2 : i.val = 2
      · simp only [h2, if_true, Option.some.injEq] at hs
        subst hs
        have : i = 2 := Fin.ext h2
        subst this
        simp [Sym.eval, Env.base, entryEnv, shape, shapeOf, BitVec.sub_add_cancel]
      by_cases h11 : i.val = 11
      · simp [h11] at hs
        subst hs
        have : i = 11 := Fin.ext h11
        subst this
        simp [Sym.eval, Env.base, entryEnv, shape, shapeOf]
      by_cases h10 : i.val = 10
      · simp [h10] at hs
        subst hs
        have : i = 10 := Fin.ext h10
        subst this
        simp [Sym.eval, Env.base, entryEnv, shape, shapeOf]
      simp [h2, h11, h10] at hs
    · simp only [regionsR, List.length_cons, List.length_nil] at hr
      have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
      rcases hr3 with rfl | rfl | rfl
      · exact hfp j (by simpa [Env.size, entryEnv, shape, shapeOf] using hj)
      · exact hinp j (by simpa [Env.size, entryEnv, shape, shapeOf] using hj)
      · exact hout j (by simpa [Env.size, entryEnv, shape, shapeOf] using hj)
  have hfit : ∀ p ∈ shape m, p.1.1.toNat + p.1.2 < 2 ^ 64 := by
    simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false]
    simp [Machine.readable, Machine.writable, Machine.inRange, Layout.rodataLo, Layout.rodataHi,
      Layout.inputLo, Layout.inputHi, Layout.ramLo, Layout.ramHi] at hrd hwr hhi
    rintro p (rfl | rfl | rfl) <;> simp <;> omega
  have hso : ∀ m', SameOutside (InWritable (envE m) S0) m m' →
      SameOutside (fun a => InRange (m.reg 10) 40 a ∨ InRange (m.reg 2 - 16) 16 a) m m' := by
    intro m' hfr
    refine SameOutside.mono hfr fun a ha => ?_
    obtain ⟨p, hp, hw, hin⟩ := inWritable_entry (shape := shape m) ha hfit
    simp only [shape, shapeOf, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact .inr hin
    · simp [inputR] at hw
    · exact .inl hin
  have hvE : ∀ i : Fin 32, i.val ∈ [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
      (envE m).vars i.val = m.reg i := fun i _ => entryEnv_var m _ i
  have hbE : ∀ j < 40, (envE m).byte0 2 j = (bytesOf m (m.reg 10) 40).getD j 0 := fun j hj => by
    rw [bytesOf_getD _ _ _ _ hj]; rfl
  have hb0 : (envE m).byte0 1 0 = firstByte m := by
    simp [envE, entryEnv, Env.byte0, shape, shapeOf, firstByte]
  have hv12 : (envE m).vars 12 = m.reg 12 := rfl
  have hv1 : (envE m).vars 1 = m.reg 1 := rfl
  have hsp2 : (envE m).base 0 + BitVec.ofInt 64 16 = m.reg 2 := by
    simp [Env.base, envE, entryEnv, shape, shapeOf, BitVec.sub_add_cancel]
  have hret : ∀ m' (l : SState), Match (envE m) l m' →
      m'.pc = (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval (envE m) →
      savedOK l (.var 8) = true → Returns m m' := fun m' l hm' hpc hok =>
    returns_of hm' hpc hv1 hok hsp2 rfl hvE
  have hal1 : ((Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval (envE m)).toNat % 4 = 0 := by
    simpa [Sym.eval, BinOp.eval, notOne] using hra
  have hx : (firstByte m).toNat < 256 := (firstByte m).isLt
  have hs1 : (envE m).size 1 = (m.reg 12).toNat := rfl
  have hb2 : (envE m).base 2 = m.reg 10 := by simp [envE, entryEnv, Env.base, shape, shapeOf]
  have hs2 : (envE m).size 2 = 40 := rfl
  have hp1 : ∀ k : Nat, (Sym.ptr 1 k).eval (envE m) = m.reg 11 + BitVec.ofNat 64 k := fun k => by
    simp [Sym.eval, envE, entryEnv, Env.base, shape, shapeOf]
  have hlen : ∀ (l : SState), l.regions = regionsR → l.regions.length = 3 := fun l h => by
    rw [h]; rfl
  refine run_reaches runE hwf hm hpc hro fun l hl hc => ?_
  simp only [runE_leaves, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc
    simp only [SBool.eval] at hc
    try simp only [eval_and_sext_init, eval_sext_init] at hc
    simp only [Sym.eval, BinOp.eval, sext_and_255, sext_slt_zero, ofBytes1, hb0, hv12] at hc
    simp [BitVec.ult, bne, BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_eq,
      Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide : 256 < 2 ^ 64))] at hc
    try simp only [land_255, land_127] at hc
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .error := by
      rw [hc]; rfl
    exact post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_err hm' rfl hb2 hs2 (by decide) hdec)
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .error := by f2_decode
    exact post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_err hm' rfl hb2 hs2 (by decide) hdec)
  case _ => sorry
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .error := by f2_decode
    exact post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_err hm' rfl hb2 hs2 (by decide) hdec)
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .success true 1 ((firstByte m).toNat - 192) := by f2_decode
    refine post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_succ (p := (.ptr 1 1)) (l := (.bin .and (.bin .add (.bin .and (.sext 8 (.init 1 0 1)) (.lit 255)) (.lit 64)) (.lit 255))) (f := (.lit 1)) (c := (.bin .add (.bin .and (.bin .add (.bin .and (.sext 8 (.init 1 0 1)) (.lit 255)) (.lit 64)) (.lit 255)) (.lit 1))) hm' rfl hb2 hs2
        (by decide) rfl hbE hdec ?_ (by f2_word) (by f2_word))
    rw [input_head m (by omega)]
    have : firstByte m ≠ 128 := fun h => by rw [h] at hc; simp at hc
    simp [Sym.eval, envE, entryEnv, Env.base, shape, shapeOf]
    exact fun h => absurd h this
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .error := by f2_decode
    exact post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_err hm' rfl hb2 hs2 (by decide) hdec)
  case _ => sorry
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .error := by f2_decode
    exact post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_err hm' rfl hb2 hs2 (by decide) hdec)
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .success false 1 ((firstByte m).toNat - 128) := by f2_decode
    refine post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_succ (p := (.ptr 1 1)) (l := (.bin .and (.bin .and (.sext 8 (.init 1 0 1)) (.lit 255)) (.lit 127))) (f := (.lit 0)) (c := (.bin .add (.bin .and (.bin .and (.sext 8 (.init 1 0 1)) (.lit 255)) (.lit 127)) (.lit 1))) hm' rfl hb2 hs2
        (by decide) rfl hbE hdec ?_ (by f2_word) (by f2_word))
    rw [input_head m (by omega)]
    have : firstByte m ≠ 128 := fun h => by rw [h] at hc; simp at hc
    simp [Sym.eval, envE, entryEnv, Env.base, shape, shapeOf]
    exact fun h => absurd h this
  case _ =>
    refine ⟨by f2_obligs, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .success false 1 0 := by f2_decode
    refine post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
      (bytes_succ (p := (.lit 1)) (l := (.lit 0)) (f := (.lit 0)) (c := (.lit 1)) hm' rfl hb2 hs2
        (by decide) rfl hbE hdec ?_ (by f2_word) (by f2_word))
    rw [input_head m (by omega)]
    have : firstByte m = 128 := BitVec.eq_of_toNat_eq (by simp; omega)
    simp [this, Sym.eval]
  case _ =>
    obtain ⟨hl0, hx1⟩ := hc
    refine ⟨?_, by decide, fun m' hm' hex hfr => Reaches.done ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        Oblig.holds, hs1]
      exact ⟨by simp [Sym.eval]; omega, hal1⟩
    · have hdec : decode (bytesOf m (m.reg 11) (m.reg 12).toNat) = .success false 0 1 := by
        rw [input_cons m (by omega)]
        simp (disch := omega) only [decode, checkedPayload, if_pos, if_neg]
      refine post_of (hret m' _ hm' hex (by decide)) (hso m' hfr)
        (bytes_succ (p := .ptr 1 0) (l := .lit 1) (f := .lit 0) (c := .lit 1) hm' rfl hb2 hs2
          (by decide) (by simp [Sym.eval]) hbE hdec ?_ rfl rfl)
      rw [input_head m (by omega)]
      have : firstByte m ≠ 128 := fun h => by rw [h] at hx1; simp at hx1
      simp [Sym.eval, envE, entryEnv, Env.base, shape, shapeOf]
      exact fun h => absurd h this
