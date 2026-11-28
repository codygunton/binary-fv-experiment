import ZesuExec.Fn.MergeInPlace.C11564.Vc
import ZesuExec.Fn.Rotate.Cuts

/-!
# `sort.block.mergeInPlace__anon_11564`: cut lemmas and leaves
-/

namespace ZesuExec.Fn.MergeInPlace.C11564

set_option maxRecDepth 8000
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Fn.MergeInPlace
open ZesuExec.Fn.Rotate (revAt rev)

theorem cfg_fs : cfg.fs = 272 := rfl
theorem cfg_key (m : Machine) : cfg.key m = sliceKey m := rfl
theorem ofInt_m16 : BitVec.ofInt 64 (-16) = w 18446744073709551600 := rfl

theorem pre_sl {m : Machine} (h : Pre cfg m) : SlicePre cfg.fs m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hp⟩ := h; exact hp

/-! ## Environments, as `simp` sees them -/

section
variable (mh : Machine) (r x y lo hi : Nat) (i : Nat)
theorem eN_v : (envN mh).vars i = mh.reg (Fin.ofNat 32 i) := rfl
theorem eF_v : (envF cfg mh).vars i = mh.reg (Fin.ofNat 32 i) := rfl
theorem eF_b0 : (envF cfg mh).base 0 = mh.reg 2 := rfl
theorem eP_v : (envP cfg r mh).vars i = mh.reg (Fin.ofNat 32 i) := rfl
theorem eP_b0 : (envP cfg r mh).base 0 = mh.reg 2 := rfl
theorem eP_b1 : (envP cfg r mh).base 1 = mh.reg (Fin.ofNat 32 r) := rfl
theorem eC_v : (envC x y mh).vars i = mh.reg (Fin.ofNat 32 i) := rfl
theorem eC_b0 : (envC x y mh).base 0 = mh.reg (Fin.ofNat 32 x) := rfl
theorem eC_b1 : (envC x y mh).base 1 = mh.reg (Fin.ofNat 32 y) := rfl
theorem eR_v : (envR3 cfg lo hi mh).vars i = mh.reg (Fin.ofNat 32 i) := rfl
theorem eR_b0 : (envR3 cfg lo hi mh).base 0 = mh.reg (Fin.ofNat 32 lo) - w 15 := rfl
theorem eR_b1 : (envR3 cfg lo hi mh).base 1 = mh.reg (Fin.ofNat 32 hi) - w 16 := rfl
theorem eR_b2 : (envR3 cfg lo hi mh).base 2 = mh.reg 2 := rfl
theorem e0_v : (env0 cfg mh).vars i = mh.reg (Fin.ofNat 32 i) := rfl
end

/-! ## Leaf tactics -/

set_option hygiene false in
/-- A word equation or a `Nat` goal through `toNat` and `omega`. -/
macro "wgoal" : tactic => `(tactic| (
  try apply BitVec.eq_of_toNat_eq
  (simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    BitVec.toNat_and, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]) <;> omega))

/-! ## Helpers -/

theorem mask1 (s : Word) : (BitVec.ofNat 64 0 - (1 : Word)) &&& s = s := by
  rw [show BitVec.ofNat 64 0 - (1 : Word) = BitVec.allOnes 64 by decide]; exact BitVec.allOnes_and
theorem mask0 (s : Word) : (BitVec.ofNat 64 0 - (0 : Word)) &&& s = BitVec.ofNat 64 0 := by simp

theorem ult_w {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : (w a).ult (w b) = decide (a < b) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem sliceLen_lt (x : List Byte) : sliceLen x < 2 ^ 64 := (leWord x 8).isLt

theorem Kstep (K s : Nat) (h : 0 < s) : K * (s / 2) + K ≤ K * s := by
  have := Nat.mul_le_mul_left K (show s / 2 + 1 ≤ s by omega)
  rwa [Nat.mul_succ] at this

/-- An element load of an `SP` cut at register `r` (element `e`). -/
theorem iP {m mh : Machine} {G : Nat → Nat → Byte} {r e off : Nat}
    (hr : mh.reg (Fin.ofNat 32 r) = ptr m + w (32 * e)) (hs : Items m mh G) (he : e < bE m)
    (hoff : off + 8 ≤ 32) : (Sym.init 1 off 8).eval (envP cfg r mh) = leWord (el G e) off :=
  init_el hr hs he hoff

/-- All frame offsets but the slot at `0x58`. -/
def kOut : List Nat := List.range 0x58 ++ List.range' 0x60 0xb0

set_option hygiene false in
/-- A symbolic value under the cut's environment: registers by `hR`, loads by `hI`. -/
macro "sevl" : tactic => `(tactic| (
  simp (disch := decide) only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, Sym.eval_ptr, BinOp.eval,
    eN_v, eF_v, eF_b0, eP_v, eP_b0, eP_b1, eC_v, eC_b0, eC_b1, eR_v, eR_b0, eR_b1, eR_b2, e0_v,
    hI, hR, Fin.reduceOfNat, Fin.isValue, ofInt_m16, Rotate.add_big, Rotate.mul_big,
    Rotate.add_neg', Nat.reducePow, Nat.reduceSub, BitVec.ofInt_ofNat, mask0, mask1, ↓reduceIte,
    Bool.false_eq_true]))

set_option hygiene false in
/-- `m'.reg r = v` from the leaf's symbolic value of `r`. -/
macro "rgoal" : tactic => `(tactic| (
  rw [reg_at hm' _]
  simp (disch := decide) only [SState.reg, List.getD_cons_succ, List.getD_cons_zero,
    Nat.reduceEqDiff, if_false]
  sevl))

set_option hygiene false in
macro "regs_tac" : tactic => `(tactic| (
  simp only [eqO, eqF, eqL, List.cons_append, List.nil_append, RegsAre]
  and_intros <;> first | exact True.intro | (rgoal <;> wgoal)))

set_option hygiene false in
/-- The leaf's conditions as `Nat` facts. -/
macro "conds_tac" : tactic => `(tactic| (
  try simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    List.not_mem_nil, false_implies, implies_true, and_true] at hc
  try simp (disch := decide) only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, Sym.eval_ptr, BinOp.eval,
    eN_v, eF_v, eF_b0, eP_v, eP_b0, eP_b1, eC_v, eC_b0, eC_b1, eR_v, eR_b0, eR_b1, eR_b2, e0_v,
    hI, hR, Fin.reduceOfNat, Fin.isValue, ofInt_m16, Rotate.add_big, Rotate.mul_big,
    Rotate.add_neg', Nat.reducePow, Nat.reduceSub, BitVec.ofInt_ofNat,
    BitVec.ult, bne_iff_ne, beq_iff_eq, ne_eq, Bool.not_eq_true, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_eq_true'] at hc
  try simp only [BitVec.toNat_eq] at hc
  try simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    BitVec.toNat_and, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod] at hc
  try simp (disch := omega) only [Nat.mod_eq_of_lt, Rotate.wsub_mod] at hc))

set_option hygiene false in
/-- A budget inequality: the budget definitions unfolded, the registers of the cut's machine
(`hR`), of the leaf's (`hm'`) and the slots (`hQ`) read off, then `omega`. -/
macro "bud" : tactic => `(tactic| (
  try dsimp only
  simp only [bOut, bFv, bF, bFp, bFc, bFn, bFj, bR0, bR1, bS0, bS1, bT0, bT1, bJ, bLv, bL, bLp, bLc,
    bLn, bLj, Q, QS, QL, ROT, LST, Rb, N, ix, bound]
  try simp only [hQ]
  try simp (disch := decide) only [Rotate.reg_of_lt hm']
  try simp (disch := decide) only [SState.reg, List.getD_cons_succ, List.getD_cons_zero,
    Nat.reduceEqDiff, if_false]
  try sevl
  try simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    BitVec.toNat_and, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]
  try simp (disch := omega) only [Nat.mod_eq_of_lt, Rotate.wsub_mod]
  try simp (disch := omega) only [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left, Nat.mul_div_cancel]
  omega))

/-- A keep-list check over slot lists that mention the machine: the offsets are literal. -/
macro "kdec" : tactic => `(tactic| (
  try simp only [baseS, rotS, List.cons_append, List.nil_append, List.all_cons, List.all_nil,
    Bool.and_true]
  decide))

set_option hygiene false in
/-- Name the facts every leaf uses: bounds, `sp`, the registers `hR`. -/
macro "lprep" : tactic => `(tactic| (
  have hfit := pre_hfit hpre
  have hbe := pre_bE hpre
  have hram := pre_items hpre
  have hfr := pre_frame hpre
  have h2 : mh.reg 2 = frame cfg m := hcom.2.1
  have hR := And.intro h2 hr
  simp only [RegsAre, eqO, eqF, eqL, List.cons_append, List.nil_append, Fin.reduceOfNat,
    and_true] at hR
  simp only [cfg_fs, Layout.ramLo, Layout.ramHi] at hram hfr
  have hI : True := trivial
  have hQ : True := trivial))

set_option hygiene false in
/-- `binaryFirst`'s probe `x` (at `a0`) and value `v`: loads, lengths. -/
macro "fpprep" : tactic => `(tactic| (
  have hx10 := hr.get (r := 10) (v := ptr m + w (32 * (curr + size / 2))) (by simp [eqF, eqO])
  have hI : (Sym.init 1 0 8).eval (envP cfg 10 mh) = slicePtr (el G (curr + size / 2)) ∧
      (Sym.init 1 8 8).eval (envP cfg 10 mh) = w (sliceLen (el G (curr + size / 2))) := by
    rw [w_sliceLen]; exact ⟨iP hx10 hs (by omega) (by omega), iP hx10 hs (by omega) (by omega)⟩
  have hlx := sliceLen_lt (el G (curr + size / 2))
  have hlv := sliceLen_lt (el G as)
  have hLx := len_round hpre hRd (e := curr + size / 2) (by omega) (by omega)
  have hLv := len_round hpre hRd (e := as) (by omega) (by omega)))

set_option hygiene false in
/-- `binaryFirst`'s byte comparison: byte `k` of the probe's string (`a1`) and the value's (`a3`). -/
macro "fcprep" : tactic => `(tactic| (
  have hx := strOk_round hpre (pre_sl hpre) hRd (e := curr + size / 2) (by omega) (by omega)
  have hv := strOk_round hpre (pre_sl hpre) hRd (e := as) (by omega) (by omega)
  have b0 := envC_byte0 (x := 11) (y := 13) (r := 0) hpre hcom hx (k := k) (by omega) (by omega)
    (hr.get (r := 11) (v := slicePtr (el G (curr + size / 2)) + w k) (by simp [eqF, eqO]))
  have b1 := envC_byte0 (x := 11) (y := 13) (r := 1) hpre hcom hv (k := k) (by omega) (by omega)
    (hr.get (r := 13) (v := slicePtr (el G as) + w k) (by simp [eqF, eqO]))
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, Sym.eval_lit, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  have hlx := sliceLen_lt (el G (curr + size / 2))
  have hlv := sliceLen_lt (el G as)
  have hLx := len_round hpre hRd (e := curr + size / 2) (by omega) (by omega)
  have hLv := len_round hpre hRd (e := as) (by omega) (by omega)))

set_option hygiene false in
/-- `binaryLast`'s probe `x` (at `a0`) and value `v`. -/
macro "lpprep" : tactic => `(tactic| (
  have hx10 := hr.get (r := 10) (v := ptr m + w (32 * (curr + size / 2))) (by simp [eqL])
  have hI : (Sym.init 1 0 8).eval (envP cfg 10 mh) = slicePtr (el G (curr + size / 2)) ∧
      (Sym.init 1 8 8).eval (envP cfg 10 mh) = w (sliceLen (el G (curr + size / 2))) := by
    rw [w_sliceLen]; exact ⟨iP hx10 hs (by omega) (by omega), iP hx10 hs (by omega) (by omega)⟩
  have hlx := sliceLen_lt (el G (curr + size / 2))
  have hlv := sliceLen_lt (el G as)
  have hLx := len_round hpre hRd (e := curr + size / 2) (by omega) (by omega)
  have hLv := len_round hpre hRd (e := as) (by omega) (by omega)))

set_option hygiene false in
/-- `binaryLast`'s byte comparison: byte `k` of the value's string (`a3`) and the probe's (`a1`). -/
macro "lcprep" : tactic => `(tactic| (
  have hx := strOk_round hpre (pre_sl hpre) hRd (e := curr + size / 2) (by omega) (by omega)
  have hv := strOk_round hpre (pre_sl hpre) hRd (e := as) (by omega) (by omega)
  have b0 := envC_byte0 (x := 13) (y := 11) (r := 0) hpre hcom hv (k := k) (by omega) (by omega)
    (hr.get (r := 13) (v := slicePtr (el G as) + w k) (by simp [eqL]))
  have b1 := envC_byte0 (x := 13) (y := 11) (r := 1) hpre hcom hx (k := k) (by omega) (by omega)
    (hr.get (r := 11) (v := slicePtr (el G (curr + size / 2)) + w k) (by simp [eqL]))
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, Sym.eval_lit, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq,
    bne_iff_ne, ne_eq, byte_word_eq] at hc
  have hlx := sliceLen_lt (el G (curr + size / 2))
  have hlv := sliceLen_lt (el G as)
  have hLx := len_round hpre hRd (e := curr + size / 2) (by omega) (by omega)
  have hLv := len_round hpre hRd (e := as) (by omega) (by omega)))

theorem sl_same {m mh m' : Machine} (hc : Common cfg m mh) (hc' : Common cfg m m')
    (hall : ∀ a, m'.mem a = mh.mem a) (off : Nat) : sl m' off = sl mh off := by
  unfold sl u64; rw [hc'.2.1, hc.2.1]; simp only [hall]

theorem AsL.same {m mh m' : Machine} {as : Nat} (hc : Common cfg m mh) (hc' : Common cfg m m')
    (hall : ∀ a, m'.mem a = mh.mem a) (h : AsL mh as) : AsL m' as := by
  unfold AsL at *; rw [sl_same hc hc' hall, sl_same hc hc' hall, sl_same hc hc' hall]; exact h

theorem sl_of {m m' : Machine} {off : Nat} {v : Word} (hc : Common cfg m m')
    (hv : FrameU64 m' (f m) off v) : sl m' off = v.toNat := by
  unfold sl; rw [hc.2.1]; exact u64_frame hv

/-- The frame offsets the rotation's first leaf leaves alone (it writes `0x30 … 0x57`, `0x60`). -/
def kR0 : List Nat := List.range 0x30 ++ List.range' 0x58 8 ++ List.range' 0x68 0xa8
/-- …the second reversal's first leaf (it writes `0x28`, `0x38`, `0x60`). -/
def kS0 : List Nat :=
  List.range 0x28 ++ List.range' 0x30 8 ++ List.range' 0x40 0x20 ++ List.range' 0x68 0xa8
/-- …a swap of the first two reversals (it spills to `0x68 … 0xa7`). -/
def kSw : List Nat := List.range' 8 0x20 ++ List.range' 0x28 0x40 ++ List.range' 0xa8 0x68
/-- …a swap of the third reversal (it spills to `0x60 … 0xa7`). -/
def kT : List Nat := List.range' 8 0x20 ++ List.range' 0x28 0x38 ++ List.range' 0xa8 0x68

set_option hygiene false in
/-- A slot an `SF` leaf writes with the value `v` (registers `hR`, loads `hI`). -/
macro "slotF" v:term : tactic => `(tactic| exact slot_at hm' (r := 0) (v := $v) (by decide)
    (by simp [envF, entryEnv, Env.size, cfg_fs]) (by decide) (by rw [eF_b0, h2]) (by sevl <;> wgoal))

/-! ## Cut points -/

theorem R11564.cut_80098ddc : CutOK R11564.plan R11564.plan.cuts[0]! := by
  cut_intro; rintro m mh ⟨rfl, hpc, hpre⟩
  exact ⟨(cut0_facts hpre).1, (cut0_facts hpre).2, hpre.1, hpc⟩

theorem R11564.cut_80098ea8 : CutOK R11564.plan R11564.plan.cuts[3]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom, -⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩
theorem R11564.cut_80098e8c : CutOK R11564.plan R11564.plan.cuts[4]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom, -⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩
theorem R11564.cut_80098ea4 : CutOK R11564.plan R11564.plan.cuts[5]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom, -⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩
theorem R11564.cut_8009968c : CutOK R11564.plan R11564.plan.cuts[16]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom, -⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩
theorem R11564.cut_800996f8 : CutOK R11564.plan R11564.plan.cuts[17]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom, -⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩
theorem R11564.cut_80099688 : CutOK R11564.plan R11564.plan.cuts[18]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom, -⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩

theorem R11564.cut_80098e60 : CutOK R11564.plan R11564.plan.cuts[1]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, -⟩
  exact ⟨(cutF_facts hpre hcom).1, (cutF_facts hpre hcom).2, hcom.1, hpc⟩
theorem R11564.cut_80098f2c : CutOK R11564.plan R11564.plan.cuts[8]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, -⟩
  exact ⟨(cutF_facts hpre hcom).1, (cutF_facts hpre hcom).2, hcom.1, hpc⟩
theorem R11564.cut_80099188 : CutOK R11564.plan R11564.plan.cuts[10]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, -⟩
  exact ⟨(cutF_facts hpre hcom).1, (cutF_facts hpre hcom).2, hcom.1, hpc⟩
theorem R11564.cut_800993e8 : CutOK R11564.plan R11564.plan.cuts[12]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, -⟩
  exact ⟨(cutF_facts hpre hcom).1, (cutF_facts hpre hcom).2, hcom.1, hpc⟩
theorem R11564.cut_80099634 : CutOK R11564.plan R11564.plan.cuts[14]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, -⟩
  exact ⟨(cutF_facts hpre hcom).1, (cutF_facts hpre hcom).2, hcom.1, hpc⟩

theorem R11564.cut_80098e78 : CutOK R11564.plan R11564.plan.cuts[2]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, G, as, ae, hs, ⟨-, -, h3, -⟩, has, hae, -, hr⟩
  have h := cutP_facts (extra := []) hpre hcom hs (show as < bE m by omega)
    (hr.get (r := 11) (v := ptr m + w (32 * as)) (by simp [eqO])) (by simp)
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R11564.cut_80099668 : CutOK R11564.plan R11564.plan.cuts[15]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, G, as, ae, hs, ⟨⟨-, has, -⟩, hlt, -⟩, hae, -, hr⟩
  have h := cutP_facts (extra := []) hpre hcom hs (show as < bE m by omega)
    (hr.get (r := 11) (v := ptr m + w (32 * as)) (by simp)) (by simp)
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R11564.cut_80098ec0 : CutOK R11564.plan R11564.plan.cuts[6]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, G, as, ae, curr, size, hs, ⟨-, -, hf⟩, hsz, -, hr⟩
  have h := cutP_facts (extra := []) hpre hcom hs
    (show curr + size / 2 < bE m by have := hf.2.1; omega)
    (hr.get (r := 10) (v := ptr m + w (32 * (curr + size / 2))) (by simp [eqF, eqO])) (by simp)
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R11564.cut_800996a4 : CutOK R11564.plan R11564.plan.cuts[19]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, G, as, ae, curr, size, hs, ⟨-, hlt, hl⟩, hsz, -, hr⟩
  have h := cutP_facts (extra := []) hpre hcom hs
    (show curr + size / 2 < bE m by have := hl.2.1; omega)
    (hr.get (r := 10) (v := ptr m + w (32 * (curr + size / 2))) (by simp [eqL])) (by simp)
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R11564.cut_80098ee0 : CutOK R11564.plan R11564.plan.cuts[7]! := by
  cut_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, G, as, ae, curr, size, k, hs, ⟨hRd, has, hf⟩, hsz, -, hk, hne, -, hr⟩
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  have hx := strOk_round hpre (pre_sl hpre) hRd (e := curr + size / 2) (by omega) (by omega)
  have hv := strOk_round hpre (pre_sl hpre) hRd (e := as) (by omega) (by omega)
  have h := cutCS_facts (a := 11) (b := 13) hpre hcom hx hv (by omega) (by omega) hne
    (hr.get (r := 11) (v := slicePtr (el G (curr + size / 2)) + w k) (by simp [eqF, eqO]))
    (hr.get (r := 13) (v := slicePtr (el G as) + w k) (by simp [eqF, eqO]))
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R11564.cut_800996c4 : CutOK R11564.plan R11564.plan.cuts[20]! := by
  cut_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, G, as, ae, curr, size, k, hs, ⟨hJ, hlt, hl⟩, hsz, -, hk, hne, -, hr⟩
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have hx := strOk_round hpre (pre_sl hpre) hJ.1 (e := curr + size / 2) (by omega) (by omega)
  have hv := strOk_round hpre (pre_sl hpre) hJ.1 (e := as) (by omega) (by omega)
  have h := cutCS_facts (a := 13) (b := 11) hpre hcom hv hx (by omega) (by omega) hne
    (hr.get (r := 13) (v := slicePtr (el G as) + w k) (by simp [eqL]))
    (hr.get (r := 11) (v := slicePtr (el G (curr + size / 2)) + w k) (by simp [eqL]))
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R11564.cut_80098f78 : CutOK R11564.plan R11564.plan.cuts[9]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, G, as, ae, mid, i, hs, ⟨⟨-, -, h3, -⟩, -⟩, hi, -, hr⟩
  have h := cutR3_facts hpre hcom hs (e₁ := as + i) (e₂ := ae - 1 - i) (by omega) (by omega) (by omega)
    (hr.get (r := 28) (v := ptr m + w (32 * (as + i) + 15)) (by simp))
    (hr.get (r := 29) (v := ptr m + w (32 * (ae - 1 - i) + 16)) (by simp))
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R11564.cut_800991d8 : CutOK R11564.plan R11564.plan.cuts[11]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, G, as, ae, mid, i, hs, ⟨-, -, hf⟩, hi, -, hr⟩
  have := hf.2.1
  have h := cutR3_facts hpre hcom hs (e₁ := ae + i) (e₂ := mid - 1 - i) (by omega) (by omega) (by omega)
    (hr.get (r := 29) (v := ptr m + w (32 * (ae + i) + 15)) (by simp))
    (hr.get (r := 30) (v := ptr m + w (32 * (mid - 1 - i) + 16)) (by simp))
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R11564.cut_8009941c : CutOK R11564.plan R11564.plan.cuts[13]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom, -⟩, G, as, ae, mid, i, hs, ⟨-, -, hf⟩, hi, -, hr⟩
  have := hf.2.1
  have h := cutR3_facts hpre hcom hs (e₁ := as + i) (e₂ := mid - 1 - i) (by omega) (by omega) (by omega)
    (hr.get (r := 6) (v := ptr m + w (32 * (as + i) + 15)) (by simp))
    (hr.get (r := 7) (v := ptr m + w (32 * (mid - 1 - i) + 16)) (by simp))
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R11564.cut_80099708 : CutOK R11564.plan R11564.plan.cuts[21]! := by
  cut_intro; rintro m mh ⟨hpre, hpc, hcom, -⟩
  exact ⟨(cutE_facts hpre hcom).1, (cutE_facts hpre hcom).2, hcom.1, hpc⟩

/-! ## Outer loop head -/

theorem R11564.leaf_80098e60_0 : LeafGoal R11564.plan R11564.plan.cuts[1]! (R11564.plan.leaves 0x80098e60)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, hs, hRd, has, hr⟩ hc
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  lprep
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_frame (keep := kOut) hpre hcom hs hm' hso rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h58 : FrameU64 m' (f m) 0x58 (w (32 * as)) := slot_at hm' (r := 0)
    (v := .bin .sll (.var 9) (.lit 5)) (by decide)
    (by simp [envF, entryEnv, Env.size, cfg_fs]) (by decide) (by rw [eF_b0, h2]) (by sevl; wgoal)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, bE m, hst.2.1,
      ⟨hRd, has, first_empty (by omega)⟩, ⟨h58, trivial⟩, by regs_tac⟩
  · bud

theorem R11564.leaf_80098e60_1 : LeafGoal R11564.plan R11564.plan.cuts[1]! (R11564.plan.leaves 0x80098e60)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, hs, hRd, has, hr⟩ hc
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  lprep
  conds_tac
  have hKN := Nat.mul_le_mul_left (K m) (show bE m - ae ≤ bE m - aS m by omega)
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_frame (keep := kOut) hpre hcom hs hm' hso rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h58 : FrameU64 m' (f m) 0x58 (w (32 * as)) := slot_at hm' (r := 0)
    (v := .bin .sll (.var 9) (.lit 5)) (by decide)
    (by simp [envF, entryEnv, Env.size, cfg_fs]) (by decide) (by rw [eF_b0, h2]) (by sevl; wgoal)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, hst.2.1, hRd, has, by omega,
      ⟨h58, trivial⟩, by regs_tac⟩
  · bud

/-! ## `binaryFirst`: the value, the head, the latch, the length comparison -/

theorem R11564.leaf_80098e78_0 : LeafGoal R11564.plan R11564.plan.cuts[2]! (R11564.plan.leaves 0x80098e78)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, hs, hRd, has, hae, hsl, hr⟩ hc
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  lprep
  have hI : (Sym.init 1 0 8).eval (envP cfg 11 mh) = slicePtr (el G as) ∧
      (Sym.init 1 8 8).eval (envP cfg 11 mh) = w (sliceLen (el G as)) := by
    have h11 := hr.get (r := 11) (v := ptr m + w (32 * as)) (by simp [eqO])
    rw [w_sliceLen]
    exact ⟨iP h11 hs (by omega) (by omega), iP h11 hs (by omega) (by omega)⟩
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roP (extra := []) hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, ae, bE m - ae, items_keep hs hst.2,
      ⟨hRd, has, first_init (by omega)⟩, by omega, hsl.same hst.2, by regs_tac⟩
  · bud

theorem R11564.leaf_80098ea8_0 : LeafGoal R11564.plan R11564.plan.cuts[3]! (R11564.plan.leaves 0x80098ea8)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, hFS, hsz, hsl, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hFS
  lprep
  have hk := Kstep (K m) size hsz
  have hK : K m = 11 * Lmax m + 64 := rfl
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_N) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2, hFS, hsz,
      hsl.same hst.2, by regs_tac⟩
  · bud

theorem R11564.leaf_80098ea4_0 : LeafGoal R11564.plan R11564.plan.cuts[5]! (R11564.plan.leaves 0x80098ea4)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, ⟨hRd, has, hf⟩, hsz, hsl, hr⟩ hc
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_N) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · rw [show size / 2 = 0 by omega] at hf
    exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, items_keep hs hst.2, ⟨hRd, has, hf⟩,
      hsl.same hst.2, by regs_tac⟩
  · bud

theorem R11564.leaf_80098ea4_1 : LeafGoal R11564.plan R11564.plan.cuts[5]! (R11564.plan.leaves 0x80098ea4)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, ⟨hRd, has, hf⟩, hsz, hsl, hr⟩ hc
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_N) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size / 2, items_keep hs hst.2,
      ⟨hRd, has, hf⟩, by omega, hsl.same hst.2, by regs_tac⟩
  · bud

theorem R11564.leaf_80098e8c_0 : LeafGoal R11564.plan R11564.plan.cuts[4]! (R11564.plan.leaves 0x80098e8c)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, ⟨hRd, has, hf⟩, hsz, hsl, hp, hr⟩ hc
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  have hlb : ltBy (cfg.key m) (el G (curr + size / 2)) (el G as) =
      decide (sliceLen (el G (curr + size / 2)) < sliceLen (el G as)) := by
    rw [cfg_key]; exact ltBy_slice_eq m hp
  have hf' := first_step (round_sortedB hRd) hf hsz
  rw [hlb] at hf'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_N) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · have hu := ult_w (sliceLen_lt (el G (curr + size / 2))) (sliceLen_lt (el G as))
    cases hlt : decide (sliceLen (el G (curr + size / 2)) < sliceLen (el G as))
    · simp only [hlt, Bool.false_eq_true, if_false] at hf'
      have hI := And.intro hu hlt
      exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2,
        ⟨hRd, has, hf'⟩, hsz, hsl.same hst.2, by regs_tac⟩
    · simp only [hlt, if_true] at hf'
      have hI := And.intro hu hlt
      exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr + size % 2 + size / 2, size,
        items_keep hs hst.2, ⟨hRd, has, hf'⟩, hsz, hsl.same hst.2, by regs_tac⟩
  · bud

/-! ## `binaryFirst`: the probe -/

theorem R11564.leaf_80098ec0_0 : LeafGoal R11564.plan R11564.plan.cuts[6]! (R11564.plan.leaves 0x80098ec0)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, hFS, hsz, hsl, hr⟩ hc
  obtain ⟨hRd, has, hf⟩ := id hFS
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  fpprep
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roP (extra := []) hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2, hFS, hsz,
      hsl.same hst.2, fun j _ => by rw [BitVec.eq_of_toNat_eq hc], by regs_tac⟩
  · bud

theorem R11564.leaf_80098ec0_1 : LeafGoal R11564.plan R11564.plan.cuts[6]! (R11564.plan.leaves 0x80098ec0)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, hFS, hsz, hsl, hr⟩ hc
  obtain ⟨hRd, has, hf⟩ := id hFS
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  fpprep
  conds_tac
  obtain ⟨c1, c2, c3⟩ := hc
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roP (extra := []) hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2, hFS, hsz,
      hsl.same hst.2, fun j hj => absurd hj (by omega), by regs_tac⟩
  · bud

theorem R11564.leaf_80098ec0_2 : LeafGoal R11564.plan R11564.plan.cuts[6]! (R11564.plan.leaves 0x80098ec0)[2]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, hFS, hsz, hsl, hr⟩ hc
  obtain ⟨hRd, has, hf⟩ := id hFS
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  fpprep
  conds_tac
  obtain ⟨c1, c2, c3⟩ := hc
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roP (extra := []) hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, 0, items_keep hs hst.2, hFS, hsz,
      hsl.same hst.2, by omega, fun h => c1 (congrArg BitVec.toNat h), fun j hj => absurd hj (by omega),
      by regs_tac⟩
  · bud

theorem R11564.leaf_80098ec0_3 : LeafGoal R11564.plan R11564.plan.cuts[6]! (R11564.plan.leaves 0x80098ec0)[3]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, hFS, hsz, hsl, hr⟩ hc
  obtain ⟨hRd, has, hf⟩ := id hFS
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  fpprep
  conds_tac
  obtain ⟨c1, c2, c3⟩ := hc
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roP (extra := []) hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2, hFS, hsz,
      hsl.same hst.2, fun j hj => absurd hj (by omega), by regs_tac⟩
  · bud

theorem R11564.leaf_80098ec0_4 : LeafGoal R11564.plan R11564.plan.cuts[6]! (R11564.plan.leaves 0x80098ec0)[4]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, hFS, hsz, hsl, hr⟩ hc
  obtain ⟨hRd, has, hf⟩ := id hFS
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  fpprep
  conds_tac
  obtain ⟨c1, c2, c3⟩ := hc
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roP (extra := []) hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, 0, items_keep hs hst.2, hFS, hsz,
      hsl.same hst.2, by omega, fun h => c1 (congrArg BitVec.toNat h), fun j hj => absurd hj (by omega),
      by regs_tac⟩
  · bud

/-! ## `binaryFirst`: the byte comparison (probe's string at `a1`, value's at `a3`) -/

theorem R11564.leaf_80098ee0_0 : LeafGoal R11564.plan R11564.plan.cuts[7]! (R11564.plan.leaves 0x80098ee0)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, k, hs, hFS, hsz, hsl, hk, hne, hp, hr⟩ hc
  obtain ⟨hRd, has, hf⟩ := id hFS
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  fcprep
  have hbn : strByte m (slicePtr (el G (curr + size / 2))) k ≠ strByte m (slicePtr (el G as)) k :=
    fun h => by simp [h] at hc
  have hnlt : ¬ (strByte m (slicePtr (el G (curr + size / 2))) k).toNat <
      (strByte m (slicePtr (el G as)) k).toNat := fun h => by simp [h] at hc
  have hlb : ltBy (cfg.key m) (el G (curr + size / 2)) (el G as) = false := by
    rw [cfg_key, ltBy_slice_ne m (by omega) (by omega) hp hbn]; simpa using hnlt
  have hf' := first_step (round_sortedB hRd) hf hsz
  rw [hlb] at hf'; simp only [Bool.false_eq_true, if_false] at hf'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2,
      ⟨hRd, has, hf'⟩, hsz, hsl.same hst.2, by regs_tac⟩
  · bud

theorem R11564.leaf_80098ee0_1 : LeafGoal R11564.plan R11564.plan.cuts[7]! (R11564.plan.leaves 0x80098ee0)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, k, hs, hFS, hsz, hsl, hk, hne, hp, hr⟩ hc
  obtain ⟨hRd, has, hf⟩ := id hFS
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  fcprep
  have hbn : strByte m (slicePtr (el G (curr + size / 2))) k ≠ strByte m (slicePtr (el G as)) k :=
    fun h => by simp [h] at hc
  have hlt : (strByte m (slicePtr (el G (curr + size / 2))) k).toNat <
      (strByte m (slicePtr (el G as)) k).toNat := Classical.byContradiction fun h => by simp [h] at hc
  have hlb : ltBy (cfg.key m) (el G (curr + size / 2)) (el G as) = true := by
    rw [cfg_key, ltBy_slice_ne m (by omega) (by omega) hp hbn]; simpa using hlt
  have hf' := first_step (round_sortedB hRd) hf hsz
  rw [hlb] at hf'; simp only [if_true] at hf'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr + size % 2 + size / 2, size,
      items_keep hs hst.2, ⟨hRd, has, hf'⟩, hsz, hsl.same hst.2, by regs_tac⟩
  · bud

theorem R11564.leaf_80098ee0_2 : LeafGoal R11564.plan R11564.plan.cuts[7]! (R11564.plan.leaves 0x80098ee0)[2]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, k, hs, hFS, hsz, hsl, hk, hne, hp, hr⟩ hc
  obtain ⟨hRd, has, hf⟩ := id hFS
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  fcprep
  exfalso
  by_cases h : (strByte m (slicePtr (el G (curr + size / 2))) k).toNat <
    (strByte m (slicePtr (el G as)) k).toNat <;> simp [h] at hc

theorem R11564.leaf_80098ee0_3 : LeafGoal R11564.plan R11564.plan.cuts[7]! (R11564.plan.leaves 0x80098ee0)[3]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, k, hs, hFS, hsz, hsl, hk, hne, hp, hr⟩ hc
  obtain ⟨hRd, has, hf⟩ := id hFS
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  fcprep
  exfalso
  by_cases h : (strByte m (slicePtr (el G (curr + size / 2))) k).toNat <
    (strByte m (slicePtr (el G as)) k).toNat <;> simp [h] at hc

theorem R11564.leaf_80098ee0_4 : LeafGoal R11564.plan R11564.plan.cuts[7]! (R11564.plan.leaves 0x80098ee0)[4]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, k, hs, hFS, hsz, hsl, hk, hne, hp, hr⟩ hc
  obtain ⟨hRd, has, hf⟩ := id hFS
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  fcprep
  obtain ⟨hab, c2⟩ := hc
  have hc := c2
  conds_tac
  have hp' : PreEq m (el G (curr + size / 2)) (el G as) (k + 1) := fun j hj => by
    rcases Nat.lt_or_ge j k with h | h
    · exact hp j h
    · rw [show j = k by omega]; exact hab
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, k + 1, items_keep hs hst.2, hFS,
      hsz, hsl.same hst.2, by omega, hne, hp', by regs_tac⟩
  · bud

theorem R11564.leaf_80098ee0_5 : LeafGoal R11564.plan R11564.plan.cuts[7]! (R11564.plan.leaves 0x80098ee0)[5]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, k, hs, hFS, hsz, hsl, hk, hne, hp, hr⟩ hc
  obtain ⟨hRd, has, hf⟩ := id hFS
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  fcprep
  obtain ⟨hab, c2⟩ := hc
  have hc := c2
  conds_tac
  have hp' : PreEq m (el G (curr + size / 2)) (el G as)
      (min (sliceLen (el G (curr + size / 2))) (sliceLen (el G as))) := fun j hj => by
    rcases Nat.lt_or_ge j k with h | h
    · exact hp j h
    · rw [show j = k by omega]; exact hab
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2, hFS, hsz,
      hsl.same hst.2, hp', by regs_tac⟩
  · bud

/-! ## `binaryLast`: the value, the head, the latch, the length comparison -/

theorem R11564.leaf_80099668_0 : LeafGoal R11564.plan R11564.plan.cuts[15]! (R11564.plan.leaves 0x80099668)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, hs, hJ, hlt, hA, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  lprep
  have hI : (Sym.init 1 0 8).eval (envP cfg 11 mh) = slicePtr (el G as) ∧
      (Sym.init 1 8 8).eval (envP cfg 11 mh) = w (sliceLen (el G as)) := by
    have h11 := hr.get (r := 11) (v := ptr m + w (32 * as)) (by simp)
    rw [w_sliceLen]
    exact ⟨iP h11 hs (by omega) (by omega), iP h11 hs (by omega) (by omega)⟩
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roP (extra := []) hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, as, ae - as, items_keep hs hst.2,
      ⟨hJ, hlt, last_init (by omega)⟩, by omega, hA.same hcom hst.1 hst.2, by regs_tac⟩
  · bud

theorem R11564.leaf_8009968c_0 : LeafGoal R11564.plan R11564.plan.cuts[16]! (R11564.plan.leaves 0x8009968c)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, hLS, hsz, hA, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  lprep
  have hk := Kstep (K m) size hsz
  have hK : K m = 11 * Lmax m + 64 := rfl
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_N) hm' (entryEnv_vars_lt _ _) hso (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2, hLS, hsz,
      hA.same hcom hst.1 hst.2, by regs_tac⟩
  · bud

theorem R11564.leaf_80099688_2 : LeafGoal R11564.plan R11564.plan.cuts[18]! (R11564.plan.leaves 0x80099688)[2]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, ⟨hJ, hlt, hl⟩, hsz, hA, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  lprep
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_N) hm' (entryEnv_vars_lt _ _) hso (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size / 2, items_keep hs hst.2,
      ⟨hJ, hlt, hl⟩, by omega, hA.same hcom hst.1 hst.2, by regs_tac⟩
  · bud

theorem R11564.leaf_80099688_0 : LeafGoal R11564.plan R11564.plan.cuts[18]! (R11564.plan.leaves 0x80099688)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, ⟨hJ, hlt, hl⟩, hsz, hA, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  lprep
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_N) hm' (entryEnv_vars_lt _ _) hso (by decide)
  rw [show size / 2 = 0 by omega] at hl
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · have hR' := round_of_last hJ hl hlt
    exact ⟨hpre, he, hst.1, G, items_keep hs hst.2, round_done hR' (.inl (by omega))⟩
  · bud

theorem R11564.leaf_80099688_1 : LeafGoal R11564.plan R11564.plan.cuts[18]! (R11564.plan.leaves 0x80099688)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, ⟨hJ, hlt, hl⟩, hsz, hA, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  lprep
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_N) hm' (entryEnv_vars_lt _ _) hso (by decide)
  rw [show size / 2 = 0 by omega] at hl
  have hc1 := last_curr hl has
  have hQ : sl mh 0x48 - sl mh 0x30 + sl mh 0x50 = as := hA
  have hq := Qf_step (be := bE m) (R := Rb m) hc1 (show curr < bE m by omega)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, curr, ae, items_keep hs hst.2,
      round_of_last hJ hl hlt, by omega, by regs_tac⟩
  · simp only [Rb, ROT, LST, N] at hq
    bud

theorem R11564.leaf_800996f8_0 : LeafGoal R11564.plan R11564.plan.cuts[17]! (R11564.plan.leaves 0x800996f8)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, ⟨hJ, hlt, hl⟩, hsz, hA, hp, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  lprep
  have hlx := sliceLen_lt (el G (curr + size / 2))
  have hlv := sliceLen_lt (el G as)
  conds_tac
  have hlb : ltBy (cfg.key m) (el G as) (el G (curr + size / 2)) = false := by
    rw [cfg_key, ltBy_slice_eq m hp]; simp; omega
  have hl' := last_step (round_sortedA hJ.1) hl hsz
  rw [hlb] at hl'; simp only [Bool.false_eq_true, if_false] at hl'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_N) hm' (entryEnv_vars_lt _ _) hso (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr + size % 2 + size / 2, size,
      items_keep hs hst.2, ⟨hJ, hlt, hl'⟩, hsz, hA.same hcom hst.1 hst.2, by regs_tac⟩
  · bud

theorem R11564.leaf_800996f8_1 : LeafGoal R11564.plan R11564.plan.cuts[17]! (R11564.plan.leaves 0x800996f8)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, ⟨hJ, hlt, hl⟩, hsz, hA, hp, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  lprep
  have hlx := sliceLen_lt (el G (curr + size / 2))
  have hlv := sliceLen_lt (el G as)
  conds_tac
  have hlb : ltBy (cfg.key m) (el G as) (el G (curr + size / 2)) = true := by
    rw [cfg_key, ltBy_slice_eq m hp]; simp; omega
  have hl' := last_step (round_sortedA hJ.1) hl hsz
  rw [hlb] at hl'; simp only [if_true] at hl'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_N) hm' (entryEnv_vars_lt _ _) hso (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2,
      ⟨hJ, hlt, hl'⟩, hsz, hA.same hcom hst.1 hst.2, by regs_tac⟩
  · bud

/-! ## `binaryLast`: the probe -/

theorem R11564.leaf_800996a4_0 : LeafGoal R11564.plan R11564.plan.cuts[19]! (R11564.plan.leaves 0x800996a4)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, hLS, hsz, hA, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have hRd := hJ.1
  lprep
  lpprep
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roP (extra := []) hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2, hLS, hsz,
      hA.same hcom hst.1 hst.2, fun j _ => by rw [BitVec.eq_of_toNat_eq hc], by regs_tac⟩
  · bud

theorem R11564.leaf_800996a4_1 : LeafGoal R11564.plan R11564.plan.cuts[19]! (R11564.plan.leaves 0x800996a4)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, hLS, hsz, hA, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have hRd := hJ.1
  lprep
  lpprep
  conds_tac
  obtain ⟨c1, c2, c3⟩ := hc
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roP (extra := []) hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2, hLS, hsz,
      hA.same hcom hst.1 hst.2, fun j hj => absurd hj (by omega), by regs_tac⟩
  · bud

theorem R11564.leaf_800996a4_2 : LeafGoal R11564.plan R11564.plan.cuts[19]! (R11564.plan.leaves 0x800996a4)[2]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, hLS, hsz, hA, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have hRd := hJ.1
  lprep
  lpprep
  conds_tac
  obtain ⟨c1, c2, c3⟩ := hc
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roP (extra := []) hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, 0, items_keep hs hst.2, hLS, hsz,
      hA.same hcom hst.1 hst.2, by omega, fun h => c1 (congrArg BitVec.toNat h),
      fun j hj => absurd hj (by omega), by regs_tac⟩
  · bud

theorem R11564.leaf_800996a4_3 : LeafGoal R11564.plan R11564.plan.cuts[19]! (R11564.plan.leaves 0x800996a4)[3]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, hLS, hsz, hA, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have hRd := hJ.1
  lprep
  lpprep
  conds_tac
  obtain ⟨c1, c2, c3⟩ := hc
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roP (extra := []) hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2, hLS, hsz,
      hA.same hcom hst.1 hst.2, fun j hj => absurd hj (by omega), by regs_tac⟩
  · bud

theorem R11564.leaf_800996a4_4 : LeafGoal R11564.plan R11564.plan.cuts[19]! (R11564.plan.leaves 0x800996a4)[4]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, hs, hLS, hsz, hA, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have hRd := hJ.1
  lprep
  lpprep
  conds_tac
  obtain ⟨c1, c2, c3⟩ := hc
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roP (extra := []) hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, 0, items_keep hs hst.2, hLS, hsz,
      hA.same hcom hst.1 hst.2, by omega, fun h => c1 (congrArg BitVec.toNat h),
      fun j hj => absurd hj (by omega), by regs_tac⟩
  · bud

/-! ## `binaryLast`: the byte comparison (value's string at `a3`, probe's at `a1`) -/

theorem R11564.leaf_800996c4_0 : LeafGoal R11564.plan R11564.plan.cuts[20]! (R11564.plan.leaves 0x800996c4)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, k, hs, hLS, hsz, hA, hk, hne, hp, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have hRd := hJ.1
  lprep
  lcprep
  have hbn : strByte m (slicePtr (el G as)) k ≠ strByte m (slicePtr (el G (curr + size / 2))) k :=
    fun h => by simp [h] at hc
  have hnlt : ¬ (strByte m (slicePtr (el G as)) k).toNat <
      (strByte m (slicePtr (el G (curr + size / 2))) k).toNat := fun h => by simp [h] at hc
  have hlb : ltBy (cfg.key m) (el G as) (el G (curr + size / 2)) = false := by
    rw [cfg_key, ltBy_slice_ne m (by omega) (by omega) hp hbn]; simpa using hnlt
  have hl' := last_step (round_sortedA hJ.1) hl hsz
  rw [hlb] at hl'; simp only [Bool.false_eq_true, if_false] at hl'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr + size % 2 + size / 2, size,
      items_keep hs hst.2, ⟨hJ, hlt, hl'⟩, hsz, hA.same hcom hst.1 hst.2, by regs_tac⟩
  · bud

theorem R11564.leaf_800996c4_1 : LeafGoal R11564.plan R11564.plan.cuts[20]! (R11564.plan.leaves 0x800996c4)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, k, hs, hLS, hsz, hA, hk, hne, hp, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have hRd := hJ.1
  lprep
  lcprep
  have hbn : strByte m (slicePtr (el G as)) k ≠ strByte m (slicePtr (el G (curr + size / 2))) k :=
    fun h => by simp [h] at hc
  have hlt' : (strByte m (slicePtr (el G as)) k).toNat <
      (strByte m (slicePtr (el G (curr + size / 2))) k).toNat :=
    Classical.byContradiction fun h => by simp [h] at hc
  have hlb : ltBy (cfg.key m) (el G as) (el G (curr + size / 2)) = true := by
    rw [cfg_key, ltBy_slice_ne m (by omega) (by omega) hp hbn]; simpa using hlt'
  have hl' := last_step (round_sortedA hJ.1) hl hsz
  rw [hlb] at hl'; simp only [if_true] at hl'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2,
      ⟨hJ, hlt, hl'⟩, hsz, hA.same hcom hst.1 hst.2, by regs_tac⟩
  · bud

theorem R11564.leaf_800996c4_2 : LeafGoal R11564.plan R11564.plan.cuts[20]! (R11564.plan.leaves 0x800996c4)[2]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, k, hs, hLS, hsz, hA, hk, hne, hp, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have hRd := hJ.1
  lprep
  lcprep
  exfalso
  by_cases h : (strByte m (slicePtr (el G as)) k).toNat <
    (strByte m (slicePtr (el G (curr + size / 2))) k).toNat <;> simp [h] at hc

theorem R11564.leaf_800996c4_3 : LeafGoal R11564.plan R11564.plan.cuts[20]! (R11564.plan.leaves 0x800996c4)[3]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, k, hs, hLS, hsz, hA, hk, hne, hp, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have hRd := hJ.1
  lprep
  lcprep
  exfalso
  by_cases h : (strByte m (slicePtr (el G as)) k).toNat <
    (strByte m (slicePtr (el G (curr + size / 2))) k).toNat <;> simp [h] at hc

theorem R11564.leaf_800996c4_4 : LeafGoal R11564.plan R11564.plan.cuts[20]! (R11564.plan.leaves 0x800996c4)[4]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, k, hs, hLS, hsz, hA, hk, hne, hp, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have hRd := hJ.1
  lprep
  lcprep
  obtain ⟨hab, c2⟩ := hc
  have hc := c2
  conds_tac
  have hp' : PreEq m (el G as) (el G (curr + size / 2)) (k + 1) := fun j hj => by
    rcases Nat.lt_or_ge j k with h | h
    · exact hp j h
    · rw [show j = k by omega]; exact hab
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, k + 1, items_keep hs hst.2, hLS,
      hsz, hA.same hcom hst.1 hst.2, by omega, hne, hp', by regs_tac⟩
  · bud

theorem R11564.leaf_800996c4_5 : LeafGoal R11564.plan R11564.plan.cuts[20]! (R11564.plan.leaves 0x800996c4)[5]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, curr, size, k, hs, hLS, hsz, hA, hk, hne, hp, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have hRd := hJ.1
  lprep
  lcprep
  obtain ⟨hab, c2⟩ := hc
  have hc := c2
  conds_tac
  have hp' : PreEq m (el G as) (el G (curr + size / 2))
      (min (sliceLen (el G as)) (sliceLen (el G (curr + size / 2)))) := fun j hj => by
    rcases Nat.lt_or_ge j k with h | h
    · exact hp j h
    · rw [show j = k by omega]; exact hab
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  have hQ := And.intro (sl_same hcom hst.1 hst.2 0x48)
    (And.intro (sl_same hcom hst.1 hst.2 0x30) (sl_same hcom hst.1 hst.2 0x50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, curr, size, items_keep hs hst.2, hLS, hsz,
      hA.same hcom hst.1 hst.2, hp', by regs_tac⟩
  · bud

/-! ## The rotation: the first reversal -/

theorem R11564.leaf_80098f2c_0 : LeafGoal R11564.plan R11564.plan.cuts[8]! (R11564.plan.leaves 0x80098f2c)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, hs, hM, hsl, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_frame (keep := kR0) hpre hcom hs hm' hso rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h58 := frame_keep hst.2.2 (by decide) hsl.1
  have h48 : FrameU64 m' (f m) 0x48 (w mid) := by slotF (.var 17)
  have h50 : FrameU64 m' (f m) 0x50 (w as) := by slotF (.var 9)
  have h38 : FrameU64 m' (f m) 0x38 (w (ae - as)) := by slotF (.bin .sub (.var 5) (.var 9))
  have h30 : FrameU64 m' (f m) 0x30 (w ae) := by slotF (.var 5)
  have h40 : FrameU64 m' (f m) 0x40 (w (32 * ae)) := by slotF (.bin .sll (.var 5) (.lit 5))
  have hQ := And.intro (sl_of hst.1 h48) (And.intro (sl_of hst.1 h50) (sl_of hst.1 h30))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, mid, ?_, hM,
      ⟨h58, h48, h50, h30, h38, h40, trivial⟩⟩
    rw [Rotate.rev_short _ (by omega)]; exact hst.2.1
  · bud

theorem R11564.leaf_80098f2c_1 : LeafGoal R11564.plan R11564.plan.cuts[8]! (R11564.plan.leaves 0x80098f2c)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, hs, hM, hsl, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  have hI := And.intro (init_F (c := cfg) h2 (hb.get (off := 0x20) (v := ptr m + w 15) (by simp [baseS])))
    (And.intro (init_F (c := cfg) h2 (hb.get (off := 0x18) (v := ptr m - w 16) (by simp [baseS])))
      (init_F (c := cfg) h2 (hsl.get (off := 0x58) (v := w (32 * as)) (by simp))))
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_frame (keep := kR0) hpre hcom hs hm' hso rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h58 := frame_keep hst.2.2 (by decide) hsl.1
  have h48 : FrameU64 m' (f m) 0x48 (w mid) := by slotF (.var 17)
  have h50 : FrameU64 m' (f m) 0x50 (w as) := by slotF (.var 9)
  have h38 : FrameU64 m' (f m) 0x38 (w (ae - as)) := by slotF (.bin .sub (.var 5) (.var 9))
  have h30 : FrameU64 m' (f m) 0x30 (w ae) := by slotF (.var 5)
  have h40 : FrameU64 m' (f m) 0x40 (w (32 * ae)) := by slotF (.bin .sll (.var 5) (.lit 5))
  have h60 : FrameU64 m' (f m) 0x60 (ptr m + w (32 * (as + (ae - as) / 2) + 15)) := by
    slotF (.bin .add (.bin .add (.init 0 32 8) (.init 0 88 8))
      (.bin .sll (.bin .srl (.bin .sub (.var 5) (.var 9)) (.lit 1)) (.lit 5)))
  have hQ := And.intro (sl_of hst.1 h48) (And.intro (sl_of hst.1 h50) (And.intro (sl_of hst.1 h30)
    (sl_of hst.1 h60)))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, mid, 0, ?_, hM, by omega,
      ⟨h58, h48, h50, h30, h38, h40, h60, trivial⟩, by regs_tac⟩
    rw [Rotate.revAt_zero]; exact hst.2.1
  · bud

theorem R11564.leaf_80098f78_0 : LeafGoal R11564.plan R11564.plan.cuts[9]! (R11564.plan.leaves 0x80098f78)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, i, hs, hM, hi, hsl, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  simp only [rotS, List.cons_append, List.nil_append] at hsl
  obtain ⟨s58, s48, s50, s30, s38, s40, s60, -⟩ := id hsl
  have hI := init_R3 (c := cfg) (lo := 28) (hi := 29) h2 s60
  have hQ := And.intro (sl_of hcom s60) (And.intro (sl_of hcom s48) (And.intro (sl_of hcom s30)
    (sl_of hcom s50)))
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_swap3 (keep := kSw) (e₁ := as + i) (e₂ := as + (ae - as - 1 - i)) hpre hcom hs
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (hr.get (r := 28) (v := ptr m + w (32 * (as + i) + 15)) (by simp))
    (by rw [show as + (ae - as - 1 - i) = ae - 1 - i by omega]
        exact hr.get (r := 29) (v := ptr m + w (32 * (ae - 1 - i) + 16)) (by simp))
    hm' hso rfl (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide)
  have hit := items_rev hi hst.2.1
  obtain ⟨t58, t48, t50, t30, t38, t40, t60, -⟩ := SlotsAre.keep hst.2.2 (by kdec) hsl
  have hQ := And.intro hQ (And.intro (sl_of hst.1 t60) (And.intro (sl_of hst.1 t48)
    (And.intro (sl_of hst.1 t30) (sl_of hst.1 t50))))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, mid, i + 1, hit, hM, by omega,
      ⟨t58, t48, t50, t30, t38, t40, t60, trivial⟩, by regs_tac⟩
  · bud

theorem R11564.leaf_80098f78_1 : LeafGoal R11564.plan R11564.plan.cuts[9]! (R11564.plan.leaves 0x80098f78)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, i, hs, hM, hi, hsl, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  simp only [rotS, List.cons_append, List.nil_append] at hsl
  obtain ⟨s58, s48, s50, s30, s38, s40, s60, -⟩ := id hsl
  have hI := init_R3 (c := cfg) (lo := 28) (hi := 29) h2 s60
  have hQ := And.intro (sl_of hcom s60) (And.intro (sl_of hcom s48) (And.intro (sl_of hcom s30)
    (sl_of hcom s50)))
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_swap3 (keep := kSw) (e₁ := as + i) (e₂ := as + (ae - as - 1 - i)) hpre hcom hs
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (hr.get (r := 28) (v := ptr m + w (32 * (as + i) + 15)) (by simp))
    (by rw [show as + (ae - as - 1 - i) = ae - 1 - i by omega]
        exact hr.get (r := 29) (v := ptr m + w (32 * (ae - 1 - i) + 16)) (by simp))
    hm' hso rfl (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide)
  have hit := items_rev hi hst.2.1
  obtain ⟨t58, t48, t50, t30, t38, t40, t60, -⟩ := SlotsAre.keep hst.2.2 (by kdec) hsl
  have hQ := And.intro hQ (And.intro (sl_of hst.1 t48) (And.intro (sl_of hst.1 t30) (sl_of hst.1 t50)))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, mid, ?_, hM,
      ⟨t58, t48, t50, t30, t38, t40, trivial⟩⟩
    rw [← Rotate.revAt_full, show (ae - as) / 2 = i + 1 by omega]; exact hit
  · bud

/-! ## The rotation: the second reversal -/

theorem R11564.leaf_80099188_0 : LeafGoal R11564.plan R11564.plan.cuts[10]! (R11564.plan.leaves 0x80099188)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, hs, hM, hsl⟩ hc
  have hr : RegsAre mh [] := trivial
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  simp only [rotS, List.cons_append, List.nil_append] at hsl
  obtain ⟨s58, s48, s50, s30, s38, s40, -⟩ := id hsl
  have hI := And.intro (init_F (c := cfg) h2 s48) (And.intro (init_F (c := cfg) h2 s50)
    (init_F (c := cfg) h2 s38))
  have hQ := And.intro (sl_of hcom s48) (And.intro (sl_of hcom s30) (sl_of hcom s50))
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_frame (keep := kS0) hpre hcom hs hm' hso rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have t58 := frame_keep hst.2.2 (by decide) s58
  have t48 := frame_keep hst.2.2 (by decide) s48
  have t50 := frame_keep hst.2.2 (by decide) s50
  have t30 := frame_keep hst.2.2 (by decide) s30
  have h28 : FrameU64 m' (f m) 0x28 (w (mid - as)) := by
    slotF (.bin .sub (.init 0 72 8) (.init 0 80 8))
  have h38 : FrameU64 m' (f m) 0x38 (w (32 * mid)) := by slotF (.bin .sll (.init 0 72 8) (.lit 5))
  have hQ := And.intro hQ (And.intro (sl_of hst.1 t50) (sl_of hst.1 h28))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, mid, ?_, hM,
      ⟨t58, t48, t50, t30, h28, h38, trivial⟩⟩
    rw [Rotate.rev_short (rev as (ae - as) G) (by omega)]; exact hst.2.1
  · bud

theorem R11564.leaf_80099188_1 : LeafGoal R11564.plan R11564.plan.cuts[10]! (R11564.plan.leaves 0x80099188)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, hs, hM, hsl⟩ hc
  have hr : RegsAre mh [] := trivial
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  simp only [rotS, List.cons_append, List.nil_append] at hsl
  obtain ⟨s58, s48, s50, s30, s38, s40, -⟩ := id hsl
  have hI := And.intro (init_F (c := cfg) h2 s48) (And.intro (init_F (c := cfg) h2 s50)
    (And.intro (init_F (c := cfg) h2 s38) (And.intro (init_F (c := cfg) h2 s40)
    (And.intro (init_F (c := cfg) h2 (hb.get (off := 0x20) (v := ptr m + w 15) (by simp [baseS])))
      (init_F (c := cfg) h2 (hb.get (off := 0x18) (v := ptr m - w 16) (by simp [baseS])))))))
  have hQ := And.intro (sl_of hcom s48) (And.intro (sl_of hcom s30) (sl_of hcom s50))
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_frame (keep := kS0) hpre hcom hs hm' hso rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have t58 := frame_keep hst.2.2 (by decide) s58
  have t48 := frame_keep hst.2.2 (by decide) s48
  have t50 := frame_keep hst.2.2 (by decide) s50
  have t30 := frame_keep hst.2.2 (by decide) s30
  have t40 := frame_keep hst.2.2 (by decide) s40
  have h28 : FrameU64 m' (f m) 0x28 (w (mid - as)) := by
    slotF (.bin .sub (.init 0 72 8) (.init 0 80 8))
  have h38 : FrameU64 m' (f m) 0x38 (w (32 * mid)) := by slotF (.bin .sll (.init 0 72 8) (.lit 5))
  have h60 : FrameU64 m' (f m) 0x60 (ptr m + w (32 * (ae + (mid - ae) / 2) + 15)) := by
    slotF (.bin .add (.bin .add (.init 0 32 8) (.init 0 64 8))
      (.bin .sll (.bin .srl (.bin .sub (.bin .sub (.init 0 72 8) (.init 0 80 8)) (.init 0 56 8))
        (.lit 1)) (.lit 5)))
  have hQ := And.intro hQ (And.intro (sl_of hst.1 t50) (And.intro (sl_of hst.1 h28)
    (sl_of hst.1 h60)))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, mid, 0, ?_, hM, by omega,
      ⟨t58, t48, t50, t30, t40, h28, h38, h60, trivial⟩, by regs_tac⟩
    rw [Rotate.revAt_zero]; exact hst.2.1
  · bud

theorem R11564.leaf_800991d8_0 : LeafGoal R11564.plan R11564.plan.cuts[11]! (R11564.plan.leaves 0x800991d8)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, i, hs, hM, hi, hsl, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  simp only [rotS, List.cons_append, List.nil_append] at hsl
  obtain ⟨s58, s48, s50, s30, s40, s28, s38, s60, -⟩ := id hsl
  have hI := init_R3 (c := cfg) (lo := 29) (hi := 30) h2 s60
  have hQ := And.intro (sl_of hcom s60) (And.intro (sl_of hcom s28) (sl_of hcom s50))
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_swap3 (keep := kSw) (e₁ := ae + i) (e₂ := ae + (mid - ae - 1 - i)) hpre hcom hs
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (hr.get (r := 29) (v := ptr m + w (32 * (ae + i) + 15)) (by simp))
    (by rw [show ae + (mid - ae - 1 - i) = mid - 1 - i by omega]
        exact hr.get (r := 30) (v := ptr m + w (32 * (mid - 1 - i) + 16)) (by simp))
    hm' hso rfl (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide)
  have hit := items_rev hi hst.2.1
  obtain ⟨t58, t48, t50, t30, t40, t28, t38, t60, -⟩ := SlotsAre.keep hst.2.2 (by kdec) hsl
  have hQ := And.intro hQ (And.intro (sl_of hst.1 t60) (And.intro (sl_of hst.1 t28)
    (sl_of hst.1 t50)))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, mid, i + 1, hit, hM, by omega,
      ⟨t58, t48, t50, t30, t40, t28, t38, t60, trivial⟩, by regs_tac⟩
  · bud

theorem R11564.leaf_800991d8_1 : LeafGoal R11564.plan R11564.plan.cuts[11]! (R11564.plan.leaves 0x800991d8)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, i, hs, hM, hi, hsl, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  simp only [rotS, List.cons_append, List.nil_append] at hsl
  obtain ⟨s58, s48, s50, s30, s40, s28, s38, s60, -⟩ := id hsl
  have hI := init_R3 (c := cfg) (lo := 29) (hi := 30) h2 s60
  have hQ := And.intro (sl_of hcom s60) (And.intro (sl_of hcom s28) (sl_of hcom s50))
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_swap3 (keep := kSw) (e₁ := ae + i) (e₂ := ae + (mid - ae - 1 - i)) hpre hcom hs
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (hr.get (r := 29) (v := ptr m + w (32 * (ae + i) + 15)) (by simp))
    (by rw [show ae + (mid - ae - 1 - i) = mid - 1 - i by omega]
        exact hr.get (r := 30) (v := ptr m + w (32 * (mid - 1 - i) + 16)) (by simp))
    hm' hso rfl (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide)
  have hit := items_rev hi hst.2.1
  obtain ⟨t58, t48, t50, t30, t40, t28, t38, t60, -⟩ := SlotsAre.keep hst.2.2 (by kdec) hsl
  have hQ := And.intro hQ (And.intro (sl_of hst.1 t28) (sl_of hst.1 t50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, mid, ?_, hM,
      ⟨t58, t48, t50, t30, t28, t38, trivial⟩⟩
    rw [← Rotate.revAt_full, show (mid - ae) / 2 = i + 1 by omega]; exact hit
  · bud

/-! ## The rotation: the third reversal -/

theorem R11564.leaf_800993e8_0 : LeafGoal R11564.plan R11564.plan.cuts[12]! (R11564.plan.leaves 0x800993e8)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, hs, hM, hsl⟩ hc
  have hr : RegsAre mh [] := trivial
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  simp only [rotS, List.cons_append, List.nil_append] at hsl
  obtain ⟨s58, s48, s50, s30, s28, s38, -⟩ := id hsl
  have hI := init_F (c := cfg) h2 s28
  have hQ := And.intro (sl_of hcom s28) (sl_of hcom s50)
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roF hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  have hQ := And.intro hQ (sl_of hst.1 (s50.keep fun _ _ => hst.2 _))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, G, as, ae, mid, ?_, hM,
      ⟨s48.keep fun _ _ => hst.2 _, s50.keep fun _ _ => hst.2 _, s30.keep fun _ _ => hst.2 _, trivial⟩⟩
    unfold R3; rw [Rotate.rev_short (rev ae (mid - ae) (rev as (ae - as) G)) (by omega)]
    exact items_keep hs hst.2
  · bud

theorem R11564.leaf_800993e8_1 : LeafGoal R11564.plan R11564.plan.cuts[12]! (R11564.plan.leaves 0x800993e8)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, hs, hM, hsl⟩ hc
  have hr : RegsAre mh [] := trivial
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  simp only [rotS, List.cons_append, List.nil_append] at hsl
  obtain ⟨s58, s48, s50, s30, s28, s38, -⟩ := id hsl
  have hI := And.intro (init_F (c := cfg) h2 s28) (And.intro (init_F (c := cfg) h2 s58)
    (And.intro (init_F (c := cfg) h2 s38)
    (And.intro (init_F (c := cfg) h2 (hb.get (off := 0x20) (v := ptr m + w 15) (by simp [baseS])))
      (init_F (c := cfg) h2 (hb.get (off := 0x18) (v := ptr m - w 16) (by simp [baseS]))))))
  have hQ := And.intro (sl_of hcom s28) (sl_of hcom s50)
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_frame (keep := kOut) hpre hcom hs hm' hso rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have t48 := frame_keep hst.2.2 (by decide) s48
  have t50 := frame_keep hst.2.2 (by decide) s50
  have t30 := frame_keep hst.2.2 (by decide) s30
  have t28 := frame_keep hst.2.2 (by decide) s28
  have t38 := frame_keep hst.2.2 (by decide) s38
  have h58 : FrameU64 m' (f m) 0x58 (ptr m + w (32 * (as + (mid - as) / 2) + 15)) := by
    slotF (.bin .add (.bin .add (.init 0 32 8) (.init 0 88 8))
      (.bin .sll (.bin .srl (.init 0 40 8) (.lit 1)) (.lit 5)))
  have hQ := And.intro hQ (And.intro (sl_of hst.1 t50) (sl_of hst.1 h58))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, mid, 0, ?_, hM, by omega,
      ⟨t48, t50, t30, t28, t38, h58, trivial⟩, by regs_tac⟩
    rw [Rotate.revAt_zero]; exact hst.2.1
  · bud

theorem R11564.leaf_8009941c_0 : LeafGoal R11564.plan R11564.plan.cuts[13]! (R11564.plan.leaves 0x8009941c)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, i, hs, hM, hi, hsl, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  obtain ⟨s48, s50, s30, s28, s38, s58, -⟩ := id hsl
  have hI := init_R3 (c := cfg) (lo := 6) (hi := 7) h2 s58
  have hQ := And.intro (sl_of hcom s58) (sl_of hcom s50)
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_swap3 (keep := kT) (e₁ := as + i) (e₂ := as + (mid - as - 1 - i)) hpre hcom hs
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (hr.get (r := 6) (v := ptr m + w (32 * (as + i) + 15)) (by simp))
    (by rw [show as + (mid - as - 1 - i) = mid - 1 - i by omega]
        exact hr.get (r := 7) (v := ptr m + w (32 * (mid - 1 - i) + 16)) (by simp))
    hm' hso rfl (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide)
  have hit := items_rev hi hst.2.1
  obtain ⟨t48, t50, t30, t28, t38, t58, -⟩ := SlotsAre.keep hst.2.2 (by kdec) hsl
  have hQ := And.intro hQ (And.intro (sl_of hst.1 t58) (sl_of hst.1 t50))
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, mid, i + 1, hit, hM, by omega,
      ⟨t48, t50, t30, t28, t38, t58, trivial⟩, by regs_tac⟩
  · bud

theorem R11564.leaf_8009941c_1 : LeafGoal R11564.plan R11564.plan.cuts[13]! (R11564.plan.leaves 0x8009941c)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, i, hs, hM, hi, hsl, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  obtain ⟨s48, s50, s30, s28, s38, s58, -⟩ := id hsl
  have hI := init_R3 (c := cfg) (lo := 6) (hi := 7) h2 s58
  have hQ := And.intro (sl_of hcom s58) (sl_of hcom s50)
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_swap3 (keep := kT) (e₁ := as + i) (e₂ := as + (mid - as - 1 - i)) hpre hcom hs
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (hr.get (r := 6) (v := ptr m + w (32 * (as + i) + 15)) (by simp))
    (by rw [show as + (mid - as - 1 - i) = mid - 1 - i by omega]
        exact hr.get (r := 7) (v := ptr m + w (32 * (mid - 1 - i) + 16)) (by simp))
    hm' hso rfl (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide)
  have hit := items_rev hi hst.2.1
  obtain ⟨t48, t50, t30, t28, t38, t58, -⟩ := SlotsAre.keep hst.2.2 (by kdec) hsl
  have hQ := And.intro hQ (sl_of hst.1 t50)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1, hb.keep hst.2.2 (by kdec)⟩, G, as, ae, mid, ?_, hM,
      ⟨t48, t50, t30, trivial⟩⟩
    unfold R3; rw [← Rotate.revAt_full, show (mid - as) / 2 = i + 1 by omega]; exact hit
  · bud

/-! ## After the rotation -/

theorem R11564.leaf_80099634_0 : LeafGoal R11564.plan R11564.plan.cuts[14]! (R11564.plan.leaves 0x80099634)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, hs, hM, hsl⟩ hc
  have hr : RegsAre mh [] := trivial
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  obtain ⟨s48, s50, s30, -⟩ := id hsl
  have hI := And.intro (init_F (c := cfg) h2 s48)
    (init_F (c := cfg) h2 (hb.get (off := 8) (v := w (bE m)) (by simp [baseS])))
  have hQ := sl_of hcom s50
  conds_tac
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roF hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, R3 G as ae mid, items_keep hs hst.2,
      round_done (join_of_mid hM).1 (.inr (by omega))⟩
  · bud

theorem R11564.leaf_80099634_1 : LeafGoal R11564.plan R11564.plan.cuts[14]! (R11564.plan.leaves 0x80099634)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, hs, hM, hsl⟩ hc
  have hr : RegsAre mh [] := trivial
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  obtain ⟨s48, s50, s30, -⟩ := id hsl
  have hI := And.intro (init_F (c := cfg) h2 s48) (And.intro (init_F (c := cfg) h2 s50)
    (And.intro (init_F (c := cfg) h2 s30)
      (init_F (c := cfg) h2 (hb.get (off := 8) (v := w (bE m)) (by simp [baseS])))))
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval] at hc
  simp (disch := decide) only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval, eF_v, hI, hR,
    Fin.reduceOfNat, Fin.isValue] at hc
  rw [show w mid - w ae + w as = w (mid - ae + as) by wgoal, ult_w (by omega) (by omega)] at hc
  simp at hc; omega

theorem R11564.leaf_80099634_3 : LeafGoal R11564.plan R11564.plan.cuts[14]! (R11564.plan.leaves 0x80099634)[3]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom, hb⟩, G, as, ae, mid, hs, hM, hsl⟩ hc
  have hr : RegsAre mh [] := trivial
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  obtain ⟨s48, s50, s30, -⟩ := id hsl
  have hI := And.intro (init_F (c := cfg) h2 s48) (And.intro (init_F (c := cfg) h2 s50)
    (And.intro (init_F (c := cfg) h2 s30)
    (And.intro (init_F (c := cfg) h2 (hb.get (off := 8) (v := w (bE m)) (by simp [baseS])))
      (init_F (c := cfg) h2 (hb.get (off := 0x10) (v := ptr m) (by simp [baseS]))))))
  have hQ := sl_of hcom s50
  conds_tac
  have hKN := Nat.mul_le_mul_left (K m) (show mid - (mid - ae + as) ≤ bE m - aS m by omega)
  have hq := Qf_le (be := bE m) (R := Rb m) (show as ≤ mid - ae + as by omega)
  simp only [Rb, ROT, LST, N] at hq
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_roF hpre hcom hm' hso rfl rfl rfl rfl (by decide)
  have t48 := s48.keep fun _ _ => hst.2 _
  have t50 := s50.keep fun _ _ => hst.2 _
  have t30 := s30.keep fun _ _ => hst.2 _
  have hA : AsL m' (mid - ae + as) := by
    unfold AsL; rw [sl_of hst.1 t48, sl_of hst.1 t30, sl_of hst.1 t50]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hQ := And.intro hQ (show sl m' 0x48 - sl m' 0x30 + sl m' 0x50 = mid - ae + as from hA)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1, hb.same hst.2⟩, R3 G as ae mid, mid - ae + as, mid, items_keep hs hst.2,
      by rw [show mid - ae + as = as + (mid - ae) by omega]; exact join_of_mid hM, by omega, hA,
      by regs_tac⟩
  · bud

/-! ## Epilogue (`0x80099708`) -/

theorem R11564.leaf_80099708_0 : LeafGoal R11564.plan R11564.plan.cuts[21]! (R11564.plan.leaves 0x80099708)[0]! := by
  leaf_intro
  rintro m mh ⟨hpre, hpc, hcom, G, hs, hmg⟩ -
  refine ⟨?_, by simp, fun m' hm' he hso => ?_⟩
  · have := hpre.2.2.1
    simp [Oblig.holds, Sym.eval, BinOp.eval, envE, Env.setVars, entryEnv]
    simpa [RetAligned] using this
  · dsimp only at hm' he hso
    exit_intro
    exact epi_post hpre hcom hs hmg hm' hso he (by decide)

/-! ## Entry (`0x80098ddc`): `A` empty, `B` empty, the first round -/

theorem w_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : w a = w b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem entry_bound {m : Machine} (h : Pre cfg m) : Qf (bE m) (aS m) (Rb m) + Rb m + 100 ≤ bound := by
  have hbe := pre_bE h
  have hL := Lmax_le (pre_sl h)
  unfold Layout.ramHi at hL
  have hK : K m ≤ 2 ^ 36 := by unfold K; omega
  have hN : N m ≤ 2 ^ 24 := by unfold N; omega
  have hKN : K m * N m ≤ 2 ^ 36 * 2 ^ 24 := Nat.mul_le_mul hK hN
  have hR : Rb m ≤ 2 ^ 62 := by unfold Rb ROT LST; omega
  have hQ : Qf (bE m) (aS m) (Rb m) ≤ 2 ^ 24 * 2 ^ 62 := by
    unfold Qf; exact Nat.mul_le_mul (by omega) hR
  unfold bound; omega

theorem R11564.leaf_80098ddc_0 : LeafGoal R11564.plan R11564.plan.cuts[0]! (R11564.plan.leaves 0x80098ddc)[0]! := by
  leaf_intro
  rintro m mh ⟨rfl, hpc, hpre⟩ hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, SBool.eval, env0_aS, env0_aE,
    beq_iff_eq] at hc
  refine ⟨by simp, by simp [bound], fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := entry_step hpre hm' hso rfl rfl rfl rfl (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, items mh (ptr mh), hst.2,
      round_done (round_init hpre) (.inl (w_inj (u64_lt _ _) (u64_lt _ _) hc).symm)⟩
  · simp [bound]

theorem R11564.leaf_80098ddc_1 : LeafGoal R11564.plan R11564.plan.cuts[0]! (R11564.plan.leaves 0x80098ddc)[1]! := by
  leaf_intro
  rintro m mh ⟨rfl, hpc, hpre⟩ hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    env0_aS, env0_aE, env0_bS, env0_bE, beq_iff_eq] at hc
  refine ⟨by simp, by simp [bound], fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := entry_step hpre hm' hso rfl rfl rfl rfl (by decide)
  have hbb := w_inj (u64_lt _ _) (u64_lt _ _) hc.2
  obtain ⟨-, hr2, -⟩ := pre_runs hpre
  simp only [bS, bE] at hr2 hbb
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, items mh (ptr mh), hst.2, round_done (round_init hpre)
      (.inr (by simp only [bE]; omega))⟩
  · simp [bound]

theorem R11564.leaf_80098ddc_2 : LeafGoal R11564.plan R11564.plan.cuts[0]! (R11564.plan.leaves 0x80098ddc)[2]! := by
  leaf_intro
  rintro m mh ⟨rfl, hpc, hpre⟩ hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    env0_aS, env0_aE, env0_bS, env0_bE, bne_iff_ne, ne_eq] at hc
  obtain ⟨hr1, hr2, hr3⟩ := pre_runs hpre
  have hne : aS mh ≠ aE mh := fun h => hc.1 (congrArg w h).symm
  have has : aS mh < aE mh := by omega
  have hfit := pre_hfit hpre
  have hbe := pre_bE hpre
  have hram := pre_items hpre
  have hR : mh.reg 10 = ptr mh := rfl
  have hI := And.intro (env0_aS (c := cfg) (m := mh)) (And.intro (env0_aE (c := cfg) (m := mh))
    (And.intro (env0_bS (c := cfg) (m := mh)) (env0_bE (c := cfg) (m := mh))))
  have hl1 := u64_lt (m := mh) (mh.reg 11) 0
  have hl2 := u64_lt (m := mh) (mh.reg 11) 8
  have hl3 := u64_lt (m := mh) (mh.reg 12) 0
  have hl4 := u64_lt (m := mh) (mh.reg 12) 8
  simp only [Layout.ramLo, Layout.ramHi] at hram
  refine ⟨by simp, by simp [bound], fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := entry_step_ex (ex := [⟨2, 8, 8, .init 1 8 8⟩, ⟨2, 16, 8, .var 10⟩,
    ⟨2, 24, 8, .bin .add (.var 10) (.lit 18446744073709551600)⟩, ⟨2, 32, 8, .bin .add (.var 10) (.lit 15)⟩])
    hpre hm' hso rfl (by decide) rfl rfl rfl (by decide)
  have hb2 : (env0 cfg mh).base 2 = f mh := by simp [env0, entryEnv, Env.base, frame]
  have hsz : ∀ off, off + 8 ≤ 0x110 → off + 8 ≤ (env0 cfg mh).size 2 := fun off h => by
    simp [env0, entryEnv, Env.size, cfg_fs]; omega
  have h20 : FrameU64 m' (f mh) 0x20 (ptr mh + w 15) :=
    slot_at hm' (r := 2) (v := .bin .add (.var 10) (.lit 15)) (by decide) (hsz _ (by omega))
      (by decide) hb2 (by sevl <;> wgoal)
  have h18 : FrameU64 m' (f mh) 0x18 (ptr mh - w 16) :=
    slot_at hm' (r := 2) (v := .bin .add (.var 10) (.lit 18446744073709551600)) (by decide)
      (hsz _ (by omega)) (by decide) hb2 (by sevl <;> wgoal)
  have h10 : FrameU64 m' (f mh) 0x10 (ptr mh) :=
    slot_at hm' (r := 2) (v := .var 10) (by decide) (hsz _ (by omega)) (by decide) hb2 (by sevl)
  have h08 : FrameU64 m' (f mh) 8 (w (bE mh)) :=
    slot_at hm' (r := 2) (v := .init 1 8 8) (by decide) (hsz _ (by omega)) (by decide) hb2 (by sevl)
  have h9 : (m'.reg (Fin.ofNat 32 9)).toNat = aS mh := by
    rw [reg_at hm' 9]
    simp (disch := decide) only [SState.reg, List.getD_cons_succ, List.getD_cons_zero,
      Nat.reduceEqDiff, if_false, env0_aS, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (u64_lt _ _)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1, ⟨h20, h18, h10, h08, trivial⟩⟩, items mh (ptr mh), aS mh, aE mh, hst.2,
      round_init hpre, has, ?_⟩
    simp only [eqO, List.cons_append, List.nil_append, RegsAre]
    and_intros <;> first | exact True.intro | (rgoal <;> wgoal)
  · simp only [bOut, Q, ix, h9]
    have := entry_bound hpre
    omega

zesu_assemble R11564

end ZesuExec.Fn.MergeInPlace.C11564
