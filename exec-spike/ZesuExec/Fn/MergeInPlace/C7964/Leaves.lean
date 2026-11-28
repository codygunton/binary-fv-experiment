import ZesuExec.Fn.MergeInPlace.C7964.Vc
import ZesuExec.Fn.Rotate.Cuts

/-!
# `sort.block.mergeInPlace__anon_7964`: cut lemmas and leaves
-/

namespace ZesuExec.Fn.MergeInPlace.C7964
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Fn.MergeInPlace
open ZesuExec.Fn.Rotate (revAt rev)

theorem cfg_fs : cfg.fs = 112 := rfl
theorem cfg_key (m : Machine) : cfg.key m = fun x => x := rfl
/-- The offset `-16` of the swaps' second pointer (rewritten before `add_big`). -/
theorem ofInt_m16 : BitVec.ofInt 64 (-16) = w 18446744073709551600 := rfl

/-- The frame offsets of the saved registers. -/
def kS : List Nat := List.range' 0x40 0x30
/-- …and of the copy at `0x20`. -/
def kHi : List Nat := List.range' 0x20 0x20 ++ kS
/-- …and of the copy at `0`. -/
def kLo : List Nat := List.range' 0 0x20 ++ kS

/-! ## Leaf tactics -/

set_option hygiene false in
/-- A word equation or a `Nat` goal through `toNat` and `omega`. -/
macro "wgoal" : tactic => `(tactic| (
  try apply BitVec.eq_of_toNat_eq
  (simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    BitVec.toNat_and, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]) <;> omega))

set_option hygiene false in
/-- `m'.reg r = v` from the leaf's symbolic value of `r` and `hR`. -/
macro "rgoal" : tactic => `(tactic| (
  rw [reg_at hm' _]
  simp (disch := decide) only [SState.reg, Sym.eval, BinOp.eval, envN, envP, envC, envR, envE, env0,
    entryEnv, Env.base, Env.setVars, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceEqDiff,
    if_false, Fin.reduceOfNat, Fin.isValue, hR, ofInt_m16, Rotate.add_big, Rotate.mul_big, Rotate.add_neg',
    Nat.reducePow, Nat.reduceSub, BitVec.ofInt_ofNat]))

set_option hygiene false in
macro "regs_tac" : tactic => `(tactic| (
  simp only [eqB, eqF, eqM, eqL, List.cons_append, List.nil_append, RegsAre]
  and_intros <;> first | exact True.intro | (rgoal <;> wgoal)))

set_option hygiene false in
/-- The leaf's conditions as `Nat` facts. -/
macro "conds_tac" : tactic => `(tactic| (
  try simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    List.not_mem_nil, false_implies, implies_true, and_true] at hc
  try simp only [Sym.eval, BinOp.eval, envN, envP, envC, envR, env0, entryEnv, Env.base, hR,
    BitVec.ult, bne_iff_ne, beq_iff_eq, ne_eq, Bool.not_eq_true, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_eq_true', Fin.reduceOfNat, Fin.isValue,
    List.getD_cons_succ, List.getD_cons_zero] at hc
  try simp (disch := decide) only [ofInt_m16, Rotate.add_big, Rotate.mul_big, Rotate.add_neg', Nat.reducePow,
    Nat.reduceSub] at hc
  try simp only [BitVec.ofInt_ofNat, BitVec.toNat_eq] at hc
  try simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    BitVec.toNat_and, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod] at hc
  try simp (disch := omega) only [Nat.mod_eq_of_lt, Rotate.wsub_mod] at hc))

set_option hygiene false in
/-- Name the facts every leaf uses: bounds, `sp`, the registers `hR`, the conditions `hc`. -/
macro "lprep" : tactic => `(tactic| (
  have hfit := pre_hfit hpre
  have hbe := pre_bE hpre
  have hram := pre_items hpre
  have hfr := pre_frame hpre
  have h2 : mh.reg 2 = frame cfg m := hcom.2.1
  have hR := And.intro h2 hr
  simp only [RegsAre, eqB, eqF, eqM, eqL, List.cons_append, List.nil_append, Fin.reduceOfNat,
    and_true] at hR
  simp only [cfg_fs, Layout.ramLo, Layout.ramHi] at hram hfr
  conds_tac))

set_option hygiene false in
/-- The leaf's conditions as `Nat` facts. -/
macro "conds_tac0" : tactic => `(tactic| (
  try simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    List.not_mem_nil, false_implies, implies_true, and_true] at hc
  try simp only [Sym.eval, BinOp.eval, envN, envP, envC, envR, env0, entryEnv, Env.base, hR,
    BitVec.ult, bne_iff_ne, beq_iff_eq, ne_eq, Bool.not_eq_true, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_eq_true', Fin.reduceOfNat, Fin.isValue,
    List.getD_cons_succ, List.getD_cons_zero] at hc
  try simp (disch := decide) only [ofInt_m16, Rotate.add_big, Rotate.mul_big, Rotate.add_neg', Nat.reducePow,
    Nat.reduceSub] at hc
  try simp only [BitVec.ofInt_ofNat, BitVec.toNat_eq] at hc
  try simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    BitVec.toNat_and, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod] at hc))

set_option hygiene false in
/-- Name the facts every leaf uses: bounds, `sp`, the registers `hR`, the conditions `hc`. -/
macro "lprep0" : tactic => `(tactic| (
  have hfit := pre_hfit hpre
  have hbe := pre_bE hpre
  have hram := pre_items hpre
  have hfr := pre_frame hpre
  have h2 : mh.reg 2 = frame cfg m := hcom.2.1
  have hR := And.intro h2 hr
  simp only [RegsAre, eqB, eqF, eqM, eqL, List.cons_append, List.nil_append, Fin.reduceOfNat,
    and_true] at hR
  simp only [cfg_fs, Layout.ramLo, Layout.ramHi] at hram hfr
  conds_tac0))

set_option hygiene false in
/-- A budget inequality: the budget definitions unfolded, the registers of the cut's machine
(`hR`) and of the leaf's (`hm'`) read off, then `omega`. -/
macro "bud" : tactic => `(tactic| (
  try dsimp only
  simp only [bOut, bF, bFp, bFc, bFj, bR0, bR1, bS0, bS1, bT0, bT1, bJ, bL, bLp, bLc, bLj, Q, QL,
    Rb, LST, ROT, N, ix, dx, bound]
  try simp (disch := decide) only [Rotate.reg_of_lt hm']
  try simp (disch := decide) only [SState.reg, Sym.eval, BinOp.eval, envN, envP, envC, envR, envE,
    env0, entryEnv, Env.base, Env.setVars, List.getD_cons_succ, List.getD_cons_zero,
    Nat.reduceEqDiff, if_false, Fin.reduceOfNat, Fin.isValue, hR, ofInt_m16, Rotate.add_big, Rotate.mul_big,
    Rotate.add_neg', Nat.reducePow, Nat.reduceSub, BitVec.ofInt_ofNat]
  try simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    BitVec.toNat_and, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]
  try simp (disch := omega) only [Nat.mod_eq_of_lt, Rotate.wsub_mod]
  try simp (disch := omega) only [Nat.add_zero, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left, Nat.mul_div_cancel]
  omega))

set_option hygiene false in
/-- `bud` without the closing normalisation and `omega`: for a budget that needs a lemma about
`Qf` (a new round, where `omega` on the whole context exceeds the recursion limit). -/
macro "bud0" : tactic => `(tactic| (
  try dsimp only
  simp only [bOut, bF, bFp, bFc, bFj, bR0, bR1, bS0, bS1, bT0, bT1, bJ, bL, bLp, bLc, bLj, Q, QL,
    Rb, LST, ROT, N, ix, dx, bound]
  try simp (disch := decide) only [Rotate.reg_of_lt hm']
  try simp (disch := decide) only [SState.reg, Sym.eval, BinOp.eval, envN, envP, envC, envR, envE,
    env0, entryEnv, Env.base, Env.setVars, List.getD_cons_succ, List.getD_cons_zero,
    Nat.reduceEqDiff, if_false, Fin.reduceOfNat, Fin.isValue, hR, ofInt_m16, Rotate.add_big, Rotate.mul_big,
    Rotate.add_neg', Nat.reducePow, Nat.reduceSub, BitVec.ofInt_ofNat]
  try simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    BitVec.toNat_and, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]
  try simp (disch := omega) only [Nat.mod_eq_of_lt, Rotate.wsub_mod]))

set_option hygiene false in
/-- `rgoal` for the entry's leaves: the loads of `A` and `B` first. -/
macro "rgoal0" : tactic => `(tactic| (
  rw [reg_at hm' _]
  simp (disch := decide) only [SState.reg, List.getD_cons_succ, List.getD_cons_zero,
    Nat.reduceEqDiff, if_false]
  try simp only [env0_aS, env0_aE, env0_bS, env0_bE]
  try simp (disch := decide) only [Sym.eval, BinOp.eval, env0, entryEnv, Env.base,
    Fin.reduceOfNat, Fin.isValue, hR, ofInt_m16, Rotate.add_big, Rotate.mul_big, Rotate.add_neg',
    Nat.reducePow, Nat.reduceSub, BitVec.ofInt_ofNat]))

set_option hygiene false in
/-- After the run of a leaf from an `SN` cut. -/
macro "nstep" : tactic => `(tactic| (
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_N) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he))

/-! ## Cut points -/

theorem R7964.cut_8004f388 : CutOK R7964.plan R7964.plan.cuts[0]! := by
  cut_intro; rintro m mh ⟨rfl, hpc, hpre⟩
  exact ⟨(cut0_facts hpre).1, (cut0_facts hpre).2, hpre.1, hpc⟩

theorem R7964.cut_8004f3dc : CutOK R7964.plan R7964.plan.cuts[1]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩
theorem R7964.cut_8004f3f8 : CutOK R7964.plan R7964.plan.cuts[2]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩
theorem R7964.cut_8004f4ac : CutOK R7964.plan R7964.plan.cuts[6]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩
theorem R7964.cut_8004f69c : CutOK R7964.plan R7964.plan.cuts[8]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩
theorem R7964.cut_8004f890 : CutOK R7964.plan R7964.plan.cuts[10]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩
theorem R7964.cut_8004fa78 : CutOK R7964.plan R7964.plan.cuts[12]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩
theorem R7964.cut_8004faac : CutOK R7964.plan R7964.plan.cuts[16]! := by
  cut_intro; rintro m mh ⟨⟨-, hpc, hcom⟩, -⟩; exact ⟨cutN_facts.1, cutN_facts.2, hcom.1, hpc⟩

theorem R7964.cut_8004f3fc : CutOK R7964.plan R7964.plan.cuts[3]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, ⟨⟨-, -, h3, -⟩, has, -⟩, -, hr⟩
  have h := cutP_facts (extra := []) hpre hcom hs (show as < bE m by omega)
    (hr.get (r := 6) (v := ptr m + w (32 * as)) (by simp [eqF, eqB])) (by simp)
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R7964.cut_8004f43c : CutOK R7964.plan R7964.plan.cuts[4]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, ⟨-, -, hf⟩, hsz, -, hr⟩
  have h := cutP_facts (extra := [(30, .ptr 0 0x20)]) hpre hcom hs
    (show curr + size / 2 < bE m by have := hf.2.1; omega)
    (hr.get (r := 20) (v := ptr m + w (32 * (curr + size / 2))) (by simp [eqF, eqB])) (by
      simp only [List.mem_singleton, forall_eq, Sym.eval, envP, entryEnv, Env.base,
        List.getD_cons_zero, Fin.reduceOfNat]
      rw [show mh.reg 30 = _ from hr.get (r := 30) (v := frame cfg m + w 32) (by simp [eqF, eqB]),
        hcom.2.1]; rfl)
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R7964.cut_8004f460 : CutOK R7964.plan R7964.plan.cuts[5]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, -, -, -, hk, -, -, -, hr⟩
  have h := cutC_facts (c := cfg) (jx := k) (jy := 32 + k) hpre hcom (by simp [cfg]; omega)
    (by simp [cfg]; omega) (by omega) (hr.get (r := 31) (v := frame cfg m + w k) (by simp [eqF, eqB]))
    (hr.get (r := 30) (v := frame cfg m + w (32 + k)) (by simp [eqF, eqB]))
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R7964.cut_8004f4d0 : CutOK R7964.plan R7964.plan.cuts[7]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, i, hs, ⟨⟨-, -, h3, -⟩, -⟩, hi, hr⟩
  have h := cutR_facts hpre hs (e₁ := as + i) (e₂ := ae - 1 - i) (by omega) (by omega) (by omega)
    (hr.get (r := 28) (v := ptr m + w (32 * (as + i) + 15)) (by simp [eqM, eqB]))
    (hr.get (r := 29) (v := ptr m + w (32 * (ae - 1 - i) + 16)) (by simp [eqM, eqB]))
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R7964.cut_8004f6c4 : CutOK R7964.plan R7964.plan.cuts[9]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, i, hs, ⟨-, -, hf⟩, hi, hr⟩
  have := hf.2.1
  have h := cutR_facts hpre hs (e₁ := ae + i) (e₂ := mid - 1 - i) (by omega) (by omega) (by omega)
    (hr.get (r := 29) (v := ptr m + w (32 * (ae + i) + 15)) (by simp [eqM, eqB]))
    (hr.get (r := 30) (v := ptr m + w (32 * (mid - 1 - i) + 16)) (by simp [eqM, eqB]))
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R7964.cut_8004f8ac : CutOK R7964.plan R7964.plan.cuts[11]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, i, hs, ⟨-, -, hf⟩, hi, hr⟩
  have := hf.2.1
  have h := cutR_facts hpre hs (e₁ := as + i) (e₂ := mid - 1 - i) (by omega) (by omega) (by omega)
    (hr.get (r := 6) (v := ptr m + w (32 * (as + i) + 15)) (by simp [eqM, eqB]))
    (hr.get (r := 7) (v := ptr m + w (32 * (mid - 1 - i) + 16)) (by simp [eqM, eqB]))
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R7964.cut_8004fab0 : CutOK R7964.plan R7964.plan.cuts[13]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, ⟨⟨-, has, -⟩, hlt, -⟩, -, hr⟩
  have h := cutP_facts (extra := []) hpre hcom hs (show as < bE m by omega)
    (hr.get (r := 17) (v := ptr m + w (32 * as)) (by simp [eqL, eqB])) (by simp)
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R7964.cut_8004faf0 : CutOK R7964.plan R7964.plan.cuts[14]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, ⟨-, hlt, hl⟩, hsz, -, hr⟩
  have h := cutP_facts (extra := [(28, .ptr 0 0x20)]) hpre hcom hs
    (show curr + size / 2 < bE m by have := hl.2.1; omega)
    (hr.get (r := 18) (v := ptr m + w (32 * (curr + size / 2))) (by simp [eqL, eqB])) (by
      simp only [List.mem_singleton, forall_eq, Sym.eval, envP, entryEnv, Env.base,
        List.getD_cons_zero, Fin.reduceOfNat]
      rw [show mh.reg 28 = _ from hr.get (r := 28) (v := frame cfg m + w 32) (by simp [eqL, eqB]),
        hcom.2.1]; rfl)
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R7964.cut_8004fb14 : CutOK R7964.plan R7964.plan.cuts[15]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, -, -, -, hk, -, -, -, hr⟩
  have h := cutC_facts (c := cfg) (jx := k) (jy := 32 + k) hpre hcom (by simp [cfg]; omega)
    (by simp [cfg]; omega) (by omega) (hr.get (r := 29) (v := frame cfg m + w k) (by simp [eqL, eqB]))
    (hr.get (r := 28) (v := frame cfg m + w (32 + k)) (by simp [eqL, eqB]))
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R7964.cut_8004fb54 : CutOK R7964.plan R7964.plan.cuts[17]! := by
  cut_intro; rintro m mh ⟨⟨hpre, hpc, hcom⟩, -⟩
  exact ⟨(cutE_facts hpre hcom).1, (cutE_facts hpre hcom).2, hcom.1, hpc⟩

/-! ## Outer loop head -/

theorem R7964.leaf_8004f3dc_1 : LeafGoal R7964.plan R7964.plan.cuts[1]! (R7964.plan.leaves 0x8004f3dc)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, hs, hRd, has, hr⟩ hc
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, G, as, ae, ae, bE m - ae, items_keep hs hst.2,
      ⟨hRd, has, first_init hRd.2.2.1⟩, by omega, by regs_tac⟩
  · bud

theorem R7964.leaf_8004f3dc_0 : LeafGoal R7964.plan R7964.plan.cuts[1]! (R7964.plan.leaves 0x8004f3dc)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, hs, hRd, has, hr⟩ hc
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, bE m, items_keep hs hst.2,
      ⟨hRd, has, first_empty (by omega)⟩, by regs_tac⟩
  · bud

/-! ## `binaryFirst`: the latch -/

theorem R7964.leaf_8004f3f8_0 : LeafGoal R7964.plan R7964.plan.cuts[2]! (R7964.plan.leaves 0x8004f3f8)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, ⟨hRd, has, hf⟩, hsz, hr⟩ hc
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · rw [show size / 2 = 0 by omega] at hf
    exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr, items_keep hs hst.2, ⟨hRd, has, hf⟩, by regs_tac⟩
  · bud

theorem R7964.leaf_8004f3f8_1 : LeafGoal R7964.plan R7964.plan.cuts[2]! (R7964.plan.leaves 0x8004f3f8)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, ⟨hRd, has, hf⟩, hsz, hr⟩ hc
  obtain ⟨r1, r2, r3, -⟩ := id hRd
  obtain ⟨f1, f2, -, -⟩ := id hf
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr, size / 2, items_keep hs hst.2, ⟨hRd, has, hf⟩,
      by omega, by regs_tac⟩
  · bud

/-! ## The rotation: the three reversals begin -/

theorem R7964.leaf_8004f4ac_0 : LeafGoal R7964.plan R7964.plan.cuts[6]! (R7964.plan.leaves 0x8004f4ac)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, hs, hM, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, G, as, ae, mid, ?_, hM, by regs_tac⟩
    rw [Rotate.rev_short _ (by omega)]; exact items_keep hs hst.2
  · bud

theorem R7964.leaf_8004f4ac_1 : LeafGoal R7964.plan R7964.plan.cuts[6]! (R7964.plan.leaves 0x8004f4ac)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, hs, hM, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, G, as, ae, mid, 0, ?_, hM, by omega, by regs_tac⟩
    rw [Rotate.revAt_zero]; exact items_keep hs hst.2
  · bud

theorem R7964.leaf_8004f69c_0 : LeafGoal R7964.plan R7964.plan.cuts[8]! (R7964.plan.leaves 0x8004f69c)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, hs, hM, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, G, as, ae, mid, ?_, hM, by regs_tac⟩
    rw [Rotate.rev_short (rev as (ae - as) G) (by omega)]; exact items_keep hs hst.2
  · bud

theorem R7964.leaf_8004f69c_1 : LeafGoal R7964.plan R7964.plan.cuts[8]! (R7964.plan.leaves 0x8004f69c)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, hs, hM, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, G, as, ae, mid, 0, ?_, hM, by omega, by regs_tac⟩
    rw [Rotate.revAt_zero]; exact items_keep hs hst.2
  · bud

theorem R7964.leaf_8004f890_0 : LeafGoal R7964.plan R7964.plan.cuts[10]! (R7964.plan.leaves 0x8004f890)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, hs, hM, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, G, as, ae, mid, ?_, hM, by regs_tac⟩
    unfold R3; rw [Rotate.rev_short (rev ae (mid - ae) (rev as (ae - as) G)) (by omega)]
    exact items_keep hs hst.2
  · bud

theorem R7964.leaf_8004f890_1 : LeafGoal R7964.plan R7964.plan.cuts[10]! (R7964.plan.leaves 0x8004f890)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, hs, hM, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, G, as, ae, mid, 0, ?_, hM, by omega, by regs_tac⟩
    rw [Rotate.revAt_zero]; exact items_keep hs hst.2
  · bud

/-! ## The swaps of the three reversals -/

theorem R7964.leaf_8004f4d0_0 : LeafGoal R7964.plan R7964.plan.cuts[7]! (R7964.plan.leaves 0x8004f4d0)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, i, hs, hM, hi, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_swap (e₁ := as + i) (e₂ := as + (ae - as - 1 - i)) hpre hcom hs (by omega) (by omega) (by omega)
    (by omega) (by omega) (hr.get (r := 28) (v := ptr m + w (32 * (as + i) + 15)) (by simp [eqM, eqB]))
    (by rw [show as + (ae - as - 1 - i) = ae - 1 - i by omega]
        exact hr.get (r := 29) (v := ptr m + w (32 * (ae - 1 - i) + 16)) (by simp [eqM, eqB]))
    hm' hso rfl (by decide) (by decide)
  have hit := items_rev hi hst.2
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, mid, i + 1, hit, hM, by omega, by regs_tac⟩
  · bud

theorem R7964.leaf_8004f4d0_1 : LeafGoal R7964.plan R7964.plan.cuts[7]! (R7964.plan.leaves 0x8004f4d0)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, i, hs, hM, hi, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_swap (e₁ := as + i) (e₂ := as + (ae - as - 1 - i)) hpre hcom hs (by omega) (by omega) (by omega)
    (by omega) (by omega) (hr.get (r := 28) (v := ptr m + w (32 * (as + i) + 15)) (by simp [eqM, eqB]))
    (by rw [show as + (ae - as - 1 - i) = ae - 1 - i by omega]
        exact hr.get (r := 29) (v := ptr m + w (32 * (ae - 1 - i) + 16)) (by simp [eqM, eqB]))
    hm' hso rfl (by decide) (by decide)
  have hit := items_rev hi hst.2
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, G, as, ae, mid, ?_, hM, by regs_tac⟩
    rw [← Rotate.revAt_full, show (ae - as) / 2 = i + 1 by omega]; exact hit
  · bud

theorem R7964.leaf_8004f6c4_0 : LeafGoal R7964.plan R7964.plan.cuts[9]! (R7964.plan.leaves 0x8004f6c4)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, i, hs, hM, hi, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_swap (e₁ := ae + i) (e₂ := ae + (mid - ae - 1 - i)) hpre hcom hs (by omega) (by omega) (by omega)
    (by omega) (by omega) (hr.get (r := 29) (v := ptr m + w (32 * (ae + i) + 15)) (by simp [eqM, eqB]))
    (by rw [show ae + (mid - ae - 1 - i) = mid - 1 - i by omega]
        exact hr.get (r := 30) (v := ptr m + w (32 * (mid - 1 - i) + 16)) (by simp [eqM, eqB]))
    hm' hso rfl (by decide) (by decide)
  have hit := items_rev hi hst.2
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, mid, i + 1, hit, hM, by omega, by regs_tac⟩
  · bud

theorem R7964.leaf_8004f6c4_1 : LeafGoal R7964.plan R7964.plan.cuts[9]! (R7964.plan.leaves 0x8004f6c4)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, i, hs, hM, hi, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_swap (e₁ := ae + i) (e₂ := ae + (mid - ae - 1 - i)) hpre hcom hs (by omega) (by omega) (by omega)
    (by omega) (by omega) (hr.get (r := 29) (v := ptr m + w (32 * (ae + i) + 15)) (by simp [eqM, eqB]))
    (by rw [show ae + (mid - ae - 1 - i) = mid - 1 - i by omega]
        exact hr.get (r := 30) (v := ptr m + w (32 * (mid - 1 - i) + 16)) (by simp [eqM, eqB]))
    hm' hso rfl (by decide) (by decide)
  have hit := items_rev hi hst.2
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, G, as, ae, mid, ?_, hM, by regs_tac⟩
    rw [← Rotate.revAt_full, show (mid - ae) / 2 = i + 1 by omega]; exact hit
  · bud

theorem R7964.leaf_8004f8ac_0 : LeafGoal R7964.plan R7964.plan.cuts[11]! (R7964.plan.leaves 0x8004f8ac)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, i, hs, hM, hi, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_swap (e₁ := as + i) (e₂ := as + (mid - as - 1 - i)) hpre hcom hs (by omega) (by omega) (by omega)
    (by omega) (by omega) (hr.get (r := 6) (v := ptr m + w (32 * (as + i) + 15)) (by simp [eqM, eqB]))
    (by rw [show as + (mid - as - 1 - i) = mid - 1 - i by omega]
        exact hr.get (r := 7) (v := ptr m + w (32 * (mid - 1 - i) + 16)) (by simp [eqM, eqB]))
    hm' hso rfl (by decide) (by decide)
  have hit := items_rev hi hst.2
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, mid, i + 1, hit, hM, by omega, by regs_tac⟩
  · bud

theorem R7964.leaf_8004f8ac_1 : LeafGoal R7964.plan R7964.plan.cuts[11]! (R7964.plan.leaves 0x8004f8ac)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, i, hs, hM, hi, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_swap (e₁ := as + i) (e₂ := as + (mid - as - 1 - i)) hpre hcom hs (by omega) (by omega) (by omega)
    (by omega) (by omega) (hr.get (r := 6) (v := ptr m + w (32 * (as + i) + 15)) (by simp [eqM, eqB]))
    (by rw [show as + (mid - as - 1 - i) = mid - 1 - i by omega]
        exact hr.get (r := 7) (v := ptr m + w (32 * (mid - 1 - i) + 16)) (by simp [eqM, eqB]))
    hm' hso rfl (by decide) (by decide)
  have hit := items_rev hi hst.2
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, G, as, ae, mid, ?_, hM, by regs_tac⟩
    unfold R3; rw [← Rotate.revAt_full, show (mid - as) / 2 = i + 1 by omega]; exact hit
  · bud

/-! ## `binaryFirst`: the copies into the frame -/

theorem R7964.leaf_8004f3fc_0 : LeafGoal R7964.plan R7964.plan.cuts[3]! (R7964.plan.leaves 0x8004f3fc)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, hFS, hsz, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hFS
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_copy (extra := []) (e := as) (d := 32) (keep := kS) hpre hcom hs (by omega)
    (hr.get (r := 6) (v := ptr m + w (32 * as)) (by simp [eqF, eqB])) hm' hso rfl (by decide)
    (by decide) (by decide) (by decide) rfl rfl (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr, size, hst.2.1, hFS, hsz, hst.2.2.1, by regs_tac⟩
  · bud

theorem R7964.leaf_8004f43c_0 : LeafGoal R7964.plan R7964.plan.cuts[4]! (R7964.plan.leaves 0x8004f43c)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, hFS, hsz, hv, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hFS
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_copy (extra := [(30, .ptr 0 0x20)]) (e := curr + size / 2) (d := 0) (keep := kHi) hpre hcom hs (by omega)
    (hr.get (r := 20) (v := ptr m + w (32 * (curr + size / 2))) (by simp [eqF, eqB])) hm' hso rfl
    (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr, size, 0, hst.2.1, hFS, hsz, by omega,
      fun j hj => ?_, fun j hj => by simpa using hst.2.2.1 j hj, fun j hj => absurd hj (by omega),
      by regs_tac⟩
    rw [hst.2.2.2 (32 + j) (by simp [kHi, List.mem_range']; omega)]; exact hv j hj
  · bud

/-! ## `binaryLast`: the copies into the frame -/

theorem R7964.leaf_8004fab0_0 : LeafGoal R7964.plan R7964.plan.cuts[13]! (R7964.plan.leaves 0x8004fab0)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, hLS, hsz, hr⟩ hc
  obtain ⟨⟨⟨r1, r2, r3, -⟩, has, -⟩, hlt, l1, l2, -, -⟩ := id hLS
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_copy (extra := []) (e := as) (d := 0) (keep := kS) hpre hcom hs (by omega)
    (hr.get (r := 17) (v := ptr m + w (32 * as)) (by simp [eqL, eqB])) hm' hso rfl (by decide)
    (by decide) (by decide) (by decide) rfl rfl (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr, size, hst.2.1, hLS, hsz,
      fun j hj => by simpa using hst.2.2.1 j hj, by regs_tac⟩
  · bud

theorem R7964.leaf_8004faf0_0 : LeafGoal R7964.plan R7964.plan.cuts[14]! (R7964.plan.leaves 0x8004faf0)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, hLS, hsz, hv, hr⟩ hc
  obtain ⟨⟨⟨r1, r2, r3, -⟩, has, -⟩, hlt, l1, l2, -, -⟩ := id hLS
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_copy (extra := [(28, .ptr 0 0x20)]) (e := curr + size / 2) (d := 32) (keep := kLo) hpre hcom hs (by omega)
    (hr.get (r := 18) (v := ptr m + w (32 * (curr + size / 2))) (by simp [eqL, eqB])) hm' hso rfl
    (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr, size, 0, hst.2.1, hLS, hsz, by omega,
      fun j hj => ?_, hst.2.2.1, fun j hj => absurd hj (by omega), by regs_tac⟩
    rw [hst.2.2.2 j (by simp [kLo, List.mem_range']; omega)]; exact hv j hj
  · bud

/-! ## Epilogue (`0x8004fb54`) -/

theorem R7964.leaf_8004fb54_0 : LeafGoal R7964.plan R7964.plan.cuts[17]! (R7964.plan.leaves 0x8004fb54)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, hs, hmg⟩ -
  refine ⟨?_, by simp, fun m' hm' he hso => ?_⟩
  · have := hpre.2.2.1
    simp [Oblig.holds, Sym.eval, BinOp.eval, envE, Env.setVars, entryEnv]
    simpa [RetAligned] using this
  · dsimp only at hm' he hso
    exit_intro
    exact epi_post hpre hcom hs hmg hm' hso he (by decide)

/-! ## Entry (`0x8004f388`): `A` empty, `B` empty, the first round -/

/-- A new round after `binaryLast` (the next round's `Q` plus a round's steps within this
round's `Q`). -/
theorem bud_step {A B R h : Nat} (hq : A + R ≤ B) : A + R + 20 ≤ B + 800 * h + 60 - 4 := by omega

theorem bud_entry {X Y : Nat} (h : X + Y + 100 ≤ 4611686018427387904) :
    X + Y + 20 ≤ 4611686018427387904 - (18 - 0) := by omega

theorem w_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : w a = w b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem R7964.leaf_8004f388_0 : LeafGoal R7964.plan R7964.plan.cuts[0]! (R7964.plan.leaves 0x8004f388)[0]! := by
  leaf_intro
  rintro m mh ⟨rfl, hpc, hpre⟩ hc
  refine ⟨?_, by simp [bound], fun m' hm' he hso => ?_⟩
  · have := hpre.2.2.1
    simp [Oblig.holds, Sym.eval, BinOp.eval, env0, entryEnv]
    simpa [RetAligned] using this
  · dsimp only at hm' he hso
    exit_intro
    refine early_post hpre hm' hso he rfl (by decide) (.inl ?_)
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, SBool.eval, env0_aS, env0_aE,
      beq_iff_eq] at hc
    exact (w_inj (u64_lt _ _) (u64_lt _ _) hc).symm

theorem R7964.leaf_8004f388_1 : LeafGoal R7964.plan R7964.plan.cuts[0]! (R7964.plan.leaves 0x8004f388)[1]! := by
  leaf_intro
  rintro m mh ⟨rfl, hpc, hpre⟩ hc
  refine ⟨?_, by simp [bound], fun m' hm' he hso => ?_⟩
  · have := hpre.2.2.1
    simp [Oblig.holds, Sym.eval, BinOp.eval, env0, entryEnv]
    simpa [RetAligned] using this
  · dsimp only at hm' he hso
    exit_intro
    refine early_post hpre hm' hso he rfl (by decide) (.inr ?_)
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
      env0_aS, env0_aE, env0_bS, env0_bE, beq_iff_eq] at hc
    exact (w_inj (u64_lt _ _) (u64_lt _ _) hc.2).symm

theorem R7964.leaf_8004f388_2 : LeafGoal R7964.plan R7964.plan.cuts[0]! (R7964.plan.leaves 0x8004f388)[2]! := by
  leaf_intro
  rintro m mh ⟨rfl, hpc, hpre⟩ hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    env0_aS, env0_aE, env0_bS, env0_bE, bne_iff_ne, ne_eq] at hc
  obtain ⟨hr1, hr2, hr3⟩ := pre_runs hpre
  have hne : aS mh ≠ aE mh := fun h => hc.1 (congrArg w h).symm
  have has : aS mh < aE mh := by omega
  have hfit := pre_hfit hpre
  have hbe := pre_bE hpre
  have hR : mh.reg 10 = ptr mh := rfl
  have hQ := Qf_entry (be := bE mh) (as := aS mh) (by omega)
  refine ⟨by simp, by simp [bound], fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := entry_step hpre hm' hso rfl rfl rfl rfl (by decide)
  simp only [ExitOk] at he
  have h13 : ix m' 13 = aS mh := by
    unfold ix; rw [reg_at hm' 13]
    simp (disch := decide) only [SState.reg, List.getD_cons_succ, List.getD_cons_zero,
      Nat.reduceEqDiff, if_false, env0_aS, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (u64_lt _ _)
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨⟨hpre, he, hst.1⟩, items mh (ptr mh), aS mh, aE mh, hst.2, round_init hpre, has, ?_⟩
    simp only [eqB, List.cons_append, List.nil_append, RegsAre]
    and_intros <;> first | exact True.intro | (rgoal0 <;> wgoal)
  · simp only [bOut, Q, Rb, N, bound, h13]
    exact bud_entry hQ

/-! ## After the rotation -/

theorem R7964.leaf_8004fa78_0 : LeafGoal R7964.plan R7964.plan.cuts[12]! (R7964.plan.leaves 0x8004fa78)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, hs, hM, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, R3 G as ae mid, items_keep hs hst.2,
      round_done (join_of_mid hM).1 (.inr (by omega))⟩
  · bud

theorem R7964.leaf_8004fa78_1 : LeafGoal R7964.plan R7964.plan.cuts[12]! (R7964.plan.leaves 0x8004fa78)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, hs, hM, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep0
  exfalso; omega

theorem R7964.leaf_8004fa78_3 : LeafGoal R7964.plan R7964.plan.cuts[12]! (R7964.plan.leaves 0x8004fa78)[3]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, mid, hs, hM, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hM
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, R3 G as ae mid, as + (mid - ae), mid, as + (mid - ae),
      mid - (as + (mid - ae)), items_keep hs hst.2, ⟨join_of_mid hM, by omega, last_init (by omega)⟩,
      by omega, by regs_tac⟩
  · have hq := Qf_le (be := bE m) (R := 2000 * (bE m - aS m) + 400)
      (show as ≤ mid - ae + as by omega)
    bud

/-! ## `binaryLast`: the latch -/

theorem R7964.leaf_8004faac_0 : LeafGoal R7964.plan R7964.plan.cuts[16]! (R7964.plan.leaves 0x8004faac)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, ⟨hJ, hlt, hl⟩, hsz, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  rw [show size / 2 = 0 by omega] at hl
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, items_keep hs hst.2,
      round_done (round_of_last hJ hl hlt) (.inl (by omega))⟩
  · bud

theorem R7964.leaf_8004faac_1 : LeafGoal R7964.plan R7964.plan.cuts[16]! (R7964.plan.leaves 0x8004faac)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, ⟨hJ, hlt, hl⟩, hsz, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  rw [show size / 2 = 0 by omega] at hl
  have hc1 := last_curr hl has
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, curr, ae, items_keep hs hst.2, round_of_last hJ hl hlt,
      by omega, by regs_tac⟩
  · have hq := Qf_step (be := bE m) (R := 2000 * (bE m - aS m) + 400) hc1 (show curr < bE m by omega)
    bud0
    simp (disch := omega) only [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left]
    exact bud_step hq

theorem R7964.leaf_8004faac_2 : LeafGoal R7964.plan R7964.plan.cuts[16]! (R7964.plan.leaves 0x8004faac)[2]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, hs, ⟨hJ, hlt, hl⟩, hsz, hr⟩ hc
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  lprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  nstep
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr, size / 2, items_keep hs hst.2, ⟨hJ, hlt, hl⟩,
      by omega, by regs_tac⟩
  · bud

/-! ## `binaryFirst`: the byte comparison (probe at `0`, value at `0x20`) -/

theorem R7964.leaf_8004f460_0 : LeafGoal R7964.plan R7964.plan.cuts[5]! (R7964.plan.leaves 0x8004f460)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, hs, hFS, hsz, hk, hv, hp, heq, hr⟩ hc
  obtain ⟨hRd, -, hf⟩ := id hFS
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hFS
  have b0 : (envC 31 30 mh).byte0 0 0 = G (curr + size / 2) k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 31) (v := frame cfg m + w k) (by simp [eqF, eqB]), hp k hk]; rfl
  have b1 : (envC 31 30 mh).byte0 1 0 = G as k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 30) (v := frame cfg m + w (32 + k)) (by simp [eqF, eqB]), hv k hk]; rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  lprep
  have hne : G (curr + size / 2) k ≠ G as k := fun h => by simp [h] at hc
  have hnlt : ¬ (G (curr + size / 2) k).toNat < (G as k).toNat := fun h => by simp [h] at hc
  have hlb : ltBy (cfg.key m) (el G (curr + size / 2)) (el G as) = false := by
    simp only [ltBy, cfg_key]; rw [cmp_ne heq hk hne]; simpa using hnlt
  have hf' := first_step (round_sortedB hRd) hf hsz
  rw [hlb] at hf'; simp only [Bool.false_eq_true, if_false] at hf'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr, size, items_keep hs hst.2, ⟨hRd, has, hf'⟩, hsz,
      by regs_tac⟩
  · bud

theorem R7964.leaf_8004f460_1 : LeafGoal R7964.plan R7964.plan.cuts[5]! (R7964.plan.leaves 0x8004f460)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, hs, hFS, hsz, hk, hv, hp, heq, hr⟩ hc
  obtain ⟨hRd, -, hf⟩ := id hFS
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hFS
  have b0 : (envC 31 30 mh).byte0 0 0 = G (curr + size / 2) k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 31) (v := frame cfg m + w k) (by simp [eqF, eqB]), hp k hk]; rfl
  have b1 : (envC 31 30 mh).byte0 1 0 = G as k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 30) (v := frame cfg m + w (32 + k)) (by simp [eqF, eqB]), hv k hk]; rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  lprep
  have hne : G (curr + size / 2) k ≠ G as k := fun h => by simp [h] at hc
  have hlt' : (G (curr + size / 2) k).toNat < (G as k).toNat := Classical.byContradiction fun h => by simp [h] at hc
  have hlb : ltBy (cfg.key m) (el G (curr + size / 2)) (el G as) = true := by
    simp only [ltBy, cfg_key]; rw [cmp_ne heq hk hne]; simpa using hlt'
  have hf' := first_step (round_sortedB hRd) hf hsz
  rw [hlb] at hf'; simp only [if_true] at hf'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr + size % 2 + size / 2, size, items_keep hs hst.2,
      ⟨hRd, has, hf'⟩, hsz, by regs_tac⟩
  · bud

theorem R7964.leaf_8004f460_2 : LeafGoal R7964.plan R7964.plan.cuts[5]! (R7964.plan.leaves 0x8004f460)[2]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, hs, hFS, hsz, hk, hv, hp, heq, hr⟩ hc
  obtain ⟨hRd, -, hf⟩ := id hFS
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hFS
  have b0 : (envC 31 30 mh).byte0 0 0 = G (curr + size / 2) k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 31) (v := frame cfg m + w k) (by simp [eqF, eqB]), hp k hk]; rfl
  have b1 : (envC 31 30 mh).byte0 1 0 = G as k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 30) (v := frame cfg m + w (32 + k)) (by simp [eqF, eqB]), hv k hk]; rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  lprep
  exfalso
  by_cases h : (G (curr + size / 2) k).toNat < (G as k).toNat <;> simp [h] at hc

theorem R7964.leaf_8004f460_3 : LeafGoal R7964.plan R7964.plan.cuts[5]! (R7964.plan.leaves 0x8004f460)[3]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, hs, hFS, hsz, hk, hv, hp, heq, hr⟩ hc
  obtain ⟨hRd, -, hf⟩ := id hFS
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hFS
  have b0 : (envC 31 30 mh).byte0 0 0 = G (curr + size / 2) k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 31) (v := frame cfg m + w k) (by simp [eqF, eqB]), hp k hk]; rfl
  have b1 : (envC 31 30 mh).byte0 1 0 = G as k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 30) (v := frame cfg m + w (32 + k)) (by simp [eqF, eqB]), hv k hk]; rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  lprep
  exfalso
  by_cases h : (G (curr + size / 2) k).toNat < (G as k).toNat <;> simp [h] at hc

theorem R7964.leaf_8004f460_4 : LeafGoal R7964.plan R7964.plan.cuts[5]! (R7964.plan.leaves 0x8004f460)[4]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, hs, hFS, hsz, hk, hv, hp, heq, hr⟩ hc
  obtain ⟨hRd, -, hf⟩ := id hFS
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hFS
  have b0 : (envC 31 30 mh).byte0 0 0 = G (curr + size / 2) k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 31) (v := frame cfg m + w k) (by simp [eqF, eqB]), hp k hk]; rfl
  have b1 : (envC 31 30 mh).byte0 1 0 = G as k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 30) (v := frame cfg m + w (32 + k)) (by simp [eqF, eqB]), hv k hk]; rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  lprep
  have hab : G (curr + size / 2) k = G as k := BitVec.eq_of_toNat_eq (by omega)
  have heq' : ∀ j < k + 1, G (curr + size / 2) j = G as j := fun j hj => by
    rcases Nat.lt_or_ge j k with h | h
    · exact heq j h
    · rw [show j = k by omega]; exact hab
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr, size, k + 1, items_keep hs hst.2, hFS, hsz, by omega,
      fun j hj => by rw [hst.2]; exact hv j hj, fun j hj => by rw [hst.2]; exact hp j hj, heq',
      by regs_tac⟩
  · bud

theorem R7964.leaf_8004f460_5 : LeafGoal R7964.plan R7964.plan.cuts[5]! (R7964.plan.leaves 0x8004f460)[5]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, hs, hFS, hsz, hk, hv, hp, heq, hr⟩ hc
  obtain ⟨hRd, -, hf⟩ := id hFS
  obtain ⟨⟨r1, r2, r3, -⟩, has, f1, f2, -, -⟩ := id hFS
  have b0 : (envC 31 30 mh).byte0 0 0 = G (curr + size / 2) k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 31) (v := frame cfg m + w k) (by simp [eqF, eqB]), hp k hk]; rfl
  have b1 : (envC 31 30 mh).byte0 1 0 = G as k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 30) (v := frame cfg m + w (32 + k)) (by simp [eqF, eqB]), hv k hk]; rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  lprep
  have hab : G (curr + size / 2) k = G as k := BitVec.eq_of_toNat_eq (by omega)
  have hk31 : k = 31 := by omega
  have hlb : ltBy (cfg.key m) (el G (curr + size / 2)) (el G as) = false := by
    simp only [ltBy, cfg_key]
    refine cmp_all fun j hj => ?_
    rcases Nat.lt_or_ge j k with h | h
    · exact heq j h
    · rw [show j = k by omega]; exact hab
  have hf' := first_step (round_sortedB hRd) hf hsz
  rw [hlb] at hf'; simp only [Bool.false_eq_true, if_false] at hf'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr, size, items_keep hs hst.2, ⟨hRd, has, hf'⟩, hsz,
      by regs_tac⟩
  · bud

/-! ## `binaryLast`: the byte comparison (value at `0`, probe at `0x20`) -/

theorem R7964.leaf_8004fb14_0 : LeafGoal R7964.plan R7964.plan.cuts[15]! (R7964.plan.leaves 0x8004fb14)[0]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, hs, hLS, hsz, hk, hv, hp, heq, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have b0 : (envC 29 28 mh).byte0 0 0 = G as k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 29) (v := frame cfg m + w k) (by simp [eqL, eqB]), hv k hk]; rfl
  have b1 : (envC 29 28 mh).byte0 1 0 = G (curr + size / 2) k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 28) (v := frame cfg m + w (32 + k)) (by simp [eqL, eqB]), hp k hk]; rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  lprep
  have hne : G as k ≠ G (curr + size / 2) k := fun h => by simp [h] at hc
  have hnlt : ¬ (G as k).toNat < (G (curr + size / 2) k).toNat := fun h => by simp [h] at hc
  have hlb : ltBy (cfg.key m) (el G as) (el G (curr + size / 2)) = false := by
    simp only [ltBy, cfg_key]; rw [cmp_ne heq hk hne]; simpa using hnlt
  have hl' := last_step (round_sortedA hJ.1) hl hsz
  rw [hlb] at hl'; simp only [Bool.false_eq_true, if_false] at hl'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr + size % 2 + size / 2, size, items_keep hs hst.2,
      ⟨hJ, hlt, hl'⟩, hsz, by regs_tac⟩
  · bud

theorem R7964.leaf_8004fb14_1 : LeafGoal R7964.plan R7964.plan.cuts[15]! (R7964.plan.leaves 0x8004fb14)[1]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, hs, hLS, hsz, hk, hv, hp, heq, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have b0 : (envC 29 28 mh).byte0 0 0 = G as k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 29) (v := frame cfg m + w k) (by simp [eqL, eqB]), hv k hk]; rfl
  have b1 : (envC 29 28 mh).byte0 1 0 = G (curr + size / 2) k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 28) (v := frame cfg m + w (32 + k)) (by simp [eqL, eqB]), hp k hk]; rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  lprep
  have hne : G as k ≠ G (curr + size / 2) k := fun h => by simp [h] at hc
  have hlt' : (G as k).toNat < (G (curr + size / 2) k).toNat := Classical.byContradiction fun h => by simp [h] at hc
  have hlb : ltBy (cfg.key m) (el G as) (el G (curr + size / 2)) = true := by
    simp only [ltBy, cfg_key]; rw [cmp_ne heq hk hne]; simpa using hlt'
  have hl' := last_step (round_sortedA hJ.1) hl hsz
  rw [hlb] at hl'; simp only [if_true] at hl'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr, size, items_keep hs hst.2, ⟨hJ, hlt, hl'⟩, hsz,
      by regs_tac⟩
  · bud

theorem R7964.leaf_8004fb14_2 : LeafGoal R7964.plan R7964.plan.cuts[15]! (R7964.plan.leaves 0x8004fb14)[2]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, hs, hLS, hsz, hk, hv, hp, heq, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have b0 : (envC 29 28 mh).byte0 0 0 = G as k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 29) (v := frame cfg m + w k) (by simp [eqL, eqB]), hv k hk]; rfl
  have b1 : (envC 29 28 mh).byte0 1 0 = G (curr + size / 2) k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 28) (v := frame cfg m + w (32 + k)) (by simp [eqL, eqB]), hp k hk]; rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  lprep
  exfalso
  by_cases h : (G as k).toNat < (G (curr + size / 2) k).toNat <;> simp [h] at hc

theorem R7964.leaf_8004fb14_3 : LeafGoal R7964.plan R7964.plan.cuts[15]! (R7964.plan.leaves 0x8004fb14)[3]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, hs, hLS, hsz, hk, hv, hp, heq, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have b0 : (envC 29 28 mh).byte0 0 0 = G as k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 29) (v := frame cfg m + w k) (by simp [eqL, eqB]), hv k hk]; rfl
  have b1 : (envC 29 28 mh).byte0 1 0 = G (curr + size / 2) k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 28) (v := frame cfg m + w (32 + k)) (by simp [eqL, eqB]), hp k hk]; rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  lprep
  exfalso
  by_cases h : (G as k).toNat < (G (curr + size / 2) k).toNat <;> simp [h] at hc

theorem R7964.leaf_8004fb14_4 : LeafGoal R7964.plan R7964.plan.cuts[15]! (R7964.plan.leaves 0x8004fb14)[4]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, hs, hLS, hsz, hk, hv, hp, heq, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have b0 : (envC 29 28 mh).byte0 0 0 = G as k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 29) (v := frame cfg m + w k) (by simp [eqL, eqB]), hv k hk]; rfl
  have b1 : (envC 29 28 mh).byte0 1 0 = G (curr + size / 2) k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 28) (v := frame cfg m + w (32 + k)) (by simp [eqL, eqB]), hp k hk]; rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  lprep
  have hab : G as k = G (curr + size / 2) k := BitVec.eq_of_toNat_eq (by omega)
  have heq' : ∀ j < k + 1, G as j = G (curr + size / 2) j := fun j hj => by
    rcases Nat.lt_or_ge j k with h | h
    · exact heq j h
    · rw [show j = k by omega]; exact hab
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr, size, k + 1, items_keep hs hst.2, hLS, hsz, by omega,
      fun j hj => by rw [hst.2]; exact hv j hj, fun j hj => by rw [hst.2]; exact hp j hj, heq',
      by regs_tac⟩
  · bud

theorem R7964.leaf_8004fb14_5 : LeafGoal R7964.plan R7964.plan.cuts[15]! (R7964.plan.leaves 0x8004fb14)[5]! := by
  leaf_intro
  rintro m mh ⟨⟨hpre, hpc, hcom⟩, G, as, ae, curr, size, k, hs, hLS, hsz, hk, hv, hp, heq, hr⟩ hc
  obtain ⟨hJ, hlt, hl⟩ := id hLS
  obtain ⟨⟨r1, r2, r3, -⟩, has, -⟩ := id hJ
  obtain ⟨l1, l2, -, -⟩ := id hl
  have b0 : (envC 29 28 mh).byte0 0 0 = G as k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 29) (v := frame cfg m + w k) (by simp [eqL, eqB]), hv k hk]; rfl
  have b1 : (envC 29 28 mh).byte0 1 0 = G (curr + size / 2) k := by
    simp only [envC, entryEnv, Env.byte0, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [hr.get (r := 28) (v := frame cfg m + w (32 + k)) (by simp [eqL, eqB]), hp k hk]; rfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    Sym.eval_bin, BinOp.eval, init1_eval, b0, b1, byte_word_ult, beq_iff_eq, bne_iff_ne, ne_eq,
    byte_word_eq] at hc
  lprep
  have hab : G as k = G (curr + size / 2) k := BitVec.eq_of_toNat_eq (by omega)
  have hk31 : k = 31 := by omega
  have hlb : ltBy (cfg.key m) (el G as) (el G (curr + size / 2)) = false := by
    simp only [ltBy, cfg_key]
    refine cmp_all fun j hj => ?_
    rcases Nat.lt_or_ge j k with h | h
    · exact heq j h
    · rw [show j = k by omega]; exact hab
  have hl' := last_step (round_sortedA hJ.1) hl hsz
  rw [hlb] at hl'; simp only [Bool.false_eq_true, if_false] at hl'
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  dsimp only at hm' he hso
  have hst := step_none hpre hcom (fun a => nw_C) hm' (entryEnv_vars_lt _ _) hso (by decide)
  simp only [ExitOk] at he
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨⟨hpre, he, hst.1⟩, G, as, ae, curr + size % 2 + size / 2, size, items_keep hs hst.2,
      ⟨hJ, hlt, hl'⟩, hsz, by regs_tac⟩
  · bud

zesu_assemble R7964

end ZesuExec.Fn.MergeInPlace.C7964
