import ZesuExec.Fn.Alloc.AllocVc

/-! # `alloc`: the 26 entry leaves (size-class search), by `leafE` -/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- The size class an entry leaf computes, under its conditions on `len` (`sizeClassOfBytes`
unfolded to the interval the conditions fix), and the alignment test of its last condition. -/
macro "sc_tac" : tactic => `(tactic| (unfold sizeClassOfBytes; repeat' split) <;> omega)

set_option hygiene false in
macro "cls_sem" : tactic => `(tactic| (
  intro g hpre hc
  have hx := hpre.2.2.1
  have ha := hpre.2.2.2.1
  simp only [SState.reg, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceEqDiff, ↓reduceIte,
    List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, SBool.eval, Sym.eval,
    BinOp.eval, envOf_vars, Fin.reduceOfNat, Fin.isValue, BitVec.ult, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, BitVec.toNat_ofNat] at hc ⊢
  unfold scOf alOf lenOf
  rw [and63 ha] at hc
  generalize g.m.reg 12 = y at *
  generalize g.m.reg 11 = x at *
  generalize hX : x.toNat = X at *
  have hsl := sc_le X
  try (split <;> rename_i hs <;> simp only [hs, ↓reduceIte] at hc)
  all_goals simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, BitVec.reduceXOr,
    BitVec.reduceSub, BitVec.ofNat_eq_ofNat] at *
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.reduceMod]
       rw [Nat.mod_eq_of_lt (by omega)]; sc_tac)
    | (intro h1 h2; first | exact h1.elim | (
        have hy : y = 4#64 := BitVec.eq_of_toNat_eq (by simp [h2])
        subst hy
        simp only [BitVec.reduceAdd, BitVec.toNat_ofNat, Nat.reduceMod] at hc
        sc_tac))))

theorem AllocF.leaf_80042494_0 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[0]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_1 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[1]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_2 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[2]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_3 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[3]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_4 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[4]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_5 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[5]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_6 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[6]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_7 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[7]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_8 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[8]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_9 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[9]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_10 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[10]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_11 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[11]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_12 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[12]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_13 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[13]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_14 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[14]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_15 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[15]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_16 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[16]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_17 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[17]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_18 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[18]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_19 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[19]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_20 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[20]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_21 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[21]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_22 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[22]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_23 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[23]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_24 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[24]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_25 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[25]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

end ZesuExec.Fn.Alloc
