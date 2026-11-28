import ZesuExec.Fn.Alloc.FreeLeaves
import ZesuExec.Fn.Alloc.AllocE

/-! # `free`: the 26 entry leaves (size-class search), by `leafFE` -/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

-- `cls_sem` of `AllocE` for `free`: length in `a2`, log2 alignment in `a3`.
set_option hygiene false in
macro "fcls_sem" : tactic => `(tactic| (
  intro g hpre hc
  have hx := hpre.2.2.1
  have ha := hpre.2.2.2.2.1
  simp only [SState.reg, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceEqDiff, ↓reduceIte,
    List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, SBool.eval, Sym.eval,
    BinOp.eval, envOf_vars, Fin.reduceOfNat, Fin.isValue, BitVec.ult, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, BitVec.toNat_ofNat] at hc ⊢
  unfold fsc falg flen
  rw [and63 ha] at hc
  generalize g.m.reg 13 = y at *
  generalize g.m.reg 12 = x at *
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

theorem FreeF.leaf_80041f38_0 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[0]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_1 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[1]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_2 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[2]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_3 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[3]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_4 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[4]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_5 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[5]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_6 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[6]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_7 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[7]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_8 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[8]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_9 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[9]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_10 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[10]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_11 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[11]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_12 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[12]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_13 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[13]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_14 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[14]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_15 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[15]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_16 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[16]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_17 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[17]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_18 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[18]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_19 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[19]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_20 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[20]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_21 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[21]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_22 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[22]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_23 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[23]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_24 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[24]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042130) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

theorem FreeF.leaf_80041f38_25 :
    LeafGoal FreeF.plan FreeF.plan.cuts[0]! (FreeF.plan.leaves 0x80041f38)[25]! := by
  leaf_intro
  refine leafFE (pcJ := 0x80042134) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  fcls_sem

end ZesuExec.Fn.Alloc
