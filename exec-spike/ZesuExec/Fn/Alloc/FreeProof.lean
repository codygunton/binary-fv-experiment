import ZesuExec.Fn.Alloc.FreeE
import ZesuExec.Sail.Run

/-!
# `FreeF.freef_spec`: `alt_fl_alloc.free` meets its contract over the free-list invariant

The second join's four leaves (oversized block: return; class in `a2` or `a3`: on to the push)
and the push leaf; `zesu_assemble FreeF` takes the 4 cut theorems and 32 leaf theorems and gives
`FreeF.reach` on `allocImage`; `runsIn_text` moves the run to `zesuImage`. `FreeF.freef_sail`:
the same at the Sail level.
-/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc ZesuExec.SailLink

theorem cls_lt22 {g : Sig} {m : Machine} {i : Fin 32} (hi : m.reg i = BitVec.ofNat 64 (fsc g))
    (h : BitVec.ult (m.reg i) (BitVec.ofNat 64 22) = true) : fsc g < 22 := by
  have := sc_le (flen g)
  rw [hi, BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by unfold fsc; omega)] at h
  exact h

theorem FreeF.leaf_80042134_0 :
    LeafGoal FreeF.plan FreeF.plan.cuts[2]! (FreeF.plan.leaves 0x80042134)[0]! := by
  leaf_intro
  exact leafFRet (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem FreeF.leaf_80042134_3 :
    LeafGoal FreeF.plan FreeF.plan.cuts[2]! (FreeF.plan.leaves 0x80042134)[3]! := by
  leaf_intro
  exact leafFRet (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem FreeF.leaf_80042134_1 :
    LeafGoal FreeF.plan FreeF.plan.cuts[2]! (FreeF.plan.leaves 0x80042134)[1]! := by
  leaf_intro
  refine leafFJ2F (i := 12) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (.inl rfl) (by decide) fun g m hA hc => ⟨hA.2.1, ?_⟩
  have h := hc (SBool.ltu (.var 12) (.lit 22)) (by decide)
  simp only [SBool.eval, Sym.eval, envOf_vars] at h
  exact cls_lt22 (i := 12) hA.2.1 h

theorem FreeF.leaf_80042134_2 :
    LeafGoal FreeF.plan FreeF.plan.cuts[2]! (FreeF.plan.leaves 0x80042134)[2]! := by
  leaf_intro
  refine leafFJ2F (i := 13) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (.inr rfl) (by decide) fun g m hA hc => ?_
  obtain ⟨⟨hpre, -⟩, -, h10, h13⟩ := hA
  have c1 := hc (SBool.ltu (.lit 3) (.var 10)) (by decide)
  have c2 := hc (SBool.ltu (.var 13) (.lit 22)) (by decide)
  simp only [SBool.eval, Sym.eval, envOf_vars] at c1 c2
  have hal := hpre.2.2.2.2.1
  have h4 : falg g = 4 := by
    rw [show (Fin.ofNat 32 10 : Fin 32) = 10 from rfl, h10, BitVec.ult, decide_eq_true_eq] at c1
    simp only [BitVec.toNat_ofNat] at c1
    unfold falg; omega
  have h1 : 1 ≤ fsc g := by
    rcases hpre.2.2.2.2.2.1 with h | h
    · unfold falg at h4; omega
    · exact sc_pos h
  have hr : m.reg 13 = BitVec.ofNat 64 (fsc g) := by rw [h13 h4, Nat.max_eq_left h1]
  exact ⟨hr, cls_lt22 (i := 13) hr c2⟩

theorem FreeF.leaf_80042170_0 :
    LeafGoal FreeF.plan FreeF.plan.cuts[3]! (FreeF.plan.leaves 0x80042170)[0]! := by
  leaf_intro
  exact leafFPush (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

zesu_assemble FreeF

theorem FreeF.freef_spec (L : List (Word × Nat)) :
    Spec zesuImage freeEntry 42 (FreePre L) (FreePost L) := fun m hpc hpre => by
  obtain ⟨k, m', hk, hr, hq⟩ :=
    FreeF.reach fE (by simp [FreeF.plan, freePlan]) ⟨L, m⟩ m ⟨rfl, hpc, hpre⟩
  exact ⟨k, m', hk, runsIn_text hr, hq⟩

theorem FreeF.freef_sail (L : List (Word × Nat)) {m : Machine} {s : BinaryFv.RiscV.State}
    (h : Rel zesuImage m s) (hpc : m.pc.toNat = freeEntry) (hpre : FreePre L m) :
    SailReaches zesuImage 42 (fun s' => ∃ m', Rel zesuImage m' s' ∧ FreePost L m m') s :=
  sail_reaches h (FreeF.freef_spec L m hpc hpre)

/--
info: 'ZesuExec.Fn.Alloc.FreeF.freef_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FreeF.freef_spec

end ZesuExec.Fn.Alloc
