import ZesuExec.Fn.Alloc.AllocP
import ZesuExec.Fn.Alloc.AllocPop
import ZesuExec.Fn.Alloc.AllocBump

/-! # `alloc`: the plan's leaves after the size-class search, by the lemmas of `AllocP`,
`AllocPop`, `AllocBump` -/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

theorem AllocF.leaf_800426a0_0 :
    LeafGoal AllocF.plan AllocF.plan.cuts[3]! (AllocF.plan.leaves 0x800426a0)[0]! :=
  leafPB_inf (by decide)

theorem AllocF.leaf_800426a0_1 :
    LeafGoal AllocF.plan AllocF.plan.cuts[3]! (AllocF.plan.leaves 0x800426a0)[1]! :=
  leafPB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem AllocF.leaf_800426a0_2 :
    LeafGoal AllocF.plan AllocF.plan.cuts[3]! (AllocF.plan.leaves 0x800426a0)[2]! :=
  leafPP1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem AllocF.leaf_800426a8_0 :
    LeafGoal AllocF.plan AllocF.plan.cuts[4]! (AllocF.plan.leaves 0x800426a8)[0]! :=
  leafPop (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem AllocF.leaf_80042740_0 :
    LeafGoal AllocF.plan AllocF.plan.cuts[7]! (AllocF.plan.leaves 0x80042740)[0]! :=
  leafRoundB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    fun env hc => .inl ⟨by decide, by decide, by
      have h := hc (SBool.eq (.bin .and (.init 0 0 8) (.bin .add (.var 13) (.lit 18446744073709551615))) (.lit 0)) (by decide)
      simpa [SBool.eval] using h⟩

theorem AllocF.leaf_80042740_1 :
    LeafGoal AllocF.plan AllocF.plan.cuts[7]! (AllocF.plan.leaves 0x80042740)[1]! :=
  leafRoundB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    fun env hc => .inr ⟨by decide, by decide, by decide, by
      have h := hc (SBool.ne (.bin .and (.init 0 0 8) (.bin .add (.var 13) (.lit 18446744073709551615))) (.lit 0)) (by decide)
      simpa [SBool.eval] using h⟩

theorem AllocF.leaf_800426e0_0 :
    LeafGoal AllocF.plan AllocF.plan.cuts[5]! (AllocF.plan.leaves 0x800426e0)[0]! :=
  leafRoundO (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    fun env hc => .inl ⟨by decide, by decide, by
      have h := hc (SBool.eq (.bin .and (.init 0 0 8) (.bin .add (.bin .sll (.lit 1) (.var 12)) (.lit 18446744073709551615))) (.lit 0)) (by decide)
      simpa [SBool.eval] using h⟩

theorem AllocF.leaf_800426e0_1 :
    LeafGoal AllocF.plan AllocF.plan.cuts[5]! (AllocF.plan.leaves 0x800426e0)[1]! :=
  leafRoundO (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    fun env hc => .inr ⟨by decide, by decide, by decide, by
      have h := hc (SBool.ne (.bin .and (.init 0 0 8) (.bin .add (.bin .sll (.lit 1) (.var 12)) (.lit 18446744073709551615))) (.lit 0)) (by decide)
      simpa [SBool.eval] using h⟩

theorem factsT (g : Sig) (m : Machine) (h : AT g m) : AllocPre g.L g.m ∧ Keep g m ∧ ∃ bytes p1,
    m.reg 11 = BitVec.ofNat 64 bytes ∧ cap (lenOf g) ≤ bytes ∧ bytes < 2 ^ 63 ∧ Rounded g m p1 := by
  obtain ⟨⟨hpre, -, hK⟩, -, -, k, p1, hok, h11, hR⟩ := h
  exact ⟨hpre, hK, classBytes k, p1, h11, cap_le_classBytes hok.1 hok.2.2,
    Nat.lt_of_le_of_lt (classBytes_le_24 hok.2.2) (by decide), hR⟩

theorem factsO2 (g : Sig) (m : Machine) (h : AO2 g m) : AllocPre g.L g.m ∧ Keep g m ∧ ∃ bytes p1,
    m.reg 11 = BitVec.ofNat 64 bytes ∧ cap (lenOf g) ≤ bytes ∧ bytes < 2 ^ 63 ∧ Rounded g m p1 := by
  obtain ⟨⟨hpre, -, hK⟩, h11, -, -, h22, p1, hR⟩ := h
  refine ⟨hpre, hK, lenOf g, p1, by rw [h11]; simp [lenOf], ?_, hpre.2.2.1, hR⟩
  unfold cap; unfold scOf at h22; rw [h22]; simp

theorem AllocF.leaf_80042760_0 :
    LeafGoal AllocF.plan AllocF.plan.cuts[8]! (AllocF.plan.leaves 0x80042760)[0]! :=
  leafBump (c := cT) rfl rfl
    (fun g m h => ⟨(AllocF.cut_80042760 g m h).1, (AllocF.cut_80042760 g m h).2.1⟩) factsT
    (by decide) (by decide) (fun _ _ => Nat.le_of_ble_eq_true rfl) (by decide) (by decide) (by decide)
    (.inl ⟨by decide, by decide, by decide, by decide⟩)

theorem AllocF.leaf_80042760_1 :
    LeafGoal AllocF.plan AllocF.plan.cuts[8]! (AllocF.plan.leaves 0x80042760)[1]! :=
  leafBump (c := cT) rfl rfl
    (fun g m h => ⟨(AllocF.cut_80042760 g m h).1, (AllocF.cut_80042760 g m h).2.1⟩) factsT
    (by decide) (by decide) (fun _ _ => Nat.le_of_ble_eq_true rfl) (by decide) (by decide) (by decide)
    (.inr ⟨by decide, by decide, by decide⟩)

theorem AllocF.leaf_80042708_0 :
    LeafGoal AllocF.plan AllocF.plan.cuts[6]! (AllocF.plan.leaves 0x80042708)[0]! :=
  leafBump (c := cO2) rfl rfl
    (fun g m h => ⟨(AllocF.cut_80042708 g m h).1, (AllocF.cut_80042708 g m h).2.1⟩) factsO2
    (by decide) (by decide) (fun _ _ => Nat.le_of_ble_eq_true rfl) (by decide) (by decide) (by decide)
    (.inl ⟨by decide, by decide, by decide, by decide⟩)

theorem AllocF.leaf_80042708_1 :
    LeafGoal AllocF.plan AllocF.plan.cuts[6]! (AllocF.plan.leaves 0x80042708)[1]! :=
  leafBump (c := cO2) rfl rfl
    (fun g m h => ⟨(AllocF.cut_80042708 g m h).1, (AllocF.cut_80042708 g m h).2.1⟩) factsO2
    (by decide) (by decide) (fun _ _ => Nat.le_of_ble_eq_true rfl) (by decide) (by decide) (by decide)
    (.inr ⟨by decide, by decide, by decide⟩)

end ZesuExec.Fn.Alloc
