import ZesuExec.Fn.Rotate.C8330.Vc

/-!
# `mem.rotate__anon_8330`: cut lemmas and leaves

Every item by the shared lemmas of `Fn/Rotate/Cuts.lean` and tactics of `Fn/Rotate/Tac.lean`;
what is this copy's: the cut indices, the inner loops' byte registers, the new loop counters.
-/

namespace ZesuExec.Fn.Rotate.C8330
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Fn.Rotate

/-! ## Cut points -/

theorem R8330.cut_8006464c : CutOK R8330.plan R8330.plan.cuts[0]! := by
  cut_intro; rintro m mh ⟨rfl, hpc, hpre⟩
  exact ⟨(cut0_facts hpre).1, (cut0_facts hpre).2, hpre.1, hpc⟩

theorem R8330.cut_80064688 : CutOK R8330.plan R8330.plan.cuts[1]! := by
  cut_intro; rintro m mh ⟨-, hpc, hcom, -⟩; exact ⟨cutO_facts.1, cutO_facts.2, hcom.1, hpc⟩
theorem R8330.cut_800646f8 : CutOK R8330.plan R8330.plan.cuts[3]! := by
  cut_intro; rintro m mh ⟨-, hpc, hcom, -⟩; exact ⟨cutO_facts.1, cutO_facts.2, hcom.1, hpc⟩
theorem R8330.cut_80064758 : CutOK R8330.plan R8330.plan.cuts[5]! := by
  cut_intro; rintro m mh ⟨-, hpc, hcom, -⟩; exact ⟨cutO_facts.1, cutO_facts.2, hcom.1, hpc⟩

theorem R8330.cut_8006469c : CutOK R8330.plan R8330.plan.cuts[2]! := by
  cut_intro; rintro m mh ⟨hpre, hpc, hcom, i, k, hi2, hk, hs, hlo, hhi, -⟩
  have h := cutI_facts hpre (by decide) (by decide) hi2 hk hs hlo hhi
  exact ⟨h.1, h.2, hcom.1, hpc⟩
theorem R8330.cut_8006470c : CutOK R8330.plan R8330.plan.cuts[4]! := by
  cut_intro; rintro m mh ⟨hpre, hpc, hcom, i, k, hi2, hk, hs, hlo, hhi, -⟩
  have h := cutI_facts hpre (by decide) (by decide) hi2 hk hs hlo hhi
  exact ⟨h.1, h.2, hcom.1, hpc⟩
theorem R8330.cut_8006476c : CutOK R8330.plan R8330.plan.cuts[6]! := by
  cut_intro; rintro m mh ⟨hpre, hpc, hcom, i, k, hi2, hk, hs, hlo, hhi, -⟩
  have h := cutI_facts hpre (by decide) (by decide) hi2 hk hs hlo hhi
  exact ⟨h.1, h.2, hcom.1, hpc⟩

theorem R8330.cut_80064798 : CutOK R8330.plan R8330.plan.cuts[7]! := by
  cut_intro; rintro m mh ⟨hpre, hpc, hcom, -⟩
  exact ⟨(cutE_facts hpre hcom).1, (cutE_facts hpre hcom).2, hcom.1, hpc⟩

/-! ## Entry (`0x8006464c`): to the epilogue, the third, second, first reversal -/

theorem R8330.leaf_8006464c_0 : LeafGoal R8330.plan R8330.plan.cuts[0]! (R8330.plan.leaves 0x8006464c)[0]! := by
  eprep
  refine ⟨by simp, by simp [bound], fun m' hm' he hso => ?_⟩
  estep
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨hpre, he, hst.1, ?_⟩
    rw [G3, rev_short _ (by omega), G2, rev_short _ (by omega), G1, rev_short _ (by omega)]
    exact hst.2
  · simp [bound]

theorem R8330.leaf_8006464c_1 : LeafGoal R8330.plan R8330.plan.cuts[0]! (R8330.plan.leaves 0x8006464c)[1]! := by
  eprep
  refine ⟨by simp, by simp [bound], fun m' hm' he hso => ?_⟩
  estep
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨hpre, he, hst.1, 0, by simp [Ph.L]; omega, ?_, by regs_tac⟩
    rw [revAt_zero]
    show SliceIs _ _ _ _ (G2 cfg mh)
    rw [G2, rev_short _ (by omega), G1, rev_short _ (by omega)]
    exact hst.2
  · bud

theorem R8330.leaf_8006464c_2 : LeafGoal R8330.plan R8330.plan.cuts[0]! (R8330.plan.leaves 0x8006464c)[2]! := by
  eprep
  refine ⟨by simp, by simp [bound], fun m' hm' he hso => ?_⟩
  estep
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨hpre, he, hst.1, 0, by simp [Ph.L]; omega, ?_, by regs_tac⟩
    rw [revAt_zero]
    show SliceIs _ _ _ _ (G1 cfg mh)
    rw [G1, rev_short _ (by omega)]
    exact hst.2
  · bud

theorem R8330.leaf_8006464c_3 : LeafGoal R8330.plan R8330.plan.cuts[0]! (R8330.plan.leaves 0x8006464c)[3]! := by
  eprep
  refine ⟨by simp, by simp [bound], fun m' hm' he hso => ?_⟩
  estep
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨hpre, he, hst.1, 0, by simp [Ph.L]; omega, ?_, by regs_tac⟩
    rw [revAt_zero]
    exact hst.2
  · bud

/-! ## Outer loop heads: to the inner loop -/

theorem R8330.leaf_80064688_0 : LeafGoal R8330.plan R8330.plan.cuts[1]! (R8330.plan.leaves 0x80064688)[0]! := by
  oprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  ostep
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, i, 0, hi2, by simp [cfg], hst.2, by rgoal <;> wgoal,
      by rgoal <;> wgoal, by regs_tac⟩
  · bud

theorem R8330.leaf_800646f8_0 : LeafGoal R8330.plan R8330.plan.cuts[3]! (R8330.plan.leaves 0x800646f8)[0]! := by
  oprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  ostep
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, i, 0, hi2, by simp [cfg], hst.2, by rgoal <;> wgoal,
      by rgoal <;> wgoal, by regs_tac⟩
  · bud

theorem R8330.leaf_80064758_0 : LeafGoal R8330.plan R8330.plan.cuts[5]! (R8330.plan.leaves 0x80064758)[0]! := by
  oprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  ostep
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, i, 0, hi2, by simp [cfg], hst.2, by rgoal <;> wgoal,
      by rgoal <;> wgoal, by regs_tac⟩
  · bud

/-! ## Inner loops: the back edge -/

theorem R8330.leaf_8006469c_0 : LeafGoal R8330.plan R8330.plan.cuts[2]! (R8330.plan.leaves 0x8006469c)[0]! := by
  iprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  istep
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, i, k + 1, hi2, by simp [cfg]; omega, hst.2, by rgoal <;> wgoal,
      by rgoal <;> wgoal, by regs_tac⟩
  · bud

theorem R8330.leaf_8006470c_0 : LeafGoal R8330.plan R8330.plan.cuts[4]! (R8330.plan.leaves 0x8006470c)[0]! := by
  iprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  istep
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, i, k + 1, hi2, by simp [cfg]; omega, hst.2, by rgoal <;> wgoal,
      by rgoal <;> wgoal, by regs_tac⟩
  · bud

theorem R8330.leaf_8006476c_0 : LeafGoal R8330.plan R8330.plan.cuts[6]! (R8330.plan.leaves 0x8006476c)[0]! := by
  iprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  istep
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, i, k + 1, hi2, by simp [cfg]; omega, hst.2, by rgoal <;> wgoal,
      by rgoal <;> wgoal, by regs_tac⟩
  · bud

/-! ## Inner loops: the next element pair -/

theorem R8330.leaf_8006469c_1 : LeafGoal R8330.plan R8330.plan.cuts[2]! (R8330.plan.leaves 0x8006469c)[1]! := by
  iprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  istep
  have hkE : k + 1 = cfg.E := by simp [cfg]; omega
  rw [hkE] at hst
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, i + 1, by simp [Ph.L]; omega, slice_next hst.2 hi2, by regs_tac⟩
  · bud

theorem R8330.leaf_8006470c_1 : LeafGoal R8330.plan R8330.plan.cuts[4]! (R8330.plan.leaves 0x8006470c)[1]! := by
  iprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  istep
  have hkE : k + 1 = cfg.E := by simp [cfg]; omega
  rw [hkE] at hst
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, i + 1, by simp [Ph.L]; omega, slice_next hst.2 hi2, by regs_tac⟩
  · bud

theorem R8330.leaf_8006476c_1 : LeafGoal R8330.plan R8330.plan.cuts[6]! (R8330.plan.leaves 0x8006476c)[1]! := by
  iprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  istep
  have hkE : k + 1 = cfg.E := by simp [cfg]; omega
  rw [hkE] at hst
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, i + 1, by simp [Ph.L]; omega, slice_next hst.2 hi2, by regs_tac⟩
  · bud

/-! ## Inner loops: a reversal ends -/

theorem R8330.leaf_8006469c_2 : LeafGoal R8330.plan R8330.plan.cuts[2]! (R8330.plan.leaves 0x8006469c)[2]! := by
  iprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  istep
  have hkE : k + 1 = cfg.E := by simp [cfg]; omega
  rw [hkE] at hst
  have hend := slice_end hst.2 hi2 (by simp [Ph.L]; omega)
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨hpre, he, hst.1, ?_⟩
    rw [G3, rev_short _ (by omega), G2, rev_short _ (by omega)]
    exact hend
  · bud

theorem R8330.leaf_8006469c_3 : LeafGoal R8330.plan R8330.plan.cuts[2]! (R8330.plan.leaves 0x8006469c)[3]! := by
  iprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  istep
  have hkE : k + 1 = cfg.E := by simp [cfg]; omega
  rw [hkE] at hst
  have hend := slice_end hst.2 hi2 (by simp [Ph.L]; omega)
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨hpre, he, hst.1, 0, by simp [Ph.L]; omega, ?_, by regs_tac⟩
    rw [revAt_zero]
    show SliceIs _ _ _ _ (G2 cfg m)
    rw [G2, rev_short _ (by omega)]
    exact hend
  · bud

theorem R8330.leaf_8006469c_4 : LeafGoal R8330.plan R8330.plan.cuts[2]! (R8330.plan.leaves 0x8006469c)[4]! := by
  iprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  istep
  have hkE : k + 1 = cfg.E := by simp [cfg]; omega
  rw [hkE] at hst
  have hend := slice_end hst.2 hi2 (by simp [Ph.L]; omega)
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨hpre, he, hst.1, 0, by simp [Ph.L]; omega, ?_, by regs_tac⟩
    rw [revAt_zero]
    exact hend
  · bud

theorem R8330.leaf_8006470c_2 : LeafGoal R8330.plan R8330.plan.cuts[4]! (R8330.plan.leaves 0x8006470c)[2]! := by
  iprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  istep
  have hkE : k + 1 = cfg.E := by simp [cfg]; omega
  rw [hkE] at hst
  have hend := slice_end hst.2 hi2 (by simp [Ph.L]; omega)
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨hpre, he, hst.1, ?_⟩
    rw [G3, rev_short _ (by omega)]
    exact hend
  · bud

theorem R8330.leaf_8006470c_3 : LeafGoal R8330.plan R8330.plan.cuts[4]! (R8330.plan.leaves 0x8006470c)[3]! := by
  iprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  istep
  have hkE : k + 1 = cfg.E := by simp [cfg]; omega
  rw [hkE] at hst
  have hend := slice_end hst.2 hi2 (by simp [Ph.L]; omega)
  exit_intro
  all_goals dsimp only
  · exact he
  · refine ⟨hpre, he, hst.1, 0, by simp [Ph.L]; omega, ?_, by regs_tac⟩
    rw [revAt_zero]
    exact hend
  · bud

theorem R8330.leaf_8006476c_2 : LeafGoal R8330.plan R8330.plan.cuts[6]! (R8330.plan.leaves 0x8006476c)[2]! := by
  iprep
  refine ⟨by simp, by bud, fun m' hm' he hso => ?_⟩
  istep
  have hkE : k + 1 = cfg.E := by simp [cfg]; omega
  rw [hkE] at hst
  have hend := slice_end hst.2 hi2 (by simp [Ph.L]; omega)
  exit_intro
  all_goals dsimp only
  · exact he
  · exact ⟨hpre, he, hst.1, hend⟩
  · bud

/-! ## Epilogue (`0x80064798`) -/

theorem R8330.leaf_80064798_0 : LeafGoal R8330.plan R8330.plan.cuts[7]! (R8330.plan.leaves 0x80064798)[0]! := by
  leaf_intro
  rintro m mh ⟨hpre, hpc, hcom, hs⟩ -
  refine ⟨?_, by simp, fun m' hm' he hso => ?_⟩
  · have := hpre.2.2.1
    simp [Oblig.holds, Sym.eval, BinOp.eval, envE, Env.setVars, entryEnv]
    simpa [RetAligned] using this
  · dsimp only at hm' he hso
    exit_intro
    exact epi_post hpre hcom hs hm' hso he (by decide)

zesu_assemble R8330

end ZesuExec.Fn.Rotate.C8330
