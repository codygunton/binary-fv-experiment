import ZesuExec.Fn.Alloc.AllocVc
import ZesuExec.Fn.Alloc.Lemmas

/-! # `alloc`: the leaves from the two joins of the size-class search -/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

theorem toNat_ofNat_small {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem shl3_add {kv : Nat} (hk : kv < 22) :
    BinOp.eval .add (BinOp.eval .sll (BitVec.ofNat 64 kv) (BitVec.ofNat 64 3))
      (BitVec.ofNat 64 0xa0534000) = BitVec.ofNat 64 (0xa0534000 + 8 * kv) := by
  show (BitVec.ofNat 64 kv <<< (3 % 64)) + BitVec.ofNat 64 0xa0534000 = _
  apply BitVec.eq_of_toNat_eq
  have e1 : (BitVec.ofNat 64 kv <<< (3 % 64)).toNat = kv * 8 := by
    rw [BitVec.toNat_shiftLeft, toNat_ofNat_small (by omega), Nat.shiftLeft_eq,
      show 2 ^ (3 % 64) = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, e1, toNat_ofNat_small (by omega), toNat_ofNat_small (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem AllocF.leaf_8004267c_0 :
    LeafGoal AllocF.plan AllocF.plan.cuts[1]! (AllocF.plan.leaves 0x8004267c)[0]! := by
  leaf_intro
  intro g m hA _
  obtain ⟨⟨hpre, -, hK⟩, hmem, h11, h12, h10, h14, hal⟩ := hA
  refine ⟨by simp, Nat.le_of_ble_eq_true rfl, fun m' hm' he hso => ?_⟩
  have hmm := mem_of_noRegions rfl hso
  have hK' := keep_of hm' (by decide) (envOf_var (fun _ => []) g m) hK
  have hpc : m'.pc.toNat = 0x80042680 := he
  refine ExitGoal.at_cut rfl ⟨cJ2, by simp [AllocF.plan, allocPlan], hpc, ⟨⟨hpre, hpc, hK'⟩, hmm.trans hmem,
    ?_, ?_, ?_, fun h4 => ?_⟩, Nat.le_of_ble_eq_true rfl⟩
  · exact (reg_var hm' 11 rfl).trans h11
  · exact (reg_var hm' 12 rfl).trans h12
  · exact (reg_var hm' 10 rfl).trans h10
  · rw [show m'.reg 13 = m.reg 14 from Match.reg_of hm' 13 (.var 14) rfl, h14]
    have h1 := hal h4
    have h4' : g.m.reg 12 = 4#64 := BitVec.eq_of_toNat_eq (by simp [alOf] at h4; simp [h4])
    rw [h4', Nat.max_eq_right h1]; rfl

/-- A leaf from the second join to the head cell (`0x800426a0`) with class `a3 = kv`. -/
theorem leafJ2P {l : Leaf} (hex : l.exit = .at 0x800426a0) (hst : l.S.steps ≤ 9)
    (hob : l.obligs = []) (hkeep : ∀ i ∈ 12 :: keepRegs, l.S.reg i = .var i) {i : Nat}
    (hi : i = 10 ∨ i = 13)
    (h13 : l.S.reg 13 = .var i)
    (h11 : l.S.reg 11 = .bin .add (.bin .sll (.var i) (.lit 3)) (.lit 0xa0534000))
    (hsem : ∀ g m, AJ2 g m → (∀ b ∈ l.conds, b.eval (envOf (fun _ => []) g m) = true) →
      ∃ kv, m.reg ⟨i, by omega⟩ = BitVec.ofNat 64 kv ∧ ClassOk g kv) :
    LeafGoal allocPlan cJ2 l := by
  intro g m hA hc
  obtain ⟨kv, hkv, hok⟩ := hsem g m hA hc
  obtain ⟨⟨hpre, -, hK⟩, hmem, -, h12, -⟩ := hA
  refine ⟨by rw [hob]; simp, by show l.S.steps - 0 ≤ 31; omega, fun m' hm' he hso => ?_⟩
  have hmm := mem_of_noRegions (S := cJ2.S) rfl hso
  have hK' := keep_of hm' (fun j hj => hkeep j (List.mem_cons_of_mem _ hj))
    (envOf_var (fun _ => []) g m) hK
  rw [hex] at he ⊢
  have hpc : m'.pc.toNat = 0x800426a0 := he
  have hvi : Sym.eval (cJ2.env g m) (.var i) = BitVec.ofNat 64 kv := by
    rw [← hkv]; rcases hi with rfl | rfl <;> rfl
  have r13 : m'.reg 13 = BitVec.ofNat 64 kv := by rw [Match.reg_of hm' 13 _ h13, hvi]
  have hk13 : (m'.reg 13).toNat = kv := by rw [r13, toNat_ofNat_small (by unfold ClassOk at hok; omega)]
  refine ExitGoal.at_cut rfl ⟨cP, by simp [allocPlan], hpc, ⟨⟨hpre, hpc, hK'⟩, hmm.trans hmem,
    ?_, by rw [hk13]; exact hok, ?_⟩, by show 22 ≤ 31 - (l.S.steps - 0); omega⟩
  · exact (reg_var hm' 12 (hkeep 12 (List.mem_cons_self ..))).trans h12
  · rw [Match.reg_of hm' 11 _ h11, hk13, Sym.eval_bin, Sym.eval_bin, hvi, Sym.eval_lit,
      Sym.eval_lit]
    exact shl3_add hok.2.2

/-- A leaf from the second join to the oversized path (`0x800426e0`). -/
theorem leafJ2O {l : Leaf} (hex : l.exit = .at 0x800426e0) (hst : l.S.steps ≤ 16)
    (hob : l.obligs = []) (hkeep : ∀ i ∈ 11 :: 12 :: keepRegs, l.S.reg i = .var i)
    (h13 : l.S.reg 13 = .lit 0xa0d346dc)
    (hsem : ∀ g m, AJ2 g m → (∀ b ∈ l.conds, b.eval (envOf (fun _ => []) g m) = true) →
      scOf g = 22) :
    LeafGoal allocPlan cJ2 l := by
  intro g m hA hc
  have h22 := hsem g m hA hc
  obtain ⟨⟨hpre, -, hK⟩, hmem, h11, h12, -⟩ := hA
  refine ⟨by rw [hob]; simp, by show l.S.steps - 0 ≤ 31; omega, fun m' hm' he hso => ?_⟩
  have hmm := mem_of_noRegions (S := cJ2.S) rfl hso
  have hK' := keep_of hm' (fun j hj => hkeep j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)))
    (envOf_var (fun _ => []) g m) hK
  rw [hex] at he ⊢
  have hpc : m'.pc.toNat = 0x800426e0 := he
  refine ExitGoal.at_cut rfl ⟨cO, by simp [allocPlan], hpc, ⟨⟨hpre, hpc, hK'⟩, hmm.trans hmem,
    ?_, ?_, by rw [Match.reg_of hm' 13 _ h13]; rfl, h22⟩, by show 15 ≤ 31 - (l.S.steps - 0); omega⟩
  · exact (reg_var hm' 11 (hkeep 11 (List.mem_cons_self ..))).trans h11
  · exact (reg_var hm' 12 (hkeep 12 (by simp))).trans h12

set_option hygiene false in
macro "j2_sem" : tactic => `(tactic| (
  intro g m hA hc
  obtain ⟨⟨hpre, -, -⟩, -, -, h12, h10, h13⟩ := hA
  have ha := hpre.2.2.2.1
  have hsl := sc_le (lenOf g)
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, SBool.eval,
    Sym.eval, envOf_vars, Fin.reduceOfNat, Fin.isValue, BitVec.ult, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, BitVec.toNat_ofNat, Nat.reduceMod, h12, h10] at hc
  unfold alOf at h13
  unfold scOf at *))

theorem AllocF.leaf_80042680_0 :
    LeafGoal AllocF.plan AllocF.plan.cuts[2]! (AllocF.plan.leaves 0x80042680)[0]! := by
  leaf_intro
  refine leafJ2P (i := 10) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  j2_sem
  refine ⟨_, h10, ?_, ?_, ?_⟩
  · rw [Nat.mod_eq_of_lt (by omega)] at hc; (try simp only [scOf, alOf] at *); omega
  · unfold alOf; (try simp only [scOf, alOf] at *); omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hc; (try simp only [scOf, alOf] at *); omega

theorem AllocF.leaf_80042680_1 :
    LeafGoal AllocF.plan AllocF.plan.cuts[2]! (AllocF.plan.leaves 0x80042680)[1]! := by
  leaf_intro
  refine leafJ2O (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  j2_sem
  rw [Nat.mod_eq_of_lt (by omega)] at hc; (try simp only [scOf, alOf] at *); omega

theorem AllocF.leaf_80042680_2 :
    LeafGoal AllocF.plan AllocF.plan.cuts[2]! (AllocF.plan.leaves 0x80042680)[2]! := by
  leaf_intro
  refine leafJ2O (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  j2_sem
  have h4 : (g.m.reg 12).toNat = 4 := by omega
  rw [h13 h4, toNat_ofNat_small (by omega)] at hc
  (try simp only [scOf, alOf] at *); omega

theorem AllocF.leaf_80042680_3 :
    LeafGoal AllocF.plan AllocF.plan.cuts[2]! (AllocF.plan.leaves 0x80042680)[3]! := by
  leaf_intro
  refine leafJ2P (i := 13) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  j2_sem
  have h4 : (g.m.reg 12).toNat = 4 := by omega
  rw [h13 h4, toNat_ofNat_small (by omega)] at hc
  refine ⟨_, h13 h4, ?_, ?_, ?_⟩
  · (try simp only [scOf, alOf] at *); omega
  · unfold alOf; (try simp only [scOf, alOf] at *); omega
  · (try simp only [scOf, alOf] at *); omega

end ZesuExec.Fn.Alloc
