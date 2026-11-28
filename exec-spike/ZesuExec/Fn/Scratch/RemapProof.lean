import ZesuExec.Fn.Scratch.FreeProof

/-!
# `scratch_arena.remap` (`0x800db944`, 35 instructions) meets `RemapPre`/`RemapPost`

Plan `RS`: the entry (budget 22) and `0x800db94c` after the null test (budget 20; region 0 the
newest chunk's `cap` and `used` words, region 1 the frame). Seven leaves. End theorems
`RS.rs_spec` and `RS.rs_sail` (in the plan's namespace, named after it, where `zesu-status` looks).
-/

namespace ZesuExec.Fn.Scratch
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc ZesuExec.Fn.Alloc

def rsAE (e m : Machine) : Prop := m = e ∧ m.pc.toNat = remapEntry ∧ RemapPre e
def rsAJ (e m : Machine) : Prop :=
  RemapPre e ∧ m.pc.toNat = remapJ ∧ m.mem = e.mem ∧ (∀ i : Fin 32, i.val ≠ 13 → m.reg i = e.reg i) ∧
    m.reg 13 = chunks e ∧ chunks e ≠ 0

def shapeRJ (m : Machine) : Shape := [((m.reg 13 + 8, 16), capR), ((m.reg 2 - 16, 16), frameR)]

def rsE : Cut Machine := ⟨0x800db944, SE, rsAE, envS shapeE, fun _ _ => 22⟩
def rsJ : Cut Machine := ⟨0x800db94c, SRJ, rsAJ, envS shapeRJ, fun _ _ => 20⟩

def rsPlan : Plan Machine allocImage where
  cuts := [rsE, rsJ]
  fuel := 48
  leaves := fun pc => if pc = 0x800db944 then rsRunE_leaves else if pc = 0x800db94c then rsRunJ_leaves
    else []
  callee := fun _ => none
  Post := RemapPost

zesu_plan RS := rsPlan

theorem RS.cut_800db944 : CutOK RS.plan RS.plan.cuts[0]! :=
  cutE fun _ _ h => by obtain ⟨rfl, hpc, hpre⟩ := h; exact ⟨hpre.2.1, hpc⟩

theorem RS.cut_800db94c : CutOK RS.plan RS.plan.cuts[1]! :=
  cutOK_S (sh := shapeRJ) (fun _ => rfl) fun e m h => by
    obtain ⟨hpre, hpc, hmem, hreg, h13, hne⟩ := h
    obtain ⟨hstk, hR, hP, hd⟩ := hpre.2.2 hne
    have h2 : m.reg 2 = e.reg 2 := hreg 2 (by decide)
    have hstk' := stack_same hstk h2 hmem
    refine ⟨?_, ?_, fun i hi s hs => ?_, fun r j hr hj => ?_, hpc⟩
    · simp only [shapeRJ, List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · rw [h13]; exact regionOk_cap hR.1 hR.2
      · exact regionOk_frame hstk'
    · simp only [shapeRJ, List.map_cons, List.map_nil, List.pairwise_cons, List.mem_singleton,
        forall_eq, List.Pairwise.nil, and_true, List.not_mem_nil, false_implies, implies_true]
      rw [h13, h2]; exact hd
    · simp only [ovRJ] at hs
      by_cases e13 : i.val = 13
      · simp [e13] at hs; subst hs; have : i = 13 := Fin.ext e13
        subst this; show m.reg 13 + 8 + BitVec.ofInt 64 (-8) = m.reg 13; simp; bv_omega
      by_cases e2 : i.val = 2
      · simp [e2] at hs; subst hs; have : i = 2 := Fin.ext e2
        subst this; show m.reg 2 - 16 + BitVec.ofInt 64 16 = m.reg 2; simp [BitVec.sub_add_cancel]
      simp [e13, e2] at hs
    · simp only [List.length_cons, List.length_nil] at hr
      have hr2 : r = 0 ∨ r = 1 := by omega
      rcases hr2 with rfl | rfl
      · have hj16 : j < 16 := by simpa [Env.size, entryEnv, shapeRJ] using hj
        simp only [Env.base, entryEnv, shapeRJ, List.map_cons, List.map_nil, List.getD_cons_zero, h13,
          hmem]
        exact hP j hj16
      · have hj16 : j < 16 := by simpa [Env.size, entryEnv, shapeRJ] using hj
        simp only [Env.base, entryEnv, shapeRJ, List.map_cons, List.map_nil, List.getD_cons_succ,
          List.getD_cons_zero]
        simpa using hstk'.2.2.2 j hj16

/-! ## Entry leaves -/

theorem RS.leaf_800db944_0 :
    LeafGoal RS.plan RS.plan.cuts[0]! (RS.plan.leaves 0x800db944)[0]! := by
  leaf_intro
  intro e m hA hc
  have hcut := RS.cut_800db944 e m hA
  obtain ⟨rfl, -, hpre⟩ := hA
  have hch := chunks_eval rfl hcut.1 hcut.2.1
  have hv := envS_var shapeE m m
  refine ⟨by simp only [List.mem_singleton, forall_eq]; exact ret_oblig_S (hv 1) hpre.1,
    Nat.le_of_ble_eq_true rfl, fun m' hm' he hso => ?_⟩
  have hmm : m'.mem = m.mem := funext fun a =>
    written_only hcut.2.1 rfl hm' rfl hso a (by rintro ⟨w, hw, -⟩; cases hw)
  have h0 : chunks m = 0 := by
    have := hc _ (List.mem_singleton_self _)
    simp only [SBool.eval, Sym.eval_lit, beq_iff_eq] at this
    rw [← hch, this]; rfl
  refine ⟨returns_S hm' (by decide) (fun i _ => hv i) ((reg_var hm' 2 rfl).trans (hv 2)) he,
    ?_, fun a _ => by rw [hmm], fun h => absurd h0 h⟩
  rw [Match.reg_of hm' 10 (.lit 0) rfl]; simp [remapOut, h0, Sym.eval_lit]

theorem RS.leaf_800db944_1 :
    LeafGoal RS.plan RS.plan.cuts[0]! (RS.plan.leaves 0x800db944)[1]! := by
  leaf_intro
  intro e m hA hc
  have hcut := RS.cut_800db944 e m hA
  obtain ⟨rfl, -, hpre⟩ := hA
  have hch := chunks_eval rfl hcut.1 hcut.2.1
  have hv := envS_var shapeE m m
  refine ⟨by simp, Nat.le_of_ble_eq_true rfl, fun m' hm' he hso => ?_⟩
  have hmm : m'.mem = m.mem := funext fun a =>
    written_only hcut.2.1 rfl hm' rfl hso a (by rintro ⟨w, hw, -⟩; cases hw)
  have hne : chunks m ≠ 0 := by
    have := hc _ (List.mem_singleton_self _)
    simp only [SBool.eval, Sym.eval_lit, bne_iff_ne, ne_eq] at this
    rw [← hch]; exact this
  refine ExitGoal.at_cut rfl ⟨rsJ, by simp [RS.plan, rsPlan], he, ⟨hpre, he, hmm, fun i hi => ?_,
    ?_, hne⟩, Nat.le_of_ble_eq_true rfl⟩
  · rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · simp [Machine.reg, h0]
    by_cases h10 : i.val = 10
    · have : i = 10 := Fin.ext h10
      subst this
      rw [Match.reg_of hm' 10 (.ptr 0 (-16)) rfl]
      show m.reg 10 + 16 + BitVec.ofInt 64 (-16) = m.reg 10; simp; bv_omega
    rw [← hv i]; refine reg_var hm' i ?_
    revert h0 h10 hi; revert i; decide
  · rw [Match.reg_of hm' 13 _ rfl]; exact hch

/-! ## Leaves after the null test -/

theorem rsLeafJ {l : Leaf}
    (hex : l.exit = .ret (.bin .and (.var 1) (.lit 18446744073709551614)))
    (hob : l.obligs = [.aligned (.bin .and (.var 1) (.lit 18446744073709551614)) 4])
    (hst : l.S.steps ≤ 20) (hreg : l.S.regions = SRJ.regions)
    (hkeep : ∀ i ∈ keepS, l.S.reg i = .var i) (h2 : l.S.reg 2 = .ptr 1 16)
    (hw : l.S.mem.all (fun w => (w.r == 1 && decide (w.off + w.n ≤ 16)) ||
      (w.r == 0 && w.off == 8 && w.n == 8)) = true)
    {s10 sU : Sym} (h10 : l.S.reg 10 = s10) (hU : readConst l.S 0 8 8 = sU)
    (hval : ∀ e m, rsAJ e m → (∀ b ∈ l.conds, b.eval (envS shapeRJ e m) = true) →
      s10.eval (envS shapeRJ e m) = (remapOut e).1 ∧
      sU.eval (envS shapeRJ e m) = (remapOut e).2.getD (used e)) :
    LeafGoal rsPlan rsJ l := by
  intro e m hA hc
  have hcut := RS.cut_800db94c e m hA
  have hwf : Env.WF (rsJ.env e m) rsJ.S := hcut.1
  have hm : Match (rsJ.env e m) rsJ.S m := hcut.2.1
  have hv := hval e m hA hc
  obtain ⟨hpre, -, hmem, hreg', h13, hne⟩ := hA
  obtain ⟨hstk, hR, -, -⟩ := hpre.2.2 hne
  have hvar : ∀ i : Fin 32, i.val ∈ keepS → (rsJ.env e m).vars i = e.reg i := fun i hi =>
    (envS_var shapeRJ e m i).trans (hreg' i (by revert hi; revert i; decide))
  refine ⟨?_, by show l.S.steps - 0 ≤ 20; omega, fun m' hm' he hso => ?_⟩
  · rw [hob]; simp only [List.mem_singleton, forall_eq]
    exact ret_oblig_S (hvar 1 (by decide)) hpre.1
  rw [hex] at he ⊢
  have e0 : (rsJ.env e m).base 0 = chunks e + 8 := by
    show m.reg 13 + 8 = _; rw [h13]
  have e1 : (rsJ.env e m).base 1 = e.reg 2 - 16 := by
    show m.reg 2 - 16 = _; rw [hreg' 2 (by decide)]
  have hc8 := hR.2; unfold Layout.ramHi at hc8
  have hs16 := sp16 hstk
  have hshi := hstk.2.2.1; unfold Layout.ramHi at hshi
  have hslo := hstk.2.1; unfold Layout.ramLo at hslo
  have hret : Returns e m' := returns_S hm' hkeep hvar
    (by rw [Match.reg_of hm' 2 _ h2]; show (rsJ.env e m).base 1 + BitVec.ofInt 64 16 = _
        rw [e1]; simp [BitVec.sub_add_cancel]) he
  have hwo := written_only hm rfl hm' hreg hso
  refine ⟨hret, by rw [Match.reg_of hm' 10 _ h10]; exact hv.1, fun a ha => ?_, fun _ => ?_⟩
  · rw [hwo a ?_, hmem]
    rintro ⟨w, hwm, j, hj1, hj2, rfl⟩
    have hw' := List.all_eq_true.mp hw w hwm
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw'
    rcases hw' with ⟨hr, hn⟩ | ⟨⟨hr, ho⟩, hn⟩
    · refine absurd (.inr ?_) ha; rw [hr, e1]
      exact inRange_add (n := 16) (by rw [hs16]; omega) (by omega)
    · refine absurd (.inl ⟨hne, ?_⟩) ha; rw [hr, e0]
      have h8 : chunks e + 8 + BitVec.ofNat 64 j = chunks e + 16 + BitVec.ofNat 64 (j - 8) := by
        rw [show j = 8 + (j - 8) by omega, ← BitVec.ofNat_add_ofNat]; simp; bv_omega
      rw [h8]
      have hc16 : (chunks e + 16).toNat = (chunks e + 8).toNat + 8 := by
        rw [show chunks e + 16 = chunks e + 8 + BitVec.ofNat 64 8 by bv_omega,
          toNat_add_ofNat (by omega)]
      exact inRange_add (n := 8) (by omega) (by omega)
  · have h := word_cst (wf_regions hwf hreg) hm' (r := 0) (off := 8) (R := capR)
      (by rw [hreg]; rfl) (by show 8 + 8 ≤ 16; decide)
    rw [show (rsJ.env e m).base 0 + BitVec.ofNat 64 8 = chunks e + 16 by rw [e0]; bv_omega] at h
    rw [h, hU]; exact hv.2

theorem rsJ_facts {e m : Machine} (hA : rsAJ e m) :
    (envS shapeRJ e m).vars 11 = e.reg 11 ∧ (envS shapeRJ e m).vars 12 = e.reg 12 ∧
    (envS shapeRJ e m).vars 14 = e.reg 14 ∧
    (envS shapeRJ e m).base 0 + BitVec.ofInt 64 (-8) = chunks e ∧
    (Sym.init 0 0 8).eval (envS shapeRJ e m) = cap e ∧
    (Sym.init 0 8 8).eval (envS shapeRJ e m) = used e := by
  have hcut := RS.cut_800db94c e m hA
  have hwf : Env.WF (envS shapeRJ e m) SRJ := hcut.1
  have hm : Match (envS shapeRJ e m) SRJ m := hcut.2.1
  obtain ⟨-, -, hmem, hreg, h13, -⟩ := hA
  have e0 : (envS shapeRJ e m).base 0 = chunks e + 8 := by show m.reg 13 + 8 = _; rw [h13]
  have hc := word_cst hwf hm (r := 0) (off := 0) (R := capR) rfl (by show 0 + 8 ≤ 16; decide)
  have hu := word_cst hwf hm (r := 0) (off := 8) (R := capR) rfl (by show 8 + 8 ≤ 16; decide)
  rw [e0, show chunks e + 8 + BitVec.ofNat 64 0 = chunks e + 8 by simp,
    show readConst SRJ 0 0 8 = Sym.init 0 0 8 by decide] at hc
  rw [e0, show chunks e + 8 + BitVec.ofNat 64 8 = chunks e + 16 by bv_omega,
    show readConst SRJ 0 8 8 = Sym.init 0 8 8 by decide] at hu
  refine ⟨(envS_var shapeRJ e m 11).trans (hreg 11 (by decide)),
    (envS_var shapeRJ e m 12).trans (hreg 12 (by decide)),
    (envS_var shapeRJ e m 14).trans (hreg 14 (by decide)), by rw [e0]; simp; bv_omega, ?_, ?_⟩
  · rw [← hc]; unfold cap word; rw [load_same hmem]
  · rw [← hu]; unfold used word; rw [load_same hmem]

set_option hygiene false in
macro "rs_sem" : tactic => `(tactic| (
  intro e m hA hc
  obtain ⟨h11, h12, h14, hb, hcap, hu⟩ := rsJ_facts hA
  have hne := hA.2.2.2.2.2
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, SBool.eval,
    Sym.eval_bin, Sym.eval_var, Sym.eval_ptr, BinOp.eval, beq_iff_eq, bne_iff_ne, ne_eq,
    BitVec.ult, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, ← Nat.not_le,
    Classical.not_not, h11, h12, h14, hb, hcap, hu] at hc
  refine ⟨?_, ?_⟩ <;>
  simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_ptr, Sym.eval_lit, BinOp.eval, h11, h12, h14, hb,
    hcap, hu, remapOut, if_neg hne] <;>
  (try simp_all [BitVec.le_def, BitVec.add_comm])
  all_goals ((try split) <;> (try simp_all [BitVec.le_def, BitVec.add_comm]) <;> omega)))

theorem RS.leaf_800db94c_0 :
    LeafGoal RS.plan RS.plan.cuts[1]! (RS.plan.leaves 0x800db94c)[0]! := by
  leaf_intro
  refine rsLeafJ (s10 := .var 11) (sU := .init 0 8 8) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  rs_sem

theorem RS.leaf_800db94c_1 :
    LeafGoal RS.plan RS.plan.cuts[1]! (RS.plan.leaves 0x800db94c)[1]! := by
  leaf_intro
  refine rsLeafJ (s10 := .lit 0) (sU := .init 0 8 8) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  rs_sem

theorem RS.leaf_800db94c_2 :
    LeafGoal RS.plan RS.plan.cuts[1]! (RS.plan.leaves 0x800db94c)[2]! := by
  leaf_intro
  refine rsLeafJ (s10 := .var 11) (sU := .bin .sub (.bin .add (.var 14) (.var 11)) (.ptr 0 (-8)))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ?_
  rs_sem

theorem RS.leaf_800db94c_3 :
    LeafGoal RS.plan RS.plan.cuts[1]! (RS.plan.leaves 0x800db94c)[3]! := by
  leaf_intro
  refine rsLeafJ (s10 := .var 11) (sU := .bin .sub (.bin .add (.var 14) (.var 11)) (.ptr 0 (-8)))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ?_
  rs_sem

theorem RS.leaf_800db94c_4 :
    LeafGoal RS.plan RS.plan.cuts[1]! (RS.plan.leaves 0x800db94c)[4]! := by
  leaf_intro
  refine rsLeafJ (s10 := .lit 0) (sU := .init 0 8 8) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  rs_sem

zesu_assemble RS

theorem RS.rs_spec : Spec zesuImage remapEntry 22 RemapPre RemapPost := fun m hpc hpre => by
  obtain ⟨k, m', hk, hr, hq⟩ := RS.reach rsE (by simp [RS.plan, rsPlan]) m m ⟨rfl, hpc, hpre⟩
  exact ⟨k, m', hk, runsIn_text hr, hq⟩

theorem RS.rs_sail {m : Machine} {s : BinaryFv.RiscV.State} (h : SailLink.Rel zesuImage m s)
    (hpc : m.pc.toNat = remapEntry) (hpre : RemapPre m) :
    SailLink.SailReaches zesuImage 22 (fun s' => ∃ m', SailLink.Rel zesuImage m' s' ∧ RemapPost m m') s :=
  SailLink.sail_reaches h (RS.rs_spec m hpc hpre)

end ZesuExec.Fn.Scratch
