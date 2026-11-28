import ZesuExec.Fn.Scratch.Vc
import ZesuExec.Sail.Run

/-!
# `scratch_arena.free` (`0x800db904`, 16 instructions) meets `FreePre`/`FreePost`

Plan `FS`: the entry (budget 16) and `0x800db90c` after the null test (budget 14; region 0 the
newest chunk's `used` word, region 1 the frame). Four leaves.
-/

namespace ZesuExec.Fn.Scratch
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc ZesuExec.Fn.Alloc

def fsAE (e m : Machine) : Prop := m = e ∧ m.pc.toNat = freeEntry ∧ FreePre e
def fsAJ (e m : Machine) : Prop :=
  FreePre e ∧ m.pc.toNat = freeJ ∧ m.mem = e.mem ∧ (∀ i : Fin 32, i.val ≠ 10 → m.reg i = e.reg i) ∧
    m.reg 10 = chunks e ∧ chunks e ≠ 0

def shapeFJ (m : Machine) : Shape := [((m.reg 10 + 16, 8), wordR), ((m.reg 2 - 16, 16), frameR)]

def fsE : Cut Machine := ⟨0x800db904, SE, fsAE, envS shapeE, fun _ _ => 16⟩
def fsJ : Cut Machine := ⟨0x800db90c, SFJ, fsAJ, envS shapeFJ, fun _ _ => 14⟩

def fsPlan : Plan Machine allocImage where
  cuts := [fsE, fsJ]
  fuel := 32
  leaves := fun pc => if pc = 0x800db904 then fsRunE_leaves else if pc = 0x800db90c then fsRunJ_leaves
    else []
  callee := fun _ => none
  Post := FreePost

zesu_plan FS := fsPlan

theorem FS.cut_800db904 : CutOK FS.plan FS.plan.cuts[0]! :=
  cutE fun _ _ h => by obtain ⟨rfl, hpc, hpre⟩ := h; exact ⟨hpre.2.1, hpc⟩

theorem FS.cut_800db90c : CutOK FS.plan FS.plan.cuts[1]! :=
  cutOK_S (sh := shapeFJ) (fun _ => rfl) fun e m h => by
    obtain ⟨hpre, hpc, hmem, hreg, h10, hne⟩ := h
    obtain ⟨hstk, hR, hP, hd⟩ := hpre.2.2 hne
    have h2 : m.reg 2 = e.reg 2 := hreg 2 (by decide)
    have hstk' := stack_same hstk h2 hmem
    refine ⟨?_, ?_, fun i hi s hs => ?_, fun r j hr hj => ?_, hpc⟩
    · simp only [shapeFJ, List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl)
      · rw [h10]; exact regionOk_word hR.1 (by have := hR.2; omega)
      · exact regionOk_frame hstk'
    · simp only [shapeFJ, List.map_cons, List.map_nil, List.pairwise_cons, List.mem_singleton,
        forall_eq, List.Pairwise.nil, and_true, List.not_mem_nil, false_implies, implies_true]
      rw [h10, h2]; exact hd
    · simp only [ovFJ] at hs
      by_cases e10 : i.val = 10
      · simp [e10] at hs; subst hs; have : i = 10 := Fin.ext e10
        subst this; show m.reg 10 + 16 + BitVec.ofInt 64 (-16) = m.reg 10; simp; bv_omega
      by_cases e2 : i.val = 2
      · simp [e2] at hs; subst hs; have : i = 2 := Fin.ext e2
        subst this; show m.reg 2 - 16 + BitVec.ofInt 64 16 = m.reg 2; simp [BitVec.sub_add_cancel]
      simp [e10, e2] at hs
    · simp only [List.length_cons, List.length_nil] at hr
      have hr2 : r = 0 ∨ r = 1 := by omega
      rcases hr2 with rfl | rfl
      · have hj8 : j < 8 := by simpa [Env.size, entryEnv, shapeFJ] using hj
        simp only [Env.base, entryEnv, shapeFJ, List.map_cons, List.map_nil, List.getD_cons_zero, h10,
          hmem]
        exact hP j hj8
      · have hj16 : j < 16 := by simpa [Env.size, entryEnv, shapeFJ] using hj
        simp only [Env.base, entryEnv, shapeFJ, List.map_cons, List.map_nil, List.getD_cons_succ,
          List.getD_cons_zero]
        simpa using hstk'.2.2.2 j hj16

/-! ## Entry leaves -/

theorem FS.leaf_800db904_0 :
    LeafGoal FS.plan FS.plan.cuts[0]! (FS.plan.leaves 0x800db904)[0]! := by
  leaf_intro
  intro e m hA hc
  have hcut := FS.cut_800db904 e m hA
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
  refine ⟨returns_S hm' (by decide) (fun i _ => hv i) ?_ he, fun a _ => by rw [hmm],
    fun h => absurd h0 h⟩
  exact (reg_var hm' 2 rfl).trans (hv 2)

theorem FS.leaf_800db904_1 :
    LeafGoal FS.plan FS.plan.cuts[0]! (FS.plan.leaves 0x800db904)[1]! := by
  leaf_intro
  intro e m hA hc
  have hcut := FS.cut_800db904 e m hA
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
  refine ExitGoal.at_cut rfl ⟨fsJ, by simp [FS.plan, fsPlan], he, ⟨hpre, he, hmm, fun i hi => ?_,
    ?_, hne⟩, Nat.le_of_ble_eq_true rfl⟩
  · rcases Nat.eq_zero_or_pos i.val with h0 | h0
    · simp [Machine.reg, h0]
    rw [← hv i]; refine reg_var hm' i ?_
    revert h0 hi; revert i; decide
  · rw [Match.reg_of hm' 10 _ rfl]; exact hch

/-! ## Leaves after the null test -/

theorem fsLeafJ {l : Leaf}
    (hex : l.exit = .ret (.bin .and (.var 1) (.lit 18446744073709551614)))
    (hob : l.obligs = [.aligned (.bin .and (.var 1) (.lit 18446744073709551614)) 4])
    (hst : l.S.steps ≤ 14) (hreg : l.S.regions = SFJ.regions)
    (hkeep : ∀ i ∈ keepS, l.S.reg i = .var i) (h2 : l.S.reg 2 = .ptr 1 16)
    (hw : l.S.mem.all (fun w => (w.r == 1 && decide (w.off + w.n ≤ 16)) ||
      (w.r == 0 && w.off == 0 && w.n == 8)) = true)
    (hval : ∀ e m, fsAJ e m → (∀ b ∈ l.conds, b.eval (envS shapeFJ e m) = true) →
      (readConst l.S 0 0 8).eval (envS shapeFJ e m) =
        if e.reg 11 + e.reg 12 = chunks e + used e then e.reg 11 - chunks e else used e) :
    LeafGoal fsPlan fsJ l := by
  intro e m hA hc
  have hcut := FS.cut_800db90c e m hA
  have hwf : Env.WF (fsJ.env e m) fsJ.S := hcut.1
  have hm : Match (fsJ.env e m) fsJ.S m := hcut.2.1
  have hv := hval e m hA hc
  obtain ⟨hpre, -, hmem, hreg', h10, hne⟩ := hA
  obtain ⟨hstk, hR, -, -⟩ := hpre.2.2 hne
  have hvar : ∀ i : Fin 32, i.val ∈ keepS → (fsJ.env e m).vars i = e.reg i := fun i hi =>
    (envS_var shapeFJ e m i).trans (hreg' i (by revert hi; revert i; decide))
  refine ⟨?_, by show l.S.steps - 0 ≤ 14; omega, fun m' hm' he hso => ?_⟩
  · rw [hob]; simp only [List.mem_singleton, forall_eq]
    exact ret_oblig_S (hvar 1 (by decide)) hpre.1
  rw [hex] at he ⊢
  have e0 : (fsJ.env e m).base 0 = chunks e + 16 := by
    show m.reg 10 + 16 = _; rw [h10]
  have e1 : (fsJ.env e m).base 1 = e.reg 2 - 16 := by
    show m.reg 2 - 16 = _; rw [hreg' 2 (by decide)]
  have hc8 := hR.2; unfold Layout.ramHi at hc8
  have hs16 := sp16 hstk
  have hshi := hstk.2.2.1; unfold Layout.ramHi at hshi
  have hslo := hstk.2.1; unfold Layout.ramLo at hslo
  have hret : Returns e m' := returns_S hm' hkeep hvar
    (by rw [Match.reg_of hm' 2 _ h2]; show (fsJ.env e m).base 1 + BitVec.ofInt 64 16 = _
        rw [e1]; simp [BitVec.sub_add_cancel]) he
  have hwo := written_only hm rfl hm' hreg hso
  refine ⟨hret, fun a ha => ?_, fun _ => ?_⟩
  · rw [hwo a ?_, hmem]
    rintro ⟨w, hwm, j, hj1, hj2, rfl⟩
    have hw' := List.all_eq_true.mp hw w hwm
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw'
    rcases hw' with ⟨hr, hn⟩ | ⟨⟨hr, ho⟩, hn⟩
    · refine absurd (.inr ?_) ha; rw [hr, e1]
      exact inRange_add (n := 16) (by rw [hs16]; omega) (by omega)
    · refine absurd (.inl ⟨hne, ?_⟩) ha; rw [hr, e0]
      exact inRange_add (n := 8) (by omega) (by omega)
  · have h := word_cst (wf_regions hwf hreg) hm' (r := 0) (off := 0) (R := wordR)
      (by rw [hreg]; rfl) (by show 0 + 8 ≤ 8; decide)
    rw [show (fsJ.env e m).base 0 + BitVec.ofNat 64 0 = chunks e + 16 by rw [e0]; simp] at h
    rw [h]; exact hv

theorem used_eval {e m : Machine} (hA : fsAJ e m) :
    (Sym.init 0 0 8).eval (envS shapeFJ e m) = used e := by
  have hcut := FS.cut_800db90c e m hA
  have hwf : Env.WF (envS shapeFJ e m) SFJ := hcut.1
  have hm : Match (envS shapeFJ e m) SFJ m := hcut.2.1
  have h := word_cst hwf hm (r := 0) (off := 0) (R := wordR) rfl (by show 0 + 8 ≤ 8; decide)
  obtain ⟨-, -, hmem, -, h10, -⟩ := hA
  rw [show (envS shapeFJ e m).base 0 + BitVec.ofNat 64 0 = chunks e + 16 by
    show m.reg 10 + 16 + _ = _; rw [h10]; simp] at h
  rw [show readConst SFJ 0 0 8 = Sym.init 0 0 8 by decide] at h
  rw [← h]; unfold used chunks word; rw [load_same hmem]

theorem fsJ_vars {e m : Machine} (hA : fsAJ e m) :
    (envS shapeFJ e m).vars 11 = e.reg 11 ∧ (envS shapeFJ e m).vars 12 = e.reg 12 ∧
    (envS shapeFJ e m).base 0 + BitVec.ofInt 64 (-16) = chunks e := by
  obtain ⟨-, -, -, hreg, h10, -⟩ := hA
  refine ⟨(envS_var shapeFJ e m 11).trans (hreg 11 (by decide)),
    (envS_var shapeFJ e m 12).trans (hreg 12 (by decide)), ?_⟩
  show m.reg 10 + 16 + _ = _; rw [h10]; simp; bv_omega

theorem FS.leaf_800db90c_0 :
    LeafGoal FS.plan FS.plan.cuts[1]! (FS.plan.leaves 0x800db90c)[0]! := by
  leaf_intro
  refine fsLeafJ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) fun e m hA hc => ?_
  obtain ⟨h11, h12, hb⟩ := fsJ_vars hA
  have hu := used_eval hA
  have c := hc _ (List.mem_singleton_self _)
  simp only [SBool.eval, Sym.eval_bin, Sym.eval_var, Sym.eval_ptr, BinOp.eval, bne_iff_ne, ne_eq,
    h11, h12, hb, hu] at c
  rw [show readConst _ 0 0 8 = Sym.init 0 0 8 by decide, hu, if_neg (by rwa [BitVec.add_comm])]

theorem FS.leaf_800db90c_1 :
    LeafGoal FS.plan FS.plan.cuts[1]! (FS.plan.leaves 0x800db90c)[1]! := by
  leaf_intro
  refine fsLeafJ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) fun e m hA hc => ?_
  obtain ⟨h11, h12, hb⟩ := fsJ_vars hA
  have hu := used_eval hA
  have c := hc _ (List.mem_singleton_self _)
  simp only [SBool.eval, Sym.eval_bin, Sym.eval_var, Sym.eval_ptr, BinOp.eval, beq_iff_eq,
    h11, h12, hb, hu] at c
  rw [show readConst _ 0 0 8 = Sym.bin .sub (.var 11) (.ptr 0 (-16)) by decide,
    if_pos (by rwa [BitVec.add_comm])]
  simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_ptr, BinOp.eval, h11, hb]

zesu_assemble FS

theorem free_spec : Spec zesuImage freeEntry 16 FreePre FreePost := fun m hpc hpre => by
  obtain ⟨k, m', hk, hr, hq⟩ := FS.reach fsE (by simp [FS.plan, fsPlan]) m m ⟨rfl, hpc, hpre⟩
  exact ⟨k, m', hk, runsIn_text hr, hq⟩

theorem free_sail {m : Machine} {s : BinaryFv.RiscV.State} (h : SailLink.Rel zesuImage m s)
    (hpc : m.pc.toNat = freeEntry) (hpre : FreePre m) :
    SailLink.SailReaches zesuImage 16 (fun s' => ∃ m', SailLink.Rel zesuImage m' s' ∧ FreePost m m') s :=
  SailLink.sail_reaches h (free_spec m hpc hpre)

end ZesuExec.Fn.Scratch
