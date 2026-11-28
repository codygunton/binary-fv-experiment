import ZesuExec.Fn.Alloc.AllocVc
import ZesuExec.Fn.Alloc.Lemmas

/-! # `alloc`: the cut points with regions (head cell, pop path, bump pointers) -/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

theorem heap_present {L : List (Word × Nat)} {m : Machine} (h : Heap L m) {a : Word}
    (ha : Arena a) : (m.mem a).isSome := by
  obtain ⟨st, hd, -⟩ := h; exact hd.present a ha

theorem fl_cell {m : Machine} {k : Nat} (h11 : m.reg 11 = BitVec.ofNat 64 (0xa0534000 + 8 * k))
    (hk : k < 22) : m.reg 11 + 8 = BitVec.ofNat 64 (flBase + 8 * k) := by
  rw [h11]; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by unfold flBase; omega)]
  unfold flBase; simp; omega

theorem arena_ofNat {x : Nat} (h : (flBase ≤ x ∧ x < flBase + 176) ∨ (posAddr ≤ x ∧ x < heapTop)) :
    Arena (BitVec.ofNat 64 x) := by
  unfold Arena; rw [toNat_ofNat_lt (by unfold flBase heapTop at h; omega)]; exact h

/-- Bytes of an arena range given by a literal base. -/
theorem present_lit {L : List (Word × Nat)} {m : Machine} (h : Heap L m) {b n j : Nat}
    (hj : j < n) (hr : (flBase ≤ b ∧ b + n ≤ flBase + 176) ∨ (posAddr ≤ b ∧ b + n ≤ heapTop)) :
    (m.mem (BitVec.ofNat 64 b + BitVec.ofNat 64 j)).isSome := by
  rw [← ofNat_add_ofNat_nat]
  exact heap_present h (arena_ofNat (by omega))
where
  ofNat_add_ofNat_nat : BitVec.ofNat 64 (b + j) = BitVec.ofNat 64 b + BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem regionOk_word {b : Word} (hlo : Layout.ramLo ≤ b.toNat) (hhi : b.toNat + 8 ≤ Layout.ramHi) :
    RegionOk ((b, 8), wordR) := by
  refine ⟨by simp [wordR], by simp [wordR, Nat.mod_one], ?_⟩
  simp [wordR, writable, inRange]; omega

theorem AllocF.cut_800426a0 : CutOK AllocF.plan AllocF.plan.cuts[3]! :=
  cutOK_entry (sh := shapeP) (fun _ => rfl) fun g m hA => by
    obtain ⟨⟨hpre, hpc, -⟩, hmem, -, hok, h11⟩ := hA
    have hb := fl_cell h11 hok.2.2
    have hk := hok.2.2
    refine ⟨?_, by simp [shapeP], fun i hi s hs => ?_, fun r j hr hj => ?_, hpc⟩
    · simp only [shapeP, List.mem_singleton, forall_eq, hb]
      exact regionOk_word (by rw [toNat_ofNat_lt (by anum)]; anum)
        (by rw [toNat_ofNat_lt (by anum)]; anum)
    · simp only [ovP] at hs
      split at hs
      · next h => cases hs; have : i = 11 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, shapeP]; bv_omega
      · simp at hs
    · simp only [List.length_singleton, Nat.lt_one_iff] at hr
      subst hr
      have hj8 : j < 8 := by simpa [Env.size, entryEnv, shapeP] using hj
      simp only [Env.base, entryEnv, shapeP, List.map_cons, List.map_nil, List.getD_cons_zero, hb,
        hmem]
      exact present_lit hpre.1 hj8 (.inl ⟨by omega, by unfold flBase; omega⟩)

theorem sp16 {m : Machine} (h : StackOk m 16) : (m.reg 2 - 16).toNat = (m.reg 2).toNat - 16 := by
  obtain ⟨-, hlo, -, -⟩ := h
  rw [BitVec.toNat_sub]; unfold Layout.ramLo at hlo; simp; omega

theorem regionOk_frame {m : Machine} (h : StackOk m 16) : RegionOk ((m.reg 2 - 16, 16), frameR) := by
  have hs := sp16 h
  obtain ⟨hal, hlo, hhi, -⟩ := h
  refine ⟨by simp [frameR], by simp [frameR, hs]; omega, ?_⟩
  simp [frameR, writable, inRange, hs]; unfold Layout.ramLo Layout.ramHi at *; omega

/-- An arena word outside the live blocks avoids the callee frame. -/
theorem frame_avoid {L : List (Word × Nat)} {m : Machine} (hfr : CalleeFrameFree (Priv L) m)
    {b : Nat} (hb : b + 8 < 2 ^ 64) (hp : ∀ t < 8, Priv L (BitVec.ofNat 64 (b + t))) :
    ∀ a, InRange (BitVec.ofNat 64 b) 8 a → ¬ InRange (m.reg 2 - 16) 16 a := fun a ha hf => by
  obtain ⟨t, ht, rfl⟩ := inRange_lit hb ha
  exact hfr _ hf (hp t ht)

theorem AllocF.cut_800426a8 : CutOK AllocF.plan AllocF.plan.cuts[4]! :=
  cutOK_entry (sh := shapeP1) (fun _ => rfl) fun g m hA => by
    obtain ⟨⟨hpre, hpc, hK⟩, hmem, hok, h11, hv, hne⟩ := hA
    have hk := hok.2.2
    have hb := fl_cell h11 hk
    obtain ⟨st, hd, hg, p, t, hfl, hp⟩ := pop_head hpre.1 hk hv hne
    have hpm : p ∈ st.fl (m.reg 13).toNat := by rw [hfl]; exact List.mem_cons_self ..
    have hin := hg.free_in hk hpm
    have h8 := eight_le_classBytes (m.reg 13).toNat
    have hsp : m.reg 2 = g.m.reg 2 := hK 2 (by decide)
    have hstk : StackOk m 16 := by
      obtain ⟨a1, a2, a3, a4⟩ := hpre.2.2.2.2.1
      exact ⟨hsp ▸ a1, hsp ▸ a2, hsp ▸ a3, fun j hj => by rw [hsp, hmem]; exact a4 j hj⟩
    have hfr : CalleeFrameFree (Priv g.L) m := fun a ha => hpre.2.2.2.2.2.2 a (hsp ▸ ha)
    have hcellP : ∀ t < 8, Priv g.L (BitVec.ofNat 64 (flBase + 8 * (m.reg 13).toNat + t)) :=
      fun t ht => priv_cell hg (by unfold flBase; omega)
    have hheadP : ∀ t < 8, Priv g.L (BitVec.ofNat 64 (p + t)) := fun t ht => priv_free hg hk hpm ht
    have hplt : p + 8 < 2 ^ 64 := by unfold heapTop at hin; omega
    refine ⟨?_, ?_, fun i hi s hs => ?_, fun r j hr hj => ?_, hpc⟩
    · simp only [shapeP1, List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl | rfl)
      · rw [hb]; exact regionOk_word (by rw [toNat_ofNat_lt (by anum)]; anum)
          (by rw [toNat_ofNat_lt (by anum)]; anum)
      · rw [hp]; exact regionOk_word (by rw [toNat_ofNat_lt (by omega)]; anum)
          (by rw [toNat_ofNat_lt (by omega)]; anum)
      · exact regionOk_frame hstk
    · simp only [shapeP1, List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons,
        List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true,
        false_implies, implies_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hb, hp]; unfold Fn.Disjoint
        rw [toNat_ofNat_lt (by anum), toNat_ofNat_lt (by omega)]; left; anum
      · rw [hb]; exact disjoint_of_avoid (by decide) (by decide)
          (frame_avoid hfr (by anum) hcellP)
      · rw [hp]; exact disjoint_of_avoid (by decide) (by decide) (frame_avoid hfr hplt hheadP)
    · simp only [ovP1] at hs
      by_cases e11 : i.val = 11
      · simp [e11] at hs; subst hs; have : i = 11 := Fin.ext e11
        subst this; show m.reg 11 + 8 + BitVec.ofInt 64 (-8) = m.reg 11; simp; bv_omega
      by_cases e10 : i.val = 10
      · simp [e10] at hs; subst hs; have : i = 10 := Fin.ext e10
        subst this; show m.reg 10 + BitVec.ofInt 64 0 = m.reg 10; simp
      by_cases e2 : i.val = 2
      · simp [e2] at hs; subst hs; have : i = 2 := Fin.ext e2
        subst this; show m.reg 2 - 16 + BitVec.ofInt 64 16 = m.reg 2; simp [BitVec.sub_add_cancel]
      simp [e11, e10, e2] at hs
    · simp only [List.length_cons, List.length_nil] at hr
      have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
      rcases hr3 with rfl | rfl | rfl
      · have hj8 : j < 8 := by simpa [Env.size, entryEnv, shapeP1] using hj
        simp only [Env.base, entryEnv, shapeP1, List.map_cons, List.map_nil, List.getD_cons_zero,
          hb, hmem]
        exact present_lit hpre.1 hj8 (.inl ⟨by omega, by unfold flBase; omega⟩)
      · have hj8 : j < 8 := by simpa [Env.size, entryEnv, shapeP1] using hj
        simp only [Env.base, entryEnv, shapeP1, List.map_cons, List.map_nil, List.getD_cons_succ,
          List.getD_cons_zero, hp, hmem]
        exact present_lit hpre.1 hj8 (.inr ⟨by unfold posAddr; unfold heapLo at hin; omega,
          by omega⟩)
      · have hj16 : j < 16 := by simpa [Env.size, entryEnv, shapeP1] using hj
        simp only [Env.base, entryEnv, shapeP1, List.map_cons, List.map_nil, List.getD_cons_succ,
          List.getD_cons_zero]
        exact hstk.2.2.2 j hj16

/-- The vars region `[HEAP_POS, HEAP_TOP]` and an `auipc` pointer into it. -/
theorem cutV {pc : Nat} {ov : Nat → Option Sym} {A : Sig → Machine → Prop}
    {bud : Sig → Machine → Nat}
    (hov : ∀ g m, A g m → ∀ i : Fin 32, i.val ≠ 0 → ∀ s, ov i.val = some s →
      s.eval (entryEnv m (shapeV.map (·.1))) = m.reg i)
    (hpres : ∀ g m, A g m → ∀ j < 16,
      (m.mem (BitVec.ofNat 64 posAddr + BitVec.ofNat 64 j)).isSome)
    (hpc : ∀ g m, A g m → m.pc.toNat = pc) :
    CutOK allocPlan (⟨pc, Fn.entryState ov [varsR] [], A, envOf fun _ => shapeV, bud⟩ : Cut Sig) :=
  cutOK_entry (sh := fun _ => shapeV) (fun _ => rfl) fun g m hA => by
    refine ⟨?_, by simp [shapeV], hov g m hA, fun r j hr hj => ?_, hpc g m hA⟩
    · simp only [shapeV, List.mem_singleton, forall_eq]
      refine ⟨by simp [varsR], by simp [varsR, Nat.mod_one], ?_⟩
      simp [varsR, writable, inRange, posAddr, Layout.ramLo, Layout.ramHi]
    · simp only [List.length_singleton, Nat.lt_one_iff] at hr
      subst hr
      have hj16 : j < 16 := by simpa [Env.size, entryEnv, shapeV] using hj
      simpa [Env.base, entryEnv, shapeV] using hpres g m hA j hj16

theorem vars_present {L : List (Word × Nat)} {m : Machine} (h : Heap L m) (j : Nat) (hj : j < 16) :
    (m.mem (BitVec.ofNat 64 posAddr + BitVec.ofNat 64 j)).isSome :=
  present_lit h hj (.inr ⟨Nat.le_refl _, by anum⟩)

/-- After rounding: `HEAP_POS` holds `p1`, `HEAP_TOP` is the entry's. -/
theorem vars_present' {g : Sig} {m : Machine} {p1 : Nat} (hpre : AllocPre g.L g.m)
    (hR : Rounded g m p1) (j : Nat) (hj : j < 16) :
    (m.mem (BitVec.ofNat 64 posAddr + BitVec.ofNat 64 j)).isSome := by
  obtain ⟨-, -, -, hrd, hso⟩ := hR
  have e : BitVec.ofNat 64 posAddr + BitVec.ofNat 64 j = BitVec.ofNat 64 (posAddr + j) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  rw [e]
  by_cases h8 : j < 8
  · exact rd_present hrd (by anum) j h8
  · rw [hso _ fun hr => by
      rw [inRange_ofNat (by anum) (by anum)] at hr; omega]
    have := vars_present hpre.1 j hj; rwa [e] at this

theorem AllocF.cut_80042740 : CutOK AllocF.plan AllocF.plan.cuts[7]! :=
  cutV (fun g m hA i hi s hs => by
      simp only [ovB] at hs; split at hs
      · next h => cases hs; have : i = 12 := Fin.ext h; subst this; rw [hA.2.2.1]; rfl
      · simp at hs)
    (fun g m hA j hj => by rw [hA.2.1]; exact vars_present hA.1.1.1 j hj) (fun g m hA => hA.1.2.1)

theorem AllocF.cut_80042760 : CutOK AllocF.plan AllocF.plan.cuts[8]! :=
  cutV (fun g m hA i hi s hs => by
      simp only [ovT] at hs
      by_cases e12 : i.val = 12
      · simp [e12] at hs; subst hs; have : i = 12 := Fin.ext e12; subst this; rw [hA.2.1]; rfl
      by_cases e13 : i.val = 13
      · simp [e13] at hs; subst hs; have : i = 13 := Fin.ext e13; subst this; rw [hA.2.2.1]; rfl
      simp [e12, e13] at hs)
    (fun g m hA j hj => by
      obtain ⟨_, _, -, -, hR⟩ := hA.2.2.2; exact vars_present' hA.1.1 hR j hj)
    (fun g m hA => hA.1.2.1)

theorem AllocF.cut_800426e0 : CutOK AllocF.plan AllocF.plan.cuts[5]! :=
  cutV (fun g m hA i hi s hs => by
      simp only [ovO] at hs; split at hs
      · next h => cases hs; have : i = 13 := Fin.ext h; subst this; rw [hA.2.2.2.2.1]; rfl
      · simp at hs)
    (fun g m hA j hj => by rw [hA.2.1]; exact vars_present hA.1.1.1 j hj) (fun g m hA => hA.1.2.1)

theorem AllocF.cut_80042708 : CutOK AllocF.plan AllocF.plan.cuts[6]! :=
  cutV (fun g m hA i hi s hs => by
      simp only [ovO2] at hs
      by_cases e13 : i.val = 13
      · simp [e13] at hs; subst hs; have : i = 13 := Fin.ext e13; subst this
        rw [hA.2.2.2.1]; rfl
      by_cases e12 : i.val = 12
      · simp [e12] at hs; subst hs; have : i = 12 := Fin.ext e12; subst this; rw [hA.2.2.1]; rfl
      simp [e12, e13] at hs)
    (fun g m hA j hj => by
      obtain ⟨_, hR⟩ := hA.2.2.2.2.2; exact vars_present' hA.1.1 hR j hj)
    (fun g m hA => hA.1.2.1)

end ZesuExec.Fn.Alloc
