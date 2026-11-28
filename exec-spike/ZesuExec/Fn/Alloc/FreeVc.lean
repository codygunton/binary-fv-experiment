import ZesuExec.Fn.Alloc.FreeRuns
import ZesuExec.Fn.Alloc.AllocCuts

/-!
# `alt_fl_alloc.free` in the obligation framework

Plan `FreeF` over `allocImage`, `σ = Sig` as for `alloc`. `free` saves `ra` and `s0` in its
frame at entry, so every later assertion states the frame (`Saved`); the entry leaves end at the
two joins of the size-class search with `a2 = sizeClassOfBytes len`; the push cut
(`0x80042170`) has `a0 = free_lists + 8 * class - 8` with the class exactly `sizeClassOfBytes len`
(`FreePre` rules out a block of at most 8 bytes freed at alignment 16).

Budgets: entry (25) → `0x80042130` (1) → `0x80042134` (9) → `0x80042170` (7) = 42.
-/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

def flen (g : Sig) : Nat := (g.m.reg 12).toNat
def falg (g : Sig) : Nat := (g.m.reg 13).toNat
def fsc (g : Sig) : Nat := sizeClassOfBytes (flen g)

/-- `ra` and the callee-saved registers other than `sp` and `s0`. -/
def fKeepRegs : List Nat := [1, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- Registers after the prologue: `sp` 16 lower, the block pointer `a1` kept. -/
def FKeep (g : Sig) (m : Machine) : Prop :=
  (∀ i : Fin 32, i.val ∈ fKeepRegs → m.reg i = g.m.reg i) ∧ m.reg 2 = g.m.reg 2 - 16 ∧
  m.reg 11 = g.m.reg 11

/-- The frame holds the entry `ra` (at `sp + 8`) and `s0` (at `sp`); memory elsewhere is the
entry's. -/
def Saved (g : Sig) (m : Machine) : Prop :=
  rd m ((g.m.reg 2 - 16).toNat + 8) = some (g.m.reg 1) ∧
  rd m (g.m.reg 2 - 16).toNat = some (g.m.reg 8) ∧
  SameOutside (InRange (g.m.reg 2 - 16) 16) g.m m

def FBase (g : Sig) (pc : Nat) (m : Machine) : Prop :=
  FreePre g.L g.m ∧ m.pc.toNat = pc ∧ FKeep g m ∧ Saved g m

def AFE (g : Sig) (m : Machine) : Prop := m = g.m ∧ m.pc.toNat = freeEntry ∧ FreePre g.L g.m

def AFJ1 (g : Sig) (m : Machine) : Prop :=
  FBase g 0x80042130 m ∧ m.reg 12 = BitVec.ofNat 64 (fsc g) ∧ m.reg 10 = g.m.reg 13 ∧
  m.reg 14 = g.m.reg 13 - 3 ∧ (falg g = 4 → fsc g ≤ 1)

def AFJ2 (g : Sig) (m : Machine) : Prop :=
  FBase g 0x80042134 m ∧ m.reg 12 = BitVec.ofNat 64 (fsc g) ∧ m.reg 10 = g.m.reg 13 ∧
  (falg g = 4 → m.reg 13 = BitVec.ofNat 64 (max (fsc g) 1))

def AFF (g : Sig) (m : Machine) : Prop :=
  FBase g 0x80042170 m ∧ fsc g < 22 ∧ m.reg 10 = BitVec.ofNat 64 (0xa0534000 + 8 * fsc g)

def shapeFE (m : Machine) : Shape := [((m.reg 2 - 16, 16), frameR)]
def shapeFJ (m : Machine) : Shape := [((m.reg 2, 16), frameR)]
def shapeFF (m : Machine) : Shape :=
  [((m.reg 10 + 8, 8), wordR), ((m.reg 11, 8), wordR), ((m.reg 2, 16), frameR)]

def fE : Cut Sig := ⟨0x80041f38, SFE, AFE, envOf shapeFE, fun _ _ => 42⟩
def fJ1 : Cut Sig := ⟨0x80042130, SFJ, AFJ1, envOf shapeFJ, fun _ _ => 17⟩
def fJ2 : Cut Sig := ⟨0x80042134, SFJ, AFJ2, envOf shapeFJ, fun _ _ => 16⟩
def fF : Cut Sig := ⟨0x80042170, SFF, AFF, envOf shapeFF, fun _ _ => 7⟩

def freePlan : Plan Sig allocImage where
  cuts := [fE, fJ1, fJ2, fF]
  fuel := 64
  leaves := fun pc =>
    if pc = 0x80041f38 then fRunE_leaves else if pc = 0x80042130 then fRunJ1_leaves
    else if pc = 0x80042134 then fRunJ2_leaves else if pc = 0x80042170 then fRunF_leaves else []
  callee := fun _ => none
  Post := fun g m' => FreePost g.L g.m m'

zesu_plan FreeF := freePlan

/-! ## Cut points -/

theorem cutOK_entryF {pc : Nat} {ov : Nat → Option Sym} {rs : List Region}
    {A : Sig → Machine → Prop} {sh : Machine → Shape} {bud : Sig → Machine → Nat}
    (hrs : ∀ m, (sh m).map (·.2) = rs)
    (h : ∀ g m, A g m → (∀ p ∈ sh m, RegionOk p) ∧ ((sh m).map (·.1)).Pairwise Fn.Disjoint ∧
      (∀ i : Fin 32, i.val ≠ 0 → ∀ s, ov i.val = some s →
        s.eval (entryEnv m ((sh m).map (·.1))) = m.reg i) ∧
      (∀ r j, r < rs.length → j < (entryEnv m ((sh m).map (·.1))).size r →
        (m.mem ((entryEnv m ((sh m).map (·.1))).base r + BitVec.ofNat 64 j)).isSome) ∧
      m.pc.toNat = pc) :
    CutOK freePlan (⟨pc, Fn.entryState ov rs [], A, envOf sh, bud⟩ : Cut Sig) := by
  intro g m hA
  obtain ⟨hok, hd, hov, hpres, hpc⟩ := h g m hA
  have hwf := entry_wf (m := m) (ov := ov) (ks := []) (sh m) hok hd
  have hmt := entry_match (m := m) (regs := (sh m).map (·.1)) (ov := ov) (rs := rs) (ks := [])
    hov hpres (by simp)
  rw [hrs m] at hwf
  exact ⟨hwf, hmt, rodata_allocImage m, hpc⟩

theorem FreeF.cut_80041f38 : CutOK FreeF.plan FreeF.plan.cuts[0]! :=
  cutOK_entryF (sh := shapeFE) (fun _ => rfl) fun g m hA => by
    obtain ⟨rfl, hpc, hpre⟩ := hA
    have hstk := hpre.2.2.2.2.2.2.1
    refine ⟨by simp only [shapeFE, List.mem_singleton, forall_eq]; exact regionOk_frame hstk,
      by simp [shapeFE], fun i hi s hs => ?_, fun r j hr hj => ?_, hpc⟩
    · simp only [ovFE] at hs; split at hs
      · next h => cases hs; have : i = 2 := Fin.ext h; subst this
                  show g.m.reg 2 - 16 + BitVec.ofInt 64 16 = g.m.reg 2; simp [BitVec.sub_add_cancel]
      · simp at hs
    · simp only [List.length_singleton, Nat.lt_one_iff] at hr; subst hr
      have hj16 : j < 16 := by simpa [Env.size, entryEnv, shapeFE] using hj
      simpa [Env.base, entryEnv, shapeFE] using hstk.2.2.2 j hj16

/-- The saved frame's 16 bytes are present. -/
theorem saved_present {g : Sig} {m : Machine} (hstk : StackOk g.m 16) (hs : Saved g m) (j : Nat)
    (hj : j < 16) : (m.mem (g.m.reg 2 - 16 + BitVec.ofNat 64 j)).isSome := by
  obtain ⟨h8, h0, -⟩ := hs
  have hsp := sp16 hstk
  have hhi := hstk.2.2.1
  have hlt : (g.m.reg 2 - 16).toNat + 16 < 2 ^ 64 := by rw [hsp]; unfold Layout.ramHi at hhi; omega
  rw [← ofNat_toNat_add]
  by_cases hj8 : j < 8
  · exact rd_present h0 (by omega) j hj8
  · have := rd_present h8 (by omega) (j - 8) (by omega)
    rwa [show (g.m.reg 2 - 16).toNat + 8 + (j - 8) = (g.m.reg 2 - 16).toNat + j by omega] at this

theorem cutFJ {pc : Nat} {A : Sig → Machine → Prop} {bud : Sig → Machine → Nat}
    (hA : ∀ g m, A g m → FBase g pc m) :
    CutOK freePlan (⟨pc, SFJ, A, envOf shapeFJ, bud⟩ : Cut Sig) :=
  cutOK_entryF (sh := shapeFJ) (fun _ => rfl) fun g m h => by
    obtain ⟨hpre, hpc, ⟨-, h2, -⟩, hs⟩ := hA g m h
    have hstk := hpre.2.2.2.2.2.2.1
    have hsp := sp16 hstk
    refine ⟨?_, by simp [shapeFJ], fun i hi s hs' => ?_, fun r j hr hj => ?_, hpc⟩
    · simp only [shapeFJ, List.mem_singleton, forall_eq, h2]; exact regionOk_frame hstk
    · simp only [ovFJ] at hs'; split at hs'
      · next h => cases hs'; have : i = 2 := Fin.ext h; subst this
                  show m.reg 2 + BitVec.ofInt 64 0 = m.reg 2; simp
      · simp at hs'
    · simp only [List.length_singleton, Nat.lt_one_iff] at hr; subst hr
      have hj16 : j < 16 := by simpa [Env.size, entryEnv, shapeFJ] using hj
      simp only [Env.base, entryEnv, shapeFJ, List.map_cons, List.map_nil, List.getD_cons_zero, h2]
      exact saved_present hstk hs j hj16

theorem FreeF.cut_80042130 : CutOK FreeF.plan FreeF.plan.cuts[1]! := cutFJ fun _ _ h => h.1
theorem FreeF.cut_80042134 : CutOK FreeF.plan FreeF.plan.cuts[2]! := cutFJ fun _ _ h => h.1

/-- A byte of a live block's first word: in the block, or in its reserved tail (private). -/
theorem live_word {L : List (Word × Nat)} {st : St} (hg : Good L st) {p : Word} {n t : Nat}
    (hb : (p, n) ∈ L) (ht : t < 8) :
    InRange p n (BitVec.ofNat 64 (p.toNat + t)) ∨ Priv L (BitVec.ofNat 64 (p.toNat + t)) := by
  have hin := hg.live_in hb
  simp only at hin
  have h8 := eight_le_cap n
  have hlt : p.toNat + t < 2 ^ 64 := by unfold heapTop at hin; omega
  by_cases htn : t < n
  · left; unfold InRange; rw [toNat_ofNat_lt hlt]; omega
  · right
    refine ⟨.inr ?_, fun ⟨b, hb', h1, h2⟩ => ?_⟩
    · rw [toNat_ofNat_lt hlt]; unfold posAddr; unfold heapLo heapTop at hin; unfold heapTop; omega
    · rw [toNat_ofNat_lt hlt] at h1 h2
      by_cases he : b = (p, n)
      · subst he; simp only at h1 h2; omega
      · -- another live block: disjoint from `(p, cap n)`
        have hd := (List.pairwise_append.mp hg.disj).2.1
        unfold liveBlocks at hd
        rw [List.pairwise_map] at hd
        have hcb := le_cap b.2
        obtain ⟨i, hi, hp⟩ := List.mem_iff_getElem.mp hb
        obtain ⟨i', hi', hq⟩ := List.mem_iff_getElem.mp hb'
        have hne : i ≠ i' := fun h => he (by subst h; rw [← hq, hp])
        have := List.pairwise_iff_getElem.mp hd
        rcases Nat.lt_or_gt_of_ne hne with hlt' | hlt'
        · have := this i i' hi hi' hlt'; rw [hq, hp] at this; simp only [NDisj] at this; omega
        · have := this i' i hi' hi hlt'; rw [hq, hp] at this; simp only [NDisj] at this; omega

theorem FreeF.cut_80042170 : CutOK FreeF.plan FreeF.plan.cuts[3]! :=
  cutOK_entryF (sh := shapeFF) (fun _ => rfl) fun g m hA => by
    obtain ⟨⟨hpre, hpc, ⟨-, h2, h11⟩, hs⟩, hk, h10⟩ := hA
    have hstk := hpre.2.2.2.2.2.2.1
    have hsp := sp16 hstk
    obtain ⟨st, hd, hg⟩ := hpre.1
    have hb := hpre.2.1
    have hin := hg.live_in hb
    simp only at hin
    have hcellA : m.reg 10 + 8 = BitVec.ofNat 64 (flBase + 8 * fsc g) := by
      rw [h10]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by unfold flBase; omega)]
      unfold flBase; simp; omega
    have hfr : CalleeFrameFree (Priv g.L) g.m := hpre.2.2.2.2.2.2.2.2.1
    have hfb := hpre.2.2.2.2.2.2.2.2.2
    have hsm : m.reg 2 = g.m.reg 2 - 16 := h2
    have hcellP : ∀ t < 8, Priv g.L (BitVec.ofNat 64 (flBase + 8 * fsc g + t)) :=
      fun t ht => priv_cell hg (by unfold flBase; omega)
    have hp8 : (g.m.reg 11).toNat + 8 < 2 ^ 64 := by unfold heapTop at hin; have := le_cap (flen g); omega
    refine ⟨?_, ?_, fun i hi s hs' => ?_, fun r j hr hj => ?_, hpc⟩
    · simp only [shapeFF, List.mem_cons, List.mem_nil_iff, or_false]
      rintro q (rfl | rfl | rfl)
      · rw [hcellA]; exact regionOk_word (by rw [toNat_ofNat_lt (by anum)]; anum)
          (by rw [toNat_ofNat_lt (by anum)]; anum)
      · rw [h11]; have := le_cap (flen g)
        exact regionOk_word (by unfold heapLo at hin; unfold Layout.ramLo; omega)
          (by unfold flen at this; unfold heapTop at hin; unfold Layout.ramHi; omega)
      · rw [hsm]; exact regionOk_frame hstk
    · simp only [shapeFF, List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons,
        List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true,
        false_implies, implies_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hcellA, h11]; unfold Fn.Disjoint
        rw [toNat_ofNat_lt (by anum)]; left; unfold heapLo at hin; anum
      · rw [hcellA, hsm]; exact disjoint_of_avoid (by decide) (by decide)
          (frame_avoid hfr (by anum) hcellP)
      · rw [h11, hsm]
        refine disjoint_of_avoid (by decide) (by decide) fun a ha hf => ?_
        have ha' : InRange (BitVec.ofNat 64 (g.m.reg 11).toNat) 8 a := by
          rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        obtain ⟨t, ht, rfl⟩ := inRange_lit (by omega) ha'
        rcases live_word hg hb ht with hblk | hpriv
        · exact hfb _ hf hblk
        · exact hfr _ hf hpriv
    · simp only [ovFF] at hs'
      by_cases e10 : i.val = 10
      · simp [e10] at hs'; subst hs'; have : i = 10 := Fin.ext e10
        subst this; show m.reg 10 + 8 + BitVec.ofInt 64 (-8) = m.reg 10; simp; bv_omega
      by_cases e11 : i.val = 11
      · simp [e11] at hs'; subst hs'; have : i = 11 := Fin.ext e11
        subst this; show m.reg 11 + BitVec.ofInt 64 0 = m.reg 11; simp
      by_cases e2 : i.val = 2
      · simp [e2] at hs'; subst hs'; have : i = 2 := Fin.ext e2
        subst this; show m.reg 2 + BitVec.ofInt 64 0 = m.reg 2; simp
      simp [e10, e11, e2] at hs'
    · simp only [List.length_cons, List.length_nil] at hr
      have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
      have hmo : ∀ a, ¬ InRange (g.m.reg 2 - 16) 16 a → m.mem a = g.m.mem a := hs.2.2
      rcases hr3 with rfl | rfl | rfl
      · have hj8 : j < 8 := by simpa [Env.size, entryEnv, shapeFF] using hj
        simp only [Env.base, entryEnv, shapeFF, List.map_cons, List.map_nil, List.getD_cons_zero,
          hcellA]
        rw [← ofNat_add_nat, hmo _ (frame_avoid hfr (by anum) hcellP _ (by
          rw [inRange_ofNat (by anum) (by anum)]; omega)), ofNat_add_nat]
        exact present_lit ⟨st, hd, hg⟩ hj8 (.inl ⟨by omega, by unfold flBase; omega⟩)
      · have hj8 : j < 8 := by simpa [Env.size, entryEnv, shapeFF] using hj
        simp only [Env.base, entryEnv, shapeFF, List.map_cons, List.map_nil, List.getD_cons_succ,
          List.getD_cons_zero, h11]
        rw [show g.m.reg 11 + BitVec.ofNat 64 j = BitVec.ofNat 64 ((g.m.reg 11).toNat + j) by
          rw [ofNat_toNat_add]]
        have hnf : ¬ InRange (g.m.reg 2 - 16) 16 (BitVec.ofNat 64 ((g.m.reg 11).toNat + j)) :=
          fun hf => (live_word hg hb hj8).elim (hfb _ hf) (hfr _ hf)
        rw [hmo _ hnf]
        have := eight_le_cap (flen g)
        exact heap_present ⟨st, hd, hg⟩ (arena_ofNat (.inr ⟨by anum, by unfold flen at this; anum⟩))
      · have hj16 : j < 16 := by simpa [Env.size, entryEnv, shapeFF] using hj
        simp only [Env.base, entryEnv, shapeFF, List.map_cons, List.map_nil, List.getD_cons_succ,
          List.getD_cons_zero, hsm]
        exact saved_present hstk hs j hj16

end ZesuExec.Fn.Alloc
