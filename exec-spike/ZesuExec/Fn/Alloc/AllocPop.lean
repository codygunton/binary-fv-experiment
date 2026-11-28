import ZesuExec.Fn.Alloc.AllocPost

/-! # `alloc`: the pop path (`0x800426a8` to the return): the head leaves its list -/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

def popKeep : List Nat := [1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem leafPop {l : Leaf}
    (hex : l.exit = .ret (.bin .and (.var 1) (.lit 18446744073709551614)))
    (hob : l.obligs = [.aligned (.bin .and (.var 1) (.lit 18446744073709551614)) 4])
    (hst : l.S.steps ≤ 10) (hreg : l.S.regions = SP1.regions)
    (hmemw : l.S.mem = [⟨0, 0, 8, .init 1 0 8⟩, ⟨2, 0, 8, .var 8⟩, ⟨2, 8, 8, .var 1⟩])
    (hrc : readConst l.S 0 0 8 = .init 1 0 8)
    (hkeep : ∀ i ∈ popKeep, l.S.reg i = .var i) (h2 : l.S.reg 2 = .ptr 2 16)
    (h10 : l.S.reg 10 = .ptr 1 0) : LeafGoal allocPlan cP1 l := by
  intro g m hA _
  obtain ⟨hwf, hm, -, -⟩ := AllocF.cut_800426a8 g m hA
  have hwf : Env.WF (cP1.env g m) cP1.S := hwf
  have hm : Match (cP1.env g m) cP1.S m := hm
  obtain ⟨⟨hpre, -, hK⟩, hmm, hok, h11m, hv, hne⟩ := hA
  have hv1 : (cP1.env g m).vars 1 = m.reg 1 := envOf_var shapeP1 g m 1
  refine ⟨by rw [hob]; simp only [List.mem_singleton, forall_eq]; exact ret_oblig hv1 hK hpre,
    by show l.S.steps - 0 ≤ 10; omega, fun m' hm' he hso => ?_⟩
  generalize (m.reg 13).toNat = k at hok h11m hv
  have hk := hok.2.2
  have hb0 := fl_cell h11m hk
  obtain ⟨st, hd, hg, p, t, hfl, hp⟩ := pop_head hpre.1 hk hv hne
  have hpm : p ∈ st.fl k := by rw [hfl]; exact List.mem_cons_self ..
  have hin := hg.free_in hk hpm
  have hsp : m.reg 2 = g.m.reg 2 := hK 2 (by decide)
  have hfr : CalleeFrameFree (Priv g.L) g.m := hpre.2.2.2.2.2.2
  -- what the run wrote: the head cell and the frame
  have hwo := written_only hm rfl hm' hreg hso
  have hwr : ∀ a, (∃ w ∈ l.S.mem, ∃ j, w.off ≤ j ∧ j < w.off + w.n ∧
      a = (cP1.env g m).base w.r + BitVec.ofNat 64 j) →
      InRange (BitVec.ofNat 64 (flBase + 8 * k)) 8 a ∨ InRange (g.m.reg 2 - 16) 16 a := by
    rintro a ⟨w, hw, j, hj1, hj2, rfl⟩
    rw [hmemw] at hw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · left
      show InRange _ 8 (m.reg 11 + 8 + BitVec.ofNat 64 j)
      rw [hb0]; simp only at hj1 hj2
      rw [← ofNat_add_nat]; rw [inRange_ofNat (by anum) (by anum)]; omega
    all_goals
      right
      show InRange _ 16 (m.reg 2 - 16 + BitVec.ofNat 64 j)
      simp only at hj1 hj2
      rw [hsp]
      have hs := sp16 hpre.2.2.2.2.1
      unfold InRange
      have hhi := hpre.2.2.2.2.1.2.2.1
      unfold Layout.ramHi at hhi
      rw [toNat_add_ofNat (by rw [hs]; omega), hs]
      omega
  have hcellP : ∀ a, InRange (BitVec.ofNat 64 (flBase + 8 * k)) 8 a → Priv g.L a := fun a ha => by
    obtain ⟨t, ht, rfl⟩ := inRange_lit (by anum) ha
    exact priv_cell hg (by unfold flBase; omega)
  have hagree : ∀ a, Priv g.L a → ¬ InRange (BitVec.ofNat 64 (flBase + 8 * k)) 8 a →
      m'.mem a = g.m.mem a := fun a hpa hnc => by
    rw [hwo a fun hw => (hwr a hw).elim hnc fun hf => hfr a hf hpa, hmm]
  have hpres : ∀ a, Arena a → (g.m.mem a).isSome → (m'.mem a).isSome := fun a _ h =>
    pres_of hm' hreg hso a (by rw [hmm]; exact h)
  -- the head cell now holds the next block
  have hcell : rd m' (flBase + 8 * k) = rd g.m p := by
    have h1 := rd_cst (wf_regions hwf hreg) hm' (r := 0) (off := 0) (R := wordR) (by rw [hreg]; rfl)
      (by show 0 + 8 ≤ 8; decide)
    have h2 := rd_cst hwf hm (r := 1) (off := 0) (R := wordR) rfl (by show 0 + 8 ≤ 8; decide)
    have e0 : (cP1.env g m).base 0 = m.reg 11 + 8 := rfl
    have e1 : (cP1.env g m).base 1 = m.reg 10 := rfl
    rw [e0, hb0, toNat_ofNat_lt (by anum), Nat.add_zero, hrc] at h1
    rw [e1, hp, toNat_ofNat_lt (by unfold heapTop at hin; omega), Nat.add_zero, rd_mem hmm] at h2
    rw [h1, h2]; rfl
  have hheap := pop_ok hd hg hk hfl hpre.2.1 hok.1 hcell hagree hpres
  have hK' : Keep g m' := fun i hi => by
    by_cases h2i : i = 2
    · subst h2i
      rw [Match.reg_of hm' 2 _ h2, ← hsp]
      show m.reg 2 - 16 + BitVec.ofInt 64 16 = m.reg 2
      simp [BitVec.sub_add_cancel]
    · exact (reg_var hm' i (hkeep i.val (by
        simp only [keepRegs, List.mem_cons, List.mem_nil_iff, or_false] at hi
        simp only [popKeep, List.mem_cons, List.mem_nil_iff, or_false]
        have : i.val ≠ 2 := fun h => h2i (Fin.ext h)
        omega))).trans ((envOf_var shapeP1 g m i).trans (hK i hi))
  rw [hex] at he ⊢
  have hret : Returns g.m m' := returns_of hK' (by rw [he]; exact ret_target hv1 hK)
  refine post_block hret (fun a ha => ?_) (q := p) ?_ hin.1 (by unfold lenOf; have := hpre.2.2.1; unfold heapTop at hin; omega)
    hheap (fun t ht => ?_)
  · rw [hwo a fun hw => (hwr a hw).elim (fun hc => ha (.inl (hcellP a hc))) fun hf => ha (.inr hf),
      hmm]
  · rw [Match.reg_of hm' 10 _ h10]
    show m.reg 10 + BitVec.ofInt 64 0 = _
    rw [hp]; simp
  · have := le_cap (lenOf g)
    have := cap_le_classBytes hok.1 hk
    exact free_blk_priv hg hk hpm (by unfold lenOf at *; omega)

end ZesuExec.Fn.Alloc
