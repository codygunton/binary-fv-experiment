import ZesuExec.Fn.Alloc.FreeVc
import ZesuExec.Fn.Alloc.AllocPost
import ZesuExec.Fn.Alloc.AllocJ

/-! # `free`: leaf lemmas and the plan's 32 leaves -/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- An address in `[b, b + n)` is `b + j` for some `j < n`. -/
theorem inRange_decomp {b : Word} {n : Nat} {a : Word} (hb : b.toNat + n < 2 ^ 64)
    (h : InRange b n a) : ∃ j < n, a = b + BitVec.ofNat 64 j := by
  unfold InRange at h
  refine ⟨a.toNat - b.toNat, by omega, BitVec.eq_of_toNat_eq ?_⟩
  rw [toNat_add_ofNat (by omega)]; omega

theorem frame_lt {m : Machine} (h : StackOk m 16) : (m.reg 2 - 16).toNat + 16 < 2 ^ 64 := by
  rw [sp16 h]; have := h.2.2.1; unfold Layout.ramHi at this; omega

/-- Bytes present at entry stay present while the frame is the saved one. -/
theorem saved_pres {g : Sig} {m : Machine} (hstk : StackOk g.m 16) (hs : Saved g m) :
    ∀ a, (g.m.mem a).isSome → (m.mem a).isSome := fun a ha => by
  by_cases hf : InRange (g.m.reg 2 - 16) 16 a
  · obtain ⟨j, hj, rfl⟩ := inRange_decomp (frame_lt hstk) hf
    exact saved_present hstk hs j hj
  · rw [hs.2.2 a hf]; exact ha

/-- With no writes and no known bytes, an 8-byte load at a constant offset is `init`. -/
theorem rd_init {env : Env} {S : SState} {m : Machine} (hwf : Env.WF env S) (hm : Match env S m)
    (hmem : S.mem = []) (hk : S.known = []) {r off : Nat} {R : Region}
    (hR : S.regions[r]? = some R) (hb : off + 8 ≤ env.size r) :
    rd m ((env.base r).toNat + off) = some ((Sym.init r off 8).eval env) := by
  rw [rd_cst hwf hm hR hb]
  congr 2
  unfold readConst; simp [hmem, hk]

/-- `ra` and `s0` read back from the saved frame. -/
theorem saved_ra {g : Sig} {m : Machine} {env : Env} {S : SState} {r : Nat} (hwf : Env.WF env S)
    (hm : Match env S m) (hmem : S.mem = []) (hk : S.known = []) (hR : S.regions[r]? = some frameR)
    (hb : env.base r = g.m.reg 2 - 16) (hs : Saved g m) :
    (Sym.init r 8 8).eval env = g.m.reg 1 ∧ (Sym.init r 0 8).eval env = g.m.reg 8 := by
  have hsz : env.size r = 16 := hwf.size r frameR 16 hR rfl
  have h8 := rd_init hwf hm hmem hk hR (off := 8) (by omega)
  have h0 := rd_init hwf hm hmem hk hR (off := 0) (by omega)
  rw [hb, hs.1] at h8
  rw [hb, Nat.add_zero, hs.2.1] at h0
  exact ⟨(Option.some.inj h8).symm, (Option.some.inj h0).symm⟩

/-! ## Entry leaves -/

/-- An entry leaf: the prologue saved `ra` and `s0`; it ends at a join of the size-class search
with `a2 = a3 = sizeClassOfBytes len`. -/
theorem leafFE {l : Leaf} {pcJ : Nat} (hJ : pcJ = 0x80042130 ∨ pcJ = 0x80042134)
    (hex : l.exit = .at pcJ) (hst : l.S.steps + (if pcJ = 0x80042130 then 17 else 16) ≤ 42)
    (hob : l.obligs = []) (hreg : l.S.regions = [frameR])
    (hmemw : l.S.mem = [⟨0, 0, 8, .var 8⟩, ⟨0, 8, 8, .var 1⟩])
    (hkeep : ∀ i ∈ 11 :: fKeepRegs, l.S.reg i = .var i) (h2 : l.S.reg 2 = .ptr 0 0)
    (h13 : l.S.reg 13 = l.S.reg 12) (h10 : l.S.reg 10 = .bin .and (.var 13) (.lit 63))
    (h14 : l.S.reg 14 = .bin .add (.bin .and (.var 13) (.lit 63)) (.lit 18446744073709551613))
    (hr8 : readConst l.S 0 8 8 = .var 1) (hr0 : readConst l.S 0 0 8 = .var 8)
    (hsem : ∀ g, FreePre g.L g.m →
      (∀ b ∈ l.conds, b.eval (envOf shapeFE g g.m) = true) →
      (l.S.reg 12).eval (envOf shapeFE g g.m) = BitVec.ofNat 64 (fsc g) ∧
      (pcJ = 0x80042130 → falg g = 4 → fsc g ≤ 1) ∧ (pcJ = 0x80042134 → falg g = 4 → 1 ≤ fsc g)) :
    LeafGoal freePlan fE l := by
  intro g m hA hc
  obtain ⟨rfl, hpc0, hpre⟩ := hA
  obtain ⟨hv12, hj1, hj2⟩ := hsem g hpre hc
  have hwf : Env.WF (fE.env g g.m) fE.S := (FreeF.cut_80041f38 g g.m ⟨rfl, hpc0, hpre⟩).1
  have hstk := hpre.2.2.2.2.2.2.1
  have hS0 : fE.S.steps = 0 := rfl
  refine ⟨by rw [hob]; simp, ?_, fun m' hm' he hso => ?_⟩
  · show l.S.steps - 0 ≤ 42
    split at hst <;> omega
  have hb : (fE.env g g.m).base 0 = g.m.reg 2 - 16 := rfl
  have hv : ∀ i : Fin 32, (fE.env g g.m).vars i.val = g.m.reg i := envOf_var shapeFE g g.m
  have hwf' := wf_regions hwf (S' := l.S) (by rw [hreg]; rfl)
  have hR : l.S.regions[0]? = some frameR := by rw [hreg]; rfl
  have hsz : (fE.env g g.m).size 0 = 16 := rfl
  have hr8' := rd_cst hwf' hm' hR (off := 8) (by omega)
  have hr0' := rd_cst hwf' hm' hR (off := 0) (by omega)
  rw [hb, hr8] at hr8'
  rw [hb, hr0, Nat.add_zero] at hr0'
  have hsaved : Saved g m' := by
    refine ⟨by rw [hr8']; exact congrArg some (hv 1), by rw [hr0']; exact congrArg some (hv 8),
      fun a ha => hso a fun hw => ha ?_⟩
    obtain ⟨p, hp, -, hin⟩ := inWritable_entry (shape := shapeFE g.m) hw (by
      simp only [shapeFE, List.mem_singleton, forall_eq]; exact frame_lt hstk)
    simp only [shapeFE, List.mem_singleton] at hp; subst hp; exact hin
  have hfk : FKeep g m' := by
    refine ⟨fun i hi => ?_, ?_, ?_⟩
    · exact (reg_var hm' i (hkeep i.val (List.mem_cons_of_mem _ hi))).trans (hv i)
    · rw [Match.reg_of hm' 2 _ h2]; show g.m.reg 2 - 16 + BitVec.ofInt 64 0 = _; simp
    · exact (reg_var hm' 11 (hkeep 11 (List.mem_cons_self ..))).trans (hv 11)
  have ha := hpre.2.2.2.2.1
  have r12 : m'.reg 12 = BitVec.ofNat 64 (fsc g) := by rw [Match.reg_of hm' 12 _ rfl]; exact hv12
  have r13 : m'.reg 13 = BitVec.ofNat 64 (fsc g) := by rw [Match.reg_of hm' 13 _ h13]; exact hv12
  have r10 : m'.reg 10 = g.m.reg 13 := by
    rw [Match.reg_of hm' 10 _ h10]
    simp only [Sym.eval, BinOp.eval]
    rw [show (fE.env g g.m).vars 13 = g.m.reg 13 from hv 13]; exact and63 ha
  have r14 : m'.reg 14 = g.m.reg 13 - 3 := by
    rw [Match.reg_of hm' 14 _ h14]
    simp only [Sym.eval, BinOp.eval]
    rw [show (fE.env g g.m).vars 13 = g.m.reg 13 from hv 13, and63 ha]; exact sub3 _
  rw [hex] at he ⊢
  have hpc : m'.pc.toNat = pcJ := he
  rcases hJ with rfl | rfl
  · refine ExitGoal.at_cut rfl ⟨fJ1, by simp [freePlan], hpc, ⟨⟨hpre, hpc, hfk, hsaved⟩, r12, r10,
      r14, hj1 rfl⟩, ?_⟩
    simp only [fJ1, fE, hS0] at hst ⊢; simp at hst; omega
  · refine ExitGoal.at_cut rfl ⟨fJ2, by simp [freePlan], hpc, ⟨⟨hpre, hpc, hfk, hsaved⟩, r12, r10,
      fun h4 => by rw [r13, Nat.max_eq_left (hj2 rfl h4)]⟩, ?_⟩
    simp only [fJ2, fE, hS0] at hst ⊢; simp at hst; omega

/-! ## Join leaves -/

theorem fJ_var (c : Cut Sig) (hc : c.env = envOf shapeFJ) (g : Sig) (m : Machine) (i : Fin 32) :
    (c.env g m).vars i.val = m.reg i := by rw [hc]; exact envOf_var shapeFJ g m i

theorem saved_mem {g : Sig} {m m' : Machine} (h : m'.mem = m.mem) (hs : Saved g m) : Saved g m' :=
  ⟨by rw [rd_mem h]; exact hs.1, by rw [rd_mem h]; exact hs.2.1, fun a ha => by
    rw [h]; exact hs.2.2 a ha⟩

theorem FreeF.leaf_80042130_0 :
    LeafGoal FreeF.plan FreeF.plan.cuts[1]! (FreeF.plan.leaves 0x80042130)[0]! := by
  leaf_intro
  intro g m hA _
  have hm : Match (fJ1.env g m) fJ1.S m := (FreeF.cut_80042130 g m hA).2.1
  obtain ⟨⟨hpre, -, ⟨hk, h2, h11⟩, hs⟩, h12, h10, h14, hal⟩ := hA
  refine ⟨by simp, Nat.le_of_ble_eq_true rfl, fun m' hm' he hso => ?_⟩
  have hmm : m'.mem = m.mem := funext fun a => written_only hm rfl hm' rfl hso a (by rintro ⟨w, hw, -⟩; cases hw)
  have hv := fJ_var fJ1 rfl g m
  have hpc : m'.pc.toNat = 0x80042134 := he
  refine ExitGoal.at_cut rfl ⟨fJ2, by simp [FreeF.plan, freePlan], hpc, ⟨⟨hpre, hpc, ⟨fun i hi => ?_, ?_, ?_⟩,
    saved_mem hmm hs⟩, ?_, ?_, fun h4 => ?_⟩, Nat.le_of_ble_eq_true rfl⟩
  · exact (reg_var hm' i (by revert hi; revert i; decide)).trans ((hv i).trans (hk i hi))
  · rw [Match.reg_of hm' 2 _ rfl]; show m.reg 2 + BitVec.ofInt 64 0 = _; simp [h2]
  · exact (reg_var hm' 11 rfl).trans ((hv 11).trans h11)
  · exact (reg_var hm' 12 rfl).trans ((hv 12).trans h12)
  · exact (reg_var hm' 10 rfl).trans ((hv 10).trans h10)
  · rw [show m'.reg 13 = m.reg 14 from Match.reg_of hm' 13 (.var 14) rfl, h14]
    have h4' : g.m.reg 13 = 4#64 := BitVec.eq_of_toNat_eq (by simp [falg] at h4; simp [h4])
    rw [h4', Nat.max_eq_right (hal h4)]; rfl

/-- From the second join to the push cut, with the class in `a2` (`i = 12`) or `a3` (`i = 13`). -/
theorem leafFJ2F {l : Leaf} (hex : l.exit = .at 0x80042170) (hst : l.S.steps ≤ 9)
    (hob : l.obligs = []) (hmem : l.S.mem = []) (hreg : l.S.regions = [frameR])
    (hkeep : ∀ i ∈ 11 :: fKeepRegs, l.S.reg i = .var i) (h2 : l.S.reg 2 = .ptr 0 0) {i : Nat}
    (hi : i = 12 ∨ i = 13)
    (h10 : l.S.reg 10 = .bin .add (.bin .sll (.var i) (.lit 3)) (.lit 0xa0534000))
    (hsem : ∀ g m, AFJ2 g m → (∀ b ∈ l.conds, b.eval (envOf shapeFJ g m) = true) →
      m.reg ⟨i, by omega⟩ = BitVec.ofNat 64 (fsc g) ∧ fsc g < 22) :
    LeafGoal freePlan fJ2 l := by
  intro g m hA hc
  have hm : Match (fJ2.env g m) fJ2.S m := (cutFJ (pc := 0x80042134) (A := AFJ2)
    (bud := fun _ _ => 16) (fun _ _ h => h.1) g m hA).2.1
  obtain ⟨hkv, hk⟩ := hsem g m hA hc
  obtain ⟨⟨hpre, -, ⟨hK, h2m, h11⟩, hs⟩, -⟩ := hA
  refine ⟨by rw [hob]; simp, by show l.S.steps - 0 ≤ 16; omega, fun m' hm' he hso => ?_⟩
  have hmm : m'.mem = m.mem := funext fun a =>
    written_only hm rfl hm' (by rw [hreg]; rfl) hso a (by rw [hmem]; rintro ⟨w, hw, -⟩; cases hw)
  have hv := fJ_var fJ2 rfl g m
  rw [hex] at he ⊢
  have hpc : m'.pc.toNat = 0x80042170 := he
  have hvi : Sym.eval (fJ2.env g m) (.var i) = BitVec.ofNat 64 (fsc g) := by
    rw [← hkv]; rcases hi with rfl | rfl <;> rfl
  refine ExitGoal.at_cut rfl ⟨fF, by simp [freePlan], hpc, ⟨⟨hpre, hpc, ⟨fun j hj => ?_, ?_, ?_⟩,
    saved_mem hmm hs⟩, hk, ?_⟩, by show 7 ≤ 16 - (l.S.steps - 0); omega⟩
  · exact (reg_var hm' j (hkeep j.val (List.mem_cons_of_mem _ hj))).trans ((hv j).trans (hK j hj))
  · rw [Match.reg_of hm' 2 _ h2]; show m.reg 2 + BitVec.ofInt 64 0 = _; simp [h2m]
  · exact (reg_var hm' 11 (hkeep 11 (List.mem_cons_self ..))).trans ((hv 11).trans h11)
  · rw [Match.reg_of hm' 10 _ h10, Sym.eval_bin, Sym.eval_bin, hvi, Sym.eval_lit, Sym.eval_lit]
    exact shl3_add hk

/-- The callee-saved registers `free` never touches (`sp`, `s0` come back from the frame). -/
def fSavedRegs : List Nat := [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem fSaved_sub {i : Nat} (h : i ∈ fSavedRegs) : i ∈ fKeepRegs := by
  simp only [fSavedRegs, fKeepRegs, List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega

theorem returns_free {g : Sig} {m' : Machine} {env : Env} {S : SState} {r : Nat}
    (hm' : Match env S m') (hkeep : ∀ i ∈ fSavedRegs, S.reg i = .var i)
    (h2 : S.reg 2 = .ptr r 16) (h8 : S.reg 8 = .init r 0 8)
    (hv : ∀ i : Fin 32, i.val ∈ fSavedRegs → env.vars i.val = g.m.reg i)
    (hra : (Sym.init r 8 8).eval env = g.m.reg 1) (hs0 : (Sym.init r 0 8).eval env = g.m.reg 8)
    (hb : env.base r = g.m.reg 2 - 16)
    (hpc : m'.pc = (Sym.bin .and (.init r 8 8) (.lit 18446744073709551614)).eval env) :
    Returns g.m m' := by
  refine ⟨by rw [hpc]; simp only [Sym.eval_bin, Sym.eval_lit, BinOp.eval, hra, notOne], fun i hi => ?_⟩
  simp only [calleeSaved, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | hi
  · rw [Match.reg_of hm' 2 _ h2]; show env.base r + BitVec.ofInt 64 16 = _
    rw [hb]; simp [BitVec.sub_add_cancel]
  · rw [Match.reg_of hm' 8 _ h8]; exact hs0
  · have hk : i.val ∈ fSavedRegs := by
      simp only [fSavedRegs, List.mem_cons, List.mem_nil_iff, or_false]
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (reg_var hm' i (hkeep i.val hk)).trans (hv i hk)

/-- An oversized block (`class = 22`): `free` only restores the frame and returns. -/
theorem leafFRet {l : Leaf}
    (hex : l.exit = .ret (.bin .and (.init 0 8 8) (.lit 18446744073709551614)))
    (hob : l.obligs = [.aligned (.bin .and (.init 0 8 8) (.lit 18446744073709551614)) 4])
    (hst : l.S.steps ≤ 16) (hmem : l.S.mem = []) (hreg : l.S.regions = [frameR])
    (hkeep : ∀ i ∈ fSavedRegs, l.S.reg i = .var i)
    (h2 : l.S.reg 2 = .ptr 0 16) (h8 : l.S.reg 8 = .init 0 0 8) :
    LeafGoal freePlan fJ2 l := by
  intro g m hA _
  have hcut := cutFJ (pc := 0x80042134) (A := AFJ2) (bud := fun _ _ => 16) (fun _ _ h => h.1) g m hA
  have hwf : Env.WF (fJ2.env g m) fJ2.S := hcut.1
  have hm : Match (fJ2.env g m) fJ2.S m := hcut.2.1
  obtain ⟨⟨hpre, -, ⟨hK, h2m, -⟩, hs⟩, -⟩ := hA
  have hb : (fJ2.env g m).base 0 = g.m.reg 2 - 16 := by rw [← h2m]; rfl
  obtain ⟨hra, hs0⟩ := saved_ra hwf hm rfl rfl rfl hb hs
  have hv := fJ_var fJ2 rfl g m
  refine ⟨?_, by show l.S.steps - 0 ≤ 16; omega, fun m' hm' he hso => ?_⟩
  · rw [hob]; simp only [List.mem_singleton, forall_eq, Oblig.holds, Sym.eval_bin, Sym.eval_lit,
      BinOp.eval, hra, notOne]
    exact hpre.2.2.2.2.2.2.2.1
  have hmm : m'.mem = m.mem := funext fun a =>
    written_only hm rfl hm' (by rw [hreg]; rfl) hso a (by rw [hmem]; rintro ⟨w, hw, -⟩; cases hw)
  rw [hex] at he ⊢
  have hret := returns_free hm' hkeep h2 h8 (fun i hi => (hv i).trans (hK i (fSaved_sub hi))) hra hs0
    hb he
  have hstk := hpre.2.2.2.2.2.2.1
  have hfr : CalleeFrameFree (Priv g.L) g.m := hpre.2.2.2.2.2.2.2.2.1
  have hfb := hpre.2.2.2.2.2.2.2.2.2
  have hout : ∀ a, ¬ InRange (g.m.reg 2 - 16) 16 a → m'.mem a = g.m.mem a := fun a ha => by
    rw [hmm]; exact hs.2.2 a ha
  have hheap : Heap g.L m' := heap_frame _ _ _ hpre.1 (fun a hp => hout a fun hf => hfr a hf hp)
    (fun b hb' j hj => by
      rw [hmm]; exact saved_pres hstk hs _ (((live_ok _ _ hpre.1).2 b hb').2 j hj))
  refine ⟨hret, fun a ha => hout a fun hf => ha (.inr (.inr hf)), erase_ok hheap hpre.2.1,
    fun a ha => priv_erase hpre.2.1 ha⟩

/-! ## The push leaf -/

/-- The freed block's first word: in the block or in its private tail. -/
theorem word_split {L : List (Word × Nat)} {st : St} (hg : Good L st) {p : Word} {n : Nat}
    (hb : (p, n) ∈ L) {a : Word} (ha : InRange p 8 a) : InRange p n a ∨ Priv L a := by
  have hin := hg.live_in hb
  simp only at hin
  have := eight_le_cap n
  have ha' : InRange (BitVec.ofNat 64 p.toNat) 8 a := by rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨t, ht, rfl⟩ := inRange_lit (by unfold heapTop at hin; omega) ha'
  exact live_word hg hb ht

/-- The push: the head cell gets the block, the block's first word the old head. -/
theorem leafFPush {l : Leaf}
    (hex : l.exit = .ret (.bin .and (.init 2 8 8) (.lit 18446744073709551614)))
    (hob : l.obligs = [.aligned (.bin .and (.init 2 8 8) (.lit 18446744073709551614)) 4])
    (hst : l.S.steps ≤ 7) (hreg : l.S.regions = SFF.regions)
    (hmemw : l.S.mem = [⟨0, 0, 8, .ptr 1 0⟩, ⟨1, 0, 8, .init 0 0 8⟩])
    (hr0 : readConst l.S 0 0 8 = .ptr 1 0) (hr1 : readConst l.S 1 0 8 = .init 0 0 8)
    (hc0 : readConst SFF 0 0 8 = .init 0 0 8)
    (hkeep : ∀ i ∈ fSavedRegs, l.S.reg i = .var i)
    (h2 : l.S.reg 2 = .ptr 2 16) (h8 : l.S.reg 8 = .init 2 0 8) :
    LeafGoal freePlan fF l := by
  intro g m hA _
  have hcut := FreeF.cut_80042170 g m hA
  have hwf : Env.WF (fF.env g m) fF.S := hcut.1
  have hm : Match (fF.env g m) fF.S m := hcut.2.1
  obtain ⟨⟨hpre, -, ⟨hK, h2m, h11⟩, hs⟩, hk, h10⟩ := hA
  have hstk := hpre.2.2.2.2.2.2.1
  have hfr : CalleeFrameFree (Priv g.L) g.m := hpre.2.2.2.2.2.2.2.2.1
  have hbL := hpre.2.1
  obtain ⟨st, hd, hg⟩ := hpre.1
  have hin := hg.live_in hbL
  simp only at hin
  have hp8 : (g.m.reg 11).toNat + 8 < 2 ^ 64 := by
    unfold heapTop at hin; have := le_cap (flen g); omega
  have hcellA : m.reg 10 + 8 = BitVec.ofNat 64 (flBase + 8 * fsc g) := by
    rw [h10]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by unfold flBase; omega)]
    unfold flBase; simp; omega
  have hcellP : ∀ t < 8, Priv g.L (BitVec.ofNat 64 (flBase + 8 * fsc g + t)) :=
    fun t ht => priv_cell hg (by unfold flBase; omega)
  have hcellF := frame_avoid hfr (by unfold flBase; omega) hcellP
  have hcellPa : ∀ a, InRange (BitVec.ofNat 64 (flBase + 8 * fsc g)) 8 a → Priv g.L a := fun a ha => by
    obtain ⟨t, ht, rfl⟩ := inRange_lit (by unfold flBase; omega) ha
    exact hcellP t ht
  have e0 : (fF.env g m).base 0 = BitVec.ofNat 64 (flBase + 8 * fsc g) := hcellA
  have e1 : (fF.env g m).base 1 = g.m.reg 11 := h11
  have hb2 : (fF.env g m).base 2 = g.m.reg 2 - 16 := h2m
  obtain ⟨hra, hs0⟩ := saved_ra (r := 2) hwf hm rfl rfl rfl hb2 hs
  have hv : ∀ i : Fin 32, (fF.env g m).vars i.val = m.reg i := envOf_var shapeFF g m
  refine ⟨?_, by show l.S.steps - 0 ≤ 7; omega, fun m' hm' he hso => ?_⟩
  · rw [hob]; simp only [List.mem_singleton, forall_eq, Oblig.holds, Sym.eval_bin, Sym.eval_lit,
      BinOp.eval, hra, notOne]
    exact hpre.2.2.2.2.2.2.2.1
  have hwo := written_only hm rfl hm' hreg hso
  have hwr : ∀ a, (∃ w ∈ l.S.mem, ∃ j, w.off ≤ j ∧ j < w.off + w.n ∧
      a = (fF.env g m).base w.r + BitVec.ofNat 64 j) →
      InRange (BitVec.ofNat 64 (flBase + 8 * fsc g)) 8 a ∨ InRange (g.m.reg 11) 8 a := by
    rintro a ⟨w, hw, j, hj1, hj2, rfl⟩
    rw [hmemw] at hw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl <;> simp only at hj1 hj2
    · left; rw [e0, ← ofNat_add_nat, inRange_ofNat (by unfold flBase; omega) (by unfold flBase; omega)]
      omega
    · right; rw [e1]; unfold InRange; rw [toNat_add_ofNat (by omega)]; omega
  -- the head cell now holds the block, the block's first word the old head
  have hcellv : rd m' (flBase + 8 * fsc g) = some (g.m.reg 11) := by
    have h := rd_cst (wf_regions hwf hreg) hm' (r := 0) (off := 0) (R := wordR) (by rw [hreg]; rfl)
      (by show 0 + 8 ≤ 8; decide)
    rw [e0, toNat_ofNat_lt (by unfold flBase; omega), Nat.add_zero, hr0] at h
    rw [h]; congr 1; show (fF.env g m).base 1 + BitVec.ofInt 64 0 = _; rw [e1]; simp
  have hnext : rd m' (g.m.reg 11).toNat = rd g.m (flBase + 8 * fsc g) := by
    have h := rd_cst (wf_regions hwf hreg) hm' (r := 1) (off := 0) (R := wordR) (by rw [hreg]; rfl)
      (by show 0 + 8 ≤ 8; decide)
    have h0 := rd_cst hwf hm (r := 0) (off := 0) (R := wordR) rfl (by show 0 + 8 ≤ 8; decide)
    rw [e1, Nat.add_zero, hr1] at h
    rw [e0, toNat_ofNat_lt (by unfold flBase; omega), Nat.add_zero, show fF.S = SFF from rfl, hc0] at h0
    rw [h, ← h0]
    refine rd_congr (a := flBase + 8 * fsc g) (by unfold flBase; omega)
      fun t ht => hs.2.2 _ ?_
    exact hcellF _ (by rw [inRange_ofNat (by unfold flBase; omega) (by unfold flBase; omega)]; omega)
  have hagree : ∀ a, Priv g.L a → ¬ InRange (BitVec.ofNat 64 (flBase + 8 * fsc g)) 8 a →
      ¬ InRange (g.m.reg 11) (cap (flen g)) a → m'.mem a = g.m.mem a := fun a hpa hnc hnb => by
    rw [hwo a fun hw => (hwr a hw).elim hnc fun h8 => hnb (by
      have := eight_le_cap (flen g); unfold InRange at h8 ⊢; omega)]
    exact hs.2.2 a fun hf => hfr a hf hpa
  have hpres : ∀ a, Arena a → (g.m.mem a).isSome → (m'.mem a).isSome := fun a _ h =>
    pres_of hm' hreg hso a (saved_pres hstk hs a h)
  have hcap : classBytes (fsc g) = cap (flen g) := by
    unfold cap; unfold fsc at hk ⊢; rw [if_pos hk]
  have hheap := push_ok hd hg hbL hk hcap hcellv hnext hagree hpres
  rw [hex] at he ⊢
  have hret := returns_free hm' hkeep h2 h8 (fun i hi => (hv i).trans (hK i (fSaved_sub hi))) hra
    hs0 hb2 he
  refine ⟨hret, fun a ha => ?_, hheap, fun a ha => priv_erase hbL ha⟩
  rw [hwo a fun hw => (hwr a hw).elim (fun hc => ha (.inl (hcellPa a hc))) fun h8 =>
    (word_split hg hbL h8).elim (fun hb => ha (.inr (.inl hb))) fun hp => ha (.inl hp)]
  exact hs.2.2 a fun hf => ha (.inr (.inr hf))

end ZesuExec.Fn.Alloc
