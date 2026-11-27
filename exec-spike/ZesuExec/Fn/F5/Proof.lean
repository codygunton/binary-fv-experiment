import ZesuExec.Fn.F5.Runs
import ZesuExec.Fn.F4.Lemmas
import ZesuExec.Fn.F4.Witness

/-!
# F5 proof: `array_list.Aligned(input.AccessListEntry,null).toOwnedSlice` against its contract

The same code as F4 with element size 40 (`slli 5` + `slli 3` for the byte counts, `mulhu` by 40
for the overflow checks) and log2 alignment 3 for the allocator calls. Paths (own steps + callee
bounds): length 0 and capacity 0 (45); length 0: `free`, return (96); length > 0: `remap` (F0,
returns null), `alloc`, then OutOfMemory (137) or `memcpy`, `free` and return
(97 + 9 + 53 + 3 + 42 = 204).
-/

namespace ZesuExec.Fn.F5
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Fn.ToOwned

theorem mul40 (x : Word) :
    BinOp.eval .add (BinOp.eval .sll x (BitVec.ofNat 64 5)) (BinOp.eval .sll x (BitVec.ofNat 64 3)) =
      BitVec.ofNat 64 (x.toNat * elemBytes) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.eval, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat, elemBytes, Nat.reducePow, Nat.reduceMod]
  omega

theorem mulhu40 {x : Word} (h : x.toNat * elemBytes < 2 ^ 32) :
    BinOp.eval .mulhu x (BitVec.ofNat 64 40) = 0 := by
  have h40 : (BitVec.ofNat 64 40).toNat = 40 := rfl
  simp only [BinOp.eval, h40, elemBytes] at h ⊢
  rw [Nat.div_eq_of_lt (by omega)]; rfl

theorem shl40 (x : Word) :
    x <<< ((BitVec.ofNat 64 5).toNat % 64) + x <<< ((BitVec.ofNat 64 3).toNat % 64) =
      BitVec.ofNat 64 (x.toNat * elemBytes) := mul40 x

theorem hi40 {x : Word} (h : x.toNat * elemBytes < 2 ^ 32) :
    BitVec.ofNat 64 (x.toNat * (BitVec.ofNat 64 40).toNat / 2 ^ 64) = 0 := mulhu40 h

theorem ofNat_toNat_lt {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 64 k).toNat = k := by
  simp only [BitVec.toNat_ofNat]; omega

section
variable {A : AllocAssumptions zesuImage} {L : List (Word × Nat)} {items : List Byte}
  {m : Machine}

/-- The end of the success path: the result holds the new block and the length, the header
the old pointer with length and capacity 0. -/
theorem stage4 (E : Entry elemBytes A L items m) {env : Env} {m4 : Machine} {p' : Word}
    (he : EnvOk m env) (hm : Match env S4 m4) (hwf : Env.WF env S4)
    (hpc : m4.pc.toNat = 0x800d6744) (hinv : Inv elemBytes A L m m4)
    (hn0 : 0 < (listLen m).toNat)
    (hv310 : env.vars 310 = p') (hp'0 : 0 < p'.toNat)
    (hp'ram : RamRange p' ((listLen m).toNat * elemBytes))
    (hitems : BytesAt m4 p' items)
    (hscr : BytesAt m4 scratch (wordBytes (BitVec.ofNat 64 ((listLen m).toNat * elemBytes))))
    (hheap : A.Heap (L.erase (listPtr m, (listCap m).toNat * elemBytes) ++
      [(p', (listLen m).toNat * elemBytes)]) m4)
    (hpriv : ∀ a, A.Priv (L.erase (listPtr m, (listCap m).toNat * elemBytes) ++
      [(p', (listLen m).toNat * elemBytes)]) a →
        A.Priv L a ∨ InRange (listPtr m) ((listCap m).toNat * elemBytes) a)
    (hblk : ∀ a, InRange p' ((listLen m).toNat * elemBytes) a → A.Priv L a) :
    Reaches zesuImage 19 (Post A L items m) m4 := by
  refine run_reaches' run4 hwf hm hpc (hinv.ro E) ?_
  intro l hl hc
  simp only [run4_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  subst hl
  refine ⟨fun o ho => ?_, by decide, fun mf hmf hex hfr hp => Reaches.done ?_⟩
  · simp at ho; subst ho; exact ret_oblig E he
  exact success_post E he (S := S4) (by decide) (by decide) (hwf.congr (by decide)) hmf (by decide)
    (by decide) hex (by decide) (by decide) (by decide) hv310 (by decide) (by decide) (by decide)
    hinv hfr hp hn0 hp'0 hp'ram hitems hscr hheap hpriv hblk

/-- After `memcpy`: `free` the old buffer, then `stage4`. -/
theorem stage3 (E : Entry elemBytes A L items m) {env : Env} {m3 : Machine} {p' : Word}
    (he : EnvOk m env) (hm : Match env S3 m3) (hwf : Env.WF env S3)
    (hpc : m3.pc.toNat = 0x800d6714) (hinv : Inv elemBytes A L m m3)
    (hn0 : 0 < (listLen m).toNat)
    (hv310 : env.vars 310 = p') (hp'0 : 0 < p'.toNat)
    (hp'ram : RamRange p' ((listLen m).toNat * elemBytes))
    (hitems : BytesAt m3 p' items)
    (hscr : BytesAt m3 scratch (wordBytes (BitVec.ofNat 64 ((listLen m).toNat * elemBytes))))
    (hheap : A.Heap (L ++ [(p', (listLen m).toNat * elemBytes)]) m3)
    (hpriv : ∀ a, A.Priv (L ++ [(p', (listLen m).toNat * elemBytes)]) a → A.Priv L a)
    (hblk : ∀ a, InRange p' ((listLen m).toNat * elemBytes) a → A.Priv L a) :
    Reaches zesuImage 73 (Post A L items m) m3 := by
  have hc0 : 0 < (listCap m).toNat := by have := E.nc; omega
  refine run_reaches' run3 hwf hm hpc (hinv.ro E) ?_
  intro l hl hc
  simp only [run3_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl
  · exfalso; sym_simp at hc; rw [he.init_eq _ _ _ (.inl rfl), E.cap] at hc
    simp only [beq_iff_eq] at hc; rw [hc] at hc0; simp at hc0
  refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr hp => ?_⟩
  obtain ⟨-, hbufL⟩ := E.buf hc0
  have g1 : mc.reg 1 = BitVec.ofNat 64 0x800d6744 := by rw [Match.reg_eq hmc 1 1 rfl]; rfl
  refine Reaches.mono (b := 42 + 19) ?_ (by decide) fun _ h => h
  refine free_step (F := 400) E (by decide) he (by decide) (by decide) hmc hwf (by simpa using hex)
    hfr hp hinv hc0 hheap hpriv (List.mem_append_left _ hbufL) (by decide) ?_ ?_ ?_
    (by unfold RetAligned; rw [g1]; decide) ?_ ?_
  · rw [Match.reg_eq hmc 11 11 rfl]; show (Sym.init 2 0 8).eval env = _
    rw [he.init_eq _ _ _ (.inl rfl), E.ptr]
  · rw [Match.reg_eq hmc 12 12 rfl]
    show (BinOp.eval .add (BinOp.eval .sll ((Sym.init 2 16 8).eval env) (BitVec.ofNat 64 5))
      (BinOp.eval .sll ((Sym.init 2 16 8).eval env) (BitVec.ofNat 64 3))).toNat = _
    rw [he.init_eq _ _ _ (.inl rfl), E.cap, mul40, ofNat_toNat_lt E.capBound]
  · rw [Match.reg_eq hmc 13 13 rfl]; show (BitVec.ofNat 64 3).toNat ≤ 3; decide
  · rw [Match.reg_eq hmc 2 2 rfl]; show env.base 0 + BitVec.ofInt 64 0 = _; rw [he.base0]; simp
  intro m4 hm4 hwf4 hret hinv4 hheap4 hpriv4 hsame
  have hL : (L ++ [(p', (listLen m).toNat * elemBytes)]).erase (listPtr m, (listCap m).toNat * elemBytes) =
      L.erase (listPtr m, (listCap m).toNat * elemBytes) ++ [(p', (listLen m).toNat * elemBytes)] :=
    List.erase_append_left _ hbufL
  rw [hL] at hheap4 hpriv4
  -- the old and new blocks are apart
  have hlive := (A.live_ok _ m3 hheap).1
  have hapart : ∀ a, InRange p' ((listLen m).toNat * elemBytes) a →
      ¬ InRange (listPtr m) ((listCap m).toNat * elemBytes) a := by
    intro a h1 h2
    have := (List.pairwise_append.mp hlive).2.2 _ hbufL _ (List.mem_singleton_self _)
    simp only [InRange] at h1 h2 this; omega
  refine stage4 E (he.setVars (by decide) _) hm4 hwf4 (by rw [hret.1, g1]; decide) hinv4 hn0
    (by simp [Env.setVars, hv310]) hp'0 hp'ram ?_ ?_ hheap4 hpriv4 hblk
  · intro i hi
    have hin : InRange p' ((listLen m).toNat * elemBytes) (p' + BitVec.ofNat 64 i) := by
      have hlen := E.itemsLen; have hram := hp'ram; have hb := E.lenBound
      unfold RamRange Layout.ramHi at hram
      simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
    rw [hsame _ (fun h => A.priv_not_live _ _ h ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hin⟩)
      (hapart _ hin) (fun h => E.priv _ (.inr (.inr (.inr (.inl ⟨h.1, by have := h.2; omega⟩))))
        (hblk _ hin)) (fun h => E.ownNotPriv h (hblk _ hin))]
    exact hitems i hi
  · intro i hi
    have hi8 : i < 8 := by simpa [wordBytes] using hi
    obtain ⟨hs1, hs2⟩ := E.scratchSafe hi8
    rw [hsame _ (fun h => hs1 (hpriv _ h)) (fun h => ?_) hs2 (E.scratchNotOwn hi8)]
    · exact hscr i hi
    · obtain ⟨-, -, -, -, d⟩ := E.dbuf hc0
      simp only [Apart, InRange, scratch_toNat i hi8] at d h
      simp [scratch, Layout.extraParams] at d h; omega

/-- After `alloc`: OutOfMemory, or `memcpy` then `stage3`. -/
theorem stage2 (E : Entry elemBytes A L items m) {env : Env} {m2 : Machine}
    (he : EnvOk m env) (hm : Match env S2 m2) (hwf : Env.WF env S2)
    (hpc : m2.pc.toNat = 0x800d66f8) (hinv : Inv elemBytes A L m m2)
    (hn0 : 0 < (listLen m).toNat)
    (hv310 : env.vars 310 = m2.reg 10)
    (hv322 : env.vars 322 = BitVec.ofNat 64 ((listLen m).toNat * elemBytes))
    (hitemsP : BytesAt m2 (listPtr m) items) (hscr : ScratchSame m m2)
    (hout : AllocOut A L ((listLen m).toNat * elemBytes) m2) :
    Reaches zesuImage 83 (Post A L items m) m2 := by
  refine run_reaches' run2 hwf hm hpc (hinv.ro E) ?_
  intro l hl hc
  simp only [run2_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl
  · -- null: OutOfMemory
    sym_simp at hc; simp only [beq_iff_eq, hv310] at hc
    have hheap : A.Heap L m2 := by
      rcases hout with ⟨-, h⟩ | ⟨hne, -⟩
      · exact h
      · exact absurd hc hne
    refine ⟨fun o ho => ?_, by decide, fun mf hmf hex hfr hp => Reaches.done ?_⟩
    · simp at ho; subst ho; exact ret_oblig E he
    exact oom_post E he (S := S2) (by decide) (by decide) (hwf.congr (by decide)) hmf (by decide)
      (by decide) hex (by decide) (by decide) (by decide) (by decide) hinv hfr hp hn0 hheap hscr
  · -- a block: copy the items with `memcpy`, then free the old buffer
    sym_simp at hc; simp only [bne_iff_ne, ne_eq, hv310] at hc
    obtain ⟨hne, hheap, hram', hpres', hblk, hpriv⟩ := hout.resolve_left fun h => hc h.1
    refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr hp => ?_⟩
    have g1 : mc.reg 1 = BitVec.ofNat 64 0x800d6714 := by rw [Match.reg_eq hmc 1 1 rfl]; rfl
    refine Reaches.mono (b := 3 + 73) ?_ (by decide) fun _ h => h
    refine copy_step E (by decide) he (by decide) (by decide) hwf hmc hex hfr hp hinv hn0 hitemsP
      hheap hram' hpres' hblk hpriv ?_ ?_ ?_ (by unfold RetAligned; rw [g1]; decide) ?_
    · rw [Match.reg_eq hmc 10 10 rfl]; exact hv310
    · rw [Match.reg_eq hmc 11 11 rfl]; show (Sym.init 2 0 8).eval env = _
      rw [he.init_eq _ _ _ (.inl rfl), E.ptr]
    · rw [Match.reg_eq hmc 12 12 rfl]; exact hv322
    intro m3 hm3 hwf3 hpc3 hinv3 hitems3 hscr3 hheap3
    exact stage3 E he hm3 hwf3 (by rw [hpc3, g1]; decide) hinv3 hn0 hv310
      (by have : (m2.reg 10).toNat ≠ 0 := fun e => hne (BitVec.eq_of_toNat_eq (by simpa using e))
          omega) hram' hitems3 hscr3 hheap3 hpriv hblk


/-- After `remap` (which returned null): `alloc`, then `stage2`. -/
theorem stage1 (E : Entry elemBytes A L items m) {env : Env} {m1 : Machine}
    (he : EnvOk m env) (hm : Match env S1 m1) (hwf : Env.WF env S1)
    (hpc : m1.pc.toNat = 0x800d6638) (hinv : Inv elemBytes A L m m1)
    (hn0 : 0 < (listLen m).toNat) (hheap : A.Heap L m1) (hscr : ScratchSame m m1)
    (hitems : BytesAt m1 (listPtr m) items) :
    Reaches zesuImage 154 (Post A L items m) m1 := by
  have hb := E.lenBound
  refine run_reaches' run1 hwf hm hpc (hinv.ro E) ?_
  intro l hl hc
  simp only [run1_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exfalso; sym_simp at hc; rw [he.init_eq _ _ _ (.inl rfl), E.len, shl40] at hc
    have h := congrArg BitVec.toNat (beq_iff_eq.mp hc.2)
    rw [ofNat_toNat_lt hb] at h; simp only [elemBytes, BitVec.toNat_ofNat] at h; omega
  · refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr hp => ?_⟩
    have g1 : mc.reg 1 = BitVec.ofNat 64 0x800d66f8 := by rw [Match.reg_eq hmc 1 1 rfl]; rfl
    have h22 : mc.reg 22 = BitVec.ofNat 64 ((listLen m).toNat * elemBytes) := by
      rw [Match.reg_eq hmc 22 22 rfl]
      show BinOp.eval .add (BinOp.eval .sll ((Sym.init 2 8 8).eval env) (BitVec.ofNat 64 5))
        (BinOp.eval .sll ((Sym.init 2 8 8).eval env) (BitVec.ofNat 64 3)) = _
      rw [he.init_eq _ _ _ (.inl rfl), E.len, mul40]
    refine Reaches.mono (b := 53 + 83) ?_ (by decide) fun _ h => h
    refine alloc_step (F := 300) (sz := (listLen m).toNat * elemBytes) E he (by decide) (by decide) hmc hwf (by simpa using hex) hfr hp
      hinv hheap hscr hitems (by decide) ?_ ⟨Nat.mul_pos hn0 (by decide), by omega⟩ ?_
      (by unfold RetAligned; rw [g1]; decide) ?_ ?_
    · rw [Match.reg_eq hmc 11 11 rfl]
      show (BinOp.eval .add (BinOp.eval .sll ((Sym.init 2 8 8).eval env) (BitVec.ofNat 64 5))
        (BinOp.eval .sll ((Sym.init 2 8 8).eval env) (BitVec.ofNat 64 3))).toNat = _
      rw [he.init_eq _ _ _ (.inl rfl), E.len, mul40, ofNat_toNat_lt hb]
    · rw [Match.reg_eq hmc 12 12 rfl]; show (BitVec.ofNat 64 3).toNat ≤ 3; decide
    · rw [Match.reg_eq hmc 2 2 rfl]; show env.base 0 + BitVec.ofInt 64 0 = _; rw [he.base0]; simp
    intro m2 hm2 hwf2 hret hinv2 hscr2 hitems2 hout
    exact stage2 E (he.setVars (by decide) _) hm2 hwf2 (by rw [hret.1, g1]; decide) hinv2 hn0
      (by simp [Env.setVars]) (by simp [Env.setVars]; rw [hret.2 22 (by decide), h22])
      hitems2 hscr2 hout
  · exfalso; sym_simp at hc; rw [he.init_eq _ _ _ (.inl rfl), E.len, hi40 hb] at hc
    simp at hc

/-- Length 0, after `free` of the buffer: reset the list, return `{p, 0}`. -/
theorem stage1f (E : Entry elemBytes A L items m) {env : Env} {m1 : Machine}
    (he : EnvOk m env) (hm : Match env S1f m1) (hwf : Env.WF env S1f)
    (hpc : m1.pc.toNat = 0x800d65f8) (hinv : Inv elemBytes A L m m1)
    (hn : (listLen m).toNat = 0) (hc0 : 0 < (listCap m).toNat)
    (hheap : A.Heap (L.erase (listPtr m, (listCap m).toNat * elemBytes)) m1)
    (hpriv : ∀ a, A.Priv (L.erase (listPtr m, (listCap m).toNat * elemBytes)) a →
      A.Priv L a ∨ InRange (listPtr m) ((listCap m).toNat * elemBytes) a)
    (hscr : ScratchSame m m1) :
    Reaches zesuImage 22 (Post A L items m) m1 := by
  have hp0 := E.p0
  refine run_reaches' run1f hwf hm hpc (hinv.ro E) ?_
  intro l hl hc
  simp only [run1f_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · refine ⟨fun o ho => ?_, by decide, fun mf hmf hex hfr hp => Reaches.done ?_⟩
    · simp at ho; subst ho; exact ret_oblig E he
    exact empty_post E he (S := S1f) (by decide) (by decide) (hwf.congr (by decide)) hmf (by decide)
      (by decide) hex (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hinv hfr hp hn (by rw [if_pos hc0]; exact hheap)
      (fun a h => by rw [if_pos hc0] at h; exact (hpriv a h).imp_right fun h => ⟨hc0, h⟩) hscr
  all_goals
    exfalso; sym_simp at hc; rw [he.init_eq _ _ _ (.inl rfl), E.ptr] at hc
    have h := congrArg BitVec.toNat (beq_iff_eq.mp hc.1); simp at h; omega

set_option hygiene false in
/-- Entry leaves with `items.ptr = 0`, `length > capacity = 0`, or a length whose byte count overflows. -/
macro "f5_infeasible" : tactic => `(tactic| (
  sym_simp at hc; simp only [E.len, E.cap, E.ptr, hi40 hb] at hc
  have hp' : listPtr m ≠ 0 := fun h => by rw [h] at hp0; simp at hp0
  have hcn : listCap m = 0 → listLen m = 0 := fun h =>
    BitVec.eq_of_toNat_eq (by rw [h] at hnc; simp at hnc ⊢; omega)
  simp at hc
  all_goals first
    | exact hp' hc.2.2.1
    | exact hc.1 (hcn hc.2.1)))

/-- From the entry: length 0 (return, or `free` then `stage1f`) or `remap` then `stage1`. -/
theorem stage0 (E : Entry elemBytes A L items m) (hpc : m.pc.toNat = entry) :
    Reaches zesuImage bound (Post A L items m) m := by
  have hb := E.lenBound; have hp0 := E.p0; have hnc := E.nc
  refine run_reaches' run0 E.wf E.match hpc E.ro ?_
  intro l hl hc
  simp only [run0_leaves, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- length 0, capacity 0: return
    sym_simp at hc; simp only [E.len, E.cap, beq_iff_eq] at hc
    have hn : (listLen m).toNat = 0 := by rw [hc.1]; rfl
    have hc0 : ¬ 0 < (listCap m).toNat := by rw [hc.2.1]; decide
    refine ⟨fun o ho => ?_, by decide, fun mf hmf hex hfr hp => Reaches.done ?_⟩
    · simp at ho; subst ho; exact ret_oblig E (envOk0 m)
    exact empty_post E (envOk0 m) (S := S0) rfl (by decide) (E.wf.congr (by decide)) hmf (by decide)
      (by decide) hex (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) Inv.refl hfr hp hn (by rw [if_neg hc0]; exact E.heap)
      (fun a h => by rw [if_neg hc0] at h; exact .inl h) (fun _ _ => rfl)
  any_goals (try (exfalso; f5_infeasible; done))
  · -- length 0, capacity > 0: `free`, then `stage1f`
    sym_simp at hc; simp only [E.len, E.cap, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    have hn : (listLen m).toNat = 0 := by rw [hc.1]; rfl
    have hc0 : 0 < (listCap m).toNat := Nat.pos_of_ne_zero fun h => hc.2 (BitVec.eq_of_toNat_eq (by simpa using h))
    obtain ⟨-, hbufL⟩ := E.buf hc0
    refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr hp => ?_⟩
    have g1 : mc.reg 1 = BitVec.ofNat 64 0x800d65f8 := by rw [Match.reg_eq hmc 1 1 rfl]; rfl
    refine Reaches.mono (b := 42 + 22) ?_ (by decide) fun _ h => h
    refine free_step (F := 200) E (by decide) (envOk0 m) rfl (by decide) hmc E.wf (by simpa using hex)
      hfr hp Inv.refl hc0 E.heap (fun _ h => h) hbufL (by decide) ?_ ?_ ?_
      (by unfold RetAligned; rw [g1]; decide) ?_ ?_
    · rw [Match.reg_eq hmc 11 11 rfl]; exact E.ptr
    · rw [Match.reg_eq hmc 12 12 rfl]
      show (BinOp.eval .add (BinOp.eval .sll ((Sym.init 2 16 8).eval (env0 m)) (BitVec.ofNat 64 5))
        (BinOp.eval .sll ((Sym.init 2 16 8).eval (env0 m)) (BitVec.ofNat 64 3))).toNat = _
      rw [E.cap, mul40, ofNat_toNat_lt E.capBound]
    · rw [Match.reg_eq hmc 13 13 rfl]; show (BitVec.ofNat 64 3).toNat ≤ 3; decide
    · rw [Match.reg_eq hmc 2 2 rfl]; show (env0 m).base 0 + BitVec.ofInt 64 0 = _
      rw [(envOk0 m).base0]; simp
    intro m1 hm1 hwf1 hret hinv1 hheap1 hpriv1 hsame
    refine stage1f E ((envOk0 m).setVars (by decide) _) hm1 hwf1 (by rw [hret.1, g1]; decide) hinv1
      hn hc0 (by simpa using hheap1) (by simpa using hpriv1) fun j hj => ?_
    obtain ⟨hs1, hs2⟩ := E.scratchSafe hj
    refine hsame _ hs1 (fun h => ?_) hs2 (E.scratchNotOwn hj)
    obtain ⟨-, -, -, -, d⟩ := E.dbuf hc0
    simp only [Apart, InRange, scratch_toNat j hj] at d h
    simp [scratch, Layout.extraParams] at d h; omega
  · -- length > 0: `remap` (F0), then `stage1`
    sym_simp at hc; simp only [E.len, E.cap, bne_iff_ne, ne_eq] at hc
    have hn0 : 0 < (listLen m).toNat := Nat.pos_of_ne_zero fun h => hc.1 (BitVec.eq_of_toNat_eq (by simpa using h))
    refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr hp => ?_⟩
    have g1 : mc.reg 1 = BitVec.ofNat 64 0x800d6638 := by rw [Match.reg_eq hmc 1 1 rfl]; rfl
    refine Reaches.mono (b := 9 + 154) ?_ (by decide) fun _ h => h
    refine remap_step E (by decide) hmc (by simpa [F0.entry] using hex) hfr hp (by decide)
      (by unfold RetAligned; rw [g1]; decide)
      (by rw [Match.reg_eq hmc 2 2 rfl]; show (env0 m).base 0 + BitVec.ofInt 64 0 = _
          rw [(envOk0 m).base0]; simp) ?_
    intro m1 hm1 hwf1 hret hinv1 hheap1 hscr1 hitems1
    exact stage1 E ((envOk0 m).setVars (by decide) _) hm1 hwf1 (by rw [hret.1, g1]; decide) hinv1
      hn0 hheap1 hscr1 hitems1

end

/-- F5 meets its contract, given the allocator's assumed contracts. -/
theorem f5_spec (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (items : List Byte) :
    Spec zesuImage entry bound (Pre A L items) (Post A L items) :=
  fun _ hpc hpre => stage0 (Entry.of_pre hpre) hpc

/--
info: 'ZesuExec.Fn.F5.f5_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f5_spec

/-- Non-vacuity: `Pre` holds of `m0` with a free 4 KiB RAM window overwritten
(`ToOwned.pre_satisfiable`), for any allocator state `A.Heap [] m0` with the image's rodata. -/
example (A : AllocAssumptions zesuImage) (m0 : Machine) (h0 : A.Heap [] m0)
    (hro : RodataLoaded zesuImage m0) (hwin : ∀ a, Win a → ¬ A.Priv [] a) :
    ∃ m, Pre A [] [] m :=
  ⟨_, pre_satisfiable elemBytes A m0 h0 hro hwin⟩

end ZesuExec.Fn.F5
