import ZesuExec.Fn.DTF.AuthExit

/-!
# DTF: growing the tuple buffer and the store's slot (programme plan S7 step 4)

The remap call returns null (`0x800029a8`), the old block's address is cleared (`0x800029c4`),
`alloc(0x90 newCap, log2 alignment 4)` (`0x800029c8`, return `0x80002a08`), `memcpy` of the `n`
tuples (`0x80002a1c`, return `0x80002a38`), `free(bp, 0x90 n, 4)` when there was an old block
(return `0x80002a6c`), the new block becomes the buffer (`0x8000241c`, `0x80002420`) and the slot
`bp + 0x90 n` is DTF's (`0x80002434`'s `SlotOk`). Tools: `alloc_pre_dtf`, `free_pre_dtf`,
`keptOn`, `app_on`, `blk_facts`, `buf_slot`.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

set_option maxRecDepth 20000

/-! ## Small tools -/

/-- A leaf without obligations. -/
theorem noObl {d : CutData} {l : Leaf} (h : l.obligs = []) :
    ∀ σ m, (mkCut d).A σ m → (∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) →
      ∀ o ∈ l.obligs, o.holds (envOf d.shape σ m) := by
  intro _ _ _ _ o ho
  rw [h] at ho
  cases ho

theorem var_reg {sh : Shape} {σ : Sig} {m : Machine} {i : Nat} (hi : i < 32) :
    (Sym.var i).eval (envOf sh σ m) = m.reg (Fin.ofNat 32 i) := by
  simp [Sym.eval, envOf, hi]

/-- The register a leaf sets, as its symbolic state says. -/
theorem ctx_regv {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {i : Nat} (hi : i < 32) {s : Sym} (h : l.S.reg i = s) :
    m'.reg (Fin.ofNat 32 i) = s.eval (envOf d.shape σ m) := by
  rw [reg_eval C.hm' hi, h]

theorem w_add_mul (a b : Nat) : w a + w b = w (a + b) := by
  simp only [w]; rw [← BitVec.ofNat_add]

/-- `alloc`'s precondition at a DTF call: the live list's heap, the size, the alignment, DTF's
stack below `sp`. -/
theorem alloc_pre_dtf {σ : Sig} {m : Machine} (hc : Common σ m) (hsp : m.reg 2 = σ.fr + w 0)
    (hra : RetAligned m) {L X : List (Word × Nat)} (hlive : Live σ m L X)
    (h0 : 0 < (m.reg 11).toNat) (h63 : (m.reg 11).toNat < 2 ^ 63) (h4 : (m.reg 12).toNat ≤ 4) :
    allocPre σ.A L m := by
  have hpre := hc.2.1
  refine ⟨hlive.1, h0, h63, h4, stack16 hc hsp, hra, fun a ha hP => ?_⟩
  rw [hsp] at ha
  have e2 := below_fr_toNat hpre
  have hsp' := pre_sp hpre
  have hfr := fr_toNat hpre
  unfold frameBytes stackBytes TX.stackBytes Layout.ramLo at *
  exact (stack_R hpre (by rw [e2]; unfold stackBytes TX.stackBytes; omega) (by rw [e2]; omega)
    ha).2 (priv_sub hpre hlive hP)

/-- `free`'s precondition at a DTF call. -/
theorem free_pre_dtf {σ : Sig} {m : Machine} (hc : Common σ m) (hsp : m.reg 2 = σ.fr + w 0)
    (hra : RetAligned m) {L X : List (Word × Nat)} (hlive : Live σ m L X)
    (hmem : (m.reg 11, (m.reg 12).toNat) ∈ X)
    (h0 : 0 < (m.reg 12).toNat) (h63 : (m.reg 12).toNat < 2 ^ 63) (h4 : (m.reg 13).toNat ≤ 4) :
    freePre σ.A L m := by
  have hpre := hc.2.1
  refine ⟨hlive.1, hlive.2.1.symm.subset (List.mem_append_right _ hmem), h0, h63, h4,
    stack16 hc hsp, hra, fun a ha hP => ?_⟩
  rw [hsp] at ha
  have e2 := below_fr_toNat hpre
  have hsp' := pre_sp hpre
  have hfr := fr_toNat hpre
  unfold frameBytes stackBytes TX.stackBytes Layout.ramLo at *
  exact (stack_R hpre (by rw [e2]; unfold stackBytes TX.stackBytes; omega) (by rw [e2]; omega)
    ha).2 (priv_sub hpre hlive hP)

/-- The plain source's `Extra` at `pc`. -/
theorem src_extra {d : CutData} {σ : Sig} {m : Machine} (hpc : d.pc ≠ entry)
    (hs : d.site = none) (hA : (mkCut d).A σ m) {pc : Nat} (h : d.pc = pc) : Extra pc σ m := by
  rw [← h]; exact extra_of_A hpc hs hA

/-- One of DTF's blocks: nonempty, in RAM, present. -/
theorem blk_facts {σ : Sig} {m : Machine} {L X : List (Word × Nat)} (hlive : Live σ m L X)
    {b : Word × Nat} (hb : b ∈ X) : 0 < b.2 ∧ RamRange b.1 b.2 ∧ Present m b.1 b.2 :=
  ⟨(hlive.2.2 b hb).1, (hlive.2.2 b hb).2.1,
    ((σ.A.live_ok L m hlive.1).2 b (hlive.2.1.symm.subset (List.mem_append_right _ hb))).2⟩

/-! ## Frame words a leaf keeps -/

/-- The leaf keeps the frame words `os`. -/
def keptOn (d : CutData) (l : Leaf) (os : List Nat) : Bool :=
  os.all fun o => decide (o + 8 ≤ frameBytes) && (Loc.slot o).sym l.S == (Loc.slot o).sym d.shape.S

theorem ctx_keptOn {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {os : List Nat} (h : keptOn d l os = true) :
    ∀ o ∈ os, m'.load (σ.fr + w o) 8 = m.load (σ.fr + w o) 8 := by
  intro o ho
  have h' := List.all_eq_true.mp h o ho
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  exact ctx_load C h'.1 h'.2

/-- The frame words `AuthApp` names. -/
def appSlots : List Nat := [0x70, 0x68, 0x30, 0x48, 0x78, 0x40, 0x38]

theorem app_on {σ : Sig} {m m' : Machine}
    (h : ∀ o ∈ appSlots, m'.load (σ.fr + w o) 8 = m.load (σ.fr + w o) 8) {n : Nat}
    (ha : AuthApp σ m n) : AuthApp σ m' n := by
  obtain ⟨⟨c, hh, p, j, k, ho, hs, hk, l48⟩, l78, l40, l38⟩ := ha
  have e : ∀ o ∈ appSlots, ∀ {v : Word}, m.load (σ.fr + w o) 8 = some v →
      m'.load (σ.fr + w o) 8 = some v := fun o ho _ hv => by rw [h o ho]; exact hv
  exact ⟨⟨c, hh, p, j, k, authOut_mono (h _ (by decide)) (h _ (by decide)) (h _ (by decide)) ho,
    hs, hk, e _ (by decide) l48⟩, e _ (by decide) l78, e _ (by decide) l40, e _ (by decide) l38⟩

theorem cap_word {σ : Sig} {m : Machine} {n : Nat} {cap : Word}
    (h1 : m.load (σ.fr + w 0x60) 8 = some cap) (h2 : m.load (σ.fr + w 0x60) 8 = some (w n))
    (hn : n < 2 ^ 32) : cap.toNat = n := by
  rw [h1, Option.some.injEq] at h2
  subst h2
  simp only [w, BitVec.toNat_ofNat]; omega

theorem app_n {σ : Sig} {m : Machine} {n : Nat} (hpre : Pre σ.A σ.g σ.m) (h4 : σ.t = 4)
    (ha : AuthApp σ m n) : n < 2 ^ 32 := by
  obtain ⟨⟨c, hh, p, j, k, ho, -⟩, -⟩ := ha
  exact (out_n hpre h4 ho).2.2

theorem new_keep {σ : Sig} {m m' : Machine} (h : LowKeep σ m m')
    (hL : ∀ L X, Live σ m L X → Live σ m' L X) {n : Nat} (hn : AuthNew σ m n) :
    AuthNew σ m' n := by
  obtain ⟨ha, bp, newp, l58, l60, l08, l50, L, X, hlive, h1, h2⟩ := hn
  exact ⟨app_lk h ha, bp, newp, lk h (by decide) l58, lk h (by decide) l60, lk h (by decide) l08,
    lk h (by decide) l50, L, X, hL L X hlive, h1, h2⟩

/-! ## After the remap call (`0x800029a8`): null, the buffer still full -/

theorem remap_ret {σ : Sig} {m : Machine} (hA : (mkCut (table[138]!)).A σ m) :
    (∃ n, AuthGrow σ m n) ∧ m.reg 10 = 0 := by
  obtain ⟨mc, x, hsite, hpost⟩ := ret_parts (i := 138) (by decide) (by decide) hA
  have hsx := hsite.2.2.2.2.2.2.2.2
  rw [show (table[138]!).pc = 0x800029a8 by decide] at hsx
  simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true] at hsx
  obtain ⟨n, hg⟩ := hsx
  have hkd : (siteAt 138).kind = .remap := by decide
  have hSF : (siteAt 138).kind.SiteFine (siteAt 138) = true := by decide
  have hk := ret_keep hSF hsite hpost fun _ _ => by rw [hkd]; rfl
  have hq : F0.Post mc m := by have := hpost.1; rw [hkd] at this; exact this
  have hSF' : Kind.SiteFine .remap (siteAt 138) = true := by rw [← hkd]; exact hSF
  exact ⟨⟨n, grow_lk hk (fun L X hl => remap_live hSF' hsite hq hpost.2 hl) hg⟩, hq.2.1⟩

theorem DTF.leaf_800029a8_0 :
    LeafGoal DTF.plan DTF.plan.cuts[138]! ((DTF.plan.leaves 0x800029a8)[0]!) := by
  refine leaf_at_xo (table[138]!) (table[139]!) ((leavesAt 0x800029a8)[0]!) (by decide)
    DTF.cut_800029a8 (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  obtain ⟨⟨n, hg⟩, h10⟩ := remap_ret hA
  refine ⟨?_, list_budget C (lenFrom_sound C (rs' := (table[139]!).rest) (by decide))
    (by decide)⟩
  rw [show (table[139]!).pc = 0x800029c4 by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  refine ⟨⟨n, grow_lk (ctx_lowKeep C (by decide)) (fun _ _ hl => ctx_live C hl) hg⟩, ?_⟩
  rw [show (10 : Fin 32) = Fin.ofNat 32 10 from rfl, ctx_reg C (i' := 10) (by decide) (by decide)
    (by decide)]
  exact h10

/-- F0 returned null: the non-null branch is vacuous. -/
theorem DTF.leaf_800029a8_1 :
    LeafGoal DTF.plan DTF.plan.cuts[138]! ((DTF.plan.leaves 0x800029a8)[1]!) := by
  refine leaf_at_xo (table[138]!) (table[140]!) ((leavesAt 0x800029a8)[1]!) (by decide)
    DTF.cut_800029a8 (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide)
    fun σ m m' hA hc C => ?_
  have h10 := (remap_ret hA).2
  have hne := hc _ (show SBool.ne (.var 10) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, var_reg (show 10 < 32 by decide), Sym.eval_lit] at hne
  rw [show (Fin.ofNat 32 10 : Fin 32) = 10 from rfl, h10] at hne
  exact absurd hne (by decide)

/-! ## `0x800029c4`, `0x800029c8`: the old block's address cleared, the allocation -/

theorem DTF.leaf_800029c4_0 :
    LeafGoal DTF.plan DTF.plan.cuts[139]! ((DTF.plan.leaves 0x800029c4)[0]!) := by
  refine leaf_at_xo (table[139]!) (table[140]!) ((leavesAt 0x800029c4)[0]!) (by decide)
    DTF.cut_800029c4 (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have hx := src_extra (by decide) (by decide) hA (show (table[139]!).pc = 0x800029c4 by decide)
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true] at hx
  obtain ⟨⟨n, hg⟩, h10⟩ := hx
  refine ⟨?_, list_budget C (lenFrom_sound C (rs' := (table[140]!).rest) (by decide))
    (by decide)⟩
  rw [show (table[140]!).pc = 0x800029c8 by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  refine ⟨⟨n, grow_lk (ctx_lowKeep C (by decide)) (fun _ _ hl => ctx_live C hl) hg⟩, ?_⟩
  rw [show (10 : Fin 32) = Fin.ofNat 32 10 from rfl, ctx_reg C (i' := 10) (by decide) (by decide)
    (by decide)]
  exact h10

theorem grow_29c8 {σ : Sig} {m : Machine} (hA : (mkCut (table[140]!)).A σ m) :
    (∃ n, AuthGrow σ m n) ∧ m.reg 10 = 0 := by
  have hx := src_extra (by decide) (by decide) hA (show (table[140]!).pc = 0x800029c8 by decide)
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true] at hx
  exact hx

theorem DTF.leaf_800029c8_0 :
    LeafGoal DTF.plan DTF.plan.cuts[140]! ((DTF.plan.leaves 0x800029c8)[0]!) := by
  refine leaf_at_xo (table[140]!) (table[122]!) ((leavesAt 0x800029c8)[0]!) (by decide)
    DTF.cut_800029c8 (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide)
    fun σ m m' hA hc C => ?_
  have h10 := (grow_29c8 hA).2
  have hne := hc _ (show SBool.ne (.var 10) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, var_reg (show 10 < 32 by decide), Sym.eval_lit] at hne
  rw [show (Fin.ofNat 32 10 : Fin 32) = 10 from rfl, h10] at hne
  exact absurd hne (by decide)

/-- The new block's size `128 newCap + 16 newCap = 0x90 newCap` (no wrap). -/
theorem grow_size {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {n : Nat} (hg : AuthGrow σ m n) (h4 : σ.t = 4)
    (i16 : (Loc.slot 0x10).sym d.shape.S = .init 0 0x10 8)
    (i24 : (Loc.slot 0x18).sym d.shape.S = .init 0 0x18 8) :
    (Sym.bin .add (.init 0 0x10 8) (.init 0 0x18 8)).eval (envOf d.shape σ m) =
      w (newCap n * 0x90) ∧ 0 < newCap n * 0x90 ∧ newCap n * 0x90 < 2 ^ 63 := by
  obtain ⟨⟨⟨c, hh, p, j, k, ho, -⟩, -⟩, -, -, -, l10, l18, -⟩ := hg
  obtain ⟨-, -, hn⟩ := out_n C.F.common.2.1 h4 ho
  have hcl := newCap_lt hn
  rw [Sym.eval_bin, src_init C (by decide) i16, src_init C (by decide) i24, wordAt_of_load l10,
    wordAt_of_load l18]
  refine ⟨?_, by unfold newCap; omega, by omega⟩
  simp only [BinOp.eval, w]
  rw [← BitVec.ofNat_add]
  congr 1
  omega

/-- The size is never 0: the zero-size branch is vacuous. -/
theorem DTF.leaf_800029c8_1 :
    LeafGoal DTF.plan DTF.plan.cuts[140]! ((DTF.plan.leaves 0x800029c8)[1]!) := by
  refine leaf_at_xo (table[140]!) (table[142]!) ((leavesAt 0x800029c8)[1]!) (by decide)
    DTF.cut_800029c8 (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide)
    fun σ m m' hA hc C => ?_
  obtain ⟨⟨n, hg⟩, -⟩ := grow_29c8 hA
  obtain ⟨e, h0, h63⟩ := grow_size C hg (arm4 C.F.arms (by decide)) (by decide) (by decide)
  have heq := hc _
    (show SBool.eq (.bin .add (.init 0 16 8) (.init 0 24 8)) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, e, Sym.eval_lit, beq_iff_eq] at heq
  have := congrArg BitVec.toNat heq
  have h64 : newCap n * 0x90 < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt h64] at this
  exact absurd this (Nat.pos_iff_ne_zero.mp h0)

/-- The allocation of the new block (`0x800029c8`, leaf 2; return `0x80002a08`): size
`0x90 newCap`, log2 alignment 4. -/
theorem DTF.leaf_800029c8_2 :
    LeafGoal DTF.plan DTF.plan.cuts[140]! ((DTF.plan.leaves 0x800029c8)[2]!) := by
  refine leaf_call_xo (table[140]!) (table[141]!) (siteAt 141) ((leavesAt 0x800029c8)[2]!)
    allocEntry (by decide) DTF.cut_800029c8 (by decide) (by decide) (noObl (by decide))
    (by decide) rfl rfl (by decide) ?_
  intro σ m m' hA hc C CF
  obtain ⟨⟨n, hg⟩, -⟩ := grow_29c8 hA
  obtain ⟨e, h0, h63⟩ := grow_size C hg (arm4 C.F.arms (by decide)) (by decide) (by decide)
  have hg' := grow_lk (ctx_lowKeep C (by decide)) (fun _ _ hl => ctx_live C hl) hg
  have r11 : m'.reg 11 = w (newCap n * 0x90) := by
    rw [show (11 : Fin 32) = Fin.ofNat 32 11 from rfl, ctx_regv C (by decide)
      (s := .bin .add (.init 0 16 8) (.init 0 24 8)) (by decide)]
    exact e
  have r12 : m'.reg 12 = w 4 := by
    rw [show (12 : Fin 32) = Fin.ofNat 32 12 from rfl, ctx_regv C (by decide) (s := .lit 4)
      (by decide)]
    rfl
  have hsp : m'.reg 2 = σ.fr + w 0 := CF.shape.1 (2, .fr 0) (by decide) _ rfl
  obtain ⟨bp, cap, l58, l60, -, -, L, X, hlive, hmem⟩ := hg'.2.1
  have hsz : (m'.reg 11).toNat = newCap n * 0x90 := by
    rw [r11]; simp only [w, BitVec.toNat_ofNat]; omega
  have hidx : IdxOk (siteAt 141).kind σ (L, [], ⟨[], []⟩) m' := by
    rw [show (siteAt 141).kind = .alloc by decide]
    exact ⟨alloc_pre_dtf CF.common hsp CF.aligned hlive (by omega) (by omega)
      (by rw [r12]; decide), X, hlive⟩
  have hsx : SiteX (table[141]!).pc σ (L, [], ⟨[], []⟩) m' := by
    rw [show (table[141]!).pc = 0x80002a08 by decide]
    simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true]
    exact ⟨n, hg', r11, bp, cap, X, l58, l60, hlive, hmem⟩
  refine ⟨_, hidx, hsx, fun m'' hpost => ?_⟩
  have hfld : FieldsOk σ m' (siteFields (table[141]!).pc) := fun f hf => by
    rw [show siteFields (table[141]!).pc = [] by decide] at hf; cases hf
  have hsite : SiteA (siteAt 141) (table[141]!).pc σ (L, [], ⟨[], []⟩) m' :=
    ⟨CF.ra, CF.common, CF.shape, CF.arms, CF.rest, hidx, hfld, CF.chk, hsx⟩
  exact call_list_budget C (by decide) hsite hpost (by decide) (o := 0x68) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide)

/-! ## The new block (`0x80002a08` on) -/

/-- After a non-null allocation (`0x80002a08`): the new block beside the old one. -/
theorem alloc_ret {σ : Sig} {m : Machine} (hA : (mkCut (table[141]!)).A σ m)
    (hnz : m.reg 10 ≠ 0) :
    ∃ n, AuthApp σ m n ∧ ∃ bp, m.load (σ.fr + w 0x58) 8 = some bp ∧
      m.load (σ.fr + w 0x60) 8 = some (w n) ∧ m.load (σ.fr + w 0x08) 8 = some (w (newCap n)) ∧
      ∃ L X, Live σ m L X ∧ (m.reg 10, newCap n * 0x90) ∈ X ∧ (0 < n → (bp, n * 0x90) ∈ X) := by
  obtain ⟨mc, x, hsite, hpost⟩ := ret_parts (i := 141) (by decide) (by decide) hA
  have hsx := hsite.2.2.2.2.2.2.2.2
  rw [show (table[141]!).pc = 0x80002a08 by decide] at hsx
  simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true] at hsx
  obtain ⟨n, hg, r11, bp, cap, X, l58, l60c, hlive, hmem⟩ := hsx
  have hkd : (siteAt 141).kind = .alloc := by decide
  have hSF : (siteAt 141).kind.SiteFine (siteAt 141) = true := by decide
  have hk := ret_keep hSF hsite hpost fun _ _ => by rw [hkd]; rfl
  have hq : allocPost σ.A x.1 mc m := by have := hpost.1; rw [hkd] at this; exact this
  have hpre := hsite.2.1.2.1
  have h4 : σ.t = 4 := arm4 hsite.2.2.2.1 (by decide)
  have hn := app_n hpre h4 hg.1
  have hcl := newCap_lt hn
  have hsz : (mc.reg 11).toNat = newCap n * 0x90 := by
    rw [r11]; simp only [w, BitVec.toNat_ofNat]; omega
  have hcap := cap_word l60c hg.2.2.1 hn
  obtain ⟨-, -, hnew⟩ := hq
  rcases hnew with ⟨h0, -⟩ | ⟨-, hheap, hram, -, hin, -⟩
  · exact absurd h0 hnz
  rw [hsz] at hheap hram hin
  have hliveM : Live σ m (x.1 ++ [(m.reg 10, newCap n * 0x90)])
      (X ++ [(m.reg 10, newCap n * 0x90)]) := by
    refine ⟨hheap, by rw [← List.append_assoc]; exact hlive.2.1.append_right _,
      fun b hb => ?_⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact hlive.2.2 b hb
    · simp only [List.mem_singleton] at hb
      subst hb
      exact ⟨by unfold newCap; omega, hram, fun a ha => priv_sub hpre hlive (hin a ha)⟩
  refine ⟨n, app_lk hk hg.1, bp, lk hk (by decide) l58, lk hk (by decide) hg.2.2.1,
    lk hk (by decide) hg.2.2.2.1, _, _, hliveM, List.mem_append_right _ (List.mem_singleton_self _),
    fun hn0 => List.mem_append_left _ (by rw [← hcap]; exact hmem (by omega))⟩

theorem DTF.leaf_80002a08_0 :
    LeafGoal DTF.plan DTF.plan.cuts[141]! ((DTF.plan.leaves 0x80002a08)[0]!) := by
  refine leaf_at_xo (table[141]!) (table[142]!) ((leavesAt 0x80002a08)[0]!) (by decide)
    DTF.cut_80002a08 (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have hne := hc _ (show SBool.ne (.var 10) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, var_reg (show 10 < 32 by decide), Sym.eval_lit, bne_iff_ne,
    ne_eq] at hne
  rw [show (Fin.ofNat 32 10 : Fin 32) = 10 from rfl] at hne
  obtain ⟨n, ha, bp, l58, l60, l08, L, X, hlive, hnew, hold⟩ := alloc_ret hA hne
  have hk := ctx_keptOn C (os := appSlots ++ [0x58, 0x60, 0x08]) (by decide)
  have e : ∀ o ∈ appSlots ++ [0x58, 0x60, 0x08], ∀ {v : Word}, m.load (σ.fr + w o) 8 = some v →
      m'.load (σ.fr + w o) 8 = some v := fun o ho _ hv => by rw [hk o ho]; exact hv
  have l50 := ctx_word C (o := 0x50) (s := .var 10) (by decide) (by decide)
  rw [var_reg (by decide)] at l50
  refine ⟨?_, list_budget C (lenFrom_sound C (rs' := (table[142]!).rest) (by decide))
    (by decide)⟩
  rw [show (table[142]!).pc = 0x80002a1c by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  exact ⟨n, app_on (fun o ho => hk o (List.mem_append_left _ ho)) ha, bp, m.reg 10,
    e _ (by decide) l58, e _ (by decide) l60, e _ (by decide) l08, l50, L, X, ctx_live C hlive,
    hnew, hold⟩

/-- The copy of the `n` tuples into the new block (`0x80002a1c`; return `0x80002a38`). -/
theorem DTF.leaf_80002a1c_0 :
    LeafGoal DTF.plan DTF.plan.cuts[142]! ((DTF.plan.leaves 0x80002a1c)[0]!) := by
  refine leaf_call_xo (table[142]!) (table[143]!) (siteAt 143) ((leavesAt 0x80002a1c)[0]!)
    Layout.memcpyEntry (by decide) DTF.cut_80002a1c (by decide) (by decide) (noObl (by decide))
    (by decide) rfl rfl (by decide) ?_
  intro σ m m' hA hc C CF
  have hx := src_extra (by decide) (by decide) hA (show (table[142]!).pc = 0x80002a1c by decide)
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true] at hx
  obtain ⟨n, hn⟩ := hx
  have hpre := C.F.common.2.1
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have hn' := new_keep (ctx_lowKeep C (by decide)) (fun _ _ hl => ctx_live C hl) hn
  obtain ⟨ha, bp, newp, l58, l60, l08, l50, L, X, hlive, hnew, hold⟩ := hn
  have hn32 := app_n hpre h4 ha
  have hcl := newCap_lt hn32
  obtain ⟨-, -, l40, l38⟩ := ha
  have r10 : m'.reg 10 = newp := by
    rw [show (10 : Fin 32) = Fin.ofNat 32 10 from rfl, ctx_regv C (by decide)
      (s := .init 0 80 8) (by decide), src_init C (by decide) (by decide), wordAt_of_load l50]
  have r11 : m'.reg 11 = bp := by
    rw [show (11 : Fin 32) = Fin.ofNat 32 11 from rfl, ctx_regv C (by decide)
      (s := .init 0 88 8) (by decide), src_init C (by decide) (by decide), wordAt_of_load l58]
  have r12 : m'.reg 12 = w (n * 0x90) := by
    rw [show (12 : Fin 32) = Fin.ofNat 32 12 from rfl, ctx_regv C (by decide)
      (s := .bin .add (.init 0 56 8) (.init 0 64 8)) (by decide), Sym.eval_bin,
      src_init C (by decide) (by decide), src_init C (by decide) (by decide), wordAt_of_load l38,
      wordAt_of_load l40]
    simp only [BinOp.eval]
    rw [w_add_mul]
    congr 1; omega
  have hlive' := ctx_live C hlive
  have hlen : (m'.reg 12).toNat = n * 0x90 := by
    rw [r12]; simp only [w, BitVec.toNat_ofNat]; omega
  obtain ⟨-, hramN, hpresN⟩ := blk_facts hlive' hnew
  simp only at hramN hpresN
  unfold RamRange Layout.ramHi at hramN
  have hscr : Present m' TX.scratch 8 := CF.common.2.2.2.2.2.2.1
  have hsub : n * 0x90 ≤ newCap n * 0x90 := Nat.mul_le_mul_right _ (by unfold newCap; omega)
  have hidx : IdxOk (siteAt 143).kind σ ([], [], ⟨[], []⟩) m' := by
    rw [show (siteAt 143).kind = .memcpy by decide]
    refine ⟨memcpy_pre_gen CF.aligned hscr fun hpos => ?_, .inr ⟨L, X, hlive',
      (newp, newCap n * 0x90), hnew, fun j hj => ?_⟩⟩
    · rw [hlen] at hpos ⊢
      obtain ⟨-, hramO, hpresO⟩ := blk_facts hlive' (hold (by omega))
      simp only at hramO hpresO
      rw [r10, r11]
      refine ⟨?_, hpresO, ⟨hramN.1, by unfold Layout.ramHi; omega⟩, fun j hj => hpresN j (by omega)⟩
      unfold RamRange at hramO
      simp only [Machine.readable, Machine.inRange, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]
      exact .inr hramO
    · rw [hlen] at hj
      rw [r10]
      simp only [InRange]
      rw [toNat_add_ofNat (by omega)]
      omega
  have hsx : SiteX (table[143]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[143]!).pc = 0x80002a38 by decide]
    simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true]
    refine ⟨n, hn', ?_, r12⟩
    rw [r10]
    exact (ctx_keptOn C (os := [0x50]) (by decide) _ (by decide)).trans l50
  refine ⟨_, hidx, hsx, fun m'' hpost => ?_⟩
  have hfld : FieldsOk σ m' (siteFields (table[143]!).pc) := fun f hf => by
    rw [show siteFields (table[143]!).pc = [] by decide] at hf; cases hf
  have hsite : SiteA (siteAt 143) (table[143]!).pc σ ([], [], ⟨[], []⟩) m' :=
    ⟨CF.ra, CF.common, CF.shape, CF.arms, CF.rest, hidx, hfld, CF.chk, hsx⟩
  exact call_list_budget C (by decide) hsite hpost (by decide) (o := 0x68) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide)

/-- After the copy (`0x80002a38`): the new block, beside the old one. -/
theorem memcpy_ret {σ : Sig} {m : Machine} (hA : (mkCut (table[143]!)).A σ m) :
    ∃ n, AuthNew σ m n := by
  obtain ⟨mc, x, hsite, hpost⟩ := ret_parts (i := 143) (by decide) (by decide) hA
  have hsx := hsite.2.2.2.2.2.2.2.2
  rw [show (table[143]!).pc = 0x80002a38 by decide] at hsx
  simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true] at hsx
  obtain ⟨n, hn, l50, r12⟩ := hsx
  have hkd : (siteAt 143).kind = .memcpy := by decide
  have hSF : (siteAt 143).kind.SiteFine (siteAt 143) = true := by decide
  have hk := ret_keep hSF hsite hpost fun _ _ => by rw [hkd]; rfl
  have hq : MemcpyPost mc m := by have := hpost.1; rw [hkd] at this; exact this
  have hpre := hsite.2.1.2.1
  have h4 : σ.t = 4 := arm4 hsite.2.2.2.1 (by decide)
  have hn32 := app_n hpre h4 hn.1
  refine ⟨n, ?_⟩
  obtain ⟨ha, bp, newp, l58, l60, l08, l50', L, X, hlive, hnew, hold⟩ := hn
  rw [l50', Option.some.injEq] at l50
  have hlen : (mc.reg 12).toNat = n * 0x90 := by
    rw [r12]; simp only [w, BitVec.toNat_ofNat]; omega
  have hsub : n * 0x90 ≤ newCap n * 0x90 := Nat.mul_le_mul_right _ (by unfold newCap; omega)
  have hlive' := memcpy_live hsite.2.1 hq hpost.2 hlive fun a ha' => by
    rw [← l50, hlen] at ha'
    exact ⟨_, hlive.2.1.symm.subset (List.mem_append_right _ hnew), by
      simp only [InRange] at ha' ⊢; omega⟩
  exact ⟨app_lk hk ha, bp, newp, lk hk (by decide) l58, lk hk (by decide) l60,
    lk hk (by decide) l08, lk hk (by decide) l50', L, X, hlive', hnew, hold⟩

/-- No old block (`cap = 0`, `0x80002a38` leaf 0): straight to `0x80002a6c`. -/
theorem DTF.leaf_80002a38_0 :
    LeafGoal DTF.plan DTF.plan.cuts[143]! ((DTF.plan.leaves 0x80002a38)[0]!) := by
  refine leaf_at_xo (table[143]!) (table[144]!) ((leavesAt 0x80002a38)[0]!) (by decide)
    DTF.cut_80002a38 (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  obtain ⟨n, hn⟩ := memcpy_ret hA
  obtain ⟨ha, bp, newp, -, -, l08, l50, L, X, hlive, hnew, -⟩ :=
    new_keep (ctx_lowKeep C (by decide)) (fun _ _ hl => ctx_live C hl) hn
  refine ⟨?_, list_budget C (lenFrom_sound C (rs' := (table[144]!).rest) (by decide))
    (by decide)⟩
  rw [show (table[144]!).pc = 0x80002a6c by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  exact ⟨n, ha, newp, l08, l50, L, X, hlive, hnew⟩

/-- The old block back to the allocator (`0x80002a38` leaf 1; return `0x80002a6c`): `free(bp,
0x90 n, log2 alignment 4)`. -/
theorem DTF.leaf_80002a38_1 :
    LeafGoal DTF.plan DTF.plan.cuts[143]! ((DTF.plan.leaves 0x80002a38)[1]!) := by
  refine leaf_call_xo (table[143]!) (table[144]!) (siteAt 144) ((leavesAt 0x80002a38)[1]!)
    freeEntry (by decide) DTF.cut_80002a38 (by decide) (by decide) (noObl (by decide))
    (by decide) rfl rfl (by decide) ?_
  intro σ m m' hA hc C CF
  obtain ⟨n, hn⟩ := memcpy_ret hA
  have hpre := C.F.common.2.1
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have hn32 := app_n hpre h4 hn.1
  have hk := ctx_lowKeep C (by decide)
  obtain ⟨ha, bp, newp, l58m, l60m, l08m, l50m, L, X, hlive, hnew, hold⟩ := hn
  have hlive' := ctx_live C hlive
  have l58 := lk hk (by decide) l58m
  have l50 := lk hk (by decide) l50m
  have hn' : AuthNew σ m' n := ⟨app_lk hk ha, bp, newp, l58, lk hk (by decide) l60m,
    lk hk (by decide) l08m, l50, L, X, hlive', hnew, hold⟩
  have hne := hc _ (show SBool.ne (.init 0 96 8) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, src_init C (by decide) (show (Loc.slot 96).sym (table[143]!).shape.S =
    .init 0 96 8 by decide), wordAt_of_load l60m, Sym.eval_lit, bne_iff_ne, ne_eq] at hne
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact absurd rfl hne
    · exact h0
  have r11 : m'.reg 11 = bp := by
    rw [show (11 : Fin 32) = Fin.ofNat 32 11 from rfl, ctx_regv C (by decide)
      (s := .init 0 88 8) (by decide), src_init C (by decide) (by decide), wordAt_of_load l58m]
  have r12 : m'.reg 12 = w (n * 0x90) := by
    rw [show (12 : Fin 32) = Fin.ofNat 32 12 from rfl, ctx_regv C (by decide)
      (s := .bin .add (.bin .sll (.init 0 96 8) (.lit 7)) (.bin .sll (.init 0 96 8) (.lit 4)))
      (by decide)]
    simp only [Sym.eval_bin, Sym.eval_lit, src_init C (by decide) (show (Loc.slot 96).sym
      (table[143]!).shape.S = .init 0 96 8 by decide), wordAt_of_load l60m, BinOp.eval]
    rw [show BitVec.ofNat 64 7 = w 7 from rfl, show BitVec.ofNat 64 4 = w 4 from rfl,
      w_sll (c := 128) (by decide) (by decide) (by omega),
      w_sll (c := 16) (by decide) (by decide) (by omega), w_add_mul]
    congr 1; omega
  have r13 : m'.reg 13 = w 4 := by
    rw [show (13 : Fin 32) = Fin.ofNat 32 13 from rfl, ctx_regv C (by decide) (s := .lit 4)
      (by decide)]
    rfl
  have hlen : (m'.reg 12).toNat = n * 0x90 := by
    rw [r12]; simp only [w, BitVec.toNat_ofNat]; omega
  have hsp : m'.reg 2 = σ.fr + w 0 := CF.shape.1 (2, .fr 0) (by decide) _ rfl
  have hmem : (m'.reg 11, (m'.reg 12).toNat) ∈ X := by rw [r11, hlen]; exact hold hn0
  have hidx : IdxOk (siteAt 144).kind σ (L, [], ⟨[], []⟩) m' := by
    rw [show (siteAt 144).kind = .free by decide]
    exact ⟨free_pre_dtf CF.common hsp CF.aligned hlive' hmem (by omega) (by omega)
      (by rw [r13]; decide), X, hlive', hmem⟩
  have hsx : SiteX (table[144]!).pc σ (L, [], ⟨[], []⟩) m' := by
    rw [show (table[144]!).pc = 0x80002a6c by decide]
    simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true]
    exact ⟨n, hn', by rw [r11]; exact l58, r12, newp, X, l50, hlive', hnew⟩
  refine ⟨_, hidx, hsx, fun m'' hpost => ?_⟩
  have hfld : FieldsOk σ m' (siteFields (table[144]!).pc) := fun f hf => by
    rw [show siteFields (table[144]!).pc = [] by decide] at hf; cases hf
  have hsite : SiteA (siteAt 144) (table[144]!).pc σ (L, [], ⟨[], []⟩) m' :=
    ⟨CF.ra, CF.common, CF.shape, CF.arms, CF.rest, hidx, hfld, CF.chk, hsx⟩
  exact call_list_budget C (by decide) hsite hpost (by decide) (o := 0x68) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide)

/-- At `0x80002a6c` (from `0x80002a38` without an old block, or after `free`): the new block. -/
theorem newF_2a6c {σ : Sig} {m : Machine} (hA : (mkCut (table[144]!)).A σ m) :
    ∃ n, AuthNewF σ m n := by
  have hne : (table[144]!).pc ≠ entry := by decide
  simp only [mkCut, if_neg hne, ACut] at hA
  rcases hA with ⟨-, hpa⟩ | ⟨s, hs, mc, x, hsite, hpost⟩
  · have hx := hpa.2.2.2.2.2.1
    rw [show (table[144]!).pc = 0x80002a6c by decide] at hx
    simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true] at hx
    exact hx
  have hs' : s = siteAt 144 := by
    show s = ((table[144]!).site).getD default; rw [hs]; rfl
  subst hs'
  have hsx := hsite.2.2.2.2.2.2.2.2
  rw [show (table[144]!).pc = 0x80002a6c by decide] at hsx
  simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true] at hsx
  obtain ⟨n, hn, -, r12, newp, X', l50, hlive', hnew⟩ := hsx
  have hkd : (siteAt 144).kind = .free := by decide
  have hSF : (siteAt 144).kind.SiteFine (siteAt 144) = true := by decide
  have hk := ret_keep hSF hsite hpost fun _ _ => by rw [hkd]; rfl
  have hq : freePost σ.A x.1 mc m := by have := hpost.1; rw [hkd] at this; exact this
  have hix := hsite.2.2.2.2.2.1
  rw [hkd] at hix
  obtain ⟨-, X, hlive, hb⟩ := hix
  have hpre := hsite.2.1.2.1
  have h4 : σ.t = 4 := arm4 hsite.2.2.2.1 (by decide)
  have hn32 := app_n hpre h4 hn.1
  have hXX : X.Perm X' := (List.perm_append_left_iff _).mp (hlive.2.1.symm.trans hlive'.2.1)
  have hb' := hXX.subset hb
  obtain ⟨-, -, hheap, -⟩ := hq
  have hlen : (mc.reg 12).toNat = n * 0x90 := by
    rw [r12]; simp only [w, BitVec.toNat_ofNat]; omega
  have hneq : (newp, newCap n * 0x90) ≠ (mc.reg 11, (mc.reg 12).toNat) := by
    rw [hlen]; intro h
    have := congrArg Prod.snd h
    simp only at this
    unfold newCap at this; omega
  obtain ⟨ha, -, -, -, -, l08, -⟩ := hn
  exact ⟨n, app_lk hk ha, newp, lk hk (by decide) l08, lk hk (by decide) l50, _, _,
    live_drop hlive' hb' hheap, List.mem_erase_of_ne hneq |>.mpr hnew⟩

/-- The new block becomes the buffer (`0x80002a6c` → `0x8000241c`): `cap := newCap n`,
`a0 := newp`. -/
theorem DTF.leaf_80002a6c_0 :
    LeafGoal DTF.plan DTF.plan.cuts[144]! ((DTF.plan.leaves 0x80002a6c)[0]!) := by
  refine leaf_at_xo (table[144]!) (table[122]!) ((leavesAt 0x80002a6c)[0]!) (by decide)
    DTF.cut_80002a6c (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  obtain ⟨n, ha, newp, l08, l50, L, X, hlive, hnew⟩ := newF_2a6c hA
  have hpre := C.F.common.2.1
  have hn32 := app_n hpre (arm4 C.F.arms (by decide)) ha
  have hcl := newCap_lt hn32
  have hk := ctx_keptOn C (os := appSlots) (by decide)
  have l60 := ctx_word C (o := 0x60) (s := .init 0 8 8) (by decide) (by decide)
  rw [src_init C (by decide) (by decide), wordAt_of_load l08] at l60
  have r10 : m'.reg 10 = newp := by
    rw [show (10 : Fin 32) = Fin.ofNat 32 10 from rfl, ctx_regv C (by decide)
      (s := .init 0 80 8) (by decide), src_init C (by decide) (by decide), wordAt_of_load l50]
  have hc' : (w (newCap n)).toNat = newCap n := by simp only [w, BitVec.toNat_ofNat]; omega
  refine ⟨?_, list_budget C (lenFrom_sound C (rs' := (table[122]!).rest) (by decide))
    (by decide)⟩
  rw [show (table[122]!).pc = 0x8000241c by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  refine ⟨n, app_on hk ha, w (newCap n), l60, by rw [hc']; unfold newCap; omega,
    by rw [hc']; unfold newCap; omega, L, X, ctx_live C hlive, fun _ => by rw [r10, hc']; exact hnew⟩

/-! ## The store's slot (`0x8000241c`, `0x80002420`) -/

theorem DTF.leaf_8000241c_0 :
    LeafGoal DTF.plan DTF.plan.cuts[122]! ((DTF.plan.leaves 0x8000241c)[0]!) := by
  refine leaf_at_xo (table[122]!) (table[123]!) ((leavesAt 0x8000241c)[0]!) (by decide)
    DTF.cut_8000241c (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have hx := src_extra (by decide) (by decide) hA (show (table[122]!).pc = 0x8000241c by decide)
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true] at hx
  obtain ⟨n, ha, cap, l60, hb⟩ := hx
  have hk := ctx_keptOn C (os := appSlots ++ [0x60]) (by decide)
  have l58 := ctx_word C (o := 0x58) (s := .var 10) (by decide) (by decide)
  rw [var_reg (by decide)] at l58
  refine ⟨?_, list_budget C (lenFrom_sound C (rs' := (table[123]!).rest) (by decide))
    (by decide)⟩
  rw [show (table[123]!).pc = 0x80002420 by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  exact ⟨n, app_on (fun o ho => hk o (List.mem_append_left _ ho)) ha, _, cap, l58,
    by rw [hk _ (by decide)]; exact l60, bufIs_mono (fun _ _ hl => ctx_live C hl) hb⟩

/-- The slot `bp + 0x90 n` of the buffer with room for `n + 1` tuples: DTF's, present. -/
theorem buf_slot {σ : Sig} {m : Machine} {n : Nat} {bp cap : Word} (hb : BufIs σ m n 1 bp cap)
    {a : Word} (ha : a = bp + w (n * 0x90)) :
    RamRange a 0x90 ∧ Present m a 0x90 ∧ ∀ x, InRange a 0x90 x → σ.A.Priv σ.g.L x := by
  obtain ⟨hn, -, L, X, hlive, hmem⟩ := hb
  have hm := hmem (by omega)
  obtain ⟨-, hram, hpres⟩ := blk_facts hlive hm
  have hpriv := (hlive.2.2 _ hm).2.2
  simp only at hram hpres hpriv
  unfold RamRange Layout.ramHi at hram
  have hle : n * 0x90 + 0x90 ≤ cap.toNat * 0x90 := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hn
  have ha' : a.toNat = bp.toNat + n * 0x90 := by
    rw [ha]; exact toNat_add_ofNat (by omega)
  refine ⟨⟨by unfold Layout.ramLo at *; omega, by unfold Layout.ramHi; omega⟩, fun j hj => ?_,
    fun x hx => hpriv x ?_⟩
  · have := hpres (n * 0x90 + j) (by omega)
    rwa [show bp + BitVec.ofNat 64 (n * 0x90 + j) = a + BitVec.ofNat 64 j by
      rw [ha]; simp only [w]; rw [F1.add_add_ofNat]] at this
  · simp only [InRange] at hx ⊢; omega

theorem DTF.leaf_80002420_0 :
    LeafGoal DTF.plan DTF.plan.cuts[123]! ((DTF.plan.leaves 0x80002420)[0]!) := by
  refine leaf_at_xo (table[123]!) (table[124]!) ((leavesAt 0x80002420)[0]!) (by decide)
    DTF.cut_80002420 (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have hx := src_extra (by decide) (by decide) hA (show (table[123]!).pc = 0x80002420 by decide)
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true] at hx
  obtain ⟨n, ha, bp, cap, l58, l60, hb⟩ := hx
  have hpre := C.F.common.2.1
  have hn32 := app_n hpre (arm4 C.F.arms (by decide)) ha
  have hk := ctx_lowKeep C (by decide)
  have ha' := app_lk hk ha
  have hb' := bufIs_mono (fun _ _ hl => ctx_live C hl) hb
  obtain ⟨-, -, l40, l38⟩ := ha
  have r10 : m'.reg 10 = bp + w (n * 0x90) := by
    rw [show (10 : Fin 32) = Fin.ofNat 32 10 from rfl, ctx_regv C (by decide)
      (s := .bin .add (.init 0 88 8) (.bin .add (.init 0 56 8) (.init 0 64 8))) (by decide)]
    simp only [Sym.eval_bin, src_init C (by decide) (show (Loc.slot 88).sym (table[123]!).shape.S
      = .init 0 88 8 by decide), src_init C (by decide) (show (Loc.slot 56).sym
      (table[123]!).shape.S = .init 0 56 8 by decide), src_init C (by decide) (show (Loc.slot 64).sym
      (table[123]!).shape.S = .init 0 64 8 by decide), wordAt_of_load l58, wordAt_of_load l38,
      wordAt_of_load l40, BinOp.eval, w_add_mul]
    congr 2; omega
  refine ⟨?_, list_budget C (lenFrom_sound C (rs' := (table[124]!).rest) (by decide))
    (by decide)⟩
  rw [show (table[124]!).pc = 0x80002434 by decide]
  simp only [Extra, if_true]
  exact ⟨buf_slot hb' r10, n, ha', ⟨bp, cap, lk hk (by decide) l58, lk hk (by decide) l60, hb'⟩, bp,
    lk hk (by decide) l58, r10⟩

end ZesuExec.Fn.DTF
