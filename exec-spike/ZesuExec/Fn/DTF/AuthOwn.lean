import ZesuExec.Fn.DTF.AuthGrow

/-!
# DTF: the authorization list's `toOwnedSlice` (programme plan S7 step 4)

After the last tuple: the remap call returns null (`0x80002f54`), `0x800022e4` with `n` tuples
(`AuthDone`; also from an empty list, `0x80001ccc` leaf 2): no tuples → the empty slice
(`0x80002ecc`), else `alloc(0x90 n, log2 alignment 4)` (return `0x80002c68`), `memcpy` of the
tuples into it (`0x80002ecc`, return `0x80002ee0`), `free(bp, 0x90 cap, 4)` of the buffer (return
`0x80002f14`). Tools: `done_on`, `own_keep`, `keep_budget`, `call_keep_budget`, `size_eval`.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

set_option maxRecDepth 20000

/-- The frame words `AuthDone` names. -/
def doneSlots : List Nat := [0x78, 0x30, 0x58, 0x60]

theorem done_on {σ : Sig} {m m' : Machine}
    (h : ∀ o ∈ doneSlots, m'.load (σ.fr + w o) 8 = m.load (σ.fr + w o) 8)
    (hL : ∀ L X, Live σ m L X → Live σ m' L X) {n : Nat} (hd : AuthDone σ m n) :
    AuthDone σ m' n := by
  obtain ⟨c, hh, p, hl, hs, hn, l78, l30, hp, hb⟩ := hd
  exact ⟨c, hh, p, hl, hs, hn, by rw [h _ (by decide)]; exact l78,
    by rw [h _ (by decide)]; exact l30, hp,
    authBuf_mono (h _ (by decide)) (h _ (by decide)) hL hb⟩

theorem done_n {σ : Sig} {m : Machine} {n : Nat} (hpre : Pre σ.A σ.g σ.m) (h4 : σ.t = 4)
    (hd : AuthDone σ m n) : n < 2 ^ 32 := by
  obtain ⟨c, hh, p, hl, -, hn, -⟩ := hd
  have := authList_le hpre h4 hl
  have := len_lt32 hpre
  omega

/-- The buffer holds the `n` tuples: `n ≤ cap`, `cap ≤ 2 n + 1`, for the `cap` at `S-0x310`. -/
theorem done_cap {σ : Sig} {m : Machine} {n : Nat} (hd : AuthDone σ m n) {cap : Word}
    (l60 : m.load (σ.fr + w 0x60) 8 = some cap) : n ≤ cap.toNat ∧ cap.toNat ≤ 2 * n + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, bp', cap', -, l60', hn1, hn2, -⟩ := hd
  rw [l60, Option.some.injEq] at l60'
  subst l60'
  exact ⟨by omega, by omega⟩

theorem own_keep {σ : Sig} {m m' : Machine} (h : LowKeep σ m m')
    (hL : ∀ L X, Live σ m L X → Live σ m' L X) (h25 : m'.reg 25 = m.reg 25) {n : Nat}
    (ho : AuthOwn σ m n) : AuthOwn σ m' n := by
  obtain ⟨hd, r25, hor⟩ := ho
  refine ⟨done_lk h hL hd, h25.trans r25, ?_⟩
  rcases hor with h0 | ⟨bp, cap, newp, l58, l60, lc8, L, X, hlive, h1, h2⟩
  · exact .inl h0
  · exact .inr ⟨bp, cap, newp, lk h (by decide) l58, lk h (by decide) l60, lk h (by decide) lc8,
      L, X, hL L X hlive, h1, h2⟩

/-- A target without an inner budget whose constant drops by the steps (`budgetKeep`). -/
theorem keep_budget {d d' : CutData} {l : Leaf} {σ : Sig} {m m' : Machine}
    (hlen : restLen d' σ m' ≤ restLen d σ m)
    (h : budgetKeep d.pc d'.pc (l.S.steps - d.shape.S.steps) = true) :
    CurOk σ m' (budgetAt d'.pc).2 ∧
      budgetOf d' σ m' + (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m := by
  unfold budgetKeep at h
  split at h
  · next hinner =>
    simp only [decide_eq_true_eq] at h
    refine ⟨by rw [hinner]; trivial, ?_⟩
    unfold budgetOf; rw [hinner]; simp only [innerOf]; omega
  · cases h

/-- A call leaf's budget when the return site has no inner budget. -/
theorem call_keep_budget {d d' : CutData} {l : Leaf} {s : Site} {σ : Sig} {x : Idx}
    {m m' m'' : Machine} (C : Ctx d l σ m m') (hSF : s.kind.SiteFine s = true)
    (hsite : SiteA s d'.pc σ x m') (hpost : (calleeOf s.kind).Post σ x m' m'')
    (hR : retLen d l s d' = true) (h' : (budgetAt d'.pc).2 = .none)
    (hK : s.kind.bound + (budgetAt d'.pc).1 + (l.S.steps - d.shape.S.steps) ≤ (budgetAt d.pc).1) :
    s.kind.bound + budgetOf d' σ m'' + (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m := by
  have hlen := ret_len C hSF hsite hpost hR
  unfold budgetOf
  rw [h']
  simp only [innerOf]
  omega

/-- `144 n` as the code computes it from the count word `w n`. -/
theorem size_eval {env : Env} {n : Nat} (h : (Sym.init 0 0x78 8).eval env = w n)
    (hn : n < 2 ^ 32) :
    (Sym.bin .add (.bin .sll (.init 0 0x78 8) (.lit 7)) (.bin .sll (.init 0 0x78 8) (.lit 4))).eval
      env = w (n * 0x90) := by
  simp only [Sym.eval_bin, Sym.eval_lit, h, BinOp.eval]
  rw [show BitVec.ofNat 64 7 = w 7 from rfl, show BitVec.ofNat 64 4 = w 4 from rfl,
    w_sll (c := 128) (by decide) (by decide) (by omega),
    w_sll (c := 16) (by decide) (by decide) (by omega), w_add_mul]
  congr 1; omega

/-! ## After `toOwnedSlice`'s remap (`0x80002f54`): null -/

theorem remap_ret2 {σ : Sig} {m : Machine} (hA : (mkCut (table[156]!)).A σ m) :
    (∃ n, AuthDone σ m n) ∧ m.reg 10 = 0 := by
  obtain ⟨mc, x, hsite, hpost⟩ := ret_parts (i := 156) (by decide) (by decide) hA
  have hsx := hsite.2.2.2.2.2.2.2.2
  rw [show (table[156]!).pc = 0x80002f54 by decide] at hsx
  simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true] at hsx
  obtain ⟨n, hd⟩ := hsx
  have hkd : (siteAt 156).kind = .remap := by decide
  have hSF : (siteAt 156).kind.SiteFine (siteAt 156) = true := by decide
  have hk := ret_keep hSF hsite hpost fun _ _ => by rw [hkd]; rfl
  have hq : F0.Post mc m := by have := hpost.1; rw [hkd] at this; exact this
  have hSF' : Kind.SiteFine .remap (siteAt 156) = true := by rw [← hkd]; exact hSF
  exact ⟨⟨n, done_lk hk (fun L X hl => remap_live hSF' hsite hq hpost.2 hl) hd⟩, hq.2.1⟩

theorem DTF.leaf_80002f54_0 :
    LeafGoal DTF.plan DTF.plan.cuts[156]! ((DTF.plan.leaves 0x80002f54)[0]!) := by
  refine leaf_at_xo (table[156]!) (table[116]!) ((leavesAt 0x80002f54)[0]!) (by decide)
    DTF.cut_80002f54 (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  obtain ⟨⟨n, hd⟩, -⟩ := remap_ret2 hA
  refine ⟨?_, ?_⟩
  · rw [show (table[116]!).pc = 0x800022e4 by decide]
    simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
    exact ⟨n, done_on (ctx_keptOn C (by decide)) (fun _ _ hl => ctx_live C hl) hd⟩
  · exact keep_budget (lenFrom_sound C (rs' := (table[116]!).rest) (by decide)) (by decide)

/-- F0 returned null: the non-null branch is vacuous. -/
theorem DTF.leaf_80002f54_1 :
    LeafGoal DTF.plan DTF.plan.cuts[156]! ((DTF.plan.leaves 0x80002f54)[1]!) := by
  refine leaf_at_xo (table[156]!) (table[116]!) ((leavesAt 0x80002f54)[1]!) (by decide)
    DTF.cut_80002f54 (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide)
    fun σ m m' hA hc C => ?_
  have h10 := (remap_ret2 hA).2
  have hne := hc _ (show SBool.ne (.var 10) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, var_reg (show 10 < 32 by decide), Sym.eval_lit] at hne
  rw [show (Fin.ofNat 32 10 : Fin 32) = 10 from rfl, h10] at hne
  exact absurd hne (by decide)

/-! ## `toOwnedSlice` (`0x800022e4`): the owned copy of the `n` tuples -/

theorem done_22e4 {σ : Sig} {m : Machine} (hA : (mkCut (table[116]!)).A σ m) :
    ∃ n, AuthDone σ m n := by
  have hx := src_extra (by decide) (by decide) hA (show (table[116]!).pc = 0x800022e4 by decide)
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true] at hx
  exact hx

/-- No tuples (`0x800022e4` leaf 0): the empty slice. -/
theorem DTF.leaf_800022e4_0 :
    LeafGoal DTF.plan DTF.plan.cuts[116]! ((DTF.plan.leaves 0x800022e4)[0]!) := by
  refine leaf_at_xo (table[116]!) (table[153]!) ((leavesAt 0x800022e4)[0]!) (by decide)
    DTF.cut_800022e4 (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  obtain ⟨n, hd⟩ := done_22e4 hA
  have hpre := C.F.common.2.1
  have hn32 := done_n hpre (arm4 C.F.arms (by decide)) hd
  have hd' := done_on (ctx_keptOn C (by decide)) (fun _ _ hl => ctx_live C hl) hd
  obtain ⟨-, -, -, -, -, -, l78, -⟩ := hd
  have e78 : (Sym.init 0 0x78 8).eval (envOf (table[116]!).shape σ m) = w n := by
    rw [src_init C (by decide) (by decide), wordAt_of_load l78]
  have hz := hc _ (show SBool.eq (.bin .add (.bin .sll (.init 0 120 8) (.lit 7))
    (.bin .sll (.init 0 120 8) (.lit 4))) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, size_eval e78 hn32, Sym.eval_lit, beq_iff_eq] at hz
  have hn0 : n = 0 := by
    have := congrArg BitVec.toNat hz
    rw [show (w (n * 0x90)).toNat = n * 0x90 by simp only [w, BitVec.toNat_ofNat]; omega] at this
    simp at this; omega
  subst hn0
  have r25 : m'.reg 25 = w (0 * 0x90) := by
    rw [show (25 : Fin 32) = Fin.ofNat 32 25 from rfl, ctx_regv C (by decide)
      (s := .bin .add (.bin .sll (.init 0 120 8) (.lit 7)) (.bin .sll (.init 0 120 8) (.lit 4)))
      (by decide)]
    exact size_eval e78 hn32
  refine ⟨?_, keep_budget (lenFrom_sound C (rs' := (table[153]!).rest) (by decide)) (by decide)⟩
  rw [show (table[153]!).pc = 0x80002ecc by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  exact ⟨0, hd', r25, .inl rfl⟩

/-- The owned copy's block (`0x800022e4` leaf 1; return `0x80002c68`): `alloc(0x90 n, 4)`. -/
theorem DTF.leaf_800022e4_1 :
    LeafGoal DTF.plan DTF.plan.cuts[116]! ((DTF.plan.leaves 0x800022e4)[1]!) := by
  refine leaf_call_xo (table[116]!) (table[147]!) (siteAt 147) ((leavesAt 0x800022e4)[1]!)
    allocEntry (by decide) DTF.cut_800022e4 (by decide) (by decide) (noObl (by decide))
    (by decide) rfl rfl (by decide) ?_
  intro σ m m' hA hc C CF
  obtain ⟨n, hd⟩ := done_22e4 hA
  have hpre := C.F.common.2.1
  have hn32 := done_n hpre (arm4 C.F.arms (by decide)) hd
  have hd' := done_on (ctx_keptOn C (by decide)) (fun _ _ hl => ctx_live C hl) hd
  obtain ⟨-, -, -, -, -, -, l78, -⟩ := hd
  have e78 : (Sym.init 0 0x78 8).eval (envOf (table[116]!).shape σ m) = w n := by
    rw [src_init C (by decide) (by decide), wordAt_of_load l78]
  have hz := hc _ (show SBool.ne (.bin .add (.bin .sll (.init 0 120 8) (.lit 7))
    (.bin .sll (.init 0 120 8) (.lit 4))) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, size_eval e78 hn32, Sym.eval_lit, bne_iff_ne, ne_eq] at hz
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact absurd rfl hz
    · exact h0
  have r11 : m'.reg 11 = w (n * 0x90) := by
    rw [show (11 : Fin 32) = Fin.ofNat 32 11 from rfl, ctx_regv C (by decide)
      (s := .bin .add (.bin .sll (.init 0 120 8) (.lit 7)) (.bin .sll (.init 0 120 8) (.lit 4)))
      (by decide)]
    exact size_eval e78 hn32
  have r25 : m'.reg 25 = w (n * 0x90) := by
    rw [show (25 : Fin 32) = Fin.ofNat 32 25 from rfl, ctx_regv C (by decide)
      (s := .bin .add (.bin .sll (.init 0 120 8) (.lit 7)) (.bin .sll (.init 0 120 8) (.lit 4)))
      (by decide)]
    exact size_eval e78 hn32
  have r12 : m'.reg 12 = w 4 := by
    rw [show (12 : Fin 32) = Fin.ofNat 32 12 from rfl, ctx_regv C (by decide) (s := .lit 4)
      (by decide)]
    rfl
  have hsz : (m'.reg 11).toNat = n * 0x90 := by
    rw [r11]; simp only [w, BitVec.toNat_ofNat]; omega
  have hsp : m'.reg 2 = σ.fr + w 0 := CF.shape.1 (2, .fr 0) (by decide) _ rfl
  have hb : AuthBuf σ m' n 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hb⟩ := hd'; exact hb
  obtain ⟨bp, cap, l58, l60, -, -, L, X, hlive, hmem⟩ := hb
  have hidx : IdxOk (siteAt 147).kind σ (L, [], ⟨[], []⟩) m' := by
    rw [show (siteAt 147).kind = .alloc by decide]
    exact ⟨alloc_pre_dtf CF.common hsp CF.aligned hlive (by omega) (by omega)
      (by rw [r12]; decide), X, hlive⟩
  have hsx : SiteX (table[147]!).pc σ (L, [], ⟨[], []⟩) m' := by
    rw [show (table[147]!).pc = 0x80002c68 by decide]
    simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true]
    exact ⟨n, hd', r11, r25, bp, cap, X, l58, l60, hlive, hmem⟩
  refine ⟨_, hidx, hsx, fun m'' hpost => ?_⟩
  have hfld := CF.fields
  have hsite : SiteA (siteAt 147) (table[147]!).pc σ (L, [], ⟨[], []⟩) m' :=
    ⟨CF.ra, CF.common, CF.shape, CF.arms, CF.rest, hidx, hfld, CF.chk, hsx⟩
  exact call_keep_budget C (by decide) hsite hpost (by decide) rfl (by decide)

/-- After the owned copy's allocation (`0x80002c68`, non-null): the new block of `0x90 n`
bytes beside the buffer. -/
theorem alloc_ret2 {σ : Sig} {m : Machine} (hA : (mkCut (table[147]!)).A σ m)
    (hnz : m.reg 10 ≠ 0) :
    ∃ n, AuthDone σ m n ∧ m.reg 25 = w (n * 0x90) ∧ ∃ bp cap : Word,
      m.load (σ.fr + w 0x58) 8 = some bp ∧ m.load (σ.fr + w 0x60) 8 = some cap ∧
      ∃ L X, Live σ m L X ∧ (m.reg 10, n * 0x90) ∈ X ∧
        (0 < cap.toNat → (bp, cap.toNat * 0x90) ∈ X) := by
  obtain ⟨mc, x, hsite, hpost⟩ := ret_parts (i := 147) (by decide) (by decide) hA
  have hsx := hsite.2.2.2.2.2.2.2.2
  rw [show (table[147]!).pc = 0x80002c68 by decide] at hsx
  simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true] at hsx
  obtain ⟨n, hd, r11, r25, bp, cap, X, l58, l60, hlive, hmem⟩ := hsx
  have hkd : (siteAt 147).kind = .alloc := by decide
  have hSF : (siteAt 147).kind.SiteFine (siteAt 147) = true := by decide
  have hk := ret_keep hSF hsite hpost fun _ _ => by rw [hkd]; rfl
  have hret := (ret_common hSF hsite hpost).1
  have hq : allocPost σ.A x.1 mc m := by have := hpost.1; rw [hkd] at this; exact this
  have hpre := hsite.2.1.2.1
  have h4 : σ.t = 4 := arm4 hsite.2.2.2.1 (by decide)
  have hn := done_n hpre h4 hd
  have hsz : (mc.reg 11).toNat = n * 0x90 := by
    rw [r11]; simp only [w, BitVec.toNat_ofNat]; omega
  obtain ⟨-, -, hnew⟩ := hq
  rcases hnew with ⟨h0, -⟩ | ⟨-, hheap, hram, -, hin, -⟩
  · exact absurd h0 hnz
  rw [hsz] at hheap hram hin
  have hpos : 0 < n * 0x90 := by
    have := (hsite.2.2.2.2.2.1)
    rw [hkd] at this
    have h0 := this.1.2.1
    rw [hsz] at h0; exact h0
  have hliveM : Live σ m (x.1 ++ [(m.reg 10, n * 0x90)]) (X ++ [(m.reg 10, n * 0x90)]) := by
    refine ⟨hheap, by rw [← List.append_assoc]; exact hlive.2.1.append_right _,
      fun b hb => ?_⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact hlive.2.2 b hb
    · simp only [List.mem_singleton] at hb
      subst hb
      exact ⟨hpos, hram, fun a ha => priv_sub hpre hlive (hin a ha)⟩
  obtain ⟨c, hh, p, hl, hs, hnp, l78, l30, hp, bp', cap', l58', l60', hn1, hn2, -⟩ := hd
  rw [l58, Option.some.injEq] at l58'
  rw [l60, Option.some.injEq] at l60'
  subst l58' l60'
  have hmem' : 0 < cap.toNat → (bp, cap.toNat * 0x90) ∈ X ++ [(m.reg 10, n * 0x90)] :=
    fun h => List.mem_append_left _ (hmem h)
  refine ⟨n, ⟨c, hh, p, hl, hs, hnp, lk hk (by decide) l78, lk hk (by decide) l30, hp, bp, cap,
    lk hk (by decide) l58, lk hk (by decide) l60, hn1, hn2, _, _, hliveM, hmem'⟩, ?_, bp, cap,
    lk hk (by decide) l58, lk hk (by decide) l60, _, _, hliveM,
    List.mem_append_right _ (List.mem_singleton_self _), hmem'⟩
  rw [hret.2 25 (by decide)]; exact r25

/-- The owned copy's block (`0x80002c68` leaf 0): its address at `S-0x2a8`. -/
theorem DTF.leaf_80002c68_0 :
    LeafGoal DTF.plan DTF.plan.cuts[147]! ((DTF.plan.leaves 0x80002c68)[0]!) := by
  refine leaf_at_xo (table[147]!) (table[153]!) ((leavesAt 0x80002c68)[0]!) (by decide)
    DTF.cut_80002c68 (by decide) (by decide) (noObl (by decide)) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have hne := hc _ (show SBool.ne (.var 10) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, var_reg (show 10 < 32 by decide), Sym.eval_lit, bne_iff_ne,
    ne_eq] at hne
  rw [show (Fin.ofNat 32 10 : Fin 32) = 10 from rfl] at hne
  obtain ⟨n, hd, r25, bp, cap, l58, l60, L, X, hlive, hnew, hold⟩ := alloc_ret2 hA hne
  have hk := ctx_keptOn C (os := doneSlots) (by decide)
  have lc8 := ctx_word C (o := 0xc8) (s := .var 10) (by decide) (by decide)
  rw [var_reg (by decide)] at lc8
  have e : ∀ o ∈ doneSlots, ∀ {v : Word}, m.load (σ.fr + w o) 8 = some v →
      m'.load (σ.fr + w o) 8 = some v := fun o ho _ hv => by rw [hk o ho]; exact hv
  refine ⟨?_, keep_budget (lenFrom_sound C (rs' := (table[153]!).rest) (by decide)) (by decide)⟩
  rw [show (table[153]!).pc = 0x80002ecc by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  refine ⟨n, done_on hk (fun _ _ hl => ctx_live C hl) hd, ?_, .inr ⟨bp, cap, m.reg 10,
    e _ (by decide) l58, e _ (by decide) l60, lc8, L, X, ctx_live C hlive, hnew, hold⟩⟩
  rw [show (25 : Fin 32) = Fin.ofNat 32 25 from rfl, ctx_reg C (i' := 25) (by decide) (by decide)
    (by decide)]
  exact r25

/-- The owned copy (`0x80002ecc`; return `0x80002ee0`): `memcpy(newp, bp, 0x90 n)`. -/
theorem DTF.leaf_80002ecc_0 :
    LeafGoal DTF.plan DTF.plan.cuts[153]! ((DTF.plan.leaves 0x80002ecc)[0]!) := by
  refine leaf_call_xo (table[153]!) (table[154]!) (siteAt 154) ((leavesAt 0x80002ecc)[0]!)
    Layout.memcpyEntry (by decide) DTF.cut_80002ecc (by decide) (by decide) (noObl (by decide))
    (by decide) rfl rfl (by decide) ?_
  intro σ m m' hA hc C CF
  have hx := src_extra (by decide) (by decide) hA (show (table[153]!).pc = 0x80002ecc by decide)
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true] at hx
  obtain ⟨n, ho⟩ := hx
  have hpre := C.F.common.2.1
  have hn32 := done_n hpre (arm4 C.F.arms (by decide)) ho.1
  have e25 : m'.reg 25 = m.reg 25 := by
    rw [show (25 : Fin 32) = Fin.ofNat 32 25 from rfl, ctx_reg C (i' := 25) (by decide)
      (by decide) (by decide)]
  have ho' := own_keep (ctx_lowKeep C (by decide)) (fun _ _ hl => ctx_live C hl) e25 ho
  have r12 : m'.reg 12 = w (n * 0x90) := by
    rw [show (12 : Fin 32) = Fin.ofNat 32 12 from rfl, ctx_regv C (by decide) (s := .var 25)
      (by decide), var_reg (by decide)]
    exact ho.2.1
  have hlen : (m'.reg 12).toNat = n * 0x90 := by
    rw [r12]; simp only [w, BitVec.toNat_ofNat]; omega
  have hscr : Present m' TX.scratch 8 := CF.common.2.2.2.2.2.2.1
  obtain ⟨hd', -, hor⟩ := ho'
  have hidx : IdxOk (siteAt 154).kind σ ([], [], ⟨[], []⟩) m' ∧
      (n = 0 ∨ m'.load (σ.fr + w 0xc8) 8 = some (m'.reg 10)) := by
    rw [show (siteAt 154).kind = .memcpy by decide]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · have hz : (m'.reg 12).toNat = 0 := by rw [hlen, h0]
      exact ⟨⟨memcpy_pre_gen CF.aligned hscr fun h => absurd hz (by omega), .inl hz⟩, .inl h0⟩
    rcases hor with h0 | ⟨bp, cap, newp, l58, l60, lc8, L, X, hlive, hnew, hold⟩
    · omega
    have r10 : m'.reg 10 = newp := by
      rw [show (10 : Fin 32) = Fin.ofNat 32 10 from rfl, ctx_regv C (by decide)
        (s := .init 0 200 8) (by decide), src_init C (by decide) (by decide), ← wordAt_of_load lc8,
        ← ctx_slot C (o := 200) (by decide) (by decide)]
    have r11 : m'.reg 11 = bp := by
      rw [show (11 : Fin 32) = Fin.ofNat 32 11 from rfl, ctx_regv C (by decide)
        (s := .init 0 88 8) (by decide), src_init C (by decide) (by decide), ← wordAt_of_load l58,
        ← ctx_slot C (o := 88) (by decide) (by decide)]
    have hcap := done_cap hd' l60
    obtain ⟨-, hramN, hpresN⟩ := blk_facts hlive hnew
    obtain ⟨-, hramO, hpresO⟩ := blk_facts hlive (hold (by omega))
    simp only at hramN hpresN hramO hpresO
    unfold RamRange at hramN hramO
    have hsub : n * 0x90 ≤ cap.toNat * 0x90 := Nat.mul_le_mul_right _ hcap.1
    refine ⟨⟨memcpy_pre_gen CF.aligned hscr fun _ => ?_, .inr ⟨L, X, hlive, _, hnew,
      fun j hj => ?_⟩⟩, .inr (by rw [r10]; exact lc8)⟩
    · rw [hlen, r10, r11]
      refine ⟨?_, fun j hj => hpresO j (by omega), ⟨hramN.1, hramN.2⟩, hpresN⟩
      simp only [Machine.readable, Machine.inRange, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq]
      exact .inr ⟨hramO.1, by omega⟩
    · rw [hlen] at hj
      rw [r10]
      unfold Layout.ramHi at hramN
      simp only [InRange]
      rw [toNat_add_ofNat (by omega)]
      omega
  have hsx : SiteX (table[154]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[154]!).pc = 0x80002ee0 by decide]
    simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true]
    exact ⟨n, own_keep (ctx_lowKeep C (by decide)) (fun _ _ hl => ctx_live C hl) e25 ho, r12,
      hidx.2⟩
  refine ⟨_, hidx.1, hsx, fun m'' hpost => ?_⟩
  have hfld := CF.fields
  have hsite : SiteA (siteAt 154) (table[154]!).pc σ ([], [], ⟨[], []⟩) m' :=
    ⟨CF.ra, CF.common, CF.shape, CF.arms, CF.rest, hidx.1, hfld, CF.chk, hsx⟩
  exact call_keep_budget C (by decide) hsite hpost (by decide) rfl (by decide)

/-- After the owned copy (`0x80002ee0`): the copy is in the new block, the buffer is DTF's. -/
theorem memcpy_ret2 {σ : Sig} {m : Machine} (hA : (mkCut (table[154]!)).A σ m) :
    ∃ n, AuthOwn σ m n := by
  obtain ⟨mc, x, hsite, hpost⟩ := ret_parts (i := 154) (by decide) (by decide) hA
  have hsx := hsite.2.2.2.2.2.2.2.2
  rw [show (table[154]!).pc = 0x80002ee0 by decide] at hsx
  simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true] at hsx
  obtain ⟨n, ho, r12, hc8⟩ := hsx
  have hkd : (siteAt 154).kind = .memcpy := by decide
  have hSF : (siteAt 154).kind.SiteFine (siteAt 154) = true := by decide
  have hk := ret_keep hSF hsite hpost fun _ _ => by rw [hkd]; rfl
  have hret := (ret_common hSF hsite hpost).1
  have hq : MemcpyPost mc m := by have := hpost.1; rw [hkd] at this; exact this
  have hpre := hsite.2.1.2.1
  have h4 : σ.t = 4 := arm4 hsite.2.2.2.1 (by decide)
  have hn32 := done_n hpre h4 ho.1
  have hlen : (mc.reg 12).toNat = n * 0x90 := by
    rw [r12]; simp only [w, BitVec.toNat_ofNat]; omega
  refine ⟨n, ?_⟩
  obtain ⟨hd, r25, hor⟩ := ho
  rcases hor with h0 | ⟨bp, cap, newp, l58, l60, lc8, L, X, hlive, hnew, hold⟩
  · subst h0
    have hz : (mc.reg 12).toNat = 0 := hlen
    refine ⟨done_lk hk (fun L X hl => memcpy_live hsite.2.1 hq hpost.2 hl fun a ha => ?_) hd,
      by rw [hret.2 25 (by decide)]; exact r25, .inl rfl⟩
    simp only [InRange, hz] at ha; omega
  have hdst : ∀ a, InRange (mc.reg 10) (mc.reg 12).toNat a → InLive L a := by
    intro a ha
    rcases hc8 with h0 | hc8
    · subst h0; simp only [InRange, hlen] at ha; omega
    rw [lc8, Option.some.injEq] at hc8
    rw [← hc8, hlen] at ha
    exact ⟨_, hlive.2.1.symm.subset (List.mem_append_right _ hnew), ha⟩
  have hlive' := memcpy_live hsite.2.1 hq hpost.2 hlive hdst
  obtain ⟨c, hh, p, hl, hs, hnp, l78, l30, hp, bp', cap', l58', l60', hn1, hn2, -⟩ := hd
  rw [l58, Option.some.injEq] at l58'
  rw [l60, Option.some.injEq] at l60'
  subst l58' l60'
  exact ⟨⟨c, hh, p, hl, hs, hnp, lk hk (by decide) l78, lk hk (by decide) l30, hp, bp, cap,
    lk hk (by decide) l58, lk hk (by decide) l60, hn1, hn2, L, X, hlive', hold⟩,
    by rw [hret.2 25 (by decide)]; exact r25, .inr ⟨bp, cap, newp, lk hk (by decide) l58,
      lk hk (by decide) l60, lk hk (by decide) lc8, L, X, hlive', hnew, hold⟩⟩

/-- The buffer back to the allocator (`0x80002ee0` leaf 1; return `0x80002f14`):
`free(bp, 0x90 cap, log2 alignment 4)`. -/
theorem DTF.leaf_80002ee0_1 :
    LeafGoal DTF.plan DTF.plan.cuts[154]! ((DTF.plan.leaves 0x80002ee0)[1]!) := by
  refine leaf_call_xo (table[154]!) (table[155]!) (siteAt 155) ((leavesAt 0x80002ee0)[1]!)
    freeEntry (by decide) DTF.cut_80002ee0 (by decide) (by decide) (noObl (by decide))
    (by decide) rfl rfl (by decide) ?_
  intro σ m m' hA hc C CF
  obtain ⟨n, ho⟩ := memcpy_ret2 hA
  have hpre := C.F.common.2.1
  have hn32 := done_n hpre (arm4 C.F.arms (by decide)) ho.1
  obtain ⟨hd, -, hor⟩ := ho
  have hdc := hd
  obtain ⟨c, hh, p, -, -, -, -, l30, hp, -⟩ := hdc
  have hne := hc _ (show SBool.ne (.init 0 48 8) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, src_init C (by decide) (show (Loc.slot 48).sym (table[154]!).shape.S =
    .init 0 48 8 by decide), wordAt_of_load l30, Sym.eval_lit, bne_iff_ne, ne_eq] at hne
  have hp0 : p ≠ 0 := fun h0 => hne (by rw [h0])
  have hn0 := hp hp0
  rcases hor with h0 | ⟨bp, cap, newp, l58, l60, -, L, X, hlive, -, hold⟩
  · omega
  have hcap := done_cap hd l60
  have hc0 : 0 < cap.toNat := by omega
  have ecap : cap = w cap.toNat := by simp [w]
  have r11 : m'.reg 11 = bp := by
    rw [show (11 : Fin 32) = Fin.ofNat 32 11 from rfl, ctx_regv C (by decide)
      (s := .init 0 88 8) (by decide), src_init C (by decide) (by decide), wordAt_of_load l58]
  have r12 : m'.reg 12 = w (cap.toNat * 0x90) := by
    rw [show (12 : Fin 32) = Fin.ofNat 32 12 from rfl, ctx_regv C (by decide)
      (s := .bin .add (.bin .sll (.init 0 96 8) (.lit 7)) (.bin .sll (.init 0 96 8) (.lit 4)))
      (by decide)]
    simp only [Sym.eval_bin, Sym.eval_lit, src_init C (by decide) (show (Loc.slot 96).sym
      (table[154]!).shape.S = .init 0 96 8 by decide), wordAt_of_load l60, BinOp.eval]
    rw [ecap, show BitVec.ofNat 64 7 = w 7 from rfl, show BitVec.ofNat 64 4 = w 4 from rfl,
      w_sll (c := 128) (by decide) (by decide) (by omega),
      w_sll (c := 16) (by decide) (by decide) (by omega), w_add_mul]
    congr 1
    simp only [w, BitVec.toNat_ofNat]
    omega
  have r13 : m'.reg 13 = w 4 := by
    rw [show (13 : Fin 32) = Fin.ofNat 32 13 from rfl, ctx_regv C (by decide) (s := .lit 4)
      (by decide)]
    rfl
  have hlen : (m'.reg 12).toNat = cap.toNat * 0x90 := by
    rw [r12]; simp only [w, BitVec.toNat_ofNat]; omega
  have hlive' := ctx_live C hlive
  have hsp : m'.reg 2 = σ.fr + w 0 := CF.shape.1 (2, .fr 0) (by decide) _ rfl
  have hmem : (m'.reg 11, (m'.reg 12).toNat) ∈ X := by rw [r11, hlen]; exact hold hc0
  have hidx : IdxOk (siteAt 155).kind σ (L, [], ⟨[], []⟩) m' := by
    rw [show (siteAt 155).kind = .free by decide]
    exact ⟨free_pre_dtf CF.common hsp CF.aligned hlive' hmem (by omega) (by omega)
      (by rw [r13]; decide), X, hlive', hmem⟩
  have hsx : SiteX (table[155]!).pc σ (L, [], ⟨[], []⟩) m' := siteX_of_no (by decide) _ _ _
  refine ⟨_, hidx, hsx, fun m'' hpost => ?_⟩
  have hfld := CF.fields
  have hsite : SiteA (siteAt 155) (table[155]!).pc σ (L, [], ⟨[], []⟩) m' :=
    ⟨CF.ra, CF.common, CF.shape, CF.arms, CF.rest, hidx, hfld, CF.chk, hsx⟩
  exact call_keep_budget C (by decide) hsite hpost (by decide) rfl (by decide)

/-- An empty authorization list (`0x80001ccc`, leaf 2): no tuples, the buffer `{16, 0}`. -/
theorem DTF.leaf_80001ccc_2 :
    LeafGoal DTF.plan DTF.plan.cuts[93]! ((DTF.plan.leaves 0x80001ccc)[2]!) := by
  refine leaf_at_x (table[93]!) (table[116]!) ((leavesAt 0x80001ccc)[2]!) (by decide)
    DTF.cut_80001ccc (by decide) (by decide) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have hpre := C.F.common.2.1
  have herr := hc _ (show SBool.eq (.init 0 688 2) (.lit 0) ∈ _ by decide)
  have hlist := hc _ (show SBool.ne (.bin .and (.init 0 672 1) (.lit 1)) (.lit 0) ∈ _ by decide)
  have hp0 := hc _ (show SBool.eq (.init 0 664 8) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, bne_iff_ne, ne_eq] at herr hlist hp0
  obtain ⟨c, h, p, hs, hd, hpw, -⟩ := list_out_at (d := table[93]!) (ko := 656) (k := 9)
    (by decide) (by decide) (by decide) hA (by simpa using herr) (by simpa [isL] using hlist)
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have hf := fit_of_arms hpre (arms := [4]) (.inr (by simp [h4])) (by decide) hs
  obtain ⟨-, -, h64⟩ := TX.fits_bounds hf hd
  have hp : p = 0 := by
    rw [hpw] at hp0
    have := congrArg BitVec.toNat hp0
    simp only [w, BitVec.toNat_ofNat, Sym.eval_lit] at this
    omega
  subst hp
  have l30 : m'.load (σ.fr + w 0x30) 8 = some (w 0) := by
    rw [ctx_word C (o := 0x30) (s := .init 0 664 8) (by decide) (by decide)]
    exact congrArg some hpw
  have l78 : m'.load (σ.fr + w 0x78) 8 = some (w 0) :=
    ctx_word C (o := 0x78) (s := .lit 0) (by decide) (by decide)
  obtain ⟨L, X, hlive⟩ := (ctx_common C).2.2.2.2.2.2.2.2
  have hbuf : AuthBuf σ m' 0 0 :=
    ⟨16, 0, ctx_word C (o := 0x58) (s := .lit 16) (by decide) (by decide),
      ctx_word C (o := 0x60) (s := .lit 0) (by decide) (by decide), by decide, by decide, L, X,
      hlive, fun h0 => absurd h0 (by decide)⟩
  refine ⟨?_, keep_budget (lenFrom_sound C (rs' := (table[116]!).rest) (by decide)) (by decide)⟩
  rw [show (table[116]!).pc = 0x800022e4 by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  exact ⟨0, c, h, 0, ⟨hs, hd⟩, rfl, Nat.le_refl _, l78, l30, fun h0 => absurd rfl h0, hbuf⟩

end ZesuExec.Fn.DTF
