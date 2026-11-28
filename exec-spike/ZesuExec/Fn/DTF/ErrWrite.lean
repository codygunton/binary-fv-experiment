import ZesuExec.Fn.DTF.AuthOwn

/-!
# DTF: the error write (`0x80001400`, programme plan S7 step 4)

`Extra 0x80001400` states `a0 = 3`: every path into it sets it (`0x800013fc`: OOM or an invalid
item, `a0 := 3`; the four TX return sites: TX's error code is not 0, and TX writes only 0 or 3,
`tx_err`). The leaf from `0x80001400` writes the low two bytes of `a0` as the result's error code
(`Done`'s error disjunct).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

set_option maxRecDepth 20000

/-- The low two bytes of an 8-byte load. -/
theorem load2_of_load8 {m : Machine} {a v : Word} (h : m.load a 8 = some v) :
    m.load a 2 = some (ofBytesLE (byteList (byteOf v) 0 2)) := by
  have hb := load_bytes h (Nat.le_refl _)
  unfold Machine.load at h ⊢
  split at h
  · next hr =>
    have hr2 : readable a.toNat 2 = true := by
      simp only [readable, inRange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr ⊢
      omega
    rw [if_pos hr2, readBytes_of (k := 0) fun t ht => by
      rw [ofNat_toNat_add]; simpa using hb t (by omega)]
    rfl
  · cases h

/-- TX's error code at a return site with the result at `fr + ka`: 0 or 3. -/
theorem tx_err {σ : Sig} {m : Machine} {i ka : Nat} (hne : (table[i]!).pc ≠ entry)
    (hpl : (table[i]!).plain = false) (hA : (mkCut (table[i]!)).A σ m)
    (hkd : (siteAt i).kind = .tx) (h10 : (10, Val.fr ka) ∈ (siteAt i).shape.regs) :
    m.load (σ.fr + w (ka + 16)) 2 = some 0 ∨ m.load (σ.fr + w (ka + 16)) 2 = some 3 := by
  obtain ⟨mc, x, hsite, hpost⟩ := ret_parts hne hpl hA
  have r10 : mc.reg 10 = σ.fr + w ka := hsite.2.2.1.1 _ h10 _ rfl
  have hq : TX.Post σ.A x.2.2 mc m := by have := hpost.1; rw [hkd] at this; exact this
  have ha : σ.fr + w ka + 16 = σ.fr + w (ka + 16) := by simp only [w]; bv_omega
  obtain ⟨-, -, -, cls, -, -, -, -, himg⟩ := hq
  rw [r10] at himg
  cases cls with
  | ok es =>
    obtain ⟨-, -, -, -, h16, -⟩ := himg
    rw [ha] at h16
    exact .inl h16
  | invalidInput =>
    obtain ⟨-, -, h16, -⟩ := himg
    rw [ha] at h16
    exact .inr ((load2_of_load8 h16).trans (by decide))
  | allocationFailure =>
    obtain ⟨-, -, h16, -⟩ := himg
    rw [ha] at h16
    exact .inr ((load2_of_load8 h16).trans (by decide))

/-- A TX return leaf to the error write `0x80001400`: TX's code is not 0, so it is 3. -/
theorem tx_err_a0 {i ka : Nat} {l : Leaf} {σ : Sig} {m m' : Machine}
    (hne : (table[i]!).pc ≠ entry) (hpl : (table[i]!).plain = false)
    (hkd : (siteAt i).kind = .tx) (h10 : (10, Val.fr ka) ∈ (siteAt i).shape.regs)
    (hk : ka + 18 ≤ frameBytes)
    (hread : readConst (table[i]!).shape.S 0 (ka + 16) 2 = .init 0 (ka + 16) 2)
    (h10l : l.S.reg 10 = .init 0 (ka + 16) 2)
    (hcond : SBool.ne (.init 0 (ka + 16) 2) (.lit 0) ∈ l.conds)
    (hA : (mkCut (table[i]!)).A σ m)
    (hc : ∀ b ∈ l.conds, b.eval (envOf (table[i]!).shape σ m) = true)
    (C : Ctx (table[i]!) l σ m m') : m'.reg 10 = w 3 := by
  have hR0 : (table[i]!).shape.S.regions[0]? = some frameR := by rw [C.hS]; rfl
  have e := load_cst C.wf C.hm hR0 (off := ka + 16) (n := 2) (by rw [envOf_size0]; omega)
  rw [env_base0, hread] at e
  have r := ctx_regv C (show 10 < 32 by decide) h10l
  have hne0 := hc _ hcond
  simp only [SBool.eval, Sym.eval_lit, bne_iff_ne, ne_eq] at hne0
  rw [show (10 : Fin 32) = Fin.ofNat 32 10 from rfl, r]
  rcases tx_err hne hpl hA hkd h10 with h | h
  · rw [show σ.fr + w (ka + 16) = σ.fr + BitVec.ofNat 64 (ka + 16) from rfl, e,
      Option.some.injEq] at h
    exact absurd h hne0
  · rw [show σ.fr + w (ka + 16) = σ.fr + BitVec.ofNat 64 (ka + 16) from rfl, e,
      Option.some.injEq] at h
    exact h

theorem DTF.leaf_80001a70_0 :
    LeafGoal DTF.plan DTF.plan.cuts[84]! ((DTF.plan.leaves 0x80001a70)[0]!) := by
  refine leaf_at_x (table[84]!) (table[64]!) ((leavesAt 0x80001a70)[0]!) (by decide)
    DTF.cut_80001a70 (by decide) (by decide) (by decide) rfl (by decide) fun σ m m' hA hc C => ?_
  refine ⟨?_, keep_budget (lenFrom_sound C (rs' := (table[64]!).rest) (by decide)) (by decide)⟩
  rw [show (table[64]!).pc = 0x80001400 by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  exact tx_err_a0 (ka := 400) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hA hc C

theorem DTF.leaf_80001c98_0 :
    LeafGoal DTF.plan DTF.plan.cuts[92]! ((DTF.plan.leaves 0x80001c98)[0]!) := by
  refine leaf_at_x (table[92]!) (table[64]!) ((leavesAt 0x80001c98)[0]!) (by decide)
    DTF.cut_80001c98 (by decide) (by decide) (by decide) rfl (by decide) fun σ m m' hA hc C => ?_
  refine ⟨?_, keep_budget (lenFrom_sound C (rs' := (table[64]!).rest) (by decide)) (by decide)⟩
  rw [show (table[64]!).pc = 0x80001400 by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  exact tx_err_a0 (ka := 544) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hA hc C

theorem DTF.leaf_80001d54_0 :
    LeafGoal DTF.plan DTF.plan.cuts[95]! ((DTF.plan.leaves 0x80001d54)[0]!) := by
  refine leaf_at_x (table[95]!) (table[64]!) ((leavesAt 0x80001d54)[0]!) (by decide)
    DTF.cut_80001d54 (by decide) (by decide) (by decide) rfl (by decide) fun σ m m' hA hc C => ?_
  refine ⟨?_, keep_budget (lenFrom_sound C (rs' := (table[64]!).rest) (by decide)) (by decide)⟩
  rw [show (table[64]!).pc = 0x80001400 by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  exact tx_err_a0 (ka := 448) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hA hc C

theorem DTF.leaf_80001ec4_0 :
    LeafGoal DTF.plan DTF.plan.cuts[101]! ((DTF.plan.leaves 0x80001ec4)[0]!) := by
  refine leaf_at_x (table[101]!) (table[64]!) ((leavesAt 0x80001ec4)[0]!) (by decide)
    DTF.cut_80001ec4 (by decide) (by decide) (by decide) rfl (by decide) fun σ m m' hA hc C => ?_
  refine ⟨?_, keep_budget (lenFrom_sound C (rs' := (table[64]!).rest) (by decide)) (by decide)⟩
  rw [show (table[64]!).pc = 0x80001400 by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  exact tx_err_a0 (ka := 496) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hA hc C

/-- OOM or an invalid item (`0x800013fc`): error code 3 in `a0`. -/
theorem DTF.leaf_800013fc_0 :
    LeafGoal DTF.plan DTF.plan.cuts[63]! ((DTF.plan.leaves 0x800013fc)[0]!) := by
  refine leaf_at_x (table[63]!) (table[64]!) ((leavesAt 0x800013fc)[0]!) (by decide)
    DTF.cut_800013fc (by decide) (by decide) (by decide) rfl (by decide) fun σ m m' hA hc C => ?_
  refine ⟨?_, keep_budget (lenFrom_sound C (rs' := (table[64]!).rest) (by decide)) (by decide)⟩
  rw [show (table[64]!).pc = 0x80001400 by decide]
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
  rw [show (10 : Fin 32) = Fin.ofNat 32 10 from rfl, ctx_regv C (by decide) (s := .lit 3)
    (by decide)]
  rfl

/-- The error write (`0x80001400`): code 3 into the result. -/
theorem DTF.leaf_80001400_0 :
    LeafGoal DTF.plan DTF.plan.cuts[64]! ((DTF.plan.leaves 0x80001400)[0]!) := by
  refine leaf_at_x (table[64]!) (table[58]!) ((leavesAt 0x80001400)[0]!) (by decide)
    DTF.cut_80001400 (by decide) (by decide) (by decide) rfl (by decide) fun σ m m' hA hc C => ?_
  refine ⟨?_, keep_budget (lenFrom_sound C (rs' := (table[58]!).rest) (by decide)) (by decide)⟩
  have hx := src_extra (by decide) (by decide) hA (show (table[64]!).pc = 0x80001400 by decide)
  simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true] at hx
  rw [show (table[58]!).pc = 0x800011f8 by decide]
  simp only [Extra, Nat.reduceEqDiff, if_false, if_true]
  left
  have hR : ((leavesAt 0x80001400)[0]!).S.regions[1]? = some resR := by rw [C.hS']; rfl
  have := load_cst C.wf' C.hm' hR (off := errOff) (n := 2)
    (by simp [envOf, entryEnv, Env.size, regionsOf, resultBytes, errOff])
  rw [env_base1, show readConst ((leavesAt 0x80001400)[0]!).S 1 errOff 2 = .bytes (.var 10) 0 2
    by decide] at this
  rw [this]
  congr 1
  have hv : (envOf (table[64]!).shape σ m).vars 10 = w 3 := by
    have := var_reg (sh := (table[64]!).shape) (σ := σ) (m := m) (show 10 < 32 by decide)
    rw [← hx]; exact this
  simp only [Sym.eval, byteList, hv]
  decide

end ZesuExec.Fn.DTF
