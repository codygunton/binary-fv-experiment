import ZesuExec.Fn.DTF.AuthLib

/-!
# DTF: into the `txAuthList` loop and the tuple's `decodeItem` (programme plan S7 step 4)

`0x80001ccc` leaf 3: item 9 is a nonempty list; the list cursor, count `0` and the empty buffer
`{16, 0}` (`AuthLoop` at `0x800024d0`). `0x800024d0` leaf 0: `decodeItem` on the list cursor.
`0x800024ec` leaf 0: the tuple is a list; `decodeItem` on its first field (`AuthTup`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- A list item's `decodeItem` at a return site of `rest` after `k` items, outcome at `ko`. -/
theorem list_out_at {d : CutData} {σ : Sig} {m : Machine} {ko k : Nat} (hpc : d.pc ≠ entry)
    (hsrc : SrcOk d = true) (hadv : advOf d = some (ko, k)) (hA : (mkCut d).A σ m)
    (herr : (Sym.init 0 (ko + 32) 2).eval (envOf d.shape σ m) = 0)
    (hlist : (isL ko).eval (envOf d.shape σ m) ≠ 0) :
    ∃ c h p, skip k σ.payload = some c ∧ F2.decode (σ.payload.drop c) = .success true h p ∧
      (Sym.init 0 (ko + 8) 8).eval (envOf d.shape σ m) = w p ∧
      (p ≠ 0 → TX.wordAt m (σ.fr + w ko) = σ.inp + w (c + h)) := by
  obtain ⟨c, l, h, p, hs, hd⟩ := f2_ok hpc hsrc hadv hA herr
  have hL := f2_list hpc hsrc hadv hA c hs l h p hd
  obtain ⟨hpw, hptr⟩ := f2_words hpc hsrc hadv hA c hs l h p hd
  have hlt : l = true := by
    cases l
    · exact absurd hL (by simpa using hlist)
    · rfl
  subst hlt
  refine ⟨c, h, p, hs, hd, hpw, fun hp0 => ?_⟩
  rw [hptr, if_neg fun h128 => hp0 ((decode_hdr hd).2 h128)]

/-- Into the loop (`0x80001ccc`, leaf 3): a nonempty list, no tuples, the buffer `{16, 0}`. -/
theorem DTF.leaf_80001ccc_3 :
    LeafGoal DTF.plan DTF.plan.cuts[93]! ((DTF.plan.leaves 0x80001ccc)[3]!) := by
  refine leaf_at_x (table[93]!) (table[125]!) ((leavesAt 0x80001ccc)[3]!) (by decide)
    DTF.cut_80001ccc (by decide) (by decide) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have hpre := C.F.common.2.1
  have h4 : σ.t = 4 := arm4 C.F.arms (by decide)
  have herr := hc _ (show SBool.eq (.init 0 688 2) (.lit 0) ∈ _ by decide)
  have hlist := hc _ (show SBool.ne (.bin .and (.init 0 672 1) (.lit 1)) (.lit 0) ∈ _ by decide)
  have hp0 := hc _ (show SBool.ne (.init 0 664 8) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq, bne_iff_ne, ne_eq] at herr hlist hp0
  obtain ⟨c, h, p, hs, hd, hpw, hptr⟩ := list_out_at (d := table[93]!) (ko := 656) (k := 9)
    (by decide) (by decide) (by decide) hA (by simpa using herr) (by simpa [isL] using hlist)
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have hf := fit_of_arms hpre (arms := [4]) (.inr (by simp [h4])) (by decide) hs
  obtain ⟨-, hle, h64⟩ := TX.fits_bounds hf hd
  rw [List.length_drop, payload_len hpre] at hle
  have hpn : p ≠ 0 := fun h0 => hp0 (by rw [hpw, h0]; rfl)
  have hptr' := hptr hpn
  -- the frame words at the target
  have l70 : m'.load (σ.fr + w 0x70) 8 = some (σ.inp + w (c + h + 0)) := by
    rw [ctx_word C (o := 0x70) (s := .bin .add (.ptr 3 0) (.var 146)) (by decide) (by decide)]
    simp only [Sym.eval_bin, BinOp.eval, var_slot (show 64 ≤ 146 by decide),
      show 8 * (146 - 64) = 656 from rfl, hptr']
    simp only [Sym.eval, env_base3, Nat.add_zero]
    simp only [BitVec.ofInt_ofNat, BitVec.add_zero]
    rw [BitVec.add_comm σ.inp (w (c + h)), BitVec.add_sub_cancel, BitVec.add_comm]
  have l68 : m'.load (σ.fr + w 0x68) 8 = some (w (p - 0)) := by
    rw [ctx_word C (o := 0x68) (s := .init 0 664 8) (by decide) (by decide), Nat.sub_zero]
    exact congrArg some hpw
  have l30 : m'.load (σ.fr + w 0x30) 8 = some (w p) := by
    rw [ctx_word C (o := 0x30) (s := .init 0 664 8) (by decide) (by decide)]
    exact congrArg some hpw
  have l78 : m'.load (σ.fr + w 0x78) 8 = some (w 0) :=
    ctx_word C (o := 0x78) (s := .lit 0) (by decide) (by decide)
  obtain ⟨L, X, hlive⟩ := (ctx_common C).2.2.2.2.2.2.2.2
  have hbuf : AuthBuf σ m' 0 0 :=
    ⟨16, 0, ctx_word C (o := 0x58) (s := .lit 16) (by decide) (by decide),
      ctx_word C (o := 0x60) (s := .lit 0) (by decide) (by decide), by decide, by decide, L, X,
      hlive, fun h0 => absurd h0 (by decide)⟩
  have hloop : AuthLoop σ m' :=
    ⟨c, h, p, 0, 0, ⟨⟨hs, hd⟩, rfl, Nat.le_refl _, l70, l68, l30⟩, l78, hbuf⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [show (table[125]!).pc = 0x800024d0 by decide]; simpa [Extra, AuthExtra] using hloop
  · rw [show budgetAt (table[125]!).pc = (7043, .list (.slot 0x68)) from rfl]; trivial
  -- the budget: `rest` moved past the list, the bytes left are the list payload
  obtain ⟨c10, hs10, hw10⟩ := restFrom_sound C (rs' := (table[125]!).rest) (by decide)
    ⟨.slot 0x158, true, 10⟩ (by decide)
  obtain ⟨c9, hs9, hw9⟩ := C.rest ⟨.reg 22, true, 9⟩ (by decide)
  rw [hs, Option.some.injEq] at hs9
  subst hs9
  rw [skip_snoc hs hd, Option.some.injEq] at hs10
  subst hs10
  have hic : TX.itemConsumed h p = h + p := Nat.mod_eq_of_lt h64
  unfold budgetOf restLen
  rw [show budgetAt (table[125]!).pc = (7043, .list (.slot 0x68)) from rfl,
    show budgetAt (table[93]!).pc = (7065, .none) from rfl,
    show (table[125]!).rest.find? (·.len) = some ⟨.slot 0x158, true, 10⟩ by decide,
    show (table[93]!).rest.find? (·.len) = some ⟨.reg 22, true, 9⟩ by decide,
    show ((leavesAt 0x80001ccc)[3]!).S.steps - (table[93]!).shape.S.steps = 22 by decide]
  simp only [innerOf, Loc.word, TX.wordAt, l68] at hw10 hw9 ⊢
  rw [hw10, hw9, hic]
  simp only [if_true, w, BitVec.toNat_sub, BitVec.toNat_ofNat, Option.getD_some]
  omega

end ZesuExec.Fn.DTF
