import ZesuExec.Fn.TX.Entry

/-!
# TX: error exits at the keys list and the keys (programme plan S6 step 6)

`0x8000015c`: the item after the address is not a list; `0x800001a0`: a key is not a 32-byte
string. Either makes `entryWalk` of the entry `none`.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- Frame bytes `[S - j, S - j + n)` survive a `decodeItem` call with its outcome at `S - k`. -/
theorem f2_bytes_keep {σ : Sig} {mc m : Machine} (hc : Common σ mc) {k : Nat}
    (hout : mc.reg 10 = σ.sl k) (hk : 40 ≤ k) (hk' : k ≤ 576)
    (hso : SameOutside (fun a => InRange (mc.reg 10) 40 a ∨ InRange (mc.reg 2 - 16) 16 a) mc m)
    {j : Nat} {bs : List Byte} (hj' : j ≤ 576) (hn : bs.length ≤ j)
    (hd : k + bs.length ≤ j ∨ j + 40 ≤ k) (h : BytesAt mc (σ.sl j) bs) : BytesAt m (σ.sl j) bs := by
  have hpre := hc.2.1
  intro i hi
  rw [← h i hi]
  refine hso _ fun hr => ?_
  rw [hout, show mc.reg 2 - 16 = σ.sl 592 from sp_sub hc 16] at hr
  have h1 := sl_toNat hpre (k := k) (by unfold stackBytes; omega)
  have h2 := sl_toNat hpre (k := 592) (by decide)
  have h3 := sl_toNat hpre (k := j) (by unfold stackBytes; omega)
  have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
  simp only [InRange] at hr
  rw [toNat_add_ofNat (by omega), h3, h1, h2] at hr
  omega

/-- An entry whose address is fine but whose next item is not a list rejects. -/
theorem entry_none_keys {e : List Byte} {ah : Nat} (hd : F2.decode e = .success false ah 20)
    (h : ∀ kh kl, F2.decode (itemRest e ah 20) ≠ .success true kh kl) :
    (entryWalk e).2 = none := by
  unfold entryWalk
  rw [hd]
  simp only [if_true]
  all_goals (split <;> first | rfl | (rename_i kh kl hk; exact absurd hk (h kh kl)))

/-- The window after the address in input coordinates. -/
theorem aft_eq (σ : Sig) (o : Obs) (k : Kobs) (hk : k.eh + k.el ≤ o.p - o.i)
    (ha : k.ah + 20 ≤ k.el) (h64 : k.el < 2 ^ 64) :
    aft σ o k = (σ.input.drop (o.h + o.i + k.eh + (k.ah + 20))).take (k.el - (k.ah + 20)) := by
  have hc : itemConsumed k.ah 20 = k.ah + 20 := Nat.mod_eq_of_lt (by omega)
  simp only [aft, itemRest, ent_eq σ o k hk, List.drop_take, List.drop_drop, hc]

/-! ## `0x8000015c`: after the keys list's `decodeItem` -/

theorem ret15c {σ : Sig} {m : Machine} (h : ARet f2C (unit Site158) σ m) :
    Common σ m ∧ ∃ o k L, EntryState σ m o k L ∧ AddrOk σ m o k ∧ ∃ before : List Byte,
      BytesAt m (σ.sl 0x140) (F2.result40 (aftPtr σ o k) (aft σ o k) before) := by
  have hcm := A15c_common h
  obtain ⟨mc, _, ⟨o, k, L, ⟨hs, hd, hle, r26⟩, ⟨had, hal, hab⟩, ha⟩, hpost, hp⟩ := h
  have hc := hs.1
  have hout : mc.reg 10 = σ.sl 0x140 := ha.arg 0 (by simp)
  have hin : mc.reg 11 = aftPtr σ o k := ha.arg 1 (by simp)
  have hlen : mc.reg 12 = w (k.el - (k.ah + 20)) := ha.arg 2 (by simp)
  have hok := hs.2.1
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hpl := hok.2.1
  have hl : (mc.reg 12).toNat = k.el - (k.ah + 20) := by
    rw [hlen]; simp only [w, BitVec.toNat_ofNat]; omega
  obtain ⟨before, -, hb⟩ := f2_result hc hout (by decide) (by decide)
    (off := o.h + o.i + k.eh + (k.ah + 20))
    (by rw [hin]; simp only [aftPtr, entPtr, curPtr, w]; bv_omega) (by omega) hpost
  rw [hl, ← aft_eq σ o k hle hal (by omega),
    show σ.inp + w (o.h + o.i + k.eh + (k.ah + 20)) = aftPtr σ o k by
      simp only [aftPtr, entPtr, curPtr, w]; bv_omega] at hb
  refine ⟨hcm, o, k, L, ⟨outer_keep hs hcm hout (by decide) (by decide) hpost hp,
    hd, hle, (hpost.1.2 26 (by decide)).trans r26⟩,
    ⟨had, hal, f2_bytes_keep hc hout (by decide) (by decide) hpost.2.1 (by decide)
      (by simp [itemPayload]; omega) (by simp [itemPayload]; omega) hab⟩, before, hb⟩

/-- A keys-list rejection at `0x8000015c`. -/
theorem keys_list_err {σ : Sig} {m : Machine} {o : Obs} {k : Kobs} {L : List (Word × Nat)}
    (hcm : Common σ m) (hs : EntryState σ m o k L) (had : AddrOk σ m o k)
    (hrej : ∀ kh kl, F2.decode (aft σ o k) ≠ .success true kh kl) : ErrOk σ m :=
  outer_err hcm hs.1.2.1 hs.1.2.2.2.2.2 (entries_none_entry (win_ne hs.1.2.1 hs.1.2.2.1.2.2.1 hcm.2.1)
    hs.2.1 (entry_none_keys had.1 hrej))

theorem TX.leaf_8000015c_0 :
    LeafGoal TX.plan TX.plan.cuts[5]! ((TX.plan.leaves 0x8000015c)[0]!) := by
  show LeafGoal TX.plan cut15c (run15c_leaves[0]!)
  have hcs : (run15c_leaves[0]!).conds = [SBool.ne (Sym.init 0 288 2) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envB_ok (A15c_common hA)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_) (fun σ m hA hc => ?_)
  · have : (run15c_leaves[0]!).S.steps - SBody.steps = 21 := by decide
    show _ ≤ 32 * outerLeft m + 37; simp only [cut15c, mkCut] at *; omega
  obtain ⟨hcm, o, k, L, hs, had, before, hb⟩ := ret15c hA
  have h1 : SBool.eval (envB σ m) (SBool.ne (Sym.init 0 288 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  simp only [SBool.eval] at h1
  rw [show (288 : Nat) = frameBytes - 0x140 + 32 from rfl,
    slot_val (BaseEnv.ofB σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h1
  have hdec := dec_err (by simpa [Sym.eval] using h1)
  exact keys_list_err hcm hs had fun kh kl h => by rw [hdec] at h; cases h

theorem TX.leaf_8000015c_1 :
    LeafGoal TX.plan TX.plan.cuts[5]! ((TX.plan.leaves 0x8000015c)[1]!) := by
  show LeafGoal TX.plan cut15c (run15c_leaves[1]!)
  have hcs : (run15c_leaves[1]!).conds = [SBool.eq (Sym.init 0 288 2) (Sym.lit 0),
      SBool.eq (Sym.bin BinOp.and (Sym.init 0 272 1) (Sym.lit 1)) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envB_ok (A15c_common hA)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_) (fun σ m hA hc => ?_)
  · have : (run15c_leaves[1]!).S.steps - SBody.steps = 24 := by decide
    show _ ≤ 32 * outerLeft m + 37; simp only [cut15c, mkCut] at *; omega
  obtain ⟨hcm, o, k, L, hs, had, before, hb⟩ := ret15c hA
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 288 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envB σ m)
      (SBool.eq (Sym.bin BinOp.and (Sym.init 0 272 1) (Sym.lit 1)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  simp only [SBool.eval] at h1 h2
  replace h2 : ((Sym.init 0 272 1).eval (envB σ m) &&& 1#64 == 0#64) = true := h2
  rw [show (288 : Nat) = frameBytes - 0x140 + 32 from rfl,
    slot_val (BaseEnv.ofB σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h1
  rw [show (272 : Nat) = frameBytes - 0x140 + 16 from rfl,
    slot_val (BaseEnv.ofB σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h2
  obtain ⟨b, hh, q, hd, hl⟩ := dec_ok (by simpa [Sym.eval] using h1)
  rw [hl] at h2
  cases b
  · exact keys_list_err hcm hs had fun kh kl h => by rw [hd] at h; cases h
  · simp at h2

/-! ## `0x800001a0`: after a key's `decodeItem` -/

/-- The keys window in input coordinates. -/
theorem kwin_eq (σ : Sig) (o : Obs) (k : Kobs) (hk : k.eh + k.el ≤ o.p - o.i)
    (ha : k.ah + 20 + k.kh + k.kl ≤ k.el) (h64 : k.el < 2 ^ 64) :
    kwin σ o k = (σ.input.drop (o.h + o.i + k.eh + (k.ah + 20) + k.kh + k.j)).take (k.kl - k.j) := by
  simp only [kwin, kpl, itemPayload, aft_eq σ o k hk (by omega) h64, List.drop_take,
    List.take_take, List.drop_drop]
  rw [Nat.min_eq_left (by omega)]

/-- The walk of a nonempty keys window whose first item is not a 32-byte string rejects. -/
theorem keys_none_head {kw : List Byte} (hne : kw ≠ [])
    (h : ∀ kh', F2.decode kw ≠ .success false kh' keySize) :
    (keysWalk kw.length kw).2 = none := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.length_cons, keysWalk]
  all_goals (split <;> first | rfl | skip)
  all_goals (rename_i kh' p hd; split <;> first | rfl | (rename_i hp; subst hp; exact absurd hd (h kh')))

/-- An entry whose keys walk rejects. -/
theorem entry_none_kw {e : List Byte} {ah kh kl : Nat} (hd : F2.decode e = .success false ah 20)
    (hk : F2.decode (itemRest e ah 20) = .success true kh kl)
    (hn : (keysWalk (itemPayload (itemRest e ah 20) kh kl).length
      (itemPayload (itemRest e ah 20) kh kl)).2 = none) :
    (entryWalk e).2 = none := by
  unfold entryWalk
  simp only [hd, hk, if_true, hn, Option.map_none]

/-- The facts of `0x800001a0` the error exits use. -/
theorem ret1a0 {σ : Sig} {m : Machine} (h : ARet f2C (unit Site19c) σ m) :
    Common σ m ∧ ∃ o k L, OuterOk σ m o ∧ o.i < o.p ∧ Live σ m L (EX o ++ KX k) ∧
      EntryOk σ m o k ∧ F2.decode (ent σ o k) = .success false k.ah 20 ∧ k.ah + 20 ≤ k.el ∧
      KeysListOk σ o k ∧ KeysWalked (kpl σ o k) k.j k.keys ∧ k.j < k.kl ∧ m.reg 27 = 32 ∧
      ∃ before : List Byte,
        BytesAt m (σ.sl 0x100) (F2.result40 (keyPtr σ o k) (kwin σ o k) before) := by
  have hcm := A1a0_common h
  obtain ⟨mc, _, ⟨o, k, L, hie, ⟨hkw, -, -, -⟩, -, hj, ha⟩, hpost, hp⟩ := h
  obtain ⟨hc, hok, hregs, -, hlive, ⟨hd, hle, r26⟩, ⟨had, hal, -⟩, hkl, r27⟩ := hie
  have hpre := hc.2.1
  have hout : mc.reg 10 = σ.sl 0x100 := ha.arg 0 (by simp)
  have hin : mc.reg 11 = keyPtr σ o k := ha.arg 1 (by simp)
  have hlen : mc.reg 12 = w (k.kl - k.j) := ha.arg 2 (by simp)
  have hR := f2_frame hc hout (by decide) (by decide)
  obtain ⟨k0, k8⟩ := rest_keep hpre hpost.2.1 hR
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hpl := hok.2.1
  have hi := hregs.2.2.1
  have hkb := hkl.2
  have hl : (mc.reg 12).toNat = k.kl - k.j := by
    rw [hlen]; simp only [w, BitVec.toNat_ofNat]; omega
  obtain ⟨before, -, hb⟩ := f2_result hc hout (by decide) (by decide)
    (off := o.h + o.i + k.eh + (k.ah + 20) + k.kh + k.j)
    (by rw [hin]; simp only [keyPtr, kplPtr, aftPtr, entPtr, curPtr, w]; bv_omega) (by omega) hpost
  rw [hl, ← kwin_eq σ o k hle hkb (by omega),
    show σ.inp + w (o.h + o.i + k.eh + (k.ah + 20) + k.kh + k.j) = keyPtr σ o k by
      simp only [keyPtr, kplPtr, aftPtr, entPtr, curPtr, w]; bv_omega] at hb
  exact ⟨hcm, o, k, L, ⟨hok.1, hok.2.1, k0.trans hok.2.2.1, k8.trans hok.2.2.2.1, hok.2.2.2.2⟩,
    hi, live_keep hpre hlive hpost.2.1 hp hR, ⟨hd, hle, (hpost.1.2 26 (by decide)).trans r26⟩,
    had, hal, hkl, hkw, hj, (hpost.1.2 27 (by decide)).trans r27, before, hb⟩

/-- A key rejection at `0x800001a0`. -/
theorem key_err {σ : Sig} {m : Machine} {o : Obs} {k : Kobs} {L : List (Word × Nat)}
    (hcm : Common σ m) (hok : OuterOk σ m o) (hi : o.i < o.p) (hlive : Live σ m L (EX o ++ KX k))
    (he : EntryOk σ m o k) (had : F2.decode (ent σ o k) = .success false k.ah 20)
    (hal : k.ah + 20 ≤ k.el) (hkl : KeysListOk σ o k) (hkw : KeysWalked (kpl σ o k) k.j k.keys)
    (hj : k.j < k.kl) (hrej : ∀ kh', F2.decode (kwin σ o k) ≠ .success false kh' keySize) :
    ErrOk σ m := by
  have hpre := hcm.2.1
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hil : σ.input.length = σ.len := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpl := hok.2.1
  have hle := he.2.1
  have hkb := hkl.2
  have hne : kwin σ o k ≠ [] := by
    rw [kwin_eq σ o k hle hkb (by omega)]
    intro h0; have := congrArg List.length h0
    simp only [List.length_take, List.length_drop, List.length_nil, Sig.input] at this hil
    omega
  have hkn := keys_none_head hne hrej
  have hkp : (keysWalk (kpl σ o k).length (kpl σ o k)).2 = none := by
    rw [hkw.2.1]; simp only [kwin] at hkn; rw [hkn]; rfl
  exact outer_err hcm hok hlive (entries_none_entry (win_ne hok hi hpre) he.1
    (entry_none_kw had hkl.1 hkp))

theorem TX.leaf_800001a0_0 :
    LeafGoal TX.plan TX.plan.cuts[7]! ((TX.plan.leaves 0x800001a0)[0]!) := by
  show LeafGoal TX.plan cut1a0 (run1a0_leaves[0]!)
  have hcs : (run1a0_leaves[0]!).conds = [SBool.ne (Sym.init 0 352 2) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envP_ok (A1a0_common hA) (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_)
    (fun σ m hA hc => ?_)
  · have : (run1a0_leaves[0]!).S.steps - S1a0.steps = 21 := by decide
    show _ ≤ 32 * (afterEntry m + keysLeft m) + 658; simp only [cut1a0, mkCut] at *; omega
  obtain ⟨hcm, o, k, L, hok, hi, hlive, he, had, hal, hkl, hkw, hj, -, before, hb⟩ := ret1a0 hA
  have h1 : SBool.eval (envP 0x100 σ m) (SBool.ne (Sym.init 0 352 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  simp only [SBool.eval] at h1
  rw [show (352 : Nat) = frameBytes - 0x100 + 32 from rfl,
    slot_val (BaseEnv.ofP 0x100 σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h1
  have hdec := dec_err (by simpa [Sym.eval] using h1)
  exact key_err hcm hok hi hlive he had hal hkl hkw hj fun kh' h => by rw [hdec] at h; cases h

theorem TX.leaf_800001a0_1 :
    LeafGoal TX.plan TX.plan.cuts[7]! ((TX.plan.leaves 0x800001a0)[1]!) := by
  show LeafGoal TX.plan cut1a0 (run1a0_leaves[1]!)
  have hcs : (run1a0_leaves[1]!).conds = [SBool.eq (Sym.init 0 352 2) (Sym.lit 0),
      SBool.ne (Sym.bin BinOp.and (Sym.init 0 336 1) (Sym.lit 1)) (Sym.lit 0)] := by decide
  refine err_leaf rfl (fun σ m hA => envP_ok (A1a0_common hA) (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_)
    (fun σ m hA hc => ?_)
  · have : (run1a0_leaves[1]!).S.steps - S1a0.steps = 24 := by decide
    show _ ≤ 32 * (afterEntry m + keysLeft m) + 658; simp only [cut1a0, mkCut] at *; omega
  obtain ⟨hcm, o, k, L, hok, hi, hlive, he, had, hal, hkl, hkw, hj, -, before, hb⟩ := ret1a0 hA
  have h1 : SBool.eval (envP 0x100 σ m) (SBool.eq (Sym.init 0 352 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envP 0x100 σ m)
      (SBool.ne (Sym.bin BinOp.and (Sym.init 0 336 1) (Sym.lit 1)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  simp only [SBool.eval] at h1 h2
  replace h2 : ((Sym.init 0 336 1).eval (envP 0x100 σ m) &&& 1#64 != 0#64) = true := h2
  rw [show (352 : Nat) = frameBytes - 0x100 + 32 from rfl,
    slot_val (BaseEnv.ofP 0x100 σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h1
  rw [show (336 : Nat) = frameBytes - 0x100 + 16 from rfl,
    slot_val (BaseEnv.ofP 0x100 σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h2
  obtain ⟨b, hh, q, hd, hl⟩ := dec_ok (by simpa [Sym.eval] using h1)
  rw [hl] at h2
  cases b
  · simp at h2
  · exact key_err hcm hok hi hlive he had hal hkl hkw hj fun kh' h => by rw [hd] at h; cases h

theorem TX.leaf_800001a0_2 :
    LeafGoal TX.plan TX.plan.cuts[7]! ((TX.plan.leaves 0x800001a0)[2]!) := by
  show LeafGoal TX.plan cut1a0 (run1a0_leaves[2]!)
  have hcs : (run1a0_leaves[2]!).conds = [SBool.eq (Sym.init 0 352 2) (Sym.lit 0),
      SBool.eq (Sym.bin BinOp.and (Sym.init 0 336 1) (Sym.lit 1)) (Sym.lit 0),
      SBool.ne (Sym.init 0 328 8) (Sym.var 27)] := by decide
  refine err_leaf rfl (fun σ m hA => envP_ok (A1a0_common hA) (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun σ m _ => ?_)
    (fun σ m hA hc => ?_)
  · have : (run1a0_leaves[2]!).S.steps - S1a0.steps = 26 := by decide
    show _ ≤ 32 * (afterEntry m + keysLeft m) + 658; simp only [cut1a0, mkCut] at *; omega
  obtain ⟨hcm, o, k, L, hok, hi, hlive, he, had, hal, hkl, hkw, hj, r27, before, hb⟩ := ret1a0 hA
  have h3 : SBool.eval (envP 0x100 σ m) (SBool.ne (Sym.init 0 328 8) (Sym.var 27)) = true :=
    hc _ (by rw [hcs]; simp)
  simp only [SBool.eval] at h3
  rw [show (328 : Nat) = frameBytes - 0x100 + 8 from rfl,
    slot_val (BaseEnv.ofP 0x100 σ m) hcm.2.1 (by decide) (by decide) hb (by decide)] at h3
  have rv : (Sym.var 27).eval (envP 0x100 σ m) = 32 := by
    simp only [Sym.eval, envP, Env.setVars, envB, entryEnv]
    simpa using r27
  rw [rv] at h3
  refine key_err hcm hok hi hlive he had hal hkl hkw hj fun kh' h => ?_
  rw [dec_len h] at h3
  simp [keySize] at h3

end ZesuExec.Fn.TX
