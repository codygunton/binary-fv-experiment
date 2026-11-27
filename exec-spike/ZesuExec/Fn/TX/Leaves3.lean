import ZesuExec.Fn.TX.Leaves2

/-!
# TX: leaves that write memory and reach a cut or a call (programme plan S6 step 6)

The outer item accepted (`0x80000068`: to the loop head `0x800000c4`, or to `toOwnedSlice` of the
empty entries list), a key stored (`0x80000230`: back to the keys loop `0x8000018c`, or to
`toOwnedSlice` of the keys list). A leaf with writes keeps `Common` (`common_keep`) when its
writes miss the save area, keeps the allocator's heap when they miss `Priv L`, and its written
words are read back with `load_cst`.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## `toOwnedSlice`'s precondition at a call from TX -/

/-- `toOwnedSlice(S-kr, S-kh, ao)` from a `Common` machine: the list header in the frame slot
`S-kh`, its buffer (if any) a block of TX's live list. -/
theorem towned_pre {eb : Nat} {σ : Sig} {m : Machine} {L X : List (Word × Nat)}
    {items : List Byte} (hc : Common σ m) (hlive : Live σ m L X) {kr kh : Nat}
    (hres : m.reg 10 = σ.sl kr) (hhdr : m.reg 11 = σ.sl kh) (hao : m.reg 12 = σ.ao)
    (hra : RetAligned m) (heb : 0 < eb) (hkr : 24 ≤ kr) (hkr' : kr ≤ 576) (hkh : 24 ≤ kh)
    (hkh' : kh ≤ 576) (hkr8 : kr % 8 = 0) (hkh8 : kh % 8 = 0) (hd : kr + 24 ≤ kh ∨ kh + 24 ≤ kr)
    {p n c : Word} (hH : F1.HeaderIs m (σ.sl kh) p n c) (hnc : n.toNat ≤ c.toNat)
    (hit : items.length = n.toNat * eb) (hp : 0 < p.toNat)
    (hX : 0 < c.toNat → RamRange p (c.toNat * eb) ∧ (p, c.toNat * eb) ∈ X)
    (hb : BytesAt m p items) : ToOwned.Pre eb σ.A L items m := by
  have hpre := hc.2.1
  obtain ⟨hlo, hhi, h16, -, -, -⟩ := entry_nums hpre
  have hS704 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have hSr := sl_toNat hpre (k := kr) (by unfold stackBytes; omega)
  have hSh := sl_toNat hpre (k := kh) (by unfold stackBytes; omega)
  have hS688 := sl_toNat hpre (k := 688) (by decide)
  have r2 : m.reg 2 = σ.sl 576 := hc.2.2.2.1
  have hsp : (m.reg 2).toNat = σ.S.toNat - 576 := by rw [r2]; exact sl_toNat hpre (by decide)
  have hsp112 : m.reg 2 - 112 = σ.sl 688 := by rw [r2]; simp only [Sig.sl, w]; bv_omega
  obtain ⟨-, -, -, -, -, -, hRao, hao8, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    d27, -, -, -, d31, -, -, d34, hP⟩ := hpre
  unfold Apart at d27 d31 d34
  rw [hS704] at d27 d34
  unfold stackBytes at d27 d34
  have hlo' : 2684355264 ≤ σ.S.toNat := by unfold Layout.ramLo at hlo; omega
  unfold RamRange at hRao
  have e1 : ToOwned.listPtr m = p := by simp [ToOwned.listPtr, ToOwned.wordAt, hhdr, hH.1]
  have e2 : ToOwned.listLen m = n := by
    simp only [ToOwned.listLen, ToOwned.wordAt, hhdr]; rw [hH.2.1]; rfl
  have e3 : ToOwned.listCap m = c := by
    simp only [ToOwned.listCap, ToOwned.wordAt, hhdr]; rw [hH.2.2]; rfl
  -- what is not the allocator's
  have hnp : ∀ a, (InRange (σ.sl kr) 24 a ∨ InRange (σ.sl kh) 24 a ∨ InRange σ.ao 16 a ∨
      InRange (σ.sl 688) 112 a ∨ InRange scratch 8 a) → ¬ σ.A.Priv σ.g.L a := by
    intro a h
    rcases h with h | h | h | h | h
    · exact stack_not_priv hc.2.1 (sl_in_stack hc.2.1 (by unfold stackBytes; omega) hkr h)
    · exact stack_not_priv hc.2.1 (sl_in_stack hc.2.1 (by unfold stackBytes; omega) hkh h)
    · exact hP a (.inr (.inl h))
    · exact stack_not_priv hc.2.1 (sl_in_stack hc.2.1 (by decide) (by decide) h)
    · exact hP a (.inr (.inr (.inr (.inr (.inr h)))))
  have hsc : scratch.toNat = Layout.extraParams := by simp [scratch, Layout.extraParams]
  have hsc' : ToOwned.scratch.toNat = Layout.extraParams := by
    simp [ToOwned.scratch, Layout.extraParams]
  rw [hsc] at d31 d34
  have hblk : 0 < c.toNat → ∀ a, InRange p (c.toNat * eb) a → σ.A.Priv σ.g.L a := fun h0 a ha =>
    (hlive.2.2 _ (hX h0).2).2.2 a ha
  simp only [ToOwned.Pre, e1, e2, e3, hres, hhdr, hao]
  refine ⟨hc.2.2.1, ⟨by rw [hsp]; omega, by rw [hsp]; unfold Layout.ramLo at *; omega,
    by rw [hsp]; omega, fun j hj => ?_⟩, hra, ?_, ?_, fun j hj => ?_, ?_, ?_, hH, hnc, hit, hp,
    fun h0 => ⟨(hX h0).1, hlive.2.1.symm.subset (List.mem_append_right _ (hX h0).2)⟩, hb,
    hRao, hao8, ?_, common_vtable hc, hc.2.2.2.2.2.2.2.2.2.2.2.2.1, hlive.1, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, fun h0 => ⟨
      apart_of_priv (Nat.mul_pos h0 heb) (by decide) (hblk h0) fun a h => hnp a (.inl h),
      apart_of_priv (Nat.mul_pos h0 heb) (by decide) (hblk h0) fun a h => hnp a (.inr (.inl h)),
      apart_of_priv (Nat.mul_pos h0 heb) (by decide) (hblk h0)
        fun a h => hnp a (.inr (.inr (.inl h))),
      (by rw [hsp112]; exact apart_of_priv (Nat.mul_pos h0 heb) (by decide) (hblk h0)
            (fun a h => hnp a (.inr (.inr (.inr (.inl h)))))),
      apart_of_priv (Nat.mul_pos h0 heb) (by decide) (hblk h0)
        fun a h => hnp a (.inr (.inr (.inr (.inr h))))⟩, fun a h => fun hpa =>
      hnp a ?_ (priv_sub hc.2.1 hlive hpa)⟩
  · have := stack_present' hc (k := 688) (j := j) (by omega) (by decide)
    rwa [show m.reg 2 - 112#64 = σ.sl 688 by rw [r2]; simp only [Sig.sl, w]; bv_omega]
  · unfold RamRange; rw [hSr]; unfold Layout.ramLo Layout.ramHi at *; omega
  · rw [hSr]; exact Nat.sub_mod_eq_zero_of_mod_eq (by omega)
  · exact stack_present' hc (k := kr) (j := j) (by omega) (by unfold stackBytes; omega)
  · unfold RamRange; rw [hSh]; unfold Layout.ramLo Layout.ramHi at *; omega
  · rw [hSh]; exact Nat.sub_mod_eq_zero_of_mod_eq (by omega)
  · rw [load_congr (m := σ.m) fun t ht => ao_same hc (by omega)]
    exact hc.2.1.2.2.2.2.2.2.2.2.1
  all_goals try rw [hsp112]
  all_goals try simp only [Sig.ao]
  all_goals try (unfold ToOwned.Apart
                 first
                   | (simp only [hSr, hSh, hS688, hsc']; omega)
                   | omega)
  all_goals try (simpa only [hsp112] using h)

/-! ## `0x80000068`: the outer item is a list -/

/-- The facts of `0x80000068` once the outer `decodeItem` found a list. -/
theorem acc068 {σ : Sig} {m : Machine} (hA : ARet f2C (unit Site064) σ m)
    (h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 120 2) (Sym.lit 0)) = true)
    (h2 : SBool.eval (envB σ m)
      (SBool.ne (Sym.bin BinOp.and (Sym.init 0 104 1) (Sym.lit 1)) (Sym.lit 0)) = true) :
    Common σ m ∧ (∃ L, Live σ m L []) ∧ m.reg 23 = σ.inp ∧ m.reg 24 = w σ.len ∧
    ∃ hh q, F2.decode σ.input = .success true hh q ∧ hh + q ≤ σ.len ∧
      WalkFits (itemPayload σ.input hh q) ∧
      (Sym.init 0 88 8).eval (envB σ m) = σ.inp + w hh ∧
      (Sym.init 0 96 8).eval (envB σ m) = w q ∧
      (Sym.init 0 112 8).eval (envB σ m) = w (hh + q) := by
  obtain ⟨hcm, hL, -, -, before, -, hb⟩ := ret068 hA
  obtain ⟨mc, _, hs, hpost, -⟩ := hA
  have hpre := hcm.2.1
  have r23 : m.reg 23 = σ.inp := (hpost.1.2 23 (by decide)).trans hs.2.2.2.2.2.1
  have r24 : m.reg 24 = w σ.len := (hpost.1.2 24 (by decide)).trans hs.2.2.2.2.2.2.1
  simp only [SBool.eval] at h1 h2
  replace h2 : ((Sym.init 0 104 1).eval (envB σ m) &&& 1#64 != 0#64) = true := h2
  rw [show (120 : Nat) = frameBytes - 0x1e8 + 32 from rfl,
    slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide)] at h1
  rw [show (104 : Nat) = frameBytes - 0x1e8 + 16 from rfl,
    slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide)] at h2
  obtain ⟨b, hh, q, hd, hl⟩ := dec_ok (by simpa [Sym.eval] using h1)
  rw [hl] at h2
  cases b
  · simp at h2
  have hdom : Domain σ.input := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hil : σ.input.length = σ.len := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hf : HeaderFits σ.input := hdom.1 (outerCall, σ.input) (by simp [calls, walk, hd])
  obtain ⟨-, hle, -⟩ := fits_bounds hf hd
  refine ⟨hcm, hL, r23, r24, hh, q, hd, by omega, fun c hc => hdom.1 c (by
    simp only [calls, walk, hd, List.mem_cons]; exact .inr hc), ?_, ?_, ?_⟩
  · rw [show (88 : Nat) = frameBytes - 0x1e8 + 0 from rfl,
      slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide), dec_ptr hd]
  · rw [show (96 : Nat) = frameBytes - 0x1e8 + 8 from rfl,
      slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide), dec_len hd]
  · rw [show (112 : Nat) = frameBytes - 0x1e8 + 24 from rfl,
      slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide), dec_cons hd]

/-- The machine after a leaf of `0x80000068` that accepted the outer list: `rest` is past the
outer item and the entries list header `S-0x1c0` is `{8, 0, 0}`. -/
theorem after068 {σ : Sig} {m m' : Machine} {S' : SState} (hA : ARet f2C (unit Site064) σ m)
    (h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 120 2) (Sym.lit 0)) = true)
    (h2 : SBool.eval (envB σ m)
      (SBool.ne (Sym.bin BinOp.and (Sym.init 0 104 1) (Sym.lit 1)) (Sym.lit 0)) = true)
    (hm' : Match (envB σ m) S' m') (hS' : S'.regions = baseRegions)
    (hfr : SameOutside (InWritable (envB σ m) S068) m m')
    (hno : S'.mem.all (fun w => w.r != 0 || decide (w.off + w.n ≤ 472)) = true)
    (hr : ∀ i ∈ ([2, 8, 9, 18, 19] : List (Fin 32)), S'.reg i.val = S068.reg i.val)
    (hw0 : readConst S' 0 128 8 = .lit 8) (hw8 : readConst S' 0 136 8 = .lit 0)
    (hw16 : readConst S' 0 144 8 = .lit 0)
    (hr0 : readConst S' 2 0 8 = .bin .add (.var 23) (.init 0 112 8))
    (hr8 : readConst S' 2 8 8 = .bin .sub (.var 24) (.init 0 112 8)) :
    Common σ m' ∧ ∃ L hh q, Live σ m' L [] ∧ F2.decode σ.input = .success true hh q ∧
      hh + q ≤ σ.len ∧ OuterOk σ m' ⟨hh, q, 0, [], [], 8, 0⟩ ∧
      EList σ m' ⟨hh, q, 0, [], [], 8, 0⟩ 0 ∧
      (Sym.init 0 88 8).eval (envB σ m) = σ.inp + w hh ∧
      (Sym.init 0 96 8).eval (envB σ m) = w q := by
  obtain ⟨hcm, ⟨L, hlive⟩, r23, r24, hh, q, hd, hle, hfit, e88, e96, e112⟩ := acc068 hA h1 h2
  have hpre := hcm.2.1
  have hwf : Env.WF (envB σ m) S068 := pre_wf hpre m ovRest [vtableKnown]
  have hm : Match (envB σ m) S068 m := (body_ok hcm (ovRest_ok hcm ?_) (ks := [vtableKnown])
    (by intro k hk t ht; simp only [List.mem_singleton] at hk; subst hk
        exact common_known_vtable hcm t ht)).2.1
  rotate_left
  · obtain ⟨mc, _, hs, hpost, -⟩ := hA
    exact (hpost.1.2 22 (by decide)).trans hs.2.2.2.2.1
  have hwf' : Env.WF (envB σ m) S' := hwf.congr (by rw [hS']; rfl)
  obtain ⟨hc', hlive', -⟩ := base_leaf hcm hlive (BaseEnv.ofB σ m) hwf rfl hm' hS' hfr hno
    (regs_keep hm hm' _ hr)
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have fw := fun k hk hk' => frame_word (BaseEnv.ofB σ m) hwf' hm' hS' (k := k) hk hk'
  have rw0 := rest_word (BaseEnv.ofB σ m) hwf' hm' hS' (off := 0) (.inl rfl)
  have rw8 := rest_word (BaseEnv.ofB σ m) hwf' hm' hS' (off := 8) (.inr rfl)
  rw [hr0] at rw0; rw [hr8] at rw8
  simp only [Sym.eval_bin, Sym.eval_var, e112, BinOp.eval] at rw0 rw8
  refine ⟨hc', L, hh, q, hlive', hd, hle, ⟨hd, by simpa using hle, ?_, ?_, ?_⟩, ?_, e88, e96⟩
  · rw [show σ.rest = σ.rest + BitVec.ofNat 64 0 by simp, rw0]
    show some (m.reg 23 + _) = _; rw [r23]
  · rw [show σ.rest + 8 = σ.rest + BitVec.ofNat 64 8 from rfl, rw8]
    show some (m.reg 24 - _) = _; rw [r24]
  · refine ⟨Nat.zero_le _, by simp, ?_⟩
    simpa [pl] using hfit
  · have f0 := fw 0x1c0 (by decide) (by decide)
    have f8 := fw 0x1b8 (by decide) (by decide)
    have f16 := fw 0x1b0 (by decide) (by decide)
    rw [show 576 - 0x1c0 = 128 from rfl, hw0] at f0
    rw [show 576 - 0x1b8 = 136 from rfl, hw8] at f8
    rw [show 576 - 0x1b0 = 144 from rfl, hw16] at f16
    refine ⟨⟨f0, ?_, ?_⟩, by simp, by simp, fun _ => rfl, by simp, fun h => by simp at h,
      rfl, fun i hi => by simp [entriesBytes] at hi, fun x hx => by simp at hx⟩
    · rw [show σ.sl 0x1c0 + 8 = σ.sl 0x1b8 by simp only [Sig.sl, w]; bv_omega, f8]; rfl
    · rw [show σ.sl 0x1c0 + 16 = σ.sl 0x1b0 by simp only [Sig.sl, w]; bv_omega, f16]; rfl

theorem TX.leaf_80000068_3 :
    LeafGoal TX.plan TX.plan.cuts[1]! ((TX.plan.leaves 0x80000068)[3]!) := by
  show LeafGoal TX.plan cut068 (run068_leaves[3]!)
  have hcs : (run068_leaves[3]!).conds = [SBool.eq (Sym.init 0 120 2) (Sym.lit 0),
      SBool.ne (Sym.bin BinOp.and (Sym.init 0 104 1) (Sym.lit 1)) (Sym.lit 0),
      SBool.ne (Sym.init 0 96 8) (Sym.lit 0)] := by decide
  have hsteps : (run068_leaves[3]!).S.steps - S068.steps = 23 := by decide
  intro σ m hA hc
  have hA' : ARet f2C (unit Site064) σ m := hA
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 120 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envB σ m)
      (SBool.ne (Sym.bin BinOp.and (Sym.init 0 104 1) (Sym.lit 1)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h3 : SBool.eval (envB σ m) (SBool.ne (Sym.init 0 96 8) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  refine ⟨nil_obligs (by decide), ?_, ?_⟩
  · show (run068_leaves[3]!).S.steps - S068.steps ≤ 32 * σ.len + 323
    rw [hsteps]; omega
  intro m' hm' hex hfr
  have hx : (run068_leaves[3]!).exit = .at 0x800000c4 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x800000c4 at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) S068) m m' at hfr
  obtain ⟨hc', L, hh, q, hlive', hd, hle, hok, hel, e88, e96⟩ := after068 hA' h1 h2 hm'
    (by decide) hfr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have hpre := hc'.2.1
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have reg : ∀ (i : Fin 32) (s : Sym), (run068_leaves[3]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r20 := (reg 20 _ (by decide : (run068_leaves[3]!).S.reg 20 = .init 0 88 8)).trans e88
  have r21 := (reg 21 _ (by decide : (run068_leaves[3]!).S.reg 21 = .init 0 96 8)).trans e96
  have r24 := reg 24 _ (by decide : (run068_leaves[3]!).S.reg 24 = .lit 20)
  have r25 := reg 25 _ (by decide : (run068_leaves[3]!).S.reg 25 = .lit 1)
  have r27 := reg 27 _ (by decide : (run068_leaves[3]!).S.reg 27 = .lit 32)
  simp only [SBool.eval, e96] at h3
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0; simp [w, Sym.eval] at h3
    · exact h0
  have hwf' : Env.WF (envB σ m) (run068_leaves[3]!).S :=
    (pre_wf hpre m ovRest [vtableKnown]).congr (by decide)
  have hmag := frame_word (BaseEnv.ofB σ m) hwf' hm' (by decide) (k := 0x1f0) (by decide) (by decide)
  rw [show readConst (run068_leaves[3]!).S 0 (576 - 0x1f0) 8 = .lit 0xffffffffcccccccd by decide]
    at hmag
  have hEX : EX ⟨hh, q, 0, [], [], 8, 0⟩ = [] := by simp [EX, keysBlocks]
  have hs : OuterState σ m' ⟨hh, q, 0, [], [], 8, 0⟩ L :=
    ⟨hc', hok, ⟨by rw [r20]; simp [curPtr], by rw [r21]; simp, hq, hmag⟩, ⟨r24, r25, r27⟩, hel,
      by rw [hEX]; exact hlive'⟩
  refine ExitGoal.at_cut rfl ⟨cut0c4, by simp [TX.plan, vcPlan], hex, ⟨hex, _, L, hs⟩, ?_⟩
  show 32 * (m'.reg 21).toNat + 300 ≤ 32 * σ.len + 323 - ((run068_leaves[3]!).S.steps - S068.steps)
  rw [hsteps, r21]; simp only [w, BitVec.toNat_ofNat]; omega

theorem TX.leaf_80000068_2 :
    LeafGoal TX.plan TX.plan.cuts[1]! ((TX.plan.leaves 0x80000068)[2]!) := by
  show LeafGoal TX.plan cut068 (run068_leaves[2]!)
  have hcs : (run068_leaves[2]!).conds = [SBool.eq (Sym.init 0 120 2) (Sym.lit 0),
      SBool.ne (Sym.bin BinOp.and (Sym.init 0 104 1) (Sym.lit 1)) (Sym.lit 0),
      SBool.eq (Sym.init 0 96 8) (Sym.lit 0)] := by decide
  have hsteps : (run068_leaves[2]!).S.steps - S068.steps = 22 := by decide
  intro σ m hA hc
  have hA' : ARet f2C (unit Site064) σ m := hA
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 120 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envB σ m)
      (SBool.ne (Sym.bin BinOp.and (Sym.init 0 104 1) (Sym.lit 1)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h3 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 96 8) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  refine ⟨nil_obligs (by decide), ?_, ?_⟩
  · show (run068_leaves[2]!).S.steps - S068.steps ≤ 32 * σ.len + 323
    rw [hsteps]; omega
  intro m' hm' hex hfr
  have hx : (run068_leaves[2]!).exit = .call 0x800d6554 0x800004a0 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x800d6554 at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) S068) m m' at hfr
  obtain ⟨hc', L, hh, q, hlive', hd, hle, hok, hel, -, e96⟩ := after068 hA' h1 h2 hm'
    (by decide) hfr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  simp only [SBool.eval, e96] at h3
  have hq : q = 0 := by
    have := congrArg BitVec.toNat (beq_iff_eq.mp h3)
    simp only [w, Sym.eval, BitVec.toNat_ofNat] at this
    omega
  subst hq
  have reg : ∀ (i : Fin 32) (s : Sym), (run068_leaves[2]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r1 := reg 1 _ (by decide : (run068_leaves[2]!).S.reg 1 = .lit 0x800004a0)
  have r10 := reg 10 _ (by decide : (run068_leaves[2]!).S.reg 10 = .ptr 0 440)
  have r11 := reg 11 _ (by decide : (run068_leaves[2]!).S.reg 11 = .ptr 0 128)
  have r12 := reg 12 _ (by decide : (run068_leaves[2]!).S.reg 12 = .ptr 3 0)
  simp only [Sym.eval, Env.base, envB, entryEnv, shapeOf, List.getD_cons_zero,
    List.getD_cons_succ, Sig.sl, w, frameBytes] at r1 r10 r11 r12
  rw [show σ.S - 576#64 + BitVec.ofInt 64 440 = σ.sl 0x88 by simp only [Sig.sl, w]; bv_omega]
    at r10
  rw [show σ.S - 576#64 + BitVec.ofInt 64 128 = σ.sl 0x1c0 by simp only [Sig.sl, w]; bv_omega]
    at r11
  rw [BitVec.ofInt_ofNat, BitVec.add_zero] at r12
  have hEX : EX ⟨hh, 0, 0, [], [], 8, 0⟩ = [] := by simp [EX, keysBlocks]
  have hlive'' : Live σ m' L (EX ⟨hh, 0, 0, [], [], 8, 0⟩) := by rw [hEX]; exact hlive'
  have hsite : Site49c σ (L, []) m' := ⟨⟨hh, 0, 0, [], [], 8, 0⟩, hc', hok, rfl, hel, hlive'',
    by simp [entriesBytes], r1, fun t ht => by
      simp only [List.length_cons, List.length_nil] at ht
      obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
      · exact r10
      · exact r11
      · exact r12⟩
  have hpre5 : F5.Pre σ.A L [] m' := towned_pre (eb := 40) hc' hlive' r10 r11 r12
    (by unfold RetAligned; rw [r1]; decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hel.1 (by simp) (by simp)
    (by show (0:Nat) < (8 : Word).toNat; decide)
    (fun h => by simp at h) (fun i hi => by simp at hi)
  refine ⟨f5C, (L, []), rfl, hex, hpre5, fun m'' hpost => ⟨cut4a0, by simp [TX.plan, vcPlan], rfl,
    ?_, ⟨m', (L, []), hsite, hpost⟩, ?_⟩⟩
  · rw [hpost.1.1.1, r1]; decide
  · show F5.bound + 23 ≤ 32 * σ.len + 323 - ((run068_leaves[2]!).S.steps - S068.steps)
    rw [hsteps]; unfold F5.bound; omega

/-! ## `0x80000230`: the key stored into its slot -/

/-- The key store writes only its 32-byte slot. -/
theorem slot_same {σ : Sig} {m m' : Machine} {S' : SState} (hc : Common σ m)
    (hm' : Match (envS keySize σ m) S' m') (hS' : S'.regions = baseRegions ++ [slotR 32])
    (hfr : SameOutside (InWritable (envS keySize σ m) S230) m m')
    (hall : S'.mem.all (fun w => w.r == 5) = true) (hram : RamRange (m.reg 10) keySize) :
    SameOutside (InRange (m.reg 10) keySize) m m' := by
  intro a ha
  by_cases hw : InWritable (envS keySize σ m) S230 a
  · obtain ⟨r, R, j, hR, -, hj, rfl⟩ := hw
    have hr6 : r < 6 := by
      have := (List.getElem?_eq_some_iff.mp hR).1
      simpa [S230, entryState, baseRegions] using this
    rcases Nat.lt_or_ge r 5 with h5 | h5
    · have hp := common_present hc r j h5 (by rwa [← envS_size (n := keySize) h5])
      rw [← envS_base (n := keySize) h5] at hp
      refine byte_keep hm' (by rw [hS']; simp [baseRegions]; omega) hj (fun w hw => ?_)
        (mem0_entry hp)
      have := List.all_eq_true.mp hall w hw
      simp only [beq_iff_eq] at this
      simp only [Write.covers, this, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
        decide_eq_false_iff_not]
      omega
    · obtain rfl : r = 5 := by omega
      exfalso; apply ha
      have hb : (envS keySize σ m).base 5 = m.reg 10 := rfl
      have hs : (envS keySize σ m).size 5 = keySize := rfl
      rw [hb]; rw [hs] at hj
      unfold RamRange Layout.ramHi at hram
      exact in_self (by omega) hj
  · exact hfr a hw

/-- The slot holds the key's words read from `S-0xd8`. -/
theorem slot_bytes {σ : Sig} {m m' : Machine} {S' : SState}
    (hwf : Env.WF (envS keySize σ m) S') (hm' : Match (envS keySize σ m) S' m')
    (hS' : S'.regions = baseRegions ++ [slotR 32])
    (hwr : ∀ t < 4, readConst S' 5 (8 * t) 8 = .var (11 + t))
    (hw : ∀ t < 4, m.load (σ.sl 0xd8 + w (8 * t)) 8 = some (m.reg (Fin.ofNat 32 (11 + t)))) :
    ∀ i < keySize, m'.mem (m.reg 10 + BitVec.ofNat 64 i) =
      m.mem (σ.sl 0xd8 + BitVec.ofNat 64 i) := by
  intro i hi
  have ht : i / 8 < 4 := by unfold keySize at hi; omega
  have l' := load_cst hwf hm' (r := 5) (R := slotR 32) (off := 8 * (i / 8)) (n := 8)
    (by rw [hS']; rfl) (by show 8 * (i / 8) + 8 ≤ keySize; unfold keySize; omega)
  rw [hwr _ ht] at l'
  have b' := load_bytes l' (Nat.le_refl _) (i % 8) (Nat.mod_lt _ (by decide))
  have b := load_bytes (hw _ ht) (Nat.le_refl _) (i % 8) (Nat.mod_lt _ (by decide))
  have e1 : (envS keySize σ m).base 5 + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
      m.reg 10 + BitVec.ofNat 64 i := by
    show m.reg 10 + _ + _ = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * (i / 8) + i % 8 = i by omega]
  have e2 : σ.sl 0xd8 + w (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) =
      σ.sl 0xd8 + BitVec.ofNat 64 i := by
    simp only [w]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * (i / 8) + i % 8 = i by omega]
  rw [e1] at b'; rw [e2] at b
  rw [b', b]; rfl

/-- The state after the key store `0x80000230`, on both of its leaves: the key is the last of
the keys list and the keys cursor is past it. -/
theorem after230 {σ : Sig} {m m' : Machine} {S' : SState} (hA : AKeyStore σ m)
    (hm' : Match (envS keySize σ m) S' m') (hS' : S'.regions = baseRegions ++ [slotR 32])
    (hfr : SameOutside (InWritable (envS keySize σ m) S230) m m')
    (hall : S'.mem.all (fun w => w.r == 5) = true)
    (hwr : ∀ t < 4, readConst S' 5 (8 * t) 8 = .var (11 + t))
    (hr : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 24, 25, 26, 27] : List (Fin 32)),
      S'.reg i.val = S230.reg i.val)
    (hr23 : S'.reg 23 = .bin .add (.var 23) (.var 25)) :
    ∃ o k L, InEntry σ m' o k L ∧ KeysOk σ m' o k ∧ KList σ m' k k.keys.length ∧
      (∀ i ∈ ([21, 22, 26] : List (Fin 32)), m'.reg i = m.reg i) ∧ k.j ≤ k.kl := by
  obtain ⟨-, o, k, L, key, kh', hIE, hKW, hj, hdk, hjk, hkey, hKL, hcap, h10, hkb, hw, r23, r22,
    r25, r24⟩ := hA
  obtain ⟨hc, hok, ⟨r20, r21, hi, hmag⟩, hEL, hlive, ⟨hd, hle, r26⟩, hAO, hKLO, r27⟩ := hIE
  have hpre := hc.2.1
  have m23 : m'.reg 23 = m.reg 23 + m.reg 25 := by rw [Match.reg_eq hm' 23 23 rfl, hr23]; rfl
  have hk0 : 0 < k.kc.toNat := by omega
  have hKX : (k.kq, keySize * k.kc.toNat) ∈ KX k := by simp [KX, hk0]
  have hbram := hKL.2.2.2.2.2.1 hk0
  have hcapb : keySize * k.keys.length + keySize ≤ keySize * k.kc.toNat := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hcap
  obtain ⟨hpriv, hram, hpres⟩ := slot_of_block hlive (p := k.kq) (sz := keySize * k.kc.toNat)
    (off := keySize * k.keys.length) (n := keySize) (List.mem_append_right _ hKX) hbram hcapb h10
  have hwf : Env.WF (envS keySize σ m) S230 := (slot_ok hc hpriv hram hpres).1
  have hm0 : Match (envS keySize σ m) S230 m := (slot_ok hc hpriv hram hpres).2.1
  have hreg : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 24, 25, 26, 27] : List (Fin 32)),
      m'.reg i = m.reg i := fun i hi => by
    rw [Match.reg_eq hm' i i.val rfl, hr i hi, ← Match.reg_eq hm0 i i.val rfl]
  have hwf' : Env.WF (envS keySize σ m) S' := hwf.congr (by rw [hS']; rfl)
  have hso := slot_same hc hm' hS' hfr hall hram
  have hp : Preserved m m' := F1.preserved_of_leaf hwf hm' (by rw [hS']; decide) hfr
  unfold RamRange Layout.ramHi at hbram
  have h10n : (m.reg 10).toNat = k.kq.toNat + keySize * k.keys.length := by
    rw [h10]; exact toNat_add_ofNat (by omega)
  have hinB : ∀ a, InRange (m.reg 10) keySize a → InRange k.kq (keySize * k.kc.toNat) a :=
    fun a ha => by unfold InRange at ha ⊢; omega
  have hsP : ∀ a, InRange (m.reg 10) keySize a → σ.A.Priv σ.g.L a := fun a ha =>
    (hlive.2.2 _ (List.mem_append_right _ hKX)).2.2 a (hinB a ha)
  have hc' : Common σ m' := common_keep hc (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact hreg _ (by decide)) hp hso
    fun a ha => ⟨.inr (hsP a ha), fun hs => stack_not_priv hpre (save_in_stack hpre hs) (hsP a ha)⟩
  have hfs : ∀ kk, kk ≤ 576 → ∀ t < kk,
      m'.mem (σ.sl kk + BitVec.ofNat 64 t) = m.mem (σ.sl kk + BitVec.ofNat 64 t) := by
    intro kk hkk t ht
    have h3 := sl_toNat hpre (k := kk) (by unfold stackBytes; omega)
    have hS := (entry_nums hpre).2.1; unfold Layout.ramHi at hS
    refine hso _ fun hin => stack_not_priv hpre (sl_in_stack hpre (k := kk) (n := kk)
      (by unfold stackBytes; omega) (Nat.le_refl _) (in_self (by rw [h3]; omega) ht)) (hsP _ hin)
  have hbs : ∀ b ∈ EX o, ∀ t < b.2,
      m'.mem (b.1 + BitVec.ofNat 64 t) = m.mem (b.1 + BitVec.ofNat 64 t) := by
    intro b hb t ht
    have hr := (hlive.2.2 b (List.mem_append_left _ hb)).2.1
    unfold RamRange Layout.ramHi at hr
    refine hso _ fun hin => ?_
    have h1 := in_self (a := b.1) (by omega) ht
    have h2 := hinB _ hin
    have := live_apart hlive hb hKX
    dsimp only at this
    simp only [InRange] at h1 h2; omega
  have hL : (k.kq, keySize * k.kc.toNat) ∈ L :=
    hlive.2.1.symm.subset (List.mem_append_right _ (List.mem_append_right _ hKX))
  have hlive' : Live σ m' L (EX o ++ KX k) := ⟨σ.A.heap_frame' L m m' hlive.1
    (fun a hPa => hso a fun hin => σ.A.priv_not_live L a hPa ⟨_, hL, hinB a hin⟩) hp,
    hlive.2.1, hlive.2.2⟩
  have hEL' : EList σ m' o o.done.length := by
    obtain ⟨hH, hle', hp0, hc0, hc32, hram', hil, hbytes, hz⟩ := hEL
    refine ⟨hdr_congr hH fun t ht => hfs 0x1c0 (by decide) t (by omega), hle', hp0, hc0, hc32,
      hram', hil, ?_, fun x hx => ?_⟩
    · rcases Nat.eq_zero_or_pos o.ec.toNat with he | he
      · have : o.done = [] := List.eq_nil_of_length_eq_zero (by omega)
        have : o.is = [] := List.eq_nil_of_length_eq_zero (by rw [hil, this]; rfl)
        intro i hi; simp [entriesBytes, *] at hi
      · have hlen := entriesBytes_length o.done o.is hil fun x hx => ⟨(hz x hx).1, (hz x hx).2.1⟩
        refine bytes_congr hbytes fun t ht => hbs (o.ep, entrySize * o.ec.toNat)
          (by simp [EX, he]) t ?_
        rw [hlen] at ht
        exact Nat.lt_of_lt_of_le ht (Nat.mul_le_mul_left _ hle')
    · obtain ⟨hpad, haddr, hkl', hkram, hkb'⟩ := hz x hx
      refine ⟨hpad, haddr, hkl', hkram, ?_⟩
      by_cases hk : x.1.keys = []
      · rw [hk]; intro i hi; simp at hi
      · exact bytes_congr hkb' fun t ht => hbs _ (by
          simp only [EX, List.mem_append]; exact .inr (mem_keysBlocks hx hk)) t
          (by rw [flatten_length _ hkl'] at ht; exact ht)
  -- the keys walk advances past the key
  obtain ⟨hjl, heq, hfit0⟩ := hKW
  have hfit : KeysFits (kwin σ o k) := hfit0
  have hne : kwin σ o k ≠ [] := by intro h; rw [h] at hdk; simp [F2.decode] at hdk
  have hdk' : F2.decode (kwin σ o k) = .success false kh' 32 := hdk
  obtain ⟨hfit', hstep⟩ := keysFits_tail hfit hne hdk'
  have hhd := keysFits_head hfit hne
  obtain ⟨-, hb2, -⟩ := fits_bounds hhd hdk'
  have hkwl : (kwin σ o k).length = (kpl σ o k).length - k.j := List.length_drop ..
  have hrest : itemRest (kwin σ o k) kh' 32 = (kpl σ o k).drop (k.j + (kh' + keySize)) := by
    rw [(fits_rest hhd hdk').1]; simp only [kwin, List.drop_drop]
    congr 1
  have hkeyl : key.length = keySize := by
    rw [hkey]; unfold keySize; simp only [itemPayload, List.length_take, List.length_drop]
    omega
  refine ⟨o, { k with j := k.j + (kh' + keySize), keys := k.keys ++ [key] }, L,
    ⟨hc', outerOk_keep hpre hso (fun a h => .inr (.inr (hsP a h))) hok,
      ⟨(hreg 20 (by decide)).trans r20, (hreg 21 (by decide)).trans r21, hi,
        (load_congr fun t ht => hfs 0x1f0 (by decide) t (by omega)).trans hmag⟩,
      hEL', hlive', ⟨hd, hle, (hreg 26 (by decide)).trans r26⟩,
      ⟨hAO.1, hAO.2.1, bytes_congr hAO.2.2 fun t ht => hfs 0x158 (by decide) t (by
        simp only [itemPayload, List.length_take] at ht; omega)⟩, hKLO,
      (hreg 27 (by decide)).trans r27⟩,
    ⟨⟨show k.j + (kh' + keySize) ≤ (kpl σ o k).length by unfold keySize; omega, ?_,
      show KeysFits ((kpl σ o k).drop (k.j + (kh' + keySize))) by rw [← hrest]; exact hfit'⟩, ?_,
      show m'.reg 22 = w (k.kl - (k.j + (kh' + keySize))) by
        rw [(hreg 22 (by decide)).trans r22]; congr 1; omega,
      show m'.reg 24 = w (k.keys ++ [key]).length by rw [(hreg 24 (by decide)).trans r24]; simp⟩,
    ?_,
    fun i hi => hreg i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
                           rcases hi with rfl | rfl | rfl <;> decide),
    show k.j + (kh' + keySize) ≤ k.kl by unfold keySize at *; omega⟩
  · change ((keysWalk (kpl σ o k).length (kpl σ o k)).2) =
      ((keysWalk ((kpl σ o k).drop (k.j + (kh' + keySize))).length
        ((kpl σ o k).drop (k.j + (kh' + keySize)))).2).map ((k.keys ++ [key]) ++ ·)
    rw [heq]
    change ((keysWalk (kwin σ o k).length (kwin σ o k)).2).map (k.keys ++ ·) = _
    rw [hstep, hrest, Option.map_map]
    congr 1; funext x; simp [hkey, keySize]
  · show m'.reg 23 = kplPtr σ o k + w (k.j + (kh' + keySize))
    rw [m23, r23, r25]; simp only [keyPtr, w, BitVec.ofNat_add, BitVec.add_assoc]
  · obtain ⟨hH, -, hq0, hc1, hc32, hR, hyl, hkb0⟩ := hKL
    refine ⟨by simpa using hdr_congr hH fun t ht => hfs 0x118 (by decide) t (by omega),
      by simpa using hcap, hq0, hc1, hc32, hR, fun y hy => ?_, ?_⟩
    · simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact hyl y hy
      · exact hkeyl
    · have hfl := flatten_length k.keys hyl
      have hsb := slot_bytes hwf' hm' hS' hwr hw
      intro i hi
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.length_append] at hi ⊢
      rcases Nat.lt_or_ge i k.keys.flatten.length with hlt | hge
      · rw [List.getElem_append_left hlt]
        refine (hso _ fun hin => ?_).trans (hkb0 i hlt)
        unfold InRange at hin
        rw [toNat_add_ofNat (by omega)] at hin
        omega
      · rw [List.getElem_append_right hge]
        have hu : i - k.keys.flatten.length < keySize := by omega
        rw [show k.kq + BitVec.ofNat 64 i = m.reg 10 + BitVec.ofNat 64 (i - k.keys.flatten.length) by
          rw [h10, hfl, BitVec.add_assoc]; simp only [w]; rw [← BitVec.ofNat_add]; congr 2; omega]
        rw [hsb _ hu, hkb _ (by omega)]

theorem TX.leaf_80000230_0 :
    LeafGoal TX.plan TX.plan.cuts[9]! ((TX.plan.leaves 0x80000230)[0]!) := by
  show LeafGoal TX.plan cut230 (run230_leaves[0]!)
  have hcs : (run230_leaves[0]!).conds = [SBool.ne (Sym.var 22) (Sym.lit 0)] := by decide
  have hsteps : (run230_leaves[0]!).S.steps - S230.steps = 6 := by decide
  intro σ m hA hc
  have h1 : SBool.eval (envS keySize σ m) (SBool.ne (Sym.var 22) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h22 : (m.reg 22 != 0#64) = true := h1
  refine ⟨nil_obligs (by decide), ?_, ?_⟩
  · show (run230_leaves[0]!).S.steps - S230.steps ≤ 32 * (afterEntry m + keysLeft m) + 744
    rw [hsteps]; omega
  intro m' hm' hex hfr
  have hx : (run230_leaves[0]!).exit = .at 0x8000018c := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x8000018c at hex
  change Match (envS keySize σ m) _ m' at hm'
  change SameOutside (InWritable (envS keySize σ m) S230) m m' at hfr
  obtain ⟨o, k, L, hie, hko, hkl, hr, hjk⟩ := after230 hA hm' (by decide) hfr (by decide)
    (by decide) (by decide) (by decide)
  have hlt : k.j < k.kl := by
    rcases Nat.lt_or_ge k.j k.kl with h | h
    · exact h
    · exfalso
      have e := hko.2.2.1
      rw [hr 22 (by decide), show k.kl - k.j = 0 by omega] at e
      rw [e] at h22; simp at h22
  refine ExitGoal.at_cut rfl ⟨cut18c, by simp [TX.plan, vcPlan], hex, ⟨hex, o, k, L, hie, hko,
    hkl, hlt⟩, ?_⟩
  show bKeys m' ≤ 32 * (afterEntry m + keysLeft m) + 744 -
    ((run230_leaves[0]!).S.steps - S230.steps)
  rw [hsteps]; unfold bKeys afterEntry keysLeft
  rw [hr 21 (by decide), hr 22 (by decide), hr 26 (by decide)]; omega

theorem TX.leaf_80000230_1 :
    LeafGoal TX.plan TX.plan.cuts[9]! ((TX.plan.leaves 0x80000230)[1]!) := by
  show LeafGoal TX.plan cut230 (run230_leaves[1]!)
  have hcs : (run230_leaves[1]!).conds = [SBool.eq (Sym.var 22) (Sym.lit 0)] := by decide
  have hsteps : (run230_leaves[1]!).S.steps - S230.steps = 11 := by decide
  intro σ m hA hc
  have h1 : SBool.eval (envS keySize σ m) (SBool.eq (Sym.var 22) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h22 : (m.reg 22 == 0#64) = true := h1
  refine ⟨nil_obligs (by decide), ?_, ?_⟩
  · show (run230_leaves[1]!).S.steps - S230.steps ≤ 32 * (afterEntry m + keysLeft m) + 744
    rw [hsteps]; omega
  intro m' hm' hex hfr
  have hx : (run230_leaves[1]!).exit = .call 0x800d677c 0x8000025c := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x800d677c at hex
  change Match (envS keySize σ m) _ m' at hm'
  change SameOutside (InWritable (envS keySize σ m) S230) m m' at hfr
  obtain ⟨o, k, L, hie, hko, hkl, hr, hjk⟩ := after230 hA hm' (by decide) hfr (by decide)
    (by decide) (by decide) (by decide)
  have hc' := hie.1
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hkl64 : k.kl ≤ σ.len := by
    have := hie.2.1.2.1; have := hie.2.2.2.2.2.1.2.1; have := hie.2.2.2.2.2.2.2.1.2; omega
  have hjeq : k.j = k.kl := by
    have e := hko.2.2.1
    rw [hr 22 (by decide), beq_iff_eq.mp h22] at e
    have := congrArg BitVec.toNat e
    simp only [w, BitVec.toNat_ofNat] at this
    omega
  have reg : ∀ (i : Fin 32) (s : Sym), (run230_leaves[1]!).S.reg i.val = s →
      m'.reg i = s.eval (envS keySize σ m) := fun i s h => by
    rw [Match.reg_eq hm' i i.val rfl, h]
  have r1 := reg 1 _ (by decide : (run230_leaves[1]!).S.reg 1 = .lit 0x8000025c)
  have r10 := reg 10 _ (by decide : (run230_leaves[1]!).S.reg 10 = .ptr 0 392)
  have r11 := reg 11 _ (by decide : (run230_leaves[1]!).S.reg 11 = .ptr 0 296)
  have r12 := reg 12 _ (by decide : (run230_leaves[1]!).S.reg 12 = .ptr 3 0)
  simp only [Sym.eval, Env.base, envS, entryEnv, shapeOf, List.cons_append,
    List.getD_cons_zero, List.getD_cons_succ, Sig.sl, w, frameBytes] at r1 r10 r11 r12
  rw [show σ.S - 576#64 + BitVec.ofInt 64 392 = σ.sl 0xb8 by simp only [Sig.sl, w]; bv_omega]
    at r10
  rw [show σ.S - 576#64 + BitVec.ofInt 64 296 = σ.sl 0x118 by simp only [Sig.sl, w]; bv_omega]
    at r11
  rw [BitVec.ofInt_ofNat, BitVec.add_zero] at r12
  have hKW : KeysWalked (kpl σ o k) k.kl k.keys := hjeq ▸ hko.1
  obtain ⟨hH, hlen, hq0, hc1, hc32, hR, hyl, hkb⟩ := hkl
  have hsite : Site258 σ (L, k.keys.flatten) m' := ⟨o, k, hie, rfl, hKW,
    ⟨hH, hlen, hq0, hc1, hc32, hR, hyl, hkb⟩, r1, fun t ht => by
      simp only [List.length_cons, List.length_nil] at ht
      obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
      · exact r10
      · exact r11
      · exact r12⟩
  have hn : (w k.keys.length).toNat = k.keys.length := by
    simp only [w, BitVec.toNat_ofNat]; omega
  have hpre4 : F4.Pre σ.A L k.keys.flatten m' := towned_pre (eb := 32) hc' hie.2.2.2.2.1 r10 r11
    r12 (by unfold RetAligned; rw [r1]; decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hH (by rw [hn]; exact hlen)
    (by rw [hn, flatten_length _ hyl, Nat.mul_comm]; rfl) hq0
    (fun h0 => ⟨by rw [Nat.mul_comm]; exact hR h0, by
      rw [Nat.mul_comm]; exact List.mem_append_right _ (by simp [KX, h0, keySize])⟩) hkb
  refine ⟨f4C, (L, k.keys.flatten), rfl, hex, hpre4, fun m'' hpost => ⟨cut25c,
    by simp [TX.plan, vcPlan], rfl, ?_, ⟨m', (L, k.keys.flatten), hsite, hpost⟩, ?_⟩⟩
  · rw [hpost.1.1.1, r1]; decide
  · have h21 : m''.reg 21 = m.reg 21 :=
      (hpost.1.1.2 21 (by decide)).trans (hr 21 (by decide))
    have h26 : m''.reg 26 = m.reg 26 :=
      (hpost.1.1.2 26 (by decide)).trans (hr 26 (by decide))
    show F4.bound + bTail m'' 539 ≤ 32 * (afterEntry m + keysLeft m) + 744 -
      ((run230_leaves[1]!).S.steps - S230.steps)
    rw [hsteps]; unfold bTail afterEntry keysLeft F4.bound; rw [h21, h26]; omega

/-! ## `0x800000d8`: the entry is a list -/

/-- The window holds `p - i` bytes. -/
theorem win_length {σ : Sig} {m : Machine} {o : Obs} (hok : OuterOk σ m o)
    (hpre : Pre σ.A σ.g σ.m) : (win σ o).length = o.p - o.i := by
  have hil : σ.input.length = σ.len := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have := hok.2.1
  rw [win_eq]; simp only [List.length_take, List.length_drop]; omega

theorem TX.leaf_800000d8_2 :
    LeafGoal TX.plan TX.plan.cuts[3]! ((TX.plan.leaves 0x800000d8)[2]!) := by
  show LeafGoal TX.plan cut0d8 (run0d8_leaves[2]!)
  have hcs : (run0d8_leaves[2]!).conds = [SBool.eq (Sym.init 0 184 2) (Sym.lit 0),
      SBool.ne (Sym.bin BinOp.and (Sym.init 0 168 1) (Sym.lit 1)) (Sym.lit 0)] := by decide
  have hsteps : (run0d8_leaves[2]!).S.steps - SBody.steps = 13 := by decide
  intro σ m hA hc
  have hA' : ARet f2C (unit Site0d4) σ m := hA
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 184 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envB σ m)
      (SBool.ne (Sym.bin BinOp.and (Sym.init 0 168 1) (Sym.lit 1)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  refine ⟨nil_obligs (by decide), ?_, ?_⟩
  · show (run0d8_leaves[2]!).S.steps - SBody.steps ≤ 32 * outerLeft m + 220
    rw [hsteps]; omega
  intro m' hm' hex hfr
  have hx : (run0d8_leaves[2]!).exit = .call 0x800d6960 0x8000010c := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x800d6960 at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SBody) m m' at hfr
  obtain ⟨hcm, o, L, hs, before, hb⟩ := ret0d8 hA'
  have hpre := hcm.2.1
  simp only [SBool.eval] at h1 h2
  replace h2 : ((Sym.init 0 168 1).eval (envB σ m) &&& 1#64 != 0#64) = true := h2
  rw [show (184 : Nat) = frameBytes - 0x1a8 + 32 from rfl,
    slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide)] at h1
  rw [show (168 : Nat) = frameBytes - 0x1a8 + 16 from rfl,
    slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide)] at h2
  obtain ⟨b, eh, el, hd, hl⟩ := dec_ok (by simpa [Sym.eval] using h1)
  rw [hl] at h2
  cases b
  · simp at h2
  have e152 : (Sym.init 0 152 8).eval (envB σ m) = curPtr σ o + w eh := by
    rw [show (152 : Nat) = frameBytes - 0x1a8 + 0 from rfl,
      slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide), dec_ptr hd]
  have e160 : (Sym.init 0 160 8).eval (envB σ m) = w el := by
    rw [show (160 : Nat) = frameBytes - 0x1a8 + 8 from rfl,
      slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide), dec_len hd]
  have e176 : (Sym.init 0 176 8).eval (envB σ m) = w (eh + el) := by
    rw [show (176 : Nat) = frameBytes - 0x1a8 + 24 from rfl,
      slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide), dec_cons hd]
  -- the entry fits the window
  have hok := hs.2.1
  have hi := hs.2.2.1.2.2.1
  have hne := win_ne hok hi hpre
  have hwf0 : WalkFits (win σ o) := hok.2.2.2.2.2.2
  obtain ⟨-, hfl, -⟩ := fits_bounds (walkFits_head hwf0 hne) hd
  rw [win_length hok hpre] at hfl
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hle := hok.2.1
  -- the machine at the call: no writes
  obtain ⟨-, hm, -⟩ := body_cut hcm
  have hmem := mem_same_nowrite hcm rfl hm' (by decide) (by decide) hfr
  have hr := regs_keep hm hm' [2, 8, 9, 18, 19, 20, 21, 24, 25, 27] (by decide)
  have hs' := os_congr hs hmem hr
  have reg : ∀ (i : Fin 32) (s : Sym), (run0d8_leaves[2]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r1 := reg 1 _ (by decide : (run0d8_leaves[2]!).S.reg 1 = .lit 0x8000010c)
  have r10 := reg 10 _ (by decide : (run0d8_leaves[2]!).S.reg 10 = .ptr 0 192)
  have r11 := (reg 11 _ (by decide : (run0d8_leaves[2]!).S.reg 11 = .init 0 152 8)).trans e152
  have r12 := (reg 12 _ (by decide : (run0d8_leaves[2]!).S.reg 12 = .init 0 160 8)).trans e160
  have r22 := (reg 22 _ (by decide : (run0d8_leaves[2]!).S.reg 22 = .init 0 160 8)).trans e160
  have r23 := (reg 23 _ (by decide : (run0d8_leaves[2]!).S.reg 23 = .init 0 152 8)).trans e152
  have r26 := (reg 26 _ (by decide : (run0d8_leaves[2]!).S.reg 26 = .init 0 176 8)).trans e176
  simp only [Sym.eval, Env.base, envB, entryEnv, shapeOf, List.getD_cons_zero, Sig.sl, w,
    frameBytes] at r1 r10
  rw [show σ.S - 576#64 + BitVec.ofInt 64 192 = σ.sl 0x180 by simp only [Sig.sl, w]; bv_omega]
    at r10
  let k : Kobs := ⟨eh, el, 0, 0, 0, 0, [], 0, 0⟩
  have hsite : Site108 σ m' := ⟨o, k, L, ⟨hs', hd, by omega, r26⟩, r23, r22, r1, fun t ht => by
    simp only [List.length_cons, List.length_nil] at ht
    obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    · exact r10
    · exact r11
    · exact r12⟩
  have hpre2 : F2.Pre m' := f2_pre hs'.1 r10 (by decide) (by decide) (by decide)
    (off := o.h + o.i + eh)
    (by rw [r11]; simp only [curPtr, w]; bv_omega)
    (by rw [r12]; simp only [w, BitVec.toNat_ofNat]; omega)
    (by unfold RetAligned; rw [r1]; decide)
  refine ⟨f2C, (), rfl, hex, hpre2, fun m'' hpost => ⟨cut10c, by simp [TX.plan, vcPlan], rfl,
    ?_, ⟨m', (), hsite, hpost⟩, ?_⟩⟩
  · rw [hpost.1.1.1, r1]; decide
  · have h21 : m''.reg 21 = m.reg 21 := (hpost.1.1.2 21 (by decide)).trans (hr 21 (by decide))
    show F2.bound + (32 * outerLeft m'' + 132) ≤ 32 * outerLeft m + 220 -
      ((run0d8_leaves[2]!).S.steps - SBody.steps)
    rw [hsteps]; unfold outerLeft; rw [h21]; unfold F2.bound; omega

/-! ## `0x8000015c`: the keys list -/

/-- Two frame ranges that do not meet. -/
theorem sl_apart {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {k1 n1 k2 n2 : Nat} {a : Word}
    (hk1 : k1 ≤ stackBytes) (hk2 : k2 ≤ stackBytes) (hd : k1 + n2 ≤ k2 ∨ k2 + n1 ≤ k1)
    (h1 : InRange (σ.sl k1) n1 a) (h2 : InRange (σ.sl k2) n2 a) : False := by
  have e1 := sl_toNat hpre hk1
  have e2 := sl_toNat hpre hk2
  have := (entry_nums hpre).1; unfold Layout.ramLo stackBytes at *
  simp only [InRange] at h1 h2; omega

/-- A leaf over the base regions whose writes lie in the frame bytes `[lo, lo + n)` changes no
other byte. -/
theorem frame_only {σ : Sig} {m m' : Machine} {env : Env} {S S' : SState} (hc : Common σ m)
    (he : BaseEnv σ m env) (hS : S.regions = baseRegions) (hm' : Match env S' m')
    (hS' : S'.regions = baseRegions) (hfr : SameOutside (InWritable env S) m m') {lo n : Nat}
    (hlo : lo + n ≤ 576)
    (hno : S'.mem.all (fun w => w.r == 0 && decide (lo ≤ w.off) &&
      decide (w.off + w.n ≤ lo + n)) = true) :
    SameOutside (InRange (σ.sl (576 - lo)) n) m m' := by
  intro a ha
  by_cases hw : InWritable env S a
  · obtain ⟨r, R, j, hR, -, hj, rfl⟩ := hw
    have hpre := hc.2.1
    have hr5 : r < 5 := by
      have := (List.getElem?_eq_some_iff.mp hR).1; rw [hS] at this
      simpa [baseRegions] using this
    have hj' : j < (envB σ m).size r := by rwa [← he.size]
    refine byte_keep hm' (by rw [hS']; simpa [baseRegions] using hr5) hj (fun w hw => ?_) ?_
    · have := List.all_eq_true.mp hno w hw
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
      obtain ⟨⟨hw0, hl1⟩, hl2⟩ := this
      by_cases h0 : r = 0
      · subst h0
        have hin : ¬ (lo ≤ j ∧ j < lo + n) := fun hjn => ha (by
          have hb : env.base 0 = σ.sl 576 := by rw [he.base]; rfl
          have h1 := sl_toNat hpre (k := 576) (by decide)
          have h2 := sl_toNat hpre (k := 576 - lo) (by unfold stackBytes; omega)
          have hlo' := (entry_nums hpre).1; unfold Layout.ramLo at hlo'
          rw [hb]; simp only [InRange]
          rw [toNat_add_ofNat (by rw [h1]; omega), h1, h2]; omega)
        simp only [Write.covers, hw0, beq_self_eq_true, Bool.true_and, Bool.and_eq_false_iff,
          decide_eq_false_iff_not, Nat.not_le, Nat.not_lt]
        omega
      · have : (w.r == r) = false := by rw [hw0]; simpa using Ne.symm h0
        simp [Write.covers, this]
    · rw [he.mem0, he.base]
      exact mem0_entry (common_present hc r j hr5 hj')
  · exact hfr a hw

/-- A list item, or an item that is not a one-byte string, has a header. -/
theorem dec_hpos {xs : List Byte} {b : Bool} {h q : Nat} (hd : F2.decode xs = .success b h q)
    (hb : b = true ∨ q ≠ 1) : 0 < h := by
  cases xs with
  | nil => simp [F2.decode] at hd
  | cons x rest =>
    simp only [F2.decode, F2.checkedPayload] at hd
    repeat' (split at hd)
    all_goals first
      | (simp at hd; done)
      | (simp only [F2.Item.success.injEq] at hd
         obtain ⟨rfl, rfl, rfl⟩ := hd
         first | omega | simp at hb)

/-- The state after a leaf of `0x8000015c` that accepted the keys list and wrote the empty keys
list header `{1, 0, 0}` at `S-0x118`. -/
theorem after15c {σ : Sig} {m m' : Machine} {S' : SState} (hA : ARet f2C (unit Site158) σ m)
    (h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 288 2) (Sym.lit 0)) = true)
    (h2 : SBool.eval (envB σ m)
      (SBool.ne (Sym.bin BinOp.and (Sym.init 0 272 1) (Sym.lit 1)) (Sym.lit 0)) = true)
    (hm' : Match (envB σ m) S' m') (hS' : S'.regions = baseRegions)
    (hfr : SameOutside (InWritable (envB σ m) SBody) m m')
    (hno : S'.mem.all (fun w => w.r == 0 && decide (296 ≤ w.off) &&
      decide (w.off + w.n ≤ 296 + 24)) = true)
    (hsave : S'.mem.all (fun w => w.r != 0 || decide (w.off + w.n ≤ 472)) = true)
    (hr : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 25, 26, 27] : List (Fin 32)),
      S'.reg i.val = SBody.reg i.val)
    (hw0 : readConst S' 0 296 8 = .var 25) (hw8 : readConst S' 0 304 8 = .lit 0)
    (hw16 : readConst S' 0 312 8 = .lit 0) :
    ∃ o k L, InEntry σ m' o k L ∧ KeysWalked (kpl σ o k) 0 [] ∧ KList σ m' k 0 ∧
      k.j = 0 ∧ k.keys = [] ∧ k.kq = 1 ∧ k.kc = 0 ∧
      (Sym.init 0 256 8).eval (envB σ m) = keyPtr σ o k ∧
      (Sym.init 0 264 8).eval (envB σ m) = w k.kl ∧ k.kl ≤ σ.len ∧
      23 + k.kl ≤ k.eh + k.el ∧ k.eh + k.el ≤ o.p - o.i ∧ o.p ≤ σ.len ∧
      m.reg 21 = w (o.p - o.i) ∧ m.reg 26 = w (k.eh + k.el) ∧
      (∀ i ∈ ([21, 26] : List (Fin 32)), m'.reg i = m.reg i) := by
  obtain ⟨hcm, o, k, L, ⟨hs, hd, hle, r26⟩, ⟨had, hal, hab⟩, before, hb⟩ := ret15c hA
  have hpre := hcm.2.1
  simp only [SBool.eval] at h1 h2
  replace h2 : ((Sym.init 0 272 1).eval (envB σ m) &&& 1#64 != 0#64) = true := h2
  rw [show (288 : Nat) = frameBytes - 0x140 + 32 from rfl,
    slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide)] at h1
  rw [show (272 : Nat) = frameBytes - 0x140 + 16 from rfl,
    slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide)] at h2
  obtain ⟨b, kh, kl, hdk, hl⟩ := dec_ok (by simpa [Sym.eval] using h1)
  rw [hl] at h2
  cases b
  · simp at h2
  have e256 : (Sym.init 0 256 8).eval (envB σ m) = aftPtr σ o k + w kh := by
    rw [show (256 : Nat) = frameBytes - 0x140 + 0 from rfl,
      slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide), dec_ptr hdk]
  have e264 : (Sym.init 0 264 8).eval (envB σ m) = w kl := by
    rw [show (264 : Nat) = frameBytes - 0x140 + 8 from rfl,
      slot_val (BaseEnv.ofB σ m) hpre (by decide) (by decide) hb (by decide), dec_len hdk]
  -- the entry's calls fit
  have hok := hs.2.1
  have hi := hs.2.2.1.2.2.1
  have hne := win_ne hok hi hpre
  have hwf0 : WalkFits (win σ o) := hok.2.2.2.2.2.2
  have hef : ∀ c ∈ (entryWalk (ent σ o k)).1, HeaderFits c.2 := walkFits_entry hwf0 hne hd
  have hdk' : F2.decode (itemRest (ent σ o k) k.ah 20) = .success true kh kl := hdk
  have hkf : HeaderFits (aft σ o k) := hef _ (by
    simp only [entryWalk, had, hdk', if_true, List.mem_cons]; exact .inr (.inl rfl))
  have hkp : ∀ c ∈ (keysWalk (itemPayload (aft σ o k) kh kl).length
      (itemPayload (aft σ o k) kh kl)).1, HeaderFits c.2 := fun c hc => hef c (by
    simp only [entryWalk, had, hdk', if_true, List.mem_cons]; exact .inr (.inr hc))
  obtain ⟨-, hkb, -⟩ := fits_bounds hkf hdk
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hpl := hok.2.1
  rw [aft_eq σ o k hle hal (by omega)] at hkb
  simp only [List.length_take, List.length_drop] at hkb
  have hil : σ.input.length = σ.len := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have heh := dec_hpos hd (.inl rfl)
  have hah := dec_hpos had (.inr (by decide))
  have hkh := dec_hpos hdk (.inl rfl)
  -- the machine after the leaf: only the keys list header changed
  obtain ⟨hwf, hm, -⟩ := body_cut hcm
  have hso := frame_only hcm (BaseEnv.ofB σ m) rfl hm' hS' hfr (lo := 296) (n := 24) (by decide) hno
  have hreg := regs_keep hm hm' _ hr
  obtain ⟨hc', hlive', -⟩ := base_leaf hcm hs.2.2.2.2.2 (BaseEnv.ofB σ m) hwf rfl hm' hS' hfr
    hsave (fun i hi => hreg i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega))
  have hRst : ∀ a, InRange (σ.sl (576 - 296)) 24 a → InRange (σ.sl stackBytes) stackBytes a :=
    fun a h => sl_in_stack hpre (by decide) (by decide) h
  have hwf' : Env.WF (envB σ m) S' := hwf.congr (by rw [hS']; rfl)
  have fw := fun kk hk hk' => frame_word (BaseEnv.ofB σ m) hwf' hm' hS' (k := kk) hk hk'
  have f0 := fw 0x118 (by decide) (by decide)
  have f8 := fw 0x110 (by decide) (by decide)
  have f16 := fw 0x108 (by decide) (by decide)
  rw [show 576 - 0x118 = 296 from rfl, hw0] at f0
  rw [show 576 - 0x110 = 304 from rfl, hw8] at f8
  rw [show 576 - 0x108 = 312 from rfl, hw16] at f16
  have r25 : m.reg 25 = 1 := hs.2.2.2.1.2.1
  let k' : Kobs := { k with kh := kh, kl := kl, j := 0, keys := [], kq := 1, kc := 0 }
  refine ⟨o, k', L, ⟨hc', outerOk_keep hpre hso (fun a h => .inl (hRst a h)) hok,
      ⟨(hreg 20 (by decide)).trans hs.2.2.1.1, (hreg 21 (by decide)).trans hs.2.2.1.2.1, hi,
        frame_keep hpre hso (k := 0x1f0) (by decide) (by decide)
          (fun a h hin => sl_apart hpre (by decide) (by decide) (by decide) h hin)
          hs.2.2.1.2.2.2⟩,
      elist_keep hpre hs.2.2.2.2.1 hs.2.2.2.2.2 (fun b hb => hb) hso hRst
        (fun x h hin => sl_apart hpre (by decide) (by decide) (by decide) h hin),
      by simpa [KX, k'] using hlive', ⟨hd, hle, (hreg 26 (by decide)).trans r26⟩,
      ⟨had, hal, bytes_congr hab fun t ht => hso _ fun hin => sl_apart hpre (k1 := 576 - 296)
        (n1 := 24) (k2 := 0x158) (n2 := 20) (by decide) (by decide) (by decide) hin
        (in_self (by have := sl_toNat hpre (k := 0x158) (by decide)
                     have := (entry_nums hpre).2.1; unfold Layout.ramHi at this; omega)
          (by simp only [itemPayload, List.length_take] at ht; omega))⟩,
      ⟨hdk, show k.ah + 20 + kh + kl ≤ k.el by omega⟩, (hreg 27 (by decide)).trans hs.2.2.2.1.2.2⟩,
    ⟨Nat.zero_le _, by simp, hkp⟩,
    ⟨⟨f0.trans (by rw [show (Sym.var 25).eval (envB σ m) = m.reg 25 from rfl, r25]),
      by rw [show σ.sl 0x118 + 8 = σ.sl 0x110 by simp only [Sig.sl, w]; bv_omega, f8]; rfl,
      by rw [show σ.sl 0x118 + 16 = σ.sl 0x108 by simp only [Sig.sl, w]; bv_omega, f16]; rfl⟩,
      Nat.zero_le _, by show 0 < (1 : Word).toNat; decide, fun _ => rfl,
      by show (0 : Word).toNat < 2 ^ 32; decide,
      fun h => absurd h (by show ¬ 0 < (0 : Word).toNat; decide),
      fun y hy => absurd hy List.not_mem_nil,
      fun i hi => absurd hi (by show ¬ i < ([] : List (List Byte)).flatten.length; simp)⟩,
    rfl, rfl, rfl, rfl,
    by rw [e256]; show aftPtr σ o k + w kh = aftPtr σ o k + w kh + w 0; simp [w], e264,
    show kl ≤ σ.len by omega, show 23 + kl ≤ k.eh + k.el by omega,
    hle, by omega, hs.2.2.1.2.1, r26,
    fun i hi => hreg i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega)⟩

theorem TX.leaf_8000015c_3 :
    LeafGoal TX.plan TX.plan.cuts[5]! ((TX.plan.leaves 0x8000015c)[3]!) := by
  show LeafGoal TX.plan cut15c (run15c_leaves[3]!)
  have hcs : (run15c_leaves[3]!).conds = [SBool.eq (Sym.init 0 288 2) (Sym.lit 0),
      SBool.ne (Sym.bin BinOp.and (Sym.init 0 272 1) (Sym.lit 1)) (Sym.lit 0),
      SBool.ne (Sym.init 0 264 8) (Sym.lit 0)] := by decide
  have hsteps : (run15c_leaves[3]!).S.steps - SBody.steps = 12 := by decide
  intro σ m hA hc
  have hA' : ARet f2C (unit Site158) σ m := hA
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 288 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envB σ m)
      (SBool.ne (Sym.bin BinOp.and (Sym.init 0 272 1) (Sym.lit 1)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h3 : SBool.eval (envB σ m) (SBool.ne (Sym.init 0 264 8) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  refine ⟨nil_obligs (by decide), ?_, ?_⟩
  · show (run15c_leaves[3]!).S.steps - SBody.steps ≤ 32 * outerLeft m + 37
    rw [hsteps]; omega
  intro m' hm' hex hfr
  have hx : (run15c_leaves[3]!).exit = .at 0x8000018c := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x8000018c at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SBody) m m' at hfr
  obtain ⟨o, k, L, hie, hkw, hkl, hj0, hk0, -, -, e256, e264, hkll, h23, hee, hpl, r21, r26, hr⟩ :=
    after15c hA' h1 h2 hm' (by decide) hfr (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  simp only [SBool.eval, e264] at h3
  have hkpos : 0 < k.kl := by
    rcases Nat.eq_zero_or_pos k.kl with h0 | h0
    · rw [h0] at h3; simp [w, Sym.eval] at h3
    · exact h0
  have reg : ∀ (i : Fin 32) (s : Sym), (run15c_leaves[3]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r22 := (reg 22 _ (by decide : (run15c_leaves[3]!).S.reg 22 = .init 0 264 8)).trans e264
  have r23 := (reg 23 _ (by decide : (run15c_leaves[3]!).S.reg 23 = .init 0 256 8)).trans e256
  have r24 := reg 24 _ (by decide : (run15c_leaves[3]!).S.reg 24 = .lit 0)
  have hko : KeysOk σ m' o k := ⟨by rw [hj0, hk0]; exact hkw, r23,
    by rw [r22, hj0, Nat.sub_zero], by rw [r24, hk0]; rfl⟩
  refine ExitGoal.at_cut rfl ⟨cut18c, by simp [TX.plan, vcPlan], hex, ⟨hex, o, k, L, hie, hko,
    by rw [hk0]; exact hkl, by omega⟩, ?_⟩
  show bKeys m' ≤ 32 * outerLeft m + 37 - ((run15c_leaves[3]!).S.steps - SBody.steps)
  rw [hsteps]; unfold bKeys afterEntry keysLeft outerLeft
  rw [hr 21 (by decide), hr 26 (by decide), r22, r21, r26]
  simp only [w, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem TX.leaf_8000015c_2 :
    LeafGoal TX.plan TX.plan.cuts[5]! ((TX.plan.leaves 0x8000015c)[2]!) := by
  show LeafGoal TX.plan cut15c (run15c_leaves[2]!)
  have hcs : (run15c_leaves[2]!).conds = [SBool.eq (Sym.init 0 288 2) (Sym.lit 0),
      SBool.ne (Sym.bin BinOp.and (Sym.init 0 272 1) (Sym.lit 1)) (Sym.lit 0),
      SBool.eq (Sym.init 0 264 8) (Sym.lit 0)] := by decide
  have hsteps : (run15c_leaves[2]!).S.steps - SBody.steps = 16 := by decide
  intro σ m hA hc
  have hA' : ARet f2C (unit Site158) σ m := hA
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 288 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envB σ m)
      (SBool.ne (Sym.bin BinOp.and (Sym.init 0 272 1) (Sym.lit 1)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h3 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 264 8) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  refine ⟨nil_obligs (by decide), ?_, ?_⟩
  · show (run15c_leaves[2]!).S.steps - SBody.steps ≤ 32 * outerLeft m + 37
    rw [hsteps]; omega
  intro m' hm' hex hfr
  have hx : (run15c_leaves[2]!).exit = .call 0x800d677c 0x8000025c := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x800d677c at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SBody) m m' at hfr
  obtain ⟨o, k, L, hie, hkw, hkl, hj0, hk0, hq1, hc0, -, e264, hkll, h23, hee, hpl, r21, r26,
    hr⟩ := after15c hA' h1 h2 hm' (by decide) hfr (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  simp only [SBool.eval, e264] at h3
  have hkz : k.kl = 0 := by
    have := congrArg BitVec.toNat (beq_iff_eq.mp h3)
    simp only [w, Sym.eval, BitVec.toNat_ofNat] at this
    omega
  have reg : ∀ (i : Fin 32) (s : Sym), (run15c_leaves[2]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r1 := reg 1 _ (by decide : (run15c_leaves[2]!).S.reg 1 = .lit 0x8000025c)
  have r10 := reg 10 _ (by decide : (run15c_leaves[2]!).S.reg 10 = .ptr 0 392)
  have r11 := reg 11 _ (by decide : (run15c_leaves[2]!).S.reg 11 = .ptr 0 296)
  have r12 := reg 12 _ (by decide : (run15c_leaves[2]!).S.reg 12 = .ptr 3 0)
  simp only [Sym.eval, Env.base, envB, entryEnv, shapeOf, List.getD_cons_zero,
    List.getD_cons_succ, Sig.sl, w, frameBytes] at r1 r10 r11 r12
  rw [show σ.S - 576#64 + BitVec.ofInt 64 392 = σ.sl 0xb8 by simp only [Sig.sl, w]; bv_omega]
    at r10
  rw [show σ.S - 576#64 + BitVec.ofInt 64 296 = σ.sl 0x118 by simp only [Sig.sl, w]; bv_omega]
    at r11
  rw [BitVec.ofInt_ofNat, BitVec.add_zero] at r12
  have hsite : Site258 σ (L, k.keys.flatten) m' := ⟨o, k, hie, rfl,
    by rw [hkz, hk0]; exact hkw, by rw [hk0]; exact hkl, r1, fun t ht => by
      simp only [List.length_cons, List.length_nil] at ht
      obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
      · exact r10
      · exact r11
      · exact r12⟩
  obtain ⟨hH, -, hq0, -, -, -, -, hkb⟩ := hkl
  have hpre4 : F4.Pre σ.A L k.keys.flatten m' := towned_pre (eb := 32) hie.1 hie.2.2.2.2.1 r10
    r11 r12 (by unfold RetAligned; rw [r1]; decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hH
    (by rw [hc0]; simp) (by rw [hk0]; simp) hq0
    (fun h => absurd h (by rw [hc0]; decide)) hkb
  refine ⟨f4C, (L, k.keys.flatten), rfl, hex, hpre4, fun m'' hpost => ⟨cut25c,
    by simp [TX.plan, vcPlan], rfl, ?_, ⟨m', (L, k.keys.flatten), hsite, hpost⟩, ?_⟩⟩
  · rw [hpost.1.1.1, r1]; decide
  · have h21 : m''.reg 21 = m.reg 21 :=
      (hpost.1.1.2 21 (by decide)).trans (hr 21 (by decide))
    have h26 : m''.reg 26 = m.reg 26 :=
      (hpost.1.1.2 26 (by decide)).trans (hr 26 (by decide))
    show F4.bound + bTail m'' 539 ≤ 32 * outerLeft m + 37 -
      ((run15c_leaves[2]!).S.steps - SBody.steps)
    rw [hsteps]; unfold bTail afterEntry outerLeft F4.bound
    rw [h21, h26, r21, r26]
    simp only [w, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

end ZesuExec.Fn.TX
