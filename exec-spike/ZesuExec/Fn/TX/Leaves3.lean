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

end ZesuExec.Fn.TX
