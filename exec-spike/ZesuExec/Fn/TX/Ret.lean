import ZesuExec.Fn.TX.Vc

/-!
# TX: cut lemmas of the call return sites after `ensureTotalCapacity`, `toOwnedSlice`, the
allocator calls and `memcpy`, and of the two store sites (programme plan S6 step 6)
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## What a callee may change, seen from `Common` -/

/-- Memory a callee may change: TX's own or the allocator's, never the save area. -/
abbrev CallR (σ : Sig) (a : Word) : Prop :=
  (Owned σ a ∨ σ.A.Priv σ.g.L a) ∧ ¬ InRange (σ.sl 104) 104 a

theorem save_in_stack {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {a : Word}
    (h : InRange (σ.sl 104) 104 a) : InRange (σ.sl stackBytes) stackBytes a := by
  have h1 := sl_toNat hpre (k := 104) (by decide)
  have h2 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have := (entry_nums hpre).1
  simp only [InRange, h1, h2] at h ⊢
  unfold stackBytes Layout.ramLo at *; omega

theorem priv_R {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {a : Word} (h : σ.A.Priv σ.g.L a) :
    CallR σ a :=
  ⟨.inr h, fun hs => owned_not_priv hpre (.inr (.inr (.inl (save_in_stack hpre hs)))) h⟩

theorem stack_R {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {k n : Nat} {a : Word} (hk : k ≤ stackBytes)
    (hn : n + 104 ≤ k) (h : InRange (σ.sl k) n a) : CallR σ a := by
  have h1 := sl_toNat hpre (k := 104) (by decide)
  have h2 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have h3 := sl_toNat hpre (k := k) hk
  have := (entry_nums hpre).1
  refine ⟨.inl (.inr (.inr (.inl ?_))), ?_⟩ <;> simp only [InRange, h1, h2, h3] at h ⊢ <;>
    unfold stackBytes Layout.ramLo at * <;> omega

theorem scratch_R {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {a : Word} (h : InRange scratch 8 a) :
    CallR σ a := by
  refine ⟨.inl (.inr (.inr (.inr h))), fun hs => ?_⟩
  have hs' := save_in_stack hpre hs
  have h2 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have d15 : Apart scratch 8 (σ.sl stackBytes) stackBytes := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at d15
  simp only [InRange] at h hs'
  rw [h2] at hs' d15
  simp only [scratch, Layout.extraParams, BitVec.toNat_ofNat] at h d15
  unfold stackBytes at *
  omega

/-- A block of TX's live list outside `g.L`. -/
theorem X_R {σ : Sig} {m : Machine} {L X : List (Word × Nat)} (hpre : Pre σ.A σ.g σ.m)
    (hlive : Live σ m L X) {b : Word × Nat} (hb : b ∈ X) {a : Word} (h : InRange b.1 b.2 a) :
    CallR σ a :=
  priv_R hpre ((hlive.2.2 b hb).2.2 a h)

theorem live_R {σ : Sig} {m : Machine} {L X : List (Word × Nat)} (hpre : Pre σ.A σ.g σ.m)
    (hlive : Live σ m L X) {a : Word} (h : σ.A.Priv L a) : CallR σ a :=
  priv_R hpre (priv_sub hpre hlive h)

theorem sp_sub {σ : Sig} {m : Machine} (hc : Common σ m) (k : Nat) :
    m.reg 2 - BitVec.ofNat 64 k = σ.sl (576 + k) := by
  rw [hc.2.2.2.1]; simp only [Sig.sl, w, frameBytes]; bv_omega

theorem f1w {m : Machine} {a v : Word} (h : m.load a 8 = some v) : F1.wordAt m a = v := by
  simp [F1.wordAt, h]

theorem f4w {m : Machine} {a v : Word} (h : m.load a 8 = some v) : ToOwned.wordAt m a = v := by
  simp [ToOwned.wordAt, h]

theorem txw {m : Machine} {a v : Word} (h : m.load a 8 = some v) : wordAt m a = v := by
  simp [wordAt, h]

/-! ## The frame spill of the vtable word -/

theorem spill_known {σ : Sig} {m : Machine} (h : m.load (σ.sl 0x220) 8 = some (w vtable)) :
    ∀ t < 8, (envB σ m).byte0 0 (fo 0x220 + t) = byteOf ((Sym.lit vtable).eval (envB σ m)) t := by
  intro t ht
  have := load_bytes h (Nat.le_refl _) t ht
  have ha : ((shapeOf σ).getD 0 (0, 0)).fst + BitVec.ofNat 64 (fo 0x220 + t) =
      σ.sl 0x220 + BitVec.ofNat 64 t := by
    simp only [shapeOf, List.getD_cons_zero, fo, Sig.sl, w]; unfold frameBytes; bv_omega
  simp only [Env.byte0, envB, entryEnv]
  rw [ha, this]; rfl

theorem spill_cut {σ : Sig} {m : Machine} (hc : Common σ m)
    (h : m.load (σ.sl 0x220) 8 = some (w vtable)) :
    Env.WF (envB σ m) SSpill ∧ Match (envB σ m) SSpill m ∧ RodataLoaded zesuImage m :=
  body_ok hc (ovBody_ok hc) (ks := [vtableKnown, vtableSpill]) (by
    intro k hk t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact common_known_vtable hc t ht
    · exact spill_known h t ht)

/-! ## Return sites -/

/-- `Common` and the pc after `ensureTotalCapacity` returns to `0x800001f8`. -/
theorem ret_1f8 {σ : Sig} {m : Machine} (h : ARet f1C Site1f4 σ m) :
    Common σ m ∧ m.pc.toNat = c1f8 := by
  obtain ⟨mc, x, ⟨o, k, kh', hIE, -, -, hKL, -, -, ha⟩, ⟨hret, hso, -⟩, hp⟩ := h
  have hc := hIE.1
  have hpre := hc.2.1
  have hlive := hIE.2.2.2.2.1
  have hhdr : mc.reg 10 = σ.sl 0x118 := ha.arg 0 (by simp)
  obtain ⟨⟨hH0, -, hH16⟩, -⟩ := hKL
  have hm : Common σ m := common_ret hc hret hp hso fun a h => by
    rw [hhdr, show mc.reg 2 - 128 = σ.sl 704 from sp_sub hc 128] at h
    rcases h with h | h | h | h | ⟨hc0, h⟩
    · exact stack_R hpre (by decide) (by decide) h
    · exact stack_R hpre (by decide) (by decide) h
    · exact scratch_R hpre h
    · exact live_R hpre hlive h
    · rw [f1w hH16] at hc0 h
      rw [f1w hH0] at h
      refine X_R hpre hlive (b := (k.kq, keySize * k.kc.toNat)) ?_ ?_
      · simp [EX, KX, hc0]
      · simpa [Nat.mul_comm, keySize, F1.elemBytes] using h
  exact ⟨hm, ret_pc hret ha.1 (by decide)⟩

theorem TX.cut_800001f8 : CutOK TX.plan TX.plan.cuts[8]! := by
  show CutOK TX.plan cut1f8
  intro σ m h
  obtain ⟨hm, hpc⟩ := ret_1f8 h
  exact ⟨(body_cut hm).1, (body_cut hm).2.1, (body_cut hm).2.2, hpc⟩

theorem stack_not_priv {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {a : Word}
    (h : InRange (σ.sl stackBytes) stackBytes a) : ¬ σ.A.Priv σ.g.L a :=
  owned_not_priv hpre (.inr (.inr (.inl h)))

theorem sl_in_stack {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {k n : Nat} {a : Word}
    (hk : k ≤ stackBytes) (hn : n ≤ k) (h : InRange (σ.sl k) n a) :
    InRange (σ.sl stackBytes) stackBytes a := by
  have h2 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have h3 := sl_toNat hpre (k := k) hk
  have := (entry_nums hpre).1
  simp only [InRange, h2, h3] at h ⊢
  unfold stackBytes Layout.ramLo at *; omega

theorem scratch_not_stack {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {a : Word}
    (h : InRange scratch 8 a) : ¬ InRange (σ.sl stackBytes) stackBytes a := fun hs => by
  have h2 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have d15 : Apart scratch 8 (σ.sl stackBytes) stackBytes := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at d15
  simp only [InRange] at h hs
  rw [h2] at hs d15
  simp only [scratch, Layout.extraParams, BitVec.toNat_ofNat] at h d15
  unfold stackBytes at *
  omega

/-- A frame word survives a call whose frame `R` misses it. -/
theorem frame_keep {σ : Sig} {mc m : Machine} (hpre : Pre σ.A σ.g σ.m) {R : Word → Prop}
    (hso : SameOutside R mc m) {k : Nat} (hk : k ≤ 576) (hk' : 8 ≤ k)
    (hR : ∀ a, R a → InRange (σ.sl k) 8 a → False) {v : Word}
    (h : mc.load (σ.sl k) 8 = some v) : m.load (σ.sl k) 8 = some v := by
  rw [load_congr (m := mc) fun t ht => hso _ fun hr => hR _ hr ?_]; exact h
  have h3 := sl_toNat hpre (k := k) (by unfold stackBytes; omega)
  have := (entry_nums hpre).1
  simp only [InRange, h3]
  rw [toNat_add_ofNat (by unfold Layout.ramLo at this; omega), h3]; omega

/-- Outside the stack: the allocator's memory or the scratch word. -/
theorem frame_keep' {σ : Sig} {mc m : Machine} (hpre : Pre σ.A σ.g σ.m) {R : Word → Prop}
    (hso : SameOutside R mc m) {k : Nat} (hk : k ≤ 576) (hk' : 8 ≤ k)
    (hR : ∀ a, R a → σ.A.Priv σ.g.L a ∨ InRange scratch 8 a) {v : Word}
    (h : mc.load (σ.sl k) 8 = some v) : m.load (σ.sl k) 8 = some v :=
  frame_keep hpre hso hk hk' (fun a hr hin => by
    have hs := sl_in_stack hpre (by unfold stackBytes; omega) hk' hin
    rcases hR a hr with h | h
    · exact stack_not_priv hpre hs h
    · exact scratch_not_stack hpre h hs) h

theorem ret_25c {σ : Sig} {m : Machine} (h : ARet f4C Site258 σ m) :
    Common σ m ∧ m.pc.toNat = c25c := by
  obtain ⟨mc, x, ⟨o, k, hIE, -, -, hKL, ha⟩, ⟨hret, hso, -⟩, hp⟩ := h
  have hc := hIE.1
  have hpre := hc.2.1
  have hlive := hIE.2.2.2.2.1
  have hres : mc.reg 10 = σ.sl 0xb8 := ha.arg 0 (by simp)
  have hhdr : mc.reg 11 = σ.sl 0x118 := ha.arg 1 (by simp)
  obtain ⟨⟨hH0, -, hH16⟩, -⟩ := hKL
  have hm : Common σ m := common_ret hc hret hp hso fun a h => by
    simp only [ToOwned.listPtr, ToOwned.listCap, hhdr, hres, f4w hH0, f4w hH16,
      show mc.reg 2 - 112 = σ.sl 688 from sp_sub hc 112] at h
    rcases h with h | h | h | h | h | ⟨hc0, h⟩
    · exact stack_R hpre (by decide) (by decide) h
    · exact stack_R hpre (by decide) (by decide) h
    · exact stack_R hpre (by decide) (by decide) h
    · exact scratch_R hpre h
    · exact live_R hpre hlive h
    · refine X_R hpre hlive (b := (k.kq, keySize * k.kc.toNat)) ?_ ?_
      · simp [EX, KX, hc0]
      · simpa [Nat.mul_comm, keySize, F4.elemBytes] using h
  exact ⟨hm, ret_pc hret ha.1 (by decide)⟩

theorem TX.cut_8000025c : CutOK TX.plan TX.plan.cuts[10]! := by
  show CutOK TX.plan cut25c
  intro σ m h
  obtain ⟨hm, hpc⟩ := ret_25c h
  exact ⟨(body_cut hm).1, (body_cut hm).2.1, (body_cut hm).2.2, hpc⟩

theorem ret_4a0 {σ : Sig} {m : Machine} (h : ARet f5C Site49c σ m) :
    Common σ m ∧ m.pc.toNat = c4a0 := by
  obtain ⟨mc, x, ⟨o, hc, -, -, hEL, hlive, -, ha⟩, ⟨hret, hso, -⟩, hp⟩ := h
  have hpre := hc.2.1
  have hres : mc.reg 10 = σ.sl 0x88 := ha.arg 0 (by simp)
  have hhdr : mc.reg 11 = σ.sl 0x1c0 := ha.arg 1 (by simp)
  obtain ⟨⟨hH0, -, hH16⟩, -⟩ := hEL
  have hm : Common σ m := common_ret hc hret hp hso fun a h => by
    simp only [ToOwned.listPtr, ToOwned.listCap, hhdr, hres, f4w hH0, f4w hH16,
      show mc.reg 2 - 112 = σ.sl 688 from sp_sub hc 112] at h
    rcases h with h | h | h | h | h | ⟨hc0, h⟩
    · exact stack_R hpre (by decide) (by decide) h
    · exact stack_R hpre (by decide) (by decide) h
    · exact stack_R hpre (by decide) (by decide) h
    · exact scratch_R hpre h
    · exact live_R hpre hlive h
    · refine X_R hpre hlive (b := (o.ep, entrySize * o.ec.toNat)) ?_ ?_
      · simp [EX, hc0]
      · simpa [Nat.mul_comm, entrySize, F5.elemBytes] using h
  exact ⟨hm, ret_pc hret ha.1 (by decide)⟩

theorem TX.cut_800004a0 : CutOK TX.plan TX.plan.cuts[16]! := by
  show CutOK TX.plan cut4a0
  intro σ m h
  obtain ⟨hm, hpc⟩ := ret_4a0 h
  exact ⟨(body_cut hm).1, (body_cut hm).2.1, (body_cut hm).2.2, hpc⟩

theorem ret_340 {σ : Sig} {m : Machine} (h : ARet remapC (unit Site33c) σ m) :
    Common σ m ∧ m.pc.toNat = c340 ∧ m.load (σ.sl 0x220) 8 = some (w vtable) := by
  obtain ⟨mc, _, ⟨o, k, L, kp', hED, hG, -, -, -, -, -, -, ha⟩, ⟨hret, -, hso⟩, hp⟩ := h
  have hc := hED.1
  have hpre := hc.2.1
  have hR : ∀ a, InRange (mc.reg 2 - 16) 16 a → CallR σ a := fun a h => by
    rw [show mc.reg 2 - 16 = σ.sl 592 from sp_sub hc 16] at h
    exact stack_R hpre (by decide) (by decide) h
  have hm : Common σ m := common_ret hc hret hp hso hR
  have hsp : m.load (σ.sl 0x220) 8 = some (w vtable) :=
    frame_keep hpre hso (by decide) (by decide) (fun a h hin => by
      rw [show mc.reg 2 - 16 = σ.sl 592 from sp_sub hc 16] at h
      have h1 := sl_toNat hpre (k := 592) (by decide)
      have h2 := sl_toNat hpre (k := 0x220) (by decide)
      have := (entry_nums hpre).1; unfold Layout.ramLo at this
      simp only [InRange, h1, h2] at h hin; omega) hG.2.2.2.2.2.2.2.2.2
  exact ⟨hm, ret_pc hret ha.1 (by decide), hsp⟩

theorem TX.cut_80000340 : CutOK TX.plan TX.plan.cuts[11]! := by
  show CutOK TX.plan cut340
  intro σ m h
  obtain ⟨hm, hpc, hsp⟩ := ret_340 h
  obtain ⟨h1, h2, h3⟩ := spill_cut hm hsp
  exact ⟨h1, h2, h3, hpc⟩

theorem ret_3d4 {σ : Sig} {m : Machine} {L : List (Word × Nat)}
    (h : ∃ mc, Site3d0 σ L mc ∧ allocC.Post σ L mc m) : Common σ m ∧ m.pc.toNat = c3d4 := by
  obtain ⟨mc, ⟨o, k, kp', hED, -, -, ha⟩, ⟨hret, hso, -⟩, hp⟩ := h
  have hc := hED.1
  have hpre := hc.2.1
  have hm : Common σ m := common_ret hc hret hp hso fun a h => by
    rcases h with h | h
    · exact live_R hpre hED.2.2.2.2.1 h
    · rw [show mc.reg 2 - 16 = σ.sl 592 from sp_sub hc 16] at h
      exact stack_R hpre (by decide) (by decide) h
  exact ⟨hm, ret_pc hret ha.1 (by decide)⟩

theorem TX.cut_800003d4 : CutOK TX.plan TX.plan.cuts[12]! := by
  show CutOK TX.plan cut3d4
  rintro σ m ⟨mc, L, hs, hpost⟩
  obtain ⟨hm, hpc⟩ := ret_3d4 ⟨mc, hs, hpost⟩
  exact ⟨(body_cut hm).1, (body_cut hm).2.1, (body_cut hm).2.2, hpc⟩

theorem grownCap_ge (n : Nat) : n ≤ grownCap n := by unfold grownCap; omega

theorem ret_400 {σ : Sig} {m : Machine} (h : ARet memcpyC (unit Site3fc) σ m) :
    Common σ m ∧ m.pc.toNat = c400 ∧ m.load (σ.sl 0x220) 8 = some (w vtable) := by
  obtain ⟨mc, _, ⟨o, k, L, kp', p'', hAl, ha⟩, hmc, hp⟩ := h
  have hc := hAl.1.1
  have hpre := hc.2.1
  have hlive := hAl.1.2.2.2.2.1
  have hEL := hAl.1.2.2.2.1
  have hdst : mc.reg 10 = p'' := ha.arg 0 (by simp)
  have hn : mc.reg 12 = w (entrySize * o.done.length) := ha.arg 2 (by simp)
  have hlen : (mc.reg 12).toNat = entrySize * o.done.length := by
    rw [hn]; have := hEL.2.1; have := hEL.2.2.2.2.1
    simp only [w, BitVec.toNat_ofNat, entrySize]; omega
  have hret : Returns mc m := by
    rw [memcpy_eq hmc]; exact ⟨rfl, fun i _ => rfl⟩
  have hso : SameOutside (fun a => InRange (mc.reg 10) (mc.reg 12).toNat a ∨ InRange scratch 8 a)
      mc m := fun a ha => memcpy_out hmc (fun h => ha (.inl h)) (fun h => ha (.inr h))
  have hRp : ∀ a, InRange (mc.reg 10) (mc.reg 12).toNat a → σ.A.Priv σ.g.L a := fun a h => by
    rw [hdst, hlen] at h
    refine (hlive.2.2 (p'', entrySize * grownCap o.done.length) (by simp)).2.2 a ?_
    have := grownCap_ge o.done.length
    simp only [InRange] at h ⊢
    have : entrySize * o.done.length ≤ entrySize * grownCap o.done.length :=
      Nat.mul_le_mul_left _ this
    omega
  have hm : Common σ m := common_ret hc hret hp hso fun a h => by
    rcases h with h | h
    · exact priv_R hpre (hRp a h)
    · exact scratch_R hpre h
  have hsp : m.load (σ.sl 0x220) 8 = some (w vtable) :=
    frame_keep' hpre hso (by decide) (by decide) (fun a h => h.imp (hRp a) id)
      hAl.2.1.2.2.2.2.2.2.2.2.2
  exact ⟨hm, ret_pc hret ha.1 (by decide), hsp⟩

theorem TX.cut_80000400 : CutOK TX.plan TX.plan.cuts[13]! := by
  show CutOK TX.plan cut400
  intro σ m h
  obtain ⟨hm, hpc, hsp⟩ := ret_400 h
  obtain ⟨h1, h2, h3⟩ := spill_cut hm hsp
  exact ⟨h1, h2, h3, hpc⟩

theorem ret_42c {σ : Sig} {m : Machine} (h : A42c σ m) : Common σ m ∧ m.pc.toNat = c42c := by
  rcases h with ⟨hpc, o, k, L, kp', p'', hcop, -⟩ |
    ⟨mc, L, ⟨o, k, kp', p'', hcop, hec, ha⟩, ⟨hret, hso, -, -⟩, hp⟩
  · exact ⟨hcop.1.1.1, hpc⟩
  · have hc := hcop.1.1.1
    have hpre := hc.2.1
    have hlive := hcop.1.1.2.2.2.2.1
    have hEL := hcop.1.1.2.2.2.1
    have h11 : mc.reg 11 = o.ep := ha.arg 1 (by simp)
    have h12 : mc.reg 12 = w (entrySize * o.ec.toNat) := ha.arg 2 (by simp)
    have hlen : (mc.reg 12).toNat = entrySize * o.ec.toNat := by
      rw [h12]; have := hEL.2.2.2.2.1
      simp only [w, BitVec.toNat_ofNat, entrySize]; omega
    have hm : Common σ m := common_ret hc hret hp hso fun a h => by
      rcases h with h | h | h
      · exact live_R hpre hlive h
      · rw [h11, hlen] at h
        exact X_R hpre hlive (b := (o.ep, entrySize * o.ec.toNat)) (by simp [EX, hec]) h
      · rw [show mc.reg 2 - 16 = σ.sl 592 from sp_sub hc 16] at h
        exact stack_R hpre (by decide) (by decide) h
    exact ⟨hm, ret_pc hret ha.1 (by decide)⟩

theorem TX.cut_8000042c : CutOK TX.plan TX.plan.cuts[14]! := by
  show CutOK TX.plan cut42c
  intro σ m h
  obtain ⟨hm, hpc⟩ := ret_42c h
  exact ⟨(body_cut hm).1, (body_cut hm).2.1, (body_cut hm).2.2, hpc⟩

end ZesuExec.Fn.TX
