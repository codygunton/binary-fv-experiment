import ZesuExec.Fn.TX.Cuts
import ZesuExec.Fn.F1.Vc

/-!
# TX: the cut lemmas and leaves `zesu_auto` left open, by hand (programme plan S6 step 6)
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## The entry's shape -/

/-- The regions of `shapeOf` with their executor view. -/
def shapeFull (σ : Sig) : Shape :=
  [((σ.sl frameBytes, frameBytes), frameR), ((σ.res, 24), resR), ((σ.rest, 16), restR),
    ((σ.ao, 16), aoR), ((σ.inp, σ.len), inR)]

theorem shapeFull_fst (σ : Sig) : (shapeFull σ).map (·.1) = shapeOf σ := rfl
theorem shapeFull_snd (σ : Sig) : (shapeFull σ).map (·.2) = baseRegions := rfl

/-- Arithmetic facts of the entry `sp`. -/
theorem pre_sp {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    Layout.ramLo + stackBytes ≤ σ.S.toNat ∧ σ.S.toNat ≤ Layout.ramHi ∧ σ.S.toNat % 16 = 0 := by
  obtain ⟨-, ⟨hal, hlo, hhi, -⟩, -⟩ := hpre
  exact ⟨hlo, hhi, hal⟩

theorem sl_toNat {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {k : Nat} (hk : k ≤ stackBytes) :
    (σ.sl k).toNat = σ.S.toNat - k := by
  have := pre_sp hpre
  simp only [Sig.sl, w, BitVec.toNat_sub, BitVec.toNat_ofNat]
  unfold Layout.ramLo stackBytes at *; omega

theorem pre_wf {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (mh : Machine) (ov : Nat → Option Sym)
    (ks : List Write) : Env.WF (entryEnv mh (shapeOf σ)) (entryState ov baseRegions ks) := by
  have hsp := pre_sp hpre
  have hfr := sl_toNat hpre (k := frameBytes) (by decide)
  have hfr' := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  obtain ⟨-, -, -, hres, -, -, hao, -, -, -, hrest, -, -, -, hin, -, hlen, -, -, -,
    d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, -⟩ := hpre
  rw [← shapeFull_fst, ← shapeFull_snd]
  refine entry_wf (shapeFull σ) ?_ ?_
  · simp only [shapeFull, List.mem_cons, List.not_mem_nil, or_false]
    unfold RamRange at hres hao hrest
    unfold InputArea RamRange at hin
    rintro p (rfl | rfl | rfl | rfl | rfl) <;>
      simp [RegionOk, frameR, resR, restR, aoR, inR, frameBytes, Machine.writable,
        Machine.readable, Machine.inRange, Layout.ramLo, Layout.ramHi, Layout.rodataLo,
        Layout.rodataHi, Layout.inputLo, Layout.inputHi, stackBytes, Sig.res, Sig.ao, Sig.rest, Sig.inp, Sig.len, Sig.S] at * <;> omega
  · simp only [Sig.sl, Sig.S, w] at hfr hfr'
    unfold Apart at d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    rw [hfr'] at d7 d8 d9 d10
    simp only [shapeFull, List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true,
      Fn.Disjoint, Sig.sl, Sig.S, Sig.res, Sig.ao, Sig.rest, Sig.inp, Sig.len, w, hfr]
    simp only [Sig.S, stackBytes, frameBytes, false_implies, implies_true, and_true] at hsp d7 d8 d9 d10 hfr ⊢
    simp only [Layout.ramLo, Layout.ramHi] at hsp
    omega

theorem isSome_of_load {m : Machine} {a v : Word} (h : m.load a 8 = some v) :
    ∀ t < 8, (m.mem (a + BitVec.ofNat 64 t)).isSome := F1.present_of_load h (Nat.le_refl _)

/-- The 16 bytes at `a` are present when its two words load. -/
theorem present16 {m : Machine} {a : Word} (h0 : (m.load a 8).isSome) (h8 : (m.load (a + 8) 8).isSome) :
    Present m a 16 := by
  obtain ⟨v0, e0⟩ := Option.isSome_iff_exists.mp h0
  obtain ⟨v8, e8⟩ := Option.isSome_iff_exists.mp h8
  intro j hj
  rcases Nat.lt_or_ge j 8 with h | h
  · exact isSome_of_load e0 j h
  · have := isSome_of_load e8 (j - 8) (by omega)
    rwa [show (8 : Word) = BitVec.ofNat 64 8 from rfl, F1.add_add_ofNat,
      show 8 + (j - 8) = j by omega] at this

theorem pre_present {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (r j : Nat) (hr : r < 5)
    (hj : j < (envB σ σ.m).size r) :
    (σ.m.mem ((envB σ σ.m).base r + BitVec.ofNat 64 j)).isSome := by
  obtain ⟨-, ⟨-, hlo, -, hst⟩, -, -, -, hres, -, -, hao0, hao8, -, -, hr0, hr8, -, hin, hlen, -⟩ :=
    hpre
  simp only [envB, entryEnv, Env.size, Env.base, shapeOf] at hj ⊢
  obtain rfl | rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  all_goals simp at hj ⊢
  · have := hst (128 + j) (by simp only [stackBytes, frameBytes] at hj ⊢; omega)
    rwa [show σ.m.reg 2 - BitVec.ofNat 64 stackBytes + BitVec.ofNat 64 (128 + j) =
      σ.m.reg 2 - BitVec.ofNat 64 frameBytes + BitVec.ofNat 64 j by
        unfold stackBytes frameBytes; bv_omega] at this
  · exact hres j hj
  · exact present16 hr0 hr8 j hj
  · exact present16 hao0 (Option.isSome_iff_exists.mpr ⟨_, hao8⟩) j hj
  · simp only [Sig.len, Sig.rest] at hj
    rw [hin j (by omega)]; rfl

theorem pre_known {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    ∀ k ∈ [vtableKnown], ∀ t < k.n,
      (envB σ σ.m).byte0 k.r (k.off + t) = byteOf (k.v.eval (envB σ σ.m)) t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hvt, -⟩ := hpre
  intro k hk t ht
  simp only [List.mem_singleton] at hk; subst hk
  simp only [vtableKnown] at ht ⊢
  have := load_bytes hvt (Nat.le_refl _) t ht
  simp only [Env.byte0, envB, entryEnv, shapeOf, Sym.eval, List.getD_cons_succ,
    List.getD_cons_zero]
  rw [← F1.add_add_ofNat, show BitVec.ofNat 64 8 = (8 : Word) from rfl, this]; rfl

theorem pre_match {σ : Sig} (hpre : Pre σ.A σ.g σ.m) : Match (envB σ σ.m) SEntry σ.m := by
  refine Fn.entry_match ?_ (fun r j hr hj => pre_present hpre r j (by simpa [baseRegions] using hr) hj)
    (pre_known hpre)
  intro i hi s hs
  simp only [ovEntry] at hs
  repeat' split at hs
  all_goals (try cases hs)
  all_goals
    rename_i h
    obtain ⟨iv, hiv⟩ := i
    simp only at h; subst h
    simp [Sym.eval, Env.base, entryEnv, shapeOf, Sig.sl, Sig.S, w, frameBytes, BitVec.sub_add_cancel]

theorem TX.cut_80000000 : CutOK TX.plan TX.plan.cuts[0]! := by
  show CutOK TX.plan cutEntry
  rintro σ m ⟨rfl, hpc, hpre⟩
  exact ⟨pre_wf hpre _ ovEntry _, pre_match hpre, hpre.1, hpc⟩

theorem sl_add (σ : Sig) {k j : Nat} (h : j ≤ k) : σ.sl k + w j = σ.sl (k - j) := by
  simp only [Sig.sl, w]; bv_omega

/-- The stack below the entry `sp` is present (`StackOk`). -/
theorem stack_present {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {k : Nat} (hk : k ≤ stackBytes) :
    Present σ.m (σ.sl k) k := by
  obtain ⟨-, ⟨-, -, -, hst⟩, -⟩ := hpre
  intro j hj
  have := hst (stackBytes - k + j) (by omega)
  rwa [show σ.m.reg 2 - BitVec.ofNat 64 stackBytes + BitVec.ofNat 64 (stackBytes - k + j) =
    σ.sl k + w j by simp only [Sig.sl, Sig.S, w]; unfold stackBytes at hk ⊢; bv_omega] at this

theorem mem0_entry {m : Machine} {regs : List (Word × Nat)} {r j : Nat}
    (h : (m.mem ((entryEnv m regs).base r + BitVec.ofNat 64 j)).isSome) :
    some ((entryEnv m regs).mem0 r j) = m.mem ((entryEnv m regs).base r + BitVec.ofNat 64 j) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
  simp only [entryEnv, Env.base] at hb ⊢; rw [hb]; rfl

theorem wordAt_of_load {m : Machine} {a : Word} (h : (m.load a 8).isSome) :
    m.load a 8 = some (wordAt m a) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h; simp [wordAt, hv]

/-! ## After a leaf: what survives -/

theorem pre_fit {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    ∀ p ∈ shapeFull σ, p.1.1.toNat + p.1.2 < 2 ^ 64 := by
  have hfr := sl_toNat hpre (k := frameBytes) (by decide)
  have hsp := pre_sp hpre
  obtain ⟨-, -, -, hres, -, -, hao, -, -, -, hrest, -, -, -, hin, -⟩ := hpre
  unfold RamRange at hres hao hrest
  unfold InputArea RamRange at hin
  simp only [shapeFull, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl | rfl) <;>
    simp [Sig.sl, Sig.S, Sig.res, Sig.ao, Sig.rest, Sig.inp, Sig.len, w, frameBytes,
      Layout.ramLo, Layout.ramHi, Layout.inputLo, Layout.inputHi, stackBytes] at * <;> omega

/-- The writable base regions are TX's own ranges. -/
theorem owned_of_inWritable {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {mh : Machine}
    {ov : Nat → Option Sym} {ks : List Write} {a : Word}
    (h : InWritable (entryEnv mh (shapeOf σ)) (entryState ov baseRegions ks) a) : Owned σ a := by
  rw [← shapeFull_fst, ← shapeFull_snd] at h
  obtain ⟨p, hp, hw, hin⟩ := inWritable_entry h (pre_fit hpre)
  have hfr := sl_toNat hpre (k := frameBytes) (by decide)
  have hst := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  simp only [shapeFull, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · refine .inr (.inr (.inl ?_))
    simp only [InRange, frameBytes, stackBytes] at hin hfr hst ⊢
    simp only [Sig.sl, w] at hfr hst hin ⊢
    omega
  · exact .inl hin
  · exact .inr (.inl hin)
  · simp [aoR] at hw
  · simp [inR] at hw

/-- Rodata stays loaded and present bytes stay present over a leaf. -/
theorem after_leaf {env : Env} {S S' : SState} {m m' : Machine} (hro : RodataLoaded zesuImage m)
    (hwf : Env.WF env S) (hm' : Match env S' m') (hreg : S.regions.length ≤ S'.regions.length)
    (hso : SameOutside (InWritable env S) m m') : RodataLoaded zesuImage m' ∧ Preserved m m' :=
  have hp := F1.preserved_of_leaf hwf hm' hreg hso
  ⟨RodataLoaded.preserved hro hp fun _ _ hb => F1.zesu_rodata_low hb, hp⟩

theorem frame_trans {σ : Sig} {m m' : Machine} {R : Word → Prop}
    (h : SameOutside (fun a => Owned σ a ∨ σ.A.Priv σ.g.L a) σ.m m) (h' : SameOutside R m m')
    (hR : ∀ a, R a → Owned σ a ∨ σ.A.Priv σ.g.L a) :
    SameOutside (fun a => Owned σ a ∨ σ.A.Priv σ.g.L a) σ.m m' :=
  fun a ha => (h' a fun hr => ha (hR a hr)).trans (h a ha)

theorem Present.of_preserved {m m' : Machine} {a : Word} {n : Nat} (h : Present m a n)
    (hp : Preserved m m') : Present m' a n := fun j hj => hp.1 _ (h j hj)

/-- An owned byte is not the allocator's. -/
theorem owned_not_priv {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {a : Word} (h : Owned σ a) :
    ¬ σ.A.Priv σ.g.L a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hP⟩ := hpre
  rcases h with h | h | h | h
  · exact hP a (.inl h)
  · exact hP a (.inr (.inr (.inl h)))
  · exact hP a (.inr (.inr (.inr (.inr (.inl h)))))
  · exact hP a (.inr (.inr (.inr (.inr (.inr h)))))

/-- The input bytes are as at the entry. -/
theorem input_same {σ : Sig} {m : Machine} (hc : Common σ m) {j : Nat} (hj : j < σ.len) :
    m.mem (σ.inp + BitVec.ofNat 64 j) = σ.m.mem (σ.inp + BitVec.ofNat 64 j) := by
  have hpre := hc.2.1
  have hfr := hc.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hfit := pre_fit hpre ((σ.inp, σ.len), inR) (by simp [shapeFull])
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hin, -, -, -, -, -, -, -, -, d4, d5, d6, d7, d8,
    d9, d10, d11, d12, d13, d14, d15, hP⟩ := hpre
  have hr : InRange σ.inp σ.len (σ.inp + BitVec.ofNat 64 j) := by
    simp only [InRange]; rw [toNat_add_ofNat (by simp at hfit; omega)]; omega
  refine hfr _ fun h => ?_
  rcases h with h | h
  · unfold Owned at h; unfold Apart at d4 d6 d10 d14
    simp only [InRange, Sig.sl, w] at h hr
    rcases h with h | h | h | h
    · simp [Sig.res, Sig.inp, Sig.len, Sig.rest] at *; omega
    · simp [Sig.inp, Sig.len, Sig.rest] at *; omega
    · simp [Sig.inp, Sig.len, Sig.rest, Sig.S] at *; omega
    · simp [Sig.inp, Sig.len, Sig.rest, scratch] at *; omega
  · exact hP _ (.inr (.inr (.inr (.inl hr)))) h

/-- The input bytes are present. -/
theorem input_present {σ : Sig} {m : Machine} (hc : Common σ m) {j : Nat} (hj : j < σ.len) :
    (m.mem (σ.inp + BitVec.ofNat 64 j)).isSome := by
  rw [input_same hc hj]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb, hl, -⟩ := hc.2.1
  rw [hb j (by simp only [Sig.len, Sig.rest, BitVec.ofNat_eq_ofNat] at hj hl ⊢; omega)]; rfl

theorem stack_present' {σ : Sig} {m : Machine} (hc : Common σ m) {k j : Nat} (hj : j < k)
    (hk : k ≤ stackBytes) : (m.mem (σ.sl k + w j)).isSome := by
  have := hc.2.2.2.2.2.2.2.2.2.1 (stackBytes - k + j) (by omega)
  rwa [show σ.sl stackBytes + BitVec.ofNat 64 (stackBytes - k + j) = σ.sl k + w j by
    simp only [Sig.sl, w]; unfold stackBytes at hk ⊢; bv_omega] at this

/-- Numeric facts of the entry: `S`, the input window. -/
theorem entry_nums {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    Layout.ramLo + 704 ≤ σ.S.toNat ∧ σ.S.toNat ≤ Layout.ramHi ∧ σ.S.toNat % 16 = 0 ∧
    σ.inp.toNat + σ.len < 2 ^ 64 ∧
    ((Layout.inputLo ≤ σ.inp.toNat ∧ σ.inp.toNat + σ.len ≤ Layout.inputHi) ∨
      (Layout.ramLo ≤ σ.inp.toNat ∧ σ.inp.toNat + σ.len ≤ Layout.ramHi)) ∧
    (σ.S.toNat ≤ σ.inp.toNat ∨ σ.inp.toNat + σ.len ≤ σ.S.toNat - 704) := by
  have hsp := pre_sp hpre
  have hfit := pre_fit hpre ((σ.inp, σ.len), inR) (by simp [shapeFull])
  have hS704 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hia, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    d10, -⟩ := hpre
  have hD := d10
  unfold Apart at hD
  rw [show (σ.m.reg 2 - BitVec.ofNat 64 stackBytes).toNat = σ.S.toNat - stackBytes from hS704] at hD
  have hia' : InputArea σ.inp σ.len := hia
  unfold InputArea RamRange at hia'
  have hD' : σ.S.toNat - 704 + 704 ≤ σ.inp.toNat ∨ σ.inp.toNat + σ.len ≤ σ.S.toNat - 704 := hD
  have h1 := hsp.1
  unfold stackBytes Layout.ramLo at h1
  refine ⟨hsp.1, hsp.2.1, hsp.2.2, by simpa using hfit, hia', by omega⟩

/-- `decodeItem`'s precondition at a call from TX: the outcome struct is a frame slot, the input
a window of TX's input. -/
theorem f2_pre {σ : Sig} {m : Machine} (hc : Common σ m) {k : Nat} (hout : m.reg 10 = σ.sl k)
    (hk : 40 ≤ k) (hk' : k ≤ frameBytes) (hk8 : k % 8 = 0) {off : Nat}
    (hin : m.reg 11 = σ.inp + w off) (hlen : off + (m.reg 12).toNat ≤ σ.len) (hra : RetAligned m) :
    F2.Pre m := by
  have hpre := hc.2.1
  obtain ⟨hlo, hhi, h16, hfit, hia, hD⟩ := entry_nums hpre
  have hS := sl_toNat hpre (k := k) (by unfold frameBytes stackBytes at *; omega)
  have hS592 := sl_toNat hpre (k := 592) (by decide)
  have r2 : m.reg 2 = σ.sl 576 := hc.2.2.2.1
  have hio : (σ.inp + w off).toNat = σ.inp.toNat + off := toNat_add_ofNat (by omega)
  have hsp16 : m.reg 2 - 16 = σ.sl 592 := by rw [r2]; simp only [Sig.sl, w]; bv_omega
  have hsp : (m.reg 2).toNat = σ.S.toNat - 576 := by rw [r2]; exact sl_toNat hpre (by decide)
  unfold Layout.ramLo Layout.ramHi Layout.inputLo Layout.inputHi frameBytes at *
  refine ⟨hc.2.2.1, ⟨?_, ?_, ?_, ?_⟩, hra, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp]; omega
  · rw [hsp]; unfold Layout.ramLo; omega
  · rw [hsp]; unfold Layout.ramHi; omega
  · intro j hj
    have := stack_present' hc (k := 592) (j := j) (by omega) (by unfold stackBytes; omega)
    rwa [show σ.sl 592 + w j = m.reg 2 - BitVec.ofNat 64 16 + BitVec.ofNat 64 j by
      rw [r2]; simp only [Sig.sl, w]; bv_omega] at this
  · rw [hin, hio]
    simp [Machine.readable, Machine.inRange, Layout.rodataLo, Layout.rodataHi, Layout.inputLo,
      Layout.inputHi, Layout.ramLo, Layout.ramHi]
    omega
  · intro j hj
    have := input_present hc (j := off + j) (by omega)
    rwa [hin, show σ.inp + w off + BitVec.ofNat 64 j = σ.inp + BitVec.ofNat 64 (off + j) by
      simp only [w]; bv_omega]
  · rw [hout, hS]; simp [Machine.writable, Machine.inRange, Layout.ramLo, Layout.ramHi]; omega
  · rw [hout, hS]; omega
  · intro j hj
    have := stack_present' hc (k := k) (j := j) (by omega) (by unfold stackBytes; omega)
    rwa [hout]
  · unfold Fn.Disjoint; simp only; rw [hin, hio, hout, hS]; omega
  · unfold Fn.Disjoint; simp only; rw [hin, hio, hsp16, hS592]; omega
  · unfold Fn.Disjoint; simp only; rw [hout, hS, hsp16, hS592]; omega

/-! ## Cut points with a `Common` machine -/

/-- The allocator object is as at the entry. -/
theorem ao_same {σ : Sig} {m : Machine} (hc : Common σ m) {j : Nat} (hj : j < 16) :
    m.mem (σ.ao + BitVec.ofNat 64 j) = σ.m.mem (σ.ao + BitVec.ofNat 64 j) := by
  have hpre := hc.2.1
  have hfr := hc.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hlo, hhi, h16, -, -, -⟩ := entry_nums hpre
  have hS704 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  obtain ⟨-, -, -, -, -, -, hao, -, -, -, -, -, -, -, -, -, -, -, -, -, d1, -, d3, -, -, -, -, d8, -,
    -, -, d12, -, -, -, hP⟩ := hpre
  have hr : InRange σ.ao 16 (σ.ao + BitVec.ofNat 64 j) := by
    unfold RamRange Layout.ramHi at hao
    simp only [InRange]; rw [toNat_add_ofNat (by simp [Sig.ao]; omega)]; omega
  refine hfr _ fun h => ?_
  rcases h with h | h
  · have d8' : (σ.sl stackBytes).toNat + stackBytes ≤ σ.ao.toNat ∨
        σ.ao.toNat + 16 ≤ (σ.sl stackBytes).toNat := d8
    rw [hS704] at d8'
    unfold Apart at d1 d3 d12
    unfold Owned InRange at h; unfold InRange at hr
    rw [hS704] at h
    unfold stackBytes at d8' h
    simp only [Sig.res, Sig.ao, Sig.rest, scratch, BitVec.toNat_ofNat, Layout.extraParams] at h hr d1 d3 d12 d8' ⊢
    unfold Layout.ramLo Layout.ramHi at *
    omega
  · exact hP _ (.inr (.inl hr)) h

theorem common_vtable {σ : Sig} {m : Machine} (hc : Common σ m) :
    m.load (σ.ao + 8) 8 = some (w vtable) := by
  rw [load_congr (m := σ.m) fun t ht => by
    rw [show σ.ao + 8 + BitVec.ofNat 64 t = σ.ao + BitVec.ofNat 64 (8 + t) by bv_omega]
    exact ao_same hc (by omega)]
  exact hc.2.1.2.2.2.2.2.2.2.2.2.1

/-- Every base region's bytes are present at a `Common` machine. -/
theorem common_present {σ : Sig} {m : Machine} (hc : Common σ m) (r j : Nat) (hr : r < 5)
    (hj : j < (envB σ m).size r) :
    (m.mem ((envB σ m).base r + BitVec.ofNat 64 j)).isSome := by
  have hpre := hc.2.1
  simp only [envB, entryEnv, Env.size, Env.base, shapeOf] at hj ⊢
  obtain rfl | rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  all_goals simp at hj ⊢
  · have := stack_present' hc (k := frameBytes) (j := j) hj (by decide)
    exact this
  · exact hc.2.2.2.2.2.2.2.2.2.2.1 j hj
  · exact hc.2.2.2.2.2.2.2.2.2.2.2.1 j hj
  · rw [ao_same hc hj]
    exact pre_present hpre 3 j (by decide) (by simpa [envB, entryEnv, Env.size, shapeOf] using hj)
  · exact input_present hc hj

theorem common_known_vtable {σ : Sig} {m : Machine} (hc : Common σ m) :
    ∀ t < 8, (envB σ m).byte0 3 (8 + t) = byteOf ((Sym.lit vtable).eval (envB σ m)) t := by
  intro t ht
  have := load_bytes (common_vtable hc) (Nat.le_refl _) t ht
  simp only [Env.byte0, envB, entryEnv, shapeOf, Sym.eval, List.getD_cons_succ,
    List.getD_cons_zero]
  rw [← F1.add_add_ofNat, show BitVec.ofNat 64 8 = (8 : Word) from rfl, this]; rfl

theorem ovBody_ok {σ : Sig} {m : Machine} (hc : Common σ m) :
    ∀ i : Fin 32, i.val ≠ 0 → ∀ s, ovBody i.val = some s → s.eval (envB σ m) = m.reg i := by
  obtain ⟨-, -, -, r2, r8, r9, r18, -⟩ := hc
  intro i hi s hs
  simp only [ovBody] at hs
  repeat' split at hs
  all_goals (try cases hs)
  all_goals
    rename_i h
    obtain ⟨iv, hiv⟩ := i
    simp only at h; subst h
    simp [Sym.eval, Env.base, envB, entryEnv, shapeOf, Sig.sl, w, frameBytes, r2, r8, r9, r18,
      BitVec.sub_add_cancel]

/-- A cut whose state is `entryState ov baseRegions ks` with `envB`: the assertion's `Common`
and the register and `known` facts give `CutOK`'s conclusion. -/
theorem body_ok {σ : Sig} {m : Machine} (hc : Common σ m) {ov : Nat → Option Sym}
    {ks : List Write}
    (hov : ∀ i : Fin 32, i.val ≠ 0 → ∀ s, ov i.val = some s → s.eval (envB σ m) = m.reg i)
    (hks : ∀ k ∈ ks, ∀ t < k.n, (envB σ m).byte0 k.r (k.off + t) = byteOf (k.v.eval (envB σ m)) t) :
    Env.WF (envB σ m) (entryState ov baseRegions ks) ∧
      Match (envB σ m) (entryState ov baseRegions ks) m ∧ RodataLoaded zesuImage m :=
  ⟨pre_wf hc.2.1 m ov ks,
   Fn.entry_match hov (fun r j hr hj => common_present hc r j (by simpa [baseRegions] using hr) hj)
     hks, hc.2.2.1⟩

/-- `Common` survives a call whose frame (`R`) is TX's own or the allocator's memory and avoids
the save area. -/
theorem common_ret {σ : Sig} {mc m : Machine} (hc : Common σ mc) (hret : Returns mc m)
    (hp : Preserved mc m) {R : Word → Prop} (hso : SameOutside R mc m)
    (hR : ∀ a, R a → (Owned σ a ∨ σ.A.Priv σ.g.L a) ∧ ¬ InRange (σ.sl 104) 104 a) :
    Common σ m := by
  obtain ⟨hpc, hpre, hro, r2, r8, r9, r18, r19, hsv, hst, hres, hrest, hscr, hfr⟩ := hc
  have hS := entry_nums hpre
  have hs : ∀ i ∈ calleeSaved, m.reg i = mc.reg i := hret.2
  refine ⟨hpc, hpre, RodataLoaded.preserved hro hp fun _ _ hb => F1.zesu_rodata_low hb,
    (hs 2 (by decide)).trans r2, (hs 8 (by decide)).trans r8, (hs 9 (by decide)).trans r9,
    (hs 18 (by decide)).trans r18, (hs 19 (by decide)).trans r19, fun k hk => ?_,
    Present.of_preserved hst hp, Present.of_preserved hres hp, Present.of_preserved hrest hp,
    Present.of_preserved hscr hp,
    frame_trans hfr hso fun a h => (hR a h).1⟩
  rw [load_congr fun t ht => hso _ fun h => (hR _ h).2 ?_]
  · exact hsv k hk
  · have h1 := sl_toNat hpre (k := 104) (by decide)
    have h2 := sl_toNat hpre (k := 8 * (k + 1)) (by unfold stackBytes; omega)
    simp only [InRange, h1]
    rw [toNat_add_ofNat (by rw [h2]; omega), h2]
    omega

/-- After a `decodeItem` call with its outcome in the frame slot `S - k`. -/
theorem common_f2 {σ : Sig} {mc m : Machine} (hc : Common σ mc) {k : Nat}
    (hout : mc.reg 10 = σ.sl k) (hk : 144 ≤ k) (hk' : k ≤ frameBytes) (hpost : F2.Post mc m)
    (hp : Preserved mc m) : Common σ m := by
  have hpre := hc.2.1
  have r2 : mc.reg 2 = σ.sl 576 := hc.2.2.2.1
  refine common_ret hc hpost.1 hp hpost.2.1 fun a h => ?_
  have h1 : Layout.ramLo + 704 ≤ σ.S.toNat := (entry_nums hpre).1
  have h104 := sl_toNat hpre (k := 104) (by decide)
  have hk2 := sl_toNat hpre (k := k) (by unfold frameBytes stackBytes at *; omega)
  have h592 := sl_toNat hpre (k := 592) (by decide)
  have h704 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have hsp16 : mc.reg 2 - 16 = σ.sl 592 := by rw [r2]; simp only [Sig.sl, w]; bv_omega
  rw [hout, hsp16] at h
  clear hpost hc hp hout r2 hsp16
  unfold Layout.ramLo at h1
  unfold frameBytes at hk'
  simp only [Owned, InRange, h104, h704, hk2, h592] at h ⊢
  unfold stackBytes at h704 ⊢
  omega

theorem TX.leaf_80000000_0 :
    LeafGoal TX.plan TX.plan.cuts[0]! ((TX.plan.leaves 0x80000000)[0]!) := by
  show LeafGoal TX.plan cutEntry (runEntry_leaves[0]!)
  rintro σ m ⟨rfl, hpc, hpre⟩ -
  refine ⟨by simp [runEntry_leaves], by simp [runEntry_leaves, cutEntry, mkCut, SEntry, entryState, bEntry], ?_⟩
  intro m' hm' hex hfr
  have hx : runEntry_leaves[0]!.exit = .call 0x800d6960 0x80000068 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x800d6960 at hex
  change Match (envB σ σ.m) _ m' at hm'
  change SameOutside (InWritable (envB σ σ.m) SEntry) σ.m m' at hfr
  have hwf := pre_wf hpre σ.m ovEntry [vtableKnown]
  obtain ⟨hro, hp⟩ := after_leaf hpre.1 hwf hm' (by decide) hfr
  have reg : ∀ (i : Fin 32) (s : Sym), runEntry_leaves[0]!.S.reg i.val = s →
      m'.reg i = s.eval (envB σ σ.m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r1 := reg 1 _ (by decide : runEntry_leaves[0]!.S.reg 1 = .lit 0x80000068)
  have r2 := reg 2 _ (by decide : runEntry_leaves[0]!.S.reg 2 = .ptr 0 0)
  have r8 := reg 8 _ (by decide : runEntry_leaves[0]!.S.reg 8 = .ptr 0 576)
  have r9 := reg 9 _ (by decide : runEntry_leaves[0]!.S.reg 9 = .ptr 1 0)
  have r10 := reg 10 _ (by decide : runEntry_leaves[0]!.S.reg 10 = .ptr 0 88)
  have r11 := reg 11 _ (by decide : runEntry_leaves[0]!.S.reg 11 = .init 2 0 8)
  have r12 := reg 12 _ (by decide : runEntry_leaves[0]!.S.reg 12 = .init 2 8 8)
  have r18 := reg 18 _ (by decide : runEntry_leaves[0]!.S.reg 18 = .ptr 3 0)
  have r19 := reg 19 _ (by decide : runEntry_leaves[0]!.S.reg 19 = .var 1)
  have r22 := reg 22 _ (by decide : runEntry_leaves[0]!.S.reg 22 = .ptr 2 0)
  have r23 := reg 23 _ (by decide : runEntry_leaves[0]!.S.reg 23 = .init 2 0 8)
  have r24 := reg 24 _ (by decide : runEntry_leaves[0]!.S.reg 24 = .init 2 8 8)
  simp only [Sym.eval, Env.base, envB, entryEnv, shapeOf, List.getD_cons_zero,
    List.getD_cons_succ, Sig.sl, w, frameBytes] at r1 r2 r8 r9 r10 r18 r19 r22
  have hwf' : Env.WF (envB σ σ.m) runEntry_leaves[0]!.S := hwf.congr (by decide)
  have E := hpre
  obtain ⟨-, hstk, -, hres, hres8, hresP, hao, hao8, hao0, hvt, hrest, hrest8, hr0, hr8, hin,
    hinB, hlen, hdom, hscr, hheap, -⟩ := E
  -- the words of `rest`
  have hl0 := wordAt_of_load hr0
  have hl8 := wordAt_of_load hr8
  have hinp : (Sym.init 2 0 8).eval (envB σ σ.m) = σ.inp :=
    init_eval_load (regs := shapeOf σ) (r := 2) (by simp [shapeOf]) (by simpa [shapeOf] using hl0)
      (by unfold RamRange at hrest; simp [shapeOf, Sig.rest]; unfold Layout.ramHi at hrest; omega)
  have hlenw : (Sym.init 2 8 8).eval (envB σ σ.m) = w σ.len :=
    (init_eval_load (regs := shapeOf σ) (r := 2) (by simp [shapeOf]) (by simpa [shapeOf] using hl8)
      (by unfold RamRange at hrest; simp [shapeOf, Sig.rest]; unfold Layout.ramHi at hrest; omega)).trans
      (by simp [Sig.len, w])
  rw [hinp] at r11 r23; rw [hlenw] at r12 r24
  rw [BitVec.ofInt_ofNat, BitVec.add_zero] at r2 r9 r18 r22
  rw [show (BitVec.ofInt 64 576) = 576#64 from rfl, BitVec.sub_add_cancel] at r8
  rw [show σ.S - 576#64 + BitVec.ofInt 64 88 = σ.sl 0x1e8 by simp only [Sig.sl, w]; bv_omega] at r10
  have hown : ∀ a, InWritable (envB σ σ.m) SEntry a → Owned σ a := fun a h =>
    owned_of_inWritable hpre h
  -- `rest` is not written by the prologue
  have hrestSame : ∀ t < 16, m'.mem (σ.rest + BitVec.ofNat 64 t) = σ.m.mem (σ.rest + BitVec.ofNat 64 t) :=
    fun t ht => region_same (r := 2) hm' (by decide) (by decide)
      (fun j hj => mem0_entry (pre_present hpre 2 j (by decide) hj)) t (by simpa [envB, entryEnv, Env.size, shapeOf] using ht)
  have hsaved : ∀ k < 13, m'.load (σ.sl (8 * (k + 1))) 8 = some (σ.m.reg (savedReg k)) := by
    intro k hk
    have ha : σ.sl (8 * (k + 1)) = (envB σ σ.m).base 0 + BitVec.ofNat 64 (576 - 8 * (k + 1)) := by
      simp only [Env.base, envB, entryEnv, shapeOf, List.getD_cons_zero, Sig.sl, w, frameBytes]
      bv_omega
    rw [ha, load_cst hwf' hm' (r := 0) (R := frameR) (by decide)
      (by simp [Env.size, envB, entryEnv, shapeOf, frameBytes]; omega)]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
        k = 11 ∨ k = 12 := by omega
    all_goals rfl
  have hcommon : Common σ m' := by
    refine ⟨hpc, hpre, hro, r2, r8, r9, r18, r19, hsaved, ?_, ?_, ?_, ?_, ?_⟩
    · exact Present.of_preserved (stack_present hpre (Nat.le_refl _)) hp
    · exact Present.of_preserved hresP hp
    · exact Present.of_preserved (present16 hr0 hr8) hp
    · exact Present.of_preserved hscr hp
    · exact frame_trans (fun _ _ => rfl) hfr fun a h => .inl (hown a h)
  have hheap' : σ.A.Heap σ.g.L m' := σ.A.heap_frame' σ.g.L σ.m m' hheap
    (fun a ha => hfr a fun hw => owned_not_priv hpre (hown a hw) ha) hp
  have hsite : Site064 σ m' := by
    refine ⟨hcommon, ⟨σ.g.L, hheap', by simp, by simp⟩, ?_, ?_, r22, r23, r24, ?_⟩
    · rw [load_congr (fun t ht => hrestSame t (by omega))]; exact hl0
    · rw [load_congr (m := σ.m) (fun t ht => by
        rw [show σ.rest + 8 + BitVec.ofNat 64 t = σ.rest + BitVec.ofNat 64 (8 + t) by bv_omega]
        exact hrestSame (8 + t) (by omega)), hl8]
      simp [Sig.len, w]
    · refine ⟨r1, fun t ht => ?_⟩
      simp only [List.length_cons, List.length_nil] at ht
      obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
      · exact r10
      · exact r11
      · exact r12
  have hpre2 : F2.Pre m' := f2_pre hcommon r10 (by decide) (by decide) (by decide) (off := 0)
    (by rw [r11]; simp [w]) (by rw [r12]; simp [w, Sig.len]) (by unfold RetAligned; rw [r1]; decide)
  refine ⟨f2C, rfl, hex, ⟨(), hpre2⟩, fun m'' hpost => ⟨cut068, by simp [TX.plan, vcPlan], rfl, ?_,
    ⟨m', hsite, hpost⟩, ?_⟩⟩
  · obtain ⟨⟨_, _, hP⟩, _⟩ := hpost
    rw [hP.1.1, r1]; decide
  · simp [f2C, famCallee, cut068, cutEntry, mkCut, bEntry, SEntry, entryState, runEntry_leaves,
      F2.bound]
    omega

theorem ovRest_ok {σ : Sig} {m : Machine} (hc : Common σ m) (h22 : m.reg 22 = σ.rest) :
    ∀ i : Fin 32, i.val ≠ 0 → ∀ s, ovRest i.val = some s → s.eval (envB σ m) = m.reg i := by
  intro i hi s hs
  by_cases h : i.val = 22
  · simp only [ovRest, h, if_true, Option.some.injEq] at hs; subst hs
    obtain ⟨iv, hiv⟩ := i; simp only at h; subst h
    simp [Sym.eval, Env.base, envB, entryEnv, shapeOf, h22]
  · simp only [ovRest, h, if_false] at hs
    exact ovBody_ok hc i hi s hs

/-- The return address of a call whose `ra` was `ret`. -/
theorem ret_pc {mc m : Machine} {ret : Nat} (hret : Returns mc m) (hra : mc.reg 1 = w ret)
    (h : (w ret &&& ~~~(1 : Word)).toNat = ret) : m.pc.toNat = ret := by
  rw [hret.1, hra, h]

/-- Argument `t` of a call. -/
theorem Args.arg {m : Machine} {ret : Nat} {as : List Word} (h : Args m ret as) (t : Nat)
    (ht : t < as.length) : m.reg (Fin.ofNat 32 (10 + t)) = as.getD t 0 := h.2 t ht

theorem TX.cut_80000068 : CutOK TX.plan TX.plan.cuts[1]! := by
  show CutOK TX.plan cut068
  rintro σ m ⟨mc, hs, ⟨_, -, hpost⟩, hp⟩
  have hout : mc.reg 10 = σ.sl 0x1e8 := hs.2.2.2.2.2.2.2.arg 0 (by simp)
  have hc := common_f2 hs.1 hout (by decide) (by decide) hpost hp
  have h22 : m.reg 22 = σ.rest := (hpost.1.2 22 (by decide)).trans hs.2.2.2.2.1
  obtain ⟨hwf, hm, hro⟩ := body_ok hc (ovRest_ok hc h22) (ks := [vtableKnown]) (by
    intro k hk t ht; simp only [List.mem_singleton] at hk; subst hk
    exact common_known_vtable hc t ht)
  exact ⟨hwf, hm, hro, ret_pc hpost.1 hs.2.2.2.2.2.2.2.1 (by decide)⟩

/-- A frame word is loadable. -/
theorem frame_load {σ : Sig} {m : Machine} (hc : Common σ m) {k : Nat} (hk : 8 ≤ k)
    (hk' : k ≤ frameBytes) : m.load (σ.sl k) 8 = some (wordAt m (σ.sl k)) := by
  apply wordAt_of_load
  have hpre := hc.2.1
  have h1 : Layout.ramLo + 704 ≤ σ.S.toNat ∧ σ.S.toNat ≤ Layout.ramHi :=
    ⟨(entry_nums hpre).1, (entry_nums hpre).2.1⟩
  have hk2 := sl_toNat hpre (k := k) (by unfold frameBytes stackBytes at *; omega)
  unfold Machine.load
  have hr : Machine.readable (σ.sl k).toNat 8 = true := by
    rw [hk2]; unfold frameBytes at hk'
    simp [Machine.readable, Machine.inRange, Layout.ramLo, Layout.ramHi] at h1 ⊢; omega
  rw [if_pos hr]
  cases hb : readBytes m.mem (σ.sl k).toNat 8 with
  | some _ => rfl
  | none =>
    exfalso
    have : ∀ t < 8, (m.mem (BitVec.ofNat 64 ((σ.sl k).toNat + t))).isSome := fun t ht => by
      rw [ofNat_toNat_add]
      exact stack_present' hc (k := k) (j := t) (by omega) (by unfold frameBytes stackBytes at *; omega)
    exact absurd hb (by
      clear hb
      have h8 : ∀ (a n : Nat), (∀ t < n, (m.mem (BitVec.ofNat 64 (a + t))).isSome) →
          readBytes m.mem a n ≠ none := by
        intro a n; induction n generalizing a with
        | zero => intro _; simp [readBytes]
        | succ n ih =>
          intro h
          obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h 0 (by omega))
          have := ih (a + 1) fun t ht => by rw [Nat.add_assoc, Nat.add_comm 1 t]; exact h (t + 1) (by omega)
          simp only [readBytes, Nat.add_zero] at hb ⊢
          rw [hb]
          cases h' : readBytes m.mem (a + 1) n with
          | none => exact absurd h' this
          | some _ => simp
      exact h8 _ _ this)

theorem payload_known {σ : Sig} {m : Machine} (hc : Common σ m) {k : Nat} (hk : 8 ≤ k)
    (hk' : k ≤ frameBytes) :
    ∀ t < 8, (envP k σ m).byte0 0 (fo k + t) =
      byteOf ((Sym.bin .add (.ptr 4 0) (.var 40)).eval (envP k σ m)) t := by
  intro t ht
  have := load_bytes (frame_load hc hk hk') (Nat.le_refl _) t ht
  have ha : ((shapeOf σ).getD 0 (0, 0)).fst + BitVec.ofNat 64 (fo k + t) =
      σ.sl k + BitVec.ofNat 64 t := by
    simp only [shapeOf, List.getD_cons_zero, fo, Sig.sl, w]
    unfold frameBytes at hk' ⊢; bv_omega
  simp only [Env.byte0, envP, Env.setVars, envB, entryEnv]
  rw [ha, this]
  simp only [Sym.eval, BinOp.eval, Env.base, shapeOf, List.getD_cons_succ, List.getD_cons_zero]
  rw [BitVec.ofInt_ofNat, BitVec.add_zero, BitVec.add_comm, if_pos (Nat.le_refl _),
    BitVec.sub_add_cancel]; rfl

/-- `CutOK`'s conclusion at a cut with the payload fact at `S - k` (`0x8000010c`, `0x800001a0`). -/
theorem payload_ok {σ : Sig} {m : Machine} (hc : Common σ m) {k : Nat} (hk : 8 ≤ k)
    (hk' : k ≤ frameBytes) :
    Env.WF (envP k σ m) (entryState ovBody baseRegions [vtableKnown, payloadKnown k]) ∧
      Match (envP k σ m) (entryState ovBody baseRegions [vtableKnown, payloadKnown k]) m ∧
      RodataLoaded zesuImage m := by
  obtain ⟨hwf, hm, hro⟩ := body_ok hc (ovBody_ok hc) (ks := []) (by simp)
  have hext : Env.Ext (envB σ m) (envP k σ m) 40 5 :=
    ⟨fun i hi => by simp [envP, Env.setVars, Nat.not_le.mpr hi], fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ _ => rfl⟩
  have hm' := hm.ext (K := 40) (by decide) hext
  have hwf' := pre_wf hc.2.1 m ovBody [vtableKnown, payloadKnown k]
  refine ⟨⟨hwf'.len, hwf'.disjoint, hwf'.size, hwf'.align, hwf'.range⟩, ⟨hm'.regsLen, hm'.regs, hm'.mem, fun w hw t ht => ?_⟩, hro⟩
  simp only [entryState, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact common_known_vtable hc t ht
  · exact payload_known hc hk hk' t ht

/-- After a `decodeItem` call from a `Common` machine with its outcome at `S - k`. -/
theorem f2_ret {σ : Sig} {mc m : Machine} (hc : Common σ mc) {ret k : Nat} {as : List Word}
    (ha : Args mc ret (σ.sl k :: as)) (hk : 144 ≤ k) (hk' : k ≤ frameBytes)
    (hr : (w ret &&& ~~~(1 : Word)).toNat = ret) (hpost : f2C.Post σ mc m) :
    Common σ m ∧ m.pc.toNat = ret := by
  obtain ⟨⟨_, -, hP⟩, hp⟩ := hpost
  exact ⟨common_f2 hc (ha.arg 0 (by simp)) hk hk' hP hp, ret_pc hP.1 ha.1 hr⟩

theorem body_cut {σ : Sig} {m : Machine} (hc : Common σ m) :
    Env.WF (envB σ m) SBody ∧ Match (envB σ m) SBody m ∧ RodataLoaded zesuImage m :=
  body_ok hc (ovBody_ok hc) (ks := [vtableKnown]) (by
    intro k hk t ht; simp only [List.mem_singleton] at hk; subst hk
    exact common_known_vtable hc t ht)

theorem TX.cut_800000d8 : CutOK TX.plan TX.plan.cuts[3]! := by
  show CutOK TX.plan cut0d8
  rintro σ m ⟨mc, ⟨o, L, hs, ha⟩, hpost⟩
  obtain ⟨hc, hpc⟩ := f2_ret hs.1 ha (by decide) (by decide) (by decide) hpost
  exact ⟨(body_cut hc).1, (body_cut hc).2.1, (body_cut hc).2.2, hpc⟩

theorem TX.cut_8000010c : CutOK TX.plan TX.plan.cuts[4]! := by
  show CutOK TX.plan cut10c
  rintro σ m ⟨mc, ⟨o, k, L, hs, -, -, ha⟩, hpost⟩
  obtain ⟨hc, hpc⟩ := f2_ret hs.1.1 ha (by decide) (by decide) (by decide) hpost
  obtain ⟨h1, h2, h3⟩ := payload_ok hc (k := 0x180) (by decide) (by decide)
  exact ⟨h1, h2, h3, hpc⟩

theorem TX.cut_8000015c : CutOK TX.plan TX.plan.cuts[5]! := by
  show CutOK TX.plan cut15c
  rintro σ m ⟨mc, ⟨o, k, L, hs, -, ha⟩, hpost⟩
  obtain ⟨hc, hpc⟩ := f2_ret hs.1.1 ha (by decide) (by decide) (by decide) hpost
  exact ⟨(body_cut hc).1, (body_cut hc).2.1, (body_cut hc).2.2, hpc⟩

theorem TX.cut_800001a0 : CutOK TX.plan TX.plan.cuts[7]! := by
  show CutOK TX.plan cut1a0
  rintro σ m ⟨mc, ⟨o, k, L, hs, -, -, -, ha⟩, hpost⟩
  obtain ⟨hc, hpc⟩ := f2_ret hs.1 ha (by decide) (by decide) (by decide) hpost
  obtain ⟨h1, h2, h3⟩ := payload_ok hc (k := 0x100) (by decide) (by decide)
  exact ⟨h1, h2, h3, hpc⟩

theorem TX.cut_800000c4 : CutOK TX.plan TX.plan.cuts[2]! := by
  show CutOK TX.plan cut0c4
  rintro σ m ⟨hpc, o, L, hs⟩
  exact ⟨(body_cut hs.1).1, (body_cut hs.1).2.1, (body_cut hs.1).2.2, hpc⟩

theorem TX.cut_8000018c : CutOK TX.plan TX.plan.cuts[6]! := by
  show CutOK TX.plan cut18c
  rintro σ m ⟨hpc, o, k, L, hs, -⟩
  exact ⟨(body_cut hs.1).1, (body_cut hs.1).2.1, (body_cut hs.1).2.2, hpc⟩

/-! ## The allocator's memory and error exits -/

/-- `Priv` of TX's live list lies in `Priv g.L` (`arena_split`). -/
theorem priv_sub {σ : Sig} {m : Machine} {L X : List (Word × Nat)} (hpre : Pre σ.A σ.g σ.m)
    (hlive : Live σ m L X) {a : Word} (h : σ.A.Priv L a) : σ.A.Priv σ.g.L a := by
  have hheap0 : σ.A.Heap σ.g.L σ.m := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have harena := (σ.A.arena_split L m a hlive.1).mpr (.inl h)
  rcases (σ.A.arena_split σ.g.L σ.m a hheap0).mp harena with h' | ⟨b, hb, hin⟩
  · exact h'
  · exact absurd ⟨b, hlive.2.1.symm.subset (List.mem_append_left _ hb), hin⟩
      (σ.A.priv_not_live L a h)

/-- An env with the base regions and the machine's initial bytes. -/
structure BaseEnv (σ : Sig) (m : Machine) (env : Env) : Prop where
  regions : env.regions = shapeOf σ
  mem0 : env.mem0 = (envB σ m).mem0

theorem BaseEnv.ofB (σ : Sig) (m : Machine) : BaseEnv σ m (envB σ m) := ⟨rfl, rfl⟩
theorem BaseEnv.ofP (k : Nat) (σ : Sig) (m : Machine) : BaseEnv σ m (envP k σ m) := ⟨rfl, rfl⟩

theorem BaseEnv.init {σ : Sig} {m : Machine} {env : Env} (he : BaseEnv σ m env) (r off n : Nat) :
    (Sym.init r off n).eval env = (Sym.init r off n).eval (envB σ m) := by
  unfold Sym.eval Env.byte0; rw [he.mem0]

theorem BaseEnv.base {σ : Sig} {m : Machine} {env : Env} (he : BaseEnv σ m env) (r : Nat) :
    env.base r = (envB σ m).base r := by simp only [Env.base, he.regions]; rfl

theorem BaseEnv.size {σ : Sig} {m : Machine} {env : Env} (he : BaseEnv σ m env) (r : Nat) :
    env.size r = (envB σ m).size r := by simp only [Env.size, he.regions]; rfl

theorem BaseEnv.owned {σ : Sig} {m : Machine} {env : Env} (he : BaseEnv σ m env)
    (hpre : Pre σ.A σ.g σ.m) {S : SState} (hS : S.regions = baseRegions) {a : Word}
    (h : InWritable env S a) : Owned σ a := by
  obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := h
  exact owned_of_inWritable hpre (mh := m) (ov := ovBody) (ks := [])
    ⟨r, R, j, by simpa [entryState, hS] using hR, hw,
      by have := he.size r; simp only [envB] at this; rwa [← this],
      by have := he.base r; simp only [envB] at this; rw [this]⟩

/-- A saved word is what the save area held at the cut. -/
theorem saved_eval {σ : Sig} {m : Machine} {env : Env} (hc : Common σ m) (he : BaseEnv σ m env)
    {k : Nat} (hk : k < 13) :
    (Sym.init 0 (576 - 8 * (k + 1)) 8).eval env = σ.m.reg (savedReg k) := by
  rw [he.init]
  apply init_eval_load (regs := shapeOf σ) (r := 0) (by simp [shapeOf])
  · have := hc.2.2.2.2.2.2.2.2.1 k hk
    rwa [show σ.sl (8 * (k + 1)) =
        ((shapeOf σ)[0]'(by simp [shapeOf])).1 + BitVec.ofNat 64 (576 - 8 * (k + 1)) by
      simp only [shapeOf, List.getElem_cons_zero, Sig.sl, w, frameBytes]; bv_omega] at this
  · have := (entry_nums hc.2.1).1
    simp only [shapeOf, List.getElem_cons_zero]
    rw [sl_toNat hc.2.1 (by decide)]
    unfold Layout.ramLo frameBytes at *; omega

/-- The writes of the error exit `+0x4a8`: `res = {0, 0, 3}`. -/
def errWrites : List Write := [⟨1, 16, 8, .lit 3⟩, ⟨1, 8, 8, .lit 0⟩, ⟨1, 0, 8, .lit 0⟩]

/-- The return target of the epilogue. -/
def retTarget : Sym := .bin .and (.init 0 568 8) (.lit 18446744073709551614)

/-- Reading the result after the error exit. -/
theorem err_res {σ : Sig} {m m' : Machine} {env : Env} {S' : SState} (he : BaseEnv σ m env) (hwf' : Env.WF env S') (hm' : Match env S' m')
    (hS'reg : S'.regions = baseRegions) (hmem : S'.mem = errWrites) :
    m'.load σ.res 8 = some 0 ∧ m'.load (σ.res + 8) 8 = some 0 ∧ m'.load (σ.res + 16) 8 = some 3 := by
  have hb : env.base 1 = σ.res := by rw [he.base]; rfl
  have hs : env.size 1 = 24 := by rw [he.size]; rfl
  have hR : S'.regions[1]? = some resR := by rw [hS'reg]; rfl
  have l0 := load_cst hwf' hm' (off := 0) (n := 8) hR (by rw [hs]; decide)
  have l8 := load_cst hwf' hm' (off := 8) (n := 8) hR (by rw [hs]; decide)
  have l16 := load_cst hwf' hm' (off := 16) (n := 8) hR (by rw [hs]; decide)
  simp only [readConst, hmem, errWrites] at l0 l8 l16
  rw [hb] at l0 l8 l16
  refine ⟨?_, ?_, ?_⟩
  · rw [show σ.res = σ.res + BitVec.ofNat 64 0 by simp, l0]; rfl
  · rw [show σ.res + 8 = σ.res + BitVec.ofNat 64 8 from rfl, l8]; rfl
  · rw [show σ.res + 16 = σ.res + BitVec.ofNat 64 16 from rfl, l16]; rfl

/-- An error exit (`+0x4a8`, epilogue, `ret`) from a `Common` machine with TX's live list:
`Post` with the given error class and consumed count. -/
theorem error_post {σ : Sig} {m m' : Machine} {env : Env} {S S' : SState}
    {L X : List (Word × Nat)} (hc : Common σ m) (hlive : Live σ m L X) (he : BaseEnv σ m env)
    (hwf : Env.WF env S) (hSreg : S.regions = baseRegions) (hm' : Match env S' m')
    (hS'reg : S'.regions = baseRegions) (hfr : SameOutside (InWritable env S) m m')
    (hsave : ∀ k < 13, S'.reg (savedReg k).val = .init 0 (576 - 8 * (k + 1)) 8)
    (hsp : S'.reg 2 = .ptr 0 576) (hpc : m'.pc = retTarget.eval env) (hmem : S'.mem = errWrites)
    {cls : OutcomeClass} (hcls : cls = .invalidInput ∨ cls = .allocationFailure) {c : Nat}
    (hall : OutcomeAllowed σ.input cls c)
    (hr0 : m.load σ.rest 8 = some (σ.inp + w c))
    (hr8 : m.load (σ.rest + 8) 8 = some (wordAt σ.m (σ.rest + 8) - w c)) :
    Post σ.A σ.g σ.m m' := by
  have hpre := hc.2.1
  have hwf' : Env.WF env S' := hwf.congr (hS'reg.trans hSreg.symm)
  have hp : Preserved m m' :=
    F1.preserved_of_leaf hwf hm' (by rw [hSreg, hS'reg]; exact Nat.le_refl _) hfr
  have hown : ∀ a, InWritable env S a → Owned σ a := fun a h => he.owned hpre hSreg h
  -- registers after the epilogue
  have hreg : ∀ i ∈ calleeSaved, m'.reg i = σ.m.reg i := by
    intro i hi
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
    have hk : ∀ k < 13, i = savedReg k → m'.reg i = σ.m.reg i := fun k hk h => by
      rw [Match.reg_eq hm' i (savedReg k).val (by rw [h]), hsave k hk, saved_eval hc he hk, h]
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Match.reg_eq hm' 2 2 rfl, hsp]
      simp only [Sym.eval, he.base]
      simp [Env.base, envB, entryEnv, shapeOf, Sig.sl, w, frameBytes, BitVec.sub_add_cancel]
    · exact hk 1 (by decide) rfl
    · exact hk 2 (by decide) rfl
    · exact hk 3 (by decide) rfl
    · exact hk 4 (by decide) rfl
    · exact hk 5 (by decide) rfl
    · exact hk 6 (by decide) rfl
    · exact hk 7 (by decide) rfl
    · exact hk 8 (by decide) rfl
    · exact hk 9 (by decide) rfl
    · exact hk 10 (by decide) rfl
    · exact hk 11 (by decide) rfl
    · exact hk 12 (by decide) rfl
  have hpc' : m'.pc = σ.m.reg 1 &&& ~~~(1 : Word) := by
    rw [hpc]
    have := saved_eval hc he (k := 0) (by decide)
    simp only [retTarget, Sym.eval, BinOp.eval] at this ⊢
    rw [this]; rfl
  -- `rest` is not written
  have hrest : ∀ t < 16, m'.mem (σ.rest + BitVec.ofNat 64 t) = m.mem (σ.rest + BitVec.ofNat 64 t) := by
    intro t ht
    have h2 := region_same (r := 2) (m := m) hm' (by rw [hS'reg]; decide) (by rw [hmem]; decide)
      (fun j hj => by
        rw [he.mem0, he.base]
        exact mem0_entry (common_present hc 2 j (by decide) (by rwa [← he.size])))
      t (by rw [he.size]; simpa [envB, entryEnv, Env.size, shapeOf] using ht)
    rwa [he.base] at h2
  have hheap : σ.A.Heap L m' := σ.A.heap_frame' L m m' hlive.1
    (fun a ha => hfr a fun hw => owned_not_priv hpre (hown a hw) (priv_sub hpre hlive ha)) hp
  obtain ⟨e0, e8, e16⟩ := err_res he hwf' hm' hS'reg hmem
  have hfr' := frame_trans hc.2.2.2.2.2.2.2.2.2.2.2.2.2 hfr fun a h => .inl (hown a h)
  refine ⟨⟨hpc', hreg⟩, fun a ha => hfr' a fun h => ha ?_,
    Present.of_preserved hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hp, cls, c, hall, ?_, ?_, ?_⟩
  · rcases h with (h | h | h | h) | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))
  · rw [load_congr fun t ht => hrest t (by omega)]; exact hr0
  · rw [load_congr (m := m) fun t ht => by
      rw [show σ.rest + 8 + BitVec.ofNat 64 t = σ.rest + BitVec.ofNat 64 (8 + t) by bv_omega]
      exact hrest (8 + t) (by omega)]
    exact hr8
  · have himg : m'.load σ.res 8 = some 0 ∧ m'.load (σ.res + 8) 8 = some 0 ∧
        m'.load (σ.res + 16) 8 = some 3 ∧ ∃ leaked : List (Word × Nat),
          (∀ b ∈ leaked, 0 < b.2 ∧ RamRange b.1 b.2) ∧
          ∃ L', L'.Perm (σ.g.L ++ leaked) ∧ σ.A.Heap L' m' :=
      ⟨e0, e8, e16, X, fun b hb => ⟨(hlive.2.2 b hb).1, (hlive.2.2 b hb).2.1⟩, L, hlive.2.1, hheap⟩
    rcases hcls with rfl | rfl <;> exact himg

end ZesuExec.Fn.TX
