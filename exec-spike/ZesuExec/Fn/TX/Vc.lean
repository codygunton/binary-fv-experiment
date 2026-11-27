import ZesuExec.Fn.TX.Cuts

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

end ZesuExec.Fn.TX
