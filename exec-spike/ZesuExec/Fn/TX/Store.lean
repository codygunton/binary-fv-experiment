import ZesuExec.Fn.TX.Ret

/-!
# TX: cut lemmas of the two store sites `0x80000230` and `0x80000460` (programme plan S6 step 6)

Their states have a sixth region, the slot at `a0` (`slotR`), inside a block of TX's live list,
so its bytes are the allocator's (`Priv g.L`) and apart from every base region.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

theorem getElem?_snoc_lt {α : Type} {l : List α} {x : α} {r : Nat} (h : r < l.length) :
    (l ++ [x])[r]? = l[r]? := List.getElem?_append_left h

theorem getElem?_snoc_gt {α : Type} {l : List α} {x : α} {r : Nat} (h : l.length < r) :
    (l ++ [x])[r]? = none := by
  rw [List.getElem?_append_right (by omega)]; simp; omega

/-- `Env.WF` for one more region whose bytes avoid every old region's. -/
theorem wf_snoc {env env' : Env} {S S' : SState} (hwf : Env.WF env S) {x : Word × Nat}
    {R : Region} (hS' : S'.regions = S.regions ++ [R]) (henv : env'.regions = env.regions ++ [x])
    (hsz : ∀ s, R.size = some s → x.2 = s) (hal : x.1.toNat % R.align = 0)
    (hrg : (if R.writable then writable x.1.toNat x.2 else readable x.1.toNat x.2) = true)
    (hdis : ∀ r j j', r < env.regions.length → j < env.size r → j' < x.2 →
      (env.base r).toNat + j ≠ x.1.toNat + j') : Env.WF env' S' := by
  have hn := hwf.len
  have hb : ∀ r, r < env.regions.length → env'.base r = env.base r := fun r hr => by
    simp only [Env.base, henv, List.getD_eq_getElem?_getD, getElem?_snoc_lt hr]
  have hs : ∀ r, r < env.regions.length → env'.size r = env.size r := fun r hr => by
    simp only [Env.size, henv, List.getD_eq_getElem?_getD, getElem?_snoc_lt hr]
  have hbn : env'.base env.regions.length = x.1 := by
    simp [Env.base, henv, List.getD_eq_getElem?_getD]
  have hsn : env'.size env.regions.length = x.2 := by
    simp [Env.size, henv, List.getD_eq_getElem?_getD]
  have hsg : ∀ r, env.regions.length < r → env'.size r = 0 := fun r hr => by
    simp [Env.size, henv, List.getD_eq_getElem?_getD, getElem?_snoc_gt hr]
  have hSr : ∀ r, r < env.regions.length → S'.regions[r]? = S.regions[r]? := fun r hr => by
    rw [hS', getElem?_snoc_lt (by omega)]
  have hSn : S'.regions[env.regions.length]? = some R := by rw [hS', hn]; simp
  have hSg : ∀ r, env.regions.length < r → S'.regions[r]? = none := fun r hr => by
    rw [hS', getElem?_snoc_gt (by omega)]
  refine ⟨by rw [henv, hS', List.length_append, List.length_append, hn]; simp, ?_, ?_, ?_, ?_⟩
  · intro r r' j j' hne hj hj'
    rcases Nat.lt_trichotomy r env.regions.length with h1 | h1 | h1 <;>
      rcases Nat.lt_trichotomy r' env.regions.length with h2 | h2 | h2
    · rw [hb r h1, hb r' h2]; rw [hs r h1] at hj; rw [hs r' h2] at hj'
      exact hwf.disjoint r r' j j' hne hj hj'
    · subst h2; rw [hb r h1, hbn]; rw [hs r h1] at hj; rw [hsn] at hj'
      exact hdis r j j' h1 hj hj'
    · rw [hsg r' h2] at hj'; omega
    · subst h1; rw [hbn, hb r' h2]; rw [hsn] at hj; rw [hs r' h2] at hj'
      exact (hdis r' j' j h2 hj' hj).symm
    · exact absurd (h1.trans h2.symm) hne
    · rw [hsg r' h2] at hj'; omega
    all_goals (rw [hsg r h1] at hj; omega)
  · intro r R' s hR hs'
    rcases Nat.lt_trichotomy r env.regions.length with h1 | h1 | h1
    · rw [hs r h1]; exact hwf.size r R' s (by rwa [hSr r h1] at hR) hs'
    · subst h1; rw [hSn] at hR; cases hR; rw [hsn]; exact hsz s hs'
    · rw [hSg r h1] at hR; cases hR
  · intro r R' hR
    rcases Nat.lt_trichotomy r env.regions.length with h1 | h1 | h1
    · rw [hb r h1]; exact hwf.align r R' (by rwa [hSr r h1] at hR)
    · subst h1; rw [hSn] at hR; cases hR; rw [hbn]; exact hal
    · rw [hSg r h1] at hR; cases hR
  · intro r R' hR
    rcases Nat.lt_trichotomy r env.regions.length with h1 | h1 | h1
    · rw [hb r h1, hs r h1]; exact hwf.range r R' (by rwa [hSr r h1] at hR)
    · subst h1; rw [hSn] at hR; cases hR; rw [hbn, hsn]; exact hrg
    · rw [hSg r h1] at hR; cases hR

theorem shape_fit {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    ∀ p ∈ shapeOf σ, p.1.toNat + p.2 < 2 ^ 64 := by
  rw [← shapeFull_fst]; intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact pre_fit hpre q hq

/-- The base regions' bytes are not the allocator's. -/
theorem shape_not_priv {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    ∀ p ∈ shapeOf σ, ∀ a, InRange p.1 p.2 a → ¬ σ.A.Priv σ.g.L a := by
  have hP := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  intro p hp a ha
  simp only [shapeOf, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact stack_not_priv hpre
      (sl_in_stack hpre (k := frameBytes) (n := frameBytes) (by decide) (Nat.le_refl _) ha)
  · exact hP a (.inl ha)
  · exact hP a (.inr (.inr (.inl ha)))
  · exact hP a (.inr (.inl ha))
  · exact hP a (.inr (.inr (.inr (.inl ha))))

theorem envS_regions (n : Nat) (σ : Sig) (m : Machine) :
    (envS n σ m).regions = (envB σ m).regions ++ [(m.reg 10, n)] := rfl

theorem envS_base {n : Nat} {σ : Sig} {m : Machine} {r : Nat} (hr : r < 5) :
    (envS n σ m).base r = (envB σ m).base r := by
  simp only [Env.base, envS_regions, List.getD_eq_getElem?_getD]
  rw [getElem?_snoc_lt (by simp [envB, entryEnv, shapeOf]; omega)]

theorem envS_size {n : Nat} {σ : Sig} {m : Machine} {r : Nat} (hr : r < 5) :
    (envS n σ m).size r = (envB σ m).size r := by
  simp only [Env.size, envS_regions, List.getD_eq_getElem?_getD]
  rw [getElem?_snoc_lt (by simp [envB, entryEnv, shapeOf]; omega)]

theorem envS_byte0 {n : Nat} {σ : Sig} {m : Machine} {r j : Nat} (hr : r < 5) :
    (envS n σ m).byte0 r j = (envB σ m).byte0 r j := by
  have := envS_base (n := n) (σ := σ) (m := m) hr
  simp only [Env.base] at this
  simp only [Env.byte0, envS, envB, entryEnv] at this ⊢
  rw [this]

/-- A slot of `n` bytes at `a0` inside a block of TX's live list. -/
theorem slot_of_block {σ : Sig} {m : Machine} {L X : List (Word × Nat)} (hlive : Live σ m L X)
    {p : Word} {sz off n : Nat} (hb : (p, sz) ∈ X) (hram : RamRange p sz) (hoff : off + n ≤ sz)
    (h10 : m.reg 10 = p + w off) :
    (∀ j < n, σ.A.Priv σ.g.L (m.reg 10 + w j)) ∧ RamRange (m.reg 10) n ∧
      Present m (m.reg 10) n := by
  unfold RamRange Layout.ramHi at hram
  have hp : (m.reg 10).toNat = p.toNat + off := by rw [h10]; exact toNat_add_ofNat (by omega)
  have hL : (p, sz) ∈ L := hlive.2.1.symm.subset (List.mem_append_right _ hb)
  have hpres := ((σ.A.live_ok L m hlive.1).2 _ hL).2
  refine ⟨fun j hj => (hlive.2.2 _ hb).2.2 _ ?_, ?_, fun j hj => ?_⟩
  · simp only [InRange]; rw [toNat_add_ofNat (by omega), hp]; omega
  · unfold RamRange Layout.ramHi; rw [hp]; omega
  · rw [h10, show p + w off + BitVec.ofNat 64 j = p + BitVec.ofNat 64 (off + j) by
      simp only [w]; bv_omega]
    exact hpres (off + j) (by omega)

theorem ovSlot_ok {σ : Sig} {m : Machine} (hc : Common σ m) (n : Nat) :
    ∀ i : Fin 32, i.val ≠ 0 → ∀ s, ovSlot i.val = some s → s.eval (envS n σ m) = m.reg i := by
  obtain ⟨-, -, -, r2, r8, r9, r18, -⟩ := hc
  intro i hi s hs
  simp only [ovSlot, ovBody] at hs
  repeat' split at hs
  all_goals (try cases hs)
  all_goals
    rename_i h
    obtain ⟨iv, hiv⟩ := i
    simp only at h; subst h
    simp [Sym.eval, Env.base, envS, entryEnv, shapeOf, Sig.sl, w, frameBytes, r2, r8, r9, r18,
      BitVec.sub_add_cancel]

/-- `CutOK`'s conclusion at a store site with an `n`-byte slot of the allocator's memory. -/
theorem slot_ok {σ : Sig} {m : Machine} (hc : Common σ m) {n : Nat}
    (hpriv : ∀ j < n, σ.A.Priv σ.g.L (m.reg 10 + w j)) (hram : RamRange (m.reg 10) n)
    (hpres : Present m (m.reg 10) n) :
    Env.WF (envS n σ m) (entryState ovSlot (baseRegions ++ [slotR n]) [vtableKnown]) ∧
      Match (envS n σ m) (entryState ovSlot (baseRegions ++ [slotR n]) [vtableKnown]) m ∧
      RodataLoaded zesuImage m := by
  have hpre := hc.2.1
  have hwf := pre_wf hpre m ovBody [vtableKnown]
  have hlen : (envB σ m).regions.length = 5 := rfl
  refine ⟨wf_snoc hwf (x := (m.reg 10, n)) rfl (envS_regions n σ m) (fun s hs => by
      simp only [slotR, Option.some.injEq] at hs; exact hs) (by simp [slotR, Nat.mod_one])
      (by unfold RamRange at hram; simp [slotR, Machine.writable, Machine.inRange] at hram ⊢; omega)
      (fun r j j' hr hj hj' he => ?_), ?_, hc.2.2.1⟩
  · replace hr : r < 5 := hr
    have hl : r < (shapeOf σ).length := by simp [shapeOf]; omega
    have hmem : (shapeOf σ)[r] ∈ shapeOf σ := List.getElem_mem hl
    have hfit := shape_fit hpre _ hmem
    have hb : (entryEnv m (shapeOf σ)).base r = (shapeOf σ)[r].1 :=
      Env.base_of_lt (by simpa [entryEnv] using hl)
    have hs : (entryEnv m (shapeOf σ)).size r = (shapeOf σ)[r].2 :=
      Env.size_of_lt (by simpa [entryEnv] using hl)
    rw [hb] at he; rw [hs] at hj
    simp only at hj' he
    unfold RamRange Layout.ramHi at hram
    apply shape_not_priv hpre _ hmem ((shapeOf σ)[r].1 + w j)
      (by simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega)
    have heq : (shapeOf σ)[r].1 + w j = m.reg 10 + w j' := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]; exact he
    rw [heq]; exact hpriv j' hj'
  · refine Fn.entry_match (ovSlot_ok hc n) (fun r j hr hj => ?_) ?_
    · simp only [List.length_append, baseRegions, List.length_cons, List.length_nil] at hr
      rcases Nat.lt_or_ge r 5 with h5 | h5
      · have := common_present hc r j h5 (by rwa [← envS_size h5])
        change (m.mem ((envS n σ m).base r + BitVec.ofNat 64 j)).isSome
        rwa [envS_base h5]
      · obtain rfl : r = 5 := by omega
        have hb : (envS n σ m).base 5 = m.reg 10 := rfl
        have hs : (envS n σ m).size 5 = n := rfl
        change (m.mem ((envS n σ m).base 5 + BitVec.ofNat 64 j)).isSome
        rw [hb]; exact hpres j (by change j < n at hj; exact hj)
    · intro k hk t ht
      simp only [List.mem_singleton] at hk; subst hk
      have := common_known_vtable hc t ht
      change (envS n σ m).byte0 3 (8 + t) = byteOf ((Sym.lit vtable).eval (envS n σ m)) t
      rw [envS_byte0 (r := 3) (by decide)]
      exact this

theorem TX.cut_80000230 : CutOK TX.plan TX.plan.cuts[9]! := by
  show CutOK TX.plan cut230
  rintro σ m ⟨hpc, o, k, L, key, kh', hIE, -, -, -, -, -, hKL, hcap, h10, -⟩
  have hc := hIE.1
  have hk0 : 0 < k.kc.toNat := by omega
  obtain ⟨hpriv, hram, hpres⟩ := slot_of_block hIE.2.2.2.2.1 (p := k.kq)
    (sz := keySize * k.kc.toNat) (off := keySize * k.keys.length) (n := keySize)
    (by simp [EX, KX, hk0]) (hKL.2.2.2.2.2.1 hk0)
    (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hcap) h10
  obtain ⟨h1, h2, h3⟩ := slot_ok hc hpriv hram hpres
  exact ⟨h1, h2, h3, hpc⟩

theorem TX.cut_80000460 : CutOK TX.plan TX.plan.cuts[15]! := by
  show CutOK TX.plan cut460
  rintro σ m ⟨hpc, o, k, L, kp', hc, -, -, -, hEL, hcap, hlive, -, -, -, -, -, -, -, -, h10, -⟩
  have hk0 : 0 < o.ec.toNat := by omega
  obtain ⟨hpriv, hram, hpres⟩ := slot_of_block hlive (p := o.ep)
    (sz := entrySize * o.ec.toNat) (off := entrySize * o.done.length) (n := entrySize)
    (by simp [EX, hk0]) (hEL.2.2.2.2.2.1 hk0)
    (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hcap) h10
  obtain ⟨h1, h2, h3⟩ := slot_ok hc hpriv hram hpres
  exact ⟨h1, h2, h3, hpc⟩

end ZesuExec.Fn.TX
