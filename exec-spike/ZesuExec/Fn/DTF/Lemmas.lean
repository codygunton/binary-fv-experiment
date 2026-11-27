import ZesuExec.Fn.DTF.Cuts
import ZesuExec.Fn.Stage
import ZesuExec.Fn.F1.Lemmas
import ZesuExec.Sym.Summary

/-!
# DTF: lemmas for the cut lemmas and leaves (programme plan S7 step 4)

`cut_plain`: the cut lemma of every cut reached only by jumps and branches whose state has no
extra region (70 of the 161): its `Common`, `ShapeOk` and the entry's `Pre` give `Env.WF`,
`Match` (registers by the shape, the base regions present, the vtable word and the shape's frame
slots as known facts) and `RodataLoaded`.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## The entry's numbers -/

theorem pre_sp {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    Layout.ramLo + stackBytes ≤ σ.S.toNat ∧ σ.S.toNat ≤ Layout.ramHi ∧ σ.S.toNat % 16 = 0 := by
  obtain ⟨-, ⟨hal, hlo, hhi, -⟩, -⟩ := hpre
  exact ⟨hlo, hhi, hal⟩

theorem S_sub_toNat {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {k : Nat} (hk : k ≤ stackBytes) :
    (σ.S - w k).toNat = σ.S.toNat - k := by
  have := pre_sp hpre
  simp only [w, BitVec.toNat_sub, BitVec.toNat_ofNat]
  unfold Layout.ramLo stackBytes TX.stackBytes at *; omega

theorem fr_toNat {σ : Sig} (hpre : Pre σ.A σ.g σ.m) : σ.fr.toNat = σ.S.toNat - frameBytes :=
  S_sub_toNat hpre (by decide)

/-- The base regions with their executor view. -/
def shapeFull (σ : Sig) : Fn.Shape :=
  [((σ.fr, frameBytes), frameR), ((σ.res, resultBytes), resR), ((σ.ao, 16), aoR),
    ((σ.inp, σ.len), inR)]

theorem regionsOf_base {sh : Shape} (hx : sh.extra = []) (σ : Sig) (m : Machine) :
    regionsOf sh σ m = (shapeFull σ).map (·.1) := by
  simp [regionsOf, hx, shapeFull]

theorem shapeFull_snd (σ : Sig) : (shapeFull σ).map (·.2) = baseRegions := rfl

theorem pre_wf {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (mh : Machine) (ov : Nat → Option Sym)
    (ks : List Write) :
    Env.WF (entryEnv mh ((shapeFull σ).map (·.1))) (entryState ov baseRegions ks) := by
  have hsp := pre_sp hpre
  have hfr := fr_toNat hpre
  have hst := S_sub_toNat hpre (k := stackBytes) (Nat.le_refl _)
  obtain ⟨-, -, -, hres, -, hao, -, -, -, -, hin, -, -, -, -, -,
    d1, d2, d3, d4, d5, d6, -⟩ := hpre
  rw [← shapeFull_snd]
  refine entry_wf (shapeFull σ) ?_ ?_
  · simp only [shapeFull, List.mem_cons, List.not_mem_nil, or_false]
    unfold RamRange at hres hao
    unfold TX.InputArea RamRange at hin
    rintro p (rfl | rfl | rfl | rfl) <;>
      simp [RegionOk, frameR, resR, aoR, inR, frameBytes, resultBytes, Machine.writable,
        Machine.readable, Machine.inRange, Layout.ramLo, Layout.ramHi, Layout.rodataLo,
        Layout.rodataHi, Layout.inputLo, Layout.inputHi, stackBytes, TX.stackBytes, Sig.res,
        Sig.ao, Sig.inp, Sig.len, Sig.S, Sig.fr] at * <;> omega
  · unfold TX.Apart at d1 d2 d3 d4 d5 d6
    simp only [Sig.S, w] at hst
    rw [hst] at d4 d5 d6
    simp only [shapeFull, List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true,
      Fn.Disjoint, hfr]
    simp only [Sig.S, Sig.res, Sig.ao, Sig.inp, Sig.len, stackBytes, TX.stackBytes, frameBytes,
      resultBytes, false_implies, implies_true, and_true] at hsp d1 d2 d3 d4 d5 d6 ⊢
    simp only [Layout.ramLo, Layout.ramHi] at hsp
    omega

theorem pre_fit {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    ∀ p ∈ shapeFull σ, p.1.1.toNat + p.1.2 < 2 ^ 64 := by
  have hfr := fr_toNat hpre
  have hsp := pre_sp hpre
  obtain ⟨-, -, -, hres, -, hao, -, -, -, -, hin, -⟩ := hpre
  unfold RamRange at hres hao
  unfold TX.InputArea RamRange at hin
  simp only [shapeFull, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl) <;>
    simp [Sig.res, Sig.ao, Sig.inp, Sig.len, frameBytes, resultBytes, Layout.ramLo,
      Layout.ramHi, Layout.inputLo, Layout.inputHi, stackBytes, TX.stackBytes] at * <;> omega

/-! ## Memory a `Common` machine keeps from the entry -/

theorem Present.of_preserved {m m' : Machine} {a : Word} {n : Nat} (h : Present m a n)
    (hp : Preserved m m') : Present m' a n := fun j hj => hp.1 _ (h j hj)

theorem isSome_of_load {m : Machine} {a v : Word} (h : m.load a 8 = some v) :
    ∀ t < 8, (m.mem (a + BitVec.ofNat 64 t)).isSome := F1.present_of_load h (Nat.le_refl _)

theorem present16 {m : Machine} {a : Word} (h0 : (m.load a 8).isSome)
    (h8 : (m.load (a + 8) 8).isSome) : Present m a 16 := by
  obtain ⟨v0, e0⟩ := Option.isSome_iff_exists.mp h0
  obtain ⟨v8, e8⟩ := Option.isSome_iff_exists.mp h8
  intro j hj
  rcases Nat.lt_or_ge j 8 with h | h
  · exact isSome_of_load e0 j h
  · have := isSome_of_load e8 (j - 8) (by omega)
    rwa [show (8 : Word) = BitVec.ofNat 64 8 from rfl, F1.add_add_ofNat,
      show 8 + (j - 8) = j by omega] at this

/-- A byte outside DTF's owned memory and the allocator's private memory is as at the entry. -/
theorem same_of_apart {σ : Sig} {m : Machine} (hc : Common σ m) {a : Word}
    (hown : ¬ Owned σ a) (hpriv : ¬ σ.A.Priv σ.g.L a) : m.mem a = σ.m.mem a :=
  hc.2.2.2.2.2.2.2.1 a fun h => h.elim hown hpriv

theorem ao_same {σ : Sig} {m : Machine} (hc : Common σ m) {j : Nat} (hj : j < 16) :
    m.mem (σ.ao + BitVec.ofNat 64 j) = σ.m.mem (σ.ao + BitVec.ofNat 64 j) := by
  have hpre := hc.2.1
  have hsp := pre_sp hpre
  have hst := S_sub_toNat hpre (k := stackBytes) (Nat.le_refl _)
  obtain ⟨-, -, -, -, -, hao, -, -, -, -, -, -, -, -, -, -, d1, -, d3, -, d5, -, -, d8, -, -,
    hP⟩ := hpre
  have hr : InRange σ.ao 16 (σ.ao + BitVec.ofNat 64 j) := by
    unfold RamRange Layout.ramHi at hao
    simp only [InRange]; rw [toNat_add_ofNat (by simp [Sig.ao]; omega)]; omega
  refine same_of_apart hc (fun h => ?_) (hP _ (.inr (.inl hr)))
  unfold TX.Apart at d1 d3 d5 d8
  simp only [Sig.S, w] at hst
  rw [hst] at d5
  unfold Owned InRange at h; unfold InRange at hr
  simp only [Sig.S, w] at h
  rw [hst] at h
  simp only [Sig.res, Sig.ao, Sig.S, TX.scratch, BitVec.toNat_ofNat, Layout.extraParams,
    resultBytes, stackBytes, TX.stackBytes] at h hr d1 d3 d5 d8 hst ⊢
  unfold Layout.ramLo Layout.ramHi at *
  omega

theorem input_same {σ : Sig} {m : Machine} (hc : Common σ m) {j : Nat} (hj : j < σ.len) :
    m.mem (σ.inp + BitVec.ofNat 64 j) = σ.m.mem (σ.inp + BitVec.ofNat 64 j) := by
  have hpre := hc.2.1
  have hfit := pre_fit hpre ((σ.inp, σ.len), inR) (by simp [shapeFull])
  have hst := S_sub_toNat hpre (k := stackBytes) (Nat.le_refl _)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, d2, -, -, -, d6, -, -, d9, -,
    hP⟩ := hpre
  have hr : InRange σ.inp σ.len (σ.inp + BitVec.ofNat 64 j) := by
    simp only [InRange]; rw [toNat_add_ofNat (by simp at hfit; omega)]; omega
  refine same_of_apart hc (fun h => ?_) (hP _ (.inr (.inr (.inl hr))))
  unfold TX.Apart at d2 d6 d9
  simp only [Sig.S, w] at hst
  rw [hst] at d6
  unfold Owned InRange at h; unfold InRange at hr
  simp only [Sig.S, w] at h
  rw [hst] at h
  simp only [Sig.res, Sig.inp, Sig.len, Sig.S, TX.scratch, BitVec.toNat_ofNat, Layout.extraParams,
    resultBytes, stackBytes, TX.stackBytes] at h hr d2 d6 d9 hst ⊢
  omega

theorem input_present {σ : Sig} {m : Machine} (hc : Common σ m) {j : Nat} (hj : j < σ.len) :
    (m.mem (σ.inp + BitVec.ofNat 64 j)).isSome := by
  rw [input_same hc hj]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hb, hl, -⟩ := hc.2.1
  rw [hb j (by simp only [Sig.len] at hj hl ⊢; omega)]; rfl

theorem stack_present {σ : Sig} {m : Machine} (hc : Common σ m) {j : Nat} (hj : j < frameBytes) :
    (m.mem (σ.fr + BitVec.ofNat 64 j)).isSome := by
  have := hc.2.2.2.2.1 (stackBytes - frameBytes + j) (by
    unfold stackBytes TX.stackBytes frameBytes at *; omega)
  rwa [show σ.S - w stackBytes + BitVec.ofNat 64 (stackBytes - frameBytes + j) =
    σ.fr + BitVec.ofNat 64 j by
      simp only [Sig.fr, Sig.S, w]; unfold stackBytes TX.stackBytes frameBytes at *; bv_omega] at this

theorem common_vtable {σ : Sig} {m : Machine} (hc : Common σ m) :
    m.load (σ.ao + 8) 8 = some (w TX.vtable) := by
  rw [load_congr (m := σ.m) fun t ht => by
    rw [show σ.ao + 8 + BitVec.ofNat 64 t = σ.ao + BitVec.ofNat 64 (8 + t) by bv_omega]
    exact ao_same hc (by omega)]
  exact hc.2.1.2.2.2.2.2.2.2.2.1

theorem common_present {σ : Sig} {m : Machine} (hc : Common σ m) (r j : Nat) (hr : r < 4)
    (hj : j < (entryEnv m ((shapeFull σ).map (·.1))).size r) :
    (m.mem ((entryEnv m ((shapeFull σ).map (·.1))).base r + BitVec.ofNat 64 j)).isSome := by
  have hpre := hc.2.1
  simp only [entryEnv, Env.size, Env.base, shapeFull] at hj ⊢
  obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  all_goals simp at hj ⊢
  · exact stack_present hc hj
  · exact hc.2.2.2.2.2.1 j hj
  · rw [ao_same hc hj]
    obtain ⟨-, -, -, -, -, -, -, hao0, hao8, -⟩ := hpre
    exact present16 hao0 (Option.isSome_iff_exists.mpr ⟨_, hao8⟩) j hj
  · exact input_present hc hj

/-- A frame word is loadable. -/
theorem frame_load {σ : Sig} {m : Machine} (hc : Common σ m) {o : Nat} (ho : o + 8 ≤ frameBytes) :
    m.load (σ.fr + w o) 8 = some (TX.wordAt m (σ.fr + w o)) := by
  have hpre := hc.2.1
  have hsp := pre_sp hpre
  have hfr := fr_toNat hpre
  have ho' : (σ.fr + w o).toNat = σ.fr.toNat + o := toNat_add_ofNat (by
    unfold Layout.ramHi frameBytes at *; omega)
  have hr : Machine.readable (σ.fr + w o).toNat 8 = true := by
    rw [ho', hfr]; unfold frameBytes stackBytes TX.stackBytes at *
    simp [Machine.readable, Machine.inRange, Layout.ramLo, Layout.ramHi] at hsp ⊢; omega
  have hb : (readBytes m.mem (σ.fr + w o).toNat 8).isSome := readBytes_isSome_of fun t ht => by
    rw [ofNat_toNat_add]
    have := stack_present hc (j := o + t) (by omega)
    rwa [← F1.add_add_ofNat] at this
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hb
  have hl : m.load (σ.fr + w o) 8 = some (ofBytesLE bs) := by
    unfold Machine.load; rw [if_pos hr, hbs]; rfl
  rw [hl]; simp [TX.wordAt, hl]

/-! ## `Match` at a plain cut -/

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (x, y) :: l, a, b, h => by
    cases hxa : a == x with
    | true =>
      have := beq_iff_eq.mp hxa; subst this
      simp [List.lookup, hxa] at h; subst h; exact List.mem_cons_self
    | false =>
      simp [List.lookup, hxa] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- No register or frame slot of the shape is a slot base; frame slots are 8-aligned words in
the frame; registers are below 32. -/
def Shape.Fine (sh : Shape) : Bool :=
  sh.regs.all (fun p => decide (p.1 < 32) && p.2 != .slot) &&
    sh.slots.all (fun p => decide (p.1 % 8 = 0) && decide (p.1 + 8 ≤ frameBytes) && p.2 != .slot)

theorem env_base0 (sh : Shape) (σ : Sig) (m : Machine) : (envOf sh σ m).base 0 = σ.fr := by
  simp [envOf, entryEnv, Env.base, regionsOf]

theorem env_base1 (sh : Shape) (σ : Sig) (m : Machine) : (envOf sh σ m).base 1 = σ.res := by
  simp [envOf, entryEnv, Env.base, regionsOf]

theorem env_base2 (sh : Shape) (σ : Sig) (m : Machine) : (envOf sh σ m).base 2 = σ.ao := by
  simp [envOf, entryEnv, Env.base, regionsOf]

theorem env_base3 (sh : Shape) (σ : Sig) (m : Machine) : (envOf sh σ m).base 3 = σ.inp := by
  simp [envOf, entryEnv, Env.base, regionsOf]

/-- A shape value with a word evaluates to that word; a payload pointer to the register. -/
theorem val_reg {sh : Shape} {σ : Sig} {m : Machine} (hs : ShapeOk σ sh m) {i : Nat} {v : Val}
    (hi : i < 32) (hmem : (i, v) ∈ sh.regs) (hv : v ≠ .slot) :
    (v.sym (regVar i)).eval (envOf sh σ m) = m.reg (Fin.ofNat 32 i) := by
  have hw := hs.1 _ hmem
  cases v with
  | fr k => have h := hw _ rfl; simp only at h; rw [h]; simp [Val.sym, Sym.eval, env_base0, w]
  | res k => have h := hw _ rfl; simp only at h; rw [h]; simp [Val.sym, Sym.eval, env_base1, w]
  | ao k => have h := hw _ rfl; simp only at h; rw [h]; simp [Val.sym, Sym.eval, env_base2, w]
  | vt => have h := hw _ rfl; simp only at h; rw [h]; rfl
  | inp =>
    simp only [Val.sym, Sym.eval, BinOp.eval, env_base3, regVar]
    simp only [envOf, show ¬ 32 + i < 32 by omega, if_false, show 32 + i < 64 by omega, if_true,
      show 32 + i - 32 = i by omega]
    bv_omega
  | slot => exact absurd rfl hv

theorem match_plain {sh : Shape} {σ : Sig} {m : Machine} (hc : Common σ m) (hs : ShapeOk σ sh m)
    (hx : sh.extra = []) (hfine : sh.Fine = true) : Match (envOf sh σ m) sh.S m := by
  simp only [Shape.Fine, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at hfine
  obtain ⟨hfr, hfs⟩ := hfine
  refine ⟨by simp [Shape.S, entryState], fun i => ?_, fun r j hr hj => ?_, fun k hk t ht => ?_⟩
  · rw [Shape.S, entryState_reg]
    split
    · next h0 => simp [Sym.eval, Machine.reg, h0]
    · next h0 =>
      cases h : sh.ov i.val with
      | none => simp [Sym.eval, envOf, i.isLt]
      | some s =>
        simp only [Shape.ov, Option.map_eq_some_iff] at h
        obtain ⟨v, hl, rfl⟩ := h
        have hmem := lookup_mem hl
        have := val_reg hs i.isLt hmem (hfr _ hmem).2
        simpa using this
  · simp only [Shape.S, entryState, hx, List.append_nil, baseRegions, List.length_cons,
      List.length_nil] at hr
    have hreg : (envOf sh σ m).regions = (shapeFull σ).map (·.1) := regionsOf_base hx σ m
    have hp := common_present hc r j hr (by
      simpa [Env.size, entryEnv, envOf, regionsOf_base hx] using hj)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hp
    simp only [memByte, Shape.S, entryState, List.find?_nil, Env.byte0, envOf, entryEnv,
      Env.base, regionsOf_base hx] at hb ⊢
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at hb ⊢
    rw [hb]; rfl
  · simp only [Shape.S, entryState, Shape.known, List.mem_cons, List.mem_map] at hk
    rcases hk with rfl | ⟨⟨o, v⟩, hov, rfl⟩
    · have := load_bytes (common_vtable hc) (Nat.le_refl _) t ht
      simp only [vtableKnown, Env.byte0, envOf, entryEnv, regionsOf_base hx, shapeFull,
        List.map_cons, List.getD_cons_succ, List.getD_cons_zero, Sym.eval]
      rw [← F1.add_add_ofNat, show BitVec.ofNat 64 8 = (8 : Word) from rfl, this]; rfl
    · obtain ⟨⟨h8, hle⟩, hv⟩ := hfs _ hov
      simp only at h8 hle hv ⊢
      have hl := frame_load hc hle
      have hbyte := load_bytes hl (Nat.le_refl _) t ht
      have ha : σ.fr + BitVec.ofNat 64 (o + t) = σ.fr + w o + BitVec.ofNat 64 t := by
        rw [F1.add_add_ofNat]
      simp only [Env.byte0, envOf, entryEnv, regionsOf_base hx, shapeFull, List.map_cons,
        List.getD_cons_zero]
      rw [ha, hbyte]
      simp only [Option.getD_some]
      congr 1
      cases v with
      | inp =>
        simp only [Val.sym, Sym.eval, BinOp.eval, Env.base, envOf, entryEnv, regionsOf_base hx,
          shapeFull, List.map_cons, List.getD_cons_succ, List.getD_cons_zero, slotVar]
        simp only [show ¬ 64 + o / 8 < 32 by omega, show ¬ 64 + o / 8 < 64 by omega, if_false,
          show 64 + o / 8 - 64 = o / 8 by omega, show 8 * (o / 8) = o by omega]
        bv_omega
      | slot => exact absurd rfl hv
      | _ =>
        have := hs.2 _ hov _ rfl
        rw [hl] at this
        simp only [Option.some.injEq] at this
        rw [this]
        simp [Val.sym, Val.word, Sym.eval, Env.base, entryEnv, regionsOf_base hx, shapeFull, w]

/-- The cut lemma of a cut reached only by jumps and branches, with no extra region. -/
theorem cut_plain (d : CutData) (hpc : d.pc ≠ entry) (hs : d.site = none)
    (hx : d.shape.extra = []) (hfine : d.shape.Fine = true) : CutOK vcPlan (mkCut d) := by
  intro σ m hA
  simp only [mkCut, if_neg hpc, ACut, hs, reduceCtorEq, false_and, exists_false,
    or_false] at hA
  obtain ⟨-, hpcm, hc, hsh, -⟩ := hA
  have hwf : Env.WF (envOf d.shape σ m) d.shape.S := by
    have := pre_wf hc.2.1 m d.shape.ov d.shape.known
    rw [Shape.S, hx, List.append_nil]
    exact Env.WF.of_regions this (regionsOf_base hx σ m)
  exact ⟨hwf, match_plain hc hsh hx hfine, hc.2.2.1, hpcm⟩

end ZesuExec.Fn.DTF
