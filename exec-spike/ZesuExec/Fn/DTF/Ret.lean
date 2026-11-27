import ZesuExec.Fn.DTF.Lemmas

/-!
# DTF: cut lemmas of the call return sites (programme plan S7 step 4)

`cut_ret`: the cut lemma of a return site whose callee writes only DTF's stack below the save
area, the outcome slot it is handed, or the allocator's memory (`decodeItem`, `alloc`, `remap`).
`ret_common` is "`Common` survives the call" per callee kind (TX's `common_ret`/`common_f2` are the
model); `RetFine` (checked by `decide` per cut) says the cut's pointer-valued registers are
callee-saved and held the same value at the call, and its pointer-valued frame slots held the same
value at the call and lie outside what the callee writes (`Kind.Keeps`).

Not covered (their callee writes memory the assertions do not locate yet, `OPEN/DTF/CUTS.md`
groups 1 and 3): `memcpy` (the destination), `free` (the freed block must be one of DTF's), F1 and
F4 (the list buffer), TX (the returned blocks are not stated to come from `Priv g.L`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## Separation from the entry's `Pre` -/

theorem owned_not_priv {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {a : Word} (h : Owned σ a) :
    ¬ σ.A.Priv σ.g.L a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hP⟩ := hpre
  rcases h with h | h | h
  · exact hP a (.inl h)
  · exact hP a (.inr (.inr (.inr (.inl h))))
  · exact hP a (.inr (.inr (.inr (.inr h))))

/-- `Priv` of DTF's live list lies in `Priv g.L` (`arena_split`). -/
theorem priv_sub {σ : Sig} {m : Machine} {L X : List (Word × Nat)} (hpre : Pre σ.A σ.g σ.m)
    (hlive : Live σ m L X) {a : Word} (h : σ.A.Priv L a) : σ.A.Priv σ.g.L a := by
  have hheap0 : σ.A.Heap σ.g.L σ.m := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have harena := (σ.A.arena_split L m a hlive.1).mpr (.inl h)
  rcases (σ.A.arena_split σ.g.L σ.m a hheap0).mp harena with h' | ⟨b, hb, hin⟩
  · exact h'
  · exact absurd ⟨b, hlive.2.1.symm.subset (List.mem_append_left _ hb), hin⟩
      (σ.A.priv_not_live L a h)

/-! ## What a callee may change -/

/-- Memory a callee may change: DTF's own or the allocator's, never the save area. -/
def CallR (σ : Sig) (a : Word) : Prop :=
  (Owned σ a ∨ σ.A.Priv σ.g.L a) ∧ ¬ InRange (σ.S - w 104) 104 a

/-- A range of DTF's stack below the save area. -/
theorem stack_R {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {lo : Word} {n : Nat} {a : Word}
    (hlo : σ.S.toNat - stackBytes ≤ lo.toNat) (hhi : lo.toNat + n + 104 ≤ σ.S.toNat)
    (h : InRange lo n a) : CallR σ a ∧ ¬ σ.A.Priv σ.g.L a := by
  have h1 := S_sub_toNat hpre (k := 104) (by decide)
  have h2 := S_sub_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have hs : InRange (σ.S - w stackBytes) stackBytes a := by
    simp only [InRange, h2] at h ⊢; omega
  refine ⟨⟨.inl (.inr (.inl hs)), fun hs' => ?_⟩, owned_not_priv hpre (.inr (.inl hs))⟩
  simp only [InRange, h1] at h hs'; omega

theorem priv_R {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {a : Word} (h : σ.A.Priv σ.g.L a) :
    CallR σ a := by
  refine ⟨.inr h, fun hs => owned_not_priv hpre (.inr (.inl ?_)) h⟩
  have h1 := S_sub_toNat hpre (k := 104) (by decide)
  have h2 := S_sub_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have := pre_sp hpre
  simp only [InRange, h1, h2] at hs ⊢
  unfold stackBytes TX.stackBytes at *; omega

/-- `Live` survives a call that leaves `Priv L` alone. -/
theorem live_keep {σ : Sig} {mc m : Machine} {L X : List (Word × Nat)} (hlive : Live σ mc L X)
    {R : Word → Prop} (hso : SameOutside R mc m) (hp : Preserved mc m)
    (hR : ∀ a, R a → ¬ σ.A.Priv L a) : Live σ m L X :=
  ⟨σ.A.heap_frame' L mc m hlive.1 (fun a h => hso a fun hr => hR a hr h) hp, hlive.2.1,
    hlive.2.2⟩

/-- `Common` survives a call whose writes `R` are `CallR`, given the live list after it. -/
theorem common_ret {σ : Sig} {mc m : Machine} (hc : Common σ mc) (hret : Returns mc m)
    (hp : Preserved mc m) {R : Word → Prop} (hso : SameOutside R mc m)
    (hR : ∀ a, R a → CallR σ a) (hlive : ∃ L X, Live σ m L X) : Common σ m := by
  obtain ⟨hpc, hpre, hro, hsv, hst, hres, hscr, hfr, -⟩ := hc
  have hsp := pre_sp hpre
  refine ⟨hpc, hpre, RodataLoaded.preserved hro hp fun _ _ hb => F1.zesu_rodata_low hb,
    fun k hk => ?_, Present.of_preserved hst hp, Present.of_preserved hres hp,
    Present.of_preserved hscr hp, fun a ha => (hso a fun hr => ha (hR a hr).1).trans (hfr a ha),
    hlive⟩
  rw [load_congr fun t ht => hso _ fun h => (hR _ h).2 ?_]
  · exact hsv k hk
  · have h1 := S_sub_toNat hpre (k := 104) (by decide)
    have h2 := S_sub_toNat hpre (k := 8 * (k + 1)) (by unfold stackBytes TX.stackBytes; omega)
    simp only [InRange, h1]
    rw [toNat_add_ofNat (by rw [h2]; unfold Layout.ramHi at hsp; omega), h2]
    unfold stackBytes TX.stackBytes at hsp
    omega

/-- A frame word survives a call whose writes miss it. -/
theorem frame_keep {σ : Sig} {mc m : Machine} (hpre : Pre σ.A σ.g σ.m) {R : Word → Prop}
    (hso : SameOutside R mc m) {o : Nat} (ho : o + 8 ≤ frameBytes)
    (hR : ∀ a, R a → a.toNat < σ.fr.toNat + o ∨ σ.fr.toNat + o + 8 ≤ a.toNat) :
    m.load (σ.fr + w o) 8 = mc.load (σ.fr + w o) 8 := by
  have hfr := fr_toNat hpre
  have hsp := pre_sp hpre
  unfold Layout.ramHi frameBytes stackBytes TX.stackBytes at *
  have hlt : (σ.fr + w o).toNat = σ.fr.toNat + o := toNat_add_ofNat (by omega)
  refine load_congr fun t ht => hso _ fun hr => ?_
  have := toNat_add_ofNat (b := σ.fr + w o) (j := t) (by omega)
  rcases hR _ hr with h | h <;> omega

theorem fr_add_toNat {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {k : Nat} (hk : k ≤ frameBytes) :
    (σ.fr + w k).toNat = σ.fr.toNat + k := by
  have hfr := fr_toNat hpre
  have hsp := pre_sp hpre
  unfold Layout.ramHi frameBytes stackBytes TX.stackBytes at *
  exact toNat_add_ofNat (by omega)

/-- The 16 bytes a leaf callee may use below DTF's frame (`sp = fr` at every call). -/
theorem below_fr_toNat {σ : Sig} (hpre : Pre σ.A σ.g σ.m) :
    (σ.fr + w 0 - 16).toNat = σ.fr.toNat - 16 := by
  have h := S_sub_toNat hpre (k := frameBytes + 16) (by unfold stackBytes frameBytes; decide)
  have hfr := fr_toNat hpre
  rw [show σ.fr + w 0 - 16 = σ.S - w (frameBytes + 16) by
    simp only [Sig.fr, w, frameBytes]; bv_omega, h, hfr]
  omega

/-! ## Per callee kind -/

/-- The frame offset a register of the call site's shape holds (`fr k`), if any. -/
def regFr (s : Site) (i : Nat) : Option Nat :=
  match s.shape.regs.lookup i with
  | some (.fr k) => some k
  | _ => none

theorem regFr_spec {s : Site} {i k : Nat} (h : regFr s i = some k) :
    s.shape.regs.lookup i = some (.fr k) := by
  unfold regFr at h
  split at h
  · next heq => cases h; exact heq
  · cases h

/-- The kinds `ret_common` covers, with what it needs of the call site: `sp = fr`, and for
`decodeItem` the outcome slot `a0 = fr + k` below the save area. -/
def Kind.SiteFine : Kind → Site → Bool
  | .f2, s => regFr s 2 == some 0 &&
      (match regFr s 10 with | some k => decide (k + 40 + 104 ≤ frameBytes) | none => false)
  | .alloc, s | .remap, s => regFr s 2 == some 0
  | _, _ => false

/-- The frame word at `o` survives the call. -/
def Kind.Keeps : Kind → Site → Nat → Bool
  | .f2, s, o => match regFr s 10 with
    | some k => decide (o + 8 ≤ k ∨ k + 40 ≤ o)
    | none => false
  | .alloc, _, _ | .remap, _, _ => true
  | _, _, _ => false

theorem sp_fr {σ : Sig} {s : Site} {x : Idx} {r : Nat} {mc : Machine} (hsite : SiteA s r σ x mc)
    (h : regFr s 2 = some 0) : mc.reg 2 = σ.fr + w 0 :=
  hsite.2.2.1.1 _ (lookup_mem (regFr_spec h)) _ rfl

/-- What `ret_common` gives at the return machine `m` of the call from `mc`. -/
def RetOut (σ : Sig) (k : Kind) (s : Site) (mc m : Machine) : Prop :=
  Returns mc m ∧ Common σ m ∧ ∀ o, o + 8 ≤ frameBytes → k.Keeps s o = true →
    m.load (σ.fr + w o) 8 = mc.load (σ.fr + w o) 8

theorem ret_f2 {s : Site} {σ : Sig} {x : Idx} {r : Nat} {mc m : Machine}
    (hk : Kind.SiteFine .f2 s = true) (hsite : SiteA s r σ x mc) (hq : F2.Post mc m)
    (hp : Preserved mc m) : RetOut σ .f2 s mc m := by
  have hc := hsite.2.1
  have hpre := hc.2.1
  have hfr := fr_toNat hpre
  have hsp := pre_sp hpre
  obtain ⟨L, X, hlive⟩ := hc.2.2.2.2.2.2.2.2
  simp only [Kind.SiteFine, Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨h2, h10⟩ := hk
  cases h10' : regFr s 10 with
  | none => simp [h10'] at h10
  | some ka =>
    simp only [h10', decide_eq_true_eq] at h10
    have r10 : mc.reg 10 = σ.fr + w ka := hsite.2.2.1.1 _ (lookup_mem (regFr_spec h10')) _ rfl
    have r2 := sp_fr hsite h2
    have e10 := fr_add_toNat hpre (k := ka) (by omega)
    have e2 := below_fr_toNat hpre
    obtain ⟨hret, hso, -⟩ := hq
    unfold frameBytes stackBytes TX.stackBytes Layout.ramLo at *
    have hR : ∀ a, (InRange (mc.reg 10) 40 a ∨ InRange (mc.reg 2 - 16) 16 a) →
        CallR σ a ∧ ¬ σ.A.Priv σ.g.L a := by
      rintro a (h | h)
      · rw [r10] at h
        exact stack_R hpre (by rw [e10]; unfold stackBytes TX.stackBytes; omega)
          (by rw [e10]; omega) h
      · rw [r2] at h
        exact stack_R hpre (by rw [e2]; unfold stackBytes TX.stackBytes; omega)
          (by rw [e2]; omega) h
    refine ⟨hret, common_ret hc hret hp hso (fun a h => (hR a h).1)
      ⟨L, X, live_keep hlive hso hp fun a h hl => (hR a h).2 (priv_sub hpre hlive hl)⟩,
      fun o ho hko => ?_⟩
    simp only [Kind.Keeps, h10', decide_eq_true_eq] at hko
    refine frame_keep hpre hso ho fun a h => ?_
    rcases h with h | h
    · rw [r10] at h; simp only [InRange, e10] at h; omega
    · rw [r2] at h; simp only [InRange, e2] at h; omega

/-- A frame word is DTF's stack, which the allocator's memory misses. -/
theorem frame_not_priv {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {o : Nat} (ho : o + 8 ≤ frameBytes)
    {a : Word} (h : σ.A.Priv σ.g.L a) : a.toNat < σ.fr.toNat + o ∨ σ.fr.toNat + o + 8 ≤ a.toNat := by
  have hfr := fr_toNat hpre
  have h2 := S_sub_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have hsp := pre_sp hpre
  refine Classical.byContradiction fun hn => owned_not_priv hpre (.inr (.inl ?_)) h
  simp only [InRange, h2]
  unfold frameBytes stackBytes TX.stackBytes at *
  omega

theorem ret_alloc {s : Site} {σ : Sig} {x : Idx} {r : Nat} {mc m : Machine}
    (hkd : s.kind = .alloc) (hk : Kind.SiteFine .alloc s = true) (hsite : SiteA s r σ x mc)
    (hq : allocPost σ.A x.1 mc m) (hp : Preserved mc m) : RetOut σ .alloc s mc m := by
  have hc := hsite.2.1
  have hpre := hc.2.1
  have hfr := fr_toNat hpre
  have hix := hsite.2.2.2.2.2
  rw [hkd] at hix
  obtain ⟨hapre, X, hlive⟩ := hix
  simp only [Kind.SiteFine, beq_iff_eq] at hk
  have r2 := sp_fr hsite hk
  have e2 := below_fr_toNat hpre
  obtain ⟨hret, hso, hnew⟩ := hq
  have hRs : ∀ a, InRange (mc.reg 2 - 16) 16 a → CallR σ a ∧ ¬ σ.A.Priv σ.g.L a := by
    intro a h
    rw [r2] at h
    have hsp := pre_sp hpre
    unfold frameBytes stackBytes TX.stackBytes Layout.ramLo at *
    exact stack_R hpre (by rw [e2]; unfold stackBytes TX.stackBytes; omega) (by rw [e2]; omega) h
  have hlive' : ∃ L X, Live σ m L X := by
    rcases hnew with ⟨-, hh⟩ | ⟨-, hh, hram, -, hin, -⟩
    · exact ⟨x.1, X, hh, hlive.2.1, hlive.2.2⟩
    · refine ⟨x.1 ++ [(m.reg 10, (mc.reg 11).toNat)], X ++ [(m.reg 10, (mc.reg 11).toNat)], hh,
        by rw [← List.append_assoc]; exact hlive.2.1.append_right _, fun b hb => ?_⟩
      rcases List.mem_append.mp hb with hb | hb
      · exact hlive.2.2 b hb
      · simp only [List.mem_singleton] at hb
        subst hb
        exact ⟨hapre.2.1, hram, fun a ha => priv_sub hpre hlive (hin a ha)⟩
  refine ⟨hret, common_ret hc hret hp hso (fun a h => ?_) hlive', fun o ho _ => ?_⟩
  · rcases h with h | h
    · exact priv_R hpre (priv_sub hpre hlive h)
    · exact (hRs a h).1
  · refine frame_keep hpre hso ho fun a h => ?_
    rcases h with h | h
    · exact frame_not_priv hpre ho (priv_sub hpre hlive h)
    · have hsp := pre_sp hpre
      unfold frameBytes stackBytes TX.stackBytes Layout.ramLo at *
      rw [r2] at h; simp only [InRange, e2] at h; omega

theorem ret_remap {s : Site} {σ : Sig} {x : Idx} {r : Nat} {mc m : Machine}
    (hk : Kind.SiteFine .remap s = true) (hsite : SiteA s r σ x mc) (hq : F0.Post mc m)
    (hp : Preserved mc m) : RetOut σ .remap s mc m := by
  have hc := hsite.2.1
  have hpre := hc.2.1
  have hfr := fr_toNat hpre
  obtain ⟨L, X, hlive⟩ := hc.2.2.2.2.2.2.2.2
  simp only [Kind.SiteFine, beq_iff_eq] at hk
  have r2 := sp_fr hsite hk
  have e2 := below_fr_toNat hpre
  obtain ⟨hret, -, hso⟩ := hq
  have hR : ∀ a, InRange (mc.reg 2 - 16) 16 a → CallR σ a ∧ ¬ σ.A.Priv σ.g.L a := by
    intro a h
    rw [r2] at h
    have hsp := pre_sp hpre
    unfold frameBytes stackBytes TX.stackBytes Layout.ramLo at *
    exact stack_R hpre (by rw [e2]; unfold stackBytes TX.stackBytes; omega) (by rw [e2]; omega) h
  refine ⟨hret, common_ret hc hret hp hso (fun a h => (hR a h).1)
    ⟨L, X, live_keep hlive hso hp fun a h hl => (hR a h).2 (priv_sub hpre hlive hl)⟩,
    fun o ho _ => frame_keep hpre hso ho fun a h => ?_⟩
  have hsp := pre_sp hpre
  unfold frameBytes stackBytes TX.stackBytes Layout.ramLo at *
  rw [r2] at h; simp only [InRange, e2] at h; omega

/-- "`Common` survives the call" for the kinds of `Kind.SiteFine`, with the frame words of
`Kind.Keeps`. -/
theorem ret_common {s : Site} {σ : Sig} {x : Idx} {r : Nat} {mc m : Machine}
    (hk : s.kind.SiteFine s = true) (hsite : SiteA s r σ x mc)
    (hpost : (calleeOf s.kind).Post σ x mc m) : RetOut σ s.kind s mc m := by
  obtain ⟨hq, hp⟩ := hpost
  revert hk hq
  cases hkd : s.kind <;> intro hk hq
  case f2 => exact ret_f2 hk hsite hq hp
  case alloc => exact ret_alloc hkd hk hsite hq hp
  case remap => exact ret_remap hk hsite hq hp
  all_goals simp [Kind.SiteFine] at hk

/-! ## The cut lemma of a return site -/

def Val.isWord : Val → Bool
  | .inp | .slot => false
  | _ => true

theorem Val.isWord_of {σ : Sig} {v : Val} {a : Word} (h : v.word σ = some a) :
    v.isWord = true := by
  cases v <;> simp_all [Val.word, Val.isWord]

/-- The return site's pointer-valued registers are callee-saved and held the same value at the
call; its pointer-valued frame slots held the same value at the call and survive the callee. -/
def RetFine (d : CutData) (s : Site) : Bool :=
  d.shape.regs.all (fun p => !p.2.isWord ||
    (decide (p ∈ s.shape.regs) && decide (Fin.ofNat 32 p.1 ∈ calleeSaved))) &&
  d.shape.slots.all (fun p => !p.2.isWord || (decide (p ∈ s.shape.slots) && s.kind.Keeps s p.1))

/-- The return-site checks of `cut_ret`, by `decide` per cut. -/
def RetCheck (d : CutData) : Bool :=
  match d.site with
  | some s => s.kind.SiteFine s && RetFine d s
  | none => false

/-- The cut lemma of a return site (not also a jump target) of a `Kind.SiteFine` callee. -/
theorem cut_ret (d : CutData) (hpc : d.pc ≠ entry) (hpl : d.plain = false)
    (hx : d.shape.extra = []) (hfine : d.shape.Fine = true) (hck : RetCheck d = true)
    (hra : (w d.pc &&& ~~~(1 : Word)).toNat = d.pc) : CutOK vcPlan (mkCut d) := by
  intro σ m hA
  cases hs : d.site with
  | none => simp [RetCheck, hs] at hck
  | some s =>
  simp only [RetCheck, hs, Bool.and_eq_true] at hck
  obtain ⟨hk, hrf⟩ := hck
  simp only [mkCut, if_neg hpc, ACut, hs, hpl, Bool.false_eq_true, false_and, false_or,
    Option.some.injEq, exists_eq_left'] at hA
  obtain ⟨mc, x, hsite, hpost⟩ := hA
  obtain ⟨hret, hc, hkeep⟩ := ret_common hk hsite hpost
  have hfine' := hfine
  simp only [Shape.Fine, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hfine'
  simp only [RetFine, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hrf
  obtain ⟨hrr, hrs⟩ := hrf
  have hsh : ShapeOk σ d.shape m := by
    constructor
    · intro p hp v hv
      rcases hrr p hp with h | ⟨hmem, hcs⟩
      · rw [Val.isWord_of hv] at h; cases h
      · rw [hret.2 _ hcs]; exact hsite.2.2.1.1 p hmem v hv
    · intro p hp v hv
      rcases hrs p hp with h | ⟨hmem, hke⟩
      · rw [Val.isWord_of hv] at h; cases h
      · rw [hkeep p.1 (hfine'.2 p hp).1.2 hke]
        exact hsite.2.2.1.2 p hmem v hv
  have hpcm : m.pc.toNat = d.pc := by rw [hret.1, hsite.1, hra]
  have hwf : Env.WF (envOf d.shape σ m) d.shape.S := by
    have := pre_wf hc.2.1 m d.shape.ov d.shape.known
    rw [Shape.S, hx, List.append_nil]
    exact Env.WF.of_regions this (regionsOf_base hx σ m)
  exact ⟨hwf, match_plain hc.avail hsh hx hfine, hc.2.2.1, hpcm⟩

end ZesuExec.Fn.DTF
