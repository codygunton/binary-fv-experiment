import ZesuExec.Fn.DTF.Ret

/-!
# DTF: facts at a cut and at the end of a leaf (programme plan S7 step 4)

The pieces of the generic leaf theorem `leaf_gen` (`Gen.lean`): a cut's `Facts` from its
assertion (`facts_of_A`; a return site by `SrcOk`: its `rest` locations are callee-saved registers
or frame words the callee keeps, its arms those of the call); locations as symbolic values of a
state (`Loc.sym`, `loc_word_eval`); `Common` at the end of a leaf that writes only frame words
below the save area (`common_leaf`); and the target checks `shapeHolds`, `armsKeep`,
`budgetKeep`, `noExtra`.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## Facts at a cut -/

/-- A return site's `rest` location the call keeps: at the call site, and callee-saved or kept by
the callee. -/
def retKeep (s : Site) (r : RestLoc) : Bool :=
  decide (r ∈ s.rest) && match r.loc with
    | .reg i => decide (Fin.ofNat 32 i ∈ calleeSaved)
    | .slot o => decide (o + 8 ≤ frameBytes) && s.kind.Keeps s o

/-- The `rest` locations a cut's assertion gives: all of them at a cut reached by jumps, the kept
ones at a return site (a callee such as TX moves `rest` on by an item it may not have parsed). -/
def kRest (d : CutData) : List RestLoc :=
  match d.site with
  | none => d.rest
  | some s => d.rest.filter (retKeep s)

theorem kRest_sub {d : CutData} {r : RestLoc} (h : r ∈ kRest d) : r ∈ d.rest := by
  unfold kRest at h
  split at h
  · exact h
  · exact (List.mem_filter.mp h).1

/-- The items a cut's assertion says are checked: its own count at a cut reached by jumps, the call
site's at a return site (a callee such as TX moves `rest` on by an item it may not have accepted),
the smaller at a cut that is both. -/
def srcChk (d : CutData) : Nat :=
  match d.site with
  | none => chkCount d.rest
  | some s => if d.plain then min (chkCount d.rest) (chkCount s.rest) else chkCount s.rest

theorem ChecksOk.mono {σ : Sig} {k k' : Nat} (h : ChecksOk σ k) (hk : k' ≤ k) : ChecksOk σ k' :=
  fun i hi => h i (by omega)

/-- What a cut other than the entry knows at its machine. -/
structure Facts (d : CutData) (σ : Sig) (m : Machine) : Prop where
  common : Common σ m
  shape : ShapeOk σ d.shape m
  arms : ArmOk σ d.arms
  rest : RestOk σ m (kRest d)
  chk : ChecksOk σ (srcChk d)

def Loc.fine : Loc → Bool
  | .reg i => decide (i < 32)
  | .slot o => decide (o + 8 ≤ frameBytes)

/-- `arms` only widen (or the target is before the dispatch). -/
def armsKeep (a a' : List Nat) : Bool := a'.isEmpty || (!a.isEmpty && a.all (a'.contains ·))

theorem armOk_keep {σ : Sig} {a a' : List Nat} (h : armsKeep a a' = true) (ha : ArmOk σ a) :
    ArmOk σ a' := by
  unfold armsKeep at h
  simp only [Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true, List.contains_iff_mem] at h
  rcases h with h | ⟨hne, hsub⟩
  · exact .inl h
  · rcases ha with ha | ha
    · exact absurd ha hne
    · exact .inr (hsub _ ha)

/-- All of a return site's `rest` locations are kept by the call. -/
def restRet (d : CutData) (s : Site) : Bool := d.rest.all (retKeep s)

/-- The return-site branch of a cut's assertion gives its `Facts`. -/
def SrcOk (d : CutData) : Bool :=
  match d.site with
  | none => true
  | some s => RetCheck d && d.shape.Fine && armsKeep s.arms d.arms

theorem facts_of_ret {d : CutData} {s : Site} {σ : Sig} {m : Machine} (hs : d.site = some s)
    (hck : SrcOk d = true) (hA : RetA s d.pc σ m) : Facts d σ m := by
  simp only [SrcOk, hs, RetCheck, Bool.and_eq_true] at hck
  obtain ⟨⟨⟨hk, hrf⟩, hfine⟩, harms⟩ := hck
  obtain ⟨mc, x, hsite, hpost⟩ := hA
  obtain ⟨hret, hc, hkeep⟩ := ret_common hk hsite hpost
  simp only [Shape.Fine, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hfine
  simp only [RetFine, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hrf
  obtain ⟨hrr', hrs⟩ := hrf
  refine ⟨hc, ⟨fun p hp v hv => ?_, fun p hp v hv => ?_⟩, armOk_keep harms hsite.2.2.2.1,
    fun r hr => ?_, hsite.2.2.2.2.2.2.2.1.mono (by simp only [srcChk, hs]; split <;> omega)⟩
  · rcases hrr' p hp with h | ⟨hmem, hcs⟩
    · rw [Val.isWord_of hv] at h; cases h
    · rw [hret.2 _ hcs]; exact hsite.2.2.1.1 p hmem v hv
  · rcases hrs p hp with h | ⟨hmem, hke⟩
    · rw [Val.isWord_of hv] at h; cases h
    · rw [hkeep p.1 (hfine.2 p hp).1.2 hke]
      exact hsite.2.2.1.2 p hmem v hv
  · simp only [kRest, hs, List.mem_filter, retKeep, Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨-, hmem, hloc⟩ := hr
    obtain ⟨c, hskip, hw⟩ := hsite.2.2.2.2.1 r hmem
    refine ⟨c, hskip, ?_⟩
    rw [← hw]
    revert hloc
    cases r.loc with
    | reg i =>
      intro hloc
      simp only [decide_eq_true_eq] at hloc
      simp only [Loc.word]
      exact hret.2 _ hloc
    | slot o =>
      intro hloc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hloc
      simp only [Loc.word, TX.wordAt]
      rw [hkeep o hloc.1 hloc.2]

theorem facts_of_A {d : CutData} {σ : Sig} {m : Machine} (hpc : d.pc ≠ entry)
    (hck : SrcOk d = true) (hA : (mkCut d).A σ m) : Facts d σ m := by
  simp only [mkCut, if_neg hpc, ACut] at hA
  rcases hA with ⟨hpl, -, hc, hs, ha, hr, -, -, hchk⟩ | ⟨s, hs, hret⟩
  · refine ⟨hc, hs, ha, fun r h => hr r (kRest_sub h), hchk.mono ?_⟩
    unfold srcChk; split
    · exact Nat.le_refl _
    · rw [if_pos hpl]; omega
  · exact facts_of_ret hs hck hret

/-! ## Locations as symbolic values -/

/-- The symbolic value of a location in `S` (a frame word: region 0). -/
def Loc.sym (S : SState) : Loc → Sym
  | .reg i => S.reg i
  | .slot o => readConst S 0 o 8

theorem envOf_size0 (sh : Shape) (σ : Sig) (m : Machine) : (envOf sh σ m).size 0 = frameBytes := by
  simp [envOf, entryEnv, Env.size, regionsOf]

/-- A state whose regions are the base regions, without region 4. -/
def BaseRegs (S : SState) : Prop := S.regions = baseRegions

theorem loc_word_eval {sh : Shape} {σ : Sig} {m mm : Machine} {S : SState}
    (hwf : Env.WF (envOf sh σ m) S) (hm : Match (envOf sh σ m) S mm) (hS : BaseRegs S)
    {loc : Loc} (hf : loc.fine = true) : loc.word σ mm = (loc.sym S).eval (envOf sh σ m) := by
  cases loc with
  | reg i =>
    simp only [Loc.fine, decide_eq_true_eq] at hf
    have := hm.regs ⟨i, hf⟩
    simp only [Loc.word, Loc.sym]
    have e : (Fin.ofNat 32 i : Fin 32) = ⟨i, hf⟩ := Fin.ext (by simp [Nat.mod_eq_of_lt hf])
    rw [e, ← this]
  | slot o =>
    simp only [Loc.fine, decide_eq_true_eq] at hf
    have hR : S.regions[0]? = some frameR := by rw [hS]; rfl
    have := load_cst hwf hm hR (by rw [envOf_size0]; exact hf)
    rw [env_base0] at this
    simp only [Loc.word, Loc.sym, TX.wordAt, w, this, Option.getD_some]

/-- A shape value with a word evaluates to it. -/
theorem Val.sym_eval {sh : Shape} {σ : Sig} {m : Machine} {v : Val} {a : Word} (n : Nat)
    (h : v.word σ = some a) : (v.sym n).eval (envOf sh σ m) = a := by
  cases v with
  | fr k => simp only [Val.word, Option.some.injEq] at h; subst h
            simp [Val.sym, Sym.eval, env_base0, w]
  | res k => simp only [Val.word, Option.some.injEq] at h; subst h
             simp [Val.sym, Sym.eval, env_base1, w]
  | ao k => simp only [Val.word, Option.some.injEq] at h; subst h
            simp [Val.sym, Sym.eval, env_base2, w]
  | vt => simp only [Val.word, Option.some.injEq] at h; subst h; rfl
  | inp => simp [Val.word] at h
  | slot => simp [Val.word] at h

/-! ## The leaf's machine -/

/-- Every write of `S` is a frame word below the save area or in the result. -/
def writesLow (S : SState) : Bool :=
  S.mem.all fun w => (w.r == 0 && decide (w.off + w.n ≤ frameBytes - 104)) || w.r == 1

theorem baseRegs_shape {sh : Shape} (hx : sh.extra = []) : BaseRegs sh.S := by
  simp [BaseRegs, Shape.S, entryState, hx]

/-- A frame byte no write covers is the source machine's. -/
theorem frame_byte_keep' {sh : Shape} {σ : Sig} {m m' : Machine} {S : SState} (hc : Avail σ m)
    (hm' : Match (envOf sh σ m) S m') (h0 : 0 < S.regions.length) {j : Nat} (hj : j < frameBytes)
    (hnc : S.mem.find? (·.covers 0 j) = none) :
    m'.mem (σ.fr + BitVec.ofNat 64 j) = m.mem (σ.fr + BitVec.ofNat 64 j) := by
  have h := hm'.mem 0 j h0 (by rw [envOf_size0]; exact hj)
  rw [env_base0] at h
  rw [h]
  simp only [memByte, hnc, Env.byte0, envOf, entryEnv, regionsOf]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (stack_present hc hj)
  simp [hb]

theorem frame_byte_keep {sh : Shape} {σ : Sig} {m m' : Machine} {S : SState} (hc : Avail σ m)
    (hm' : Match (envOf sh σ m) S m') (hS : BaseRegs S) {j : Nat} (hj : j < frameBytes)
    (hnc : S.mem.find? (·.covers 0 j) = none) :
    m'.mem (σ.fr + BitVec.ofNat 64 j) = m.mem (σ.fr + BitVec.ofNat 64 j) :=
  frame_byte_keep' hc hm' (by rw [hS]; decide) hj hnc

theorem writesLow_nocover {S : SState} (h : writesLow S = true) {j : Nat}
    (hj : frameBytes - 104 ≤ j) : S.mem.find? (·.covers 0 j) = none := by
  rw [List.find?_eq_none]
  intro w hw hcov
  simp only [writesLow, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  have := h w hw
  simp only [Write.covers, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcov
  omega

/-- An address of a writable base region is DTF's own. -/
theorem inWritable_owned {sh : Shape} {σ : Sig} {m : Machine} {S : SState} (hpre : Pre σ.A σ.g σ.m)
    (hS : BaseRegs S) {a : Word} (h : InWritable (envOf sh σ m) S a) :
    Owned σ a ∧ ∃ r j, r < 2 ∧ j < (envOf sh σ m).size r ∧ a = (envOf sh σ m).base r + BitVec.ofNat 64 j := by
  obtain ⟨r, R, j, hR, hwr, hj, rfl⟩ := h
  rw [hS] at hR
  have hr : r < 2 := by
    rcases r with _ | _ | _ | _ | r
    · omega
    · omega
    · simp [baseRegions, aoR] at hR; subst hR; simp at hwr
    · simp [baseRegions, inR] at hR; subst hR; simp at hwr
    · simp [baseRegions] at hR
  refine ⟨?_, r, j, hr, hj, rfl⟩
  have hsp := pre_sp hpre
  obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
  · rw [envOf_size0] at hj
    rw [env_base0]
    refine .inr (.inl ?_)
    have h2 := S_sub_toNat hpre (k := stackBytes) (Nat.le_refl _)
    have hfr := fr_toNat hpre
    simp only [InRange, h2]
    rw [toNat_add_ofNat (by unfold Layout.ramHi frameBytes stackBytes TX.stackBytes at *; omega), hfr]
    unfold frameBytes stackBytes TX.stackBytes at *; omega
  · have hsz : (envOf sh σ m).size 1 = resultBytes := by
      simp [envOf, entryEnv, Env.size, regionsOf]
    rw [hsz] at hj
    rw [env_base1]
    refine .inl ?_
    have hrr : RamRange σ.res resultBytes := hpre.2.2.2.1
    simp only [InRange]
    rw [toNat_add_ofNat (by unfold RamRange Layout.ramHi at hrr; omega)]
    omega

/-- An address of a writable region of a state whose regions beyond the base ones are read-only
is DTF's own. -/
theorem inWritable_owned_ro {sh : Shape} {σ : Sig} {m : Machine} {S : SState}
    (hpre : Pre σ.A σ.g σ.m) {ex : List Region} (hS : S.regions = baseRegions ++ ex)
    (hex : ∀ R ∈ ex, R.writable = false) {a : Word} (h : InWritable (envOf sh σ m) S a) :
    Owned σ a := by
  obtain ⟨r, R, j, hR, hwr, hj, rfl⟩ := h
  rw [hS] at hR
  by_cases hr : r < 4
  · rw [List.getElem?_append_left (by simpa [baseRegions] using hr)] at hR
    exact (inWritable_owned (S := { S with regions := baseRegions }) hpre rfl
      ⟨r, R, j, hR, hwr, hj, rfl⟩).1
  · rw [List.getElem?_append_right (by simp [baseRegions]; omega)] at hR
    rw [hex R (List.mem_of_getElem? hR)] at hwr
    cases hwr

/-- `Common` at the end of a leaf that keeps present bytes, writes only DTF's own memory and, of the
frame, only words below the save area. -/
theorem common_leaf_of {sh : Shape} {σ : Sig} {m m' : Machine} {S S' : SState} (hc : Common σ m)
    (hp : Preserved m m') (hown : ∀ a, InWritable (envOf sh σ m) S a → Owned σ a)
    (hm' : Match (envOf sh σ m) S' m') (h0 : 0 < S'.regions.length)
    (hso : SameOutside (InWritable (envOf sh σ m) S) m m') (hlow : writesLow S' = true) :
    Common σ m' := by
  have hpre := hc.2.1
  let R : Word → Prop := fun a => InWritable (envOf sh σ m) S a ∧ ¬ InRange (σ.S - w 104) 104 a
  have hso' : SameOutside R m m' := fun a ha => by
    by_cases hw : InWritable (envOf sh σ m) S a
    · have hin : InRange (σ.S - w 104) 104 a :=
        Classical.byContradiction fun h => ha ⟨hw, h⟩
      -- the save area is frame bytes `0x308 ..< 0x370`
      have h1 := S_sub_toNat hpre (k := 104) (by decide)
      have hfr := fr_toNat hpre
      have hsp := pre_sp hpre
      simp only [InRange, h1] at hin
      have ha' : a = σ.fr + BitVec.ofNat 64 (a.toNat - σ.fr.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_add_ofNat (by unfold Layout.ramHi frameBytes stackBytes TX.stackBytes at *; omega)]
        unfold frameBytes stackBytes TX.stackBytes at *; omega
      rw [ha']
      exact frame_byte_keep' hc.avail hm' h0 (by unfold frameBytes stackBytes TX.stackBytes at *; omega)
        (writesLow_nocover hlow (by unfold frameBytes stackBytes TX.stackBytes at *; omega))
    · exact hso a hw
  obtain ⟨L, X, hlive⟩ := hc.2.2.2.2.2.2.2.2
  exact common_keep hc hp hso' (fun a ha => ⟨.inl (hown a ha.1), ha.2⟩)
    ⟨L, X, live_keep hlive hso' hp fun a ha hpv =>
      owned_not_priv hpre (hown a ha.1) (priv_sub hpre hlive hpv)⟩

/-- `Common` at the end of a leaf that writes only frame words below the save area. -/
theorem common_leaf {sh : Shape} {σ : Sig} {m m' : Machine} {S S' : SState} (hc : Common σ m)
    (hwf : Env.WF (envOf sh σ m) S) (hS : BaseRegs S) (hS' : BaseRegs S')
    (hm' : Match (envOf sh σ m) S' m') (hso : SameOutside (InWritable (envOf sh σ m) S) m m')
    (hlow : writesLow S' = true) : Common σ m' :=
  common_leaf_of hc (F1.preserved_of_leaf hwf hm'
    (Nat.le_of_eq (congrArg List.length ((show S.regions = baseRegions from hS).trans
      (show S'.regions = baseRegions from hS').symm))) hso)
    (fun a h => (inWritable_owned hc.2.1 hS h).1) hm' (by rw [hS']; decide) hso hlow

theorem wf_of_regions {env : Env} {S S' : SState} (hwf : Env.WF env S)
    (h : S'.regions = S.regions) : Env.WF env S' :=
  ⟨by rw [h]; exact hwf.len, hwf.disjoint, fun r R s hR => hwf.size r R s (h ▸ hR),
    fun r R hR => hwf.align r R (h ▸ hR), fun r R hR => hwf.range r R (h ▸ hR)⟩

/-- The target's pointer registers and frame slots hold the shape's values in `S`. -/
def shapeHolds (S : SState) (sh : Shape) : Bool :=
  sh.regs.all (fun p => !p.2.isWord || S.reg p.1 == p.2.sym 0) &&
  sh.slots.all (fun p => !p.2.isWord || readConst S 0 p.1 8 == p.2.sym 0)

/-- No `Extra` conjunct at `pc`. -/
def noExtra (pc : Nat) : Bool :=
  pc != 0x80000574 && pc != 0x80002138 && pc != 0x80002434 && pc != 0x800011f8 &&
    pc != 0x800020ac

/-- No `SiteX` conjunct at the return site `r`. -/
def noSiteX (r : Nat) : Bool := r != 0x800020c0 && r != 0x8000211c

/-- The target has no inner budget and the constant part drops by the steps. -/
def budgetKeep (pc pc' steps : Nat) : Bool :=
  match (budgetAt pc').2 with
  | .none => decide ((budgetAt pc').1 + steps ≤ (budgetAt pc).1)
  | _ => false

end ZesuExec.Fn.DTF
