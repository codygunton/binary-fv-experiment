import ZesuExec.Fn.DTF.Ret

/-!
# DTF: the generic leaf theorem `leaf_keep` (programme plan S7 step 4)

A leaf that ends at a plain cut (`.at`), has no obligations, writes only DTF's frame below the save
area, and carries the target's facts over unchanged: the target's pointer registers and frame
slots hold the shape's symbolic values in the leaf's state (`shapeHolds`), the target's `rest`
locations hold the same symbolic values as locations of the source with the same item count
(`restKeep`), the arms only widen (`armsKeep`), and the budget drops by at least the steps
(`budgetKeep`). `KeepCheck` is all of it, by `decide` per leaf; `SrcOk` says the source cut's
facts (`Facts`) follow from its assertion (a return site: its `rest` locations are callee-saved
registers or frame words the callee keeps, its arms those of the call).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## Facts at a cut -/

/-- What a cut other than the entry knows at its machine. -/
structure Facts (d : CutData) (σ : Sig) (m : Machine) : Prop where
  common : Common σ m
  shape : ShapeOk σ d.shape m
  arms : ArmOk σ d.arms
  rest : RestOk σ m d.rest

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

/-- A return site's `rest` locations: at the call site, and callee-saved or kept by the callee. -/
def restRet (d : CutData) (s : Site) : Bool :=
  d.rest.all fun r => decide (r ∈ s.rest) && match r.loc with
    | .reg i => decide (Fin.ofNat 32 i ∈ calleeSaved)
    | .slot o => decide (o + 8 ≤ frameBytes) && s.kind.Keeps s o

/-- The return-site branch of a cut's assertion gives its `Facts`. -/
def SrcOk (d : CutData) : Bool :=
  match d.site with
  | none => true
  | some s => RetCheck d && d.shape.Fine && armsKeep s.arms d.arms && restRet d s

theorem facts_of_ret {d : CutData} {s : Site} {σ : Sig} {m : Machine} (hs : d.site = some s)
    (hck : SrcOk d = true) (hA : RetA s d.pc σ m) : Facts d σ m := by
  simp only [SrcOk, hs, RetCheck, Bool.and_eq_true] at hck
  obtain ⟨⟨⟨⟨hk, hrf⟩, hfine⟩, harms⟩, hrr⟩ := hck
  obtain ⟨mc, x, hsite, hpost⟩ := hA
  obtain ⟨hret, hc, hkeep⟩ := ret_common hk hsite hpost
  simp only [Shape.Fine, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hfine
  simp only [RetFine, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hrf
  obtain ⟨hrr', hrs⟩ := hrf
  refine ⟨hc, ⟨fun p hp v hv => ?_, fun p hp v hv => ?_⟩, armOk_keep harms hsite.2.2.2.1,
    fun r hr => ?_⟩
  · rcases hrr' p hp with h | ⟨hmem, hcs⟩
    · rw [Val.isWord_of hv] at h; cases h
    · rw [hret.2 _ hcs]; exact hsite.2.2.1.1 p hmem v hv
  · rcases hrs p hp with h | ⟨hmem, hke⟩
    · rw [Val.isWord_of hv] at h; cases h
    · rw [hkeep p.1 (hfine.2 p hp).1.2 hke]
      exact hsite.2.2.1.2 p hmem v hv
  · simp only [restRet, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hrr
    obtain ⟨hmem, hloc⟩ := hrr r hr
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
  rcases hA with ⟨-, -, hc, hs, ha, hr, -⟩ | ⟨s, hs, hret⟩
  · exact ⟨hc, hs, ha, hr⟩
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

/-- Every write of `S` is a frame word below the save area. -/
def writesLow (S : SState) : Bool :=
  S.mem.all fun w => w.r == 0 && decide (w.off + w.n ≤ frameBytes - 104)

theorem baseRegs_shape {sh : Shape} (hx : sh.extra = []) : BaseRegs sh.S := by
  simp [BaseRegs, Shape.S, entryState, hx]

/-- A frame byte no write covers is the source machine's. -/
theorem frame_byte_keep {sh : Shape} {σ : Sig} {m m' : Machine} {S : SState} (hc : Avail σ m)
    (hm' : Match (envOf sh σ m) S m') (hS : BaseRegs S) {j : Nat} (hj : j < frameBytes)
    (hnc : S.mem.find? (·.covers 0 j) = none) :
    m'.mem (σ.fr + BitVec.ofNat 64 j) = m.mem (σ.fr + BitVec.ofNat 64 j) := by
  have h := hm'.mem 0 j (by rw [hS]; decide) (by rw [envOf_size0]; exact hj)
  rw [env_base0] at h
  rw [h]
  simp only [memByte, hnc, Env.byte0, envOf, entryEnv, regionsOf]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (stack_present hc hj)
  simp [hb]

theorem writesLow_nocover {S : SState} (h : writesLow S = true) {j : Nat}
    (hj : frameBytes - 104 ≤ j) : S.mem.find? (·.covers 0 j) = none := by
  rw [List.find?_eq_none]
  intro w hw hcov
  simp only [writesLow, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
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

/-- `Common` at the end of a leaf that writes only frame words below the save area. -/
theorem common_leaf {sh : Shape} {σ : Sig} {m m' : Machine} {S S' : SState} (hc : Common σ m)
    (hwf : Env.WF (envOf sh σ m) S) (hS : BaseRegs S) (hS' : BaseRegs S')
    (hm' : Match (envOf sh σ m) S' m') (hso : SameOutside (InWritable (envOf sh σ m) S) m m')
    (hlow : writesLow S' = true) : Common σ m' := by
  have hpre := hc.2.1
  have hp : Preserved m m' := F1.preserved_of_leaf hwf hm'
    (Nat.le_of_eq (congrArg List.length ((show S.regions = baseRegions from hS).trans
      (show S'.regions = baseRegions from hS').symm))) hso
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
      exact frame_byte_keep hc.avail hm' hS' (by unfold frameBytes stackBytes TX.stackBytes at *; omega)
        (writesLow_nocover hlow (by unfold frameBytes stackBytes TX.stackBytes at *; omega))
    · exact hso a hw
  obtain ⟨L, X, hlive⟩ := hc.2.2.2.2.2.2.2.2
  exact common_keep hc hp hso' (fun a ha => ⟨.inl (inWritable_owned hpre hS ha.1).1, ha.2⟩)
    ⟨L, X, live_keep hlive hso' hp fun a ha hpv =>
      owned_not_priv hpre (inWritable_owned hpre hS ha.1).1 (priv_sub hpre hlive hpv)⟩

theorem wf_of_regions {env : Env} {S S' : SState} (hwf : Env.WF env S)
    (h : S'.regions = S.regions) : Env.WF env S' :=
  ⟨by rw [h]; exact hwf.len, hwf.disjoint, fun r R s hR => hwf.size r R s (h ▸ hR),
    fun r R hR => hwf.align r R (h ▸ hR), fun r R hR => hwf.range r R (h ▸ hR)⟩

/-! ## The check and the theorem -/

/-- The target's pointer registers and frame slots hold the shape's values in `S`. -/
def shapeHolds (S : SState) (sh : Shape) : Bool :=
  sh.regs.all (fun p => !p.2.isWord || S.reg p.1 == p.2.sym 0) &&
  sh.slots.all (fun p => !p.2.isWord || readConst S 0 p.1 8 == p.2.sym 0)

/-- Every target `rest` location holds what a source location with the same item count held. -/
def restKeep (S S' : SState) (rs rs' : List RestLoc) : Bool :=
  rs'.all fun r' => r'.loc.fine && rs.any fun r =>
    r.loc.fine && r.k == r'.k && r.len == r'.len && r'.loc.sym S' == r.loc.sym S

/-- The target's `rest` length is the source's (or the target has none). -/
def lenKeep (S S' : SState) (rs rs' : List RestLoc) : Bool :=
  match rs'.find? (·.len) with
  | none => true
  | some r' => match rs.find? (·.len) with
    | some r => r.loc.fine && r'.loc.fine && r'.loc.sym S' == r.loc.sym S
    | none => false

/-- No `Extra` conjunct at `pc`. -/
def noExtra (pc : Nat) : Bool :=
  pc != 0x80000574 && pc != 0x80002138 && pc != 0x80002434 && pc != 0x800011f8

/-- The target has no inner budget and the constant part drops by the steps. -/
def budgetKeep (pc pc' steps : Nat) : Bool :=
  match (budgetAt pc').2 with
  | .none => decide ((budgetAt pc').1 + steps ≤ (budgetAt pc).1)
  | _ => false

def KeepCheck (d : CutData) (l : Leaf) (d' : CutData) : Bool :=
  l.exit == .at d'.pc && d'.pc != entry && d'.plain && noExtra d'.pc && d.shape.extra.isEmpty &&
  d'.shape.extra.isEmpty && d'.shape.Fine && l.S.regions == baseRegions && l.obligs.isEmpty &&
  writesLow l.S && shapeHolds l.S d'.shape && armsKeep d.arms d'.arms &&
  restKeep d.shape.S l.S d.rest d'.rest && lenKeep d.shape.S l.S d.rest d'.rest &&
  budgetKeep d.pc d'.pc (l.S.steps - d.shape.S.steps)

theorem leaf_keep (d d' : CutData) (l : Leaf) (hd' : d' ∈ table) (hpc : d.pc ≠ entry)
    (hcut : CutOK vcPlan (mkCut d)) (hsrc : SrcOk d = true) (hck : KeepCheck d l d' = true) :
    LeafGoal vcPlan (mkCut d) l := by
  simp only [KeepCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    List.isEmpty_iff] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hex, hpc'⟩, hpl⟩, hnx⟩, hx⟩, hx'⟩, hfine'⟩, hreg⟩, hob⟩, hlow⟩, hsh⟩,
    harms⟩, hrest⟩, hlen⟩, hbud⟩ := hck
  intro σ m hA _
  have F := facts_of_A hpc hsrc hA
  obtain ⟨hwf, hm, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf hm
  have hS : BaseRegs d.shape.S := baseRegs_shape hx
  have hS' : BaseRegs l.S := hreg
  have hwf' : Env.WF (envOf d.shape σ m) l.S :=
    wf_of_regions hwf ((show l.S.regions = baseRegions from hS').trans hS.symm)
  simp only [budgetKeep] at hbud
  split at hbud
  case h_2 => cases hbud
  rename_i hinner
  simp only [decide_eq_true_eq] at hbud
  have hsteps : l.S.steps - d.shape.S.steps ≤ (budgetAt d.pc).1 := by omega
  refine ⟨fun o ho => (by rw [hob] at ho; cases ho), ?_, fun m' hm' hexok hso => ?_⟩
  · show l.S.steps - d.shape.S.steps ≤ budgetOf d σ m
    unfold budgetOf; omega
  simp only [mkCut] at hm' hso
  rw [hex] at hexok ⊢
  simp only [ExitOk] at hexok
  -- the target's `rest` length is the source's
  have hlen' : restLen d' σ m' ≤ restLen d σ m := by
    unfold lenKeep at hlen
    unfold restLen
    split at hlen
    · next h => rw [h]; exact Nat.zero_le _
    · next r' h' =>
      split at hlen
      · next r h =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hlen
        obtain ⟨⟨hf, hf'⟩, he⟩ := hlen
        rw [h', h]
        dsimp only
        rw [loc_word_eval hwf' hm' hS' hf', he, ← loc_word_eval hwf hm hS hf]
        exact Nat.le_refl _
      · cases hlen
  refine ExitGoal.at_cut rfl ⟨mkCut d', List.mem_map_of_mem hd', hexok, ?_, ?_⟩
  · simp only [mkCut, if_neg hpc', ACut]
    refine .inl ⟨hpl, hexok, common_leaf F.common hwf hS hS' hm' hso hlow, ⟨?_, ?_⟩,
      armOk_keep harms F.arms, fun r' hr' => ?_, ?_⟩
    · intro p hp v hv
      simp only [shapeHolds, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', beq_iff_eq] at hsh
      rcases hsh.1 p hp with h | h
      · rw [Val.isWord_of hv] at h; cases h
      · simp only [Shape.Fine, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hfine'
        have hi := (hfine'.1 p hp).1
        have e : (Fin.ofNat 32 p.1 : Fin 32) = ⟨p.1, hi⟩ := Fin.ext (by simp [Nat.mod_eq_of_lt hi])
        rw [e, ← hm'.regs ⟨p.1, hi⟩]
        show (l.S.reg p.1).eval _ = v
        rw [h]
        exact Val.sym_eval 0 hv
    · intro p hp v hv
      simp only [shapeHolds, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', beq_iff_eq] at hsh
      rcases hsh.2 p hp with h | h
      · rw [Val.isWord_of hv] at h; cases h
      · simp only [Shape.Fine, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hfine'
        have ho := (hfine'.2 p hp).1.2
        have hR : l.S.regions[0]? = some frameR := by rw [hS']; rfl
        have := load_cst hwf' hm' hR (by rw [envOf_size0]; exact ho)
        rw [env_base0, h, Val.sym_eval 0 hv] at this
        exact this
    · simp only [restKeep, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hrest
      obtain ⟨hf', r, hr, ⟨⟨⟨hf, hk⟩, hl⟩, he⟩⟩ := hrest r' hr'
      obtain ⟨c, hskip, hw⟩ := F.rest r hr
      refine ⟨c, hk ▸ hskip, ?_⟩
      rw [loc_word_eval hwf' hm' hS' hf', he, ← loc_word_eval hwf hm hS hf, hw, hl]
    · simp only [noExtra, Bool.and_eq_true, bne_iff_ne, ne_eq] at hnx
      simp only [Extra, if_neg hnx.1.1.1, if_neg hnx.1.1.2, if_neg hnx.1.2, if_neg hnx.2]
  · show budgetOf d' σ m' ≤ budgetOf d σ m - (l.S.steps - d.shape.S.steps)
    unfold budgetOf
    rw [hinner]
    simp only [innerOf]
    omega

end ZesuExec.Fn.DTF
