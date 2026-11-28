import ZesuExec.Fn.DTF.Gen

/-!
# DTF: `leaf_gen` with the target's assertion left to the caller (programme plan S7 step 4)

`leaf_at_x` and `leaf_call_x` are `leaf_gen`'s two branches with the parts the boolean checks
cannot decide stated as hypotheses over the leaf's `Ctx`: at a plain cut its `Extra`, cursor and
budget; at a call the callee's index (`IdxOk`), the site's `SiteX` and the return budget. The
shared checks (`CoreChk`, `AtChk`, `CallChk`) are decided per leaf. The list loops' leaves
(`Hash.lean`) use them.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- The source-side checks of `leaf_gen` but the obligations: no extra region at the source,
base regions in the leaf, writes below the save area. -/
def CoreChk0 (d : CutData) (l : Leaf) : Bool :=
  d.shape.extra.isEmpty && l.S.regions == baseRegions && writesLow l.S

/-- `CoreChk0` and the obligations at the source's byte-loop cursor or outcome. -/
def CoreChk (d : CutData) (l : Leaf) : Bool :=
  CoreChk0 d l && l.obligs.all (fun o => curObl d o || outObl d l o)

/-- What a leaf of `d` knows before its exit: any machine matching its final state is a `Ctx`. -/
theorem core_ctx0 {d : CutData} {l : Leaf} (hpc : d.pc ≠ entry) (hcut : CutOK vcPlan (mkCut d))
    (hsrc : SrcOk d = true) (hck : CoreChk0 d l = true) {σ : Sig} {m : Machine}
    (hA : (mkCut d).A σ m) (hc : ∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) :
    Match (envOf d.shape σ m) d.shape.S m ∧
      ∀ m', Match (envOf d.shape σ m) l.S m' →
        SameOutside (InWritable (envOf d.shape σ m) d.shape.S) m m' → Ctx d l σ m m' := by
  have F := facts_of_A hpc hsrc hA
  obtain ⟨hwf, hm, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf hm
  unfold CoreChk0 at hck
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hck
  obtain ⟨⟨hx, hreg⟩, hlow⟩ := hck
  have hS : BaseRegs d.shape.S := baseRegs_shape hx
  have hS' : BaseRegs l.S := hreg
  have hwf' : Env.WF (envOf d.shape σ m) l.S :=
    wf_of_regions hwf ((show l.S.regions = baseRegions from hS').trans hS.symm)
  have hadv : ∀ ko k, advUse d l = some (ko, k) →
      AdvOk d σ m ko k ∧ (Sym.init 0 (ko + 32) 2).eval (envOf d.shape σ m) = 0 := by
    intro ko k h
    unfold advUse at h
    split at h
    · next ko0 k0 h0 =>
      split at h
      · next hcond =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨adv_of_A hpc hsrc h0 hA, ?_⟩
        have := hc _ (List.contains_iff_mem.mp hcond)
        simpa [SBool.eval, Sym.eval_lit] using this
      · cases h
    · cases h
  exact ⟨hm, fun m' hm' hso => ⟨F, hwf, hm, hS, hwf', hm', hS', hso, hlow, hadv,
    fun r hr => (List.mem_append.mp hr).elim (F.rest r) (tx_rest hpc hA hc r)⟩⟩

/-- What a leaf of `d` knows before its exit: the obligations hold, and any machine matching its
final state is a `Ctx`. -/
theorem core_ctx {d : CutData} {l : Leaf} (hpc : d.pc ≠ entry) (hcut : CutOK vcPlan (mkCut d))
    (hsrc : SrcOk d = true) (hck : CoreChk d l = true) {σ : Sig} {m : Machine}
    (hA : (mkCut d).A σ m) (hc : ∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) :
    (∀ o ∈ l.obligs, o.holds (envOf d.shape σ m)) ∧ Match (envOf d.shape σ m) d.shape.S m ∧
      ∀ m', Match (envOf d.shape σ m) l.S m' →
        SameOutside (InWritable (envOf d.shape σ m) d.shape.S) m m' → Ctx d l σ m m' := by
  unfold CoreChk at hck
  simp only [Bool.and_eq_true] at hck
  obtain ⟨hck0, hob⟩ := hck
  obtain ⟨hm, hctx⟩ := core_ctx0 hpc hcut hsrc hck0 hA hc
  obtain ⟨hwf, -, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf
  have hS : BaseRegs d.shape.S := baseRegs_shape (by
    unfold CoreChk0 at hck0
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hck0
    exact hck0.1.1)
  refine ⟨fun o ho => ?_, hm, hctx⟩
  have h := List.all_eq_true.mp hob o ho
  simp only [Bool.or_eq_true] at h
  exact h.elim (curObl_holds hpc hA hm) (outObl_holds hpc hsrc hA hwf hm hS hc)

/-- The obligations `CoreChk` decides. -/
theorem core_obl {d : CutData} {l : Leaf} (hpc : d.pc ≠ entry) (hcut : CutOK vcPlan (mkCut d))
    (hsrc : SrcOk d = true) (hck : CoreChk d l = true) {σ : Sig} {m : Machine}
    (hA : (mkCut d).A σ m) (hc : ∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) :
    ∀ o ∈ l.obligs, o.holds (envOf d.shape σ m) :=
  (core_ctx hpc hcut hsrc hck hA hc).1

theorem coreChk0 {d : CutData} {l : Leaf} (hck : CoreChk d l = true) : CoreChk0 d l = true := by
  unfold CoreChk at hck; simp only [Bool.and_eq_true] at hck; exact hck.1

/-- The target-side checks of an `.at` leaf other than `Extra`, the cursor and the budget. -/
def AtChk (d : CutData) (l : Leaf) (d' : CutData) : Bool :=
  d'.pc != entry && d'.plain && d'.shape.Fine && shapeHolds l.S d'.shape &&
    armsKeep d.arms d'.arms && restFrom d.shape.S l.S (advUse d l) (srcRest d l) d'.rest &&
    chkStep d l (chkCount d'.rest) && decide (l.S.steps - d.shape.S.steps ≤ (budgetAt d.pc).1)

/-- `leaf_at_x` with the leaf's obligations a hypothesis. -/
theorem leaf_at_xo (d d' : CutData) (l : Leaf) (hpc : d.pc ≠ entry)
    (hcut : CutOK vcPlan (mkCut d)) (hsrc : SrcOk d = true) (hck : CoreChk0 d l = true)
    (hO : ∀ σ m, (mkCut d).A σ m → (∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) →
      ∀ o ∈ l.obligs, o.holds (envOf d.shape σ m))
    (hex : l.exit = .at d'.pc) (ht : targetOf d'.pc = some d') (hat : AtChk d l d' = true)
    (hX : ∀ σ m m', (mkCut d).A σ m → (∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) →
      Ctx d l σ m m' → Extra d'.pc σ m' ∧ CurOk σ m' (budgetAt d'.pc).2 ∧
        budgetOf d' σ m' + (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m) :
    LeafGoal vcPlan (mkCut d) l := by
  intro σ m hA hc
  simp only [mkCut] at hc
  obtain ⟨-, hctx⟩ := core_ctx0 hpc hcut hsrc hck hA hc
  have hob := hO σ m hA hc
  have F := facts_of_A hpc hsrc hA
  unfold AtChk at hat
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hat
  obtain ⟨⟨⟨⟨⟨⟨⟨hne, hpl⟩, hfine'⟩, hsh⟩, harms⟩, hrest⟩, hchk⟩, hst⟩ := hat
  cases hexit : l.exit with
  | «at» pc' =>
    rw [hexit] at hex
    cases hex
    refine ⟨hob, ?_, fun m' hm' hexok hso => ?_⟩
    · show l.S.steps - d.shape.S.steps ≤ budgetOf d σ m
      unfold budgetOf; omega
    simp only [mkCut] at hm' hso
    simp only [ExitOk] at hexok
    have C := hctx m' hm' hso
    obtain ⟨hcm, hshp, harm, hrst⟩ := target_facts C hfine' hsh harms hrest
    obtain ⟨hx, hcur, hbud⟩ := hX σ m m' hA hc C
    refine ExitGoal.at_cut rfl
      ⟨mkCut d', List.mem_map_of_mem (targetOf_spec ht).1, hexok, ?_, ?_⟩
    · simp only [mkCut, if_neg hne, ACut]
      exact .inl ⟨hpl, hexok, hcm, hshp, harm, hrst, hx, hcur,
        chkStep_sound hpc hsrc hA hc F hchk⟩
    · show budgetOf d' σ m' ≤ budgetOf d σ m - (l.S.steps - d.shape.S.steps)
      omega
  | _ => rw [hexit] at hex; cases hex

theorem leaf_at_x (d d' : CutData) (l : Leaf) (hpc : d.pc ≠ entry)
    (hcut : CutOK vcPlan (mkCut d)) (hsrc : SrcOk d = true) (hck : CoreChk d l = true)
    (hex : l.exit = .at d'.pc) (ht : targetOf d'.pc = some d') (hat : AtChk d l d' = true)
    (hX : ∀ σ m m', (mkCut d).A σ m → (∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) →
      Ctx d l σ m m' → Extra d'.pc σ m' ∧ CurOk σ m' (budgetAt d'.pc).2 ∧
        budgetOf d' σ m' + (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m) :
    LeafGoal vcPlan (mkCut d) l :=
  leaf_at_xo d d' l hpc hcut hsrc (coreChk0 hck)
    (fun _ _ hA hc => core_obl hpc hcut hsrc hck hA hc) hex ht hat hX

/-- The call-side checks of a call leaf other than the callee's index, `SiteX` and the budget. -/
def CallChk (d : CutData) (l : Leaf) (d' : CutData) (s : Site) (t r : Nat) : Bool :=
  t == s.kind.entry && d'.pc != entry && SrcOk d' && s.shape.Fine &&
    shapeHolds l.S s.shape && armsKeep d.arms s.arms &&
    restFrom d.shape.S l.S (advUse d l) (srcRest d l) s.rest &&
    l.S.reg 1 == .lit r && decide ((w r &&& ~~~(1 : Word)).toNat = r) && decide (r % 4 = 0) &&
    fieldsFrom d l (siteFields r) && chkStep d l (chkCount s.rest) &&
    decide (l.S.steps - d.shape.S.steps ≤ (budgetAt d.pc).1)

/-- What the call site knows at the call machine, for the hypotheses of `leaf_call_x`. -/
structure CallFacts (s : Site) (r : Nat) (σ : Sig) (m' : Machine) : Prop where
  common : Common σ m'
  shape : ShapeOk σ s.shape m'
  arms : ArmOk σ s.arms
  rest : RestOk σ m' s.rest
  chk : ChecksOk σ (chkCount s.rest)
  ra : m'.reg 1 = w r
  aligned : RetAligned m'

/-- `leaf_call_x` with the leaf's obligations a hypothesis. -/
theorem leaf_call_xo (d d' : CutData) (s : Site) (l : Leaf) (t : Nat) (hpc : d.pc ≠ entry)
    (hcut : CutOK vcPlan (mkCut d)) (hsrc : SrcOk d = true) (hck : CoreChk0 d l = true)
    (hO : ∀ σ m, (mkCut d).A σ m → (∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) →
      ∀ o ∈ l.obligs, o.holds (envOf d.shape σ m))
    (hex : l.exit = .call t d'.pc) (ht : targetOf d'.pc = some d') (hs : d'.site = some s)
    (hcl : CallChk d l d' s t d'.pc = true)
    (hX : ∀ σ m m', (mkCut d).A σ m → (∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) →
      Ctx d l σ m m' → CallFacts s d'.pc σ m' →
      ∃ x, IdxOk s.kind σ x m' ∧ SiteX d'.pc σ m' ∧ ∀ m'', (calleeOf s.kind).Post σ x m' m'' →
        s.kind.bound + budgetOf d' σ m'' + (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m) :
    LeafGoal vcPlan (mkCut d) l := by
  intro σ m hA hc
  simp only [mkCut] at hc
  obtain ⟨-, hctx⟩ := core_ctx0 hpc hcut hsrc hck hA hc
  have hob := hO σ m hA hc
  have F := facts_of_A hpc hsrc hA
  unfold CallChk at hcl
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at hcl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht', hne⟩, hsrc'⟩, hfine'⟩, hsh⟩, harms⟩, hrest⟩, hra1⟩, hra⟩, hr4⟩, hfld⟩,
    hchk⟩, hst⟩ := hcl
  cases hexit : l.exit with
  | call t0 r0 =>
    rw [hexit] at hex
    cases hex
    refine ⟨hob, ?_, fun m' hm' hexok hso => ?_⟩
    · show l.S.steps - d.shape.S.steps ≤ budgetOf d σ m
      unfold budgetOf; omega
    simp only [mkCut] at hm' hso
    simp only [ExitOk] at hexok
    have C := hctx m' hm' hso
    obtain ⟨hcm, hshp, harm, hrst⟩ := target_facts C hfine' hsh harms hrest
    have hSF : s.kind.SiteFine s = true := by
      simp only [SrcOk, hs, RetCheck, Bool.and_eq_true] at hsrc'; exact hsrc'.1.1.1
    have hr1 : m'.reg 1 = w d'.pc := by
      rw [← C.hm'.regs 1]; show (l.S.reg 1).eval _ = _; rw [hra1]; rfl
    have hraM : RetAligned m' := by unfold RetAligned; rw [hr1, hra]; exact hr4
    have hchk' := chkStep_sound hpc hsrc hA hc F hchk
    obtain ⟨x0, hidx, hsx, hbud⟩ :=
      hX σ m m' hA hc C ⟨hcm, hshp, harm, hrst, hchk', hr1, hraM⟩
    have hsite : SiteA s d'.pc σ x0 m' := ⟨hr1, hcm, hshp, harm, hrst, hidx,
      fieldsFrom_sound C hpc hsrc hA hfld, hchk', hsx⟩
    refine ⟨calleeOf s.kind, x0, ?_, ?_, hidx.1, fun m'' hpost => ?_⟩
    · show calleeAt d'.pc = _
      unfold calleeAt
      rw [show table.find? (·.pc = d'.pc) = targetOf d'.pc from rfl, ht]
      simp [hs]
    · rw [hexok, ht']; rfl
    have hpc'' : m''.pc.toNat = d'.pc := by rw [(ret_common hSF hsite hpost).1.1, hr1, hra]
    refine ⟨mkCut d', List.mem_map_of_mem (targetOf_spec ht).1, rfl, hpc'', ?_, ?_⟩
    · simp only [mkCut, if_neg hne, ACut]
      exact .inr ⟨s, hs, m', x0, hsite, hpost⟩
    · show s.kind.bound + budgetOf d' σ m'' ≤ budgetOf d σ m - (l.S.steps - d.shape.S.steps)
      have := hbud m'' hpost
      omega
  | _ => rw [hexit] at hex; cases hex

theorem leaf_call_x (d d' : CutData) (s : Site) (l : Leaf) (t : Nat) (hpc : d.pc ≠ entry)
    (hcut : CutOK vcPlan (mkCut d)) (hsrc : SrcOk d = true) (hck : CoreChk d l = true)
    (hex : l.exit = .call t d'.pc) (ht : targetOf d'.pc = some d') (hs : d'.site = some s)
    (hcl : CallChk d l d' s t d'.pc = true)
    (hX : ∀ σ m m', (mkCut d).A σ m → (∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) →
      Ctx d l σ m m' → CallFacts s d'.pc σ m' →
      ∃ x, IdxOk s.kind σ x m' ∧ SiteX d'.pc σ m' ∧ ∀ m'', (calleeOf s.kind).Post σ x m' m'' →
        s.kind.bound + budgetOf d' σ m'' + (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m) :
    LeafGoal vcPlan (mkCut d) l :=
  leaf_call_xo d d' s l t hpc hcut hsrc (coreChk0 hck)
    (fun _ _ hA hc => core_obl hpc hcut hsrc hck hA hc) hex ht hs hcl hX

end ZesuExec.Fn.DTF
