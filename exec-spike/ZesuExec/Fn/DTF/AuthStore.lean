import ZesuExec.Fn.DTF.AuthOwn

/-!
# DTF: the tuple store (`0x80002434`, programme plan S7 step 4)

The three leaves store the tuple's `0x90` bytes into the slot `bp + 0x90 n` (region 4), advance
the list cursor past it (`S-0x300 += k`, `S-0x308 -= k`); leaf 2 loops back to `0x800024d0` with
`n + 1` tuples, leaf 0 calls `toOwnedSlice`'s remap when no list bytes are left, leaf 1 (its
overflow check failing) is vacuous. As `HashStore.lean`: the slot lies in a live block
(`common_slot`), words no write covers keep their values (`slot_word_keep`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

set_option maxRecDepth 20000

/-- The source's facts at the tuple store cut `0x80002434`. -/
theorem astore_src {σ : Sig} {m : Machine} (hA : (mkCut (table[124]!)).A σ m) :
    Common σ m ∧ ArmOk σ (table[124]!).arms ∧ RestOk σ m (table[124]!).rest ∧
      SlotOk σ m 0x90 ∧ AuthSlot σ m ∧ ChecksOk σ (chkCount (table[124]!).rest) := by
  have hne : (table[124]!).pc ≠ entry := by decide
  simp only [mkCut, if_neg hne, ACut, show (table[124]!).site = none by decide, reduceCtorEq,
    false_and, exists_false, or_false] at hA
  obtain ⟨-, -, hcm, -, harm, hrst, hex, -, hchk⟩ := hA
  rw [show (table[124]!).pc = 0x80002434 by decide] at hex
  simp only [Extra] at hex
  exact ⟨hcm, harm, hrst, hex.1, hex.2, hchk⟩

/-- What a store leaf leaves: the `n + 1`-th tuple stored, the list cursor past it. -/
theorem astore_out {σ : Sig} {m m' : Machine} {l : Leaf}
    (hreg : l.S.regions = baseRegions ++ [slotR 0x90]) (hlow : writesLowS l.S = true)
    (h112 : readConst l.S 0 112 8 = .bin .add (.bin .add (.ptr 3 0) (.var 78)) (.init 0 72 8))
    (h104 : readConst l.S 0 104 8 = .bin .sub (.init 0 104 8) (.init 0 72 8))
    (hk : [0x30, 0x58, 0x60, 0x78, 336, 344].all (fun o =>
      readConst l.S 0 o 8 == readConst (table[124]!).shape.S 0 o 8) = true)
    (hA : (mkCut (table[124]!)).A σ m)
    (hm' : Match (envOf (table[124]!).shape σ m) l.S m')
    (hso : SameOutside (InWritable (envOf (table[124]!).shape σ m) (table[124]!).shape.S) m m') :
    ∃ c h p n j k, AuthList σ c h p ∧
      skip (n + 1) (TX.itemPayload (σ.payload.drop c) h p) = some (j + k) ∧ n + 1 ≤ j + k ∧
      22 ≤ k ∧ j + k ≤ p ∧
      (Sym.bin .sub (.init 0 104 8) (.init 0 72 8)).eval (envOf (table[124]!).shape σ m) =
        w (p - (j + k)) ∧
      (Sym.init 0 120 8).eval (envOf (table[124]!).shape σ m) = w (n + 1) ∧ n < 2 ^ 32 ∧
      AuthOut σ m' (n + 1) (j + k) c h p ∧
      m'.load (σ.fr + w 0x78) 8 = some (w (n + 1)) ∧ AuthBuf σ m' (n + 1) 0 ∧ Common σ m' ∧
      m.load (σ.fr + w 0x68) 8 = some (w (p - j)) ∧
      m'.load (σ.fr + w 336) 8 = m.load (σ.fr + w 336) 8 ∧
      m'.load (σ.fr + w 344) 8 = m.load (σ.fr + w 344) 8 := by
  have hcut : CutOK vcPlan (mkCut (table[124]!)) := DTF.cut_80002434
  obtain ⟨hwf, hm, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf hm
  have hx : (table[124]!).shape.extra = [slotR 0x90] := by decide
  have hS : (table[124]!).shape.S.regions = baseRegions ++ [slotR 0x90] := by decide
  obtain ⟨hcm, harm, -, hslot, ⟨n, ⟨⟨c, h, p, j, k, ho, hsk1, hk22, l48⟩, l78, l40, l38⟩,
    ⟨bp, cap, l58, l60, hn1, hn2, L, X, hlive, hmem⟩, bp', l58', r10⟩, -⟩ := astore_src hA
  rw [l58, Option.some.injEq] at l58'
  subst l58'
  have hpre := hcm.2.1
  have h4 : σ.t = 4 := arm4 harm (by decide)
  obtain ⟨hl, hsk, hnj, l70, l68, l30⟩ := ho
  obtain ⟨-, hle, hn32⟩ := out_n hpre h4 ⟨hl, hsk, hnj, l70, l68, l30⟩
  have hjk : j + k ≤ p := by
    have := skip_le hsk1
    simp only [TX.itemPayload, List.length_take, List.length_drop] at this
    omega
  have hlen32 := len_lt32 hpre
  have hwf' : Env.WF (envOf (table[124]!).shape σ m) l.S := wf_of_regions hwf (hreg.trans hS.symm)
  have hR0 : l.S.regions[0]? = some frameR := by rw [hreg]; rfl
  have hR0s : (table[124]!).shape.S.regions[0]? = some frameR := by rw [hS]; rfl
  have hp : Preserved m m' := F1.preserved_of_leaf hwf hm' (Nat.le_of_eq (by rw [hS, hreg])) hso
  have hcap0 : 0 < cap.toNat := by omega
  have hm0 := hmem hcap0
  obtain ⟨-, hram, -⟩ := blk_facts hlive hm0
  simp only at hram
  unfold RamRange Layout.ramHi at hram
  have hle' : n * 0x90 + 0x90 ≤ cap.toNat * 0x90 := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hn1
  have hin : ∀ a, InRange (m.reg 10) 0x90 a → InLive L a := fun a ha =>
    ⟨(bp, cap.toNat * 0x90), hlive.2.1.symm.subset (List.mem_append_right _ hm0), by
      rw [r10] at ha
      simp only [InRange] at ha ⊢
      rw [toNat_add_ofNat (by omega)] at ha
      omega⟩
  obtain ⟨hcm', hlive'⟩ := common_slot hcm hS hx hp hm' (by rw [hreg]; decide) hso hlow hslot
    hlive hin
  have hb0 := env_base0 (table[124]!).shape σ m
  have hs0 := envOf_size0 (table[124]!).shape σ m
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
    at hk
  obtain ⟨k30, k58, k60, k78, k336, k344⟩ := hk
  have e30 := slot_word_keep hwf hm hR0s hwf' hm' hR0 hb0 hs0 (o := 0x30) (by decide) k30
  have e58 := slot_word_keep hwf hm hR0s hwf' hm' hR0 hb0 hs0 (o := 0x58) (by decide) k58
  have e60 := slot_word_keep hwf hm hR0s hwf' hm' hR0 hb0 hs0 (o := 0x60) (by decide) k60
  have e78 := slot_word_keep hwf hm hR0s hwf' hm' hR0 hb0 hs0 (o := 0x78) (by decide) k78
  have e336 := slot_word_keep hwf hm hR0s hwf' hm' hR0 hb0 hs0 (o := 336) (by decide) k336
  have e344 := slot_word_keep hwf hm hR0s hwf' hm' hR0 hb0 hs0 (o := 344) (by decide) k344
  have w112 := slot_word hwf' hm' hR0 hb0 hs0 (o := 112) (by decide) h112
  have w104 := slot_word hwf' hm' hR0 hb0 hs0 (o := 104) (by decide) h104
  have i72 : (Sym.init 0 72 8).eval (envOf (table[124]!).shape σ m) = w k := by
    have := load_cst hwf hm hR0s (off := 72) (n := 8) (by rw [hs0]; decide)
    rw [hb0, show readConst (table[124]!).shape.S 0 72 8 = .init 0 72 8 by decide] at this
    rw [← Option.some.injEq, ← this]; exact l48
  have i104 : (Sym.init 0 104 8).eval (envOf (table[124]!).shape σ m) = w (p - j) := by
    have := load_cst hwf hm hR0s (off := 104) (n := 8) (by rw [hs0]; decide)
    rw [hb0, show readConst (table[124]!).shape.S 0 104 8 = .init 0 104 8 by decide] at this
    rw [← Option.some.injEq, ← this]; exact l68
  have i120 : (Sym.init 0 120 8).eval (envOf (table[124]!).shape σ m) = w (n + 1) := by
    have := load_cst hwf hm hR0s (off := 120) (n := 8) (by rw [hs0]; decide)
    rw [hb0, show readConst (table[124]!).shape.S 0 120 8 = .init 0 120 8 by decide] at this
    rw [← Option.some.injEq, ← this]; exact l78
  have hsub : (Sym.bin .sub (.init 0 104 8) (.init 0 72 8)).eval (envOf (table[124]!).shape σ m) =
      w (p - (j + k)) := by
    rw [Sym.eval_bin, i104, i72]
    apply BitVec.eq_of_toNat_eq
    simp only [BinOp.eval, w, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hv78 : (Sym.var 78).eval (envOf (table[124]!).shape σ m) =
      TX.wordAt m (σ.fr + w 112) - σ.inp := var_slot (by decide)
  have hp3 : (Sym.ptr 3 0).eval (envOf (table[124]!).shape σ m) = σ.inp := by
    simp only [Sym.eval, env_base3]; simp
  refine ⟨c, h, p, n, j, k, hl, hsk1, by omega, hk22, hjk, hsub, i120, hn32,
    ⟨hl, hsk1, by omega, ?_, ?_, by rw [e30]; exact l30⟩, by rw [e78]; exact l78,
    ⟨bp, cap, by rw [e58]; exact l58, by rw [e60]; exact l60, by omega, by omega, L, X, hlive',
      hmem⟩, hcm', l68, e336, e344⟩
  · rw [w112]
    simp only [Sym.eval_bin, BinOp.eval, hv78, hp3, i72, wordAt_of_load l70]
    rw [show σ.inp + w (c + h + j) - σ.inp = w (c + h + j) by
      rw [BitVec.add_comm, BitVec.add_sub_cancel]]
    simp only [w]; rw [F1.add_add_ofNat, Nat.add_assoc (c + h)]
  · rw [w104, hsub]

/-- List bytes left after the tuple (`0x80002434` leaf 2): back to the loop head with `n + 1`
tuples. -/
theorem DTF.leaf_80002434_2 :
    LeafGoal DTF.plan DTF.plan.cuts[124]! ((DTF.plan.leaves 0x80002434)[2]!) := by
  show LeafGoal vcPlan (mkCut (table[124]!)) ((leavesAt 0x80002434)[2]!)
  have hcut : CutOK vcPlan (mkCut (table[124]!)) := DTF.cut_80002434
  have hob : ((leavesAt 0x80002434)[2]!).obligs = [] := by decide
  have hexit : ((leavesAt 0x80002434)[2]!).exit = .at 0x800024d0 := by decide
  have hsteps : ((leavesAt 0x80002434)[2]!).S.steps - (table[124]!).shape.S.steps = 39 := by
    decide
  have hreg : ((leavesAt 0x80002434)[2]!).S.regions = baseRegions ++ [slotR 0x90] := by decide
  have hS : (table[124]!).shape.S.regions = baseRegions ++ [slotR 0x90] := by decide
  have hne' : (table[125]!).pc ≠ entry := by decide
  have hrest0 : (table[124]!).rest = [⟨.slot 336, false, 10⟩, ⟨.slot 344, true, 10⟩] := by
    decide
  have hrest : (table[125]!).rest = (table[124]!).rest := by decide
  intro σ m hA hc
  obtain ⟨hwf, hm, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf hm hc
  refine ⟨fun o ho => (by rw [hob] at ho; cases ho), ?_, fun m' hm' hexok hso => ?_⟩
  · show ((leavesAt 0x80002434)[2]!).S.steps - (table[124]!).shape.S.steps ≤
      budgetOf (table[124]!) σ m
    unfold budgetOf
    rw [hsteps, show budgetAt (table[124]!).pc = (2562, .list (.slot 0x68)) from rfl]
    omega
  simp only [mkCut] at hm' hso
  rw [hexit] at hexok ⊢
  simp only [ExitOk] at hexok
  obtain ⟨c, h, p, n, j, k, hl, hsk1, hnk, hk22, hjk, -, -, -, ho, l78, hb, hcm', l68, k336,
    k344⟩ := astore_out hreg (by decide) (by decide) (by decide) (by decide) hA hm' hso
  obtain ⟨-, harm, hrst, -, -, hchk⟩ := astore_src hA
  have hwf' := wf_of_regions hwf (hreg.trans hS.symm)
  have hR0 : ((leavesAt 0x80002434)[2]!).S.regions[0]? = some frameR := by rw [hreg]; rfl
  have hloop : AuthLoop σ m' := ⟨c, h, p, n + 1, j + k, ho, l78, hb⟩
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have hle := authList_le hcm'.2.1 (arm4 harm (by decide)) hl
  refine ExitGoal.at_cut rfl ⟨mkCut (table[125]!),
    List.mem_map_of_mem (targetOf_spec (pc := 0x800024d0) (d' := table[125]!) rfl).1, ?_, ?_, ?_⟩
  · rw [hexok]; rfl
  · simp only [mkCut, if_neg hne', ACut]
    refine .inl ⟨by decide, by rw [hexok]; rfl, hcm', shapeOk_of_holds hwf' hm' hR0 (by decide)
      (by decide), by rw [show (table[125]!).arms = (table[124]!).arms by decide]; exact harm,
      ?_, ?_, ?_, ?_⟩
    · rw [hrest, hrest0]
      rw [hrest0] at hrst
      intro r hr
      obtain ⟨c', hs', hw'⟩ := hrst r hr
      refine ⟨c', hs', ?_⟩
      rw [← hw']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Loc.word, TX.wordAt, k336]
      · simp only [Loc.word, TX.wordAt, k344]
    · rw [show (table[125]!).pc = 0x800024d0 by decide]
      simp only [Extra, AuthExtra, Nat.reduceEqDiff, if_false, if_true]
      exact hloop
    · rw [show budgetAt (table[125]!).pc = (7043, .list (.slot 0x68)) from rfl]; trivial
    · rw [show chkCount (table[125]!).rest = chkCount (table[124]!).rest by decide]; exact hchk
  · show budgetOf (table[125]!) σ m' ≤ budgetOf (table[124]!) σ m -
      (((leavesAt 0x80002434)[2]!).S.steps - (table[124]!).shape.S.steps)
    rw [hsteps]
    obtain ⟨-, -, -, -, l68', -⟩ := ho
    unfold budgetOf restLen
    rw [show budgetAt (table[125]!).pc = (7043, .list (.slot 0x68)) from rfl,
      show budgetAt (table[124]!).pc = (2562, .list (.slot 0x68)) from rfl,
      show (table[125]!).rest.find? (·.len) = some ⟨.slot 344, true, 10⟩ by decide,
      show (table[124]!).rest.find? (·.len) = some ⟨.slot 344, true, 10⟩ by decide]
    simp only [innerOf, Loc.word, TX.wordAt, k344, l68, l68', Option.getD_some]
    simp only [w, BitVec.toNat_ofNat]
    omega

/-- The list used up (`0x80002434` leaf 0): `toOwnedSlice`'s remap (return `0x80002f54`). -/
theorem DTF.leaf_80002434_0 :
    LeafGoal DTF.plan DTF.plan.cuts[124]! ((DTF.plan.leaves 0x80002434)[0]!) := by
  show LeafGoal vcPlan (mkCut (table[124]!)) ((leavesAt 0x80002434)[0]!)
  have hcut : CutOK vcPlan (mkCut (table[124]!)) := DTF.cut_80002434
  have hob : ((leavesAt 0x80002434)[0]!).obligs = [] := by decide
  have hexit : ((leavesAt 0x80002434)[0]!).exit = .call F0.entry 0x80002f54 := by decide
  have hsteps : ((leavesAt 0x80002434)[0]!).S.steps - (table[124]!).shape.S.steps = 62 := by
    decide
  have hreg : ((leavesAt 0x80002434)[0]!).S.regions = baseRegions ++ [slotR 0x90] := by decide
  have hS : (table[124]!).shape.S.regions = baseRegions ++ [slotR 0x90] := by decide
  have hne' : (table[156]!).pc ≠ entry := by decide
  have hrest0 : (table[124]!).rest = [⟨.slot 336, false, 10⟩, ⟨.slot 344, true, 10⟩] := by
    decide
  have hrest : (siteAt 156).rest = (table[124]!).rest := by decide
  have hkind : (siteAt 156).kind = .remap := by decide
  have hSF : (siteAt 156).kind.SiteFine (siteAt 156) = true := by decide
  intro σ m hA hc
  obtain ⟨hwf, hm, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf hm hc
  refine ⟨fun o ho => (by rw [hob] at ho; cases ho), ?_, fun m' hm' hexok hso => ?_⟩
  · show ((leavesAt 0x80002434)[0]!).S.steps - (table[124]!).shape.S.steps ≤
      budgetOf (table[124]!) σ m
    unfold budgetOf
    rw [hsteps, show budgetAt (table[124]!).pc = (2562, .list (.slot 0x68)) from rfl]
    omega
  simp only [mkCut] at hm' hso
  rw [hexit] at hexok ⊢
  simp only [ExitOk] at hexok
  obtain ⟨c, h, p, n, j, k, hl, hsk1, hnk, hk22, hjk, hsub, -, -, ho, l78, hb, hcm', -, k336,
    k344⟩ := astore_out hreg (by decide) (by decide) (by decide) (by decide) hA hm' hso
  obtain ⟨-, harm, hrst, -, -, hchk⟩ := astore_src hA
  have hcond := hc _ (show SBool.eq (.bin .sub (.init 0 104 8) (.init 0 72 8)) (.lit 0) ∈ _ by
    decide)
  simp only [SBool.eval, hsub, beq_iff_eq, Sym.eval_lit] at hcond
  have hpre := hcm'.2.1
  have hle := authList_le hpre (arm4 harm (by decide)) hl
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have hpjk : p = j + k := by
    have := congrArg BitVec.toNat hcond
    simp only [w, BitVec.toNat_ofNat] at this
    omega
  have hwf' := wf_of_regions hwf (hreg.trans hS.symm)
  have hR0 : ((leavesAt 0x80002434)[0]!).S.regions[0]? = some frameR := by rw [hreg]; rfl
  have hr1 : m'.reg 1 = w 0x80002f54 := by
    rw [← hm'.regs 1]
    show (((leavesAt 0x80002434)[0]!).S.reg 1).eval _ = _
    rw [show ((leavesAt 0x80002434)[0]!).S.reg 1 = .lit 0x80002f54 by decide]
    rfl
  have hshp : ShapeOk σ (siteAt 156).shape m' :=
    shapeOk_of_holds hwf' hm' hR0 (by decide) (by decide)
  have hsp : m'.reg 2 = σ.fr + w 0 := hshp.1 (2, .fr 0) (by decide) _ rfl
  have hra : RetAligned m' := by unfold RetAligned; rw [hr1]; decide
  have hidx : IdxOk (siteAt 156).kind σ ([], [], ⟨[], []⟩) m' := by
    rw [hkind]; exact ⟨⟨hcm'.2.2.1, stack16 hcm' hsp, hra⟩, trivial⟩
  obtain ⟨-, -, -, -, -, l30⟩ := ho
  have hdone : AuthDone σ m' (n + 1) :=
    ⟨c, h, p, hl, by rw [hsk1, hpjk], by omega, l78, l30, fun _ => by omega, hb⟩
  have hrst' : RestOk σ m' (siteAt 156).rest := by
    rw [hrest, hrest0]
    rw [hrest0] at hrst
    intro r hr
    obtain ⟨c', hs', hw'⟩ := hrst r hr
    refine ⟨c', hs', ?_⟩
    rw [← hw']
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Loc.word, TX.wordAt, k336]
    · simp only [Loc.word, TX.wordAt, k344]
  have harm' : ArmOk σ (siteAt 156).arms := by
    rw [show (siteAt 156).arms = (table[124]!).arms by decide]; exact harm
  have hsite : SiteA (siteAt 156) (table[156]!).pc σ ([], [], ⟨[], []⟩) m' := by
    rw [show (table[156]!).pc = 0x80002f54 by decide]
    refine ⟨hr1, hcm', hshp, harm', hrst', hidx, fun f hf => ?_, ?_, ?_⟩
    · rw [show siteFields 0x80002f54 = [] by decide] at hf; cases hf
    · rw [show chkCount (siteAt 156).rest = chkCount (table[124]!).rest by decide]; exact hchk
    · simp only [SiteX, AuthSite, Nat.reduceEqDiff, if_false, if_true]
      exact ⟨n + 1, hdone⟩
  refine ⟨calleeOf (siteAt 156).kind, ([], [], ⟨[], []⟩), ?_, ?_, hidx.1, fun m'' hpost => ?_⟩
  · show calleeAt 0x80002f54 = _
    unfold calleeAt
    rw [show table.find? (·.pc = 0x80002f54) = targetOf (table[156]!).pc from rfl,
      show targetOf (table[156]!).pc = some (table[156]!) from rfl]
    rfl
  · rw [hexok, hkind]; rfl
  obtain ⟨hret, -, hkeep⟩ := ret_common hSF hsite hpost
  have hpc'' : m''.pc.toNat = 0x80002f54 := by rw [hret.1, hr1]; decide
  refine ⟨mkCut (table[156]!),
    List.mem_map_of_mem (targetOf_spec (pc := 0x80002f54) (d' := table[156]!) rfl).1,
    by decide, hpc'', ?_, ?_⟩
  · simp only [mkCut, if_neg hne', ACut]
    exact .inr ⟨siteAt 156, rfl, m', _, hsite, hpost⟩
  have k344' := hkeep 344 (by decide) (by rw [hkind]; rfl)
  show (siteAt 156).kind.bound + budgetOf (table[156]!) σ m'' ≤ budgetOf (table[124]!) σ m -
    (((leavesAt 0x80002434)[0]!).S.steps - (table[124]!).shape.S.steps)
  rw [hsteps, show (siteAt 156).kind.bound = 9 by decide]
  unfold budgetOf restLen
  rw [show budgetAt (table[156]!).pc = (2491, .none) from rfl,
    show budgetAt (table[124]!).pc = (2562, .list (.slot 0x68)) from rfl,
    show (table[156]!).rest.find? (·.len) = some ⟨.slot 344, true, 10⟩ by decide,
    show (table[124]!).rest.find? (·.len) = some ⟨.slot 344, true, 10⟩ by decide]
  simp only [innerOf, Loc.word, TX.wordAt]
  rw [k344', k344]
  omega

/-- The overflow check of `toOwnedSlice` never fails (`0x80002434` leaf 1): vacuous. -/
theorem DTF.leaf_80002434_1 :
    LeafGoal DTF.plan DTF.plan.cuts[124]! ((DTF.plan.leaves 0x80002434)[1]!) := by
  show LeafGoal vcPlan (mkCut (table[124]!)) ((leavesAt 0x80002434)[1]!)
  intro σ m hA hc
  exfalso
  have hcut : CutOK vcPlan (mkCut (table[124]!)) := DTF.cut_80002434
  obtain ⟨hwf, hm, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf hm hc
  obtain ⟨hcm, harm, -, -, ⟨n, ⟨⟨c, h, p, j, k, ho, -⟩, l78, -⟩, -⟩, -⟩ := astore_src hA
  obtain ⟨-, -, hn32⟩ := out_n hcm.2.1 (arm4 harm (by decide)) ho
  have hR0s : (table[124]!).shape.S.regions[0]? = some frameR := by
    rw [show (table[124]!).shape.S.regions = baseRegions ++ [slotR 0x90] by decide]; rfl
  have i120 : (Sym.init 0 120 8).eval (envOf (table[124]!).shape σ m) = w (n + 1) := by
    have := load_cst hwf hm hR0s (off := 120) (n := 8) (by rw [envOf_size0]; decide)
    rw [env_base0, show readConst (table[124]!).shape.S 0 120 8 = .init 0 120 8 by decide] at this
    rw [← Option.some.injEq, ← this]; exact l78
  have hov := hc _ (show SBool.ne (.bin .mulhu (.init 0 120 8) (.lit 144)) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, Sym.eval_bin, Sym.eval_lit, i120, mulhu0 (show n + 1 < 2 ^ 40 by omega)]
    at hov
  exact absurd hov (by decide)

end ZesuExec.Fn.DTF
