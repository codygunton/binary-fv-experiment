import ZesuExec.Fn.DTF.Slot

/-!
# DTF: the `txHashList` loop's store (`0x80002138`, programme plan S7 step 4)

Both leaves store the item's four words into the slot `p + 32 n`, set the header's length to
`n + 1`, advance the cursor past the item (`s7 += k`, `s6 -= k`, `s9 = n + 1`); leaf 0 loops
back to `0x800020ac` when list bytes are left, leaf 1 calls `toOwnedSlice` when none are.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- The source's facts at the store cut `0x80002138`. -/
theorem store_src {σ : Sig} {m : Machine} (hA : (mkCut (table[110]!)).A σ m) :
    Common σ m ∧ ArmOk σ (table[110]!).arms ∧ RestOk σ m (table[110]!).rest ∧
      SlotOk σ m 32 ∧ HashItem σ m 1 ∧ HashSlot σ m ∧
      ChecksOk σ (chkCount (table[110]!).rest) := by
  have hne : (table[110]!).pc ≠ entry := by decide
  simp only [mkCut, if_neg hne, ACut, show (table[110]!).site = none by decide, reduceCtorEq,
    false_and, exists_false, or_false] at hA
  obtain ⟨-, -, hcm, -, harm, hrst, hex, -, hchk⟩ := hA
  rw [show (table[110]!).pc = 0x80002138 by decide] at hex
  simp only [Extra] at hex
  exact ⟨hcm, harm, hrst, hex.1, hex.2.1, hex.2.2, hchk⟩

/-- What a store leaf leaves: the loop after `n + 1` hashes, `Common`, the `rest` words. -/
theorem store_out {σ : Sig} {m m' : Machine} {l : Leaf}
    (hreg : l.S.regions = baseRegions ++ [slotR 32]) (hlow : writesLowS l.S = true)
    (h23 : l.S.reg 23 = .bin .add (.bin .add (.ptr 3 0) (.var 55)) (.var 20))
    (h22 : l.S.reg 22 = .bin .sub (.var 22) (.var 20))
    (h25 : l.S.reg 25 = .bin .add (.var 25) (.lit 1))
    (h608 : readConst l.S 0 608 8 = .bin .add (.var 25) (.lit 1))
    (h600 : readConst l.S 0 600 8 = readConst (table[110]!).shape.S 0 600 8)
    (h616 : readConst l.S 0 616 8 = readConst (table[110]!).shape.S 0 616 8)
    (h336 : readConst l.S 0 336 8 = readConst (table[110]!).shape.S 0 336 8)
    (h344 : readConst l.S 0 344 8 = readConst (table[110]!).shape.S 0 344 8)
    (hA : (mkCut (table[110]!)).A σ m)
    (hm' : Match (envOf (table[110]!).shape σ m) l.S m')
    (hso : SameOutside (InWritable (envOf (table[110]!).shape σ m) (table[110]!).shape.S) m m') :
    ∃ c h p n j k, HashList σ c h p ∧
      skip (n + 1) (TX.itemPayload (σ.payload.drop c) h p) = some (j + k) ∧ n + 1 ≤ j + k ∧
      32 ≤ k ∧ j + k ≤ p ∧ c + h + p ≤ σ.len ∧ m.reg 22 = w (p - j) ∧
      (Sym.bin .sub (.var 22) (.var 20)).eval (envOf (table[110]!).shape σ m) = w (p - (j + k)) ∧
      m'.reg 23 = σ.inp + w (c + h + (j + k)) ∧ m'.reg 22 = w (p - (j + k)) ∧
      m'.reg 25 = w (n + 1) ∧ ListHdr σ m' 0x258 (n + 1) 0 ∧ Common σ m' ∧
      m'.load (σ.fr + w 336) 8 = m.load (σ.fr + w 336) 8 ∧
      m'.load (σ.fr + w 344) 8 = m.load (σ.fr + w 344) 8 := by
  have hcut : CutOK vcPlan (mkCut (table[110]!)) := DTF.cut_80002138
  obtain ⟨hwf, hm, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf hm
  have hx : (table[110]!).shape.extra = [slotR 32] := by decide
  have hS : (table[110]!).shape.S.regions = baseRegions ++ [slotR 32] := by decide
  obtain ⟨hcm, harm, -, hslot, hit, hhs, -⟩ := store_src hA
  obtain ⟨c, h, p, n, j, k, hl, hsk, hsk1, hnk, hk32, r23, r22, r25, r20, hdr⟩ := hit
  have hpre := hcm.2.1
  have hle := hashList_le hpre (arm3 harm (by decide)) hl
  have hjk : j + k ≤ p := by
    have := skip_le hsk1
    simp only [TX.itemPayload, List.length_take, List.length_drop] at this
    omega
  have hn32 : n < 2 ^ 32 := by have := len_lt32 hpre; omega
  have hlen32 := len_lt32 hpre
  have hwf' : Env.WF (envOf (table[110]!).shape σ m) l.S := wf_of_regions hwf (hreg.trans hS.symm)
  have hR0 : l.S.regions[0]? = some frameR := by rw [hreg]; rfl
  have hR0s : (table[110]!).shape.S.regions[0]? = some frameR := by rw [hS]; rfl
  have hp : Preserved m m' := F1.preserved_of_leaf hwf hm' (Nat.le_of_eq (by rw [hS, hreg])) hso
  obtain ⟨p0, cap, l0, l8, l16, hnr, hp0, L, X, hlive, hbuf⟩ := hdr
  obtain ⟨p1, lp1, h10⟩ := hhs
  rw [l0, Option.some.injEq] at lp1
  subst lp1
  have hmem := hbuf (by omega)
  have hram := (hlive.2.2 _ hmem).2.1
  simp only at hram
  unfold RamRange Layout.ramHi at hram
  have h32n : (32 : Word) * w n = w (32 * n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [w, BitVec.toNat_mul, BitVec.toNat_ofNat, show (32 : Word).toNat = 32 from rfl]
    omega
  have hin : ∀ a, InRange (m.reg 10) 32 a → InLive L a := fun a ha =>
    ⟨(p0, cap.toNat * 32), hlive.2.1.symm.subset (List.mem_append_right _ hmem), by
      rw [h10, r25, h32n] at ha
      simp only [InRange] at ha ⊢
      rw [toNat_add_ofNat (by omega)] at ha
      omega⟩
  obtain ⟨hcm', hlive'⟩ := common_slot hcm hS hx hp hm' (by rw [hreg]; decide) hso hlow hslot
    hlive hin
  have hb0 := env_base0 (table[110]!).shape σ m
  have hs0 := envOf_size0 (table[110]!).shape σ m
  have k600 := slot_word_keep hwf hm hR0s hwf' hm' hR0 hb0 hs0 (o := 600) (by decide) h600
  have k616 := slot_word_keep hwf hm hR0s hwf' hm' hR0 hb0 hs0 (o := 616) (by decide) h616
  have k336 := slot_word_keep hwf hm hR0s hwf' hm' hR0 hb0 hs0 (o := 336) (by decide) h336
  have k344 := slot_word_keep hwf hm hR0s hwf' hm' hR0 hb0 hs0 (o := 344) (by decide) h344
  have w608 := slot_word hwf' hm' hR0 hb0 hs0 (o := 608) (by decide) h608
  have hv : ∀ i, i < 32 → (Sym.var i).eval (envOf (table[110]!).shape σ m) =
      m.reg (Fin.ofNat 32 i) := fun i hi => by simp [Sym.eval, envOf, hi]
  have hreg' : ∀ i : Fin 32, m'.reg i =
      (l.S.reg i.val).eval (envOf (table[110]!).shape σ m) := fun i => (hm'.regs i).symm
  have hk64 : k < 2 ^ 64 := by omega
  have hsub : m.reg 22 - m.reg 20 = w (p - (j + k)) := by
    rw [r22, r20]
    apply BitVec.eq_of_toNat_eq
    simp only [w, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have e25 : m.reg 25 + 1 = w (n + 1) := by
    rw [r25]; simp only [w]; rw [BitVec.ofNat_add]; rfl
  refine ⟨c, h, p, n, j, k, hl, hsk1, hnk, hk32, hjk, hle, r22, ?_, ?_, ?_, ?_, ?_, hcm', k336,
    k344⟩
  · simp only [Sym.eval_bin, BinOp.eval, hv 22 (by decide), hv 20 (by decide)]
    exact hsub
  · rw [hreg' 23, show (23 : Fin 32).val = 23 from rfl, h23]
    have hv55 : (Sym.var 55).eval (envOf (table[110]!).shape σ m) = m.reg 23 - σ.inp := by
      simp [Sym.eval, envOf]
    have hp3 : (Sym.ptr 3 0).eval (envOf (table[110]!).shape σ m) = σ.inp := by
      simp only [Sym.eval, env_base3]; simp
    simp only [Sym.eval_bin, BinOp.eval, hv 20 (by decide), hv55, hp3]
    rw [show (Fin.ofNat 32 20 : Fin 32) = 20 from rfl, r23, r20]
    rw [show σ.inp + w (c + h + j) - σ.inp = w (c + h + j) by
      rw [BitVec.add_comm, BitVec.add_sub_cancel]]
    simp only [w]; rw [F1.add_add_ofNat, Nat.add_assoc (c + h)]
  · rw [hreg' 22, show (22 : Fin 32).val = 22 from rfl, h22]
    simp only [Sym.eval_bin, BinOp.eval, hv 22 (by decide), hv 20 (by decide)]
    exact hsub
  · rw [hreg' 25, show (25 : Fin 32).val = 25 from rfl, h25]
    simp only [Sym.eval_bin, BinOp.eval, hv 25 (by decide), Sym.eval_lit]
    exact e25
  · refine ⟨p0, cap, by rw [k600]; exact l0, ?_, by rw [k616]; exact l16, by omega, hp0, L, X,
      hlive', hbuf⟩
    rw [show (0x258 + 8 : Nat) = 608 from rfl, w608]
    simp only [Sym.eval_bin, BinOp.eval, hv 25 (by decide), Sym.eval_lit]
    rw [← e25]
    rfl

/-- List bytes left after the item (`0x80002138`, leaf 0): back to the loop head. -/
theorem DTF.leaf_80002138_0 :
    LeafGoal DTF.plan DTF.plan.cuts[110]! ((DTF.plan.leaves 0x80002138)[0]!) := by
  show LeafGoal vcPlan (mkCut (table[110]!)) ((leavesAt 0x80002138)[0]!)
  have hcut : CutOK vcPlan (mkCut (table[110]!)) := DTF.cut_80002138
  have hob : ((leavesAt 0x80002138)[0]!).obligs = [] := by decide
  have hexit : ((leavesAt 0x80002138)[0]!).exit = .at 0x800020ac := by decide
  have hsteps : ((leavesAt 0x80002138)[0]!).S.steps - (table[110]!).shape.S.steps = 13 := by
    decide
  have hreg : ((leavesAt 0x80002138)[0]!).S.regions = baseRegions ++ [slotR 32] := by decide
  have hS : (table[110]!).shape.S.regions = baseRegions ++ [slotR 32] := by decide
  have hne' : (table[107]!).pc ≠ entry := by decide
  have hrest0 : (table[110]!).rest = [⟨.slot 0x150, false, 11⟩, ⟨.slot 0x158, true, 11⟩] := by
    decide
  have hrest : (table[107]!).rest = (table[110]!).rest := by decide
  intro σ m hA hc
  obtain ⟨hwf, hm, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf hm hc
  refine ⟨fun o ho => (by rw [hob] at ho; cases ho), ?_, fun m' hm' hexok hso => ?_⟩
  · show ((leavesAt 0x80002138)[0]!).S.steps - (table[110]!).shape.S.steps ≤
      budgetOf (table[110]!) σ m
    unfold budgetOf
    rw [hsteps, show budgetAt (table[110]!).pc = (2564, .list (.reg 22)) from rfl]
    omega
  simp only [mkCut] at hm' hso
  rw [hexit] at hexok ⊢
  simp only [ExitOk] at hexok
  obtain ⟨c, h, p, n, j, k, hl, hsk1, hnk, hk32, hjk, hle, r22, hsub, e23, e22, e25, hdr, hcm',
    k336, k344⟩ := store_out hreg (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hA hm' hso
  obtain ⟨-, harm, hrst, -, -, -, hchk⟩ := store_src hA
  have hcond := hc _ (show SBool.ne (.bin .sub (.var 22) (.var 20)) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, hsub, bne_iff_ne, ne_eq] at hcond
  have hwf' := wf_of_regions hwf (hreg.trans hS.symm)
  have hR0 : ((leavesAt 0x80002138)[0]!).S.regions[0]? = some frameR := by rw [hreg]; rfl
  have hloop : HashLoop σ m' := ⟨c, h, p, n + 1, j + k, hl, hsk1, hnk, e23, e22, e25, hdr⟩
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  refine ExitGoal.at_cut rfl ⟨mkCut (table[107]!),
    List.mem_map_of_mem (targetOf_spec (pc := 0x800020ac) (d' := table[107]!) rfl).1, ?_, ?_, ?_⟩
  · rw [hexok]; rfl
  · simp only [mkCut, if_neg hne', ACut]
    refine .inl ⟨by decide, by rw [hexok]; rfl, hcm', shapeOk_of_holds hwf' hm' hR0 (by decide)
      (by decide), by rw [show (table[107]!).arms = (table[110]!).arms by decide]; exact harm,
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
    · rw [show (table[107]!).pc = 0x800020ac by decide]; simpa [Extra] using hloop
    · rw [show budgetAt (table[107]!).pc = (2871, .list (.reg 22)) from rfl]; trivial
    · rw [show chkCount (table[107]!).rest = chkCount (table[110]!).rest by decide]; exact hchk
  · show budgetOf (table[107]!) σ m' ≤ budgetOf (table[110]!) σ m -
      (((leavesAt 0x80002138)[0]!).S.steps - (table[110]!).shape.S.steps)
    rw [hsteps]
    unfold budgetOf restLen
    rw [show budgetAt (table[107]!).pc = (2871, .list (.reg 22)) from rfl,
      show budgetAt (table[110]!).pc = (2564, .list (.reg 22)) from rfl,
      show (table[107]!).rest.find? (·.len) = some ⟨.slot 0x158, true, 11⟩ by decide,
      show (table[110]!).rest.find? (·.len) = some ⟨.slot 0x158, true, 11⟩ by decide]
    simp only [innerOf, Loc.word, TX.wordAt, k344]
    rw [show (Fin.ofNat 32 22 : Fin 32) = 22 from rfl, e22, r22]
    simp only [w, BitVec.toNat_ofNat]
    have : p - (j + k) ≠ 0 := fun h0 => hcond (by rw [h0]; rfl)
    omega

/-- The list payload used up (`0x80002138`, leaf 1): `toOwnedSlice` on the header. -/
theorem DTF.leaf_80002138_1 :
    LeafGoal DTF.plan DTF.plan.cuts[110]! ((DTF.plan.leaves 0x80002138)[1]!) := by
  show LeafGoal vcPlan (mkCut (table[110]!)) ((leavesAt 0x80002138)[1]!)
  have hcut : CutOK vcPlan (mkCut (table[110]!)) := DTF.cut_80002138
  have hob : ((leavesAt 0x80002138)[1]!).obligs = [] := by decide
  have hexit : ((leavesAt 0x80002138)[1]!).exit = .call F4.entry 0x80002180 := by decide
  have hsteps : ((leavesAt 0x80002138)[1]!).S.steps - (table[110]!).shape.S.steps = 18 := by
    decide
  have hreg : ((leavesAt 0x80002138)[1]!).S.regions = baseRegions ++ [slotR 32] := by decide
  have hS : (table[110]!).shape.S.regions = baseRegions ++ [slotR 32] := by decide
  have hne' : (table[111]!).pc ≠ entry := by decide
  have hrest0 : (table[110]!).rest = [⟨.slot 0x150, false, 11⟩, ⟨.slot 0x158, true, 11⟩] := by
    decide
  have hrest : (siteAt 111).rest = (table[110]!).rest := by decide
  have hkind : (siteAt 111).kind = .f4 := by decide
  have hSF : (siteAt 111).kind.SiteFine (siteAt 111) = true := by decide
  intro σ m hA hc
  obtain ⟨hwf, hm, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf hm hc
  refine ⟨fun o ho => (by rw [hob] at ho; cases ho), ?_, fun m' hm' hexok hso => ?_⟩
  · show ((leavesAt 0x80002138)[1]!).S.steps - (table[110]!).shape.S.steps ≤
      budgetOf (table[110]!) σ m
    unfold budgetOf
    rw [hsteps, show budgetAt (table[110]!).pc = (2564, .list (.reg 22)) from rfl]
    omega
  simp only [mkCut] at hm' hso
  rw [hexit] at hexok ⊢
  simp only [ExitOk] at hexok
  obtain ⟨c, h, p, n, j, k, hl, hsk1, hnk, hk32, hjk, hle, r22, hsub, e23, e22, e25, hdr, hcm',
    k336, k344⟩ := store_out hreg (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hA hm' hso
  obtain ⟨-, harm, hrst, -, -, -, hchk⟩ := store_src hA
  have hcond := hc _ (show SBool.eq (.bin .sub (.var 22) (.var 20)) (.lit 0) ∈ _ by decide)
  simp only [SBool.eval, hsub, beq_iff_eq] at hcond
  have hwf' := wf_of_regions hwf (hreg.trans hS.symm)
  have hR0 : ((leavesAt 0x80002138)[1]!).S.regions[0]? = some frameR := by rw [hreg]; rfl
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  -- the call machine
  have hr1 : m'.reg 1 = w 0x80002180 := by
    rw [← hm'.regs 1]
    show (((leavesAt 0x80002138)[1]!).S.reg 1).eval _ = _
    rw [show ((leavesAt 0x80002138)[1]!).S.reg 1 = .lit 0x80002180 by decide]
    rfl
  have hshp : ShapeOk σ (siteAt 111).shape m' :=
    shapeOk_of_holds hwf' hm' hR0 (by decide) (by decide)
  have hsp : m'.reg 2 = σ.fr + w 0 := hshp.1 (2, .fr 0) (by decide) _ rfl
  have hres : m'.reg 10 = σ.fr + w 0x270 := hshp.1 (10, .fr 0x270) (by decide) _ rfl
  have hhdr : m'.reg 11 = σ.fr + w 0x258 := hshp.1 (11, .fr 0x258) (by decide) _ rfl
  have hao : m'.reg 12 = σ.ao + w 0 := hshp.1 (12, .ao 0) (by decide) _ rfl
  have hra : RetAligned m' := by unfold RetAligned; rw [hr1]; decide
  obtain ⟨L, X, items, hpre4, hlive, hbuf⟩ := f4_pre_dtf hcm' hsp hres hhdr hao
    (by decide) (by decide) (by decide) (by decide) (by decide) hdr hra
  have hidx : IdxOk (siteAt 111).kind σ (L, items, ⟨[], []⟩) m' := by
    rw [hkind]; exact ⟨hpre4, X, hlive, hbuf⟩
  have hrst' : RestOk σ m' (siteAt 111).rest := by
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
  have harm' : ArmOk σ (siteAt 111).arms := by
    rw [show (siteAt 111).arms = (table[110]!).arms by decide]; exact harm
  have hsite : SiteA (siteAt 111) (table[111]!).pc σ (L, items, ⟨[], []⟩) m' := by
    rw [show (table[111]!).pc = 0x80002180 by decide]
    refine ⟨hr1, hcm', hshp, harm', hrst', hidx, fun f hf => ?_, ?_,
      siteX_of_no (by decide) σ _ m'⟩
    · rw [show siteFields 0x80002180 = [] by decide] at hf; cases hf
    · rw [show chkCount (siteAt 111).rest = chkCount (table[110]!).rest by decide]; exact hchk
  refine ⟨calleeOf (siteAt 111).kind, (L, items, ⟨[], []⟩), ?_, ?_, hidx.1, fun m'' hpost => ?_⟩
  · show calleeAt 0x80002180 = _
    unfold calleeAt
    rw [show table.find? (·.pc = 0x80002180) = targetOf (table[111]!).pc from rfl,
      show targetOf (table[111]!).pc = some (table[111]!) from rfl]
    rfl
  · rw [hexok, hkind]; rfl
  obtain ⟨hret, -, hkeep⟩ := ret_common hSF hsite hpost
  have hpc'' : m''.pc.toNat = 0x80002180 := by rw [hret.1, hr1]; decide
  refine ⟨mkCut (table[111]!),
    List.mem_map_of_mem (targetOf_spec (pc := 0x80002180) (d' := table[111]!) rfl).1,
    by decide, hpc'', ?_, ?_⟩
  · simp only [mkCut, if_neg hne', ACut]
    exact .inr ⟨siteAt 111, rfl, m', _, hsite, hpost⟩
  -- the budget: no list bytes left
  have k344' := hkeep 344 (by decide) (by decide)
  show (siteAt 111).kind.bound + budgetOf (table[111]!) σ m'' ≤ budgetOf (table[110]!) σ m -
    (((leavesAt 0x80002138)[1]!).S.steps - (table[110]!).shape.S.steps)
  rw [hsteps, show (siteAt 111).kind.bound = 194 by decide]
  unfold budgetOf restLen
  rw [show budgetAt (table[111]!).pc = (2352, .none) from rfl,
    show budgetAt (table[110]!).pc = (2564, .list (.reg 22)) from rfl,
    show (table[111]!).rest.find? (·.len) = some ⟨.slot 0x158, true, 11⟩ by decide,
    show (table[110]!).rest.find? (·.len) = some ⟨.slot 0x158, true, 11⟩ by decide]
  simp only [innerOf, Loc.word, TX.wordAt]
  rw [show (0x158 : Nat) = 344 from rfl, k344', k344]
  omega

end ZesuExec.Fn.DTF
