import ZesuExec.Fn.SszRoot.ProgCall

/-!
# `progressiveRootAt`: leaves

Entry (`runE`): no chunks, 32 zero bytes and return; else `sparseRoot` (`DGoal`, `entry_call`) on
`sz` chunks, the two leaves differing in how `sz` is computed. After `sparseRoot` (`runS`): the
recursive call (`SelfGoal`). After it (`runR`): `zkvm_sha256` on the 64 bytes at `fb + 0x28` into
`fb + 8` (`sha_exit`). After it (`runH`): the result copied out, return.
-/

namespace ZesuExec.Fn.SszRoot.Prog
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

variable (hsha : ShaSpec) (hsp : SparseSpec)

/-! ## Leaf facts (by `decide`) -/

abbrev ESaved (l : Leaf) : Prop :=
  ∀ q < 7, ∀ t < 8, byteVal l.S.mem 0 (0x68 + 8 * q + t) = some (.var (savedReg q).val, t)

abbrev EShape (l : Leaf) : Prop :=
  l.S.reg 2 = .ptr 0 0 ∧ l.S.reg 8 = .ptr 0 0xa0 ∧ l.S.reg 9 = .ptr 1 0 ∧
  (∀ i ∈ [22, 23, 24, 25, 26, 27], l.S.reg i = .var i) ∧ l.S.regions.length = 2 ∧ ESaved l ∧
  l.exit = .call sparseEntry pcS ∧ l.obligs = [] ∧ l.S.reg 1 = .lit pcS ∧
  l.S.reg 10 = .ptr 0 40 ∧ l.S.reg 11 = .var 11 ∧ l.S.reg 13 = .var 13 ∧ l.S.reg 18 = .var 12 ∧
  l.S.reg 20 = .var 11 ∧ l.S.reg 21 = .var 13 ∧ l.S.steps ≤ 22

def M2 : Nat := 18446744073709551614
def sllD : Sym := .bin .sll (.lit 1) (.var 13)

theorem lE : runE_leaves = [runE_leaves[0], runE_leaves[1], runE_leaves[2]] := rfl

theorem fE0 : runE_leaves[0].conds = [.eq (.var 12) (.lit 0)] ∧
    runE_leaves[0].obligs = [.aligned (.bin .and (.var 1) (.lit M2)) 4] ∧
    runE_leaves[0].exit = .ret (.bin .and (.var 1) (.lit M2)) ∧ runE_leaves[0].S.steps = 24 ∧
    runE_leaves[0].S.reg 2 = .ptr 0 0xa0 ∧
    (∀ i ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], runE_leaves[0].S.reg i = .var i) ∧
    runE_leaves[0].S.regions.length = 2 ∧
    (∀ j < 32, byteLit runE_leaves[0].S.mem 1 j = some 0) := by decide

theorem fE1 : EShape runE_leaves[1] ∧
    runE_leaves[1].conds = [.ne (.var 12) (.lit 0), .ltu sllD (.var 12)] ∧
    runE_leaves[1].S.reg 12 = sllD ∧ runE_leaves[1].S.reg 19 = sllD := by decide

theorem fE2 : EShape runE_leaves[2] ∧
    runE_leaves[2].conds = [.ne (.var 12) (.lit 0), .geu sllD (.var 12)] ∧
    runE_leaves[2].S.reg 12 = .var 12 ∧ runE_leaves[2].S.reg 19 = .var 12 := by decide

/-- The leaves of `cS` and `cR`: a call, no memory, the callee-saved registers kept. -/
abbrev MidShape (l : Leaf) (t r : Nat) (steps : Nat) : Prop :=
  l.exit = .call t r ∧ l.conds = [] ∧ l.obligs = [] ∧ l.S.steps = steps ∧ l.S.reg 1 = .lit r ∧
  (∀ i ∈ [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], l.S.reg i = .var i)

theorem lS : runS_leaves = [runS_leaves[0]] := rfl
theorem lR : runR_leaves = [runR_leaves[0]] := rfl
theorem lH : runH_leaves = [runH_leaves[0]] := rfl

theorem fS : MidShape runS_leaves[0] progEntry pcR 7 ∧
    runS_leaves[0].S.reg 10 = .bin .add (.var 8) (.lit 18446744073709551528) ∧
    runS_leaves[0].S.reg 11 = .bin .add (.var 20) (.bin .sll (.var 19) (.lit 5)) ∧
    runS_leaves[0].S.reg 12 = .bin .sub (.var 18) (.var 19) ∧
    runS_leaves[0].S.reg 13 = .bin .add (.var 21) (.lit 2) := by decide

theorem fR : MidShape runR_leaves[0] Sha256.entry pcH 5 ∧
    runR_leaves[0].S.reg 10 = .bin .add (.var 8) (.lit 18446744073709551496) ∧
    runR_leaves[0].S.reg 11 = .lit 64 ∧
    runR_leaves[0].S.reg 12 = .bin .add (.var 8) (.lit 18446744073709551464) := by decide

theorem fH : runH_leaves[0].conds = [] ∧
    runH_leaves[0].obligs = [.aligned (.bin .and (.init 0 152 8) (.lit M2)) 4] ∧
    runH_leaves[0].exit = .ret (.bin .and (.init 0 152 8) (.lit M2)) ∧
    runH_leaves[0].S.steps = 18 ∧ runH_leaves[0].S.reg 2 = .ptr 0 0xa0 ∧
    runH_leaves[0].S.reg 8 = .init 0 144 8 ∧ runH_leaves[0].S.reg 9 = .init 0 136 8 ∧
    runH_leaves[0].S.reg 18 = .init 0 128 8 ∧ runH_leaves[0].S.reg 19 = .init 0 120 8 ∧
    runH_leaves[0].S.reg 20 = .init 0 112 8 ∧ runH_leaves[0].S.reg 21 = .init 0 104 8 ∧
    (∀ i ∈ [22, 23, 24, 25, 26, 27], runH_leaves[0].S.reg i = .var i) ∧
    runH_leaves[0].S.regions.length = 2 ∧
    (∀ j < 32, byteSrc runH_leaves[0].S.mem 1 j = some (0, 8 + j)) := by decide


/-! ## Entry leaves -/

theorem entry_keep {g m' : Machine} {l : Leaf} (hpre : ProgPre g) (hn : lenOf g ≠ 0)
    (hwf : Env.WF (entryEnv g (regsE g)) SE) (hm' : Match (entryEnv g (regsE g)) l.S m')
    (hso : SameOutside (InWritable (entryEnv g (regsE g)) SE) g m') (hsh : EShape l) :
    Keep g m' := by
  obtain ⟨s2, s8, s9, sk, hreg, hsv, -⟩ := hsh
  have F := PreFacts.of hpre.2
  have hN := need_ge g
  have hlo := F.spLo; have hhi := F.spHi
  have hb0 : (entryEnv g (regsE g)).base 0 = fb g := by simp [Env.base, entryEnv, regsE, fb]
  have hb1 : (entryEnv g (regsE g)).base 1 = g.reg 10 := by simp [Env.base, entryEnv, regsE]
  refine ⟨hpre, hn, ?_, preserved_of_leaf hwf hm' (by simp [SE, entryState, hreg]) hso, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro a ha
    apply hso a
    intro hw
    obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := inWritable_of hw
    rcases r with _ | _ | r
    · simp only [regsE, List.getD_cons_zero] at hj ha
      have hfbd : g.reg 2 - BitVec.ofNat 64 0xa0 = fb g := rfl
      rw [hfbd] at ha
      apply ha
      have e := fb_add_toNat F (c := j) (by omega)
      exact written_stack F (by rw [e]; omega) (by rw [e]; omega)
    · simp only [regsE, List.getD_cons_succ, List.getD_cons_zero] at hj ha
      exact ha (written_out F hj rfl)
    · simp [SE, entryState] at hR
  · intro q hq t ht
    have := mem_of_val hm' (r := 0) (by omega) (by simp [Env.size, entryEnv, regsE]; omega)
      (hsv q hq t ht)
    simp only [regsE, List.getD_cons_zero] at this
    rw [show fb g = g.reg 2 - BitVec.ofNat 64 0xa0 from rfl, this]
    simp [Sym.eval, entryEnv_vars]
  · rw [reg_eq_of hm' 2 s2]; simp [Sym.eval, hb0]
  · rw [reg_eq_of hm' 8 s8, Sym.eval_ptr, hb0]
    exact (fb_ofInt g 0xa0 (by omega)).trans (by simp [fb, BitVec.sub_add_cancel])
  · rw [reg_eq_of hm' 9 s9, Sym.eval_ptr, hb1]; simp
  · intro i hi
    have hi' : i.val ∈ [22, 23, 24, 25, 26, 27] := by
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [reg_eq_of hm' i (sk i.val hi'), Sym.eval_var, entryEnv_var]

/-- `sparseRoot` from the entry, on `sz g` chunks. -/
theorem entry_call {g m' : Machine} {l : Leaf} {rem : Nat} (hpre : ProgPre g) (hn : lenOf g ≠ 0)
    (hwf : Env.WF (entryEnv g (regsE g)) SE) (hm' : Match (entryEnv g (regsE g)) l.S m')
    (hso : SameOutside (InWritable (entryEnv g (regsE g)) SE) g m') (hsh : EShape l)
    (r12 : lenOf m' = sz g) (r19 : m'.reg 19 = BitVec.ofNat 64 (sz g))
    (hpc : m'.pc.toNat = sparseEntry) (hrem : sparseCost (depthOf g) (sz g) + restS g ≤ rem) :
    DGoal (plan hsha hsp) g m' rem pcS := by
  have hk := entry_keep hpre hn hwf hm' hso hsh
  obtain ⟨-, -, -, -, -, -, -, -, s1, s10, s11, s13, s18, s20, s21, _⟩ := hsh
  have F := PreFacts.of hpre.2
  have hd26 := (progFits_ne hn hpre.1).1
  have hb0 : (entryEnv g (regsE g)).base 0 = fb g := by simp [Env.base, entryEnv, regsE, fb]
  have r1 : m'.reg 1 = BitVec.ofNat 64 pcS := by rw [reg_eq_of hm' 1 s1]; rfl
  have r10 : m'.reg 10 = fb g + BitVec.ofNat 64 0x28 := by
    rw [reg_eq_of hm' 10 s10, Sym.eval_ptr, hb0]; exact fb_ofInt g 0x28 (by omega)
  have r11 : m'.reg 11 = chunkPtr g + BitVec.ofNat 64 (32 * 0) := by
    rw [reg_eq_of hm' 11 s11]; simp [Sym.eval, entryEnv_vars]
  have r13 : depthOf m' = depthOf g := by
    simp only [depthOf]; rw [reg_eq_of hm' 13 s13]; rfl
  have r18 : m'.reg 18 = g.reg 12 := by rw [reg_eq_of hm' 18 s18]; rfl
  have r20 : m'.reg 20 = g.reg 11 := by rw [reg_eq_of hm' 20 s20]; rfl
  have r21 : m'.reg 21 = g.reg 13 := by rw [reg_eq_of hm' 21 s21]; rfl
  have hns := need_sparse hn r13
  refine ⟨sparseD hsp, by simp [plan], hpc, (), ⟨⟨by rw [r13]; exact hd26,
    callee_pre hk (by simp only [RetAligned, r1]; decide) hns r10 (by omega) r11 r12
      (by have := sz_le g; omega)⟩, r13, r12⟩, fun k m'' hrun _ hpost => ?_⟩
  obtain ⟨hk'', -⟩ := keep_after hk (o := 0x28) (by omega) (written_callee hk hns r10 (by omega))
    hpost.2.2 hpost.1.2 hrun.preserved
  have hcs := hpost.1.2
  refine ⟨cS, by simp [plan, cuts], by rw [hpost.1.1, r1]; rfl,
    ⟨hk'', by rw [hpost.1.1, r1]; rfl, by rw [hcs 18 (by decide), r18],
      by rw [hcs 19 (by decide), r19], by rw [hcs 20 (by decide), r20],
      by rw [hcs 21 (by decide), r21], ?_⟩, ?_⟩
  · have hb := hpost.2.1
    simp only [outOf, r10] at hb
    rw [show chunkPtr m' = chunkPtr g + BitVec.ofNat 64 (32 * 0) from r11, r12, r13,
      chunks_same hpre hk.2.2.1 (by have := sz_le g; omega)] at hb
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hb
    rw [leftRoot, chunksOf_take]; exact hb
  · show sparseCost (depthOf g) (sz g) + restS g ≤ rem
    exact hrem

theorem sll_eval {g : Machine} (hd : depthOf g ≤ 26) :
    (sllD.eval (entryEnv g (regsE g))).toNat = pw g := by
  show ((1 : Word) <<< ((g.reg (Fin.ofNat 32 13)).toNat % 64)).toNat = _
  rw [show g.reg (Fin.ofNat 32 13) = g.reg 13 from rfl, Nat.mod_eq_of_lt (by simp only [depthOf] at hd; omega),
    shl_toNat (by simp only [depthOf] at hd; omega)]

theorem cond_ne {m : Machine}
    (c1 : (SBool.ne (.var 12) (.lit 0)).eval (entryEnv m (regsE m)) = true) : lenOf m ≠ 0 := by
  intro h0
  have : m.reg 12 = 0 := by apply BitVec.eq_of_toNat_eq; simpa [lenOf] using h0
  simp [SBool.eval, Sym.eval_var, Sym.eval_lit, entryEnv_vars,
    show m.reg (Fin.ofNat 32 12) = m.reg 12 from rfl, this] at c1

/-- An entry leaf calling `sparseRoot` on `sz` chunks. -/
theorem call_leaf {m : Machine} {l : Leaf} (hpre : ProgPre m) (hn : lenOf m ≠ 0)
    (hwf : Env.WF (entryEnv m (regsE m)) SE) (hsh : EShape l)
    (r12 : ∀ m', Match (entryEnv m (regsE m)) l.S m' → lenOf m' = sz m)
    (r19 : ∀ m', Match (entryEnv m (regsE m)) l.S m' → m'.reg 19 = BitVec.ofNat 64 (sz m)) :
    (∀ o ∈ l.obligs, o.holds (entryEnv m (regsE m))) ∧
    l.S.steps - cE.S.steps ≤ cE.budget m m ∧
    ∀ m', Match (entryEnv m (regsE m)) l.S m' → ExitOk (entryEnv m (regsE m)) l.exit m' →
      SameOutside (InWritable (entryEnv m (regsE m)) cE.S) m m' →
      ExitGoalR (plan hsha hsp) m m' (cE.budget m m - (l.S.steps - cE.S.steps)) l.exit := by
  have hob := hsh.2.2.2.2.2.2.2.1
  have hex := hsh.2.2.2.2.2.2.1
  have hst := hsh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hcost := progCost_ne (d := depthOf m) hn
  rw [Nat.min_comm] at hcost
  have hb : cE.budget m m = progCost (lenOf m) (depthOf m) := rfl
  have h0 : cE.S.steps = 0 := rfl
  refine ⟨by rw [hob]; simp, by rw [hb, h0]; omega, fun m' hm' he hso => ?_⟩
  rw [hex] at he ⊢
  refine ExitGoalR.dcall (entry_call hsha hsp hpre hn hwf hm' hso hsh (r12 m' hm') (r19 m' hm') he ?_)
  rw [hb, h0]; simp only [restS, sz, pw]; omega

theorem leaf_E : ∀ l ∈ runE_leaves, LeafGoalR (plan hsha hsp) cE l := by
  intro l hl
  rw [lE] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rintro g m ⟨rfl, hpc, hpre⟩ hc
  have hcut := cut_E hsha hsp m m ⟨rfl, hpc, hpre⟩
  have F := PreFacts.of hpre.2
  rw [show cE.env m m = entryEnv m (regsE m) from rfl] at hc ⊢
  have hc' : ∀ b ∈ l.conds, b.eval (entryEnv m (regsE m)) = true := hc
  have hr12 : m.reg (Fin.ofNat 32 12) = m.reg 12 := rfl
  rcases hl with rfl | rfl | rfl
  · -- no chunks: 32 zero bytes
    obtain ⟨hcs, hob, hex, hst, s2, sk, hreg, hlit⟩ := fE0
    rw [hcs] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hc'
    simp only [SBool.eval, Sym.eval_var, Sym.eval_lit, entryEnv_vars, hr12] at hc'
    have hn0 : lenOf m = 0 := by have := beq_iff_eq.mp hc'; simp only [lenOf]; rw [this]; rfl
    have hneed : progNeed m = 0xa0 := by unfold progNeed; rw [hn0, progStack, if_pos rfl]
    have hN := need_ge m
    have hlo := F.spLo; have hhi := F.spHi
    have hra : ((Sym.bin .and (.var 1) (.lit M2)).eval (entryEnv m (regsE m))) = m.reg 1 &&& ~~~1 := by
      simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval, entryEnv_vars, M2, not_one_eq]
      rfl
    refine ⟨?_, by
      show runE_leaves[0].S.steps - 0 ≤ progCost (lenOf m) (depthOf m)
      rw [hst, hn0, progCost, if_pos rfl]; omega, fun m' hm' he hso => ?_⟩
    · rw [hob]; intro o ho; rw [List.mem_singleton] at ho; subst ho
      show ((Sym.bin .and (.var 1) (.lit M2)).eval (entryEnv m (regsE m))).toNat % 4 = 0
      rw [hra]; exact F.ra
    rw [hex] at he ⊢
    left
    show ProgPost m m'
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [ExitOk] at he; rw [he, hra]
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
      rintro i (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · rw [reg_eq_of hm' 2 s2, Sym.eval_ptr]
        show fb m + _ = _
        exact (fb_ofInt m 0xa0 (by omega)).trans (by simp [fb, BitVec.sub_add_cancel])
      all_goals
        rw [reg_eq_of hm' _ (sk _ (by decide)), Sym.eval_var, entryEnv_var]
    · rw [show chunksOf m (chunkPtr m) (lenOf m) = [] by simp [hn0, chunksOf], progressiveRootAt,
        if_pos rfl]
      intro i hi
      simp only [zeroHash, zeroChunk, List.length_replicate] at hi ⊢
      have := mem_of_lit hm' (r := 1) (by omega) (by simp [Env.size, entryEnv, regsE]; omega)
        (hlit i hi)
      simp only [regsE, List.getD_cons_succ, List.getD_cons_zero] at this
      rw [this, List.getElem_replicate]
    · intro a ha
      apply hso a
      intro hw
      obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := inWritable_of hw
      rcases r with _ | _ | r
      · simp only [regsE, List.getD_cons_zero] at hj ha
        have hfbd : m.reg 2 - BitVec.ofNat 64 0xa0 = fb m := rfl
        rw [hfbd] at ha
        apply ha
        have e := fb_add_toNat F (c := j) (by omega)
        exact written_stack F (by rw [e]; omega) (by rw [e]; omega)
      · simp only [regsE, List.getD_cons_succ, List.getD_cons_zero] at hj ha
        exact ha (written_out F hj rfl)
      · simp [SE, entryState] at hR
  · obtain ⟨hsh, hcs, s12, s19⟩ := fE1
    rw [hcs] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc'
    obtain ⟨c1, c2⟩ := hc'
    have hn := cond_ne c1
    have hpw : pw m < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (progFits_ne hn hpre.1).1) (by decide)
    have hsl := sll_eval (g := m) (progFits_ne hn hpre.1).1
    have hlt : pw m < lenOf m := by
      simp only [SBool.eval, Sym.eval_var, entryEnv_vars, hr12, BitVec.ult, decide_eq_true_eq,
        hsl] at c2
      exact c2
    have hsz : sz m = pw m := by unfold sz; omega
    refine call_leaf hsha hsp hpre hn hcut.1 hsh (fun m' hm' => ?_) (fun m' hm' => ?_)
    · simp only [lenOf]; rw [reg_eq_of hm' 12 s12, hsl, hsz]
    · rw [reg_eq_of hm' 19 s19]; apply BitVec.eq_of_toNat_eq
      rw [hsl, hsz, toNat_ofNat_lt hpw]
  · obtain ⟨hsh, hcs, s12, s19⟩ := fE2
    rw [hcs] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc'
    obtain ⟨c1, c2⟩ := hc'
    have hn := cond_ne c1
    have hsl := sll_eval (g := m) (progFits_ne hn hpre.1).1
    have hge : lenOf m ≤ pw m := by
      simp only [SBool.eval, Sym.eval_var, entryEnv_vars, hr12, BitVec.ult, Bool.not_eq_true',
        decide_eq_false_iff_not, Nat.not_lt, hsl] at c2
      exact c2
    have hsz : sz m = lenOf m := by unfold sz; omega
    refine call_leaf hsha hsp hpre hn hcut.1 hsh (fun m' hm' => ?_) (fun m' hm' => ?_)
    · simp only [lenOf]; rw [reg_eq_of hm' 12 s12, hsz]; rfl
    · rw [reg_eq_of hm' 19 s19]; apply BitVec.eq_of_toNat_eq
      rw [hsz, toNat_ofNat_lt (m.reg 12).isLt]; rfl
end ZesuExec.Fn.SszRoot.Prog
