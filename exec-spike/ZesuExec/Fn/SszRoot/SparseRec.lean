import ZesuExec.Fn.SszRoot.SparseVc

/-!
# `sparseRoot`: the recursive calls, assembly, `sparseRoot_spec`

The entry leaves (depth 0: the first chunk or the zero chunk to `c54`; depth ≥ 1: the left
recursive call) and the leaves after the left call (`ccK (depth - 1)` when no chunk reaches the
right half, else the right recursive call). The recursive calls are `SelfGoal`s: the callee's
precondition is `callee_pre`, what the caller keeps across them is `after_self`. `vc_sound_rec`
assembles the plan.
-/

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

theorem cost_split {g : Machine} (hd : 1 ≤ depthOf g) :
    sparseCost (depthOf g) (lenOf g) = 25 + sparseCost (depthOf g - 1) (min (lenOf g) (half g)) +
      rest70 g := by
  obtain ⟨k, hk⟩ : ∃ k, depthOf g = k + 1 := ⟨depthOf g - 1, by omega⟩
  simp only [rest70, half, hk, Nat.add_sub_cancel, sparseCost]

theorem half_toNat {g : Machine} (hpre : SparsePre g) (hd : 1 ≤ depthOf g) :
    ((1 : Word) <<< ((g.reg 13 - 1).toNat % 64)).toNat = half g := by
  have h26 := hpre.1
  have : (g.reg 13 - 1).toNat = depthOf g - 1 := by
    simp only [depthOf] at hd ⊢; rw [BitVec.toNat_sub]; simp; omega
  rw [this, Nat.mod_eq_of_lt (by omega), shl_toNat (by omega)]

/-- What a caller keeps across a recursive call with its result at `fb + o`. -/
theorem fr_after {g m' m'' : Machine} (hk : Fr g m') {o : Nat} (ho : o + 32 ≤ 0xe8)
    (r10 : m'.reg 10 = fb g + BitVec.ofNat 64 o) (r13 : depthOf m' = depthOf g - 1)
    (hpost : SparsePost m' m'') (hrun : Preserved m' m'') :
    Fr g m'' ∧ (∀ a : Word, (g.reg 2).toNat - 0x120 ≤ a.toNat → a.toNat < (g.reg 2).toNat →
        ¬ ((g.reg 2).toNat - 0x120 + o ≤ a.toNat ∧ a.toNat < (g.reg 2).toNat - 0x120 + o + 32) →
        m''.mem a = m'.mem a) ∧ (∀ i ∈ calleeSaved, m''.reg i = m'.reg i) ∧
      m''.pc = m'.reg 1 &&& ~~~1 := by
  obtain ⟨⟨hpre, hso, hp, hS, h2, h9, hkeep⟩, hd, h8, h19⟩ := hk
  obtain ⟨⟨hpc, hcs⟩, -, hso2⟩ := hpost
  obtain ⟨hso', hfr⟩ := after_self hpre hd hso h2 r10 (by omega) r13 hso2
  have F := PreFacts.of hpre.2
  have hN := need_ge g
  have hlo := F.spLo; have hhi := F.spHi
  refine ⟨⟨⟨hpre, hso', hp.trans hrun, ?_, ?_, ?_, ?_⟩, hd, ?_, ?_⟩, hfr, hcs, hpc⟩
  · intro q hq t ht
    rw [hfr _ ?_ ?_ ?_, hS q hq t ht]
    all_goals rw [fb_add F, toNat_ofNat_lt (by simp [Layout.ramHi] at hhi; omega)]
    all_goals omega
  · rw [hcs 2 (by decide), h2]
  · rw [hcs 9 (by decide), h9]
  · intro i hi
    rw [hcs i (by simp [keepRegs, calleeSaved] at hi ⊢; omega), hkeep i hi]
  · rw [hcs 8 (by decide), h8]
  · rw [hcs 19 (by decide), h19]

end ZesuExec.Fn.SszRoot.Sparse

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

def decS : Sym := .bin .add (.var 13) (.lit 18446744073709551615)

/-- The left recursive call from the entry (`n'` chunks: `min len half`). -/
theorem entry_call {g m' : Machine} {l : Leaf} {n' rem : Nat} (hpre : SparsePre g)
    (hd : 1 ≤ depthOf g) (hn' : n' = min (lenOf g) (half g))
    (hwf : Env.WF (entryEnv g (regsE g)) SE) (hm' : Match (entryEnv g (regsE g)) l.S m')
    (hso : SameOutside (InWritable (entryEnv g (regsE g)) SE) g m') (hsh : EShape l)
    (s1 : l.S.reg 1 = .lit pc70) (s10 : l.S.reg 10 = .ptr 0 40) (s11 : l.S.reg 11 = .ptr 1 0)
    (r12 : lenOf m' = n') (s13 : l.S.reg 13 = decS) (s18 : l.S.reg 18 = .ptr 1 0)
    (s20 : l.S.reg 20 = decS) (s21 : l.S.reg 21 = .bin .sll (.lit 1) decS)
    (hpc : m'.pc.toNat = sparseEntry) (hrem : sparseCost (depthOf g) (lenOf g) - 25 ≤ rem) :
    SelfGoal (plan hsha) g m' rem pc70 := by
  obtain ⟨hk, h8, h19⟩ := entry_keep hpre hwf hm' hso hsh
  have F := PreFacts.of hpre.2
  have hr : ∀ (i : Fin 32) (s : Sym), l.S.reg i.val = s → m'.reg i = s.eval (entryEnv g (regsE g)) :=
    fun i s h => by rw [← hm'.regs i, h]
  have hb0 : (entryEnv g (regsE g)).base 0 = fb g := by simp [Env.base, entryEnv, regsE, fb]
  have hb1 : (entryEnv g (regsE g)).base 1 = chunkPtr g := by simp [Env.base, entryEnv, regsE]
  have r1 : m'.reg 1 = BitVec.ofNat 64 pc70 := by rw [hr 1 _ s1]; rfl
  have r10 : m'.reg 10 = fb g + BitVec.ofNat 64 0x28 := by
    rw [hr 10 _ s10, Sym.eval_ptr, hb0]; exact fb_ofInt g 0x28 (by omega)
  have r11 : m'.reg 11 = chunkPtr g + BitVec.ofNat 64 (32 * 0) := by
    rw [hr 11 _ s11, Sym.eval_ptr, hb1]; simp
  have r18 : m'.reg 18 = chunkPtr g := by rw [hr 18 _ s18, Sym.eval_ptr, hb1]; simp
  have rdec : decS.eval (entryEnv g (regsE g)) = g.reg 13 - 1 := by
    simp only [decS, Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval, entryEnv_vars]
    exact dec_eq _
  have r13 : depthOf m' = depthOf g - 1 := by
    simp only [depthOf]; rw [hr 13 _ s13, rdec, BitVec.toNat_sub]
    simp only [depthOf] at hd; simp; omega
  have r20 : m'.reg 20 = g.reg 13 - 1 := by rw [hr 20 _ s20, rdec]
  have r21 : m'.reg 21 = (1 : Word) <<< ((g.reg 13 - 1).toNat % 64) := by
    rw [hr 21 _ s21, Sym.eval_bin, rdec]; rfl
  have hfr : Fr g m' := ⟨hk, hd, h8, h19⟩
  have hcost := cost_split (g := g) hd
  refine ⟨cE, by show cE ∈ cuts; simp [cuts], m', ⟨rfl, hpc, ?_⟩, ?_, fun k m'' hrun hk' hpost => ?_⟩
  · exact callee_pre hpre hk.2.2.1 hd hk.2.2.2.2.1 (by simp only [RetAligned, r1]; decide) r13 r10
      (by omega) r11 r12 (by omega)
  · show sparseCost (depthOf m') (lenOf m') ≤ rem
    rw [r13, r12, hn']; omega
  obtain ⟨hfr'', -, hcs, hpc''⟩ := fr_after hfr (o := 0x28) (by omega) r10 r13 hpost hrun.preserved
  refine ⟨c70, by show c70 ∈ cuts; simp [cuts], by rw [hpc'', r1]; rfl,
    ⟨hfr'', by rw [hpc'', r1]; rfl, by rw [hcs 18 (by decide), r18], by rw [hcs 20 (by decide), r20],
      by rw [hcs 21 (by decide), r21], ?_⟩, ?_⟩
  · have hb := hpost.2.1
    simp only [outOf, r10] at hb
    rw [show chunkPtr m' = chunkPtr g + BitVec.ofNat 64 (32 * 0) from r11, r12, r13,
      chunks_same hpre hk.2.1 (by omega)] at hb
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hb
    rw [leftRoot, chunksOf_take]; rw [hn', Nat.min_comm] at hb; exact hb
  · show sparseCost (depthOf m') (lenOf m') + rest70 g ≤ rem
    rw [r13, r12, hn']; omega

theorem lE : runE_leaves = [runE_leaves[0], runE_leaves[1], runE_leaves[2], runE_leaves[3]] := rfl

theorem shE : ∀ l ∈ runE_leaves, EShape l := by decide

theorem fE0 : runE_leaves[0].conds = [.eq (.bin .and (.var 13) (.lit 255)) (.lit 0),
      .eq (.var 12) (.lit 0)] ∧
    runE_leaves[0].obligs = [] ∧ runE_leaves[0].exit = .at pc54 ∧ runE_leaves[0].S.steps = 18 ∧
    runE_leaves[0].S.reg 18 = .lit 0x801154c0 := by decide

theorem fE1 : runE_leaves[1].conds = [.eq (.bin .and (.var 13) (.lit 255)) (.lit 0),
      .ne (.var 12) (.lit 0)] ∧
    runE_leaves[1].obligs = [.inBounds 1 0 (.lit 0) 1 8, .inBounds 1 8 (.lit 0) 1 8,
      .inBounds 1 16 (.lit 0) 1 8, .inBounds 1 24 (.lit 0) 1 8] ∧
    runE_leaves[1].exit = .at pc54 ∧ runE_leaves[1].S.steps = 25 ∧
    runE_leaves[1].S.reg 18 = .ptr 0 8 ∧
    (∀ j < 32, byteSrc runE_leaves[1].S.mem 0 (8 + j) = some (1, j)) := by decide

theorem fE2 : runE_leaves[2].conds = [.ne (.bin .and (.var 13) (.lit 255)) (.lit 0),
      .ltu (.var 12) (.bin .sll (.lit 1) decS)] ∧
    runE_leaves[2].obligs = [] ∧ runE_leaves[2].exit = .call sparseEntry pc70 ∧
    runE_leaves[2].S.steps = 24 ∧ runE_leaves[2].S.reg 1 = .lit pc70 ∧
    runE_leaves[2].S.reg 10 = .ptr 0 40 ∧ runE_leaves[2].S.reg 11 = .ptr 1 0 ∧
    runE_leaves[2].S.reg 12 = .var 12 ∧ runE_leaves[2].S.reg 13 = decS ∧
    runE_leaves[2].S.reg 18 = .ptr 1 0 ∧ runE_leaves[2].S.reg 20 = decS ∧
    runE_leaves[2].S.reg 21 = .bin .sll (.lit 1) decS := by decide

theorem fE3 : runE_leaves[3].conds = [.ne (.bin .and (.var 13) (.lit 255)) (.lit 0),
      .geu (.var 12) (.bin .sll (.lit 1) decS)] ∧
    runE_leaves[3].obligs = [] ∧ runE_leaves[3].exit = .call sparseEntry pc70 ∧
    runE_leaves[3].S.steps = 25 ∧ runE_leaves[3].S.reg 1 = .lit pc70 ∧
    runE_leaves[3].S.reg 10 = .ptr 0 40 ∧ runE_leaves[3].S.reg 11 = .ptr 1 0 ∧
    runE_leaves[3].S.reg 12 = .bin .sll (.lit 1) decS ∧ runE_leaves[3].S.reg 13 = decS ∧
    runE_leaves[3].S.reg 18 = .ptr 1 0 ∧ runE_leaves[3].S.reg 20 = decS ∧
    runE_leaves[3].S.reg 21 = .bin .sll (.lit 1) decS := by decide

end ZesuExec.Fn.SszRoot.Sparse

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

theorem sll_eval (env : Env) (h : decS.eval env = x) :
    (Sym.bin .sll (.lit 1) decS).eval env = (1 : Word) <<< (x.toNat % 64) := by
  rw [Sym.eval_bin, h]; rfl

theorem reg_eq_of {env : Env} {S : SState} {m : Machine} (hm : Match env S m) (i : Fin 32)
    {s : Sym} (h : S.reg i.val = s) : m.reg i = s.eval env := by rw [← hm.regs i, h]

theorem leaf_E : ∀ l ∈ runE_leaves, LeafGoalR (plan hsha) cE l := by
  intro l hl
  have hsh := shE l hl
  rw [lE] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rintro g m ⟨rfl, hpc, hpre⟩ hc
  have hcut := cut_E hsha m m ⟨rfl, hpc, hpre⟩
  have F := PreFacts.of hpre.2
  have hd26 := hpre.1
  have hb0 : (entryEnv m (regsE m)).base 0 = fb m := by simp [Env.base, entryEnv, regsE, fb]
  have hb1 : (entryEnv m (regsE m)).base 1 = chunkPtr m := by simp [Env.base, entryEnv, regsE]
  have rdec : decS.eval (entryEnv m (regsE m)) = m.reg 13 - 1 := by
    simp only [decS, Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval, entryEnv_vars]
    exact dec_eq _
  have hc' : ∀ b ∈ l.conds, b.eval (entryEnv m (regsE m)) = true := hc
  rcases hl with rfl | rfl | rfl | rfl
  · -- depth 0, no chunks: the zero chunk
    obtain ⟨hcs, hob, hex, hst, s18⟩ := fE0
    rw [hcs] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc'
    obtain ⟨c1, c2⟩ := hc'
    simp only [SBool.eval, Sym.eval_bin, Sym.eval_var, Sym.eval_lit, entryEnv_vars, BinOp.eval] at c1 c2
    have hd0 : depthOf m = 0 := (depth_zero_iff hd26).mp (by simpa using c1)
    have hn0 : lenOf m = 0 := by
      have := beq_iff_eq.mp c2; simp only [lenOf]; rw [show m.reg (Fin.ofNat 32 12) = m.reg 12 from rfl] at this
      rw [this]; rfl
    refine ⟨by rw [hob]; simp, by simp [cE, SE, entryState, hst, hd0, sparseCost], fun m' hm' he hso => ?_⟩
    rw [hex] at he ⊢
    left
    refine ExitGoal.at_cut rfl ⟨c54, by show c54 ∈ cuts; simp [cuts], he, ⟨(entry_keep hpre hcut.1 hm' hso hsh).1, he, ?_, ?_⟩,
      by simp [cE, SE, entryState, hst, hd0, sparseCost, c54]⟩
    · have r18 : m'.reg 18 = BitVec.ofNat 64 0x801154c0 := by rw [reg_eq_of hm' 18 s18]; rfl
      have hro := ro_of F (entry_keep hpre hcut.1 hm' hso hsh).1.2.2.1
      rw [r18, show ch m = [] by simp [ch, hn0, chunksOf], hd0]
      intro i hi
      simp only [sparseRoot, List.headD, zeroChunk, List.length_replicate] at hi ⊢
      have ha : (BitVec.ofNat 64 0x801154c0 : Word) + BitVec.ofNat 64 i =
          BitVec.ofNat 64 (0x801154c0 + i) := by
        apply BitVec.eq_of_toNat_eq; simp
      rw [ha, hro _ _ (zeroChunk_ro i hi), List.getElem_replicate]; rfl
    · right; right; rw [reg_eq_of hm' 18 s18]; rfl
  · -- depth 0, the first chunk
    obtain ⟨hcs, hob, hex, hst, s18, hsrc⟩ := fE1
    rw [hcs] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc'
    obtain ⟨c1, c2⟩ := hc'
    simp only [SBool.eval, Sym.eval_bin, Sym.eval_var, Sym.eval_lit, entryEnv_vars, BinOp.eval] at c1 c2
    have hd0 : depthOf m = 0 := (depth_zero_iff hd26).mp (by simpa using c1)
    have hn0 : lenOf m ≠ 0 := by
      intro h0
      have : m.reg 12 = 0 := by apply BitVec.eq_of_toNat_eq; simpa [lenOf] using h0
      simp [show m.reg (Fin.ofNat 32 12) = m.reg 12 from rfl, this] at c2
    refine ⟨?_, by simp [cE, SE, entryState, hst, hd0, sparseCost], fun m' hm' he hso => ?_⟩
    · rw [hob]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro o (rfl | rfl | rfl | rfl) <;>
        simp [Oblig.holds, Sym.eval, Env.size, entryEnv, regsE, cE] <;> omega
    rw [hex] at he ⊢
    left
    have hk := (entry_keep hpre hcut.1 hm' hso hsh).1
    have r18 : m'.reg 18 = fb m + BitVec.ofNat 64 8 := by
      rw [reg_eq_of hm' 18 s18, Sym.eval_ptr]
      show (entryEnv m (regsE m)).base 0 + _ = _
      rw [hb0]; exact fb_ofInt m 8 (by omega)
    refine ExitGoal.at_cut rfl ⟨c54, by show c54 ∈ cuts; simp [cuts], he, ⟨hk, he, ?_, .inl r18⟩,
      by simp [cE, SE, entryState, hst, hd0, sparseCost, c54]⟩
    rw [r18, hd0]
    obtain ⟨k, hk'⟩ : ∃ k, lenOf m = k + 1 := ⟨lenOf m - 1, by omega⟩
    have hhead : sparseRoot (ch m) 0 =
        (List.range 32).map fun j => (m.mem (chunkPtr m + BitVec.ofNat 64 j)).getD 0 := by
      simp only [sparseRoot, ch, chunksOf, hk', List.range_succ_eq_map, List.map_cons,
        List.headD_cons, Nat.mul_zero, Nat.zero_add]
    rw [hhead]
    intro i hi
    simp only [List.length_map, List.length_range] at hi
    have := mem_of_src hm' (r := 0) (by simp [hsh.2.2.2.2.2.1]) (by simp [Env.size, entryEnv, regsE]; omega)
      (hsrc i hi)
    simp only [regsE, List.getD_cons_zero, List.getD_cons_succ] at this
    rw [ofNat_add_ofNat]
    rw [show fb m = m.reg 2 - BitVec.ofNat 64 0x120 from rfl, this]
    simp
  · obtain ⟨hcs, hob, hex, hst, s1, s10, s11, s12, s13, s18, s20, s21⟩ := fE2
    rw [hcs] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc'
    obtain ⟨c1, c2⟩ := hc'
    have hd : 1 ≤ depthOf m := by
      rcases Nat.eq_zero_or_pos (depthOf m) with h0 | h0
      · exfalso
        have h0' : m.reg 13 = 0 := BitVec.eq_of_toNat_eq (by simp only [depthOf] at h0; simp; omega)
        simp [SBool.eval, Sym.eval, BinOp.eval, entryEnv_vars,
          show m.reg (Fin.ofNat 32 13) = m.reg 13 from rfl, h0'] at c1
      · exact h0
    have hsl : (Sym.bin .sll (.lit 1) decS).eval (entryEnv m (regsE m)) =
        (1 : Word) <<< ((m.reg 13 - 1).toNat % 64) := sll_eval _ rdec
    have hhalf := half_toNat hpre hd
    have hcost := cost_split (g := m) hd
    have hlt : lenOf m < half m := by
      simp only [SBool.eval, hsl, Sym.eval_var, entryEnv_vars] at c2
      rw [show m.reg (Fin.ofNat 32 12) = m.reg 12 from rfl] at c2
      simp only [BitVec.ult, hhalf, decide_eq_true_eq] at c2
      exact c2
    refine ⟨by rw [hob]; simp, by simp only [cE, SE, entryState, hst]; omega,
      fun m' hm' he hso => ?_⟩
    rw [hex] at he ⊢
    refine ExitGoalR.self (entry_call (hsha := hsha) hpre hd (n' := min (lenOf m) (half m)) rfl
      hcut.1 hm' hso hsh s1 s10 s11 ?_ s13 s18 s20 s21 he ?_)
    · simp only [lenOf]
      rw [reg_eq_of hm' 12 s12]
      show (m.reg 12).toNat = _
      simp only [lenOf] at hlt; omega
    · show _ ≤ sparseCost (depthOf m) (lenOf m) - (_ - 0)
      simp only [hst]; omega
  · obtain ⟨hcs, hob, hex, hst, s1, s10, s11, s12, s13, s18, s20, s21⟩ := fE3
    rw [hcs] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc'
    obtain ⟨c1, c2⟩ := hc'
    have hd : 1 ≤ depthOf m := by
      rcases Nat.eq_zero_or_pos (depthOf m) with h0 | h0
      · exfalso
        have h0' : m.reg 13 = 0 := BitVec.eq_of_toNat_eq (by simp only [depthOf] at h0; simp; omega)
        simp [SBool.eval, Sym.eval, BinOp.eval, entryEnv_vars,
          show m.reg (Fin.ofNat 32 13) = m.reg 13 from rfl, h0'] at c1
      · exact h0
    have hsl : (Sym.bin .sll (.lit 1) decS).eval (entryEnv m (regsE m)) =
        (1 : Word) <<< ((m.reg 13 - 1).toNat % 64) := sll_eval _ rdec
    have hhalf := half_toNat hpre hd
    have hcost := cost_split (g := m) hd
    have hge : half m ≤ lenOf m := by
      simp only [SBool.eval, hsl, Sym.eval_var, entryEnv_vars] at c2
      rw [show m.reg (Fin.ofNat 32 12) = m.reg 12 from rfl] at c2
      simp only [BitVec.ult, hhalf, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at c2
      exact c2
    refine ⟨by rw [hob]; simp, by simp only [cE, SE, entryState, hst]; omega,
      fun m' hm' he hso => ?_⟩
    rw [hex] at he ⊢
    refine ExitGoalR.self (entry_call (hsha := hsha) hpre hd (n' := min (lenOf m) (half m)) rfl
      hcut.1 hm' hso hsh s1 s10 s11 ?_ s13 s18 s20 s21 he ?_)
    · simp only [lenOf]
      rw [reg_eq_of hm' 12 s12]
      show ((Sym.bin .sll (.lit 1) decS).eval (entryEnv m (regsE m))).toNat = _
      rw [hsl, hhalf]; simp only [lenOf] at hge; omega
    · show _ ≤ sparseCost (depthOf m) (lenOf m) - (_ - 0)
      simp only [hst]; omega

end ZesuExec.Fn.SszRoot.Sparse
