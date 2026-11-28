import ZesuExec.Fn.SszRoot.SparseRec
import ZesuExec.Fn.Sha256.Proof

/-!
# `sparseRoot` (`0x80042c0c`): the leaves after the left call, assembly, `sparseRoot_spec`

The leaves of `c70` (after the left recursive call): `ccK (depth - 1)` when no chunk reaches the
right half (the right root is `ZERO_HASHES[depth - 1]`), else the right recursive call (a
`SelfGoal` on the chunks from `half`, its root at `fb + 0x68`, then `c94`). `vc_sound_rec`
assembles the plan into `sparse_spec_of`, with `zkvm_sha256`'s contract as the hypothesis
`ShaSpec`; `sparseRoot_spec` discharges it with `Sha256.sha256_spec 64` (`shaSpec`).
-/

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

variable (hsha : ShaSpec)

/-! ## Leaves of `c70` -/

/-- The registers both leaves of `c70` keep. -/
def keep70 : List Nat := [2, 8, 9, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem l70 : run70_leaves = [run70_leaves[0], run70_leaves[1]] := rfl

theorem f70a : run70_leaves[0].conds = [.geu (.var 21) (.var 19)] ∧ run70_leaves[0].obligs = [] ∧
    run70_leaves[0].exit = .at pcC4 ∧ run70_leaves[0].S.steps = 1 ∧
    ∀ i ∈ keep70, run70_leaves[0].S.reg i = .var i := by decide

theorem f70b : run70_leaves[1].conds = [.ltu (.var 21) (.var 19)] ∧ run70_leaves[1].obligs = [] ∧
    run70_leaves[1].exit = .call sparseEntry pc94 ∧ run70_leaves[1].S.steps = 9 ∧
    run70_leaves[1].S.reg 1 = .lit pc94 ∧
    run70_leaves[1].S.reg 10 = .bin .add (.var 8) (.lit 18446744073709551432) ∧
    run70_leaves[1].S.reg 11 = .bin .add (.var 18) (.bin .sll (.var 21) (.lit 5)) ∧
    run70_leaves[1].S.reg 12 = .bin .sub (.var 19) (.var 21) ∧ run70_leaves[1].S.reg 13 = .var 20 ∧
    run70_leaves[1].S.reg 18 = .bin .add (.var 8) (.lit 18446744073709551432) ∧
    ∀ i ∈ keep70, run70_leaves[1].S.reg i = .var i := by decide

/-- `c70` has no regions: a leaf from it writes no memory. -/
theorem mem70 {m m' : Machine} (hso : SameOutside (InWritable (entryEnv m []) S70) m m') :
    m'.mem = m.mem :=
  funext fun a => hso a (by rintro ⟨r, R, j, hR, -⟩; simp [S70, entryState] at hR)

theorem reg70 {m m' : Machine} {S : SState} (hm : Match (entryEnv m []) S m') (i : Fin 32)
    (h : S.reg i.val = .var i.val) : m'.reg i = m.reg i := by
  rw [reg_eq_of hm i h, Sym.eval_var, entryEnv_var]

theorem fr_move {g m m' : Machine} (hk : Fr g m) (hmem : m'.mem = m.mem)
    (hr : ∀ i : Fin 32, i.val ∈ keep70 → m'.reg i = m.reg i) : Fr g m' := by
  obtain ⟨⟨hpre, hso, hp, hS, h2, h9, hkeep⟩, hd, h8, h19⟩ := hk
  refine ⟨⟨hpre, fun a ha => by rw [hmem]; exact hso a ha, hp.trans (Preserved.of_mem_eq hmem),
    fun q hq t ht => by rw [hmem]; exact hS q hq t ht, by rw [hr 2 (by decide), h2],
    by rw [hr 9 (by decide), h9], fun i hi => ?_⟩, hd, by rw [hr 8 (by decide), h8],
    by rw [hr 19 (by decide), h19]⟩
  rw [hr i ?_, hkeep i hi]
  simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem depth_dec {g : Machine} (hpre : SparsePre g) (hd : 1 ≤ depthOf g) :
    (g.reg 13 - 1).toNat = depthOf g - 1 := by
  have h26 := hpre.1
  simp only [depthOf] at hd ⊢; rw [BitVec.toNat_sub]; simp; omega

theorem sub_b8 (x : Word) :
    x + BitVec.ofNat 64 18446744073709551432 = x - BitVec.ofNat 64 0x120 + BitVec.ofNat 64 0x68 := by
  bv_omega

theorem leaf_70 : ∀ l ∈ run70_leaves, LeafGoalR (plan hsha) c70 l := by
  intro l hl
  rw [l70] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rintro g m ⟨hk, hpc, h18, h20, h21, hleft⟩ hc
  have hpre := hk.1.1
  have hd := hk.2.1
  have h26 := hpre.1
  have F := PreFacts.of hpre.2
  have hhalf := half_toNat hpre hd
  have h19 := hk.2.2.2
  have hc' : ∀ b ∈ l.conds, b.eval (entryEnv m []) = true := hc
  have v19 : (Sym.var 19).eval (entryEnv m []) = m.reg 19 := rfl
  have v21 : (Sym.var 21).eval (entryEnv m []) = m.reg 21 := rfl
  have hlo' : Layout.ramLo = 0xa0000000 := rfl
  have hsp : 0x120 ≤ (g.reg 2).toNat := by have := F.spLo; have := need_ge g; omega
  have hcost := cost_split (g := g) hd
  rcases hl with rfl | rfl
  · obtain ⟨hcs, hob, hex, hst, hregs⟩ := f70a
    rw [hcs] at hc'
    have c1 := hc' _ (List.mem_singleton_self _)
    have hle : lenOf g ≤ half g := by
      simp only [SBool.eval, v21, v19, h21, h19] at c1
      simp only [BitVec.ult, hhalf, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at c1
      exact c1
    refine ⟨by rw [hob]; simp, by simp [c70, S70, entryState, hst, rest70, hle], fun m' hm' he hso => ?_⟩
    rw [hex] at he ⊢
    left
    have hmem := mem70 hso
    have hr : ∀ i : Fin 32, i.val ∈ keep70 → m'.reg i = m.reg i := fun i hi => reg70 hm' i (hregs _ hi)
    refine ExitGoal.at_cut rfl ⟨ccK (depthOf g - 1),
      List.mem_append_right _ (List.mem_map.mpr ⟨_, List.mem_range.mpr (by omega), rfl⟩), he,
      ⟨fr_move hk hmem hr, he, ?_, by omega, hle, fun i hi => by rw [hmem]; exact hleft i hi⟩, ?_⟩
    · rw [hr 20 (by decide), h20]
      apply BitVec.eq_of_toNat_eq
      rw [depth_dec hpre hd, toNat_ofNat_lt (by omega)]
    · simp only [ccK, c70, S70, entryState, hst, rest70, if_pos hle]; omega
  · obtain ⟨hcs, hob, hex, hst, s1, s10, s11, s12, s13, s18, hregs⟩ := f70b
    rw [hcs] at hc'
    have c1 := hc' _ (List.mem_singleton_self _)
    have hlt : half g < lenOf g := by
      simp only [SBool.eval, v21, v19, h21, h19] at c1
      simp only [BitVec.ult, hhalf, decide_eq_true_eq] at c1
      exact c1
    have hrest : rest70 g = 9 + sparseCost (depthOf g - 1) (lenOf g - half g) + 23 + shaCost + 17 := by
      simp [rest70, Nat.not_le.mpr hlt]
    refine ⟨by rw [hob]; simp, by simp only [c70, S70, entryState, hst, hrest]; omega,
      fun m' hm' he hso => ?_⟩
    rw [hex] at he ⊢
    have hmem := mem70 hso
    have hr : ∀ i : Fin 32, i.val ∈ keep70 → m'.reg i = m.reg i := fun i hi => reg70 hm' i (hregs _ hi)
    have hfr : Fr g m' := fr_move hk hmem hr
    have hp : Preserved g m' := hk.1.2.2.1.trans (Preserved.of_mem_eq hmem)
    have hfb := fb_toNat F
    have hlo := F.spLo; have hhi := F.spHi
    have hh26 : half g ≤ 2 ^ 25 := Nat.pow_le_pow_right (by omega) (by omega)
    have r21 : m.reg 21 = BitVec.ofNat 64 (half g) := by
      apply BitVec.eq_of_toNat_eq; rw [h21, hhalf, toNat_ofNat_lt (by omega)]
    have r1 : m'.reg 1 = BitVec.ofNat 64 pc94 := by rw [reg_eq_of hm' 1 s1]; rfl
    have r2 : m'.reg 2 = fb g := by rw [hr 2 (by decide), hk.1.2.2.2.2.1]
    have r68 : m.reg 8 + BitVec.ofNat 64 18446744073709551432 = fb g + BitVec.ofNat 64 0x68 := by
      rw [hk.2.2.1]; exact sub_b8 _
    have r10 : m'.reg 10 = fb g + BitVec.ofNat 64 0x68 := by
      rw [reg_eq_of hm' 10 s10]; exact r68
    have r18 : m'.reg 18 = fb g + BitVec.ofNat 64 0x68 := by
      rw [reg_eq_of hm' 18 s18]; exact r68
    have r11 : m'.reg 11 = chunkPtr g + BitVec.ofNat 64 (32 * half g) := by
      have e : (BitVec.ofNat 64 (half g) : Word) <<< 5 = BitVec.ofNat 64 (32 * half g) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_shiftLeft, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega),
          Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
        omega
      rw [reg_eq_of hm' 11 s11]
      show m.reg 18 + m.reg 21 <<< ((BitVec.ofNat 64 5 : Word).toNat % 64) = _
      rw [h18, r21, show (BitVec.ofNat 64 5 : Word).toNat % 64 = 5 from rfl, e]
    have r12 : lenOf m' = lenOf g - half g := by
      simp only [lenOf]
      rw [reg_eq_of hm' 12 s12]
      show (m.reg 19 - m.reg 21).toNat = _
      rw [h19, r21, BitVec.toNat_sub, toNat_ofNat_lt (by omega)]
      simp only [lenOf] at hlt ⊢
      have := (g.reg 12).isLt
      omega
    have r13 : depthOf m' = depthOf g - 1 := by
      simp only [depthOf]; rw [reg_eq_of hm' 13 s13]
      show (m.reg 20).toNat = _
      rw [h20]; exact depth_dec hpre hd
    refine ExitGoalR.self ⟨cE, by show cE ∈ cuts; simp [cuts], m', ⟨rfl, he, ?_⟩, ?_,
      fun k m'' hrun hk' hpost => ?_⟩
    · exact callee_pre hpre hp hd r2 (by simp only [RetAligned, r1]; decide) r13 r10 (by omega) r11
        r12 (by omega)
    · show sparseCost (depthOf m') (lenOf m') ≤ _
      rw [r13, r12]; simp only [c70, S70, entryState, hrest]; omega
    obtain ⟨hfr'', hframe, hcs', hpc''⟩ := fr_after hfr (o := 0x68) (by omega) r10 r13 hpost
      hrun.preserved
    have hll : (leftRoot g).length = 32 := sparseRoot_length _ _ chunksOf_take_mem
    refine ⟨c94, by show c94 ∈ cuts; simp [cuts], by rw [hpc'', r1]; rfl,
      ⟨hfr'', by rw [hpc'', r1]; rfl, by rw [hcs' 18 (by decide), r18], hlt, ?_, ?_⟩, ?_⟩
    · intro i hi
      have hi' : i < 32 := hll ▸ hi
      rw [ofNat_add_ofNat, hframe _ ?_ ?_ ?_, ← ofNat_add_ofNat, hmem]
      · exact hleft i hi
      all_goals rw [fb_add_toNat F (by omega)]
      all_goals omega
    · have hb := hpost.2.1
      simp only [outOf, r10] at hb
      rw [show chunkPtr m' = chunkPtr g + BitVec.ofNat 64 (32 * half g) from r11, r12, r13,
        chunks_same hpre hfr.1.2.1 (by omega)] at hb
      rw [rightRoot, chunksOf_drop]; exact hb
    · show sparseCost (depthOf m') (lenOf m') + (23 + shaCost + 17) ≤ _
      rw [r13, r12]; simp only [c70, S70, entryState, hrest]; omega

/-! ## Assembly -/

theorem cuts_length : cuts.length = 30 := rfl

theorem cuts_C (k : Nat) (h : k + 4 < cuts.length) : cuts[k + 4] = ccK k := by
  simp [cuts]

theorem leaves_C (k : Nat) : leaves (k + 4) = lvC.getD k [] := by
  simp [leaves]

theorem steps_E : ∀ l ∈ runE_leaves, 0 < l.S.steps := by decide
theorem steps_70 : ∀ l ∈ run70_leaves, 0 < l.S.steps := by decide
theorem steps_54 : ∀ l ∈ run54_leaves, 0 < l.S.steps := by decide

include hsha in
theorem sparse_reaches : ∀ m, m.pc.toNat = sparseEntry → SparsePre m →
    Reaches zesuImage (sparseCost (depthOf m) (lenOf m)) (SparsePost m) m := by
  intro m hpc hpre
  refine vc_sound_rec (plan hsha) ?_ ?_ ?_ ?_ cE (by show cE ∈ cuts; simp [cuts]) m m ⟨rfl, hpc, hpre⟩
  · intro i hi
    show run zesuImage (cuts.map (·.pc)) fuel cuts[i].pc cuts[i].S = some (leaves i)
    rw [cuts_pcs]
    match i, hi with
    | 0, _ => exact runE
    | 1, _ => exact run70
    | 2, _ => exact run94
    | 3, _ => exact run54
    | k + 4, hi =>
      rw [cuts_C k hi, leaves_C]
      exact runC k (by have : k + 4 < 30 := hi; omega)
  · intro i hi l hl
    show cuts[i].S.steps < l.S.steps
    change l ∈ leaves i at hl
    match i, hi with
    | 0, _ => exact steps_E l hl
    | 1, _ => exact steps_70 l hl
    | 2, _ => have := (leaf94_facts l hl).2.1; show 0 < _; omega
    | 3, _ => exact steps_54 l hl
    | k + 4, hi =>
      rw [cuts_C k hi]
      rw [leaves_C] at hl
      have := (leafC_facts k (List.mem_range.mpr (by have : k + 4 < 30 := hi; omega)) l hl).2.1
      show 0 < _; omega
  · intro c hc
    change c ∈ cuts at hc
    simp only [cuts, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl) | ⟨k, -, rfl⟩
    · exact cut_E hsha
    · exact cut_70 hsha
    · exact cut_94 hsha
    · exact cut_54 hsha
    · exact cut_C hsha k
  · intro i hi l hl
    change l ∈ leaves i at hl
    match i, hi with
    | 0, _ => exact leaf_E l hl
    | 1, _ => exact leaf_70 hsha l hl
    | 2, _ => exact leaf_94 l hl
    | 3, _ => exact leaf_54 l hl
    | k + 4, hi =>
      rw [leaves_C] at hl
      show LeafGoalR (plan hsha) cuts[k + 4] l
      rw [cuts_C k hi]
      exact leaf_C k (by have : k + 4 < 30 := hi; omega) l hl

/-! ## `sparseRoot_spec` -/

/-- The `sparseRoot` contract at depth `d` on `n` chunks, budget `sparseCost d n`. -/
def SparseSpec : Prop :=
  ∀ d n, Spec zesuImage sparseEntry (sparseCost d n)
    (fun m => SparsePre m ∧ depthOf m = d ∧ lenOf m = n) SparsePost

include hsha in
theorem sparse_spec_of : SparseSpec := by
  rintro d n m hpc ⟨hpre, rfl, rfl⟩
  exact sparse_reaches hsha m hpc hpre

/-- `zkvm_sha256`'s contract on 64 bytes (`Fn/Sha256/Proof.lean`). -/
theorem shaSpec : ShaSpec := Sha256.sha256_spec 64

theorem sparseRoot_spec : SparseSpec := sparse_spec_of shaSpec

end ZesuExec.Fn.SszRoot.Sparse
