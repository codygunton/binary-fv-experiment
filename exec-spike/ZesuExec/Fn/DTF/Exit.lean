import ZesuExec.Fn.DTF.Leaves
import ZesuExec.Fn.DTF.Gen

/-!
# DTF: the return leaf (programme plan S7 step 4)

The leaf from the result-written cut `0x800011f8` reloads `ra`, `s0`–`s11` from the save area,
restores `sp` and returns, writing nothing. `Post` follows from `Common` at its end
(`common_leaf`), the saved words (`frame_init`) and `Done`, carried over the unchanged memory
(`mem_same`, `done_congr`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- A loaded frame word is what `init` reads there. -/
theorem frame_init {sh : Shape} {σ : Sig} {m : Machine} {o : Nat} {v : Word}
    (h : m.load (σ.fr + w o) 8 = some v) : (Sym.init 0 o 8).eval (envOf sh σ m) = v := by
  have hb : BytesAt m (σ.fr + w o) ((List.range 8).map (byteOf v)) := fun i hi => by
    simp only [List.length_map, List.length_range] at hi
    rw [load_bytes h (Nat.le_refl _) i hi]
    simp
  have := init_frame (sh := sh) (off := 0) (n := 8) hb (by simp)
  rw [Nat.add_zero] at this
  rw [this, List.drop_zero, List.take_of_length_le (by simp)]
  exact ofBytesLE_bytes8 v

/-- A leaf without writes leaves the memory as it was. -/
theorem mem_same {sh : Shape} {σ : Sig} {m m' : Machine} {S S' : SState} (hc : Common σ m)
    (hS : BaseRegs S) (hS' : BaseRegs S') (hnw : S'.mem = []) (hm' : Match (envOf sh σ m) S' m')
    (hso : SameOutside (InWritable (envOf sh σ m) S) m m') : m'.mem = m.mem := by
  funext a
  by_cases hw : InWritable (envOf sh σ m) S a
  · obtain ⟨-, r, j, hr, hj, rfl⟩ := inWritable_owned hc.2.1 hS hw
    obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
    · rw [envOf_size0] at hj
      rw [env_base0]
      exact frame_byte_keep hc.avail hm' hS' hj (by rw [hnw]; rfl)
    · have hsz : (envOf sh σ m).size 1 = resultBytes := by
        simp [envOf, entryEnv, Env.size, regionsOf]
      have h := hm'.mem 1 j (by rw [hS']; decide) hj
      rw [hsz] at hj
      rw [env_base1] at h ⊢
      rw [h]
      simp only [memByte, hnw, List.find?_nil, Env.byte0, envOf, entryEnv, regionsOf]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hc.avail.res j hj)
      simp [hb]
  · exact hso a hw

theorem txAt_congr {m m' : Machine} (h : m'.mem = m.mem) {res : Word} {tx : Tx}
    (ht : TxAt m res tx) : TxAt m' res tx := by
  unfold TxAt SliceAt AuthAt BytesAt Machine.load at *
  rw [h]
  exact ht

theorem done_congr {σ : Sig} {m m' : Machine} (h : m'.mem = m.mem) (hd : Done σ m) :
    Done σ m' := by
  have hl : ∀ a n, m'.load a n = m.load a n := fun a n => by unfold Machine.load; rw [h]
  rcases hd with h3 | ⟨tx, hdec, h0, ht⟩
  · exact .inl (by rw [hl]; exact h3)
  · exact .inr ⟨tx, hdec, by rw [hl]; exact h0, txAt_congr h ht⟩

/-- The return target `ra & ~1` (the immediate is `~1`). -/
abbrev retT : Sym := .bin .and (.init 0 872 8) (.lit 18446744073709551614)

/-- The return leaf of `0x800011f8`. -/
theorem DTF.leaf_800011f8_0 :
    LeafGoal DTF.plan DTF.plan.cuts[58]! ((DTF.plan.leaves 0x800011f8)[0]!) := by
  show LeafGoal vcPlan (mkCut (table[58]!)) ((leavesAt 0x800011f8)[0]!)
  have hcut : CutOK vcPlan (mkCut (table[58]!)) := DTF.cut_800011f8
  have hpc : (table[58]!).pc = 0x800011f8 := by decide
  have hne : (table[58]!).pc ≠ entry := by decide
  have hsite : (table[58]!).site = none := by decide
  have hsrc : SrcOk (table[58]!) = true := by decide
  have hx : (table[58]!).shape.extra = [] := by decide
  have hreg : ((leavesAt 0x800011f8)[0]!).S.regions = baseRegions := by decide
  have hnw : ((leavesAt 0x800011f8)[0]!).S.mem = [] := by decide
  have hob : ((leavesAt 0x800011f8)[0]!).obligs = [.aligned retT 4] := by decide
  have hexit : ((leavesAt 0x800011f8)[0]!).exit = .ret retT := by decide
  have hsave : ∀ k < 13, ((leavesAt 0x800011f8)[0]!).S.reg (savedReg k).val =
      .init 0 (880 - 8 * (k + 1)) 8 := by decide
  have hsp : ((leavesAt 0x800011f8)[0]!).S.reg 2 = .ptr 0 880 := by decide
  have hsteps : ((leavesAt 0x800011f8)[0]!).S.steps - (table[58]!).shape.S.steps ≤
      (budgetAt (table[58]!).pc).1 := by decide
  have hlow : writesLow ((leavesAt 0x800011f8)[0]!).S = true := by decide
  have hnot : (BitVec.ofNat 64 18446744073709551614 : Word) = ~~~1 := by decide
  intro σ m hA hc
  have F := facts_of_A hne hsrc hA
  obtain ⟨hwf, hm, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf hm hc
  have hS : BaseRegs (table[58]!).shape.S := baseRegs_shape hx
  have hS' : BaseRegs ((leavesAt 0x800011f8)[0]!).S := hreg
  have hc0 := F.common
  have hpre := hc0.2.1
  -- `Done` at the source
  have hdone : Done σ m := by
    simp only [mkCut, if_neg hne, ACut, hsite, reduceCtorEq, false_and, exists_false,
      or_false] at hA
    have hex := hA.2.2.2.2.2.2.1
    unfold Extra at hex
    rw [hpc, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl] at hex
    exact hex
  -- the saved words
  have hsv : ∀ k < 13, (Sym.init 0 (880 - 8 * (k + 1)) 8).eval (envOf (table[58]!).shape σ m) =
      σ.m.reg (savedReg k) := fun k hk => frame_init (by
    rw [show σ.fr + w (880 - 8 * (k + 1)) = σ.S - w (8 * (k + 1)) by
      simp only [Sig.fr, w, frameBytes]; bv_omega]
    exact hc0.2.2.2.1 k hk)
  have hra : retT.eval (envOf (table[58]!).shape σ m) = σ.m.reg 1 &&& ~~~1 := by
    simp only [retT, Sym.eval_bin, Sym.eval_lit, BinOp.eval]
    rw [show (872 : Nat) = 880 - 8 * (0 + 1) from rfl, hsv 0 (by decide), hnot]
    rfl
  refine ⟨?_, ?_, fun m' hm' hexok hso => ?_⟩
  · rw [hob]
    intro o ho
    simp only [List.mem_singleton] at ho
    subst ho
    show (retT.eval (envOf (table[58]!).shape σ m)).toNat % 4 = 0
    rw [hra]
    exact hpre.2.2.1
  · show ((leavesAt 0x800011f8)[0]!).S.steps - (table[58]!).shape.S.steps ≤
      budgetOf (table[58]!) σ m
    unfold budgetOf
    omega
  simp only [mkCut] at hm' hso
  rw [hexit] at hexok ⊢
  simp only [ExitOk, mkCut] at hexok
  show Post σ.A σ.g σ.m m'
  have hcm := common_leaf hc0 hwf hS hS' hm' hso hlow
  have hmem := mem_same hc0 hS hS' hnw hm' hso
  have key : ∀ k < 13, ∀ i, savedReg k = i → m'.reg i = σ.m.reg i := fun k hk i he => by
    subst he
    rw [← hm'.regs, hsave k hk, hsv k hk]
  obtain ⟨L, X, hH, hperm, hX⟩ := hcm.2.2.2.2.2.2.2.2
  refine ⟨⟨by rw [hexok, hra], fun i hi => ?_⟩, fun a ha => hcm.2.2.2.2.2.2.2.1 a fun h => ha ?_,
    hcm.2.2.2.2.2.2.1, ⟨X, fun b hb => ⟨(hX b hb).1, (hX b hb).2.1⟩, L, hperm, hH⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← hm'.regs]
      change Sym.eval _ (((leavesAt 0x800011f8)[0]!).S.reg 2) = _
      rw [hsp]
      simp only [Sym.eval, env_base0, Sig.fr, Sig.S, w, frameBytes]
      rw [show (BitVec.ofInt 64 880 : Word) = BitVec.ofNat 64 880 from rfl]
      bv_omega
    all_goals first
      | exact key 1 (by decide) _ (by decide) | exact key 2 (by decide) _ (by decide)
      | exact key 3 (by decide) _ (by decide) | exact key 4 (by decide) _ (by decide)
      | exact key 5 (by decide) _ (by decide) | exact key 6 (by decide) _ (by decide)
      | exact key 7 (by decide) _ (by decide) | exact key 8 (by decide) _ (by decide)
      | exact key 9 (by decide) _ (by decide) | exact key 10 (by decide) _ (by decide)
      | exact key 11 (by decide) _ (by decide) | exact key 12 (by decide) _ (by decide)
  · rcases h with (h | h | h) | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  · rcases done_congr hmem hdone with h3 | ⟨tx, h1, h2, h3⟩
    · exact .inr h3
    · exact .inl ⟨tx, h1, h2, h3⟩

end ZesuExec.Fn.DTF
