import ZesuExec.Fn.DTF.Leaves
import ZesuExec.Fn.DTF.Gen

/-!
# DTF: the entry leaf (programme plan S7 step 4)

The leaf from the entry to the jump-table load `0x80000574`: the prologue saves `ra`, `s0`–`s11`
in the save area, sets up the frame and the `rest` registers, and computes the table word's address
`0x80110050 + 8 · (tx_type & 0xff)`. `Common` at its end follows from `Pre` and the save-area
writes (`common_entry`), the target's shape from the leaf state (`shapeOk_of_holds`), `rest` is the
payload after no items, and the table address follows from `tx_type ≤ 4`.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- `Common` after the prologue: the entry's `Pre`, a step that writes only DTF's own memory and
keeps present bytes, and the save area holding the entry's `ra`, `s0`–`s11`. -/
theorem common_entry {σ : Sig} {m' : Machine} (hpc : σ.m.pc.toNat = entry)
    (hpre : Pre σ.A σ.g σ.m) (hp : Preserved σ.m m') (hso : SameOutside (Owned σ) σ.m m')
    (hsv : ∀ k < 13, m'.load (σ.S - w (8 * (k + 1))) 8 = some (σ.m.reg (savedReg k))) :
    Common σ m' := by
  have hheap : σ.A.Heap σ.g.L σ.m := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hscr : Present σ.m TX.scratch 8 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hpc, hpre, RodataLoaded.preserved hpre.1 hp fun _ _ hb => F1.zesu_rodata_low hb, hsv,
    Present.of_preserved hpre.2.1.2.2.2 hp, Present.of_preserved hpre.2.2.2.2.1 hp,
    Present.of_preserved hscr hp, fun a ha => hso a fun h => ha (.inl h),
    σ.g.L, [], σ.A.heap_frame' _ _ _ hheap
      (fun a hpv => hso a fun h => owned_not_priv hpre h hpv) hp, by simp, by simp⟩

/-- A register of the entry machine, as the entry environment's variable. -/
theorem entry_var {sh : Shape} {σ : Sig} {m : Machine} (i : Fin 32) :
    (Sym.var i.val).eval (envOf sh σ m) = m.reg i := by
  simp only [Sym.eval, envOf, i.isLt, if_true]
  congr 1
  exact Fin.ext (by simp)
set_option maxRecDepth 20000 in

/-- The entry leaf. -/
theorem DTF.leaf_8000050c_0 :
    LeafGoal DTF.plan DTF.plan.cuts[0]! ((DTF.plan.leaves 0x8000050c)[0]!) := by
  show LeafGoal vcPlan (mkCut (table[0]!)) ((leavesAt 0x8000050c)[0]!)
  have hcut : CutOK vcPlan (mkCut (table[0]!)) := DTF.cut_8000050c
  have hpc : (table[0]!).pc = entry := by decide
  have hx : (table[0]!).shape.extra = [] := by decide
  have hreg : ((leavesAt 0x8000050c)[0]!).S.regions = baseRegions := by decide
  have hob : ((leavesAt 0x8000050c)[0]!).obligs = [] := by decide
  have hexit : ((leavesAt 0x8000050c)[0]!).exit = .at 0x80000574 := by decide
  have hsave : ∀ k < 13, readConst ((leavesAt 0x8000050c)[0]!).S 0 (880 - 8 * (k + 1)) 8 =
      .var (savedReg k).val := by decide
  have hr10 : ((leavesAt 0x8000050c)[0]!).S.reg 10 =
      .bin .add (.bin .sll (.bin .and (.var 12) (.lit 255)) (.lit 3)) (.lit 2148597840) := by
    decide
  have hr13 : ((leavesAt 0x8000050c)[0]!).S.reg 13 = .bin .add (.ptr 3 0) (.var 45) := by decide
  have hr14 : ((leavesAt 0x8000050c)[0]!).S.reg 14 = .var 14 := by decide
  have hr21 : ((leavesAt 0x8000050c)[0]!).S.reg 21 = .var 14 := by decide
  have hr22 : ((leavesAt 0x8000050c)[0]!).S.reg 22 = .bin .add (.ptr 3 0) (.var 45) := by decide
  have hsteps : ((leavesAt 0x8000050c)[0]!).S.steps - (table[0]!).shape.S.steps = 26 := by decide
  have hpc1 : (table[1]!).pc = 0x80000574 := by decide
  have hne1 : (table[1]!).pc ≠ entry := by decide
  have hpl1 : (table[1]!).plain = true := by decide
  have harms1 : (table[1]!).arms = [] := by decide
  have hrest1 : (table[1]!).rest =
      [⟨.reg 13, false, 0⟩, ⟨.reg 14, true, 0⟩, ⟨.reg 21, true, 0⟩, ⟨.reg 22, false, 0⟩] := by
    decide
  have hrest0 : (table[0]!).rest = [⟨.reg 13, false, 0⟩, ⟨.reg 14, true, 0⟩] := by decide
  have hfine1 : (table[1]!).shape.Fine = true := by decide
  have hsh1 : shapeHolds ((leavesAt 0x8000050c)[0]!).S (table[1]!).shape = true := by decide
  have hb0 : (budgetAt 0x8000050c).1 = 34359750421 := by decide
  have hb1 : (budgetAt 0x80000574).1 = 34359750395 := by decide
  have hi0 : (budgetAt 0x8000050c).2 = .none := rfl
  have hi1 : (budgetAt 0x80000574).2 = .none := rfl
  have hmem1 : mkCut (table[1]!) ∈ vcPlan.cuts := List.mem_map_of_mem (by
    rw [getElem!_pos table 1 (by decide)]; exact List.getElem_mem _)
  intro σ m hA _
  obtain ⟨hwf, -, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf
  simp only [mkCut, if_pos hpc] at hA
  obtain ⟨rfl, hpcm, hpre⟩ := hA
  have hS : BaseRegs (table[0]!).shape.S := baseRegs_shape hx
  refine ⟨fun o ho => (by rw [hob] at ho; cases ho), ?_, fun m' hm' hexok hso => ?_⟩
  · show ((leavesAt 0x8000050c)[0]!).S.steps - (table[0]!).shape.S.steps ≤
      budgetOf (table[0]!) σ σ.m
    unfold budgetOf
    rw [hsteps, hpc, entry_eq, hb0]
    omega
  simp only [mkCut] at hm' hso
  rw [hexit] at hexok ⊢
  simp only [ExitOk] at hexok
  have hwf' : Env.WF (envOf (table[0]!).shape σ σ.m) ((leavesAt 0x8000050c)[0]!).S :=
    wf_of_regions hwf (hreg.trans hS.symm)
  have hR0 : ((leavesAt 0x8000050c)[0]!).S.regions[0]? = some frameR := by rw [hreg]; rfl
  have hp : Preserved σ.m m' :=
    F1.preserved_of_leaf hwf hm' (Nat.le_of_eq (by rw [hS, hreg])) hso
  have hso' : SameOutside (Owned σ) σ.m m' := fun a ha =>
    hso a fun h => ha (inWritable_owned hpre hS h).1
  have hreg' : ∀ i : Fin 32, m'.reg i = (((leavesAt 0x8000050c)[0]!).S.reg i.val).eval
      (envOf (table[0]!).shape σ σ.m) := fun i => (hm'.regs i).symm
  -- the save area
  have hsv : ∀ k < 13, m'.load (σ.S - w (8 * (k + 1))) 8 = some (σ.m.reg (savedReg k)) := by
    intro k hk
    have := load_cst hwf' hm' hR0 (off := 880 - 8 * (k + 1)) (n := 8)
      (by rw [envOf_size0]; unfold frameBytes; omega)
    rw [env_base0, hsave k hk, entry_var] at this
    rw [show σ.S - w (8 * (k + 1)) = σ.fr + BitVec.ofNat 64 (880 - 8 * (k + 1)) by
      simp only [Sig.fr, w, frameBytes]; bv_omega]
    exact this
  have hcm : Common σ m' := common_entry hpcm hpre hp hso' hsv
  -- registers at the end
  have e13 : m'.reg 13 = σ.inp := by
    rw [hreg' 13, show (13 : Fin 32).val = 13 from rfl, hr13]
    simp only [Sym.eval, BinOp.eval, env_base3]
    simp [envOf]
  have e22 : m'.reg 22 = σ.inp := by
    rw [hreg' 22, show (22 : Fin 32).val = 22 from rfl, hr22]
    simp only [Sym.eval, BinOp.eval, env_base3]
    simp [envOf]
  have e14 : m'.reg 14 = σ.m.reg 14 := by
    rw [hreg' 14, show (14 : Fin 32).val = 14 from rfl, hr14]
    exact entry_var 14
  have e21 : m'.reg 21 = σ.m.reg 14 := by
    rw [hreg' 21, show (21 : Fin 32).val = 21 from rfl, hr21]
    exact entry_var 14
  have ht : σ.t ≤ 4 := hpre.2.2.2.2.2.2.2.2.2.1
  have e10 : m'.reg 10 = w (0x80110050 + 8 * σ.t) := by
    rw [hreg' 10, show (10 : Fin 32).val = 10 from rfl, hr10]
    have e12 : (Sym.var 12).eval (envOf (table[0]!).shape σ σ.m) = σ.m.reg 12 := entry_var 12
    simp only [Sym.eval_bin, Sym.eval_lit, e12]
    simp only [Sig.t] at ht ⊢
    generalize σ.m.reg 12 = x at ht ⊢
    have hx5 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by bv_omega
    rcases hx5 with rfl | rfl | rfl | rfl | rfl <;> decide
  have hlen' : (m'.reg 14).toNat = σ.len := by rw [e14]
  refine ExitGoal.at_cut rfl ⟨mkCut (table[1]!), hmem1, hexok.trans hpc1.symm, ?_, ?_⟩
  · simp only [mkCut, if_neg hne1, ACut]
    refine .inl ⟨hpl1, by rw [hexok, hpc1], hcm,
      shapeOk_of_holds hwf' hm' hR0 hfine1 hsh1, .inl harms1, ?_, ?_, ?_⟩
    · intro r hr
      rw [hrest1] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> refine ⟨0, rfl, ?_⟩ <;>
        simp only [Loc.word, if_true, if_false, Bool.false_eq_true]
      · show m'.reg 13 = _; rw [e13]; simp [w]
      · show m'.reg 14 = _; rw [e14]; simp [w, Sig.len]
      · show m'.reg 21 = _; rw [e21]; simp [w, Sig.len]
      · show m'.reg 22 = _; rw [e22]; simp [w]
    · unfold Extra; rw [hpc1, if_pos rfl]; exact e10
    · rw [hpc1, hi1]; trivial
  · show budgetOf (table[1]!) σ m' ≤ budgetOf (table[0]!) σ σ.m -
      (((leavesAt 0x8000050c)[0]!).S.steps - (table[0]!).shape.S.steps)
    unfold budgetOf restLen
    rw [hrest1, hrest0, hpc1, hpc, entry_eq, hb0, hb1, hi0, hi1, hsteps]
    simp only [List.find?, Loc.word, innerOf]
    show 34359750395 + 256 * (m'.reg 14).toNat + 0 ≤
      34359750421 + 256 * (σ.m.reg 14).toNat + 0 - 26
    rw [e14]
    omega

end ZesuExec.Fn.DTF
