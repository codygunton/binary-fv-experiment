import ZesuExec.Fn.DTF.Leaves
import ZesuExec.Fn.DTF.Gen

/-!
# DTF: the jump-table dispatch leaf (programme plan S7 step 4)

The leaf from the jump-table load `0x80000574` (region 4 = the table word `0x80110050 + 8·t`)
loads the word, zeroes three frame words and jumps to it. For `t ≤ 4` the word is the arm's
entry (`tgtPc t`, checked against the image's rodata by `decide`); the arm's cut gets `Common` (the
leaf writes frame words below the save area only; region 4 is read-only, `inWritable_owned_ro`),
its shape from the leaf state, `rest` unchanged and the arm `t`.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- The arm entries of the jump table, by `tx_type`. -/
def tgtPc (t : Nat) : Nat := [0x80000588, 0x8000081c, 0x8000069c, 0x8000075c, 0x800005dc][t]!

/-- The arm entries' indices in `table`. -/
def tgtIdx (t : Nat) : Nat := [2, 16, 8, 12, 4][t]!

def Inner.isNone : Inner → Bool
  | .none => true
  | _ => false

theorem byteList_congr {f g : Nat → Byte} : ∀ {k n : Nat},
    (∀ j, k ≤ j → j < k + n → f j = g j) → byteList f k n = byteList g k n
  | _, 0, _ => rfl
  | k, n + 1, h => by
    simp only [byteList]
    rw [h k (Nat.le_refl _) (by omega), byteList_congr fun j h1 h2 => h j (by omega) (by omega)]

/-- The table word region 4 holds: the image's rodata. -/
theorem table_word {sh : Shape} {R : Region} (hx : sh.extra = [R]) {σ : Sig} {m : Machine}
    (hro : RodataLoaded zesuImage m) {t : Nat} (ht : t < 5)
    (h10 : m.reg 10 = w (0x80110050 + 8 * t)) :
    (Sym.init 4 0 8).eval (envOf sh σ m) = ofBytesLE (byteList
      (fun j => BitVec.ofNat 8 ((zesuImage.rodataByte? (0x80110050 + 8 * t + j)).getD 0)) 0 8) := by
  simp only [Sym.eval]
  congr 1
  refine byteList_congr fun j _ hj => ?_
  show (m.mem ((envOf sh σ m).base 4 + BitVec.ofNat 64 j)).getD 0 = _
  rw [env_base4 sh hx, h10, show w (0x80110050 + 8 * t) + BitVec.ofNat 64 j =
    BitVec.ofNat 64 (0x80110050 + 8 * t + j) by
      simp only [w]; rw [BitVec.ofNat_add (0x80110050 + 8 * t) j]]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (table_rodata t ht j (by omega))
  rw [hro _ _ hb, hb]
  rfl

/-- What `decide` checks of the five arms. -/
def ArmCheck (t : Nat) : Bool :=
  let d' := table[tgtIdx t]!
  let l := (leavesAt 0x80000574)[0]!
  d'.pc == tgtPc t && d'.plain && d'.arms == [t] && d'.shape.extra.isEmpty &&
    d'.rest == [⟨.reg 13, false, 0⟩, ⟨.reg 14, true, 0⟩, ⟨.reg 21, true, 0⟩, ⟨.reg 22, false, 0⟩] &&
    d'.shape.Fine && shapeHolds l.S d'.shape && noExtra d'.pc && (budgetAt d'.pc).2.isNone &&
    decide ((budgetAt d'.pc).1 + 5 ≤ 34359750395) && decide (tgtPc t % 4 = 0) &&
    ofBytesLE (byteList
      (fun j => BitVec.ofNat 8 ((zesuImage.rodataByte? (0x80110050 + 8 * t + j)).getD 0)) 0 8) ==
      w (tgtPc t) &&
    decide (tgtIdx t < table.length) && decide (tgtPc t ≠ entry) &&
    (w (tgtPc t) &&& ~~~1) == w (tgtPc t) && decide ((w (tgtPc t)).toNat % 4 = 0) &&
    decide (tgtPc t < 2 ^ 64)

set_option maxRecDepth 20000 in
theorem armCheck_all : ∀ t < 5, ArmCheck t = true := by decide

set_option maxRecDepth 20000 in
/-- The jump-table dispatch leaf. -/
theorem DTF.leaf_80000574_0 :
    LeafGoal DTF.plan DTF.plan.cuts[1]! ((DTF.plan.leaves 0x80000574)[0]!) := by
  show LeafGoal vcPlan (mkCut (table[1]!)) ((leavesAt 0x80000574)[0]!)
  have hcut : CutOK vcPlan (mkCut (table[1]!)) := DTF.cut_80000574
  have hne : (table[1]!).pc ≠ entry := by decide
  have hpc : (table[1]!).pc = 0x80000574 := by decide
  have hsite : (table[1]!).site = none := by decide
  have hx : (table[1]!).shape.extra = [⟨some 8, 1, false⟩] := by decide
  have hrest0 : (table[1]!).rest =
      [⟨.reg 13, false, 0⟩, ⟨.reg 14, true, 0⟩, ⟨.reg 21, true, 0⟩, ⟨.reg 22, false, 0⟩] := by
    decide
  have hreg : ((leavesAt 0x80000574)[0]!).S.regions = baseRegions ++ [⟨some 8, 1, false⟩] := by
    decide
  have hS : (table[1]!).shape.S.regions = baseRegions ++ [⟨some 8, 1, false⟩] := by decide
  have hob : ((leavesAt 0x80000574)[0]!).obligs =
      [.aligned (.bin .and (.init 4 0 8) (.lit 18446744073709551614)) 4] := by decide
  have hexit : ((leavesAt 0x80000574)[0]!).exit =
      .jumpInd (.bin .and (.init 4 0 8) (.lit 18446744073709551614)) := by decide
  have hr13 : ((leavesAt 0x80000574)[0]!).S.reg 13 = .bin .add (.ptr 3 0) (.var 45) := by decide
  have hr14 : ((leavesAt 0x80000574)[0]!).S.reg 14 = .var 14 := by decide
  have hr21 : ((leavesAt 0x80000574)[0]!).S.reg 21 = .var 21 := by decide
  have hr22 : ((leavesAt 0x80000574)[0]!).S.reg 22 = .bin .add (.ptr 3 0) (.var 54) := by decide
  have hsteps : ((leavesAt 0x80000574)[0]!).S.steps - (table[1]!).shape.S.steps = 5 := by decide
  have hlow : writesLow ((leavesAt 0x80000574)[0]!).S = true := by decide
  have hb1 : (budgetAt 0x80000574).1 = 34359750395 := by decide
  have hi1 : (budgetAt 0x80000574).2 = .none := rfl
  have hnot : (BitVec.ofNat 64 18446744073709551614 : Word) = ~~~1 := by decide
  intro σ m hA hc
  obtain ⟨hwf, hm, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf hm hc
  simp only [mkCut, if_neg hne, ACut, hsite, reduceCtorEq, false_and, exists_false,
    or_false] at hA
  obtain ⟨-, hpcm, hcm, -, -, hrst, hex, -⟩ := hA
  have hpre := hcm.2.1
  have h10 : m.reg 10 = w (0x80110050 + 8 * σ.t) := by
    unfold Extra at hex; rw [hpc, if_pos rfl] at hex; exact hex
  have ht5 : σ.t < 5 := by
    have : σ.t ≤ 4 := hpre.2.2.2.2.2.2.2.2.2.1
    omega
  have hck := armCheck_all σ.t ht5
  simp only [ArmCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.isEmpty_iff] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpc', hpl'⟩, harms'⟩, hx'⟩, hrest'⟩, hfine'⟩, hsh'⟩, hnx⟩, hin'⟩, hbud'⟩,
    hal⟩, hword⟩, hidx⟩, hne'⟩, hand⟩, hal4⟩, h64⟩ := hck
  have htw : (Sym.init 4 0 8).eval (envOf (table[1]!).shape σ m) = w (tgtPc σ.t) := by
    rw [table_word hx hcm.2.2.1 ht5 h10, hword]
  have htgt : (Sym.bin .and (.init 4 0 8) (.lit 18446744073709551614)).eval
      (envOf (table[1]!).shape σ m) = w (tgtPc σ.t) := by
    rw [Sym.eval_bin, htw, Sym.eval_lit, hnot]
    exact hand
  refine ⟨fun o ho => ?_, ?_, fun m' hm' hexok hso => ?_⟩
  · rw [hob, List.mem_singleton] at ho
    subst ho
    show ((Sym.bin .and (.init 4 0 8) (.lit 18446744073709551614)).eval
      (envOf (table[1]!).shape σ m)).toNat % 4 = 0
    rw [htgt]; exact hal4
  · show ((leavesAt 0x80000574)[0]!).S.steps - (table[1]!).shape.S.steps ≤
      budgetOf (table[1]!) σ m
    unfold budgetOf; rw [hsteps, hpc, hb1]; omega
  simp only [mkCut] at hm' hso
  rw [hexit] at hexok ⊢
  simp only [ExitOk, mkCut] at hexok
  have hwf' : Env.WF (envOf (table[1]!).shape σ m) ((leavesAt 0x80000574)[0]!).S :=
    wf_of_regions hwf (hreg.trans hS.symm)
  have hR0 : ((leavesAt 0x80000574)[0]!).S.regions[0]? = some frameR := by rw [hreg]; rfl
  have hp : Preserved m m' :=
    F1.preserved_of_leaf hwf hm' (Nat.le_of_eq (by rw [hS, hreg])) hso
  have hcm' : Common σ m' := common_leaf_of hcm hp
    (fun a h => inWritable_owned_ro hpre hS (by simp) h) hm' (by rw [hreg]; decide) hso hlow
  have hreg' : ∀ i : Fin 32, m'.reg i = (((leavesAt 0x80000574)[0]!).S.reg i.val).eval
      (envOf (table[1]!).shape σ m) := fun i => (hm'.regs i).symm
  have e13 : m'.reg 13 = m.reg 13 := by
    rw [hreg' 13, show (13 : Fin 32).val = 13 from rfl, hr13]
    simp only [Sym.eval, BinOp.eval, env_base3]
    simp [envOf]; bv_omega
  have e22 : m'.reg 22 = m.reg 22 := by
    rw [hreg' 22, show (22 : Fin 32).val = 22 from rfl, hr22]
    simp only [Sym.eval, BinOp.eval, env_base3]
    simp [envOf]; bv_omega
  have e14 : m'.reg 14 = m.reg 14 := by
    rw [hreg' 14, show (14 : Fin 32).val = 14 from rfl, hr14]
    simp [Sym.eval, envOf]
  have e21 : m'.reg 21 = m.reg 21 := by
    rw [hreg' 21, show (21 : Fin 32).val = 21 from rfl, hr21]
    simp [Sym.eval, envOf]
  have hmem' : mkCut (table[tgtIdx σ.t]!) ∈ vcPlan.cuts := List.mem_map_of_mem (by
    rw [getElem!_pos table _ hidx]; exact List.getElem_mem _)
  have hpcm' : m'.pc.toNat = tgtPc σ.t := by
    rw [hexok, htgt]; simp only [w, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
  have hne'' : (table[tgtIdx σ.t]!).pc ≠ entry := by rw [hpc']; exact hne'
  have hinner : innerOf σ m' (budgetAt (table[tgtIdx σ.t]!).pc).2 = 0 ∧
      CurOk σ m' (budgetAt (table[tgtIdx σ.t]!).pc).2 := by
    revert hin'
    cases (budgetAt (table[tgtIdx σ.t]!).pc).2 <;> simp [Inner.isNone, innerOf, CurOk]
  refine ⟨mkCut (table[tgtIdx σ.t]!), hmem', hpcm'.trans hpc'.symm, ?_, ?_⟩
  · simp only [mkCut, if_neg hne'', ACut]
    refine .inl ⟨hpl', hpcm'.trans hpc'.symm, hcm', shapeOk_of_holds hwf' hm' hR0 hfine' hsh',
      .inr (by rw [harms']; exact List.mem_singleton_self _), ?_, ?_, hinner.2,
      fun i hi => by rw [hrest'] at hi; simp [chkCount] at hi⟩
    · rw [hrest']
      intro r hr
      have := hrst r (by rw [hrest0]; exact hr)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simpa [Loc.word, e13, e14, e21, e22] using this
    · simp only [noExtra, Bool.and_eq_true, bne_iff_ne, ne_eq] at hnx
      simp only [Extra, if_neg hnx.1.1.1.1, if_neg hnx.1.1.1.2, if_neg hnx.1.1.2, if_neg hnx.1.2,
        if_neg hnx.2]
  · show budgetOf (table[tgtIdx σ.t]!) σ m' ≤ budgetOf (table[1]!) σ m -
      (((leavesAt 0x80000574)[0]!).S.steps - (table[1]!).shape.S.steps)
    unfold budgetOf restLen
    rw [hrest', hrest0, hpc, hb1, hi1, hsteps, hinner.1]
    simp only [List.find?, Loc.word, innerOf]
    show (budgetAt (table[tgtIdx σ.t]!).pc).1 + 256 * (m'.reg 14).toNat + 0 ≤
      34359750395 + 256 * (m.reg 14).toNat + 0 - 5
    rw [e14]
    omega

end ZesuExec.Fn.DTF
