import ZesuExec.Fn.Alloc.Runs
import ZesuExec.Vc.Tactics

/-!
# `alt_fl_alloc.alloc` in the obligation framework

Plan `AllocF` over `allocImage` (no rodata, `Fn/Alloc/Runs.lean`). `σ = Sig`: the live list and
the entry machine. Every cut state is an entry state (`Fn.entryState`) whose environment is
`entryEnv` of the machine at the cut, so each assertion states, about that machine: the kept
registers (`ra`, `sp`, `s0`–`s11`), the registers the next run reads, and memory relative to the
entry machine. Cut points and what they add:

* `0x8004267c`, `0x80042680` (joins of the size-class search): `a0 = sizeClassOfBytes len`;
  at the first `a4 = log2_align - 3`, at the second the class in `a3` when the alignment is 16.
* `0x800426a0` (after `free_lists + 8 * class`): the class `k` in `a3` with `ClassOk`, the head
  cell is region 0.
* `0x800426a8` (non-empty list): the head `a0` is region 1, the frame region 2.
* `0x80042740`, `0x80042760` (fresh block; before and after rounding `HEAP_POS` up): block size
  and alignment `classBytes k`; after rounding, the new bump pointer `p1` in `a0` and in memory.
* `0x800426e0`, `0x80042708` (oversized: `len > 16 MiB`, the same two steps with alignment
  `2^log2_align` and size `len`).

Budgets: the longest path is entry (21) → `0x8004267c` (1) → `0x80042680` (9) → `0x800426a0`
(9) → `0x80042740` (8) → `0x80042760` (5) = 53.
-/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## Images: `RunsIn` reads only `.text` -/

theorem next_allocImage (m : Machine) : next allocImage m = next zesuImage m := rfl

theorem runsIn_text {k : Nat} {m m' : Machine} (h : RunsIn allocImage k m m') :
    RunsIn zesuImage k m m' := by
  induction h with
  | refl => exact .refl
  | step hn _ ih => exact .step (by rw [← next_allocImage]; exact hn) ih

theorem rodata_allocImage (m : Machine) : RodataLoaded allocImage m := fun a b h => by
  simp [allocImage, Image.rodataByte?] at h

/-! ## Parameters and assertions -/

structure Sig where
  L : List (Word × Nat)
  m : Machine

def lenOf (g : Sig) : Nat := (g.m.reg 11).toNat
def alOf (g : Sig) : Nat := (g.m.reg 12).toNat
def scOf (g : Sig) : Nat := sizeClassOfBytes (lenOf g)
/-- `HEAP_POS` at entry. -/
def posOf (g : Sig) : Nat := ((rd g.m posAddr).getD 0).toNat

/-- `ra` and the callee-saved registers. -/
def keepRegs : List Nat := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

def Keep (g : Sig) (m : Machine) : Prop := ∀ i : Fin 32, i.val ∈ keepRegs → m.reg i = g.m.reg i

def Base (g : Sig) (pc : Nat) (m : Machine) : Prop :=
  AllocPre g.L g.m ∧ m.pc.toNat = pc ∧ Keep g m

/-- Class `k` serves the request: it holds `len` bytes at the requested alignment. -/
def ClassOk (g : Sig) (k : Nat) : Prop := scOf g ≤ k ∧ alOf g ≤ k + 3 ∧ k < 22

def AE (g : Sig) (m : Machine) : Prop := m = g.m ∧ m.pc.toNat = allocEntry ∧ AllocPre g.L g.m

def AJ1 (g : Sig) (m : Machine) : Prop :=
  Base g 0x8004267c m ∧ m.mem = g.m.mem ∧ m.reg 11 = g.m.reg 11 ∧ m.reg 12 = g.m.reg 12 ∧
  m.reg 10 = BitVec.ofNat 64 (scOf g) ∧ m.reg 14 = g.m.reg 12 - 3 ∧ (alOf g = 4 → scOf g ≤ 1)

def AJ2 (g : Sig) (m : Machine) : Prop :=
  Base g 0x80042680 m ∧ m.mem = g.m.mem ∧ m.reg 11 = g.m.reg 11 ∧ m.reg 12 = g.m.reg 12 ∧
  m.reg 10 = BitVec.ofNat 64 (scOf g) ∧
  (alOf g = 4 → m.reg 13 = BitVec.ofNat 64 (max (scOf g) 1))

def AP (g : Sig) (m : Machine) : Prop :=
  Base g 0x800426a0 m ∧ m.mem = g.m.mem ∧ m.reg 12 = g.m.reg 12 ∧ ClassOk g (m.reg 13).toNat ∧
  m.reg 11 = BitVec.ofNat 64 (0xa0534000 + 8 * (m.reg 13).toNat)

def AP1 (g : Sig) (m : Machine) : Prop :=
  Base g 0x800426a8 m ∧ m.mem = g.m.mem ∧ ClassOk g (m.reg 13).toNat ∧
  m.reg 11 = BitVec.ofNat 64 (0xa0534000 + 8 * (m.reg 13).toNat) ∧
  rd g.m (flBase + 8 * (m.reg 13).toNat) = some (m.reg 10) ∧ m.reg 10 ≠ 0

def AB (g : Sig) (m : Machine) : Prop :=
  Base g 0x80042740 m ∧ m.mem = g.m.mem ∧ m.reg 12 = BitVec.ofNat 64 0xa0d3473c ∧
  ∃ k, ClassOk g k ∧ m.reg 11 = BitVec.ofNat 64 (classBytes k) ∧
    m.reg 13 = BitVec.ofNat 64 (classBytes k)

/-- `HEAP_POS` rounded up to `p1`, which `a0` holds; memory is the entry's elsewhere. -/
def Rounded (g : Sig) (m : Machine) (p1 : Nat) : Prop :=
  m.reg 10 = BitVec.ofNat 64 p1 ∧ posOf g ≤ p1 ∧ p1 ≤ Layout.ramHi ∧
  rd m posAddr = some (BitVec.ofNat 64 p1) ∧
  SameOutside (InRange (BitVec.ofNat 64 posAddr) 8) g.m m

def AT (g : Sig) (m : Machine) : Prop :=
  Base g 0x80042760 m ∧ m.reg 12 = BitVec.ofNat 64 0xa0d3473c ∧
  m.reg 13 = BitVec.ofNat 64 0xa0d3475c ∧
  ∃ k p1, ClassOk g k ∧ m.reg 11 = BitVec.ofNat 64 (classBytes k) ∧ Rounded g m p1

def AO (g : Sig) (m : Machine) : Prop :=
  Base g 0x800426e0 m ∧ m.mem = g.m.mem ∧ m.reg 11 = g.m.reg 11 ∧ m.reg 12 = g.m.reg 12 ∧
  m.reg 13 = BitVec.ofNat 64 0xa0d346dc ∧ scOf g = 22

def AO2 (g : Sig) (m : Machine) : Prop :=
  Base g 0x80042708 m ∧ m.reg 11 = g.m.reg 11 ∧ m.reg 12 = BitVec.ofNat 64 0xa0d34704 ∧
  m.reg 13 = BitVec.ofNat 64 0xa0d346dc ∧ scOf g = 22 ∧ ∃ p1, Rounded g m p1

/-! ## Shapes -/

def shapeP (m : Machine) : Shape := [((m.reg 11 + 8, 8), wordR)]
def shapeP1 (m : Machine) : Shape :=
  [((m.reg 11 + 8, 8), wordR), ((m.reg 10, 8), wordR), ((m.reg 2 - 16, 16), frameR)]
def shapeV : Shape := [((BitVec.ofNat 64 posAddr, 16), varsR)]

def envOf (sh : Machine → Shape) (_ : Sig) (m : Machine) : Env := entryEnv m ((sh m).map (·.1))

def cE : Cut Sig := ⟨0x80042494, SE, AE, envOf fun _ => [], fun _ _ => 53⟩
def cJ1 : Cut Sig := ⟨0x8004267c, SE, AJ1, envOf fun _ => [], fun _ _ => 32⟩
def cJ2 : Cut Sig := ⟨0x80042680, SE, AJ2, envOf fun _ => [], fun _ _ => 31⟩
def cP : Cut Sig := ⟨0x800426a0, SP, AP, envOf shapeP, fun _ _ => 22⟩
def cP1 : Cut Sig := ⟨0x800426a8, SP1, AP1, envOf shapeP1, fun _ _ => 10⟩
def cO : Cut Sig := ⟨0x800426e0, SO, AO, envOf fun _ => shapeV, fun _ _ => 15⟩
def cO2 : Cut Sig := ⟨0x80042708, SO2, AO2, envOf fun _ => shapeV, fun _ _ => 5⟩
def cB : Cut Sig := ⟨0x80042740, SB, AB, envOf fun _ => shapeV, fun _ _ => 13⟩
def cT : Cut Sig := ⟨0x80042760, ST, AT, envOf fun _ => shapeV, fun _ _ => 5⟩

def allocPlan : Plan Sig allocImage where
  cuts := [cE, cJ1, cJ2, cP, cP1, cO, cO2, cB, cT]
  fuel := 64
  leaves := fun pc =>
    if pc = 0x80042494 then aRunE_leaves else if pc = 0x8004267c then aRunJ1_leaves
    else if pc = 0x80042680 then aRunJ2_leaves else if pc = 0x800426a0 then aRunP_leaves
    else if pc = 0x800426a8 then aRunP1_leaves else if pc = 0x800426e0 then aRunO_leaves
    else if pc = 0x80042708 then aRunO2_leaves else if pc = 0x80042740 then aRunB_leaves
    else if pc = 0x80042760 then aRunT_leaves else []
  callee := fun _ => none
  Post := fun g m' => AllocPost g.L g.m m'

zesu_plan AllocF := allocPlan

/-! ## Cut points -/

/-- `CutOK` of a cut whose state is an entry state over the shape `sh`. -/
theorem cutOK_entry {pc : Nat} {ov : Nat → Option Sym} {rs : List Region}
    {A : Sig → Machine → Prop} {sh : Machine → Shape} {bud : Sig → Machine → Nat}
    (hrs : ∀ m, (sh m).map (·.2) = rs)
    (h : ∀ g m, A g m → (∀ p ∈ sh m, RegionOk p) ∧ ((sh m).map (·.1)).Pairwise Fn.Disjoint ∧
      (∀ i : Fin 32, i.val ≠ 0 → ∀ s, ov i.val = some s →
        s.eval (entryEnv m ((sh m).map (·.1))) = m.reg i) ∧
      (∀ r j, r < rs.length → j < (entryEnv m ((sh m).map (·.1))).size r →
        (m.mem ((entryEnv m ((sh m).map (·.1))).base r + BitVec.ofNat 64 j)).isSome) ∧
      m.pc.toNat = pc) :
    CutOK allocPlan (⟨pc, Fn.entryState ov rs [], A, envOf sh, bud⟩ : Cut Sig) := by
  intro g m hA
  obtain ⟨hok, hd, hov, hpres, hpc⟩ := h g m hA
  have hwf := entry_wf (m := m) (ov := ov) (ks := []) (sh m) hok hd
  have hmt := entry_match (m := m) (regs := (sh m).map (·.1)) (ov := ov) (rs := rs) (ks := [])
    hov hpres (by simp)
  rw [hrs m] at hwf
  exact ⟨hwf, hmt, rodata_allocImage m, hpc⟩

theorem AllocF.cut_80042494 : CutOK AllocF.plan AllocF.plan.cuts[0]! :=
  cutOK_entry (sh := fun _ => []) (fun _ => rfl) fun _ _ hA =>
    ⟨by simp, by simp, fun _ _ _ hs => by simp at hs, fun _ _ h => by simp at h, hA.2.1⟩

theorem AllocF.cut_8004267c : CutOK AllocF.plan AllocF.plan.cuts[1]! :=
  cutOK_entry (sh := fun _ => []) (fun _ => rfl) fun _ _ hA =>
    ⟨by simp, by simp, fun _ _ _ hs => by simp at hs, fun _ _ h => by simp at h, hA.1.2.1⟩

theorem AllocF.cut_80042680 : CutOK AllocF.plan AllocF.plan.cuts[2]! :=
  cutOK_entry (sh := fun _ => []) (fun _ => rfl) fun _ _ hA =>
    ⟨by simp, by simp, fun _ _ _ hs => by simp at hs, fun _ _ h => by simp at h, hA.1.2.1⟩

/-! ## Leaf lemmas: common facts -/

theorem and63 {x : Word} (h : x.toNat ≤ 4) : x &&& BitVec.ofNat 64 63 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofNat 64 63).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

theorem sub3 (x : Word) : x + BitVec.ofNat 64 18446744073709551613 = x - 3 := by
  bv_omega

theorem envOf_vars (sh : Machine → Shape) (g : Sig) (m : Machine) (i : Nat) :
    (envOf sh g m).vars i = m.reg (Fin.ofNat 32 i) := rfl

/-- A cut state without regions: the run writes no memory. -/
theorem mem_of_noRegions {env : Env} {S : SState} {m m' : Machine} (hS : S.regions = [])
    (h : SameOutside (InWritable env S) m m') : m'.mem = m.mem := by
  funext a
  exact h a fun ⟨r, R, j, hR, _⟩ => by rw [hS] at hR; simp at hR

theorem keep_of {g : Sig} {m m' : Machine} {env : Env} {S : SState} (hm : Match env S m')
    (hk : ∀ i ∈ keepRegs, S.reg i = .var i) (hv : ∀ i : Fin 32, env.vars i.val = m.reg i)
    (hK : Keep g m) : Keep g m' := fun i hi => by
  rw [Match.reg_of hm i _ (hk i.val hi), Sym.eval_var, hv i, hK i hi]

theorem keep_entry {g : Sig} : Keep g g.m := fun _ _ => rfl

theorem envOf_var (sh : Machine → Shape) (g : Sig) (m : Machine) (i : Fin 32) :
    (envOf sh g m).vars i.val = m.reg i := by
  simp [envOf, entryEnv]

/-- An entry leaf: it ends at a join of the size-class search with `a0` the size class. -/
theorem leafE {l : Leaf} {pcJ : Nat} (hJ : pcJ = 0x8004267c ∨ pcJ = 0x80042680)
    (hex : l.exit = .at pcJ) (hmem : l.S.regions = []) (hst : l.S.steps + (if pcJ = 0x8004267c then 32 else 31) ≤ 53)
    (hob : l.obligs = []) (hkeep : ∀ i ∈ 11 :: keepRegs, l.S.reg i = .var i)
    (h12 : l.S.reg 12 = .bin .and (.var 12) (.lit 63)) (h13 : l.S.reg 13 = l.S.reg 10)
    (h14 : l.S.reg 14 = .bin .add (.bin .and (.var 12) (.lit 63)) (.lit 18446744073709551613))
    (hsem : ∀ g, AllocPre g.L g.m →
      (∀ b ∈ l.conds, b.eval (envOf (fun _ => []) g g.m) = true) →
      (l.S.reg 10).eval (envOf (fun _ => []) g g.m) = BitVec.ofNat 64 (scOf g) ∧
      (pcJ = 0x8004267c → alOf g = 4 → scOf g ≤ 1) ∧ (pcJ = 0x80042680 → alOf g = 4 → 1 ≤ scOf g)) :
    LeafGoal allocPlan cE l := by
  intro g m hA hc
  obtain ⟨rfl, -, hpre⟩ := hA
  obtain ⟨hv10, hj1, hj2⟩ := hsem g hpre hc
  have hS0 : cE.S.steps = 0 := rfl
  refine ⟨by rw [hob]; simp, ?_, fun m' hm' he hso => ?_⟩
  · show l.S.steps - 0 ≤ 53
    split at hst <;> omega
  have hmm := mem_of_noRegions (S := cE.S) rfl hso
  rw [hex] at he
  have hpc : m'.pc.toNat = pcJ := he
  have hK : Keep g m' := keep_of hm' (fun i hi => hkeep i (List.mem_cons_of_mem _ hi))
    (envOf_var (fun _ => []) g g.m) keep_entry
  have r11 : m'.reg 11 = g.m.reg 11 := by
    rw [Match.reg_of hm' 11 _ (hkeep 11 (List.mem_cons_self ..))]; rfl
  have r12 : m'.reg 12 = g.m.reg 12 := by
    rw [Match.reg_of hm' 12 _ h12]
    simp only [Sym.eval, BinOp.eval, envOf_vars]
    exact and63 hpre.2.2.2.1
  have r10 : m'.reg 10 = BitVec.ofNat 64 (scOf g) := by rw [Match.reg_of hm' 10 _ rfl]; exact hv10
  have r13 : m'.reg 13 = BitVec.ofNat 64 (scOf g) := by rw [Match.reg_of hm' 13 _ h13]; exact hv10
  have r14 : m'.reg 14 = g.m.reg 12 - 3 := by
    rw [Match.reg_of hm' 14 _ h14]
    simp only [Sym.eval, BinOp.eval]
    rw [show (cE.env g g.m).vars 12 = g.m.reg 12 from rfl, and63 hpre.2.2.2.1]; exact sub3 _
  have hSE : SE.steps = 0 := rfl
  rw [hex]
  rcases hJ with rfl | rfl
  · refine ExitGoal.at_cut rfl ⟨cJ1, by simp [allocPlan], hpc, ⟨⟨hpre, hpc, hK⟩, hmm, r11, r12, r10,
      r14, hj1 rfl⟩, ?_⟩
    simp only [cJ1, cE, hSE] at hst ⊢; simp at hst; omega
  · refine ExitGoal.at_cut rfl ⟨cJ2, by simp [allocPlan], hpc, ⟨⟨hpre, hpc, hK⟩, hmm, r11, r12, r10,
      fun h4 => by rw [r13, Nat.max_eq_left (hj2 rfl h4)]⟩, ?_⟩
    simp only [cJ2, cE, hSE] at hst ⊢; simp at hst; omega

/-- The size class an entry leaf computes, under its conditions on `len` (`sizeClassOfBytes`
unfolded to the interval the conditions fix), and the alignment test of its last condition. -/
macro "sc_tac" : tactic => `(tactic| (unfold sizeClassOfBytes; repeat' split) <;> omega)

set_option hygiene false in
macro "cls_sem" : tactic => `(tactic| (
  intro g hpre hc
  have hx := hpre.2.2.1
  have ha := hpre.2.2.2.1
  simp only [SState.reg, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceEqDiff, ↓reduceIte,
    List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, SBool.eval, Sym.eval,
    BinOp.eval, envOf_vars, Fin.reduceOfNat, Fin.isValue, BitVec.ult, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, BitVec.toNat_ofNat] at hc ⊢
  unfold scOf alOf lenOf
  rw [and63 ha] at hc
  generalize g.m.reg 12 = y at *
  generalize g.m.reg 11 = x at *
  generalize hX : x.toNat = X at *
  have hsl := sc_le X
  try (split <;> rename_i hs <;> simp only [hs, ↓reduceIte] at hc)
  all_goals simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, BitVec.reduceXOr,
    BitVec.reduceSub, BitVec.ofNat_eq_ofNat] at *
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.reduceMod]
       rw [Nat.mod_eq_of_lt (by omega)]; sc_tac)
    | (intro h1 h2; first | exact h1.elim | (
        have hy : y = 4#64 := BitVec.eq_of_toNat_eq (by simp [h2])
        subst hy
        simp only [BitVec.reduceAdd, BitVec.toNat_ofNat, Nat.reduceMod] at hc
        sc_tac))))

theorem AllocF.leaf_80042494_0 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[0]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_1 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[1]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_2 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[2]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_3 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[3]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_4 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[4]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_5 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[5]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_6 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[6]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_7 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[7]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_8 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[8]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_9 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[9]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_10 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[10]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_11 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[11]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_12 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[12]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_13 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[13]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_14 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[14]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_15 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[15]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_16 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[16]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_17 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[17]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_18 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[18]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_19 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[19]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_20 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[20]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_21 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[21]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_22 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[22]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_23 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[23]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_24 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[24]! := by
  leaf_intro
  refine leafE (pcJ := 0x8004267c) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

theorem AllocF.leaf_80042494_25 :
    LeafGoal AllocF.plan AllocF.plan.cuts[0]! (AllocF.plan.leaves 0x80042494)[25]! := by
  leaf_intro
  refine leafE (pcJ := 0x80042680) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_
  cls_sem

end ZesuExec.Fn.Alloc
