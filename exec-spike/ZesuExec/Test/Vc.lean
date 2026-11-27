import ZesuExec.Vc.Assemble
import ZesuExec.Sym.Tactic
import ZesuExec.Vc.Legacy
import ZesuExec.Axioms

/-!
# Obligation framework tests (programme plan S2 step 6)

A toy function from four words: `li a0,3; L: addi a0,a0,-1; bnez a0,L; ret`. Cut points at the
entry and at the loop head `L`; three leaves. `zesu_auto` closes nothing (no automation before
S4); with every item proved by hand `zesu_assemble Toy` yields `Toy.reach`; a copy `Toy2` of the
plan without the theorem for leaf 1 of `L` yields `Toy2.Open` with exactly that field. Last, the
legacy table's theorem names exist.
-/

namespace ZesuExec.Test.VcTest
open ZesuExec ZesuExec.Sym ZesuExec.Vc

/-- `li a0,3; L: addi a0,a0,-1; bnez a0,L; ret` at `0x80000000`. -/
def toyImage : Image := ⟨[⟨0x80000000, [0x00300513, 0xfff50513, 0xfe051ee3, 0x00008067]⟩], []⟩

def retAddr : Word := 0x80000100

/-- Every register a variable. -/
def S0 : SState where
  regs := (List.range 32).map fun i => if i = 0 then .lit 0 else .var i
  mem := []
  known := []
  regions := []
  steps := 0

def envOf (m : Machine) : Env where
  vars := fun i => m.reg ⟨i % 32, Nat.mod_lt _ (by decide)⟩
  regions := []
  mem0 := fun _ _ => 0

def c0 : Cut Unit where
  pc := 0x80000000
  S := S0
  A := fun _ m => m.pc.toNat = 0x80000000 ∧ m.reg 1 = retAddr
  env := fun _ m => envOf m
  budget := fun _ _ => 8

def c1 : Cut Unit where
  pc := 0x80000004
  S := S0
  A := fun _ m => m.pc.toNat = 0x80000004 ∧ m.reg 1 = retAddr ∧
    1 ≤ (m.reg 10).toNat ∧ (m.reg 10).toNat ≤ 3
  env := fun _ m => envOf m
  budget := fun _ m => 2 * (m.reg 10).toNat + 1

theorem S0_wf (m : Machine) : Env.WF (envOf m) S0 where
  len := rfl
  disjoint := by intro r r' j j' _ hj; simp [Env.size, envOf] at hj
  size := by intro r R s h; simp [S0] at h
  align := by intro r R h; simp [S0] at h
  range := by intro r R h; simp [S0] at h

theorem S0_match (m : Machine) : Match (envOf m) S0 m where
  regsLen := rfl
  regs := by
    intro ⟨i, hi⟩
    by_cases h0 : i = 0
    · subst h0; simp [SState.reg, Sym.eval, Machine.reg]
    · simp [SState.reg, S0, h0, hi, Sym.eval, envOf, Nat.mod_eq_of_lt hi]
  mem := by intro r j hr; simp [S0] at hr
  known := by simp [S0]

theorem toy_ro (m : Machine) : RodataLoaded toyImage m := by
  intro a b h; simp [Image.rodataByte?, toyImage] at h

def cuts : List (Cut Unit) := [c0, c1]

sym_run run0 := run toyImage (cuts.map (·.pc)) 20 0x80000000 S0
sym_run run1 := run toyImage (cuts.map (·.pc)) 20 0x80000004 S0

def toyPlan : Plan Unit toyImage where
  cuts := cuts
  fuel := 20
  leaves := fun pc =>
    if pc = 0x80000000 then run0_leaves else if pc = 0x80000004 then run1_leaves else []
  callee := fun _ => none
  Post := fun _ m => m.reg 10 = 0

/--
info: ZesuExec.Test.VcTest.Toy: 2 cut points
  0x80000000: 1 leaves
  0x80000004: 2 leaves
-/
#guard_msgs in
zesu_plan Toy := toyPlan

/--
info: ZesuExec.Test.VcTest.Toy: zesu_auto closed 0 of 5 items
-/
#guard_msgs in
zesu_auto Toy

theorem Toy.cut_80000000 : CutOK Toy.plan Toy.plan.cuts[0]! := by
  show CutOK Toy.plan c0
  intro _ m hA
  exact ⟨S0_wf m, S0_match m, toy_ro m, hA.1⟩

theorem Toy.cut_80000004 : CutOK Toy.plan Toy.plan.cuts[1]! := by
  show CutOK Toy.plan c1
  intro _ m hA
  exact ⟨S0_wf m, S0_match m, toy_ro m, hA.1⟩

theorem Toy.leaf_80000000_0 :
    LeafGoal Toy.plan Toy.plan.cuts[0]! ((Toy.plan.leaves 0x80000000)[0]!) := by
  show LeafGoal Toy.plan c0 (run0_leaves[0]!)
  intro g m hA _
  obtain ⟨_, h1⟩ := hA
  refine ⟨by simp [run0_leaves], by simp [run0_leaves, c0, S0], fun m' hm' he _ => ?_⟩
  have r1 : m'.reg 1 = m.reg 1 := (hm'.regs 1).symm
  have r10 : m'.reg 10 = 3 := (hm'.regs 10).symm
  refine ⟨c1, by simp [Toy.plan, toyPlan, cuts], he, ⟨he, r1.trans h1, ?_⟩, ?_⟩ <;>
    simp [c1, c0, S0, run0_leaves, r10]

theorem Toy.leaf_80000004_0 :
    LeafGoal Toy.plan Toy.plan.cuts[1]! ((Toy.plan.leaves 0x80000004)[0]!) := by
  show LeafGoal Toy.plan c1 (run1_leaves[0]!)
  intro g m hA hc
  obtain ⟨_, h1, hlo, hhi⟩ := hA
  have hne := hc _ (List.mem_singleton_self _)
  simp [SBool.eval, Sym.eval, BinOp.eval, envOf, c1] at hne
  have hs : run1_leaves[0]!.S.steps - c1.S.steps = 2 := rfl
  have he0 : run1_leaves[0]!.exit = .at 0x80000004 := rfl
  rw [hs, he0]
  refine ⟨by simp [run1_leaves], by simp [c1]; omega, fun m' hm' he _ => ?_⟩
  have r1 : (Sym.var 1).eval (c1.env g m) = m'.reg 1 := hm'.regs 1
  have r10 : (Sym.bin .add (.var 10) (.lit 18446744073709551615)).eval (c1.env g m) = m'.reg 10 :=
    hm'.regs 10
  simp [Sym.eval, BinOp.eval, envOf, c1] at r1 r10
  refine ⟨c1, by simp [Toy.plan, toyPlan, cuts], he, ⟨he, r1 ▸ h1, ?_, ?_⟩, ?_⟩ <;>
    simp only [c1, ← r10] <;> bv_omega

theorem Toy.leaf_80000004_1 :
    LeafGoal Toy.plan Toy.plan.cuts[1]! ((Toy.plan.leaves 0x80000004)[1]!) := by
  show LeafGoal Toy.plan c1 (run1_leaves[1]!)
  intro g m hA hc
  obtain ⟨_, h1, hlo, _⟩ := hA
  have heq := hc _ (List.mem_singleton_self _)
  simp [SBool.eval, Sym.eval, BinOp.eval, envOf, c1] at heq
  have hs : run1_leaves[1]!.S.steps - c1.S.steps = 3 := rfl
  have hob : run1_leaves[1]!.obligs = [.aligned (.bin .and (.var 1) (.lit 18446744073709551614)) 4] :=
    rfl
  have he0 : run1_leaves[1]!.exit = .ret (.bin .and (.var 1) (.lit 18446744073709551614)) := rfl
  rw [hs, hob, he0]
  refine ⟨?_, by simp [c1]; omega, fun m' hm' _ _ => ?_⟩
  · intro o ho
    simp only [List.mem_singleton] at ho
    subst ho
    simp [Oblig.holds, Sym.eval, BinOp.eval, envOf, c1, h1, retAddr]
  · have r10 : (Sym.bin .add (.var 10) (.lit 18446744073709551615)).eval (c1.env g m) = m'.reg 10 :=
      hm'.regs 10
    simp [Sym.eval, BinOp.eval, envOf, c1] at r10
    show m'.reg 10 = 0
    rw [← r10, heq]; rfl

/--
info: ZesuExec.Test.VcTest.Toy: 5 items, 0 auto, 5 manual, 0 open
-/
#guard_msgs in
zesu_assemble Toy

/-- info: 'ZesuExec.Test.VcTest.Toy.reach' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Toy.reach

/-! The same plan with the leaf `0x80000004 [1]` left unproved: `Toy2.Open` has that one field. -/

/--
info: ZesuExec.Test.VcTest.Toy2: 2 cut points
  0x80000000: 1 leaves
  0x80000004: 2 leaves
-/
#guard_msgs in
zesu_plan Toy2 := toyPlan

theorem Toy2.cut_80000000 : CutOK Toy2.plan Toy2.plan.cuts[0]! := Toy.cut_80000000
theorem Toy2.cut_80000004 : CutOK Toy2.plan Toy2.plan.cuts[1]! := Toy.cut_80000004
theorem Toy2.leaf_80000000_0 :
    LeafGoal Toy2.plan Toy2.plan.cuts[0]! ((Toy2.plan.leaves 0x80000000)[0]!) := Toy.leaf_80000000_0
theorem Toy2.leaf_80000004_0 :
    LeafGoal Toy2.plan Toy2.plan.cuts[1]! ((Toy2.plan.leaves 0x80000004)[0]!) := Toy.leaf_80000004_0

/--
info: ZesuExec.Test.VcTest.Toy2: 5 items, 0 auto, 4 manual, 1 open
-/
#guard_msgs in
zesu_assemble Toy2

/--
info: structure ZesuExec.Test.VcTest.Toy2.Open : Prop
number of parameters: 0
fields:
  ZesuExec.Test.VcTest.Toy2.Open.leaf_80000004_1 : LeafGoal Toy2.plan Toy2.plan.cuts[1]!
      (Toy2.plan.leaves 2147483652)[1]!
constructor:
  ZesuExec.Test.VcTest.Toy2.Open.mk
    (leaf_80000004_1 : LeafGoal Toy2.plan Toy2.plan.cuts[1]! (Toy2.plan.leaves 2147483652)[1]!) : Toy2.Open
-/
#guard_msgs in
#print Toy2.Open

/-- `Toy.reach` at the entry cut as a `Spec`. -/
example : Spec toyImage 0x80000000 8 (fun m => m.reg 1 = retAddr) (fun _ m' => m'.reg 10 = 0) :=
  fun m hpc h1 => Toy.reach c0 (by simp [Toy.plan, toyPlan, cuts]) () m ⟨hpc, h1⟩

/-- Toy2 has `reach_from` and no `reach`. -/
example : ∀ c ∈ Toy2.plan.cuts, ∀ g m, c.A g m → Reaches toyImage (c.budget g m) (Toy2.plan.Post g) m :=
  Toy2.reach_from ⟨Toy.leaf_80000004_1⟩

run_cmd do
  if (← Lean.getEnv).contains `ZesuExec.Test.VcTest.Toy2.reach then throwError "Toy2.reach exists"
  for l in legacyFns do
    for n in [l.spec, l.sail] ++ l.compliance.toList do
      unless (← Lean.getEnv).contains n do throwError "legacy: {n} missing"

/-! A tail call: `j memcpy` at `0x80000000` (`jal x0, 0xe06c0`). The run stops at the `memcpy`
entry; the plan's `tail` names `Callee.memcpy` there, so the leaf goal asks for `MemcpyPre` at
the jump and `Post` of every `memcpy` result. -/

def tailImage : Image := ⟨[⟨0x80000000, [0x6c0e006f]⟩], []⟩

def ct : Cut Unit where
  pc := 0x80000000
  S := S0
  A := fun _ m => m.pc.toNat = 0x80000000 ∧ MemcpyPre m
  env := fun _ m => envOf m
  budget := fun _ _ => 4

sym_run runT := run tailImage [0x80000000] 20 0x80000000 S0

def tailPlan : Plan Unit tailImage where
  cuts := [ct]
  fuel := 20
  leaves := fun pc => if pc = 0x80000000 then runT_leaves else []
  callee := fun _ => none
  Post := fun _ m => m.pc = (m.reg 1 &&& ~~~(1 : Word))
  tail := fun pc => if pc = Layout.memcpyEntry then some (Callee.memcpy Unit tailImage) else none

/--
info: ZesuExec.Test.VcTest.Tail: 1 cut points
  0x80000000: 1 leaves
-/
#guard_msgs in
zesu_plan Tail := tailPlan

theorem Tail.cut_80000000 : CutOK Tail.plan Tail.plan.cuts[0]! := by
  show CutOK Tail.plan ct
  intro _ m hA
  exact ⟨S0_wf m, S0_match m, fun a b h => by simp [Image.rodataByte?, tailImage] at h, hA.1⟩

theorem Tail.leaf_80000000_0 :
    LeafGoal Tail.plan Tail.plan.cuts[0]! ((Tail.plan.leaves 0x80000000)[0]!) := by
  show LeafGoal Tail.plan ct (runT_leaves[0]!)
  intro g m hA _
  obtain ⟨_, hpre⟩ := hA
  have he0 : runT_leaves[0]!.exit = .at Layout.memcpyEntry := rfl
  have hs : runT_leaves[0]!.S.steps - ct.S.steps = 1 := rfl
  rw [he0, hs]
  refine ⟨by simp [runT_leaves], by simp [ct], fun m' hm' he hso => ?_⟩
  have hr : ∀ i : Fin 32, m'.reg i = m.reg i := fun i => by
    rw [← hm'.regs i, show runT_leaves[0]!.S.reg i.val = S0.reg i.val from rfl]
    exact (S0_match m).regs i
  have hmem : m'.mem = m.mem := funext fun a => hso a fun ⟨r, R, j, h, _⟩ => by
    simp [ct, S0] at h
  have hd : ziskMemcpyDomain m' = true := by
    have : ziskMemcpyDomain m' = ziskMemcpyDomain m := by simp only [ziskMemcpyDomain, hr, hmem]
    rw [this]; exact hpre
  refine ExitGoal.at_tail (k := Callee.memcpy Unit tailImage) (by rfl)
    ⟨he, hd, by simp [Callee.memcpy, ct], fun m'' hz => ?_⟩
  have hz : ziskMemcpy m' = some m'' := hz
  rw [ziskMemcpy, if_pos hd] at hz
  cases hz
  rfl

/--
info: ZesuExec.Test.VcTest.Tail: 2 items, 0 auto, 2 manual, 0 open
-/
#guard_msgs in
zesu_assemble Tail

/-- info: 'ZesuExec.Test.VcTest.Tail.reach' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tail.reach

end ZesuExec.Test.VcTest
