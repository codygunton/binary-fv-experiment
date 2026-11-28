import ZesuExec.Vc.Tactics
import ZesuExec.Test.Vc

/-!
# Automation tests (programme plan S4, Verification item 4)

1. `zesu_auto` on the toy plan of `ZesuExec.Test.Vc` (with the toy's `Env` and constants as
   `zesu_simp` lemmas) proves every cut and leaf, and `zesu_assemble` yields `Toy3.reach`.
2. Not unsound by construction: a reachable leaf of the toy asserted infeasible, and a leaf
   goal made false by a wrong postcondition (`Toy5`), are not proved (`fail_if_success`);
   `zesu_auto Toy5` leaves exactly that leaf open.
3. `region_tac` on two regions: `Env.WF`, an address outside the writable region, and bytes
   kept under `SameOutside`.
4. `sym_show` prints a leaf against its cut's state.
5. `budget_auto` (a budget behind a definition and a table read at a literal address) and
   `oblig_auto` (an index bound and a masked return alignment over `rEnv`) close their goals
   and fail on false ones (`fail_if_success`) (programme plan S11, Verification item 3).
-/

namespace ZesuExec.Test.AutoTest
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Test.VcTest

attribute [local zesu_simp] envOf retAddr toy_ro

zesu_plan Toy3 := toyPlan

/-- info: ZesuExec.Test.AutoTest.Toy3: zesu_auto closed 5 of 5 items -/
#guard_msgs in
zesu_auto Toy3

/-- info: ZesuExec.Test.AutoTest.Toy3: 5 items, 5 auto, 0 manual, 0 open -/
#guard_msgs in
zesu_assemble Toy3

/--
info: 'ZesuExec.Test.AutoTest.Toy3.reach' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Toy3.reach

/-! ## Failing on false goals -/

/-- The loop's back edge (`a0 - 1 ≠ 0`) is reachable from `a0 = 2`: not infeasible. -/
example : True := by
  fail_if_success
    have : ∀ m : Machine, c1.A () m →
        (∀ b ∈ (run1_leaves[0]!).conds, b.eval (envOf m) = true) → False := by
      intro m hA hc
      simp only [c1] at hA
      simp only [run1_leaves, List.getElem!_cons_zero] at hc
      leaf_infeasible
  trivial

/-- Control: with `a0 = 1` the back edge is infeasible, and `leaf_infeasible` proves it. -/
example : ∀ m : Machine, c1.A () m → m.reg 10 = 1 →
    (∀ b ∈ (run1_leaves[0]!).conds, b.eval (envOf m) = true) → False := by
  intro m hA h1 hc
  simp only [c1] at hA
  simp only [run1_leaves, List.getElem!_cons_zero] at hc
  leaf_infeasible

/-- `toyPlan` with the wrong postcondition `a0 = 1`. -/
def badPlan : Plan Unit toyImage := { toyPlan with Post := fun _ m => m.reg 10 = 1 }

zesu_plan Toy5 := badPlan

example : True := by
  fail_if_success
    have : LeafGoal Toy5.plan Toy5.plan.cuts[1]! ((Toy5.plan.leaves 0x80000004)[1]!) := by
      leaf_auto
  trivial

/-- info: ZesuExec.Test.AutoTest.Toy5: zesu_auto closed 4 of 5 items -/
#guard_msgs in
zesu_auto Toy5

/-- info: ZesuExec.Test.AutoTest.Toy5: 5 items, 4 auto, 0 manual, 1 open -/
#guard_msgs in
zesu_assemble Toy5

/--
info: structure ZesuExec.Test.AutoTest.Toy5.Open : Prop
number of parameters: 0
fields:
  ZesuExec.Test.AutoTest.Toy5.Open.leaf_80000004_1 : LeafGoal Toy5.plan Toy5.plan.cuts[1]!
      (Toy5.plan.leaves 2147483652)[1]!
constructor:
  ZesuExec.Test.AutoTest.Toy5.Open.mk
    (leaf_80000004_1 : LeafGoal Toy5.plan Toy5.plan.cuts[1]! (Toy5.plan.leaves 2147483652)[1]!) : Toy5.Open
-/
#guard_msgs in
#print Toy5.Open

/-! ## `region_tac` -/

/-- A writable 16-byte frame and a read-only 8-byte input, from two machine registers. -/
def rEnv (m : Machine) : Env where
  vars := fun i => m.reg (Fin.ofNat 32 i)
  regions := [(m.reg 2, 16), (m.reg 11, 8)]
  mem0 := fun _ _ => 0

def rS : SState where
  regs := []
  mem := []
  known := []
  regions := [⟨some 16, 16, true⟩, ⟨some 8, 1, false⟩]
  steps := 0

attribute [local zesu_simp] rEnv rS

/-- The facts a cut assertion would state. -/
def RFacts (m : Machine) : Prop :=
  Layout.ramLo ≤ (m.reg 2).toNat ∧ (m.reg 2).toNat + 16 ≤ Layout.ramHi ∧ (m.reg 2).toNat % 16 = 0 ∧
  Layout.inputLo ≤ (m.reg 11).toNat ∧ (m.reg 11).toNat + 8 ≤ Layout.inputHi

attribute [local zesu_simp] RFacts

example (m : Machine) (h : RFacts m) : Env.WF (rEnv m) rS := by
  region_tac

example (m : Machine) (h : RFacts m) (j : Nat) (hj : j < 8) :
    ¬ InWritable (rEnv m) rS (m.reg 11 + BitVec.ofNat 64 j) := by
  have e : (m.reg 11 + BitVec.ofNat 64 j).toNat = (m.reg 11).toNat + j := by
    simp only [RFacts, Layout.inputHi] at h
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  region_tac

example (m m' : Machine) (h : RFacts m) (hso : SameOutside (InWritable (rEnv m) rS) m m') (t : Nat)
    (ht : t < 8) : m'.mem (m.reg 11 + BitVec.ofNat 64 t) = m.mem (m.reg 11 + BitVec.ofNat 64 t) := by
  region_tac

/-- A wrong layout (the input 8 bytes into the frame, both in RAM) is not proved well formed. -/
example : True := by
  fail_if_success
    have : ∀ m : Machine, Layout.ramLo ≤ (m.reg 2).toNat → (m.reg 2).toNat + 16 ≤ Layout.ramHi →
        (m.reg 2).toNat % 16 = 0 → (m.reg 11).toNat = (m.reg 2).toNat + 8 →
        Env.WF (rEnv m) rS := by
      intro m h1 h2 h3 h4
      region_tac
  trivial

/-- Control: the same with the input right after the frame is well formed. -/
example (m : Machine) (h1 : Layout.ramLo ≤ (m.reg 2).toNat) (h2 : (m.reg 2).toNat + 24 ≤ Layout.ramHi)
    (h3 : (m.reg 2).toNat % 16 = 0) (h4 : (m.reg 11).toNat = (m.reg 2).toNat + 16) :
    Env.WF (rEnv m) rS := by
  region_tac

/-! ## `sym_show` -/

/--
info: at 0x80000004, 2 steps
  a0 = (a0₀ + -1)
  if (a0₀ + -1) != 0
-/
#guard_msgs in
example : LeafGoal Toy3.plan Toy3.plan.cuts[1]! ((Toy3.plan.leaves 0x80000004)[0]!) := by
  leaf_intro
  sym_show
  exact Toy3.leaf_80000004_0

/-! ## `budget_auto` and `oblig_auto` (programme plan S11) -/

/-- A budget behind a definition: 32 instructions per byte from `a1` to `a2`, plus 9. -/
def tBudget (m : Machine) : Nat := 32 * (m.reg 12 - m.reg 11).toNat + 9

/-- A budget table by cut address. -/
def tTable : List (Nat × Nat) := [(0x80000000, 300), (0x80000004, 41)]

def tAt (pc : Nat) : Nat := (tTable.lookup pc).getD 0

example (m : Machine) : 9 - 0 ≤ tBudget m := by budget_auto

example (n : Nat) : 40 ≤ tAt 0x80000004 + 3 * n := by budget_auto

/-- One more instruction than the definition allows when `a1 = a2`. -/
example : True := by
  fail_if_success
    have : ∀ m : Machine, 10 ≤ tBudget m := by
      intro m
      budget_auto
  trivial

/-- One more instruction than the table allows at `0x80000004` when `n = 0`. -/
example : True := by
  fail_if_success
    have : ∀ n : Nat, 42 ≤ tAt 0x80000004 + 3 * n := by
      intro n
      budget_auto
  trivial

/-- A one-byte read at offset `x3` of the 8-byte input region. -/
example (m : Machine) (h : (m.reg 3).toNat < 8) :
    ∀ o ∈ [Oblig.inBounds 1 0 (.var 3) 1 1], o.holds (rEnv m) := by
  oblig_auto

/-- The same read with `x3 = 8` allowed: past the end. -/
example : True := by
  fail_if_success
    have : ∀ m : Machine, (m.reg 3).toNat < 9 →
        ∀ o ∈ [Oblig.inBounds 1 0 (.var 3) 1 1], o.holds (rEnv m) := by
      intro m h
      oblig_auto
  trivial

/-- The return through the saved `ra` (frame bytes 8..15): it is the entry's `x1`, whose
alignment with bit 0 cleared is a fact. -/
example (m : Machine) (hra : Sym.eval (rEnv m) (.init 0 8 8) = m.reg 1)
    (hal : (m.reg 1 &&& ~~~1).toNat % 4 = 0) :
    ∀ o ∈ [Oblig.aligned (.bin .and (.init 0 8 8) (.lit 18446744073709551614)) 4],
      o.holds (rEnv m) := by
  oblig_auto

/-- The same with only 2-byte alignment known. -/
example : True := by
  fail_if_success
    have : ∀ m : Machine, Sym.eval (rEnv m) (.init 0 8 8) = m.reg 1 →
        (m.reg 1 &&& ~~~1).toNat % 2 = 0 →
        ∀ o ∈ [Oblig.aligned (.bin .and (.init 0 8 8) (.lit 18446744073709551614)) 4],
          o.holds (rEnv m) := by
      intro m hra hal
      oblig_auto
  trivial

end ZesuExec.Test.AutoTest
