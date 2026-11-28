import ZesuExec.Fn.Rotate.C10572.Runs
import ZesuExec.Fn.Rotate.Tac

/-!
# `mem.rotate__anon_10572` in the obligation framework

The assertions are `Rotate.OuterA`/`InnerA`/`EpiA` with this copy's register equations; the
budgets count `7` per byte, `7·104 + 9 = 737` per element pair and the joins between the
reversals.
-/

namespace ZesuExec.Fn.Rotate.C10572
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Fn.Rotate

/-! ## Register equations (`p` = `a0`, `n` = `a1`, `a` = `a2` at entry) -/

/-- The word `-104`. -/
def mE : Word := w (2 ^ 64 - 104)

@[rot_simp] def eqO1 (m : Machine) (i : Nat) : List (Nat × Word) :=
  [(10, ptr m), (11, w (len m)), (12, w (amt m)), (13, w (amt m / 2)), (14, w i),
   (15, w (104 * amt m)), (16, ptr m + w (104 * (amt m - 1 - i))), (17, mE),
   (5, ptr m + w (104 * i))]
@[rot_simp] def eqI1 (m : Machine) (i _k : Nat) : List (Nat × Word) :=
  eqO1 m i ++ [(6, ptr m + w (104 * (amt m - i)))]

@[rot_simp] def eqO2 (m : Machine) (i : Nat) : List (Nat × Word) :=
  [(10, ptr m), (11, w (len m)), (14, w i), (13, w ((len m - amt m) / 2)), (12, w (104 * len m)),
   (15, ptr m + w (104 * (amt m + i))), (16, ptr m + w (104 * (len m - 1 - i))), (17, mE)]
@[rot_simp] def eqI2 (m : Machine) (i _k : Nat) : List (Nat × Word) :=
  eqO2 m i ++ [(5, ptr m + w (104 * (len m - i)))]

@[rot_simp] def eqO3 (m : Machine) (i : Nat) : List (Nat × Word) :=
  [(10, ptr m), (13, w i), (12, w (len m / 2)), (11, w (104 * len m)),
   (14, ptr m + w (104 * (len m - 1 - i))), (15, mE), (16, ptr m + w (104 * i))]
@[rot_simp] def eqI3 (m : Machine) (i _k : Nat) : List (Nat × Word) :=
  eqO3 m i ++ [(17, ptr m + w (104 * (len m - i)))]

/-! ## Budgets -/

@[rot_simp] def H1 (m : Machine) : Nat := amt m / 2
@[rot_simp] def H2 (m : Machine) : Nat := (len m - amt m) / 2
@[rot_simp] def H3 (m : Machine) : Nat := len m / 2
@[rot_simp] def R3 (_m : Machine) : Nat := 4
@[rot_simp] def R2 (m : Machine) : Nat := H3 m * 737 + 13
@[rot_simp] def R1 (m : Machine) : Nat := 11 + H2 m * 737 + R2 m

@[rot_simp] def bound : Nat := 2 ^ 32 + 40

@[rot_simp] def bO (H R : Machine → Nat) (ir : Nat) (m mh : Machine) : Nat := (H m - ix mh ir) * 737 + R m
@[rot_simp] def bI (H R : Machine → Nat) (ir lo base : Nat) (m mh : Machine) : Nat :=
  (H m - ix mh ir) * 737 - 5 - 7 * kx mh lo base + R m

/-! ## The plan -/

def cE : Cut Machine where
  pc := entry
  S := S0 cfg
  A := fun m mh => mh = m ∧ mh.pc.toNat = entry ∧ Pre cfg m
  env := fun m _ => env0 cfg m
  budget := fun _ _ => bound

def cO1 : Cut Machine where
  pc := o1
  S := SO
  A := OuterA cfg .one o1 eqO1
  env := fun _ mh => envO mh
  budget := bO H1 R1 14

def cI1 : Cut Machine where
  pc := i1
  S := SI 7 28
  A := InnerA cfg .one i1 7 28 eqI1
  env := fun _ mh => envI 7 28 mh
  budget := bI H1 R1 14 7 5

def cO2 : Cut Machine where
  pc := o2
  S := SO
  A := OuterA cfg .two o2 eqO2
  env := fun _ mh => envO mh
  budget := bO H2 R2 14

def cI2 : Cut Machine where
  pc := i2
  S := SI 6 7
  A := InnerA cfg .two i2 6 7 eqI2
  env := fun _ mh => envI 6 7 mh
  budget := bI H2 R2 14 6 15

def cO3 : Cut Machine where
  pc := o3
  S := SO
  A := OuterA cfg .three o3 eqO3
  env := fun _ mh => envO mh
  budget := bO H3 R3 13

def cI3 : Cut Machine where
  pc := i3
  S := SI 5 6
  A := InnerA cfg .three i3 5 6 eqI3
  env := fun _ mh => envI 5 6 mh
  budget := bI H3 R3 13 5 16

def cEp : Cut Machine where
  pc := epi
  S := SE cfg
  A := EpiA cfg epi
  env := fun m mh => envE cfg m mh
  budget := fun _ _ => 4

def vcPlan : Plan Machine zesuImage where
  cuts := [cE, cO1, cI1, cO2, cI2, cO3, cI3, cEp]
  fuel := 200
  leaves := fun pc =>
    if pc = entry then runE_leaves else if pc = o1 then runO1_leaves
    else if pc = i1 then runI1_leaves else if pc = o2 then runO2_leaves
    else if pc = i2 then runI2_leaves else if pc = o3 then runO3_leaves
    else if pc = i3 then runI3_leaves else if pc = epi then runEp_leaves else []
  callee := fun _ => none
  Post := Post cfg

zesu_plan R10572 := vcPlan

zesu_auto R10572

end ZesuExec.Fn.Rotate.C10572
