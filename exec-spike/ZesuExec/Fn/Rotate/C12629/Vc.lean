import ZesuExec.Fn.Rotate.C12629.Runs
import ZesuExec.Fn.Rotate.Tac

/-!
# `mem.rotate__anon_12629` in the obligation framework

The assertions are `Rotate.OuterA`/`InnerA`/`EpiA` with this copy's register equations; the
budgets count `7` per byte, `7·64 + 9 = 457` per element pair and the joins between the
reversals.
-/

namespace ZesuExec.Fn.Rotate.C12629
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Fn.Rotate

/-! ## Register equations (`p` = `a0`, `n` = `a1`, `a` = `a2` at entry) -/

/-- The word `-64`. This copy scales by shifts and never holds it; the shared tactics name it. -/
def mE : Word := w (2 ^ 64 - 64)

@[rot_simp] def eqO1 (m : Machine) (i : Nat) : List (Nat × Word) :=
  [(10, ptr m), (11, w (len m)), (12, w (amt m)), (14, w (amt m / 2)), (15, w i),
   (13, w (64 * amt m)), (16, ptr m + w (64 * (amt m - 1 - i))), (17, ptr m + w (64 * i))]
@[rot_simp] def eqI1 (m : Machine) (i _k : Nat) : List (Nat × Word) :=
  eqO1 m i ++ [(5, ptr m + w (64 * (amt m - i)))]

@[rot_simp] def eqO2 (m : Machine) (i : Nat) : List (Nat × Word) :=
  [(10, ptr m), (11, w (len m)), (15, w i), (14, w ((len m - amt m) / 2)), (12, w (64 * len m)),
   (13, ptr m + w (64 * (amt m + i))), (16, ptr m + w (64 * (len m - 1 - i)))]
@[rot_simp] def eqI2 (m : Machine) (i _k : Nat) : List (Nat × Word) :=
  eqO2 m i ++ [(17, ptr m + w (64 * (len m - i)))]

@[rot_simp] def eqO3 (m : Machine) (i : Nat) : List (Nat × Word) :=
  [(10, ptr m), (13, w i), (11, w (len m / 2)), (12, w (64 * len m)),
   (14, ptr m + w (64 * (len m - 1 - i))), (15, ptr m + w (64 * i))]
@[rot_simp] def eqI3 (m : Machine) (i _k : Nat) : List (Nat × Word) :=
  eqO3 m i ++ [(16, ptr m + w (64 * (len m - i)))]

/-! ## Budgets -/

@[rot_simp] def H1 (m : Machine) : Nat := amt m / 2
@[rot_simp] def H2 (m : Machine) : Nat := (len m - amt m) / 2
@[rot_simp] def H3 (m : Machine) : Nat := len m / 2
@[rot_simp] def R3 (_m : Machine) : Nat := 4
@[rot_simp] def R2 (m : Machine) : Nat := H3 m * 457 + 10
@[rot_simp] def R1 (m : Machine) : Nat := 8 + H2 m * 457 + R2 m

@[rot_simp] def bound : Nat := 2 ^ 32 + 40

@[rot_simp] def bO (H R : Machine → Nat) (ir : Nat) (m mh : Machine) : Nat := (H m - ix mh ir) * 457 + R m
@[rot_simp] def bI (H R : Machine → Nat) (ir lo base : Nat) (m mh : Machine) : Nat :=
  (H m - ix mh ir) * 457 - 5 - 7 * kx mh lo base + R m

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
  budget := bO H1 R1 15

def cI1 : Cut Machine where
  pc := i1
  S := SI 6 7
  A := InnerA cfg .one i1 6 7 eqI1
  env := fun _ mh => envI 6 7 mh
  budget := bI H1 R1 15 6 17

def cO2 : Cut Machine where
  pc := o2
  S := SO
  A := OuterA cfg .two o2 eqO2
  env := fun _ mh => envO mh
  budget := bO H2 R2 15

def cI2 : Cut Machine where
  pc := i2
  S := SI 5 6
  A := InnerA cfg .two i2 5 6 eqI2
  env := fun _ mh => envI 5 6 mh
  budget := bI H2 R2 15 5 13

def cO3 : Cut Machine where
  pc := o3
  S := SO
  A := OuterA cfg .three o3 eqO3
  env := fun _ mh => envO mh
  budget := bO H3 R3 13

def cI3 : Cut Machine where
  pc := i3
  S := SI 17 5
  A := InnerA cfg .three i3 17 5 eqI3
  env := fun _ mh => envI 17 5 mh
  budget := bI H3 R3 13 17 15

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

zesu_plan R12629 := vcPlan

zesu_auto R12629

end ZesuExec.Fn.Rotate.C12629
