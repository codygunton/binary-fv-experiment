import ZesuExec.Fn.Rotate.C8330.Runs
import ZesuExec.Fn.Rotate.Tac

/-!
# `mem.rotate__anon_8330` in the obligation framework

The assertions are `Rotate.OuterA`/`InnerA`/`EpiA` with this copy's register equations; the
budgets count `7` per byte, `7·48 + 9 = 345` per element pair and the joins between the
reversals.
-/

namespace ZesuExec.Fn.Rotate.C8330
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Fn.Rotate

/-! ## Register equations (`p` = `a0`, `n` = `a1`, `a` = `a2` at entry) -/

/-- The word `-48`. -/
def mE : Word := w (2 ^ 64 - 48)

@[rot_simp] def eqO1 (m : Machine) (i : Nat) : List (Nat × Word) :=
  [(10, ptr m), (11, w (len m)), (12, w (amt m)), (15, w (amt m / 2)), (16, w i),
   (13, w (16 * amt m)), (14, w (64 * amt m)), (17, w (48 * amt m)),
   (5, ptr m + w (48 * (amt m - 1 - i))), (6, mE), (7, ptr m + w (48 * i))]
@[rot_simp] def eqI1 (m : Machine) (i _k : Nat) : List (Nat × Word) :=
  eqO1 m i ++ [(28, ptr m + w (48 * (amt m - i)))]

@[rot_simp] def eqO2 (m : Machine) (i : Nat) : List (Nat × Word) :=
  [(10, ptr m), (11, w (len m)), (17, w i), (16, w ((len m - amt m) / 2)), (12, w (16 * len m)),
   (15, w (64 * len m)), (13, w (48 * len m)), (14, ptr m + w (48 * (amt m + i))),
   (5, ptr m + w (48 * (len m - 1 - i))), (6, mE)]
@[rot_simp] def eqI2 (m : Machine) (i _k : Nat) : List (Nat × Word) :=
  eqO2 m i ++ [(7, ptr m + w (48 * (len m - i)))]

@[rot_simp] def eqO3 (m : Machine) (i : Nat) : List (Nat × Word) :=
  [(10, ptr m), (13, w i), (11, w (len m / 2)), (15, w (48 * len m)),
   (12, ptr m + w (48 * (len m - 1 - i))), (14, mE), (16, ptr m + w (48 * i))]
@[rot_simp] def eqI3 (m : Machine) (i _k : Nat) : List (Nat × Word) :=
  eqO3 m i ++ [(17, ptr m + w (48 * (len m - i)))]

/-! ## Budgets -/

@[rot_simp] def H1 (m : Machine) : Nat := amt m / 2
@[rot_simp] def H2 (m : Machine) : Nat := (len m - amt m) / 2
@[rot_simp] def H3 (m : Machine) : Nat := len m / 2
@[rot_simp] def R3 (_m : Machine) : Nat := 5
@[rot_simp] def R2 (m : Machine) : Nat := H3 m * 345 + 13
@[rot_simp] def R1 (m : Machine) : Nat := 12 + H2 m * 345 + R2 m

@[rot_simp] def bound : Nat := 2 ^ 32 + 40

@[rot_simp] def bO (H R : Machine → Nat) (ir : Nat) (m mh : Machine) : Nat := (H m - ix mh ir) * 345 + R m
@[rot_simp] def bI (H R : Machine → Nat) (ir lo base : Nat) (m mh : Machine) : Nat :=
  (H m - ix mh ir) * 345 - 5 - 7 * kx mh lo base + R m

/-! ## Budgets as functions of the loop counters -/

section
variable {m mh : Machine} {i k : Nat}

theorem bO_val {H R : Machine → Nat} {ir : Nat} (h : Pre cfg m) (hb : 2 * i + 2 ≤ len m)
    (hr : mh.reg (Fin.ofNat 32 ir) = w i) : bO H R ir m mh = (H m - i) * 345 + R m := by
  have hfit := pre_hfit h; simp only [cfg] at hfit
  unfold bO; rw [ix_eq hr (by omega)]

theorem bI_val {H R : Machine → Nat} {ir lo base : Nat} {b : Nat} (h : Pre cfg m)
    (hb : 2 * i + 2 ≤ len m) (hbl : b + k < 48 * len m)
    (hr : mh.reg (Fin.ofNat 32 ir) = w i) (hl : mh.reg (Fin.ofNat 32 lo) = ptr m + w (b + k))
    (hbase : mh.reg (Fin.ofNat 32 base) = ptr m + w b) :
    bI H R ir lo base m mh = (H m - i) * 345 - 5 - 7 * k + R m := by
  have hfit := pre_hfit h; simp only [cfg] at hfit
  unfold bI; rw [ix_eq hr (by omega), kx_eq hl hbase (by omega) (by omega)]
  congr 2; omega

end

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
  budget := bO H1 R1 16

def cI1 : Cut Machine where
  pc := i1
  S := SI 29 30
  A := InnerA cfg .one i1 29 30 eqI1
  env := fun _ mh => envI 29 30 mh
  budget := bI H1 R1 16 29 7

def cO2 : Cut Machine where
  pc := o2
  S := SO
  A := OuterA cfg .two o2 eqO2
  env := fun _ mh => envO mh
  budget := bO H2 R2 17

def cI2 : Cut Machine where
  pc := i2
  S := SI 28 29
  A := InnerA cfg .two i2 28 29 eqI2
  env := fun _ mh => envI 28 29 mh
  budget := bI H2 R2 17 28 14

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
  budget := fun _ _ => 5

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

zesu_plan R8330 := vcPlan

zesu_auto R8330

end ZesuExec.Fn.Rotate.C8330
