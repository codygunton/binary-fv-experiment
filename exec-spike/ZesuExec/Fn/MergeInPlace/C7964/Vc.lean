import ZesuExec.Fn.MergeInPlace.C7964.Runs
import ZesuExec.Fn.MergeInPlace.Lemmas
import ZesuExec.Vc.Tactics

/-!
# `sort.block.mergeInPlace__anon_7964` in the obligation framework

Every assertion after the entry is `Pre`, the pc, `Common` and, for some items `G` and round
`[as, ae)`: `Items G`, the round's semantic state (`Round`, the searches' `First`/`Last`, `MidR`
during the rotation, `JoinR` after it) and the registers (`RegsAre`). The budget of a round is
`Q` (the rounds after it, `Rb` each: `as` strictly grows) plus what is left of this one: the
`binaryFirst` probes (800 per unit of the search size), the rotation's swaps (115 per element
pair) and `binaryLast` (`LST`).
-/

namespace ZesuExec.Fn.MergeInPlace.C7964
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Fn.MergeInPlace
open ZesuExec.Fn.Rotate (revAt rev)

/-! ## Registers (`p` = `a0`, `f` the frame) -/

/-- `a0 = p`, `a1 = B.end`, `a2 = p + 15`, `a4 = p - 16`, `a5 = 1`. -/
def eqB (m : Machine) : List (Nat × Word) :=
  [(10, ptr m), (11, w (bE m)), (12, ptr m + w 15), (14, ptr m - w 16), (15, w 1)]

/-- The round `[as, ae)` (`a3`, `a7`) during `binaryFirst`: `t0 = 32·as`, `t1 = &items[as]`. -/
def eqF (m : Machine) (as ae : Nat) : List (Nat × Word) :=
  eqB m ++ [(13, w as), (17, w ae), (5, w (32 * as)), (6, ptr m + w (32 * as))]

/-- The rotation: `a3 = as`, `a7 = ae`, `a6 = mid`. -/
def eqM (m : Machine) (as ae mid : Nat) : List (Nat × Word) :=
  eqB m ++ [(13, w as), (17, w ae), (16, w mid)]

/-- `binaryLast` on `[as, ae)`: `a6 = ae`, `a7 = &items[as]`, `a3 = curr`. -/
def eqL (m : Machine) (as ae curr : Nat) : List (Nat × Word) :=
  eqB m ++ [(16, w ae), (17, ptr m + w (32 * as)), (13, w curr)]

/-! ## Assertions -/

/-- What every cut after the prologue states. -/
def At (pc : Nat) (m mh : Machine) : Prop := Pre cfg m ∧ mh.pc.toNat = pc ∧ Common cfg m mh

/-- A round of the outer loop with its `First` search. -/
def FirstS (m : Machine) (G : Nat → Nat → Byte) (as ae curr size : Nat) : Prop :=
  Round cfg m G as ae ∧ as < ae ∧ First (cfg.key m) G (el G as) ae (bE m) curr size

/-- `binaryLast` after the rotation. -/
def LastS (m : Machine) (G : Nat → Nat → Byte) (as ae curr size : Nat) : Prop :=
  JoinR cfg m G as ae ∧ ae < bE m ∧ Last (cfg.key m) G (el G as) as ae curr size

def aOut (m mh : Machine) : Prop := At cOut m mh ∧ ∃ G as ae, Items m mh G ∧
  Round cfg m G as ae ∧ as < ae ∧ RegsAre mh (eqB m ++ [(13, w as), (17, w ae), (28, w ae)])

def aF (m mh : Machine) : Prop := At cF m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  FirstS m G as ae curr size ∧ 0 < size ∧ RegsAre mh (eqF m as ae ++ [(16, w curr), (7, w size)])

def aFp (m mh : Machine) : Prop := At cFp m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  FirstS m G as ae curr size ∧ 0 < size ∧
  (∀ j < 32, mh.mem (frame cfg m + w (32 + j)) = some (G as j)) ∧
  RegsAre mh (eqF m as ae ++ [(16, w curr), (28, w size), (7, w (size / 2)),
    (20, ptr m + w (32 * (curr + size / 2))), (30, frame cfg m + w 32), (29, w 32)])

def aFc (m mh : Machine) : Prop := At cFc m mh ∧ ∃ G as ae curr size k, Items m mh G ∧
  FirstS m G as ae curr size ∧ 0 < size ∧ k < 32 ∧
  (∀ j < 32, mh.mem (frame cfg m + w (32 + j)) = some (G as j)) ∧
  (∀ j < 32, mh.mem (frame cfg m + w j) = some (G (curr + size / 2) j)) ∧
  (∀ j < k, G (curr + size / 2) j = G as j) ∧
  RegsAre mh (eqF m as ae ++ [(16, w curr), (28, w size), (7, w (size / 2)), (29, w (32 - k)),
    (31, frame cfg m + w k), (30, frame cfg m + w (32 + k))])

def aFj (m mh : Machine) : Prop := At cFj m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  FirstS m G as ae curr (size / 2) ∧ 0 < size ∧
  RegsAre mh (eqF m as ae ++ [(16, w curr), (7, w (size / 2)), (28, w size)])

def aR0 (m mh : Machine) : Prop := At cR0 m mh ∧ ∃ G as ae mid, Items m mh G ∧
  MidR cfg m G as ae mid ∧ RegsAre mh (eqM m as ae mid ++ [(5, w (32 * as))])

def aR1 (m mh : Machine) : Prop := At cR1 m mh ∧ ∃ G as ae mid i,
  Items m mh (revAt as (ae - as) i 0 G) ∧ MidR cfg m G as ae mid ∧ 2 * i + 2 ≤ ae - as ∧
  RegsAre mh (eqM m as ae mid ++ [(5, w (32 * as)), (6, w (32 * ae)), (7, w (ae - as)),
    (28, ptr m + w (32 * (as + i) + 15)), (29, ptr m + w (32 * (ae - 1 - i) + 16)),
    (30, ptr m + w (32 * (as + (ae - as) / 2) + 15))])

def aS0 (m mh : Machine) : Prop := At cS0 m mh ∧ ∃ G as ae mid,
  Items m mh (rev as (ae - as) G) ∧ MidR cfg m G as ae mid ∧
  RegsAre mh (eqM m as ae mid ++ [(5, w (32 * as)), (6, w (32 * ae)), (7, w (ae - as))])

def aS1 (m mh : Machine) : Prop := At cS1 m mh ∧ ∃ G as ae mid i,
  Items m mh (revAt ae (mid - ae) i 0 (rev as (ae - as) G)) ∧ MidR cfg m G as ae mid ∧
  2 * i + 2 ≤ mid - ae ∧
  RegsAre mh (eqM m as ae mid ++ [(5, w (32 * as)), (28, w (mid - as)), (7, w (32 * mid)),
    (29, ptr m + w (32 * (ae + i) + 15)), (30, ptr m + w (32 * (mid - 1 - i) + 16)),
    (6, ptr m + w (32 * (ae + (mid - ae) / 2) + 15))])

def aT0 (m mh : Machine) : Prop := At cT0 m mh ∧ ∃ G as ae mid,
  Items m mh (rev ae (mid - ae) (rev as (ae - as) G)) ∧ MidR cfg m G as ae mid ∧
  RegsAre mh (eqM m as ae mid ++ [(5, w (32 * as)), (28, w (mid - as)), (7, w (32 * mid))])

def aT1 (m mh : Machine) : Prop := At cT1 m mh ∧ ∃ G as ae mid i,
  Items m mh (revAt as (mid - as) i 0 (rev ae (mid - ae) (rev as (ae - as) G))) ∧
  MidR cfg m G as ae mid ∧ 2 * i + 2 ≤ mid - as ∧
  RegsAre mh (eqM m as ae mid ++ [(6, ptr m + w (32 * (as + i) + 15)),
    (7, ptr m + w (32 * (mid - 1 - i) + 16)), (5, ptr m + w (32 * (as + (mid - as) / 2) + 15))])

def aJ (m mh : Machine) : Prop := At cJ m mh ∧ ∃ G as ae mid,
  Items m mh (R3 G as ae mid) ∧ MidR cfg m G as ae mid ∧ RegsAre mh (eqM m as ae mid)

def aL (m mh : Machine) : Prop := At cL m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  LastS m G as ae curr size ∧ 0 < size ∧ RegsAre mh (eqL m as ae curr ++ [(5, w size)])

def aLp (m mh : Machine) : Prop := At cLp m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  LastS m G as ae curr size ∧ 0 < size ∧
  (∀ j < 32, mh.mem (frame cfg m + w j) = some (G as j)) ∧
  RegsAre mh (eqL m as ae curr ++ [(6, w size), (5, w (size / 2)),
    (18, ptr m + w (32 * (curr + size / 2))), (28, frame cfg m + w 32), (7, w 32)])

def aLc (m mh : Machine) : Prop := At cLc m mh ∧ ∃ G as ae curr size k, Items m mh G ∧
  LastS m G as ae curr size ∧ 0 < size ∧ k < 32 ∧
  (∀ j < 32, mh.mem (frame cfg m + w j) = some (G as j)) ∧
  (∀ j < 32, mh.mem (frame cfg m + w (32 + j)) = some (G (curr + size / 2) j)) ∧
  (∀ j < k, G as j = G (curr + size / 2) j) ∧
  RegsAre mh (eqL m as ae curr ++ [(6, w size), (5, w (size / 2)), (7, w (32 - k)),
    (29, frame cfg m + w k), (28, frame cfg m + w (32 + k))])

def aLj (m mh : Machine) : Prop := At cLj m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  LastS m G as ae curr (size / 2) ∧ 0 < size ∧
  RegsAre mh (eqL m as ae curr ++ [(5, w (size / 2)), (6, w size)])

def aEp (m mh : Machine) : Prop := At cEp m mh ∧ ∃ G, Items m mh G ∧
  MergeOf (cfg.key m) (X m) (Y m) (win G (aS m) (bE m))

/-! ## Budgets -/

def N (m : Machine) : Nat := bE m - aS m
def Rb (m : Machine) : Nat := 2000 * N m + 400
def LST (m : Machine) : Nat := 800 * N m + 70
def ROT (m : Machine) : Nat := 120 * N m + 50
/-- The rounds after this one (`as` in `a3`). -/
def Q (m mh : Machine) : Nat := Qf (bE m) (ix mh 13) (Rb m)
/-- The same during `binaryLast` (`as` from `a7 = &items[as]`). -/
def QL (m mh : Machine) : Nat := Qf (bE m) (dx mh 17 10 / 32) (Rb m)

def bound : Nat := 4611686018427387904

def bOut (m mh : Machine) : Nat := Q m mh + Rb m + 20
def bF (m mh : Machine) : Nat := Q m mh + ROT m + LST m + 800 * ix mh 7 + 50
def bFp (m mh : Machine) : Nat := Q m mh + ROT m + LST m + 800 * ix mh 28 + 34
def bFc (m mh : Machine) : Nat := Q m mh + ROT m + LST m + (800 * ix mh 28 + 10 * ix mh 29 - 295)
def bFj (m mh : Machine) : Nat := Q m mh + ROT m + LST m + 800 * ix mh 7 + 60
def bR0 (m mh : Machine) : Nat := Q m mh + ROT m + LST m
def bR1 (m mh : Machine) : Nat := Q m mh + LST m + 115 * (dx mh 30 28 / 32) +
  115 * ((ix mh 16 - ix mh 17) / 2) + 115 * ((ix mh 16 - ix mh 13) / 2) + 30
def bS0 (m mh : Machine) : Nat := Q m mh + LST m +
  115 * ((ix mh 16 - ix mh 17) / 2) + 115 * ((ix mh 16 - ix mh 13) / 2) + 30
def bS1 (m mh : Machine) : Nat := Q m mh + LST m + 115 * (dx mh 6 29 / 32) + 115 * (ix mh 28 / 2) + 20
def bT0 (m mh : Machine) : Nat := Q m mh + LST m + 115 * (ix mh 28 / 2) + 15
def bT1 (m mh : Machine) : Nat := Q m mh + LST m + 115 * (dx mh 5 6 / 32) + 5
def bJ (m mh : Machine) : Nat := Q m mh + LST m
def bL (m mh : Machine) : Nat := QL m mh + 800 * ix mh 5 + 50
def bLp (m mh : Machine) : Nat := QL m mh + 800 * ix mh 6 + 34
def bLc (m mh : Machine) : Nat := QL m mh + (800 * ix mh 6 + 10 * ix mh 7 - 295)
def bLj (m mh : Machine) : Nat := QL m mh + 800 * ix mh 5 + 60

/-! ## The plan -/

def xE : Cut Machine where
  pc := entry
  S := S0 cfg
  A := fun m mh => mh = m ∧ mh.pc.toNat = entry ∧ Pre cfg m
  env := fun m _ => env0 cfg m
  budget := fun _ _ => bound

def xOut : Cut Machine := ⟨cOut, SN, aOut, fun _ mh => envN mh, bOut⟩
def xFj : Cut Machine := ⟨cFj, SN, aFj, fun _ mh => envN mh, bFj⟩
def xF : Cut Machine := ⟨cF, SP cfg 6 [], aF, fun _ mh => envP cfg 6 mh, bF⟩
def xFp : Cut Machine :=
  ⟨cFp, SP cfg 20 [(30, .ptr 0 0x20)], aFp, fun _ mh => envP cfg 20 mh, bFp⟩
def xFc : Cut Machine := ⟨cFc, SC 31 30, aFc, fun _ mh => envC 31 30 mh, bFc⟩
def xR0 : Cut Machine := ⟨cR0, SN, aR0, fun _ mh => envN mh, bR0⟩
def xR1 : Cut Machine := ⟨cR1, SR 28 29, aR1, fun _ mh => envR 28 29 mh, bR1⟩
def xS0 : Cut Machine := ⟨cS0, SN, aS0, fun _ mh => envN mh, bS0⟩
def xS1 : Cut Machine := ⟨cS1, SR 29 30, aS1, fun _ mh => envR 29 30 mh, bS1⟩
def xT0 : Cut Machine := ⟨cT0, SN, aT0, fun _ mh => envN mh, bT0⟩
def xT1 : Cut Machine := ⟨cT1, SR 6 7, aT1, fun _ mh => envR 6 7 mh, bT1⟩
def xJ : Cut Machine := ⟨cJ, SN, aJ, fun _ mh => envN mh, bJ⟩
def xL : Cut Machine := ⟨cL, SP cfg 17 [], aL, fun _ mh => envP cfg 17 mh, bL⟩
def xLp : Cut Machine :=
  ⟨cLp, SP cfg 18 [(28, .ptr 0 0x20)], aLp, fun _ mh => envP cfg 18 mh, bLp⟩
def xLc : Cut Machine := ⟨cLc, SC 29 28, aLc, fun _ mh => envC 29 28 mh, bLc⟩
def xLj : Cut Machine := ⟨cLj, SN, aLj, fun _ mh => envN mh, bLj⟩
def xEp : Cut Machine where
  pc := cEp
  S := SE cfg
  A := aEp
  env := fun m mh => envE cfg m mh
  budget := fun _ _ => 8

def vcPlan : Plan Machine zesuImage where
  cuts := [xE, xOut, xFj, xF, xFp, xFc, xR0, xR1, xS0, xS1, xT0, xT1, xJ, xL, xLp, xLc, xLj, xEp]
  fuel := 400
  leaves := fun pc =>
    if pc = entry then runE_leaves else if pc = cOut then runOut_leaves
    else if pc = cFj then runFj_leaves else if pc = cF then runF_leaves
    else if pc = cFp then runFp_leaves else if pc = cFc then runFc_leaves
    else if pc = cR0 then runR0_leaves else if pc = cR1 then runR1_leaves
    else if pc = cS0 then runS0_leaves else if pc = cS1 then runS1_leaves
    else if pc = cT0 then runT0_leaves else if pc = cT1 then runT1_leaves
    else if pc = cJ then runJ_leaves else if pc = cL then runL_leaves
    else if pc = cLp then runLp_leaves else if pc = cLc then runLc_leaves
    else if pc = cLj then runLj_leaves else if pc = cEp then runEp_leaves else []
  callee := fun _ => none
  Post := Post cfg

zesu_plan R7964 := vcPlan

zesu_auto R7964

end ZesuExec.Fn.MergeInPlace.C7964
