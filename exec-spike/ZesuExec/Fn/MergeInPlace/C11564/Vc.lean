import ZesuExec.Fn.MergeInPlace.C11564.Runs
import ZesuExec.Vc.Tactics

/-!
# `sort.block.mergeInPlace__anon_11564` in the obligation framework

Every assertion after the entry is `Pre`, the pc, `Common`, the four slots the entry spills (`p+15`,
`p-16`, `p`, `B.end`) and, for some items `G` and round `[as, ae)`: `Items G`, the round's
semantic state (as `C7964`), the registers (`RegsAre`) and the live frame slots (`SlotsAre`). The
searches compare the strings two elements point to (`sliceKey`); the comparison loop's cuts carry
the equal prefix so far.

The budget of a round is the rounds after it (`Qf … Rb`) plus what is left of this one: `K` per
unit of a search's size (a probe costs at most `11` per string byte, `Lmax` the longest input
string), `140` per swap of the rotation, the last search `LST`. During the rotation and the last
search `as` lives in frame slots (`QS`, `QL`), read as `sl`.
-/

namespace ZesuExec.Fn.MergeInPlace.C11564
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Fn.MergeInPlace
open ZesuExec.Fn.Rotate (revAt rev)

/-! ## Registers and slots (`p` = `a0`, `f` the frame) -/

/-- The frame slots the entry writes: `p + 15`, `p - 16`, `p`, `B.end`. -/
def baseS (m : Machine) : List (Nat × Word) :=
  [(0x20, ptr m + w 15), (0x18, ptr m - w 16), (0x10, ptr m), (8, w (bE m))]

/-- The outer loop: `s1 = as`, `t0 = ae`, `t6 = B.end`, `t5 = p`, `s2 = 1`. -/
def eqO (m : Machine) (as ae : Nat) : List (Nat × Word) :=
  [(9, w as), (5, w ae), (31, w (bE m)), (30, ptr m), (18, w 1)]

/-- `binaryFirst`: also `t1 = v.ptr`, `t2 = v.len` (`v` = `A[0]`). -/
def eqF (m : Machine) (G : Nat → Nat → Byte) (as ae : Nat) : List (Nat × Word) :=
  eqO m as ae ++ [(6, slicePtr (el G as)), (7, w (sliceLen (el G as)))]

/-- `binaryLast` on `[as, ae)`: `t3 = ae`, `t5 = p`, `t6 = B.end`, `s2 = 1`, `a7 = v.ptr`,
`t0 = v.len`. -/
def eqL (m : Machine) (G : Nat → Nat → Byte) (as ae : Nat) : List (Nat × Word) :=
  [(28, w ae), (30, ptr m), (31, w (bE m)), (18, w 1), (17, slicePtr (el G as)),
    (5, w (sliceLen (el G as)))]

/-! ## Assertions -/

abbrev f (m : Machine) : Word := frame cfg m

/-- What every cut after the prologue states. -/
def At (pc : Nat) (m mh : Machine) : Prop :=
  Pre cfg m ∧ mh.pc.toNat = pc ∧ Common cfg m mh ∧ SlotsAre mh (f m) (baseS m)

def FirstS (m : Machine) (G : Nat → Nat → Byte) (as ae curr size : Nat) : Prop :=
  Round cfg m G as ae ∧ as < ae ∧ First (cfg.key m) G (el G as) ae (bE m) curr size

def LastS (m : Machine) (G : Nat → Nat → Byte) (as ae curr size : Nat) : Prop :=
  JoinR cfg m G as ae ∧ ae < bE m ∧ Last (cfg.key m) G (el G as) as ae curr size

/-- The strings of `x` and `y` agree below `k`. -/
def PreEq (m : Machine) (x y : List Byte) (k : Nat) : Prop :=
  ∀ j < k, strByte m (slicePtr x) j = strByte m (slicePtr y) j

/-- The slot `as` of the last search is read from: `mid - ae + as` of the rotation. -/
def sl (mh : Machine) (off : Nat) : Nat := u64 mh (mh.reg 2) off

def aOut (m mh : Machine) : Prop := At cOut m mh ∧ ∃ G as ae, Items m mh G ∧
  Round cfg m G as ae ∧ as < ae ∧ RegsAre mh (eqO m as ae ++ [(10, w ae)])

def aFv (m mh : Machine) : Prop := At cFv m mh ∧ ∃ G as ae, Items m mh G ∧
  Round cfg m G as ae ∧ as < ae ∧ ae < bE m ∧ SlotsAre mh (f m) [(0x58, w (32 * as))] ∧
  RegsAre mh (eqO m as ae ++ [(10, w ae), (11, ptr m + w (32 * as))])

def aF (m mh : Machine) : Prop := At cF m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  FirstS m G as ae curr size ∧ 0 < size ∧ SlotsAre mh (f m) [(0x58, w (32 * as))] ∧
  RegsAre mh (eqF m G as ae ++ [(17, w curr), (28, w size)])

def aFp (m mh : Machine) : Prop := At cFp m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  FirstS m G as ae curr size ∧ 0 < size ∧ SlotsAre mh (f m) [(0x58, w (32 * as))] ∧
  RegsAre mh (eqF m G as ae ++ [(17, w curr), (28, w (size / 2)), (29, w size),
    (10, ptr m + w (32 * (curr + size / 2)))])

def aFn (m mh : Machine) : Prop := At cFn m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  FirstS m G as ae curr size ∧ 0 < size ∧ SlotsAre mh (f m) [(0x58, w (32 * as))] ∧
  PreEq m (el G (curr + size / 2)) (el G as)
    (min (sliceLen (el G (curr + size / 2))) (sliceLen (el G as))) ∧
  RegsAre mh (eqF m G as ae ++ [(17, w curr), (28, w (size / 2)), (29, w size),
    (10, w (sliceLen (el G (curr + size / 2))))])

def aFc (m mh : Machine) : Prop := At cFc m mh ∧ ∃ G as ae curr size k, Items m mh G ∧
  FirstS m G as ae curr size ∧ 0 < size ∧ SlotsAre mh (f m) [(0x58, w (32 * as))] ∧
  k < min (sliceLen (el G (curr + size / 2))) (sliceLen (el G as)) ∧
  slicePtr (el G (curr + size / 2)) ≠ slicePtr (el G as) ∧
  PreEq m (el G (curr + size / 2)) (el G as) k ∧
  RegsAre mh (eqF m G as ae ++ [(17, w curr), (28, w (size / 2)), (29, w size),
    (10, w (sliceLen (el G (curr + size / 2)))), (11, slicePtr (el G (curr + size / 2)) + w k),
    (13, slicePtr (el G as) + w k),
    (12, w (min (sliceLen (el G (curr + size / 2))) (sliceLen (el G as)) - k))])

def aFj (m mh : Machine) : Prop := At cFj m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  FirstS m G as ae curr (size / 2) ∧ 0 < size ∧ SlotsAre mh (f m) [(0x58, w (32 * as))] ∧
  RegsAre mh (eqF m G as ae ++ [(17, w curr), (28, w (size / 2)), (29, w size)])

def aR0 (m mh : Machine) : Prop := At cR0 m mh ∧ ∃ G as ae mid, Items m mh G ∧
  MidR cfg m G as ae mid ∧ SlotsAre mh (f m) [(0x58, w (32 * as))] ∧
  RegsAre mh [(9, w as), (5, w ae), (17, w mid)]

/-- The rotation's slots: `32·as`, `mid`, `as`, `ae`. -/
def rotS (as ae mid : Nat) : List (Nat × Word) :=
  [(0x58, w (32 * as)), (0x48, w mid), (0x50, w as), (0x30, w ae)]

def aR1 (m mh : Machine) : Prop := At cR1 m mh ∧ ∃ G as ae mid i,
  Items m mh (revAt as (ae - as) i 0 G) ∧ MidR cfg m G as ae mid ∧ 2 * i + 2 ≤ ae - as ∧
  SlotsAre mh (f m) (rotS as ae mid ++ [(0x38, w (ae - as)), (0x40, w (32 * ae)),
    (0x60, ptr m + w (32 * (as + (ae - as) / 2) + 15))]) ∧
  RegsAre mh [(28, ptr m + w (32 * (as + i) + 15)), (29, ptr m + w (32 * (ae - 1 - i) + 16))]

def aS0 (m mh : Machine) : Prop := At cS0 m mh ∧ ∃ G as ae mid,
  Items m mh (rev as (ae - as) G) ∧ MidR cfg m G as ae mid ∧
  SlotsAre mh (f m) (rotS as ae mid ++ [(0x38, w (ae - as)), (0x40, w (32 * ae))])

def aS1 (m mh : Machine) : Prop := At cS1 m mh ∧ ∃ G as ae mid i,
  Items m mh (revAt ae (mid - ae) i 0 (rev as (ae - as) G)) ∧ MidR cfg m G as ae mid ∧
  2 * i + 2 ≤ mid - ae ∧
  SlotsAre mh (f m) (rotS as ae mid ++ [(0x40, w (32 * ae)), (0x28, w (mid - as)),
    (0x38, w (32 * mid)), (0x60, ptr m + w (32 * (ae + (mid - ae) / 2) + 15))]) ∧
  RegsAre mh [(29, ptr m + w (32 * (ae + i) + 15)), (30, ptr m + w (32 * (mid - 1 - i) + 16))]

def aT0 (m mh : Machine) : Prop := At cT0 m mh ∧ ∃ G as ae mid,
  Items m mh (rev ae (mid - ae) (rev as (ae - as) G)) ∧ MidR cfg m G as ae mid ∧
  SlotsAre mh (f m) (rotS as ae mid ++ [(0x28, w (mid - as)), (0x38, w (32 * mid))])

def aT1 (m mh : Machine) : Prop := At cT1 m mh ∧ ∃ G as ae mid i,
  Items m mh (revAt as (mid - as) i 0 (rev ae (mid - ae) (rev as (ae - as) G))) ∧
  MidR cfg m G as ae mid ∧ 2 * i + 2 ≤ mid - as ∧
  SlotsAre mh (f m) [(0x48, w mid), (0x50, w as), (0x30, w ae), (0x28, w (mid - as)),
    (0x38, w (32 * mid)), (0x58, ptr m + w (32 * (as + (mid - as) / 2) + 15))] ∧
  RegsAre mh [(6, ptr m + w (32 * (as + i) + 15)), (7, ptr m + w (32 * (mid - 1 - i) + 16))]

def aJ (m mh : Machine) : Prop := At cJ m mh ∧ ∃ G as ae mid,
  Items m mh (R3 G as ae mid) ∧ MidR cfg m G as ae mid ∧
  SlotsAre mh (f m) [(0x48, w mid), (0x50, w as), (0x30, w ae)]

/-- The last search's `as` from the slots. -/
def AsL (mh : Machine) (as : Nat) : Prop := sl mh 0x48 - sl mh 0x30 + sl mh 0x50 = as

def aLv (m mh : Machine) : Prop := At cLv m mh ∧ ∃ G as ae, Items m mh G ∧
  JoinR cfg m G as ae ∧ ae < bE m ∧ AsL mh as ∧
  RegsAre mh [(10, w as), (11, ptr m + w (32 * as)), (28, w ae), (30, ptr m), (31, w (bE m)),
    (18, w 1)]

def aL (m mh : Machine) : Prop := At cL m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  LastS m G as ae curr size ∧ 0 < size ∧ AsL mh as ∧
  RegsAre mh (eqL m G as ae ++ [(9, w curr), (6, w size)])

def aLp (m mh : Machine) : Prop := At cLp m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  LastS m G as ae curr size ∧ 0 < size ∧ AsL mh as ∧
  RegsAre mh (eqL m G as ae ++ [(9, w curr), (6, w (size / 2)), (7, w size),
    (10, ptr m + w (32 * (curr + size / 2)))])

def aLn (m mh : Machine) : Prop := At cLn m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  LastS m G as ae curr size ∧ 0 < size ∧ AsL mh as ∧
  PreEq m (el G as) (el G (curr + size / 2))
    (min (sliceLen (el G as)) (sliceLen (el G (curr + size / 2)))) ∧
  RegsAre mh (eqL m G as ae ++ [(9, w curr), (6, w (size / 2)), (7, w size),
    (10, w (sliceLen (el G (curr + size / 2))))])

def aLc (m mh : Machine) : Prop := At cLc m mh ∧ ∃ G as ae curr size k, Items m mh G ∧
  LastS m G as ae curr size ∧ 0 < size ∧ AsL mh as ∧
  k < min (sliceLen (el G as)) (sliceLen (el G (curr + size / 2))) ∧
  slicePtr (el G as) ≠ slicePtr (el G (curr + size / 2)) ∧
  PreEq m (el G as) (el G (curr + size / 2)) k ∧
  RegsAre mh (eqL m G as ae ++ [(9, w curr), (6, w (size / 2)), (7, w size),
    (10, w (sliceLen (el G (curr + size / 2)))), (13, slicePtr (el G as) + w k),
    (11, slicePtr (el G (curr + size / 2)) + w k),
    (12, w (min (sliceLen (el G as)) (sliceLen (el G (curr + size / 2))) - k))])

def aLj (m mh : Machine) : Prop := At cLj m mh ∧ ∃ G as ae curr size, Items m mh G ∧
  LastS m G as ae curr (size / 2) ∧ 0 < size ∧ AsL mh as ∧
  RegsAre mh (eqL m G as ae ++ [(9, w curr), (6, w (size / 2)), (7, w size)])

def aEp (m mh : Machine) : Prop := Pre cfg m ∧ mh.pc.toNat = cEp ∧ Common cfg m mh ∧ ∃ G,
  Items m mh G ∧ MergeOf (cfg.key m) (X m) (Y m) (win G (aS m) (bE m))

/-! ## Budgets -/

def N (m : Machine) : Nat := bE m - aS m
/-- A probe's steps per unit of a search's size. -/
def K (m : Machine) : Nat := 11 * Lmax m + 64
def ROT (m : Machine) : Nat := 140 * N m + 100
def LST (m : Machine) : Nat := K m * N m + 100
def Rb (m : Machine) : Nat := K m * N m + ROT m + LST m + 100
/-- The rounds after this one (`as` in `s1`). -/
def Q (m mh : Machine) : Nat := Qf (bE m) (ix mh 9) (Rb m)
/-- …during the rotation (`as` in slot `0x50`). -/
def QS (m mh : Machine) : Nat := Qf (bE m) (sl mh 0x50) (Rb m)
/-- …during `binaryLast`. -/
def QL (m mh : Machine) : Nat := Qf (bE m) (sl mh 0x48 - sl mh 0x30 + sl mh 0x50) (Rb m)

def bound : Nat := 2 ^ 100

def bOut (m mh : Machine) : Nat := Q m mh + Rb m + 20
def bFv (m mh : Machine) : Nat := Q m mh + ROT m + LST m + K m * (ix mh 31 - ix mh 10) + 40
def bF (m mh : Machine) : Nat := Q m mh + ROT m + LST m + K m * ix mh 28 + 30
def bFp (m mh : Machine) : Nat := Q m mh + ROT m + LST m + K m * ix mh 28 + 11 * Lmax m + 70
def bFc (m mh : Machine) : Nat := Q m mh + ROT m + LST m + K m * ix mh 28 + 11 * ix mh 12 + 55
def bFn (m mh : Machine) : Nat := Q m mh + ROT m + LST m + K m * ix mh 28 + 50
def bFj (m mh : Machine) : Nat := Q m mh + ROT m + LST m + K m * ix mh 28 + 40
def bR0 (m mh : Machine) : Nat := Q m mh + ROT m + LST m
def bR1 (m mh : Machine) : Nat := QS m mh + LST m + 140 * ((sl mh 0x60 - ix mh 28) / 32) +
  140 * ((sl mh 0x48 - sl mh 0x30) / 2) + 140 * ((sl mh 0x48 - sl mh 0x50) / 2) + 60
def bS0 (m mh : Machine) : Nat := QS m mh + LST m +
  140 * ((sl mh 0x48 - sl mh 0x30) / 2) + 140 * ((sl mh 0x48 - sl mh 0x50) / 2) + 60
def bS1 (m mh : Machine) : Nat := QS m mh + LST m + 140 * ((sl mh 0x60 - ix mh 29) / 32) +
  140 * (sl mh 0x28 / 2) + 40
def bT0 (m mh : Machine) : Nat := QS m mh + LST m + 140 * (sl mh 0x28 / 2) + 30
def bT1 (m mh : Machine) : Nat := QS m mh + LST m + 140 * ((sl mh 0x58 - ix mh 6) / 32) + 10
def bJ (m mh : Machine) : Nat := QS m mh + LST m
def bLv (m mh : Machine) : Nat := QL m mh + K m * (ix mh 28 - ix mh 10) + 50
def bL (m mh : Machine) : Nat := QL m mh + K m * ix mh 6 + 40
def bLp (m mh : Machine) : Nat := QL m mh + K m * ix mh 6 + 11 * Lmax m + 70
def bLc (m mh : Machine) : Nat := QL m mh + K m * ix mh 6 + 11 * ix mh 12 + 55
def bLn (m mh : Machine) : Nat := QL m mh + K m * ix mh 6 + 50
def bLj (m mh : Machine) : Nat := QL m mh + K m * ix mh 6 + 45

/-! ## The plan -/

def xE : Cut Machine where
  pc := entry
  S := S0 cfg
  A := fun m mh => mh = m ∧ mh.pc.toNat = entry ∧ Pre cfg m
  env := fun m _ => env0 cfg m
  budget := fun _ _ => bound

def xOut : Cut Machine := ⟨cOut, SF cfg, aOut, fun _ mh => envF cfg mh, bOut⟩
def xFv : Cut Machine := ⟨cFv, SP cfg 11 [], aFv, fun _ mh => envP cfg 11 mh, bFv⟩
def xF : Cut Machine := ⟨cF, SN, aF, fun _ mh => envN mh, bF⟩
def xFn : Cut Machine := ⟨cFn, SN, aFn, fun _ mh => envN mh, bFn⟩
def xFj : Cut Machine := ⟨cFj, SN, aFj, fun _ mh => envN mh, bFj⟩
def xFp : Cut Machine := ⟨cFp, SP cfg 10 [], aFp, fun _ mh => envP cfg 10 mh, bFp⟩
def xFc : Cut Machine := ⟨cFc, SC 11 13, aFc, fun _ mh => envC 11 13 mh, bFc⟩
def xR0 : Cut Machine := ⟨cR0, SF cfg, aR0, fun _ mh => envF cfg mh, bR0⟩
def xR1 : Cut Machine := ⟨cR1, SR3 cfg 28 29, aR1, fun _ mh => envR3 cfg 28 29 mh, bR1⟩
def xS0 : Cut Machine := ⟨cS0, SF cfg, aS0, fun _ mh => envF cfg mh, bS0⟩
def xS1 : Cut Machine := ⟨cS1, SR3 cfg 29 30, aS1, fun _ mh => envR3 cfg 29 30 mh, bS1⟩
def xT0 : Cut Machine := ⟨cT0, SF cfg, aT0, fun _ mh => envF cfg mh, bT0⟩
def xT1 : Cut Machine := ⟨cT1, SR3 cfg 6 7, aT1, fun _ mh => envR3 cfg 6 7 mh, bT1⟩
def xJ : Cut Machine := ⟨cJ, SF cfg, aJ, fun _ mh => envF cfg mh, bJ⟩
def xLv : Cut Machine := ⟨cLv, SP cfg 11 [], aLv, fun _ mh => envP cfg 11 mh, bLv⟩
def xL : Cut Machine := ⟨cL, SN, aL, fun _ mh => envN mh, bL⟩
def xLn : Cut Machine := ⟨cLn, SN, aLn, fun _ mh => envN mh, bLn⟩
def xLj : Cut Machine := ⟨cLj, SN, aLj, fun _ mh => envN mh, bLj⟩
def xLp : Cut Machine := ⟨cLp, SP cfg 10 [], aLp, fun _ mh => envP cfg 10 mh, bLp⟩
def xLc : Cut Machine := ⟨cLc, SC 13 11, aLc, fun _ mh => envC 13 11 mh, bLc⟩
def xEp : Cut Machine where
  pc := cEp
  S := SE cfg
  A := aEp
  env := fun m mh => envE cfg m mh
  budget := fun _ _ => 15

def vcPlan : Plan Machine zesuImage where
  cuts := [xE, xOut, xFv, xF, xFn, xFj, xFp, xFc, xR0, xR1, xS0, xS1, xT0, xT1, xJ, xLv, xL, xLn,
    xLj, xLp, xLc, xEp]
  fuel := 400
  leaves := fun pc =>
    if pc = entry then runE_leaves else if pc = cOut then runOut_leaves
    else if pc = cFv then runFv_leaves else if pc = cF then runF_leaves
    else if pc = cFn then runFn_leaves else if pc = cFj then runFj_leaves
    else if pc = cFp then runFp_leaves else if pc = cFc then runFc_leaves
    else if pc = cR0 then runR0_leaves else if pc = cR1 then runR1_leaves
    else if pc = cS0 then runS0_leaves else if pc = cS1 then runS1_leaves
    else if pc = cT0 then runT0_leaves else if pc = cT1 then runT1_leaves
    else if pc = cJ then runJ_leaves else if pc = cLv then runLv_leaves
    else if pc = cL then runL_leaves else if pc = cLn then runLn_leaves
    else if pc = cLj then runLj_leaves else if pc = cLp then runLp_leaves
    else if pc = cLc then runLc_leaves else if pc = cEp then runEp_leaves else []
  callee := fun _ => none
  Post := Post cfg

zesu_plan R11564 := vcPlan

zesu_auto R11564

end ZesuExec.Fn.MergeInPlace.C11564
