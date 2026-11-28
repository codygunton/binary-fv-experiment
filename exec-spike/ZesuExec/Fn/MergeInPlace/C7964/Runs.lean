import ZesuExec.Fn.MergeInPlace.Cuts

/-!
# `sort.block.mergeInPlace__anon_7964` (`0x8004f388`, 507 instructions, 8 loops): copy data and runs

Elements are `[32]u8`, ordered by `std.mem.lessThan(u8, …)` on the element itself (`key = id`).
A 0x70-byte frame saving `s4`, `s3`, `s2`, `s1`, `s0`, `ra` at 0x40 … 0x68; each search copies
the compared elements into the frame at 0x20 (`s0-0x50`) and 0 (`s0-0x70`) and compares the
copies byte by byte.

Cut points: the map's loop heads and joins, plus `0x8004f43c` and `0x8004faf0` (each search's
load of its probe: the address `a0 + 32·curr + 32·half` has two index terms, so the cut makes the
probe a region) and the joins `0x8004f3f8`, `0x8004faac` after each comparison.
-/

namespace ZesuExec.Fn.MergeInPlace.C7964
open ZesuExec ZesuExec.Sym

def cfg : Cfg where
  entry := 0x8004f388
  fs := 0x70
  saved := [(0x40, 20), (0x48, 19), (0x50, 18), (0x58, 9), (0x60, 8), (0x68, 1)]
  kept := [21, 22, 23, 24, 25, 26, 27]
  key := fun _ x => x
  pre := fun _ => True

def entry : Nat := 0x8004f388
/-- outer loop head; `binaryFirst` on `B` begins -/
def cOut : Nat := 0x8004f3dc
/-- `binaryFirst`: loop latch (after a comparison) and head -/
def cFj : Nat := 0x8004f3f8
def cF : Nat := 0x8004f3fc
/-- `binaryFirst`: the probe's load -/
def cFp : Nat := 0x8004f43c
/-- `binaryFirst`: the byte comparison loop -/
def cFc : Nat := 0x8004f460
/-- the rotation: first reversal (`A`), second (`B[..mid]`), third (all) -/
def cR0 : Nat := 0x8004f4ac
def cR1 : Nat := 0x8004f4d0
def cS0 : Nat := 0x8004f69c
def cS1 : Nat := 0x8004f6c4
def cT0 : Nat := 0x8004f890
def cT1 : Nat := 0x8004f8ac
/-- after the rotation -/
def cJ : Nat := 0x8004fa78
/-- `binaryLast`: head, probe load, comparison, latch -/
def cL : Nat := 0x8004fab0
def cLp : Nat := 0x8004faf0
def cLc : Nat := 0x8004fb14
def cLj : Nat := 0x8004faac
/-- the epilogue -/
def cEp : Nat := 0x8004fb54

def cutPcs : List Nat :=
  [entry, cOut, cFj, cF, cFp, cFc, cR0, cR1, cS0, cS1, cT0, cT1, cJ, cL, cLp, cLc, cLj, cEp]

sym_run runE := run zesuImage cutPcs 400 entry (S0 cfg)
sym_run runOut := run zesuImage cutPcs 400 cOut SN
sym_run runFj := run zesuImage cutPcs 400 cFj SN
sym_run runF := run zesuImage cutPcs 400 cF (SP cfg 6 [])
sym_run runFp := run zesuImage cutPcs 400 cFp (SP cfg 20 [(30, .ptr 0 0x20)])
sym_run runFc := run zesuImage cutPcs 400 cFc (SC 31 30)
sym_run runR0 := run zesuImage cutPcs 400 cR0 SN
sym_run runR1 := run zesuImage cutPcs 400 cR1 (SR 28 29)
sym_run runS0 := run zesuImage cutPcs 400 cS0 SN
sym_run runS1 := run zesuImage cutPcs 400 cS1 (SR 29 30)
sym_run runT0 := run zesuImage cutPcs 400 cT0 SN
sym_run runT1 := run zesuImage cutPcs 400 cT1 (SR 6 7)
sym_run runJ := run zesuImage cutPcs 400 cJ SN
sym_run runL := run zesuImage cutPcs 400 cL (SP cfg 17 [])
sym_run runLp := run zesuImage cutPcs 400 cLp (SP cfg 18 [(28, .ptr 0 0x20)])
sym_run runLc := run zesuImage cutPcs 400 cLc (SC 29 28)
sym_run runLj := run zesuImage cutPcs 400 cLj SN
sym_run runEp := run zesuImage cutPcs 400 cEp (SE cfg)

end ZesuExec.Fn.MergeInPlace.C7964
