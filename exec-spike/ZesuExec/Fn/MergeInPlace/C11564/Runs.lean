import ZesuExec.Fn.MergeInPlace.Cuts

/-!
# `sort.block.mergeInPlace__anon_11564` (`0x80098ddc`, 602 instructions, 8 loops): copy data and runs

Elements are 32 bytes whose first 16 are a byte slice (`ptr`, `len`); the order is
`std.mem.lessThan(u8, …)` on the slices (`key m x` = the bytes the slice points to). A 0x110-byte
frame saving `ra`, `s0`…`s11` at 0x108 … 0xa8; the body spills to the frame (`s0-0xb0` …
`s0-0x108`) and uses `ra` and `s1`…`s11` as scratch.

Cut points: the map's loop heads and joins, plus the loads whose address has two index terms
(each search's probe `items + 32·curr + 32·half`) or a spilled base (`items + 32·as`, the value
of `binaryFirst` and `binaryLast`).
-/

namespace ZesuExec.Fn.MergeInPlace.C11564
open ZesuExec ZesuExec.Sym

/-- The frame only (`sp`, `s0`). -/
def SF (fs : Nat) : SState := entryState (ovL [(2, .ptr 0 0), (8, .ptr 0 fs)]) [frameR fs] []
/-- A swap with spills: the two elements and the frame. -/
def SR3 (fs lo hi : Nat) : SState :=
  entryState (ovL [(lo, .ptr 0 15), (hi, .ptr 1 16), (2, .ptr 2 0), (8, .ptr 2 fs)])
    [elemW, elemW, frameR fs] []

def fs : Nat := 0x110
def knownE11 : List Write :=
  [(0xa8, 27), (0xb0, 26), (0xb8, 25), (0xc0, 24), (0xc8, 23), (0xd0, 22), (0xd8, 21), (0xe0, 20),
   (0xe8, 19), (0xf0, 18), (0xf8, 9), (0x100, 8), (0x108, 1)].map fun s => ⟨0, s.1, 8, .var (32 + s.2)⟩
def SE11 : SState := entryState (ovL [(2, .ptr 0 0)]) [frameR fs] knownE11
def S011 : SState :=
  entryState (ovL [(11, .ptr 0 0), (12, .ptr 1 0), (2, .ptr 2 fs)]) [rangeR, rangeR, frameR fs] []
def SP11 (r : Nat) : SState :=
  entryState (ovL [(2, .ptr 0 0), (8, .ptr 0 fs), (r, .ptr 1 0)]) [frameR fs, elemR] []

def entry : Nat := 0x80098ddc
def cOut : Nat := 0x80098e60
def cFv : Nat := 0x80098e78
def cF : Nat := 0x80098ea8
/-- `binaryFirst`: the length comparison after an equal common prefix, and the loop latch -/
def cFn : Nat := 0x80098e8c
def cFj : Nat := 0x80098ea4
def cFp : Nat := 0x80098ec0
def cFc : Nat := 0x80098ee0
def cR0 : Nat := 0x80098f2c
def cR1 : Nat := 0x80098f78
def cS0 : Nat := 0x80099188
def cS1 : Nat := 0x800991d8
def cT0 : Nat := 0x800993e8
def cT1 : Nat := 0x8009941c
def cJ : Nat := 0x80099634
def cLv : Nat := 0x80099668
def cL : Nat := 0x8009968c
/-- `binaryLast`: the length comparison and the loop latch -/
def cLn : Nat := 0x800996f8
def cLj : Nat := 0x80099688
def cLp : Nat := 0x800996a4
def cLc : Nat := 0x800996c4
def cEp : Nat := 0x80099708
def cutPcs : List Nat :=
  [entry, cOut, cFv, cF, cFn, cFj, cFp, cFc, cR0, cR1, cS0, cS1, cT0, cT1, cJ, cLv, cL, cLn, cLj,
    cLp, cLc, cEp]

sym_run runE := run zesuImage cutPcs 400 entry S011
sym_run runOut := run zesuImage cutPcs 400 cOut (SF fs)
sym_run runFv := run zesuImage cutPcs 400 cFv (SP11 11)
sym_run runF := run zesuImage cutPcs 400 cF SN
sym_run runFp := run zesuImage cutPcs 400 cFp (SP11 10)
sym_run runFc := run zesuImage cutPcs 400 cFc (SC 11 13)
sym_run runFn := run zesuImage cutPcs 400 cFn SN
sym_run runFj := run zesuImage cutPcs 400 cFj SN
sym_run runR0 := run zesuImage cutPcs 400 cR0 (SF fs)
sym_run runR1 := run zesuImage cutPcs 400 cR1 (SR3 fs 28 29)
sym_run runS0 := run zesuImage cutPcs 400 cS0 (SF fs)
sym_run runS1 := run zesuImage cutPcs 400 cS1 (SR3 fs 29 30)
sym_run runT0 := run zesuImage cutPcs 400 cT0 (SF fs)
sym_run runT1 := run zesuImage cutPcs 400 cT1 (SR3 fs 6 7)
sym_run runJ := run zesuImage cutPcs 400 cJ (SF fs)
sym_run runLv := run zesuImage cutPcs 400 cLv (SP11 11)
sym_run runL := run zesuImage cutPcs 400 cL SN
sym_run runLp := run zesuImage cutPcs 400 cLp (SP11 10)
sym_run runLc := run zesuImage cutPcs 400 cLc (SC 13 11)
sym_run runLn := run zesuImage cutPcs 400 cLn SN
sym_run runLj := run zesuImage cutPcs 400 cLj SN
sym_run runEp := run zesuImage cutPcs 400 cEp SE11

end ZesuExec.Fn.MergeInPlace.C11564
