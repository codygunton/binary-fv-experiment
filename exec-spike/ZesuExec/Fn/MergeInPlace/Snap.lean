import ZesuExec.Fn.MergeInPlace.Spec

/-!
# `sort.block.mergeInPlace` copies: `Post` on Unicorn snapshots (contract rule (b))

A `Snap` holds what `tools/snap_post.py --kind merge|keyed` reads from a `zesu-snap/1` snapshot of
a copy: the registers at entry and exit, the exit `pc`, the ranges `A`, `B` (the `u64` pairs at
`a1`, `a2` in the entry memory), the items bytes `[0, 32·B.end)` at `a0` at entry and at exit,
the addresses of every changed byte and, for keyed copies, the `(ptr, len, bytes)` of each slice
the entry elements hold (its bytes from the entry memory).

`SnapOk fs key s` is `Post` on these values for a copy with frame size `fs` whose element order
is `lexLt` on `key s x` (`idKey`: the element itself; `snapSliceKey`: the bytes its leading slice
points to): the return (`pc` is `ra` with bit 0 clear, callee-saved registers kept), only bytes of
`items[A.start..B.end]` and of the frame changed, and `MergeOf`: the output elements
`[A.start, B.end)` a permutation of the input runs `A ++ B` and sorted by their keys; plus
`A.start ≤ A.end = B.start ≤ B.end` of `Pre`. Each copy's `post_snapshot` evaluates it on its
snapshots by `decide`.
-/

namespace ZesuExec.Fn.MergeInPlace
open ZesuExec

structure Snap where
  /-- `x1 … x31` at entry -/
  regs0 : List Nat
  /-- `x1 … x31` at the return -/
  regs1 : List Nat
  pc1 : Nat
  /-- `A = [aS, aE)`, `B = [bS, bE)` -/
  aS : Nat
  aE : Nat
  bS : Nat
  bE : Nat
  /-- the items `[0, bE)` at entry and at the return -/
  before : List Nat
  after : List Nat
  /-- every byte address whose value changed -/
  changed : List Nat
  /-- keyed copies: `(ptr, len, the len bytes at ptr)` of each slice in the entry elements -/
  keys : List (Nat × Nat × List Nat) := []

def Snap.r0 (s : Snap) (i : Nat) : Nat := s.regs0.getD (i - 1) 0
def Snap.r1 (s : Snap) (i : Nat) : Nat := s.regs1.getD (i - 1) 0

/-- Elements `[lo, hi)` of a byte list, as `Byte` lists. -/
def snapWin (bs : List Nat) (lo hi : Nat) : List (List Byte) :=
  (List.range' lo (hi - lo)).map fun e => (List.range 32).map fun o => BitVec.ofNat 8 (bs.getD (32 * e + o) 0)

/-- `Sorted id` (`Pairwise (leBy id)`) as a `Bool`. -/
def sortedB : List (List Byte) → Bool
  | [] => true
  | a :: l => l.all (fun b => !lexLt b a) && sortedB l

/-- Little-endian bytes as a number. -/
def leNat (bs : List Byte) : Nat := bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- The key of an element ordered by itself. -/
def idKey (_ : Snap) (x : List Byte) : Option (List Byte) := some x

/-- The key of an element whose first 16 bytes are a slice `{ptr, len}`: the slice's bytes. -/
def snapSliceKey (s : Snap) (x : List Byte) : Option (List Byte) :=
  let q := leNat (x.take 8); let n := leNat ((x.drop 8).take 8)
  (s.keys.find? fun k => k.1 == q && k.2.1 == n).map fun k => k.2.2.map (BitVec.ofNat 8)

def SnapOk (fs : Nat) (key : Snap → List Byte → Option (List Byte)) (s : Snap) : Bool :=
  let p := s.r0 10; let sp := s.r0 2; let out := snapWin s.after s.aS s.bE
  decide (s.aS ≤ s.aE) && s.aE == s.bS && decide (s.bS ≤ s.bE) &&
  s.before.length == 32 * s.bE && s.after.length == 32 * s.bE &&
  s.pc1 == s.r0 1 - s.r0 1 % 2 &&
  [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27].all (fun i => s.r1 i == s.r0 i) &&
  s.changed.all (fun x => (decide (p + 32 * s.aS ≤ x) && decide (x < p + 32 * s.bE)) ||
    (decide (sp - fs ≤ x) && decide (x < sp))) &&
  out.isPerm (snapWin s.before s.aS s.aE ++ snapWin s.before s.bS s.bE) &&
  match out.mapM (key s) with
  | some ks => sortedB ks
  | none => false

end ZesuExec.Fn.MergeInPlace
