import ZesuExec.Fn.Alloc.Inv

/-!
# `alloc` and `free`: `Post` on Unicorn snapshots (contract rule (b))

A `Snap` holds what `tools/snap_alloc.py` reads from a `zesu-snap/1` snapshot of `alloc` or
`free` (`tools/snap.py --fn Alloc|Free`): the registers at entry and exit, the exit `pc`, the
words of the allocator's memory that `Decode` reads (the 22 head cells, `HEAP_POS`, `HEAP_TOP`
and the first word of every free block), at entry and at exit, the address of every changed
byte, and the live blocks `L` of the input.

`decodeB` recovers the abstract state from those words: the bump pointer and, per class, the
chain from its head cell (a missing word or a chain longer than `fuel` fails). `goodB L st` is
`Good L st` with `HEAP_TOP = heapTop`. `allocOk` and `freeOk` are `Pre` and `Post` on these values:
`Pre`'s numeric conditions and `Heap L` at entry; `Returns` (`pc` is `ra` with bit 0 clear,
callee-saved registers kept); every changed byte in `Priv L` (for `free`: or in the freed block)
or in the 16-byte frame; and `Heap` at exit: for `alloc`, null with `Heap L`, or a block of `len`
bytes in RAM and in `Priv L` with `Heap (L ++ [(ptr, len)])`; for `free`,
`Heap (L.erase (ptr, len))`. `Present` is not tested (the snapshot lists only the pages the
run touches). Each `post_snapshot` evaluates them by `decide`.
-/

namespace ZesuExec.Fn.Alloc

structure Snap where
  /-- `x1 … x31` at entry and at the return -/
  regs0 : List Nat
  regs1 : List Nat
  pc1 : Nat
  /-- `(address, word)`: the words `Decode` reads, at entry and at the return -/
  mem0 : List (Nat × Nat)
  mem1 : List (Nat × Nat)
  /-- every byte address whose value changed -/
  changed : List Nat
  /-- the live blocks `L` -/
  live : List (Nat × Nat)

def Snap.r0 (s : Snap) (i : Nat) : Nat := s.regs0.getD (i - 1) 0
def Snap.r1 (s : Snap) (i : Nat) : Nat := s.regs1.getD (i - 1) 0

def wordAt (mem : List (Nat × Nat)) (a : Nat) : Option Nat := mem.lookup a

/-- The chain from cell `c`: the word at `c` is the first block, the first word of a block the
next; `none` when a word is missing or the chain is longer than `fuel`. -/
def chainB (mem : List (Nat × Nat)) : Nat → Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, c => do
    let p ← wordAt mem c
    if p = 0 then pure [] else return p :: (← chainB mem fuel p)

/-- `HEAP_POS` and the 22 chains, with `HEAP_TOP = heapTop`. -/
def decodeB (mem : List (Nat × Nat)) : Option (Nat × List (List Nat)) := do
  let pos ← wordAt mem posAddr
  let top ← wordAt mem topAddr
  guard (top = heapTop)
  let fl ← (List.range 22).mapM fun k => chainB mem 64 (flBase + 8 * k)
  return (pos, fl)

def ndisjB (a b : Nat × Nat) : Bool := a.1 + a.2 ≤ b.1 || b.1 + b.2 ≤ a.1

def pairwiseB : List (Nat × Nat) → Bool
  | [] => true
  | b :: bs => bs.all (ndisjB b) && pairwiseB bs

/-- `Good L st` on a decoded state. -/
def goodB (L : List (Nat × Nat)) (st : Nat × List (List Nat)) : Bool :=
  let free := (List.range 22).flatMap fun k => (st.2.getD k []).map fun p => (p, classBytes k)
  let bs := free ++ L.map fun b => (b.1, cap b.2)
  heapLo ≤ st.1 && st.1 ≤ Layout.ramHi && L.all (0 < ·.2) &&
    bs.all (fun b => heapLo ≤ b.1 && b.1 + b.2 ≤ st.1 && b.1 + b.2 ≤ heapTop) && pairwiseB bs

def heapB (L : List (Nat × Nat)) (mem : List (Nat × Nat)) : Bool :=
  match decodeB mem with
  | some st => goodB L st
  | none => false

def arenaB (a : Nat) : Bool :=
  (flBase ≤ a && a < flBase + 176) || (posAddr ≤ a && a < heapTop)

def inLiveB (L : List (Nat × Nat)) (a : Nat) : Bool := L.any fun b => b.1 ≤ a && a < b.1 + b.2

/-- `[lo, lo + n)` lies in `Priv L`: in the heap part of the arena and apart from every live
block. -/
def privRangeB (L : List (Nat × Nat)) (lo n : Nat) : Bool :=
  posAddr ≤ lo && lo + n ≤ heapTop && L.all fun b => ndisjB (lo, n) b

/-- `Returns`: `pc` is `ra` with bit 0 clear, `sp`, `s0`–`s11` kept. -/
def returnsB (s : Snap) : Bool :=
  s.pc1 == s.r0 1 - s.r0 1 % 2 &&
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27].all fun i => s.r1 i == s.r0 i

def inFrameB (s : Snap) (a : Nat) : Bool := s.r0 2 - 16 ≤ a && a < s.r0 2

/-- `AllocPre` and `AllocPost` on a snapshot of `alloc`. -/
def allocOk (s : Snap) : Bool :=
  let n := s.r0 11; let r := s.r1 10; let L := s.live
  -- Pre
  0 < n && n < 2 ^ 63 && s.r0 12 ≤ 4 && heapB L s.mem0 &&
  -- Post
  returnsB s &&
  s.changed.all (fun a => (arenaB a && !inLiveB L a) || inFrameB s a) &&
  ((r == 0 && heapB L s.mem1) ||
   (r != 0 && heapB (L ++ [(r, n)]) s.mem1 && Layout.ramLo ≤ r && r + n ≤ Layout.ramHi &&
     privRangeB L r n))

/-- `FreePre` and `FreePost` on a snapshot of `free`. -/
def freeOk (s : Snap) : Bool :=
  let p := s.r0 11; let n := s.r0 12; let al := s.r0 13; let L := s.live
  -- Pre
  L.contains (p, n) && 0 < n && n < 2 ^ 63 && al ≤ 4 && (al ≤ 3 || 8 < n) && heapB L s.mem0 &&
  ndisjB (s.r0 2 - 16, 16) (p, n) &&
  -- Post
  returnsB s &&
  s.changed.all (fun a => (arenaB a && !inLiveB L a) || (p ≤ a && a < p + n) || inFrameB s a) &&
  heapB (L.erase (p, n)) s.mem1

end ZesuExec.Fn.Alloc
