import ZesuExec.Fn.Alloc.Snap
import ZesuExec.Fn.Scratch.AllocSpec

/-!
# `scratch_arena.free`, `remap` and `alloc`: `Pre` and `Post` on Unicorn snapshots (contract rule (b))

The snapshots are `Alloc.Snap` values (`tools/snap.py --fn ScratchFree|ScratchRemap|ScratchAlloc`,
rendered by `tools/snap_alloc.py`): the registers, the exit `pc`, every changed byte and, at entry
and at exit, the words the check reads. For `free` and `remap` (`live` is empty): the `chunks`
word at `a0 + 16` and, when it is not null, the chunk's `cap` (at 8) and `used` (at 16) words.
For `alloc`: `alt_fl_alloc`'s words (`Alloc.decodeB`), the arena's `child.vtable`, `chunks` and
`last_chunk_size` words (`a0 + 8`, `+ 16`, `+ 24`) and, when `chunks` is not null, the chunk's
`next`, `cap` and `used` words; `live` lists the child's live blocks (the chunk among them).
Arithmetic is on 64-bit words (`% 2 ^ 64`), comparisons unsigned, as in `Fn/Scratch/Spec.lean`;
a word the check needs and the snapshot lacks fails it.

`freeOk` and `remapOk` are `FreePre`/`FreePost` and `RemapPre`/`RemapPost` on these values:
`RetAligned`, `CtxOk`'s range, and with a chunk `StackOk`'s numeric part, the chunk words in RAM
and apart from the frame; `Returns`, every changed byte in the chunk's `used` word (with a
chunk) or the 16-byte frame, the new `used` and (`remap`) `a0` as `remapOut` gives them.
`saOk` is `AllocPreS Alloc.contract L` and `AllocPostS` (`Fn/Scratch/AllocSpec.lean`) on them,
with `Alloc.heapB` for `Heap` and `Alloc.Priv` by bytes (`arenaB`, `inLiveB`); `alignUp` is the
word function itself, so the check rounds as the contract does.
`Present` and `RodataLoaded` are not tested (the snapshot lists only the pages the run touches).
-/

namespace ZesuExec.Fn.Scratch
open ZesuExec.Fn.Alloc (Snap wordAt returnsB inFrameB ndisjB)

def wmod (x : Nat) : Nat := x % 2 ^ 64

def ramB (lo n : Nat) : Bool := Layout.ramLo ≤ lo && lo + n ≤ Layout.ramHi

/-- `RetAligned`, `CtxOk`'s range, and with a chunk the stack frame and the chunk words
`[ch + off, ch + off + n)` in RAM and apart from the frame. -/
def preB (s : Snap) (ch off n : Nat) : Bool :=
  let sp := s.r0 2
  (s.r0 1 - s.r0 1 % 2) % 4 == 0 && ramB (wmod (s.r0 10 + 16)) 8 &&
  (ch == 0 || (sp % 16 == 0 && Layout.ramLo + 16 ≤ sp && sp ≤ Layout.ramHi &&
    ramB (wmod (ch + off)) n && ndisjB (wmod (ch + off), n) (sp - 16, 16)))

/-- Every changed byte is in the chunk's `used` word (with a chunk) or the frame. -/
def changedB (s : Snap) (ch : Nat) : Bool :=
  s.changed.all fun a =>
    (ch != 0 && wmod (ch + 16) ≤ a && a < wmod (ch + 16) + 8) || inFrameB s a

/-- `remapOut` on numbers: `a0` and the new `used` (`none`: unchanged). -/
def remapOutB (ch u cap p n nl : Nat) : Nat × Option Nat :=
  if ch = 0 then (0, none)
  else if wmod (p + n) = wmod (ch + u) then
    if nl ≤ n ∨ wmod (p + nl) ≤ wmod (ch + cap) then (p, some (wmod (p + nl + 2 ^ 64 - ch)))
    else (0, none)
  else if nl ≤ n then (p, none) else (0, none)

/-- `FreePre` and `FreePost` on a snapshot of `scratch_arena.free`. -/
def freeOk (s : Snap) : Bool :=
  let p := s.r0 11; let n := s.r0 12
  match wordAt s.mem0 (wmod (s.r0 10 + 16)) with
  | none => false
  | some ch =>
    preB s ch 16 8 && returnsB s && changedB s ch &&
    (ch == 0 ||
      match wordAt s.mem0 (wmod (ch + 16)), wordAt s.mem1 (wmod (ch + 16)) with
      | some u, some u' =>
        u' == if wmod (p + n) = wmod (ch + u) then wmod (p + 2 ^ 64 - ch) else u
      | _, _ => false)

/-- `RemapPre` and `RemapPost` on a snapshot of `scratch_arena.remap`. -/
def remapOk (s : Snap) : Bool :=
  let p := s.r0 11; let n := s.r0 12; let nl := s.r0 14
  match wordAt s.mem0 (wmod (s.r0 10 + 16)) with
  | none => false
  | some ch =>
    preB s ch 8 16 && returnsB s && changedB s ch &&
    if ch = 0 then s.r1 10 == 0
    else
      match wordAt s.mem0 (wmod (ch + 8)), wordAt s.mem0 (wmod (ch + 16)),
        wordAt s.mem1 (wmod (ch + 16)) with
      | some cap, some u, some u' =>
        let o := remapOutB ch u cap p n nl
        s.r1 10 == o.1 && u' == o.2.getD u
      | _, _, _ => false

end ZesuExec.Fn.Scratch

/-! ## `scratch_arena.alloc` -/

namespace ZesuExec.Fn.Scratch
open ZesuExec.Fn.Alloc (Snap wordAt returnsB ndisjB heapB arenaB inLiveB privRangeB)

/-- `alignUp` on numbers: the word function of the contract. -/
def alignUpB (x k : Nat) : Nat := (alignUp (BitVec.ofNat 64 x) (BitVec.ofNat 64 k)).toNat

/-- `newSize` on numbers (`len`, log2 alignment, `last_chunk_size`). -/
def newSizeB (n al last : Nat) : Nat :=
  if last = 0 then max (n + 2 ^ al + 23) 4096 else max (n + 2 ^ al + 23) (2 * last)

/-- No byte of `[lo, lo + n)` is in `Alloc.Priv L` (the allocator's arena minus the live blocks). -/
def notPrivB (L : List (Nat × Nat)) (lo n : Nat) : Bool :=
  (List.range n).all fun i => !arenaB (wmod (lo + i)) || inLiveB L (wmod (lo + i))

def inB (lo n a : Nat) : Bool := lo ≤ a && a < lo + n

/-- `AllocPreS Alloc.contract L` without `RodataLoaded` and `Present`; `vt`, `ch`, `last`, `cp`,
`u`: the `child.vtable`, `chunks` and `last_chunk_size` words, the chunk's `cap` and `used`. -/
def saPreB (s : Snap) (vt ch last cp u : Nat) : Bool :=
  let ctx := s.r0 10; let n := s.r0 11; let al := s.r0 12; let sp := s.r0 2; let L := s.live
  (s.r0 1 - s.r0 1 % 2) % 4 == 0 &&
  sp % 16 == 0 && Layout.ramLo + 80 ≤ sp && sp ≤ Layout.ramHi &&
  ramB ctx 32 && vt == allocVt && al < 64 && n + 2 ^ al + 23 ≤ 2 ^ 62 && last < 2 ^ 62 &&
  ndisjB (ctx, 32) (sp - 80, 80) && heapB L s.mem0 && notPrivB L ctx 32 && notPrivB L (sp - 80) 80 &&
  (ch == 0 || (ramB ch 24 && u ≤ cp && ch + cp ≤ Layout.ramHi &&
    ndisjB (wmod (ch + 8), 16) (ctx, 32) && ndisjB (wmod (ch + 8), 16) (sp - 80, 80) &&
    notPrivB L (ch + 8) 16))

/-- `Fits`. -/
def fitsB (n al ch cp u : Nat) : Bool :=
  ch != 0 && wmod (alignUpB (wmod (ch + u)) al + n) ≤ wmod (ch + cp)

/-- `AllocPostS`'s fast-path clause. -/
def fastB (s : Snap) (ch u : Nat) : Bool :=
  let n := s.r0 11; let r := s.r1 10; let sp := s.r0 2
  match wordAt s.mem1 (wmod (ch + 16)) with
  | some u' =>
    r == alignUpB (wmod (ch + u)) (s.r0 12) && u' == wmod (r + n + 2 ^ 64 - ch) &&
    s.changed.all (fun a => inB (wmod (ch + 16)) 8 a || inB (sp - 64) 64 a) && heapB s.live s.mem1
  | none => false

/-- `AllocPostS`'s slow-path clause: the frame condition and `SlowOut` (the new chunk `b` is the
`chunks` word at exit). -/
def slowB (s : Snap) (ch last : Nat) : Bool :=
  let ctx := s.r0 10; let n := s.r0 11; let al := s.r0 12; let r := s.r1 10; let sp := s.r0 2
  let L := s.live; let ns := newSizeB n al last
  s.changed.all (fun a => (arenaB a && !inLiveB L a) || inB (sp - 80) 80 a || inB (wmod (ctx + 16)) 16 a) &&
  ((r == 0 && heapB L s.mem1) ||
    match wordAt s.mem1 (wmod (ctx + 16)), wordAt s.mem1 (wmod (ctx + 24)) with
    | some b, some last' =>
      match wordAt s.mem1 b, wordAt s.mem1 (wmod (b + 8)), wordAt s.mem1 (wmod (b + 16)) with
      | some nx, some cp', some u' =>
        b != 0 && heapB (L ++ [(b, ns)]) s.mem1 && ramB b ns && privRangeB L b ns &&
        last' == ns && nx == ch && cp' == ns && r == alignUpB (wmod (b + 24)) al &&
        u' == wmod (r + n + 2 ^ 64 - b)
      | _, _, _ => false
    | _, _ => false)

/-- `AllocPreS Alloc.contract s.live` and `AllocPostS` on a snapshot of `scratch_arena.alloc`. -/
def saOk (s : Snap) : Bool :=
  let ctx := s.r0 10
  match wordAt s.mem0 (wmod (ctx + 8)), wordAt s.mem0 (wmod (ctx + 16)),
    wordAt s.mem0 (wmod (ctx + 24)) with
  | some vt, some ch, some last =>
    let cu := if ch = 0 then some (0, 0) else
      match wordAt s.mem0 (wmod (ch + 8)), wordAt s.mem0 (wmod (ch + 16)) with
      | some cp, some u => some (cp, u)
      | _, _ => none
    match cu with
    | some (cp, u) =>
      saPreB s vt ch last cp u && returnsB s &&
      if fitsB (s.r0 11) (s.r0 12) ch cp u then fastB s ch u else slowB s ch last
    | none => false
  | _, _, _ => false

end ZesuExec.Fn.Scratch
