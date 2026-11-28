import ZesuExec.Fn.Alloc.Snap

/-!
# `scratch_arena.free` and `remap`: `Pre` and `Post` on Unicorn snapshots (contract rule (b))

The snapshots are `Alloc.Snap` values (`tools/snap.py --fn ScratchFree|ScratchRemap`, rendered by
`tools/snap_alloc.py`; `live` is empty): the registers, the exit `pc`, every changed byte and, at
entry and at exit, the `chunks` word at `a0 + 16` and, when it is not null, the chunk's `cap`
(at 8) and `used` (at 16) words. Arithmetic is on 64-bit words (`% 2 ^ 64`), comparisons
unsigned, as in `Fn/Scratch/Spec.lean`; a word the check needs and the snapshot lacks fails it.

`freeOk` and `remapOk` are `FreePre`/`FreePost` and `RemapPre`/`RemapPost` on these values:
`RetAligned`, `CtxOk`'s range, and with a chunk `StackOk`'s numeric part, the chunk words in RAM
and apart from the frame; `Returns`, every changed byte in the chunk's `used` word (with a
chunk) or the 16-byte frame, the new `used` and (`remap`) `a0` as `remapOut` gives them.
`Present` is not tested (the snapshot lists only the pages the run touches).
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
