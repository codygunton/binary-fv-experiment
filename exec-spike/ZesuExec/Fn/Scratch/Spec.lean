import ZesuExec.Fn.Alloc.Inv

/-!
# Contracts of `scratch_arena.free` and `scratch_arena.remap` (programme plan S13)

Draft, unreviewed (contract rule). Transcribed from `src/stateless/executor/scratch_arena.zig`:
a `ScratchArena` at `ctx = a0` holds `chunks` (the newest chunk or null) at offset 16; a chunk
header holds `cap` at 8 and `used` at 16 (header included, from the chunk's start). Both
functions act on the newest chunk only, and only when the buffer `[ptr, ptr + len)` ends at
`chunk + used` (the most recent allocation). Arithmetic is on 64-bit words, as in the code.

`free(ctx, ptr = a1, len = a2, alignment, ret_addr)`: if the buffer is the most recent
allocation, `used := ptr - chunk`.

`remap(ctx, ptr = a1, len = a2, alignment, new_len = a4, ret_addr)` returns `ptr` or null
(`resize` then `remap` of the source): no chunk, null; the most recent allocation, shrinking or
growing within `cap`: `used := ptr + new_len - chunk`, `ptr`; growing past `cap`: null; any other
buffer: `ptr` if `new_len ≤ len`, else null.

Both use 16 bytes of stack below `sp` when there is a chunk, and return like any function.
-/

namespace ZesuExec.Fn.Scratch
open ZesuExec

/-- The word at `a` (0 if unreadable). -/
def word (m : Machine) (a : Word) : Word := (m.load a 8).getD 0

/-- `ctx.chunks`. -/
def chunks (m : Machine) : Word := word m (m.reg 10 + 16)
/-- The newest chunk's `used`. -/
def used (m : Machine) : Word := word m (chunks m + 16)
/-- The newest chunk's `cap`. -/
def cap (m : Machine) : Word := word m (chunks m + 8)

/-- The `chunks` word is RAM and present. -/
def CtxOk (m : Machine) : Prop := RamRange (m.reg 10 + 16) 8 ∧ Present m (m.reg 10 + 16) 8

def FreePre (m : Machine) : Prop :=
  RetAligned m ∧ CtxOk m ∧
    (chunks m ≠ 0 → StackOk m 16 ∧ RamRange (chunks m + 16) 8 ∧ Present m (chunks m + 16) 8 ∧
      Fn.Disjoint (chunks m + 16, 8) (m.reg 2 - 16, 16))

def FreePost (m m' : Machine) : Prop :=
  Returns m m' ∧
    SameOutside (fun a => (chunks m ≠ 0 ∧ InRange (chunks m + 16) 8 a) ∨
      InRange (m.reg 2 - 16) 16 a) m m' ∧
    (chunks m ≠ 0 → word m' (chunks m + 16) =
      if m.reg 11 + m.reg 12 = chunks m + used m then m.reg 11 - chunks m else used m)

def RemapPre (m : Machine) : Prop :=
  RetAligned m ∧ CtxOk m ∧
    (chunks m ≠ 0 → StackOk m 16 ∧ RamRange (chunks m + 8) 16 ∧ Present m (chunks m + 8) 16 ∧
      Fn.Disjoint (chunks m + 8, 16) (m.reg 2 - 16, 16))

/-- `resize`'s answer and the new `used` (`none`: unchanged). -/
def remapOut (m : Machine) : Word × Option Word :=
  if chunks m = 0 then (0, none)
  else if m.reg 11 + m.reg 12 = chunks m + used m then
    if m.reg 14 ≤ m.reg 12 ∨ m.reg 11 + m.reg 14 ≤ chunks m + cap m then
      (m.reg 11, some (m.reg 11 + m.reg 14 - chunks m))
    else (0, none)
  else if m.reg 14 ≤ m.reg 12 then (m.reg 11, none) else (0, none)

def RemapPost (m m' : Machine) : Prop :=
  Returns m m' ∧ m'.reg 10 = (remapOut m).1 ∧
    SameOutside (fun a => (chunks m ≠ 0 ∧ InRange (chunks m + 16) 8 a) ∨
      InRange (m.reg 2 - 16) 16 a) m m' ∧
    (chunks m ≠ 0 → word m' (chunks m + 16) = ((remapOut m).2.getD (used m)))

end ZesuExec.Fn.Scratch
