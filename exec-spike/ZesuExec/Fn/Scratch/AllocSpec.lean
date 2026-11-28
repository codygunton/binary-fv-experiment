import ZesuExec.Fn.Scratch.Spec
import ZesuExec.Fn.Alloc.Contract

/-!
# Contract of `scratch_arena.alloc` (programme plan S13)

Draft, unreviewed (contract rule). Transcribed from `src/stateless/executor/scratch_arena.zig`
and the code at `0x800db7a4`: `alloc(ctx = a0, len = a1, log2 alignment = a2, ret_addr = a3)` on a
`ScratchArena` at `ctx` (`child = {ptr, vtable}` at 0 and 8, `chunks` at 16, `last_chunk_size`
at 24; a chunk header holds `next` at 0, `cap` at 8, `used` at 16, from the chunk's start).

Fast path: when there is a newest chunk and `alignUp(chunk + used) + len ≤ chunk + cap` (64-bit
words, unsigned), the answer is `alignUp(chunk + used)` and `used` becomes its end minus `chunk`.
Otherwise a new chunk of `newSize` bytes (`max(len + 2^align + 23, 4096)` when
`last_chunk_size = 0`, else `max(len + 2^align + 23, 2 · last_chunk_size)`) is requested from the
child allocator, `alt_fl_alloc` (`child.vtable` is `0x801136d8`, its vtable in rodata), with
alignment 8 and the caller's `ret_addr`. Null from the child gives null. A block `b` becomes the
newest chunk (`next` = the old `chunks`, `cap = newSize`, `chunks = b`,
`last_chunk_size = newSize`) and the answer is `alignUp(b + 24)` with `used` at its end.

`Pre` bounds the request so that no address computation wraps: `len + 2^align + 23 ≤ 2^62`,
`align < 64`, `last_chunk_size < 2^62`, the newest chunk's `[chunk, chunk + cap)` in RAM with
`used ≤ cap`. It names the child's allocator state (`AllocContract`, `Heap L`); the arena, the
newest chunk's `cap`/`used` words and the 80 bytes below `sp` (own frame 64, child's 16) are
outside `Priv L`. `Post`, besides `Returns`: on the fast path only `used` and the frame change and
`Heap L` holds; otherwise changes stay in `Priv L`, the 80 bytes below `sp` and
`ctx.chunks`/`last_chunk_size`, and either the answer is null with `Heap L`, or the child's new
live block `b` of `newSize` bytes (from `Priv L`, in RAM) carries the new header and the answer.
-/

namespace ZesuExec.Fn.Scratch
open ZesuExec

/-- `alt_fl_alloc`'s vtable (rodata). -/
def allocVt : Nat := 0x801136d8

/-- `ctx.last_chunk_size`. -/
def lastSize (m : Machine) : Word := word m (m.reg 10 + 24)

/-- `~(2^k - 1)`, from `-1 << k` as the code computes it. -/
def maskW (k : Word) : Word := (-1 : Word) <<< (k.toNat % 64)

/-- `x` rounded up to a multiple of `2^k`, as the code computes it. -/
def alignUp (x k : Word) : Word := (x + (maskW k ^^^ -1)) &&& maskW k

/-- The request with its worst-case padding and a header: `len + 2^align + 23`. -/
def needN (m : Machine) : Nat := (m.reg 11).toNat + 2 ^ (m.reg 12).toNat + 23

/-- The size of a new chunk. -/
def newSize (m : Machine) : Nat :=
  if lastSize m = 0 then max (needN m) 4096 else max (needN m) (2 * (lastSize m).toNat)

/-- The fast path applies: the request fits in the newest chunk. -/
def Fits (m : Machine) : Prop :=
  chunks m ≠ 0 ∧ alignUp (chunks m + used m) (m.reg 12) + m.reg 11 ≤ chunks m + cap m

def AllocPreS (A : AllocContract zesuImage) (L : List (Word × Nat)) (m : Machine) : Prop :=
  RodataLoaded zesuImage m ∧ RetAligned m ∧ StackOk m 80 ∧
  RamRange (m.reg 10) 32 ∧ Present m (m.reg 10) 32 ∧
  m.load (m.reg 10 + 8) 8 = some (BitVec.ofNat 64 allocVt) ∧
  (m.reg 12).toNat < 64 ∧ needN m ≤ 2 ^ 62 ∧ (lastSize m).toNat < 2 ^ 62 ∧
  Fn.Disjoint (m.reg 10, 32) (m.reg 2 - 80, 80) ∧ A.Heap L m ∧
  (∀ a, InRange (m.reg 10) 32 a ∨ InRange (m.reg 2 - 80) 80 a → ¬ A.Priv L a) ∧
  (chunks m ≠ 0 → RamRange (chunks m) 24 ∧ Present m (chunks m + 8) 16 ∧ used m ≤ cap m ∧
    (chunks m).toNat + (cap m).toNat ≤ Layout.ramHi ∧
    Fn.Disjoint (chunks m + 8, 16) (m.reg 10, 32) ∧
    Fn.Disjoint (chunks m + 8, 16) (m.reg 2 - 80, 80) ∧
    ∀ a, InRange (chunks m + 8) 16 a → ¬ A.Priv L a)

/-- After a new chunk was requested. -/
def SlowOut (A : AllocContract zesuImage) (L : List (Word × Nat)) (m m' : Machine) : Prop :=
  (m'.reg 10 = 0 ∧ A.Heap L m') ∨
  ∃ b : Word, b ≠ 0 ∧ A.Heap (L ++ [(b, newSize m)]) m' ∧ RamRange b (newSize m) ∧
    (∀ a, InRange b (newSize m) a → A.Priv L a) ∧
    word m' (m.reg 10 + 16) = b ∧ word m' (m.reg 10 + 24) = BitVec.ofNat 64 (newSize m) ∧
    word m' b = chunks m ∧ word m' (b + 8) = BitVec.ofNat 64 (newSize m) ∧
    m'.reg 10 = alignUp (b + 24) (m.reg 12) ∧ word m' (b + 16) = m'.reg 10 + m.reg 11 - b

def AllocPostS (A : AllocContract zesuImage) (L : List (Word × Nat)) (m m' : Machine) : Prop :=
  Returns m m' ∧
  (Fits m → m'.reg 10 = alignUp (chunks m + used m) (m.reg 12) ∧
    word m' (chunks m + 16) = m'.reg 10 + m.reg 11 - chunks m ∧
    SameOutside (fun a => InRange (chunks m + 16) 8 a ∨ InRange (m.reg 2 - 64) 64 a) m m' ∧
    A.Heap L m') ∧
  (¬ Fits m →
    SameOutside (fun a => A.Priv L a ∨ InRange (m.reg 2 - 80) 80 a ∨
      InRange (m.reg 10 + 16) 16 a) m m' ∧ SlowOut A L m m')

end ZesuExec.Fn.Scratch
