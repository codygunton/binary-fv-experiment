import ZesuExec.Fn.SszRoot.Model
import ZesuExec.Fn.Sha256.Spec

/-!
# `ssz_output.sparseRoot` (`0x80042c0c`) and `ssz_output.progressiveRootAt` (`0x80042b2c`):
contracts

Drafted from the code (`llvm-objdump -d -M no-aliases` of `build/stock-zisk/zesu-zisk.elf`,
`0x80042b2c`–`0x80042da4`) and `ssz_output.zig` lines 41-166, unreviewed (`map/reviews.json`,
`STATEMENTS.md` S15). Both take the result pointer in `a0` (32 bytes written), the chunk pointer
in `a1` (`len` chunks of 32 bytes), `len` in `a2` and the depth in `a3`.

`sparseRoot` (frame `0x120`, `ra`, `s0`–`s5` saved): `a3 & 0xff = 0` returns the first chunk
(`len ≥ 1`, copied through the frame) or the zero chunk at `0x801154c0`; else `s4 = a3 - 1` (not
masked), `half = 1 << (s4 mod 64)`, the left root of `min(len, half)` chunks into the frame by a
recursive call at depth `s4`, the right root either `ZERO_HASHES[s4 & 0xff]` (rodata
`0x80113728 + 32 (s4 & 0xff)`, no bounds check) copied to the frame or a recursive call on the
chunks from `half`, both roots copied to a 64-byte block in the frame, `zkvm_sha256(block, 64,
frame)`, the 32 result bytes copied to `a0`.

`progressiveRootAt` (frame `0xa0`): `len = 0` writes 32 zero bytes; else `n = min(1 << (a3 mod
64), len)`, `sparseRoot(frame + 0x28, a1, n, a3)`, `progressiveRootAt(frame + 0x48, a1 + 32 n,
len - n, a3 + 2)` (not masked), `zkvm_sha256(frame + 0x28, 64, frame + 8)`, the result copied to
`a0`.

`Pre` (each): rodata loaded; the stack the recursion needs (`sparseStack`, `progStack`: frames
nest down to a `zkvm_sha256` frame) present in RAM below `sp`, 16-aligned; return address aligned;
the depth bounds (`sparseRoot`: `a3 ≤ 26`, the size of `ZERO_HASHES`; `progressiveRootAt`:
`progFits len a3`, every `sparseRoot` depth it asks is at most 26); the chunks readable; the
result, `zkvm_sha256`'s bump words and the memcpy staging word present RAM; stack, result, bump
words, staging word and chunks pairwise disjoint.

`Post` (each): return (`Returns`); the 32 bytes at `a0` are the model's root of the chunks;
memory changed only in the stack below `sp`, the result, the bump words and the staging word.
-/

namespace ZesuExec.Fn.SszRoot
open ZesuExec ZesuExec.Machine ZesuExec.Fn

def sparseEntry : Nat := 0x80042c0c
def progEntry : Nat := 0x80042b2c

/-- `zkvm_sha256` on 64 bytes: its budget `Sha256.bound 64`. -/
def shaCost : Nat := 210

/-- Stack `sparseRoot` at depth `d` uses below `sp`: `d + 1` frames of `0x120` and a
`zkvm_sha256` frame. -/
def sparseStack (d : Nat) : Nat := 0x120 * (d + 1) + Sha256.frameSize

/-- Instructions of `sparseRoot` at depth `d` on `n` chunks (the leaves' step counts: entry 25,
after the left call 1 then 36 (zero right half) or 9 then 23 (right call), `zkvm_sha256`
`shaCost`, return 17). -/
def sparseCost : Nat → Nat → Nat
  | 0, _ => 42
  | d + 1, n =>
    25 + sparseCost d (min n (2 ^ d)) +
      (if n ≤ 2 ^ d then 1 + 36 + shaCost + 17 else 9 + sparseCost d (n - 2 ^ d) + 23 + shaCost + 17)

/-- Stack `progressiveRootAt` on `n` nodes at depth `d` uses below `sp`. -/
def progStack (n d : Nat) : Nat :=
  if n = 0 then 0xa0 else 0xa0 + max (sparseStack d) (progStack (n - 2 ^ d) (d + 2))
termination_by n
decreasing_by
  have : 0 < 2 ^ d := Nat.two_pow_pos d
  omega

/-- Instructions of `progressiveRootAt` on `n` nodes at depth `d` (entry 24 / 22, after
`sparseRoot` 7, after the recursive call 5, after `zkvm_sha256` 18). -/
def progCost (n d : Nat) : Nat :=
  if n = 0 then 24
  else 22 + sparseCost d (min n (2 ^ d)) + 7 + progCost (n - 2 ^ d) (d + 2) + 5 + shaCost + 18
termination_by n
decreasing_by
  have : 0 < 2 ^ d := Nat.two_pow_pos d
  omega

/-- The `n` chunks of 32 bytes at `a` (absent bytes read as 0). -/
def chunksOf (m : Machine) (a : Word) (n : Nat) : List (List Byte) :=
  (List.range n).map fun i => (List.range 32).map fun j =>
    (m.mem (a + BitVec.ofNat 64 (32 * i + j))).getD 0

/-! ## Arguments -/

abbrev outOf (m : Machine) : Word := m.reg 10
abbrev chunkPtr (m : Machine) : Word := m.reg 11
abbrev lenOf (m : Machine) : Nat := (m.reg 12).toNat
abbrev depthOf (m : Machine) : Nat := (m.reg 13).toNat

def outR (m : Machine) : Word × Nat := (outOf m, 32)
def chunkR (m : Machine) : Word × Nat := (chunkPtr m, 32 * lenOf m)

/-- The memory both functions and their callees may write, for a stack of `need` bytes. -/
def WrittenN (need : Nat) (m : Machine) (a : Word) : Prop :=
  InRange (m.reg 2 - BitVec.ofNat 64 need) need a ∨ InRange (outOf m) 32 a ∨
    InRange (BitVec.ofNat 64 Sha256.bump) 16 a ∨ InRange (BitVec.ofNat 64 Layout.extraParams) 8 a

def PreN (need : Nat) (m : Machine) : Prop :=
  RodataLoaded zesuImage m ∧ StackOk m need ∧ RetAligned m ∧
  srcOk m.mem (chunkPtr m).toNat (32 * lenOf m) = true ∧
  dstOk m.mem (outOf m).toNat 32 = true ∧ dstOk m.mem Sha256.bump 16 = true ∧
  dstOk m.mem Layout.extraParams 8 = true ∧
  [(m.reg 2 - BitVec.ofNat 64 need, need), outR m, Sha256.bumpR, Sha256.stageR, chunkR m].Pairwise
    Disjoint

def PostN (need : Nat) (root : List Byte) (m m' : Machine) : Prop :=
  Returns m m' ∧ BytesAt m' (outOf m) root ∧ SameOutside (WrittenN need m) m m'

/-! ## `sparseRoot` -/

def sparseNeed (m : Machine) : Nat := sparseStack (depthOf m)

def SparsePre (m : Machine) : Prop := depthOf m ≤ 26 ∧ PreN (sparseNeed m) m

def SparsePost (m m' : Machine) : Prop :=
  PostN (sparseNeed m) (sparseRoot (chunksOf m (chunkPtr m) (lenOf m)) (depthOf m)) m m'

/-! ## `progressiveRootAt` -/

def progNeed (m : Machine) : Nat := progStack (lenOf m) (depthOf m)

def ProgPre (m : Machine) : Prop := progFits (lenOf m) (depthOf m) = true ∧ PreN (progNeed m) m

def ProgPost (m m' : Machine) : Prop :=
  PostN (progNeed m) (progressiveRootAt (chunksOf m (chunkPtr m) (lenOf m)) (depthOf m)) m m'

/-- The `zkvm_sha256` contract the proofs use (`Fn/Sha256/Proof.lean`: `sha256_spec 64`). -/
def ShaSpec : Prop :=
  Spec zesuImage Sha256.entry (Sha256.bound 64)
    (fun m => Sha256.Pre m ∧ (m.reg 11).toNat = 64) Sha256.Post

end ZesuExec.Fn.SszRoot
