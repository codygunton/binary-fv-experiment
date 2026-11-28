import ZesuExec.Fn.Common
import ZesuExec.Fn.SvcSteps

/-!
# `zkvm_sha256` (`0x800ea180`, 242 instructions): contract

Drafted from the code (ZisK's `ziskos` `zkvm_sha256(data = a0, len = a1, out = a2)`), unreviewed
(`map/reviews.json`, `STATEMENTS.md` S14):

* prologue: a `0xe0`-byte frame below `sp`, `s0`–`s11` and `ra` saved; the two words of its bump
  allocator at `0xa05340b8` are set to `0xa05340c8` and `0xa0d340c8`;
* the initial hash value (32 bytes of rodata at `0x801153e0`) is copied to `sp' + 8`
  (`csrs 0x813`, immediate count), `sp' = sp - 0xe0`;
* every whole 64-byte block of the input is compressed into it with CSR `0x805` (parameter block
  at `sp' + 0x68` and the block copied to `sp' + 0x28` by CSR `0x813` when `data` is not
  8-aligned; parameter block at `sp' + 0x28` and the block read in place when it is);
* the tail: `sp' + 0x28 .. + 0x68` zeroed (CSR `0x816`, immediate count), the remaining bytes
  copied there (CSR `0x813`, register count: the count is staged at `Layout.extraParams`), `0x80`
  after them, the bit length big-endian in the last 8 bytes, one or two more compressions;
* the eight state words written big-endian to `out`; `a0 = 0`.

`Pre`: rodata loaded; `0xe0` bytes of stack; return address aligned; the input is empty or present
readable memory; `out`, the bump words and the staging word are present RAM; the frame, `out`,
the bump words and the staging word are pairwise disjoint, and a nonempty input is disjoint from
the frame, the bump words and the staging word.

`Post`: return; `a0 = 0`; the 32 bytes at `out` are `Sha256.hash` of the input; the bump words;
memory changed only in the frame, `out`, the bump words and the staging word.
-/

namespace ZesuExec.Fn.Sha256
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym

def entry : Nat := 0x800ea180
/-- Size of the frame below `sp`. -/
def frameSize : Nat := 0xe0
/-- The two words of `zkvm_sha256`'s bump allocator. -/
def bump : Nat := 0xa05340b8
/-- What the prologue stores there: `0xa05340c8`, then `0xa0d340c8`, little-endian. -/
def bumpBytes : List Byte :=
  ((List.range 8).map fun j => byteOf (0xa05340c8 : Word) j) ++
    (List.range 8).map fun j => byteOf (0xa0d340c8 : Word) j

/-- Instructions (service steps at their ZisK cost) for an input of `n` bytes:
`200 + 10 ⌊n / 64⌋` (the longest path: prologue and dispatch 35, 10 per block, tail 21,
two-block padding 30, output 96). -/
def bound (n : Nat) : Nat := 200 + 10 * (n / 64)

/-- The input bytes `[a0, a0 + a1)`. -/
def msgOf (m : Machine) : List Byte := (readBytes m.mem (m.reg 10).toNat (m.reg 11).toNat).getD []

def frameR (m : Machine) : Word × Nat := (m.reg 2 - BitVec.ofNat 64 frameSize, frameSize)
def outR (m : Machine) : Word × Nat := (m.reg 12, 32)
def bumpR : Word × Nat := (BitVec.ofNat 64 bump, 16)
def stageR : Word × Nat := (BitVec.ofNat 64 Layout.extraParams, 8)
def inR (m : Machine) : Word × Nat := (m.reg 10, (m.reg 11).toNat)

def Pre (m : Machine) : Prop :=
  RodataLoaded zesuImage m ∧ StackOk m frameSize ∧ RetAligned m ∧
  ((m.reg 11).toNat = 0 ∨ srcOk m.mem (m.reg 10).toNat (m.reg 11).toNat = true) ∧
  dstOk m.mem (m.reg 12).toNat 32 = true ∧ dstOk m.mem bump 16 = true ∧
  dstOk m.mem Layout.extraParams 8 = true ∧
  [frameR m, outR m, bumpR, stageR].Pairwise Disjoint ∧
  ((m.reg 11).toNat = 0 ∨ (Disjoint (inR m) (frameR m) ∧ Disjoint (inR m) bumpR ∧
    Disjoint (inR m) stageR))

/-- The addresses `zkvm_sha256` may write. -/
def Written (m : Machine) (a : Word) : Prop :=
  InRange (frameR m).1 frameSize a ∨ InRange (m.reg 12) 32 a ∨ InRange (BitVec.ofNat 64 bump) 16 a ∨
    InRange (BitVec.ofNat 64 Layout.extraParams) 8 a

def Post (m m' : Machine) : Prop :=
  Returns m m' ∧ m'.reg 10 = 0 ∧ BytesAt m' (m.reg 12) (ZesuExec.Sha256.hash (msgOf m)) ∧
  BytesAt m' (BitVec.ofNat 64 bump) bumpBytes ∧ SameOutside (Written m) m m'

end ZesuExec.Fn.Sha256
