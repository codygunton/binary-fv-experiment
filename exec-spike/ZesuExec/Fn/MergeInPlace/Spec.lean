import ZesuExec.Fn.MergeInPlace.Model
import ZesuExec.Fn.Rotate.Model

/-!
# `sort.block.mergeInPlace` copies: the contract (programme plan S16)

`mergeInPlace(items, A, B)` with `a0` = `items.ptr`, `a1` = `&A`, `a2` = `&B` (`Range` =
`{start, end}`, two little-endian `u64`); the elements are 32 bytes. A copy is a `Cfg`: entry,
frame size, saved slots, kept registers, and the element order as a key (`key m x`: the byte
string an element `x` is compared by, read in the entry machine `m`).

`Pre`: the two ranges readable, `A.start ≤ A.end = B.start ≤ B.end`, `items[0..B.end]` present
writable RAM disjoint from the frame and the ranges, both runs sorted (`Sorted`), the copy's
extra condition `c.pre` (what its key needs). `Post`: a return, memory changed only in
`items[A.start..B.end]` and the frame, and the output range is a sorted permutation of the two
runs (`MergeOf`, the model).
-/

namespace ZesuExec.Fn.MergeInPlace
open ZesuExec ZesuExec.Sym ZesuExec.Fn.Rotate

structure Cfg where
  entry : Nat
  fs : Nat
  /-- (frame offset, register) of each register the prologue saves -/
  saved : List (Nat × Nat)
  /-- callee-saved registers other than `sp` and the saved ones; the body never writes them -/
  kept : List Nat
  /-- the comparison key of an element (its 32 bytes), in the entry machine -/
  key : Machine → List Byte → List Byte
  /-- what the key needs of the entry machine -/
  pre : Machine → Prop
  saved_le : ∀ s ∈ saved, s.1 + 8 ≤ fs := by decide
  saved_disj : saved.Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1) := by decide
  saved_reg : ∀ s ∈ saved, s.2 < 32 := by decide
  fs_align : fs % 16 = 0 := by decide

/-- The `u64` at `a + off` (little-endian), as a number. -/
def u64 (m : Machine) (a : Word) (off : Nat) : Nat :=
  (Machine.ofBytesLE (byteList (fun j => (m.mem (a + BitVec.ofNat 64 j)).getD 0) off 8)).toNat

def ptr (m : Machine) : Word := m.reg 10
def aS (m : Machine) : Nat := u64 m (m.reg 11) 0
def aE (m : Machine) : Nat := u64 m (m.reg 11) 8
def bS (m : Machine) : Nat := u64 m (m.reg 12) 0
def bE (m : Machine) : Nat := u64 m (m.reg 12) 8

/-- Element `e` of a byte function: its 32 bytes. -/
def el (G : Nat → Nat → Byte) (e : Nat) : List Byte := (List.range 32).map (G e)

/-- Elements `[lo, hi)`. -/
def win (G : Nat → Nat → Byte) (lo hi : Nat) : List (List Byte) := (List.range' lo (hi - lo)).map (el G)

/-- The items as a byte function. -/
def items (m : Machine) (p : Word) : Nat → Nat → Byte := bytesOf 32 p m

section
variable (c : Cfg)

def frame (m : Machine) : Word := m.reg 2 - BitVec.ofNat 64 c.fs

def Pre (m : Machine) : Prop :=
  RodataLoaded zesuImage m ∧ StackOk m c.fs ∧ RetAligned m ∧
  Machine.readable (m.reg 11).toNat 16 = true ∧ (∀ j < 16, (m.mem (m.reg 11 + BitVec.ofNat 64 j)).isSome) ∧
  Machine.readable (m.reg 12).toNat 16 = true ∧ (∀ j < 16, (m.mem (m.reg 12 + BitVec.ofNat 64 j)).isSome) ∧
  aS m ≤ aE m ∧ aE m = bS m ∧ bS m ≤ bE m ∧
  Machine.writable (ptr m).toNat (32 * bE m) = true ∧
  (∀ j < 32 * bE m, (m.mem (ptr m + BitVec.ofNat 64 j)).isSome) ∧
  Disjoint (ptr m, 32 * bE m) (frame c m, c.fs) ∧
  Disjoint (m.reg 11, 16) (m.reg 12, 16) ∧ Disjoint (m.reg 11, 16) (frame c m, c.fs) ∧
  Disjoint (m.reg 12, 16) (frame c m, c.fs) ∧
  Sorted (c.key m) (win (items m (ptr m)) (aS m) (aE m)) ∧
  Sorted (c.key m) (win (items m (ptr m)) (bS m) (bE m)) ∧ c.pre m

/-- The output range or the frame. -/
def Writes (m : Machine) (a : Word) : Prop :=
  InRange (ptr m + BitVec.ofNat 64 (32 * aS m)) (32 * (bE m - aS m)) a ∨ InRange (frame c m) c.fs a

def Post (m m' : Machine) : Prop :=
  Returns m m' ∧ SameOutside (Writes c m) m m' ∧
  MergeOf (c.key m) (win (items m (ptr m)) (aS m) (aE m)) (win (items m (ptr m)) (bS m) (bE m))
    (win (items m' (ptr m)) (aS m) (bE m))

end

end ZesuExec.Fn.MergeInPlace
