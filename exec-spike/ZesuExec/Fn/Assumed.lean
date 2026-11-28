import ZesuExec.Fn.Common
import ZesuExec.Fn.Preserve

/-!
# Assumed contracts of `alt_fl_alloc.alloc` and `alt_fl_alloc.free`

`AllocAssumptions` transcribes, without separation logic, `altFlAllocCallSpec` and
`altFlFreeCallSpec` of zesislar's `ZesuSsz/Contracts/AltFlAllocPremises.v`. It is a structure
that theorems take as an explicit hypothesis, never an axiom.

The allocator state (`altFlHeap` there) is the abstract `Heap L m`, where `L` lists the live
blocks `(pointer, bytes)`. The memory the allocator owns between calls is the abstract
`Priv L`: it never meets a live block, and `Heap L` depends only on it (`heap_frame`). A
caller owns memory outside `Priv L`; it states that its regions avoid `Priv L`.

`alloc(ctx = a0, bytes = a1, log2 alignment = a2, ret_addr = a3)` returns in `a0` either null
(the heap is unchanged) or a new block carved from `Priv L`; `free(ctx, ptr = a1, bytes = a2,
log2 alignment = a3, ret_addr)` takes a live block back. Both use 16 bytes of stack below `sp`
and return like any function (`Returns`). `remap` is not assumed: it is F0 (`f0_spec`).

Requests carry log2 alignment at most 4 (S7 trust-base change approved by the user: DTF's
authorization list allocates 16-byte aligned tuples; `alt_fl_alloc` rounds the size class up to
the alignment, `sizeClass = max(sizeClassOfBytes len, log2_align - 3)`, in `alloc` and `free`
alike). zesislar's `altFlMaxLog2Alignment` is 3; this contract diverges (STATEMENTS.md).
-/

namespace ZesuExec.Fn
open ZesuExec

def allocEntry : Nat := 0x80042494
def freeEntry : Nat := 0x80041f38

/-- An address inside one of the live blocks. -/
def InLive (L : List (Word × Nat)) (a : Word) : Prop := ∃ b ∈ L, InRange b.1 b.2 a

/-- `[lo, lo+n)` lies in RAM. -/
def RamRange (lo : Word) (n : Nat) : Prop :=
  Layout.ramLo ≤ lo.toNat ∧ lo.toNat + n ≤ Layout.ramHi

/-- The `n` bytes at `a` are present. -/
def Present (m : Machine) (a : Word) (n : Nat) : Prop :=
  ∀ j < n, (m.mem (a + BitVec.ofNat 64 j)).isSome

/-- The 16-byte frame an allocator callee uses avoids the allocator's memory. -/
def CalleeFrameFree (Priv : Word → Prop) (m : Machine) : Prop :=
  ∀ a, InRange (m.reg 2 - 16) 16 a → ¬ Priv a

structure AllocAssumptions (img : Image) where
  Heap : List (Word × Nat) → Machine → Prop
  Priv : List (Word × Nat) → Word → Prop
  priv_not_live : ∀ L a, Priv L a → ¬ InLive L a
  /-- `Heap L` depends only on `Priv L` and on the live blocks staying present. (Without the
  presence premise, a machine that drops a live block's bytes would keep `Heap L`, and `live_ok`
  would force every live block to be empty.) -/
  heap_frame : ∀ L m m', Heap L m → (∀ a, Priv L a → m'.mem a = m.mem a) →
    (∀ b ∈ L, Present m' b.1 b.2) → Heap L m'
  live_ok : ∀ L m, Heap L m →
    L.Pairwise (fun b c => b.1.toNat + b.2 ≤ c.1.toNat ∨ c.1.toNat + c.2 ≤ b.1.toNat) ∧
    ∀ b ∈ L, RamRange b.1 b.2 ∧ Present m b.1 b.2
  /-- `alloc` returns null and keeps the heap, or a fresh block from `Priv L`. -/
  alloc_spec : ∀ L, Spec img allocEntry 53
    (fun m => Heap L m ∧ 0 < (m.reg 11).toNat ∧ (m.reg 11).toNat < 2 ^ 63 ∧
      (m.reg 12).toNat ≤ 4 ∧ StackOk m 16 ∧ RetAligned m ∧ CalleeFrameFree (Priv L) m)
    (fun m m' => Returns m m' ∧
      SameOutside (fun a => Priv L a ∨ InRange (m.reg 2 - 16) 16 a) m m' ∧
      ((m'.reg 10 = 0 ∧ Heap L m') ∨
       (m'.reg 10 ≠ 0 ∧ Heap (L ++ [(m'.reg 10, (m.reg 11).toNat)]) m' ∧
        RamRange (m'.reg 10) (m.reg 11).toNat ∧ Present m' (m'.reg 10) (m.reg 11).toNat ∧
        (∀ a, InRange (m'.reg 10) (m.reg 11).toNat a → Priv L a) ∧
        (∀ a, Priv (L ++ [(m'.reg 10, (m.reg 11).toNat)]) a → Priv L a))))
  /-- `free` takes a live block back into `Priv`. -/
  free_spec : ∀ L, Spec img freeEntry 42
    (fun m => Heap L m ∧ (m.reg 11, (m.reg 12).toNat) ∈ L ∧ 0 < (m.reg 12).toNat ∧
      (m.reg 12).toNat < 2 ^ 63 ∧ (m.reg 13).toNat ≤ 4 ∧ StackOk m 16 ∧ RetAligned m ∧
      CalleeFrameFree (Priv L) m)
    (fun m m' => Returns m m' ∧
      SameOutside (fun a => Priv L a ∨ InRange (m.reg 11) (m.reg 12).toNat a ∨
        InRange (m.reg 2 - 16) 16 a) m m' ∧
      Heap (L.erase (m.reg 11, (m.reg 12).toNat)) m' ∧
      (∀ a, Priv (L.erase (m.reg 11, (m.reg 12).toNat)) a →
        Priv L a ∨ InRange (m.reg 11) (m.reg 12).toNat a))
  /-- The allocator's arena (state object and heap area, fixed): under any `Heap L`, it is
  exactly `Priv L` and the live blocks of `L` (programme plan S6, TX). -/
  Arena : Word → Prop
  arena_split : ∀ L m a, Heap L m → (Arena a ↔ Priv L a ∨ InLive L a)

/-- `heap_frame` for a step that keeps present bytes present (every run does, `Preserved`). -/
theorem AllocAssumptions.heap_frame' {img : Image} (A : AllocAssumptions img)
    (L : List (Word × Nat)) (m m' : Machine) (h : A.Heap L m)
    (hpriv : ∀ a, A.Priv L a → m'.mem a = m.mem a) (hp : Preserved m m') : A.Heap L m' :=
  A.heap_frame L m m' h hpriv fun b hb j hj => hp.1 _ (((A.live_ok L m h).2 b hb).2 j hj)

end ZesuExec.Fn
