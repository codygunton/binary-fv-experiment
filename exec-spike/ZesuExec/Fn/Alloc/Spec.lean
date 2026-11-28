import ZesuExec.Fn.Alloc.Inv

/-!
# Contracts of `alt_fl_alloc.alloc` and `alt_fl_alloc.free` over the free-list invariant

Draft, unreviewed (programme plan S13, contract rule). The interface is the one zesislar's
`altFlAllocCallSpec` / `altFlFreeCallSpec` (`ZesuSsz/Contracts/AltFlAllocPremises.v`) give,
without separation logic, now over the concrete invariant `Alloc.Heap` and private memory
`Alloc.Priv` of `Fn/Alloc/Inv.lean` instead of abstract ones.

`alloc(ctx = a0, len = a1, log2 alignment = a2, ret_addr = a3)` returns in `a0` either null (the
heap is unchanged) or a new block carved from `Priv L`; `free(ctx, ptr = a1, len = a2,
log2 alignment = a3, ret_addr)` takes a live block back. Both use at most 16 bytes of stack below
`sp` and return like any function (`Returns`). `remap` is F0 (`f0_spec`).

Requests carry log2 alignment at most 4 (the S7 trust-base change of commit `9285684f`: DTF's
authorization list allocates 16-byte aligned tuples). `alloc` and `free` round the size class up
to the alignment, `sizeClass = max(sizeClassOfBytes len, log2_align - 3)`; a block of `len ≤ 8`
bytes allocated with alignment below 16 is 8 bytes long, so `free` of it must not claim
alignment 16: `free`'s precondition asks `log2_align ≤ 3 ∨ 8 < len` (a strengthening recorded in
`STATEMENTS.md`; every caller frees with the alignment it allocated with, and no caller frees a
block of at most 8 bytes at alignment 16).
-/

namespace ZesuExec.Fn
open ZesuExec

def allocEntry : Nat := 0x80042494
def freeEntry : Nat := 0x80041f38

namespace Alloc

def AllocPre (L : List (Word × Nat)) (m : Machine) : Prop :=
  Heap L m ∧ 0 < (m.reg 11).toNat ∧ (m.reg 11).toNat < 2 ^ 63 ∧ (m.reg 12).toNat ≤ 4 ∧
    StackOk m 16 ∧ RetAligned m ∧ CalleeFrameFree (Priv L) m

/-- `alloc` returns null and keeps the heap, or a fresh block from `Priv L`. -/
def AllocPost (L : List (Word × Nat)) (m m' : Machine) : Prop :=
  Returns m m' ∧ SameOutside (fun a => Priv L a ∨ InRange (m.reg 2 - 16) 16 a) m m' ∧
    ((m'.reg 10 = 0 ∧ Heap L m') ∨
     (m'.reg 10 ≠ 0 ∧ Heap (L ++ [(m'.reg 10, (m.reg 11).toNat)]) m' ∧
      RamRange (m'.reg 10) (m.reg 11).toNat ∧ Present m' (m'.reg 10) (m.reg 11).toNat ∧
      (∀ a, InRange (m'.reg 10) (m.reg 11).toNat a → Priv L a) ∧
      (∀ a, Priv (L ++ [(m'.reg 10, (m.reg 11).toNat)]) a → Priv L a)))

def FreePre (L : List (Word × Nat)) (m : Machine) : Prop :=
  Heap L m ∧ (m.reg 11, (m.reg 12).toNat) ∈ L ∧ 0 < (m.reg 12).toNat ∧
    (m.reg 12).toNat < 2 ^ 63 ∧ (m.reg 13).toNat ≤ 4 ∧
    ((m.reg 13).toNat ≤ 3 ∨ 8 < (m.reg 12).toNat) ∧ StackOk m 16 ∧ RetAligned m ∧
    CalleeFrameFree (Priv L) m

/-- `free` takes a live block back into `Priv`. -/
def FreePost (L : List (Word × Nat)) (m m' : Machine) : Prop :=
  Returns m m' ∧
    SameOutside (fun a => Priv L a ∨ InRange (m.reg 11) (m.reg 12).toNat a ∨
      InRange (m.reg 2 - 16) 16 a) m m' ∧
    Heap (L.erase (m.reg 11, (m.reg 12).toNat)) m' ∧
    (∀ a, Priv (L.erase (m.reg 11, (m.reg 12).toNat)) a →
      Priv L a ∨ InRange (m.reg 11) (m.reg 12).toNat a)

end Alloc
end ZesuExec.Fn
