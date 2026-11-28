import ZesuExec.Fn.Alloc.NonVacuous

/-!
# The allocator contract `AllocContract` and its proved instance `Alloc.contract`

`AllocContract` is the interface callers of `alt_fl_alloc.alloc` and `alt_fl_alloc.free` work
against, transcribed without separation logic from `altFlAllocCallSpec` and `altFlFreeCallSpec`
of zesislar's `ZesuSsz/Contracts/AltFlAllocPremises.v`: an allocator state `Heap L m` (`L` the
live blocks `(pointer, bytes)`), the memory `Priv L` the allocator owns between calls (it never
meets a live block, and `Heap L` depends only on it, `heap_frame`), the contracts of `alloc` and
`free`, and the fixed arena that is exactly `Priv L` and the live blocks (`arena_split`). A caller
owns memory outside `Priv L`; it states that its regions avoid `Priv L`. Callers' proofs are
generic in an `AllocContract`; their end theorems use `Alloc.contract`, so they carry no
allocator hypothesis.

`alloc(ctx = a0, bytes = a1, log2 alignment = a2, ret_addr = a3)` returns in `a0` either null
(the heap is unchanged) or a new block carved from `Priv L`; `free(ctx, ptr = a1, bytes = a2,
log2 alignment = a3, ret_addr)` takes a live block back. Both use 16 bytes of stack below `sp`
and return like any function (`Returns`). `remap` is F0 (`f0_spec`).

Requests carry log2 alignment at most 4 (S7 trust-base change approved by the user: DTF's
authorization list allocates 16-byte aligned tuples; zesislar's `altFlMaxLog2Alignment` is 3,
STATEMENTS.md). `free`'s precondition is `Alloc.FreePre`: besides the former assumed one, a block
of at most 8 bytes is not freed at alignment 16 (`log2_align ≤ 3 ∨ 8 < bytes`), and the callee's
16-byte frame avoids the freed block (both in STATEMENTS.md, S13).

`Alloc.contract` is the instance over the free-list invariant of `Fn/Alloc/Inv.lean`: `Heap`,
`Priv` and `Arena` are `Alloc.Heap`, `Alloc.Priv` and `Alloc.Arena`, `alloc_spec` and
`free_spec` are `Alloc.AllocF.allocf_spec` and `Alloc.FreeF.freef_spec`.
-/

namespace ZesuExec.Fn
open ZesuExec

structure AllocContract (img : Image) where
  Heap : List (Word × Nat) → Machine → Prop
  Priv : List (Word × Nat) → Word → Prop
  priv_not_live : ∀ L a, Priv L a → ¬ InLive L a
  /-- `Heap L` depends only on `Priv L` and on the live blocks staying present. -/
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
      (m.reg 12).toNat < 2 ^ 63 ∧ (m.reg 13).toNat ≤ 4 ∧
      ((m.reg 13).toNat ≤ 3 ∨ 8 < (m.reg 12).toNat) ∧ StackOk m 16 ∧ RetAligned m ∧
      CalleeFrameFree (Priv L) m ∧
      ∀ a, InRange (m.reg 2 - 16) 16 a → ¬ InRange (m.reg 11) (m.reg 12).toNat a)
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
theorem AllocContract.heap_frame' {img : Image} (A : AllocContract img)
    (L : List (Word × Nat)) (m m' : Machine) (h : A.Heap L m)
    (hpriv : ∀ a, A.Priv L a → m'.mem a = m.mem a) (hp : Preserved m m') : A.Heap L m' :=
  A.heap_frame L m m' h hpriv fun b hb j hj => hp.1 _ (((A.live_ok L m h).2 b hb).2 j hj)

/-- `alt_fl_alloc` meets `AllocContract`: every field proved from the free-list invariant. -/
def Alloc.contract : AllocContract zesuImage where
  Heap := Alloc.Heap
  Priv := Alloc.Priv
  priv_not_live := Alloc.priv_not_live
  heap_frame := Alloc.heap_frame
  live_ok := Alloc.live_ok
  alloc_spec := Alloc.AllocF.allocf_spec
  free_spec := Alloc.FreeF.freef_spec
  Arena := Alloc.Arena
  arena_split := Alloc.arena_split

/-- The start-up machine `Alloc.initM` holds `Heap []` of the instance. -/
theorem Alloc.contract_init : Alloc.contract.Heap [] Alloc.initM :=
  Alloc.init_heap Alloc.init_initM

/-- The instance's private memory at start-up is the arena (free lists, bump words, heap). -/
theorem Alloc.contract_priv_nil {a : Word} (h : Alloc.contract.Priv [] a) : Alloc.Arena a := h.1

/-- `Alloc.initM` with the image's rodata loaded (callers' `Pre` asks `RodataLoaded`). -/
def Alloc.initRoM : Machine :=
  ⟨Alloc.initM.regs, Alloc.initM.pc, fun a => match zesuImage.rodataByte? a.toNat with
    | some b => some (BitVec.ofNat 8 b)
    | none => Alloc.initM.mem a⟩

theorem Alloc.initRo_rodata : RodataLoaded zesuImage Alloc.initRoM := by
  intro a b h
  have ha : a < 2 ^ 64 := by
    have := zesu_rodata_range h; unfold Layout.rodataHi at this; omega
  simp [Alloc.initRoM, Nat.mod_eq_of_lt ha, h]

theorem Alloc.contract_initRo : Alloc.contract.Heap [] Alloc.initRoM :=
  Alloc.heap_frame [] _ _ Alloc.contract_init (fun a ha => by
    have hA := ha.1
    cases hq : zesuImage.rodataByte? a.toNat with
    | none => simp [Alloc.initRoM, hq]
    | some b =>
      have := zesu_rodata_range hq
      unfold Alloc.Arena Alloc.flBase Alloc.posAddr Alloc.heapTop at hA
      unfold Layout.rodataHi at this; omega) (by simp)

end ZesuExec.Fn
