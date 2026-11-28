import ZesuExec.Fn.Scratch.AllocProof
import ZesuExec.Fn.Scratch.Snap
import ZesuExec.Fn.Scratch.SnapsAlloc

/-!
# Non-vacuity and snapshots of the `scratch_arena.alloc` contract (programme plan S13)

`saM`: `Alloc.initRoM` (the allocator's start-up state, rodata loaded, `sp = sp0`, `ra = ra0`,
`len = 24`, `log2 alignment = 3`) with `a0 = ctxS`, an arena outside the allocator's memory whose
`child.vtable` word holds `alt_fl_alloc`'s vtable `0x801136d8`, no chunk and
`last_chunk_size = 0`. It satisfies `AllocPreS Alloc.contract []` (`SA.pre_nonvacuous`): the
first call of an arena, which requests a new chunk from the child. `SA.post_snapshot` evaluates
`saOk` (`Fn/Scratch/Snap.lean`) on the Unicorn snapshots `test/snapshots/ScratchAlloc` by `decide`:
no chunk (small and large request), fast fit with and without padding, a full chunk with
`last_chunk_size ≠ 0` (new chunk of `2 · last` and of `needN`), and the child returning null.
-/

namespace ZesuExec.Fn.Scratch
open ZesuExec

def ctxS : Word := 0xa0600000

def saByte (a : Word) : Option Byte :=
  if ctxS.toNat + 8 ≤ a.toNat ∧ a.toNat < ctxS.toNat + 16 then
    some (BitVec.ofNat 8 (allocVt >>> (8 * (a.toNat - (ctxS.toNat + 8)))))
  else Alloc.initRoM.mem a

def saM : Machine :=
  ⟨fun i => if i.val = 10 then ctxS else Alloc.initRoM.regs i, BitVec.ofNat 64 allocEntryS, saByte⟩

theorem saM_present (a : Word) : (saM.mem a).isSome := by
  show (saByte a).isSome
  unfold saByte; split
  · rfl
  · show (match zesuImage.rodataByte? a.toNat with
      | some b => some (BitVec.ofNat 8 b) | none => Alloc.initM.mem a).isSome
    split <;> rfl

theorem saM_ctx_out {a : Word} (h : ¬ (ctxS.toNat + 8 ≤ a.toNat ∧ a.toNat < ctxS.toNat + 16)) :
    saM.mem a = Alloc.initRoM.mem a := by
  show saByte a = _; unfold saByte; rw [if_neg h]

theorem saM_heap : Alloc.contract.Heap [] saM :=
  Alloc.contract.heap_frame [] _ _ Alloc.contract_initRo (fun a ha => saM_ctx_out fun h => by
    have := Alloc.contract_priv_nil ha
    unfold Alloc.Arena Alloc.flBase Alloc.posAddr Alloc.heapTop at this
    unfold ctxS at h; simp at h; omega) (by simp)

theorem saM_ro : RodataLoaded zesuImage saM := fun a b h => by
  have ha := zesu_rodata_range h
  unfold Layout.rodataHi at ha
  rw [saM_ctx_out fun h' => by unfold ctxS at h'; simp at h'; omega]
  exact Alloc.initRo_rodata a b h

theorem SA.pre_nonvacuous :
    ∃ (L : List (Word × Nat)) (m : Machine), m.pc.toNat = allocEntryS ∧ AllocPreS Alloc.contract L m := by
  have r10 : saM.reg 10 = 0xa0600000 := rfl
  have r2 : saM.reg 2 = 0xbfff1000 := rfl
  refine ⟨[], saM, rfl, saM_ro, by unfold RetAligned; decide, ⟨by rw [r2]; decide, by rw [r2]; decide,
    by rw [r2]; decide, fun j _ => saM_present _⟩, by unfold RamRange; rw [r10]; decide,
    fun j _ => saM_present _, by decide, by decide, by unfold needN; decide, by decide,
    by unfold Fn.Disjoint; rw [r10, r2]; decide, saM_heap, fun a ha hp => ?_,
    fun h => absurd (by decide) h⟩
  have := Alloc.contract_priv_nil hp
  unfold Alloc.Arena Alloc.flBase Alloc.posAddr Alloc.heapTop at this
  unfold InRange at ha
  rw [r10, r2, show (0xbfff1000 - 80 : Word).toNat = 0xbfff0fb0 from rfl] at ha
  simp at ha; omega

/-- Contract rule (b): `alloc`'s `Pre` and `Post` hold on the Unicorn snapshots
`test/snapshots/ScratchAlloc` (`tools/snap.py --fn ScratchAlloc`), evaluated by `decide`. -/
theorem SA.post_snapshot : SA.snaps.all saOk = true := by decide +kernel

end ZesuExec.Fn.Scratch
