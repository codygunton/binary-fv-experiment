import ZesuExec.Fn.Alloc.AllocProof
import ZesuExec.Fn.Alloc.FreeProof
import ZesuExec.Fn.Alloc.SnapsAlloc
import ZesuExec.Fn.Alloc.SnapsFree

/-!
# Non-vacuity of the allocator contracts (programme plan S13)

`initM`: a concrete machine in the allocator's start-up state (`Init`: every free-list head
null, `HEAP_POS = __zesu_heap_bottom`, `HEAP_TOP = __zesu_heap_top`, all memory present and
zero elsewhere), with `sp` just above the heap. `alloc_free_alloc`: from it, `alloc` of 24
bytes at alignment 8 runs (`AllocF.allocf_spec`); when it returns a block, `free` of that block
runs (`FreeF.freef_spec`, its precondition proved, both strengthenings included), and then
`alloc` runs again on the emptied heap. The contracts allow `alloc` to answer null; the theorem
covers both answers.

Contract rule, registered beside the end theorems: `AllocF.pre_nonvacuous` (`initM` satisfies
`AllocPre []`) and `FreeF.pre_nonvacuous` (`freeM`, one live block of 24 bytes below a bumped
`HEAP_POS`, satisfies `FreePre`), their components checked by `decide`; `AllocF.post_snapshot`
and `FreeF.post_snapshot` evaluate `allocOk` / `freeOk` (`Fn/Alloc/Snap.lean`) on the Unicorn
snapshots `test/snapshots/Alloc` and `Free` by `decide`.
-/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Machine

/-- Allocator memory with `HEAP_POS = pos`: the two bump words, zero elsewhere. -/
def heapByte (pos n : Nat) : Byte :=
  if posAddr ≤ n ∧ n < posAddr + 8 then BitVec.ofNat 8 (pos >>> (8 * (n - posAddr)))
  else if topAddr ≤ n ∧ n < topAddr + 8 then BitVec.ofNat 8 (heapTop >>> (8 * (n - topAddr)))
  else 0

def sp0 : Word := 0xbfff1000
def ra0 : Word := 0x80000000

/-- A call of the function at `pc` from `ra0` with `sp0`: `a1`, `a2`, `a3` as given, other
registers zero. -/
def callRegs (r11 r12 r13 : Word) (i : Fin 32) : Word :=
  if i.val = 1 then ra0 else if i.val = 2 then sp0 else if i.val = 11 then r11
  else if i.val = 12 then r12 else if i.val = 13 then r13 else 0

def initM : Machine :=
  ⟨callRegs 24 3 0, BitVec.ofNat 64 allocEntry, fun a => some (heapByte heapLo a.toNat)⟩

/-- `free(ptr = a0 of m, len = 24, log2 alignment = 3)` from `ra0`, memory and `sp` of `m`. -/
def toFree (m : Machine) : Machine :=
  ⟨fun i => if i.val = 2 then m.reg 2 else callRegs (m.reg 10) 24 3 i, BitVec.ofNat 64 freeEntry, m.mem⟩

/-- `alloc(len = 24, log2 alignment = 3)` from `ra0`, memory and `sp` of `m`. -/
def toAlloc (m : Machine) : Machine :=
  ⟨fun i => if i.val = 2 then m.reg 2 else callRegs 24 3 0 i, BitVec.ofNat 64 allocEntry, m.mem⟩

theorem heap_mem {L : List (Word × Nat)} {m m' : Machine} (h : Heap L m) (hm : m'.mem = m.mem) :
    Heap L m' :=
  heap_frame' L m m' h (fun a _ => by rw [hm]) ⟨fun a ha => by rw [hm]; exact ha, fun a _ => by rw [hm]⟩

theorem toFree_reg (m : Machine) : (toFree m).reg 1 = ra0 ∧ (toFree m).reg 11 = m.reg 10 ∧
    (toFree m).reg 12 = 24 ∧ (toFree m).reg 13 = 3 := ⟨rfl, rfl, rfl, rfl⟩

theorem toAlloc_reg (m : Machine) : (toAlloc m).reg 1 = ra0 ∧ (toAlloc m).reg 11 = 24 ∧
    (toAlloc m).reg 12 = 3 := ⟨rfl, rfl, rfl⟩

theorem init_initM : Init initM where
  present _ _ := rfl
  heads := by decide
  pos := by decide
  top := by decide

/-- The frame below `sp0` is outside the allocator's memory. -/
theorem frame_not_arena {a : Word} (h : InRange (sp0 - 16) 16 a) : ¬ Arena a := by
  unfold InRange at h
  rw [show (sp0 - 16).toNat = 0xbfff0ff0 from rfl] at h
  unfold Arena flBase posAddr heapTop; omega

theorem frame_free {L : List (Word × Nat)} {m : Machine} (h2 : m.reg 2 = sp0) :
    CalleeFrameFree (Priv L) m := fun _ ha hp => frame_not_arena (h2 ▸ ha) hp.1

/-- `sp0`'s frame is a valid 16-byte stack frame wherever its bytes are present. -/
theorem stack_ok {m : Machine} (h2 : m.reg 2 = sp0)
    (hp : ∀ j < 16, (m.mem (sp0 - BitVec.ofNat 64 16 + BitVec.ofNat 64 j)).isSome) : StackOk m 16 :=
  ⟨by rw [h2]; decide, by rw [h2]; decide, by rw [h2]; decide, by rw [h2]; exact hp⟩

theorem pre_initM : AllocPre [] initM :=
  ⟨init_heap init_initM, by decide, by decide, by decide, stack_ok rfl fun _ _ => rfl,
    by unfold RetAligned; rw [show initM.reg 1 = ra0 from rfl]; decide, frame_free rfl⟩

theorem toFree_pre {m0 m1 : Machine} (h2 : m0.reg 2 = sp0) (hst : StackOk m0 16)
    (hpost : AllocPost [] m0 m1 ∧ Preserved m0 m1) (h11 : (m0.reg 11).toNat = 24)
    (hne : m1.reg 10 ≠ 0) : FreePre [(m1.reg 10, 24)] (toFree m1) := by
  obtain ⟨⟨hret, -, hr⟩, hpres⟩ := hpost
  rcases hr with ⟨h0, -⟩ | ⟨-, hheap, -, -, hpriv, -⟩
  · exact absurd h0 hne
  rw [h11] at hheap hpriv
  have r2 : m1.reg 2 = sp0 := by rw [hret.2 2 (by decide), h2]
  have f2 : (toFree m1).reg 2 = sp0 := r2
  obtain ⟨g1, g11, g12, g13⟩ := toFree_reg m1
  rw [List.nil_append] at hheap
  refine ⟨heap_mem hheap rfl, by rw [g11, g12]; exact List.mem_singleton_self _, by rw [g12]; decide,
    by rw [g12]; decide, by rw [g13]; decide, .inl (by rw [g13]; decide),
    stack_ok f2 fun j hj => hpres.1 _ (by rw [← h2]; exact hst.2.2.2 j hj),
    by unfold RetAligned; rw [g1]; decide, frame_free f2, fun a ha hb => ?_⟩
  rw [g11, g12] at hb
  exact frame_not_arena (f2 ▸ ha) (hpriv a hb).1

theorem toAlloc_pre {mf m2 : Machine} (h2 : mf.reg 2 = sp0) (hst : StackOk mf 16) {p : Word}
    (hpost : FreePost [(p, 24)] mf m2 ∧ Preserved mf m2) (h11 : mf.reg 11 = p)
    (h12 : (mf.reg 12).toNat = 24) : AllocPre [] (toAlloc m2) := by
  obtain ⟨⟨hret, -, hheap, -⟩, hpres⟩ := hpost
  rw [h11, h12] at hheap
  simp only [List.erase_cons_head] at hheap
  have f2 : (toAlloc m2).reg 2 = sp0 := by
    show m2.reg 2 = sp0; rw [hret.2 2 (by decide), h2]
  obtain ⟨g1, g11, g12⟩ := toAlloc_reg m2
  exact ⟨heap_mem hheap rfl, by rw [g11]; decide, by rw [g11]; decide, by rw [g12]; decide,
    stack_ok f2 fun j hj => hpres.1 _ (by rw [← h2]; exact hst.2.2.2 j hj),
    by unfold RetAligned; rw [g1]; decide, frame_free f2⟩

/-- `alloc`, `free`, `alloc` from the start-up state. -/
theorem alloc_free_alloc :
    Init initM ∧ AllocPre [] initM ∧
    Reaches zesuImage 53 (fun m1 => AllocPost [] initM m1 ∧ (m1.reg 10 = 0 ∨
      (FreePre [(m1.reg 10, 24)] (toFree m1) ∧
       Reaches zesuImage 42 (fun m2 => FreePost [(m1.reg 10, 24)] (toFree m1) m2 ∧
         AllocPre [] (toAlloc m2) ∧ Reaches zesuImage 53 (AllocPost [] (toAlloc m2)) (toAlloc m2))
         (toFree m1)))) initM := by
  refine ⟨init_initM, pre_initM, ?_⟩
  refine (Reaches.preserve (AllocF.allocf_spec [] initM rfl pre_initM)).mono (Nat.le_refl _)
    fun m1 h1 => ⟨h1.1, ?_⟩
  by_cases hne : m1.reg 10 = 0
  · exact .inl hne
  have hf := toFree_pre rfl pre_initM.2.2.2.2.1 h1 rfl hne
  refine .inr ⟨hf, ?_⟩
  refine (Reaches.preserve (FreeF.freef_spec _ (toFree m1) rfl hf)).mono (Nat.le_refl _)
    fun m2 h2 => ⟨h2.1, ?_⟩
  have hf2 : (toFree m1).reg 2 = sp0 := by
    show m1.reg 2 = sp0; rw [h1.1.1.2 2 (by decide)]; rfl
  have ha := toAlloc_pre hf2 hf.2.2.2.2.2.2.1 h2 rfl rfl
  exact ⟨ha, AllocF.allocf_spec [] (toAlloc m2) rfl ha⟩

/-! ## Contract rule: non-vacuity and snapshots -/

/-- `initM` satisfies `alloc`'s precondition. -/
theorem AllocF.pre_nonvacuous : ∃ m : Machine, m.pc.toNat = allocEntry ∧ AllocPre [] m :=
  ⟨initM, rfl, pre_initM⟩

/-- The live block of `freeM`: 24 bytes at the first 32-aligned heap address. -/
def p0 : Word := 0xa0d34540

/-- `free(ptr = p0, len = 24, log2 alignment = 3)` from `ra0` with `sp0`, `HEAP_POS` just above
`p0`'s 32-byte block, every free list empty. -/
def freeM : Machine :=
  ⟨callRegs p0 24 3, BitVec.ofNat 64 freeEntry, fun a => some (heapByte (heapLo + 0x30) a.toNat)⟩

theorem heap_freeM : Heap [(p0, 24)] freeM :=
  ⟨⟨heapLo + 0x30, fun _ => []⟩,
    ⟨fun _ _ => rfl, by decide, by decide,
      fun k hk => (by decide : ∀ k < 22, rd freeM (flBase + 8 * k) = some 0) k hk⟩,
    ⟨Nat.le_add_right _ _, by decide, by decide, by decide,
      by rw [show blocks [(p0, 24)] ⟨heapLo + 0x30, fun _ => []⟩ = [(p0.toNat, cap 24)] from rfl]
         exact List.pairwise_singleton _ _⟩⟩

/-- `freeM` satisfies `free`'s precondition, both strengthenings included. -/
theorem FreeF.pre_nonvacuous :
    ∃ (L : List (Word × Nat)) (m : Machine), m.pc.toNat = freeEntry ∧ FreePre L m :=
  ⟨[(p0, 24)], freeM, rfl, heap_freeM, List.mem_singleton_self _, by decide, by decide, by decide,
    .inl (by decide), stack_ok rfl fun _ _ => rfl,
    by unfold RetAligned; rw [show freeM.reg 1 = ra0 from rfl]; decide, frame_free rfl,
    fun a ha hb => by
      unfold InRange at ha hb
      rw [show (freeM.reg 2 - 16).toNat = 0xbfff0ff0 from rfl] at ha
      rw [show (freeM.reg 11).toNat = 0xa0d34540 from rfl, show (freeM.reg 12).toNat = 24 from rfl] at hb
      omega⟩

/-- Contract rule (b): `alloc`'s `Pre` and `Post` hold on the Unicorn snapshots
`test/snapshots/Alloc` (`tools/snap.py --fn Alloc`), evaluated by `decide`. -/
theorem AllocF.post_snapshot : AllocF.snaps.all allocOk = true := by decide +kernel

/-- Contract rule (b): `free`'s `Pre` and `Post` hold on the Unicorn snapshots
`test/snapshots/Free` (`tools/snap.py --fn Free`), evaluated by `decide`. -/
theorem FreeF.post_snapshot : FreeF.snaps.all freeOk = true := by decide +kernel

end ZesuExec.Fn.Alloc
