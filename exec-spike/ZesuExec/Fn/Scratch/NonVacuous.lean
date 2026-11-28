import ZesuExec.Fn.Scratch.RemapProof
import ZesuExec.Fn.Alloc.NonVacuous
import ZesuExec.Fn.Scratch.Snap
import ZesuExec.Fn.Scratch.SnapsFree
import ZesuExec.Fn.Scratch.SnapsRemap

/-!
# Non-vacuity and snapshots of the `scratch_arena.free` / `remap` contracts (programme plan S13)

`scrM pc`: a call at `pc` from `ra0` with `sp0` (`Fn/Alloc/NonVacuous.lean`) on an arena at
`ctx0` whose `chunks` word holds one chunk at `ch0` with `cap = 4096`, `used = 256`; `a1` is the
chunk's most recent allocation (`ch0 + 192`, `a2 = 64` bytes), `a3 = 3`, `a4 = 16` (remap's
`new_len`). All memory is present (zero outside those words). It satisfies `FreePre` at
`freeEntry` and `RemapPre` at `remapEntry`, the chunk branch included.

Contract rule, registered beside the end theorems: `FS.pre_nonvacuous`, `RS.pre_nonvacuous`,
and `FS.post_snapshot`, `RS.post_snapshot`, which evaluate `freeOk` / `remapOk`
(`Fn/Scratch/Snap.lean`) on the Unicorn snapshots `test/snapshots/ScratchFree` and
`ScratchRemap` by `decide`.
-/

namespace ZesuExec.Fn.Scratch
open ZesuExec
open ZesuExec.Fn.Alloc (sp0 ra0)

def ctx0 : Nat := 0xa0600000
def ch0 : Nat := 0xa0610000

/-- Byte `n` of the little-endian word `w` stored at `a`, if `n` is one of its bytes. -/
def wordByte (a w n : Nat) : Option Byte :=
  if a ≤ n ∧ n < a + 8 then some (BitVec.ofNat 8 (w >>> (8 * (n - a)))) else none

/-- `ctx0.chunks = ch0`, `ch0.cap = 4096`, `ch0.used = 256`, zero elsewhere. -/
def scrByte (n : Nat) : Byte :=
  ((wordByte (ctx0 + 16) ch0 n).orElse fun _ => (wordByte (ch0 + 8) 4096 n).orElse fun _ =>
    wordByte (ch0 + 16) 256 n).getD 0

def scrRegs (i : Fin 32) : Word :=
  if i.val = 1 then ra0 else if i.val = 2 then sp0 else if i.val = 10 then BitVec.ofNat 64 ctx0
  else if i.val = 11 then BitVec.ofNat 64 (ch0 + 192) else if i.val = 12 then 64
  else if i.val = 13 then 3 else if i.val = 14 then 16 else 0

def scrM (pc : Nat) : Machine := ⟨scrRegs, BitVec.ofNat 64 pc, fun a => some (scrByte a.toNat)⟩

theorem FS.pre_nonvacuous : ∃ m : Machine, m.pc.toNat = freeEntry ∧ FreePre m := by
  refine ⟨scrM freeEntry, rfl, ?_⟩
  unfold FreePre CtxOk Present StackOk RamRange RetAligned Fn.Disjoint
  decide

theorem RS.pre_nonvacuous : ∃ m : Machine, m.pc.toNat = remapEntry ∧ RemapPre m := by
  refine ⟨scrM remapEntry, rfl, ?_⟩
  unfold RemapPre CtxOk Present StackOk RamRange RetAligned Fn.Disjoint
  decide

/-- Contract rule (b): `free`'s `Pre` and `Post` hold on the Unicorn snapshots
`test/snapshots/ScratchFree` (`tools/snap.py --fn ScratchFree`), evaluated by `decide`. -/
theorem FS.post_snapshot : FS.snaps.all freeOk = true := by decide +kernel

/-- Contract rule (b): `remap`'s `Pre` and `Post` hold on the Unicorn snapshots
`test/snapshots/ScratchRemap` (`tools/snap.py --fn ScratchRemap`), evaluated by `decide`. -/
theorem RS.post_snapshot : RS.snaps.all remapOk = true := by decide +kernel

end ZesuExec.Fn.Scratch
