import BinaryFv.Zesu.Contracts.Environment
import BinaryFv.Zesu.Contracts.CanonicalParams
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.StateBuilder

/-!
# Regression: `CodeIntact` ignores BSS writes but catches code corruption

`CodeIntact` was corrected from a full-image `matchesMemory` to a file-backed `fileBytesLoadedFaithfully`
(see `DecoderEnvironment.CodeIntact`). The full-image version was unsatisfiable on every mutating
path: it pinned every BSS byte to its static zero, so `postAlloc`'s `CodeIntact after` demanded the
heap cursor still be zero after the allocator advanced it, and the wrapper's `CodeIntact after`
demanded the decoder globals still be zero after the wrapper wrote them.

These regressions lock the correction in place against the *canonical* environment:

* the host-provided heap cursor `ZKVM_HEAP_POS` — which the runner sets nonzero at entry and the
  allocator advances on every allocation — is not file-backed, so writing it preserves `CodeIntact`;
* a genuine code byte (the `decodeRaw` entry at `0x10444`) is file-backed, so corrupting it breaks
  `CodeIntact`.

Together they say exactly what the corrected contract should: the decoder's and host's legitimate BSS
writes leave "code intact" undisturbed, while a corrupted instruction is still caught.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary
open BinaryFv.Zesu
open BinaryFv.Zesu.Contracts

/-- `ZKVM_HEAP_POS` sits in the BSS tail: not backed by any file byte of the pinned image. -/
theorem heapPos_not_file_backed :
    Artifacts.programImage.readFileByte? zkvmHeapPos = none := by native_decide

/-- The `decodeRaw` entry instruction is a real file-backed code byte. -/
theorem codeByte_file_backed :
    (Artifacts.programImage.readFileByte? 0x10444).isSome = true := by native_decide

/-- **Writing the host heap cursor preserves `CodeIntact`** against the canonical environment. This
is the fact the old full-image definition made false, and the reason the entry state — which sets
`ZKVM_HEAP_POS` to the arena base — can satisfy the exported entry binding at all.

Stated at the memory-map level (`CodeIntact` quantifies only over `state.mem`), so it applies to any
state whose memory the runner updates at the heap cursor. -/
theorem codeIntact_insert_heapPos {mem : Std.ExtHashMap Nat (BitVec 8)} {value : BitVec 8}
    (h : Artifacts.programImage.fileBytesLoadedFaithfully mem) :
    Artifacts.programImage.fileBytesLoadedFaithfully (mem.insert zkvmHeapPos value) :=
  ProgramImage.fileBytesLoadedFaithfully_insert_non_file heapPos_not_file_backed h

/-- **Corrupting a code byte breaks `CodeIntact`.** The companion negative: `fileBytesLoadedFaithfully`
genuinely pins the code, so a wrong value at the `decodeRaw` entry is caught. -/
theorem not_codeIntact_corrupt_code {mem : Std.ExtHashMap Nat (BitVec 8)} :
    ∃ value : BitVec 8, ¬ Artifacts.programImage.fileBytesLoadedFaithfully (mem.insert 0x10444 value) := by
  obtain ⟨byte, hbyte⟩ := Option.isSome_iff_exists.mp codeByte_file_backed
  refine ⟨BitVec.ofNat 8 (byte.toNat + 1), ProgramImage.not_fileBytesLoadedFaithfully_insert_file hbyte ?_⟩
  intro heq
  have hb : byte.toNat < 256 := byte.toNat_lt
  have hval := congrArg BitVec.toNat heq
  simp [BitVec.toNat_ofNat] at hval
  omega