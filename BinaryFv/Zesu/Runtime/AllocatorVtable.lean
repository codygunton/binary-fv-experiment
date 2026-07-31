import BinaryFv.Zesu.Artifact.AllocatorCalls
import BinaryFv.Zesu.MemoryRepresentation.RawV4

namespace BinaryFv.Zesu.Runtime

open BinaryFv.RiscV
open BinaryFv.Zesu.MemoryRepresentation

/-- Loading the immutable ELF vtable makes every slot-24 cleanup dispatch target its pinned stub. -/
theorem loaded_vtable_free_target (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    Word64LERep state (Artifact.allocatorVtableAddress + Artifact.allocatorVtableCallSlotOffset)
      0x10440 := by
  intro index indexBound
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨
      index = 6 ∨ index = 7 := by
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact loaded 0x13f88 0x40 (by native_decide)
  · exact loaded 0x13f89 0x04 (by native_decide)
  · exact loaded 0x13f8a 0x01 (by native_decide)
  · exact loaded 0x13f8b 0x00 (by native_decide)
  · exact loaded 0x13f8c 0x00 (by native_decide)
  · exact loaded 0x13f8d 0x00 (by native_decide)
  · exact loaded 0x13f8e 0x00 (by native_decide)
  · exact loaded 0x13f8f 0x00 (by native_decide)

end BinaryFv.Zesu.Runtime
