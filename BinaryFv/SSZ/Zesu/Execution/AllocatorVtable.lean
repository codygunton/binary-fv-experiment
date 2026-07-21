import BinaryFv.SSZ.Zesu.Analysis.AllocatorCalls
import BinaryFv.SSZ.Zesu.Execution.Representation

namespace BinaryFv.SSZ.Zesu.Execution

open BinaryFv.RiscV

/-- Loading the immutable ELF vtable makes every slot-24 cleanup dispatch target its pinned stub. -/
theorem loaded_vtable_free_target (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    Word64LERep state (Analysis.allocatorVtableAddress + Analysis.allocatorVtableCallSlotOffset)
      0x10440 := by
  intro index indexBound
  interval_cases index <;>
    exact loaded _ _ (by native_decide)

end BinaryFv.SSZ.Zesu.Execution
