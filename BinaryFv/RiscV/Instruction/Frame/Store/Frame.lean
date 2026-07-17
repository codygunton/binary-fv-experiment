import BinaryFv.RiscV.Instruction.Frame.Store.Translation

/-!
# The STORE stack-pointer frame

The two exported conclusions: the generated `execute_STORE`, and its dispatch, leave `x2` alone.
-/

namespace BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The generated STORE action preserves `x2` on normal and error outcomes. -/
theorem execute_STORE_preserves_stack_pointer (immediate : BitVec 12)
    (sourceData sourceAddress : regidx) (width : Nat) :
    PreservesStackPointer (execute_STORE immediate sourceData sourceAddress width) := by
  apply preservesStackPointer_of_preservesX2
  exact preservesX2_execute_STORE_of_translate immediate sourceData sourceAddress width
    (fun vaddr => preservesX2_translateAddr_store_data vaddr)

/-- The generated dispatcher preserves `x2` for every STORE instruction outcome. -/
theorem executeSTOREDispatchPreservesStackPointer (state : State) (immediate : BitVec 12)
    (sourceData sourceAddress : regidx) (width : Nat) :
    (match (execute (.STORE (immediate, sourceData, sourceAddress, width))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  exact execute_STORE_dispatch_preservesX2_of_translate
    state immediate sourceData sourceAddress width
    (fun vaddr => preservesX2_translateAddr_store_data vaddr)

theorem mem_write_ea_preserves_stack_pointer (state : State) (address : physaddr)
    (width : Nat) :
    (match (mem_write_ea address width false false false).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  simp [mem_write_ea, write_kind_of_flags, write_ram_ea, EStateM.run, EStateM.bind,
    EStateM.pure, EStateM.instMonad]

end BinaryFv.RiscV
