import BinaryFv.RISCV.FenceFrame
import BinaryFv.RISCV.JalFrame

namespace BinaryFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The generated `execute` dispatcher preserves `x2` for every conditional branch. -/
theorem executeBTYPEDispatchPreservesStackPointer (state : State) (immediate : BitVec 13)
    (source2 source1 : regidx) (operation : bop) :
    (match (execute (.BTYPE (immediate, source2, source1, operation))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_BTYPE immediate source2 source1 operation).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame := execute_BTYPE_preserves_stack_pointer immediate source2 source1 operation
  unfold PreservesStackPointer at frame
  cases hAction : (execute_BTYPE immediate source2 source1 operation).run state <;>
    simpa [hAction] using frame state

/-- The generated `execute` dispatcher preserves `x2` for a non-stack JAL link destination. -/
theorem executeJALDispatchPreservesStackPointer (state : State) (immediate : BitVec 21)
    (destination : regidx) (notStack : destination ≠ stackPointer) :
    (match (execute (.JAL (immediate, destination))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_JAL immediate destination).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame := execute_JAL_preserves_stack_pointer state immediate destination notStack
  cases hAction : (execute_JAL immediate destination).run state <;>
    simpa [hAction] using frame

/-- The generated `execute` dispatcher preserves `x2` for a non-stack JALR link destination. -/
theorem executeJALRDispatchPreservesStackPointer (state : State) (immediate : BitVec 12)
    (source destination : regidx) (notStack : destination ≠ stackPointer) :
    (match (execute (.JALR (immediate, source, destination))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_JALR immediate source destination).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame := execute_JALR_preserves_stack_pointer state immediate source destination notStack
  cases hAction : (execute_JALR immediate source destination).run state <;>
    simpa [hAction] using frame

/-- The generated dispatcher preserves `x2` for the generated TSO fence. -/
theorem executeFENCE_TSODispatchPreservesStackPointer (state : State) :
    (match (execute (.FENCE_TSO ())).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_FENCE_TSO ()).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame := execute_FENCE_TSO_preserves_stack_pointer state
  cases hAction : (execute_FENCE_TSO ()).run state <;>
    simpa [hAction] using frame

/-- The generated dispatcher preserves `x2` for every generated FENCE outcome. -/
theorem executeFENCEDispatchPreservesStackPointer (state : State) (fm pred succ : BitVec 4)
    (source destination : regidx) :
    (match (execute (.FENCE (fm, pred, succ, source, destination))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_FENCE fm pred succ source destination).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame := execute_FENCE_preserves_stack_pointer state fm pred succ source destination
  cases hAction : (execute_FENCE fm pred succ source destination).run state <;>
    simpa [hAction] using frame

end BinaryFv.RISCV
