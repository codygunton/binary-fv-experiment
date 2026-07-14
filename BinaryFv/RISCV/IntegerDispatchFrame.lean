import BinaryFv.RISCV.ITypeFrame
import BinaryFv.RISCV.MulDivFrame
import BinaryFv.RISCV.RTypeFrame
import BinaryFv.RISCV.ShiftIopFrame

namespace BinaryFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The generated dispatcher preserves `x2` for a non-stack U-type destination. -/
theorem executeUTYPEDispatchPreservesStackPointer (state : State) (immediate : BitVec 20)
    (destination : regidx) (operation : uop) (notStack : destination ≠ stackPointer) :
    (match (execute (.UTYPE (immediate, destination, operation))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_UTYPE immediate destination operation).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame := execute_UTYPE_preserves_stack_pointer state immediate destination operation notStack
  cases hAction : (execute_UTYPE immediate destination operation).run state <;>
    simpa [hAction] using frame

/-- The generated dispatcher preserves `x2` for a non-stack R-type destination. -/
theorem executeRTYPEDispatchPreservesStackPointer (state : State)
    (source2 source1 destination : regidx) (operation : rop) (notStack : destination ≠ stackPointer) :
    (match (execute (.RTYPE (source2, source1, destination, operation))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_RTYPE source2 source1 destination operation).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame := execute_RTYPE_preserves_stack_pointer state source2 source1 destination operation notStack
  cases hAction : (execute_RTYPE source2 source1 destination operation).run state <;>
    simpa [hAction] using frame

/-- The generated dispatcher preserves `x2` for a non-stack I-type destination. -/
theorem executeITYPEDispatchPreservesStackPointer (state : State) (immediate : BitVec 12)
    (source destination : regidx) (operation : iop) (notStack : destination ≠ stackPointer) :
    (match (execute (.ITYPE (immediate, source, destination, operation))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_ITYPE immediate source destination operation).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame := execute_ITYPE_preserves_stack_pointer state immediate source destination operation notStack
  cases hAction : (execute_ITYPE immediate source destination operation).run state <;>
    simpa [hAction] using frame

/-- The generated dispatcher preserves `x2` for a non-stack shift-immediate destination. -/
theorem executeSHIFTIOPDispatchPreservesStackPointer (state : State) (shiftAmount : BitVec 6)
    (source destination : regidx) (operation : sop) (notStack : destination ≠ stackPointer) :
    (match (execute (.SHIFTIOP (shiftAmount, source, destination, operation))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_SHIFTIOP shiftAmount source destination operation).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame :=
    execute_SHIFTIOP_preserves_stack_pointer state shiftAmount source destination operation notStack
  cases hAction : (execute_SHIFTIOP shiftAmount source destination operation).run state <;>
    simpa [hAction] using frame

/-- The generated dispatcher preserves `x2` for a non-stack multiplication destination. -/
theorem executeMULDispatchPreservesStackPointer (state : State)
    (source2 source1 destination : regidx) (operation : mul_op) (notStack : destination ≠ stackPointer) :
    (match (execute (.MUL (source2, source1, destination, operation))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_MUL source2 source1 destination operation).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame := execute_MUL_preserves_stack_pointer state source2 source1 destination operation notStack
  cases hAction : (execute_MUL source2 source1 destination operation).run state <;>
    simpa [hAction] using frame

/-- The generated dispatcher preserves `x2` for a non-stack division destination. -/
theorem executeDIVDispatchPreservesStackPointer (state : State)
    (source2 source1 destination : regidx) (isUnsigned : Bool) (notStack : destination ≠ stackPointer) :
    (match (execute (.DIV (source2, source1, destination, isUnsigned))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_DIV source2 source1 destination isUnsigned).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame := execute_DIV_preserves_stack_pointer state source2 source1 destination isUnsigned notStack
  cases hAction : (execute_DIV source2 source1 destination isUnsigned).run state <;>
    simpa [hAction] using frame

/-- The generated dispatcher preserves `x2` for a non-stack remainder destination. -/
theorem executeREMDispatchPreservesStackPointer (state : State)
    (source2 source1 destination : regidx) (isUnsigned : Bool) (notStack : destination ≠ stackPointer) :
    (match (execute (.REM (source2, source1, destination, isUnsigned))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_REM source2 source1 destination isUnsigned).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame := execute_REM_preserves_stack_pointer state source2 source1 destination isUnsigned notStack
  cases hAction : (execute_REM source2 source1 destination isUnsigned).run state <;>
    simpa [hAction] using frame

end BinaryFv.RISCV
