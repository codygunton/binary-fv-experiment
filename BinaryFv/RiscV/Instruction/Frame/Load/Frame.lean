import BinaryFv.RiscV.Instruction.Frame.Load.Translation

/-!
# The LOAD stack-pointer frame

The two exported conclusions: the generated `execute_LOAD`, and its dispatch, leave `x2` alone.
-/

namespace BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType

/-- A generated LOAD preserves `x2` when its destination is not the stack pointer. -/
theorem execute_LOAD_preserves_stack_pointer (immediate : BitVec 12)
    (source destination : regidx) (isUnsigned : Bool) (width : Nat)
    (notStack : destination ≠ stackPointer) :
    PreservesStackPointer (execute_LOAD immediate source destination isUnsigned width) := by
  unfold execute_LOAD
  apply load_preserves_bind (Sail.assert (width ≤b LeanRV64DExecutable.Functions.xlen_bytes)
    "extensions/I/base_insts.sail:289.28-289.29")
  · exact load_preserves_assert _ _
  · intro _
    apply load_preserves_bind
    · exact load_preserves_vmem_read_load_data source (sign_extend (m := 64) immediate) width
    · intro result
      cases result with
      | Err error => exact load_preserves_pure error
      | Ok data =>
        apply load_preserves_bind (wX_bits destination (extend_value isUnsigned data))
        · exact load_preserves_wX_bits destination _ notStack
        · intro _
          exact load_preserves_pure RETIRE_SUCCESS

/-- The generated dispatcher preserves `x2` for every LOAD outcome off the stack destination. -/
theorem executeLOADDispatchPreservesStackPointer (state : State) (immediate : BitVec 12)
    (source destination : regidx) (isUnsigned : Bool) (width : Nat)
    (notStack : destination ≠ stackPointer) :
    (match (execute (.LOAD (immediate, source, destination, isUnsigned, width))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_LOAD immediate source destination isUnsigned width).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame :=
    execute_LOAD_preserves_stack_pointer immediate source destination isUnsigned width notStack
  unfold PreservesStackPointer at frame
  cases hAction : (execute_LOAD immediate source destination isUnsigned width).run state <;>
    simpa [hAction] using frame state

end BinaryFv.RiscV
