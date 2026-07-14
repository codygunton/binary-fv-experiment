import BinaryFv.Keccak.FrameCoverage
import BinaryFv.RISCV.ControlDispatchFrame
import BinaryFv.RISCV.IntegerDispatchFrame

namespace BinaryFv.Keccak

open BinaryFv.RISCV
open LeanRV64DExecutable.Functions
open Register

/-- A generated instruction preserves the observed stack-pointer register on every outcome. -/
def RuntimeX2Frame (decoded : instruction) : Prop :=
  PreservesStackPointer (execute decoded)

private theorem runtime_x2_frame_of_pointwise (decoded : instruction)
    (frame : ∀ (state : BinaryFv.RISCV.State),
      (match (execute decoded).run state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = state.regs.get? x2) :
    RuntimeX2Frame decoded := by
  unfold RuntimeX2Frame PreservesStackPointer
  intro state
  cases hAction : (execute decoded).run state <;>
    simpa [hAction] using frame state

private theorem non_stack_destination_stack_pointer :
    nonStackDestination stackPointer = false := by
  change (stackPointer != stackPointer) = false
  decide

private theorem destination_ne_of_framed (expected actual : ExecutionConstructor)
    (destination : regidx)
    (frame : frameForDestination expected destination = .framed actual) :
    destination ≠ stackPointer := by
  intro equal
  subst destination
  rw [frameForDestination, non_stack_destination_stack_pointer] at frame
  cases frame

private theorem itype_destination_ne_of_framed (immediate : BitVec 12)
    (source destination : regidx) (operation : iop) (constructor : ExecutionConstructor)
    (framed : x2FrameStatus (.ITYPE (immediate, source, destination, operation)) =
      .framed constructor) :
    destination ≠ stackPointer := by
  intro equal
  subst destination
  have stackEquals : (stackPointer == stackPointer) = true := by
    decide
  have stackNotEquals : (stackPointer != stackPointer) = false := by
    decide
  cases operation with
  | ADDI =>
    cases hSource : source == stackPointer <;>
      simp [x2FrameStatus, instructionStackDelta?, frameForDestination, nonStackDestination,
        hSource, stackEquals, stackNotEquals] at framed
  | SLTI | SLTIU | XORI | ORI | ANDI =>
    simp [x2FrameStatus, instructionStackDelta?, frameForDestination, nonStackDestination,
      stackNotEquals] at framed

/-- Existing static `framed` labels carry the corresponding generated dispatcher contract. -/
theorem runtime_x2_frame_of_static_framed (decoded : instruction)
    (constructor : ExecutionConstructor)
    (framed : x2FrameStatus decoded = .framed constructor) : RuntimeX2Frame decoded := by
  match decoded with
  | .UTYPE (immediate, destination, operation) =>
    have status : frameForDestination .utype destination = .framed constructor := by
      simpa [x2FrameStatus, instructionStackDelta?] using framed
    have notStack := destination_ne_of_framed .utype constructor destination status
    apply runtime_x2_frame_of_pointwise
    intro state
    exact executeUTYPEDispatchPreservesStackPointer state immediate destination operation notStack
  | .JAL (immediate, destination) =>
    have status : frameForDestination .jal destination = .framed constructor := by
      simpa [x2FrameStatus, instructionStackDelta?] using framed
    have notStack := destination_ne_of_framed .jal constructor destination status
    apply runtime_x2_frame_of_pointwise
    intro state
    exact executeJALDispatchPreservesStackPointer state immediate destination notStack
  | .JALR (immediate, source, destination) =>
    have status : frameForDestination .jalr destination = .framed constructor := by
      simpa [x2FrameStatus, instructionStackDelta?] using framed
    have notStack := destination_ne_of_framed .jalr constructor destination status
    apply runtime_x2_frame_of_pointwise
    intro state
    exact executeJALRDispatchPreservesStackPointer state immediate source destination notStack
  | .BTYPE (immediate, source2, source1, operation) =>
    apply runtime_x2_frame_of_pointwise
    intro state
    exact executeBTYPEDispatchPreservesStackPointer state immediate source2 source1 operation
  | .ITYPE (immediate, source, destination, operation) =>
    have notStack :=
      itype_destination_ne_of_framed immediate source destination operation constructor framed
    apply runtime_x2_frame_of_pointwise
    intro state
    exact
      executeITYPEDispatchPreservesStackPointer state immediate source destination operation
        notStack
  | .SHIFTIOP (shiftAmount, source, destination, operation) =>
    have status : frameForDestination .shiftIop destination = .framed constructor := by
      simpa [x2FrameStatus, instructionStackDelta?] using framed
    have notStack := destination_ne_of_framed .shiftIop constructor destination status
    apply runtime_x2_frame_of_pointwise
    intro state
    exact
      executeSHIFTIOPDispatchPreservesStackPointer state shiftAmount source destination operation
        notStack
  | .RTYPE (source2, source1, destination, operation) =>
    have status : frameForDestination .rtype destination = .framed constructor := by
      simpa [x2FrameStatus, instructionStackDelta?] using framed
    have notStack := destination_ne_of_framed .rtype constructor destination status
    apply runtime_x2_frame_of_pointwise
    intro state
    exact
      executeRTYPEDispatchPreservesStackPointer state source2 source1 destination operation notStack
  | .FENCE_TSO _ =>
    apply runtime_x2_frame_of_pointwise
    intro state
    exact executeFENCE_TSODispatchPreservesStackPointer state
  | .FENCE (fm, pred, succ, source, destination) =>
    apply runtime_x2_frame_of_pointwise
    intro state
    exact executeFENCEDispatchPreservesStackPointer state fm pred succ source destination
  | .MUL (source2, source1, destination, operation) =>
    have status : frameForDestination .mul destination = .framed constructor := by
      simpa [x2FrameStatus, instructionStackDelta?] using framed
    have notStack := destination_ne_of_framed .mul constructor destination status
    apply runtime_x2_frame_of_pointwise
    intro state
    exact
      executeMULDispatchPreservesStackPointer state source2 source1 destination operation notStack
  | .DIV (source2, source1, destination, isUnsigned) =>
    have status : frameForDestination .div destination = .framed constructor := by
      simpa [x2FrameStatus, instructionStackDelta?] using framed
    have notStack := destination_ne_of_framed .div constructor destination status
    apply runtime_x2_frame_of_pointwise
    intro state
    exact
      executeDIVDispatchPreservesStackPointer state source2 source1 destination isUnsigned notStack
  | .REM (source2, source1, destination, isUnsigned) =>
    have status : frameForDestination .rem destination = .framed constructor := by
      simpa [x2FrameStatus, instructionStackDelta?] using framed
    have notStack := destination_ne_of_framed .rem constructor destination status
    apply runtime_x2_frame_of_pointwise
    intro state
    exact
      executeREMDispatchPreservesStackPointer state source2 source1 destination isUnsigned notStack
  | .LOAD payload =>
    by_cases h : nonStackDestination payload.2.2.fst = true
    · simp [x2FrameStatus, instructionStackDelta?, h] at framed
    · simp [x2FrameStatus, instructionStackDelta?, h] at framed
  | .STORE _ =>
    simp [x2FrameStatus, instructionStackDelta?] at framed
  | .ILLEGAL _ | .C_ILLEGAL _ | .LPAD _ | .ADDIW _ | .RTYPEW _ | .SHIFTIWOP _
    | .ECALL _ | .MRET _ | .SRET _ | .EBREAK _ | .WFI _ | .SFENCE_VMA _ | .MULW _
    | .DIVW _ | .REMW _ =>
    simp [x2FrameStatus, instructionStackDelta?, executionConstructor] at framed

end BinaryFv.Keccak
