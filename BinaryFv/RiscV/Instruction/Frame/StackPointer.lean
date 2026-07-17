import BinaryFv.RiscV.Instruction.Frame.ControlDispatch
import BinaryFv.RiscV.Instruction.Frame.IntegerDispatch
import BinaryFv.RiscV.Instruction.Frame.Load
import BinaryFv.RiscV.Instruction.Frame.Store

namespace BinaryFv.RiscV

open LeanRV64DExecutable.Functions
open Register

/-! ## Static x2-frame classification of decoded instructions -/

/-- Generated instruction constructors retained by the closed static inventory. -/
inductive ExecutionConstructor where
  | illegal | compressedIllegal | landingPad | utype | jal | jalr | btype | itype | shiftIop
  | rtype | load | store | addiw | rtypew | shiftiwop | fenceTso | fence | ecall | mret | sret
  | ebreak | wfi | sfenceVma | mul | div | rem | mulw | divw | remw
  deriving BEq, DecidableEq, Repr
def executionConstructor : instruction → ExecutionConstructor
  | .ILLEGAL _ => .illegal | .C_ILLEGAL _ => .compressedIllegal | .LPAD _ => .landingPad
  | .UTYPE _ => .utype | .JAL _ => .jal | .JALR _ => .jalr | .BTYPE _ => .btype
  | .ITYPE _ => .itype | .SHIFTIOP _ => .shiftIop | .RTYPE _ => .rtype | .LOAD _ => .load
  | .STORE _ => .store | .ADDIW _ => .addiw | .RTYPEW _ => .rtypew | .SHIFTIWOP _ => .shiftiwop
  | .FENCE_TSO _ => .fenceTso | .FENCE _ => .fence | .ECALL _ => .ecall | .MRET _ => .mret
  | .SRET _ => .sret | .EBREAK _ => .ebreak | .WFI _ => .wfi | .SFENCE_VMA _ => .sfenceVma
  | .MUL _ => .mul | .DIV _ => .div | .REM _ => .rem | .MULW _ => .mulw | .DIVW _ => .divw
  | .REMW _ => .remw
/-- `framed` has an exported all-outcome `x2` frame; stack adjustment changes `x2` by design. -/
inductive X2FrameStatus where
  | framed (constructor : ExecutionConstructor) | stackAdjustment
  | uncovered (constructor : ExecutionConstructor)
  deriving BEq, DecidableEq, Repr
def nonStackDestination (destination : regidx) : Bool := destination != stackPointer
def frameForDestination (constructor : ExecutionConstructor) (destination : regidx) :
    X2FrameStatus :=
  if nonStackDestination destination then .framed constructor else .uncovered constructor
/--
Map generated constructors to the already exported frame families: UTYPE, RTYPE, ITYPE, SHIFTIOP,
MUL/DIV/REM, BTYPE, non-`x2` JAL/JALR, LOAD, STORE, and FENCE/FENCE_TSO. All other constructors
and unexpected `x2` writes remain uncovered; this is not semantic reachability, arbitrary-state
execution coverage, or a stack-bound claim.
-/
def x2FrameStatus (decoded : instruction) : X2FrameStatus :=
  if (instructionStackDelta? decoded).isSome then .stackAdjustment else
  match decoded with
  | .UTYPE (_, destination, _) => frameForDestination .utype destination
  | .JAL (_, destination) => frameForDestination .jal destination
  | .JALR (_, _, destination) => frameForDestination .jalr destination
  | .BTYPE _ => .framed .btype
  | .ITYPE (_, _, destination, _) => frameForDestination .itype destination
  | .SHIFTIOP (_, _, destination, _) => frameForDestination .shiftIop destination
  | .RTYPE (_, _, destination, _) => frameForDestination .rtype destination
  | .LOAD (_, _, destination, _, _) => frameForDestination .load destination
  | .STORE _ => .framed .store
  | .FENCE_TSO _ => .framed .fenceTso
  | .FENCE _ => .framed .fence
  | .MUL (_, _, destination, _) => frameForDestination .mul destination
  | .DIV (_, _, destination, _) => frameForDestination .div destination
  | .REM (_, _, destination, _) => frameForDestination .rem destination
  | _ => .uncovered (executionConstructor decoded)
def X2FrameStatus.isClassified : X2FrameStatus → Bool
  | .framed _ | .stackAdjustment => true
  | .uncovered _ => false

/-- A generated instruction preserves the observed stack-pointer register on every outcome. -/
def RuntimeX2Frame (decoded : instruction) : Prop :=
  PreservesStackPointer (execute decoded)

private theorem runtime_x2_frame_of_pointwise (decoded : instruction)
    (frame : ∀ (state : BinaryFv.RiscV.State),
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
  | .LOAD (immediate, source, destination, isUnsigned, width) =>
    have status : frameForDestination .load destination = .framed constructor := by
      simpa [x2FrameStatus, instructionStackDelta?] using framed
    have notStack := destination_ne_of_framed .load constructor destination status
    apply runtime_x2_frame_of_pointwise
    intro state
    exact
      executeLOADDispatchPreservesStackPointer state immediate source destination isUnsigned width
        notStack
  | .STORE (immediate, sourceData, sourceAddress, width) =>
    apply runtime_x2_frame_of_pointwise
    intro state
    exact executeSTOREDispatchPreservesStackPointer state immediate sourceData sourceAddress width
  | .ILLEGAL _ | .C_ILLEGAL _ | .LPAD _ | .ADDIW _ | .RTYPEW _ | .SHIFTIWOP _
    | .ECALL _ | .MRET _ | .SRET _ | .EBREAK _ | .WFI _ | .SFENCE_VMA _ | .MULW _
    | .DIVW _ | .REMW _ =>
    simp [x2FrameStatus, instructionStackDelta?, executionConstructor] at framed

end BinaryFv.RiscV
