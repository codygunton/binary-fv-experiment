import BinaryFv.RiscV.Decode

namespace BinaryFv.RiscV

open LeanRV64DExecutable.Functions

/-- The architectural integer register used as the direct-call stack pointer. -/
def stackPointer : regidx := .Regidx 2#5

/-- The integer destination register written by a decoded instruction, when it has one. -/
def instructionDestination? : instruction → Option regidx
  | .UTYPE (_, destination, _) => some destination
  | .JAL (_, destination) => some destination
  | .JALR (_, _, destination) => some destination
  | .ITYPE (_, _, destination, _) => some destination
  | .SHIFTIOP (_, _, destination, _) => some destination
  | .RTYPE (_, _, destination, _) => some destination
  | .LOAD (_, _, destination, _, _) => some destination
  | .ADDIW (_, _, destination) => some destination
  | .RTYPEW (_, _, destination, _) => some destination
  | .SHIFTIWOP (_, _, destination, _) => some destination
  | .MUL (_, _, destination, _) => some destination
  | .DIV (_, _, destination, _) => some destination
  | .REM (_, _, destination, _) => some destination
  | .MULW (_, _, destination) => some destination
  | .DIVW (_, _, destination, _) => some destination
  | .REMW (_, _, destination, _) => some destination
  | _ => none

/-- The signed stack-pointer delta of the generated `addi sp, sp, immediate` form. -/
def instructionStackDelta? : instruction → Option Int
  | .ITYPE (immediate, source, destination, .ADDI) =>
      if source == stackPointer && destination == stackPointer then some immediate.toInt else none
  | _ => none

def instructionWritesStackPointer (decoded : instruction) : Bool :=
  match instructionDestination? decoded with
  | some destination => destination == stackPointer
  | none => false

/-- Every stack-pointer write must be an explicitly classified stack adjustment. -/
def instructionStackWriteClassified (decoded : instruction) : Bool :=
  !instructionWritesStackPointer decoded || (instructionStackDelta? decoded).isSome

def DecodedWord.stackDelta? (decoded : DecodedWord) : Option Int :=
  instructionStackDelta? decoded.instruction

def DecodedWord.writesStackPointer (decoded : DecodedWord) : Bool :=
  instructionWritesStackPointer decoded.instruction

def DecodedWord.stackWriteClassified (decoded : DecodedWord) : Bool :=
  instructionStackWriteClassified decoded.instruction

end BinaryFv.RiscV
