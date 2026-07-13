import ShaFv.RISCV.ABI

namespace ShaFv.RISCV

/-- A file-backed memory segment, independent of any executable file format. -/
structure LoadSegment where
  virtualAddress : Nat
  initialBytes : ByteArray
  memorySize : Nat
  flags : Nat

namespace LoadSegment

def fileSize (segment : LoadSegment) : Nat :=
  segment.initialBytes.size

def initialEndAddress (segment : LoadSegment) : Nat :=
  segment.virtualAddress + segment.fileSize

def endAddress (segment : LoadSegment) : Nat :=
  segment.virtualAddress + segment.memorySize

def containsInitialByte (segment : LoadSegment) (address : Nat) : Bool :=
  decide (segment.virtualAddress ≤ address ∧ address < segment.initialEndAddress)

def containsMemoryByte (segment : LoadSegment) (address : Nat) : Bool :=
  decide (segment.virtualAddress ≤ address ∧ address < segment.endAddress)

def containsMemoryRange (segment : LoadSegment) (address size : Nat) : Bool :=
  decide (segment.virtualAddress ≤ address ∧ address + size ≤ segment.endAddress)

def executable (segment : LoadSegment) : Bool :=
  segment.flags &&& 1 != 0

def readByte? (segment : LoadSegment) (address : Nat) : Option UInt8 :=
  if segment.containsMemoryByte address then
    some ((segment.initialBytes[address - segment.virtualAddress]?).getD 0)
  else
    none

end LoadSegment

/-- The loadable memory image supplied to the ISA model. -/
structure ProgramImage where
  segments : Array LoadSegment

namespace ProgramImage

def segmentAt? (image : ProgramImage) (address : Nat) : Option LoadSegment :=
  image.segments.toList.find? fun segment => segment.containsMemoryByte address

def readByte? (image : ProgramImage) (address : Nat) : Option UInt8 :=
  match image.segmentAt? address with
  | some segment => segment.readByte? address
  | none => none

def readNatLE? (image : ProgramImage) (address : Nat) : Nat → Option Nat
  | 0 => some 0
  | width + 1 => do
    let byte ← image.readByte? address
    let rest ← image.readNatLE? (address + 1) width
    pure (byte.toNat + 256 * rest)

def readU32LE? (image : ProgramImage) (address : Nat) : Option Nat :=
  image.readNatLE? address 4

end ProgramImage

end ShaFv.RISCV
