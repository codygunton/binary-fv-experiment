import LeanRV64DExecutable
import BinaryFv.RISCV.Address
import BinaryFv.RISCV.ProgramImage

namespace BinaryFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register

abbrev State := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

def initialState : State := default

def initializeModel : SailM Unit :=
  sail_model_init ()

/-- The selected Reth path uses RV64M multiplication and division instructions. -/
def enableMExtension : SailM Unit := do
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 12 12 1#1)

def loadSegmentPrefix (segment : LoadSegment) : Nat → SailM Unit
  | 0 => pure ()
  | count + 1 => do
    let index := count
    let byte := (segment.initialBytes[index]?).getD 0
    let _ ← PreSail.writeByte (segment.virtualAddress + index) (BitVec.ofNat 8 byte.toNat)
    loadSegmentPrefix segment count

def loadSegment (segment : LoadSegment) : SailM Unit :=
  loadSegmentPrefix segment segment.memorySize

def loadSegments : List LoadSegment → SailM Unit
  | [] => pure ()
  | segment :: remaining => do
    loadSegment segment
    loadSegments remaining

/-- Load every byte of a parsed image, including zero-fill after each file-backed segment. -/
def loadProgramImage (image : ProgramImage) : SailM Unit :=
  loadSegments image.segments.toList.reverse

end BinaryFv.RISCV
