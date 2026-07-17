import BinaryFv.RiscV.Logic.ImageMemory

open PreSail
open LeanRV64DExecutable.Functions
open Register

namespace BinaryFv.Binary

/-- Executable finite check used only by closed concrete Sail regressions. -/
def LoadSegment.checkUnchanged (segment : LoadSegment) : Nat → SailM Bool
  | 0 => pure true
  | count + 1 => do
    let index := count
    let expected := BitVec.ofNat 8 ((segment.initialBytes[index]?).getD 0).toNat
    let actual ← readByte (segment.virtualAddress + index)
    if actual == expected then segment.checkUnchanged count else pure false

def ProgramImage.checkSegmentsUnchanged : List LoadSegment → SailM Bool
  | [] => pure true
  | segment :: remaining => do
    if (← segment.checkUnchanged segment.memorySize) then
      checkSegmentsUnchanged remaining
    else
      pure false

def ProgramImage.checkUnchanged (image : ProgramImage) : SailM Bool :=
  ProgramImage.checkSegmentsUnchanged image.segments.toList

end BinaryFv.Binary

namespace BinaryFv.RiscV

open BinaryFv.Binary

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

end BinaryFv.RiscV
