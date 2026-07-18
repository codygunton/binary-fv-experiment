import BinaryFv.RiscV.Logic.ImageMemory
import BinaryFv.RiscV.ELF.Elf64

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

/-- Check only the bytes supplied by the executable file, not its logical zero-filled BSS tail. -/
def LoadSegment.checkFileBytesUnchanged (segment : LoadSegment) : Nat → SailM Bool
  | 0 => pure true
  | count + 1 => do
    let index := count
    let expected := BitVec.ofNat 8 ((segment.initialBytes[index]?).getD 0).toNat
    let actual ← readByte (segment.virtualAddress + index)
    if actual == expected then segment.checkFileBytesUnchanged count else pure false

def ProgramImage.checkFileSegmentsUnchanged : List LoadSegment → SailM Bool
  | [] => pure true
  | segment :: remaining => do
    if (← segment.checkFileBytesUnchanged segment.fileSize) then
      checkFileSegmentsUnchanged remaining
    else
      pure false

def ProgramImage.checkFileBytesUnchanged (image : ProgramImage) : SailM Bool :=
  ProgramImage.checkFileSegmentsUnchanged image.segments.toList

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

/-- Materialize only the bytes physically present in a load segment's backing file. -/
def loadFileSegment (segment : LoadSegment) : SailM Unit :=
  loadSegmentPrefix segment segment.fileSize

def loadFileSegments : List LoadSegment → SailM Unit
  | [] => pure ()
  | segment :: remaining => do
    loadFileSegment segment
    loadFileSegments remaining

/-- Load every ELF-backed byte but leave logical BSS absent from Sail's sparse memory. -/
def loadFileBackedImage (image : ProgramImage) : SailM Unit :=
  loadFileSegments image.segments.toList.reverse

def loadZeroFillRanges : List AddressRange → SailM Unit
  | [] => pure ()
  | range :: remaining => do
    loadSegmentPrefix
      { virtualAddress := range.start, initialBytes := .empty, memorySize := range.size, flags := 0 }
      range.size
    loadZeroFillRanges remaining

/--
Load a validated sparse plan: ELF file bytes plus only its explicitly requested BSS ranges. Unlike
`loadProgramImage`, this never expands an entire zero-filled ELF tail into Sail's sparse memory.
-/
def loadSparseProgramImage (plan : ProgramImage.SparseLoadPlan) : SailM Unit := do
  loadFileBackedImage plan.image
  loadZeroFillRanges plan.zeroFillRanges.toList

/-- Build the sparse file-backed loader directly from a parser-validated ELF. -/
def Elf64.sparseLoader (elf : Elf64) (zeroFillRanges : Array AddressRange) :
    Except ProgramImage.SparseLoadError (SailM Unit) := do
  let plan ← elf.programImage.sparseLoadPlan? zeroFillRanges
  pure (loadSparseProgramImage plan)

end BinaryFv.RiscV
