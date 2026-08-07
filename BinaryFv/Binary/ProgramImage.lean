import BinaryFv.Binary.Address

namespace BinaryFv.Binary

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

/-- The half-open range `[virtualAddress, virtualAddress + fileSize)` backed by ELF file bytes. -/
def fileBackedRange (segment : LoadSegment) : AddressRange :=
  { start := segment.virtualAddress, size := segment.fileSize }

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

/-- Read only a byte present in the ELF file, never the logical zero-fill tail. -/
def readFileByte? (segment : LoadSegment) (address : Nat) : Option UInt8 :=
  if segment.containsInitialByte address then
    segment.initialBytes[address - segment.virtualAddress]?
  else
    none

/-- The zero-filled part of a load segment, excluding all file-backed bytes. -/
def zeroFillRange (segment : LoadSegment) : AddressRange :=
  { start := segment.initialEndAddress, size := segment.memorySize - segment.fileSize }

/-- Whether a requested range lies wholly in this segment's zero-filled tail. -/
def containsZeroFillRange (segment : LoadSegment) (range : AddressRange) : Bool :=
  decide (segment.zeroFillRange.start ≤ range.start ∧ range.stop ≤ segment.zeroFillRange.stop)

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

/-- A readable address lies inside one of the image's load segments. Stated generically, so a proof
about a concrete image never has to unfold the parsed segment data to use it. -/
theorem readByte?_mem_segment {image : ProgramImage} {address : Nat} {byte : UInt8}
    (h : image.readByte? address = some byte) :
    ∃ segment ∈ image.segments.toList,
      segment.virtualAddress ≤ address ∧ address < segment.virtualAddress + segment.memorySize := by
  unfold readByte? at h
  cases hfind : image.segmentAt? address with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some segment =>
      have hfind' : image.segments.toList.find?
          (fun segment => segment.containsMemoryByte address) = some segment := hfind
      have hmem : segment ∈ image.segments.toList :=
        List.mem_of_find?_eq_some (p := fun s : LoadSegment => s.containsMemoryByte address) hfind'
      have hcontains : segment.containsMemoryByte address = true :=
        List.find?_some (p := fun s : LoadSegment => s.containsMemoryByte address) hfind'
      rw [LoadSegment.containsMemoryByte, decide_eq_true_eq] at hcontains
      exact ⟨segment, hmem, hcontains.1, hcontains.2⟩

def fileSegmentAt? (image : ProgramImage) (address : Nat) : Option LoadSegment :=
  image.segments.toList.find? fun segment => segment.containsInitialByte address

/-- Read a byte backed by the ELF file, distinguishing it from logical BSS zero-fill. -/
def readFileByte? (image : ProgramImage) (address : Nat) : Option UInt8 :=
  match image.fileSegmentAt? address with
  | some segment => segment.readFileByte? address
  | none => none

/-- A file-backed address lies inside one segment's file-backed window
`[virtualAddress, initialEndAddress)`. The file-byte companion to `readByte?_mem_segment`: stated
generically, so a proof about a concrete image bounds its file addresses without unfolding the parsed
segment data — the intended use is to confine `fileBytesLoadedFaithfully`'s addresses below a runner range
so a later loader's frame preserves them. -/
theorem readFileByte?_mem_segment {image : ProgramImage} {address : Nat} {byte : UInt8}
    (h : image.readFileByte? address = some byte) :
    ∃ segment ∈ image.segments.toList,
      segment.virtualAddress ≤ address ∧ address < segment.initialEndAddress := by
  unfold readFileByte? at h
  cases hfind : image.fileSegmentAt? address with
  | none => rw [hfind] at h; exact absurd h (by simp)
  | some segment =>
      have hfind' : image.segments.toList.find?
          (fun segment => segment.containsInitialByte address) = some segment := hfind
      have hmem : segment ∈ image.segments.toList :=
        List.mem_of_find?_eq_some (p := fun s : LoadSegment => s.containsInitialByte address) hfind'
      have hcontains : segment.containsInitialByte address = true :=
        List.find?_some (p := fun s : LoadSegment => s.containsInitialByte address) hfind'
      rw [LoadSegment.containsInitialByte, decide_eq_true_eq] at hcontains
      exact ⟨segment, hmem, hcontains.1, hcontains.2⟩

def readNatLE? (image : ProgramImage) (address : Nat) : Nat → Option Nat
  | 0 => some 0
  | width + 1 => do
    let byte ← image.readByte? address
    let rest ← image.readNatLE? (address + 1) width
    pure (byte.toNat + 256 * rest)

def readU32LE? (image : ProgramImage) (address : Nat) : Option Nat :=
  image.readNatLE? address 4

/-- Read one file-or-zero-fill-backed 64-bit little-endian word from the image. -/
def readU64LE? (image : ProgramImage) (address : Nat) : Option Nat :=
  image.readNatLE? address 8

def readFileNatLE? (image : ProgramImage) (address : Nat) : Nat → Option Nat
  | 0 => some 0
  | width + 1 => do
    let byte ← image.readFileByte? address
    let rest ← image.readFileNatLE? (address + 1) width
    pure (byte.toNat + 256 * rest)

def readFileU32LE? (image : ProgramImage) (address : Nat) : Option Nat :=
  image.readFileNatLE? address 4

/-- Whether a range is disjoint from every segment's half-open file-backed range. -/
def disjointFromFileBackedRanges (image : ProgramImage) (range : AddressRange) : Bool :=
  image.segments.all fun segment =>
    decide (range.stop ≤ segment.fileBackedRange.start ∨
      segment.fileBackedRange.stop ≤ range.start)

/--
Whether a range can be safely materialized as zero-filled BSS for this image. It must be contained
in one segment's BSS tail and disjoint from every segment's file-backed range. This deliberately
does not rely on an ELF parser having established that segments are pairwise disjoint.
-/
def containsZeroFillRange (image : ProgramImage) (range : AddressRange) : Bool :=
  image.segments.any (fun segment => segment.containsZeroFillRange range) &&
    image.disjointFromFileBackedRanges range

inductive SparseLoadError where
  | requestedRangeOutsideZeroFill
  deriving DecidableEq, Repr

/--
A file-backed image together with exactly the BSS ranges that execution is allowed to materialize.
The proof field requires each range to be in a BSS tail and disjoint from every segment's file
bytes, without depending on a parser-specific segment-disjointness invariant.
-/
structure SparseLoadPlan where
  image : ProgramImage
  zeroFillRanges : Array AddressRange
  zeroFillRangesValid : zeroFillRanges.all image.containsZeroFillRange = true

/--
Construct a sparse plan only when every requested range passes the generic BSS/file-range check.
-/
def sparseLoadPlan? (image : ProgramImage) (zeroFillRanges : Array AddressRange) :
    Except SparseLoadError SparseLoadPlan :=
  if valid : zeroFillRanges.all image.containsZeroFillRange then
    .ok { image, zeroFillRanges, zeroFillRangesValid := valid }
  else
    .error .requestedRangeOutsideZeroFill

end ProgramImage

end BinaryFv.Binary
