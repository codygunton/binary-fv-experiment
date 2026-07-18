import BinaryFv.Binary.ProgramImage

namespace BinaryFv.Binary

private abbrev sparseTestImage : ProgramImage := {
  segments := #[
    { virtualAddress := 100,
      initialBytes := ([1, 2, 3, 4] : List UInt8).toByteArray,
      memorySize := 16,
      flags := 0 },
    { virtualAddress := 108,
      initialBytes := ([5, 6, 7, 8] : List UInt8).toByteArray,
      memorySize := 8,
      flags := 0 },
  ]
}

private abbrev sparseLoadPlanAccepted (image : ProgramImage) (ranges : Array AddressRange) : Bool :=
  match image.sparseLoadPlan? ranges with
  | .ok _ => true
  | .error _ => false

/-- A subrange of the first segment's BSS tail that touches no file-backed range is accepted. -/
example :
    sparseTestImage.containsZeroFillRange { start := 104, size := 2 } = true ∧
      sparseLoadPlanAccepted sparseTestImage #[{ start := 104, size := 2 }] = true := by
  simp [sparseTestImage, sparseLoadPlanAccepted, ProgramImage.sparseLoadPlan?,
    ProgramImage.containsZeroFillRange, ProgramImage.disjointFromFileBackedRanges,
    LoadSegment.containsZeroFillRange, LoadSegment.zeroFillRange, LoadSegment.fileBackedRange,
    LoadSegment.initialEndAddress, LoadSegment.fileSize, AddressRange.stop]

/-- A range outside every BSS tail is rejected by both the predicate and sparse-plan constructor. -/
example :
    sparseTestImage.containsZeroFillRange { start := 96, size := 2 } = false ∧
      sparseLoadPlanAccepted sparseTestImage #[{ start := 96, size := 2 }] = false := by
  simp [sparseLoadPlanAccepted, ProgramImage.sparseLoadPlan?,
    ProgramImage.containsZeroFillRange, ProgramImage.disjointFromFileBackedRanges,
    LoadSegment.containsZeroFillRange, LoadSegment.zeroFillRange, LoadSegment.fileBackedRange,
    LoadSegment.initialEndAddress, LoadSegment.fileSize, AddressRange.stop]

/-- A BSS-tail subrange that overlaps another segment's file bytes is rejected. -/
example :
    sparseTestImage.containsZeroFillRange { start := 109, size := 2 } = false ∧
      sparseLoadPlanAccepted sparseTestImage #[{ start := 109, size := 2 }] = false := by
  simp [sparseLoadPlanAccepted, ProgramImage.sparseLoadPlan?,
    ProgramImage.containsZeroFillRange, ProgramImage.disjointFromFileBackedRanges,
    LoadSegment.containsZeroFillRange, LoadSegment.zeroFillRange, LoadSegment.fileBackedRange,
    LoadSegment.initialEndAddress, LoadSegment.fileSize, AddressRange.stop]

end BinaryFv.Binary
