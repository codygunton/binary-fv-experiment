import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 03 is valid against the canonical decoded control-flow graph. -/
theorem chunk_03 : sliceValidC chunk03 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
