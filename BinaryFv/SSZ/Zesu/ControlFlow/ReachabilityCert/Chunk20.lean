import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 20 is valid against the canonical decoded control-flow graph. -/
theorem chunk_20 : sliceValidC chunk20 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
