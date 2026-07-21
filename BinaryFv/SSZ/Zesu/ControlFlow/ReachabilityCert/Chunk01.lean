import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 01 is valid against the canonical decoded control-flow graph. -/
theorem chunk_01 : sliceValidC chunk01 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
