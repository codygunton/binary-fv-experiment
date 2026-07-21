import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 22 is valid against the canonical decoded control-flow graph. -/
theorem chunk_22 : sliceValidC chunk22 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
