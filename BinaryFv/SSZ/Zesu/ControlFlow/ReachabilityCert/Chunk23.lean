import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 23 is valid against the canonical decoded control-flow graph. -/
theorem chunk_23 : sliceValidC chunk23 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
