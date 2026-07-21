import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 17 is valid against the canonical decoded control-flow graph. -/
theorem chunk_17 : sliceValidC chunk17 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
