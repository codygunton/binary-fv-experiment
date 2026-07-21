import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 10 is valid against the canonical decoded control-flow graph. -/
theorem chunk_10 : sliceValidC chunk10 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
