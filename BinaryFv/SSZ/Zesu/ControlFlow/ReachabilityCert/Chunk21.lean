import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 21 is valid against the canonical decoded control-flow graph. -/
theorem chunk_21 : sliceValidC chunk21 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
