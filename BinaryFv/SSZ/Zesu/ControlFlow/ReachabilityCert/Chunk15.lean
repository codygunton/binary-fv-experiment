import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 15 is valid against the canonical decoded control-flow graph. -/
theorem chunk_15 : sliceValidC chunk15 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
