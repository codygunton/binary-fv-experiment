import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 18 is valid against the canonical decoded control-flow graph. -/
theorem chunk_18 : sliceValidC chunk18 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
