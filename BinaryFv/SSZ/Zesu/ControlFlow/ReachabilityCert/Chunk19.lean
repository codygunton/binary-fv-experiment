import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 19 is valid against the canonical decoded control-flow graph. -/
theorem chunk_19 : sliceValidC chunk19 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
