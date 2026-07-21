import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 14 is valid against the canonical decoded control-flow graph. -/
theorem chunk_14 : sliceValidC chunk14 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
