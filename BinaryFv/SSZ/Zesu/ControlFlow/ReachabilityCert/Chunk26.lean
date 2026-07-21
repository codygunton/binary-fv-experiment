import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 26 is valid against the canonical decoded control-flow graph. -/
theorem chunk_26 : sliceValidC chunk26 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
