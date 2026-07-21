import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 24 is valid against the canonical decoded control-flow graph. -/
theorem chunk_24 : sliceValidC chunk24 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
