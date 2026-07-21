import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 16 is valid against the canonical decoded control-flow graph. -/
theorem chunk_16 : sliceValidC chunk16 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
