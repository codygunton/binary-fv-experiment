import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 11 is valid against the canonical decoded control-flow graph. -/
theorem chunk_11 : sliceValidC chunk11 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
