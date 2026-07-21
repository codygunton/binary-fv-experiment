import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 09 is valid against the canonical decoded control-flow graph. -/
theorem chunk_09 : sliceValidC chunk09 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
