import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 06 is valid against the canonical decoded control-flow graph. -/
theorem chunk_06 : sliceValidC chunk06 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
