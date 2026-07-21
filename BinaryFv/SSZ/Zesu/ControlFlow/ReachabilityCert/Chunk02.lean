import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 02 is valid against the canonical decoded control-flow graph. -/
theorem chunk_02 : sliceValidC chunk02 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
