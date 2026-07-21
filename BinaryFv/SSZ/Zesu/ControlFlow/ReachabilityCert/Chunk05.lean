import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 05 is valid against the canonical decoded control-flow graph. -/
theorem chunk_05 : sliceValidC chunk05 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
