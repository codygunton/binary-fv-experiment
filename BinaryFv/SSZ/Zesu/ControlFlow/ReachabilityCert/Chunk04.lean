import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 04 is valid against the canonical decoded control-flow graph. -/
theorem chunk_04 : sliceValidC chunk04 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
