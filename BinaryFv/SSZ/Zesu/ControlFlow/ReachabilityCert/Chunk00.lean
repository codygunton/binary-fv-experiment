import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 00 is valid against the canonical decoded control-flow graph. -/
theorem chunk_00 : sliceValidC chunk00 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
