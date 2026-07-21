import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 08 is valid against the canonical decoded control-flow graph. -/
theorem chunk_08 : sliceValidC chunk08 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
