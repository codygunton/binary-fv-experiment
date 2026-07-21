import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 12 is valid against the canonical decoded control-flow graph. -/
theorem chunk_12 : sliceValidC chunk12 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
