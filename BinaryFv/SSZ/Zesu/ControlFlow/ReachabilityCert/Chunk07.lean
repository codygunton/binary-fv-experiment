import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- Chunk 07 is valid against the canonical decoded control-flow graph. -/
theorem chunk_07 : sliceValidC chunk07 = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
