import BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert.Check

namespace BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert

/-- The entry decoder address is inside the materialized reachable set. -/
theorem entry_contained : entryContained = true := by native_decide

/-- The canonical ELF parses and decodes. -/
theorem controlFlow_isSome_bool : controlFlow?.isSome = true := by native_decide

/-- The entry symbol resolves. -/
theorem entryFunction_isSome_bool : entryFunction?.isSome = true := by native_decide

end BinaryFv.SSZ.Zesu.ControlFlow.ReachabilityCert
