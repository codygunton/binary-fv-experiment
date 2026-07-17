import BinaryFv.SSZ.Root
import BinaryFv.SSZ.SpecBridge.Decode

/-!
# `BinaryFv.SSZ`

Umbrella for the Amsterdam V4 SSZ target. The specification bridge is pure; the Zesu artifact,
machine execution, and proof layers will be added beneath this target without introducing a reverse
dependency into the generic RISC-V library.
-/
