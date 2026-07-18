import BinaryFv.SSZ.SpecBridge.Decode
import BinaryFv.SSZ.Zesu.Artifact.Image
import BinaryFv.SSZ.Zesu.Artifact.Layout
import BinaryFv.SSZ.Zesu.Interface
import BinaryFv.SSZ.Root

/-!
# `BinaryFv.SSZ`

Umbrella for the Amsterdam V4 SSZ target. The specification bridge is pure; the Zesu artifact,
machine execution, and proof layers will be added beneath this target without introducing a reverse
dependency into the generic RISC-V library.
-/
