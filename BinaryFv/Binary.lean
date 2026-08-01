import BinaryFv.Binary.Address
import BinaryFv.Binary.Elfling
import BinaryFv.Binary.ProgramImage

/-!
# `BinaryFv.Binary`

Umbrella for the architecture-independent binary layer: half-open address ranges, the
file-format-independent loadable program image, and the source-associated Elfling decomposition.
Nothing here knows about RISC-V, and nothing here
may depend on `BinaryFv.RiscV` or `BinaryFv.Zesu`.
-/
