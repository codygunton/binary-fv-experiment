import BinaryFv.Binary
import BinaryFv.RiscV
import BinaryFv.Specs
import BinaryFv.Zesu

/-!
# `BinaryFv`

Root of the binary formal-verification library. It imports the architecture-independent binary layer,
the generic RISC-V layer, implementation-independent specifications, and the concrete Zesu
verification target built on top of them.
-/
