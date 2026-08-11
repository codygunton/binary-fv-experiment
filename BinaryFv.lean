import BinaryFv.Binary
import BinaryFv.RiscV

/-!
# `BinaryFv`

Root of the binary formal-verification library. It imports the architecture-independent binary layer,
and the generic RISC-V layer. Concrete verification targets and extracted specifications are separate
packages so replacing either does not contaminate this reusable library.
-/
