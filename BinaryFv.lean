import BinaryFv.Binary
import BinaryFv.RiscV
import BinaryFv.Keccak

/-!
# `BinaryFv`

Root of the binary formal-verification library. It imports the three supported umbrellas, in layer
order: the architecture-independent binary layer, the generic RISC-V layer, and the Keccak target
layer built on top of them.
-/
