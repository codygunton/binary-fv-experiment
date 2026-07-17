import BinaryFv.Binary.Address
import BinaryFv.Binary.ProgramImage

/-!
# `BinaryFv.Binary`

Umbrella for the architecture-independent binary layer: half-open address ranges and the
file-format-independent loadable program image. Nothing here knows about RISC-V, and nothing here
may depend on `BinaryFv.RiscV` or `BinaryFv.Keccak`.
-/
