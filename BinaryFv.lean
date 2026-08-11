import BinaryFv.Binary
import LeanRV64DExecutable

/-!
# `BinaryFv`

Root of the SSZ binary-verification library. It imports the architecture-independent binary layer and
the extracted RISC-V semantics. Historical target-specific proof utilities remain available through
their explicit module names, but are not dependencies of the new compliance theorem.
-/
