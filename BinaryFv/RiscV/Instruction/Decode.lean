import BinaryFv.RiscV.Model.State

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The generated external decoder is definitionally the generated instruction decoder. -/
theorem extDecode_eq (word : BitVec 32) :
    ext_decode word = encdec_backwards word := by
  rfl

end BinaryFv.RiscV
