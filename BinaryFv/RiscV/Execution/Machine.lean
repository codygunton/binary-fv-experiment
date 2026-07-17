import BinaryFv.RiscV.Model.State

/-!
# Generic machine configuration
-/

namespace BinaryFv.RiscV

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register

def initializeIntegerRegisters : SailM Unit := do
  writeReg x3 (0 : BitVec 64)
  writeReg x4 (0 : BitVec 64)
  writeReg x5 (0 : BitVec 64)
  writeReg x6 (0 : BitVec 64)
  writeReg x7 (0 : BitVec 64)
  writeReg x8 (0 : BitVec 64)
  writeReg x9 (0 : BitVec 64)
  writeReg x10 (0 : BitVec 64)
  writeReg x11 (0 : BitVec 64)
  writeReg x12 (0 : BitVec 64)
  writeReg x13 (0 : BitVec 64)
  writeReg x14 (0 : BitVec 64)
  writeReg x15 (0 : BitVec 64)
  writeReg x16 (0 : BitVec 64)
  writeReg x17 (0 : BitVec 64)
  writeReg x18 (0 : BitVec 64)
  writeReg x19 (0 : BitVec 64)
  writeReg x20 (0 : BitVec 64)
  writeReg x21 (0 : BitVec 64)
  writeReg x22 (0 : BitVec 64)
  writeReg x23 (0 : BitVec 64)
  writeReg x24 (0 : BitVec 64)
  writeReg x25 (0 : BitVec 64)
  writeReg x26 (0 : BitVec 64)
  writeReg x27 (0 : BitVec 64)
  writeReg x28 (0 : BitVec 64)
  writeReg x29 (0 : BitVec 64)
  writeReg x30 (0 : BitVec 64)
  writeReg x31 (0 : BitVec 64)

end BinaryFv.RiscV
