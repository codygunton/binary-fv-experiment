import BinaryFv.RiscV.Model.State

/-!
# Generic sparse-memory I/O

Bulk reads and writes over the generated Sail sparse memory, independent of any target.
-/

namespace BinaryFv.RiscV

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register

def loadBytes (base : Nat) (bytes : ByteArray) : SailM Unit := do
  for h : index in [:bytes.size] do
    writeByte (base + index) (BitVec.ofNat 8 bytes[index].toNat)

def readByteArray (base length : Nat) : SailM ByteArray := do
  let mut result := ByteArray.emptyWithCapacity length
  for index in [:length] do
    result := result.push (UInt8.ofNat (← readByte (base + index)).toNat)
  pure result

/-- Materialize a sparse Sail memory range with a known byte value. -/
def loadFilledBytes (base count : Nat) (value : UInt8) : SailM Unit := do
  for index in [:count] do
    writeByte (base + index) (BitVec.ofNat 8 value.toNat)

/-- Materialize zeroed sparse memory required by the generated Sail memory model. -/
def loadZeroBytes (base count : Nat) : SailM Unit :=
  loadFilledBytes base count 0

end BinaryFv.RiscV
