import BinaryFv.SSZ.Zesu.Execution.Observer
import SizzLean.Spec.Deserialize

namespace BinaryFv.SSZ.Zesu.Proof

open BinaryFv.SSZ.Zesu.Execution

/-- Materialize one guarded Sail-memory range as the byte array consumed by the pinned spec. -/
def observeByteArray? (state : BinaryFv.RiscV.State) (base length : Nat) : Option ByteArray :=
  (observeBytes? state base length).map fun bytes => ByteArray.mk bytes.toArray

/-- A guarded Sail-memory range materializes exactly the byte array supplied to SizzLean. -/
theorem observe_byte_array_of_memory (state : BinaryFv.RiscV.State) (base : Nat)
    (bytes : List UInt8) (memory : MemoryListBytes state base bytes) :
    observeByteArray? state base bytes.length = some (ByteArray.mk bytes.toArray) := by
  unfold observeByteArray?
  rw [observe_bytes_of_memory state base bytes memory]
  rfl

/-- Primitive little-endian observations call the pinned SizzLean readers directly. -/
def observeUInt8At? (state : BinaryFv.RiscV.State) (base length offset : Nat) : Option UInt8 := do
  let bytes ← observeByteArray? state base length
  SizzLean.Spec.readUInt8At bytes offset

def observeUInt16LE? (state : BinaryFv.RiscV.State) (base length offset : Nat) : Option UInt16 := do
  let bytes ← observeByteArray? state base length
  SizzLean.Spec.readUInt16LE bytes offset

def observeUInt32LE? (state : BinaryFv.RiscV.State) (base length offset : Nat) : Option UInt32 := do
  let bytes ← observeByteArray? state base length
  SizzLean.Spec.readUInt32LE bytes offset

def observeUInt64LE? (state : BinaryFv.RiscV.State) (base length offset : Nat) : Option UInt64 := do
  let bytes ← observeByteArray? state base length
  SizzLean.Spec.readUInt64LE bytes offset

end BinaryFv.SSZ.Zesu.Proof
