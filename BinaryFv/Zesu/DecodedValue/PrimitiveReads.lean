import BinaryFv.Zesu.DecodedValue.Observers
import SizzLean.Spec.Deserialize

namespace BinaryFv.Zesu.DecodedValue

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

/-- Each guarded integer observation is the corresponding pinned SizzLean operation on the same bytes. -/
theorem observe_uint8_at_of_memory (state : BinaryFv.RiscV.State) (base offset : Nat)
    (bytes : List UInt8) (memory : MemoryListBytes state base bytes) :
    observeUInt8At? state base bytes.length offset =
      SizzLean.Spec.readUInt8At (ByteArray.mk bytes.toArray) offset := by
  unfold observeUInt8At?
  rw [observe_byte_array_of_memory state base bytes memory]
  rfl

theorem observe_uint16_le_of_memory (state : BinaryFv.RiscV.State) (base offset : Nat)
    (bytes : List UInt8) (memory : MemoryListBytes state base bytes) :
    observeUInt16LE? state base bytes.length offset =
      SizzLean.Spec.readUInt16LE (ByteArray.mk bytes.toArray) offset := by
  unfold observeUInt16LE?
  rw [observe_byte_array_of_memory state base bytes memory]
  rfl

theorem observe_uint32_le_of_memory (state : BinaryFv.RiscV.State) (base offset : Nat)
    (bytes : List UInt8) (memory : MemoryListBytes state base bytes) :
    observeUInt32LE? state base bytes.length offset =
      SizzLean.Spec.readUInt32LE (ByteArray.mk bytes.toArray) offset := by
  unfold observeUInt32LE?
  rw [observe_byte_array_of_memory state base bytes memory]
  rfl

theorem observe_uint64_le_of_memory (state : BinaryFv.RiscV.State) (base offset : Nat)
    (bytes : List UInt8) (memory : MemoryListBytes state base bytes) :
    observeUInt64LE? state base bytes.length offset =
      SizzLean.Spec.readUInt64LE (ByteArray.mk bytes.toArray) offset := by
  unfold observeUInt64LE?
  rw [observe_byte_array_of_memory state base bytes memory]
  rfl

/-- The guarded primitive observers inherit the pinned readers' exact bounds failures. -/
theorem observe_uint8_at_out_of_bounds (state : BinaryFv.RiscV.State) (base offset : Nat)
    (bytes : List UInt8) (memory : MemoryListBytes state base bytes)
    (outOfBounds : bytes.length ≤ offset) :
    observeUInt8At? state base bytes.length offset = none := by
  rw [observe_uint8_at_of_memory state base offset bytes memory]
  have size : (ByteArray.mk bytes.toArray).size = bytes.length := by
    change bytes.toArray.size = bytes.length
    simp
  have guard : ¬offset < (ByteArray.mk bytes.toArray).size := by omega
  unfold SizzLean.Spec.readUInt8At
  simp [guard]

theorem observe_uint16_le_out_of_bounds (state : BinaryFv.RiscV.State) (base offset : Nat)
    (bytes : List UInt8) (memory : MemoryListBytes state base bytes)
    (outOfBounds : bytes.length < offset + 2) :
    observeUInt16LE? state base bytes.length offset = none := by
  rw [observe_uint16_le_of_memory state base offset bytes memory]
  have size : (ByteArray.mk bytes.toArray).size = bytes.length := by
    change bytes.toArray.size = bytes.length
    simp
  have guard : ¬offset + 2 ≤ (ByteArray.mk bytes.toArray).size := by omega
  unfold SizzLean.Spec.readUInt16LE
  simp [guard]

theorem observe_uint32_le_out_of_bounds (state : BinaryFv.RiscV.State) (base offset : Nat)
    (bytes : List UInt8) (memory : MemoryListBytes state base bytes)
    (outOfBounds : bytes.length < offset + 4) :
    observeUInt32LE? state base bytes.length offset = none := by
  rw [observe_uint32_le_of_memory state base offset bytes memory]
  have size : (ByteArray.mk bytes.toArray).size = bytes.length := by
    change bytes.toArray.size = bytes.length
    simp
  have guard : ¬offset + 4 ≤ (ByteArray.mk bytes.toArray).size := by omega
  unfold SizzLean.Spec.readUInt32LE
  simp [guard]

theorem observe_uint64_le_out_of_bounds (state : BinaryFv.RiscV.State) (base offset : Nat)
    (bytes : List UInt8) (memory : MemoryListBytes state base bytes)
    (outOfBounds : bytes.length < offset + 8) :
    observeUInt64LE? state base bytes.length offset = none := by
  rw [observe_uint64_le_of_memory state base offset bytes memory]
  have size : (ByteArray.mk bytes.toArray).size = bytes.length := by
    change bytes.toArray.size = bytes.length
    simp
  have guard : ¬offset + 8 ≤ (ByteArray.mk bytes.toArray).size := by omega
  unfold SizzLean.Spec.readUInt64LE
  simp [guard]

end BinaryFv.Zesu.DecodedValue
