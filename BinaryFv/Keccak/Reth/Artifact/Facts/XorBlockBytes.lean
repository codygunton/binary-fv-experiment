import BinaryFv.Keccak.Reth.Artifact.Facts.ImageByte
import BinaryFv.RiscV.ELF.Decode

/-!
# Closed image-byte facts for `xor_block`

Closed statements about one fixed input, discharged by `native_decide` under the approved
fixed-artifact exception.
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary
open BinaryFv.RiscV

/-- Closed parser byte facts: the image's little-endian bytes at `0x10c6c` are `13 06 80 08`. -/
theorem imageByte_10c6c :
    imageByte 0x10c6c 0x13 = true ∧ imageByte (0x10c6c + 1) 0x06 = true ∧
      imageByte (0x10c6c + 2) 0x80 = true ∧ imageByte (0x10c6c + 3) 0x08 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c70` are `63 0c 06 06`. -/
theorem imageByte_10c70 :
    imageByte 0x10c70 0x63 = true ∧ imageByte (0x10c70 + 1) 0x0c = true ∧
      imageByte (0x10c70 + 2) 0x06 = true ∧ imageByte (0x10c70 + 3) 0x06 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c74` are `83 c6 15 00`. -/
theorem imageByte_10c74 :
    imageByte 0x10c74 0x83 = true ∧ imageByte (0x10c74 + 1) 0xc6 = true ∧
      imageByte (0x10c74 + 2) 0x15 = true ∧ imageByte (0x10c74 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c78` are `03 c7 25 00`. -/
theorem imageByte_10c78 :
    imageByte 0x10c78 0x03 = true ∧ imageByte (0x10c78 + 1) 0xc7 = true ∧
      imageByte (0x10c78 + 2) 0x25 = true ∧ imageByte (0x10c78 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c7c` are `83 c7 35 00`. -/
theorem imageByte_10c7c :
    imageByte 0x10c7c 0x83 = true ∧ imageByte (0x10c7c + 1) 0xc7 = true ∧
      imageByte (0x10c7c + 2) 0x35 = true ∧ imageByte (0x10c7c + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c80` are `03 c8 05 00`. -/
theorem imageByte_10c80 :
    imageByte 0x10c80 0x03 = true ∧ imageByte (0x10c80 + 1) 0xc8 = true ∧
      imageByte (0x10c80 + 2) 0x05 = true ∧ imageByte (0x10c80 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c84` are `93 96 86 00`. -/
theorem imageByte_10c84 :
    imageByte 0x10c84 0x93 = true ∧ imageByte (0x10c84 + 1) 0x96 = true ∧
      imageByte (0x10c84 + 2) 0x86 = true ∧ imageByte (0x10c84 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c88` are `13 17 07 01`. -/
theorem imageByte_10c88 :
    imageByte 0x10c88 0x13 = true ∧ imageByte (0x10c88 + 1) 0x17 = true ∧
      imageByte (0x10c88 + 2) 0x07 = true ∧ imageByte (0x10c88 + 3) 0x01 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c8c` are `93 97 87 01`. -/
theorem imageByte_10c8c :
    imageByte 0x10c8c 0x93 = true ∧ imageByte (0x10c8c + 1) 0x97 = true ∧
      imageByte (0x10c8c + 2) 0x87 = true ∧ imageByte (0x10c8c + 3) 0x01 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c90` are `b3 e6 06 01`. -/
theorem imageByte_10c90 :
    imageByte 0x10c90 0xb3 = true ∧ imageByte (0x10c90 + 1) 0xe6 = true ∧
      imageByte (0x10c90 + 2) 0x06 = true ∧ imageByte (0x10c90 + 3) 0x01 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c94` are `33 e7 e7 00`. -/
theorem imageByte_10c94 :
    imageByte 0x10c94 0x33 = true ∧ imageByte (0x10c94 + 1) 0xe7 = true ∧
      imageByte (0x10c94 + 2) 0xe7 = true ∧ imageByte (0x10c94 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c98` are `83 c7 55 00`. -/
theorem imageByte_10c98 :
    imageByte 0x10c98 0x83 = true ∧ imageByte (0x10c98 + 1) 0xc7 = true ∧
      imageByte (0x10c98 + 2) 0x55 = true ∧ imageByte (0x10c98 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c9c` are `03 c8 45 00`. -/
theorem imageByte_10c9c :
    imageByte 0x10c9c 0x03 = true ∧ imageByte (0x10c9c + 1) 0xc8 = true ∧
      imageByte (0x10c9c + 2) 0x45 = true ∧ imageByte (0x10c9c + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10ca0` are `83 c8 65 00`. -/
theorem imageByte_10ca0 :
    imageByte 0x10ca0 0x83 = true ∧ imageByte (0x10ca0 + 1) 0xc8 = true ∧
      imageByte (0x10ca0 + 2) 0x65 = true ∧ imageByte (0x10ca0 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10ca4` are `83 c2 75 00`. -/
theorem imageByte_10ca4 :
    imageByte 0x10ca4 0x83 = true ∧ imageByte (0x10ca4 + 1) 0xc2 = true ∧
      imageByte (0x10ca4 + 2) 0x75 = true ∧ imageByte (0x10ca4 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10ca8` are `93 97 87 00`. -/
theorem imageByte_10ca8 :
    imageByte 0x10ca8 0x93 = true ∧ imageByte (0x10ca8 + 1) 0x97 = true ∧
      imageByte (0x10ca8 + 2) 0x87 = true ∧ imageByte (0x10ca8 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10cac` are `b3 e7 07 01`. -/
theorem imageByte_10cac :
    imageByte 0x10cac 0xb3 = true ∧ imageByte (0x10cac + 1) 0xe7 = true ∧
      imageByte (0x10cac + 2) 0x07 = true ∧ imageByte (0x10cac + 3) 0x01 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10cb0` are `93 98 08 01`. -/
theorem imageByte_10cb0 :
    imageByte 0x10cb0 0x93 = true ∧ imageByte (0x10cb0 + 1) 0x98 = true ∧
      imageByte (0x10cb0 + 2) 0x08 = true ∧ imageByte (0x10cb0 + 3) 0x01 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10cb4` are `93 92 82 01`. -/
theorem imageByte_10cb4 :
    imageByte 0x10cb4 0x93 = true ∧ imageByte (0x10cb4 + 1) 0x92 = true ∧
      imageByte (0x10cb4 + 2) 0x82 = true ∧ imageByte (0x10cb4 + 3) 0x01 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10cb8` are `33 e8 12 01`. -/
theorem imageByte_10cb8 :
    imageByte 0x10cb8 0x33 = true ∧ imageByte (0x10cb8 + 1) 0xe8 = true ∧
      imageByte (0x10cb8 + 2) 0x12 = true ∧ imageByte (0x10cb8 + 3) 0x01 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10cbc` are `13 06 86 ff`. -/
theorem imageByte_10cbc :
    imageByte 0x10cbc 0x13 = true ∧ imageByte (0x10cbc + 1) 0x06 = true ∧
      imageByte (0x10cbc + 2) 0x86 = true ∧ imageByte (0x10cbc + 3) 0xff = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10cc0` are `93 85 85 00`. -/
theorem imageByte_10cc0 :
    imageByte 0x10cc0 0x93 = true ∧ imageByte (0x10cc0 + 1) 0x85 = true ∧
      imageByte (0x10cc0 + 2) 0x85 = true ∧ imageByte (0x10cc0 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10cc4` are `b3 66 d7 00`. -/
theorem imageByte_10cc4 :
    imageByte 0x10cc4 0xb3 = true ∧ imageByte (0x10cc4 + 1) 0x66 = true ∧
      imageByte (0x10cc4 + 2) 0xd7 = true ∧ imageByte (0x10cc4 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10cc8` are `03 37 05 00`. -/
theorem imageByte_10cc8 :
    imageByte 0x10cc8 0x03 = true ∧ imageByte (0x10cc8 + 1) 0x37 = true ∧
      imageByte (0x10cc8 + 2) 0x05 = true ∧ imageByte (0x10cc8 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10ccc` are `b3 67 f8 00`. -/
theorem imageByte_10ccc :
    imageByte 0x10ccc 0xb3 = true ∧ imageByte (0x10ccc + 1) 0x67 = true ∧
      imageByte (0x10ccc + 2) 0xf8 = true ∧ imageByte (0x10ccc + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10cd0` are `93 97 07 02`. -/
theorem imageByte_10cd0 :
    imageByte 0x10cd0 0x93 = true ∧ imageByte (0x10cd0 + 1) 0x97 = true ∧
      imageByte (0x10cd0 + 2) 0x07 = true ∧ imageByte (0x10cd0 + 3) 0x02 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10cd4` are `b3 e6 d7 00`. -/
theorem imageByte_10cd4 :
    imageByte 0x10cd4 0xb3 = true ∧ imageByte (0x10cd4 + 1) 0xe6 = true ∧
      imageByte (0x10cd4 + 2) 0xd7 = true ∧ imageByte (0x10cd4 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10cd8` are `b3 46 d7 00`. -/
theorem imageByte_10cd8 :
    imageByte 0x10cd8 0xb3 = true ∧ imageByte (0x10cd8 + 1) 0x46 = true ∧
      imageByte (0x10cd8 + 2) 0xd7 = true ∧ imageByte (0x10cd8 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10cdc` are `23 30 d5 00`. -/
theorem imageByte_10cdc :
    imageByte 0x10cdc 0x23 = true ∧ imageByte (0x10cdc + 1) 0x30 = true ∧
      imageByte (0x10cdc + 2) 0xd5 = true ∧ imageByte (0x10cdc + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10ce0` are `13 05 85 00`. -/
theorem imageByte_10ce0 :
    imageByte 0x10ce0 0x13 = true ∧ imageByte (0x10ce0 + 1) 0x05 = true ∧
      imageByte (0x10ce0 + 2) 0x85 = true ∧ imageByte (0x10ce0 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10ce4` are `e3 18 06 f8`. -/
theorem imageByte_10ce4 :
    imageByte 0x10ce4 0xe3 = true ∧ imageByte (0x10ce4 + 1) 0x18 = true ∧
      imageByte (0x10ce4 + 2) 0x06 = true ∧ imageByte (0x10ce4 + 3) 0xf8 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10ce8` are `67 80 00 00`. -/
theorem imageByte_10ce8 :
    imageByte 0x10ce8 0x67 = true ∧ imageByte (0x10ce8 + 1) 0x80 = true ∧
      imageByte (0x10ce8 + 2) 0x00 = true ∧ imageByte (0x10ce8 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end BinaryFv.Keccak
