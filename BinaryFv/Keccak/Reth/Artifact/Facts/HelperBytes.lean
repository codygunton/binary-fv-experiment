import BinaryFv.Keccak.Reth.Artifact.Facts.ImageByte
import BinaryFv.RiscV.ELF.Decode

/-!
# Closed image-byte facts for the memory helpers

Each fact says the pinned image holds a given byte at a given address. Closed statements about one
fixed input, discharged by `native_decide` under the approved fixed-artifact exception.
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary
open BinaryFv.RiscV

/-- Closed parser byte facts: the image's little-endian bytes at `0x10d18` are `93 07 00 00`. -/
theorem imageByte_10d18 :
    imageByte 0x10d18 0x93 = true ∧ imageByte (0x10d18 + 1) 0x07 = true ∧
      imageByte (0x10d18 + 2) 0x00 = true ∧ imageByte (0x10d18 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d1c` are `63 94 c7 00`. -/
theorem imageByte_10d1c :
    imageByte 0x10d1c 0x63 = true ∧ imageByte (0x10d1c + 1) 0x94 = true ∧
      imageByte (0x10d1c + 2) 0xc7 = true ∧ imageByte (0x10d1c + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d20` are `67 80 00 00`. -/
theorem imageByte_10d20 :
    imageByte 0x10d20 0x67 = true ∧ imageByte (0x10d20 + 1) 0x80 = true ∧
      imageByte (0x10d20 + 2) 0x00 = true ∧ imageByte (0x10d20 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d24` are `b3 86 f5 00`. -/
theorem imageByte_10d24 :
    imageByte 0x10d24 0xb3 = true ∧ imageByte (0x10d24 + 1) 0x86 = true ∧
      imageByte (0x10d24 + 2) 0xf5 = true ∧ imageByte (0x10d24 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d28` are `83 c6 06 00`. -/
theorem imageByte_10d28 :
    imageByte 0x10d28 0x83 = true ∧ imageByte (0x10d28 + 1) 0xc6 = true ∧
      imageByte (0x10d28 + 2) 0x06 = true ∧ imageByte (0x10d28 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d2c` are `33 07 f5 00`. -/
theorem imageByte_10d2c :
    imageByte 0x10d2c 0x33 = true ∧ imageByte (0x10d2c + 1) 0x07 = true ∧
      imageByte (0x10d2c + 2) 0xf5 = true ∧ imageByte (0x10d2c + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d30` are `93 87 17 00`. -/
theorem imageByte_10d30 :
    imageByte 0x10d30 0x93 = true ∧ imageByte (0x10d30 + 1) 0x87 = true ∧
      imageByte (0x10d30 + 2) 0x17 = true ∧ imageByte (0x10d30 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d34` are `23 00 d7 00`. -/
theorem imageByte_10d34 :
    imageByte 0x10d34 0x23 = true ∧ imageByte (0x10d34 + 1) 0x00 = true ∧
      imageByte (0x10d34 + 2) 0xd7 = true ∧ imageByte (0x10d34 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d38` are `6f f0 5f fe`. -/
theorem imageByte_10d38 :
    imageByte 0x10d38 0x6f = true ∧ imageByte (0x10d38 + 1) 0xf0 = true ∧
      imageByte (0x10d38 + 2) 0x5f = true ∧ imageByte (0x10d38 + 3) 0xfe = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d3c` are `93 07 00 00`. -/
theorem imageByte_10d3c :
    imageByte 0x10d3c 0x93 = true ∧ imageByte (0x10d3c + 1) 0x07 = true ∧
      imageByte (0x10d3c + 2) 0x00 = true ∧ imageByte (0x10d3c + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d40` are `63 94 c7 00`. -/
theorem imageByte_10d40 :
    imageByte 0x10d40 0x63 = true ∧ imageByte (0x10d40 + 1) 0x94 = true ∧
      imageByte (0x10d40 + 2) 0xc7 = true ∧ imageByte (0x10d40 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d44` are `67 80 00 00`. -/
theorem imageByte_10d44 :
    imageByte 0x10d44 0x67 = true ∧ imageByte (0x10d44 + 1) 0x80 = true ∧
      imageByte (0x10d44 + 2) 0x00 = true ∧ imageByte (0x10d44 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d48` are `33 07 f5 00`. -/
theorem imageByte_10d48 :
    imageByte 0x10d48 0x33 = true ∧ imageByte (0x10d48 + 1) 0x07 = true ∧
      imageByte (0x10d48 + 2) 0xf5 = true ∧ imageByte (0x10d48 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d4c` are `23 00 b7 00`. -/
theorem imageByte_10d4c :
    imageByte 0x10d4c 0x23 = true ∧ imageByte (0x10d4c + 1) 0x00 = true ∧
      imageByte (0x10d4c + 2) 0xb7 = true ∧ imageByte (0x10d4c + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d50` are `93 87 17 00`. -/
theorem imageByte_10d50 :
    imageByte 0x10d50 0x93 = true ∧ imageByte (0x10d50 + 1) 0x87 = true ∧
      imageByte (0x10d50 + 2) 0x17 = true ∧ imageByte (0x10d50 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10d54` are `6f f0 df fe`. -/
theorem imageByte_10d54 :
    imageByte 0x10d54 0x6f = true ∧ imageByte (0x10d54 + 1) 0xf0 = true ∧
      imageByte (0x10d54 + 2) 0xdf = true ∧ imageByte (0x10d54 + 3) 0xfe = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c44` are `13 87 05 00`. -/
theorem imageByte_10c44 :
    imageByte 0x10c44 0x13 = true ∧ imageByte (0x10c44 + 1) 0x87 = true ∧
      imageByte (0x10c44 + 2) 0x05 = true ∧ imageByte (0x10c44 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c48` are `63 9a d5 00`. -/
theorem imageByte_10c48 :
    imageByte 0x10c48 0x63 = true ∧ imageByte (0x10c48 + 1) 0x9a = true ∧
      imageByte (0x10c48 + 2) 0xd5 = true ∧ imageByte (0x10c48 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c4c` are `93 05 06 00`. -/
theorem imageByte_10c4c :
    imageByte 0x10c4c 0x93 = true ∧ imageByte (0x10c4c + 1) 0x05 = true ∧
      imageByte (0x10c4c + 2) 0x06 = true ∧ imageByte (0x10c4c + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c50` are `13 06 07 00`. -/
theorem imageByte_10c50 :
    imageByte 0x10c50 0x13 = true ∧ imageByte (0x10c50 + 1) 0x06 = true ∧
      imageByte (0x10c50 + 2) 0x07 = true ∧ imageByte (0x10c50 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c54` are `17 03 00 00`. -/
theorem imageByte_10c54 :
    imageByte 0x10c54 0x17 = true ∧ imageByte (0x10c54 + 1) 0x03 = true ∧
      imageByte (0x10c54 + 2) 0x00 = true ∧ imageByte (0x10c54 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c58` are `67 00 43 0c`. -/
theorem imageByte_10c58 :
    imageByte 0x10c58 0x67 = true ∧ imageByte (0x10c58 + 1) 0x00 = true ∧
      imageByte (0x10c58 + 2) 0x43 = true ∧ imageByte (0x10c58 + 3) 0x0c = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c5c` are `13 05 07 00`. -/
theorem imageByte_10c5c :
    imageByte 0x10c5c 0x13 = true ∧ imageByte (0x10c5c + 1) 0x05 = true ∧
      imageByte (0x10c5c + 2) 0x07 = true ∧ imageByte (0x10c5c + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c60` are `93 85 06 00`. -/
theorem imageByte_10c60 :
    imageByte 0x10c60 0x93 = true ∧ imageByte (0x10c60 + 1) 0x85 = true ∧
      imageByte (0x10c60 + 2) 0x06 = true ∧ imageByte (0x10c60 + 3) 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c64` are `97 f0 ff ff`. -/
theorem imageByte_10c64 :
    imageByte 0x10c64 0x97 = true ∧ imageByte (0x10c64 + 1) 0xf0 = true ∧
      imageByte (0x10c64 + 2) 0xff = true ∧ imageByte (0x10c64 + 3) 0xff = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
/-- Closed parser byte facts: the image's little-endian bytes at `0x10c68` are `e7 80 c0 48`. -/
theorem imageByte_10c68 :
    imageByte 0x10c68 0xe7 = true ∧ imageByte (0x10c68 + 1) 0x80 = true ∧
      imageByte (0x10c68 + 2) 0xc0 = true ∧ imageByte (0x10c68 + 3) 0x48 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end BinaryFv.Keccak
