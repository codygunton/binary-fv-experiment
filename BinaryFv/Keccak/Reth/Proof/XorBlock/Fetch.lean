import BinaryFv.Keccak.Reth.Artifact.Facts.XorBlockBytes
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.Platform.Fetch

/-!
# Fetch lifts for `xor_block`
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary
open BinaryFv.RiscV

/-- Derive the exact four fetch bytes at `0x10c6c` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `13 06 80 08` there. -/
theorem fetchBytesAt_10c6c (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c6c) 0x13#8 0x06#8 0x80#8 0x08#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c6c
  have pcNat : (BitVec.ofNat 64 0x10c6c).toNat = 0x10c6c := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c6c 0x13 (imageByte_readByte image imageEq 0x10c6c 0x13 h0)
  · simpa using loaded (0x10c6c + 1) 0x06 (imageByte_readByte image imageEq (0x10c6c + 1) 0x06 h1)
  · simpa using loaded (0x10c6c + 2) 0x80 (imageByte_readByte image imageEq (0x10c6c + 2) 0x80 h2)
  · simpa using loaded (0x10c6c + 3) 0x08 (imageByte_readByte image imageEq (0x10c6c + 3) 0x08 h3)
/-- Derive the exact four fetch bytes at `0x10c70` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `63 0c 06 06` there. -/
theorem fetchBytesAt_10c70 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c70) 0x63#8 0x0c#8 0x06#8 0x06#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c70
  have pcNat : (BitVec.ofNat 64 0x10c70).toNat = 0x10c70 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c70 0x63 (imageByte_readByte image imageEq 0x10c70 0x63 h0)
  · simpa using loaded (0x10c70 + 1) 0x0c (imageByte_readByte image imageEq (0x10c70 + 1) 0x0c h1)
  · simpa using loaded (0x10c70 + 2) 0x06 (imageByte_readByte image imageEq (0x10c70 + 2) 0x06 h2)
  · simpa using loaded (0x10c70 + 3) 0x06 (imageByte_readByte image imageEq (0x10c70 + 3) 0x06 h3)
/-- Derive the exact four fetch bytes at `0x10c74` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `83 c6 15 00` there. -/
theorem fetchBytesAt_10c74 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c74) 0x83#8 0xc6#8 0x15#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c74
  have pcNat : (BitVec.ofNat 64 0x10c74).toNat = 0x10c74 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c74 0x83 (imageByte_readByte image imageEq 0x10c74 0x83 h0)
  · simpa using loaded (0x10c74 + 1) 0xc6 (imageByte_readByte image imageEq (0x10c74 + 1) 0xc6 h1)
  · simpa using loaded (0x10c74 + 2) 0x15 (imageByte_readByte image imageEq (0x10c74 + 2) 0x15 h2)
  · simpa using loaded (0x10c74 + 3) 0x00 (imageByte_readByte image imageEq (0x10c74 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c78` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `03 c7 25 00` there. -/
theorem fetchBytesAt_10c78 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c78) 0x03#8 0xc7#8 0x25#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c78
  have pcNat : (BitVec.ofNat 64 0x10c78).toNat = 0x10c78 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c78 0x03 (imageByte_readByte image imageEq 0x10c78 0x03 h0)
  · simpa using loaded (0x10c78 + 1) 0xc7 (imageByte_readByte image imageEq (0x10c78 + 1) 0xc7 h1)
  · simpa using loaded (0x10c78 + 2) 0x25 (imageByte_readByte image imageEq (0x10c78 + 2) 0x25 h2)
  · simpa using loaded (0x10c78 + 3) 0x00 (imageByte_readByte image imageEq (0x10c78 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c7c` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `83 c7 35 00` there. -/
theorem fetchBytesAt_10c7c (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c7c) 0x83#8 0xc7#8 0x35#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c7c
  have pcNat : (BitVec.ofNat 64 0x10c7c).toNat = 0x10c7c := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c7c 0x83 (imageByte_readByte image imageEq 0x10c7c 0x83 h0)
  · simpa using loaded (0x10c7c + 1) 0xc7 (imageByte_readByte image imageEq (0x10c7c + 1) 0xc7 h1)
  · simpa using loaded (0x10c7c + 2) 0x35 (imageByte_readByte image imageEq (0x10c7c + 2) 0x35 h2)
  · simpa using loaded (0x10c7c + 3) 0x00 (imageByte_readByte image imageEq (0x10c7c + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c80` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `03 c8 05 00` there. -/
theorem fetchBytesAt_10c80 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c80) 0x03#8 0xc8#8 0x05#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c80
  have pcNat : (BitVec.ofNat 64 0x10c80).toNat = 0x10c80 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c80 0x03 (imageByte_readByte image imageEq 0x10c80 0x03 h0)
  · simpa using loaded (0x10c80 + 1) 0xc8 (imageByte_readByte image imageEq (0x10c80 + 1) 0xc8 h1)
  · simpa using loaded (0x10c80 + 2) 0x05 (imageByte_readByte image imageEq (0x10c80 + 2) 0x05 h2)
  · simpa using loaded (0x10c80 + 3) 0x00 (imageByte_readByte image imageEq (0x10c80 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c84` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 96 86 00` there. -/
theorem fetchBytesAt_10c84 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c84) 0x93#8 0x96#8 0x86#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c84
  have pcNat : (BitVec.ofNat 64 0x10c84).toNat = 0x10c84 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c84 0x93 (imageByte_readByte image imageEq 0x10c84 0x93 h0)
  · simpa using loaded (0x10c84 + 1) 0x96 (imageByte_readByte image imageEq (0x10c84 + 1) 0x96 h1)
  · simpa using loaded (0x10c84 + 2) 0x86 (imageByte_readByte image imageEq (0x10c84 + 2) 0x86 h2)
  · simpa using loaded (0x10c84 + 3) 0x00 (imageByte_readByte image imageEq (0x10c84 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c88` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `13 17 07 01` there. -/
theorem fetchBytesAt_10c88 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c88) 0x13#8 0x17#8 0x07#8 0x01#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c88
  have pcNat : (BitVec.ofNat 64 0x10c88).toNat = 0x10c88 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c88 0x13 (imageByte_readByte image imageEq 0x10c88 0x13 h0)
  · simpa using loaded (0x10c88 + 1) 0x17 (imageByte_readByte image imageEq (0x10c88 + 1) 0x17 h1)
  · simpa using loaded (0x10c88 + 2) 0x07 (imageByte_readByte image imageEq (0x10c88 + 2) 0x07 h2)
  · simpa using loaded (0x10c88 + 3) 0x01 (imageByte_readByte image imageEq (0x10c88 + 3) 0x01 h3)
/-- Derive the exact four fetch bytes at `0x10c8c` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 97 87 01` there. -/
theorem fetchBytesAt_10c8c (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c8c) 0x93#8 0x97#8 0x87#8 0x01#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c8c
  have pcNat : (BitVec.ofNat 64 0x10c8c).toNat = 0x10c8c := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c8c 0x93 (imageByte_readByte image imageEq 0x10c8c 0x93 h0)
  · simpa using loaded (0x10c8c + 1) 0x97 (imageByte_readByte image imageEq (0x10c8c + 1) 0x97 h1)
  · simpa using loaded (0x10c8c + 2) 0x87 (imageByte_readByte image imageEq (0x10c8c + 2) 0x87 h2)
  · simpa using loaded (0x10c8c + 3) 0x01 (imageByte_readByte image imageEq (0x10c8c + 3) 0x01 h3)
/-- Derive the exact four fetch bytes at `0x10c90` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `b3 e6 06 01` there. -/
theorem fetchBytesAt_10c90 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c90) 0xb3#8 0xe6#8 0x06#8 0x01#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c90
  have pcNat : (BitVec.ofNat 64 0x10c90).toNat = 0x10c90 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c90 0xb3 (imageByte_readByte image imageEq 0x10c90 0xb3 h0)
  · simpa using loaded (0x10c90 + 1) 0xe6 (imageByte_readByte image imageEq (0x10c90 + 1) 0xe6 h1)
  · simpa using loaded (0x10c90 + 2) 0x06 (imageByte_readByte image imageEq (0x10c90 + 2) 0x06 h2)
  · simpa using loaded (0x10c90 + 3) 0x01 (imageByte_readByte image imageEq (0x10c90 + 3) 0x01 h3)
/-- Derive the exact four fetch bytes at `0x10c94` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `33 e7 e7 00` there. -/
theorem fetchBytesAt_10c94 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c94) 0x33#8 0xe7#8 0xe7#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c94
  have pcNat : (BitVec.ofNat 64 0x10c94).toNat = 0x10c94 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c94 0x33 (imageByte_readByte image imageEq 0x10c94 0x33 h0)
  · simpa using loaded (0x10c94 + 1) 0xe7 (imageByte_readByte image imageEq (0x10c94 + 1) 0xe7 h1)
  · simpa using loaded (0x10c94 + 2) 0xe7 (imageByte_readByte image imageEq (0x10c94 + 2) 0xe7 h2)
  · simpa using loaded (0x10c94 + 3) 0x00 (imageByte_readByte image imageEq (0x10c94 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c98` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `83 c7 55 00` there. -/
theorem fetchBytesAt_10c98 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c98) 0x83#8 0xc7#8 0x55#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c98
  have pcNat : (BitVec.ofNat 64 0x10c98).toNat = 0x10c98 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c98 0x83 (imageByte_readByte image imageEq 0x10c98 0x83 h0)
  · simpa using loaded (0x10c98 + 1) 0xc7 (imageByte_readByte image imageEq (0x10c98 + 1) 0xc7 h1)
  · simpa using loaded (0x10c98 + 2) 0x55 (imageByte_readByte image imageEq (0x10c98 + 2) 0x55 h2)
  · simpa using loaded (0x10c98 + 3) 0x00 (imageByte_readByte image imageEq (0x10c98 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c9c` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `03 c8 45 00` there. -/
theorem fetchBytesAt_10c9c (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c9c) 0x03#8 0xc8#8 0x45#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c9c
  have pcNat : (BitVec.ofNat 64 0x10c9c).toNat = 0x10c9c := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c9c 0x03 (imageByte_readByte image imageEq 0x10c9c 0x03 h0)
  · simpa using loaded (0x10c9c + 1) 0xc8 (imageByte_readByte image imageEq (0x10c9c + 1) 0xc8 h1)
  · simpa using loaded (0x10c9c + 2) 0x45 (imageByte_readByte image imageEq (0x10c9c + 2) 0x45 h2)
  · simpa using loaded (0x10c9c + 3) 0x00 (imageByte_readByte image imageEq (0x10c9c + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10ca0` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `83 c8 65 00` there. -/
theorem fetchBytesAt_10ca0 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10ca0) 0x83#8 0xc8#8 0x65#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10ca0
  have pcNat : (BitVec.ofNat 64 0x10ca0).toNat = 0x10ca0 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10ca0 0x83 (imageByte_readByte image imageEq 0x10ca0 0x83 h0)
  · simpa using loaded (0x10ca0 + 1) 0xc8 (imageByte_readByte image imageEq (0x10ca0 + 1) 0xc8 h1)
  · simpa using loaded (0x10ca0 + 2) 0x65 (imageByte_readByte image imageEq (0x10ca0 + 2) 0x65 h2)
  · simpa using loaded (0x10ca0 + 3) 0x00 (imageByte_readByte image imageEq (0x10ca0 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10ca4` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `83 c2 75 00` there. -/
theorem fetchBytesAt_10ca4 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10ca4) 0x83#8 0xc2#8 0x75#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10ca4
  have pcNat : (BitVec.ofNat 64 0x10ca4).toNat = 0x10ca4 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10ca4 0x83 (imageByte_readByte image imageEq 0x10ca4 0x83 h0)
  · simpa using loaded (0x10ca4 + 1) 0xc2 (imageByte_readByte image imageEq (0x10ca4 + 1) 0xc2 h1)
  · simpa using loaded (0x10ca4 + 2) 0x75 (imageByte_readByte image imageEq (0x10ca4 + 2) 0x75 h2)
  · simpa using loaded (0x10ca4 + 3) 0x00 (imageByte_readByte image imageEq (0x10ca4 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10ca8` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 97 87 00` there. -/
theorem fetchBytesAt_10ca8 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10ca8) 0x93#8 0x97#8 0x87#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10ca8
  have pcNat : (BitVec.ofNat 64 0x10ca8).toNat = 0x10ca8 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10ca8 0x93 (imageByte_readByte image imageEq 0x10ca8 0x93 h0)
  · simpa using loaded (0x10ca8 + 1) 0x97 (imageByte_readByte image imageEq (0x10ca8 + 1) 0x97 h1)
  · simpa using loaded (0x10ca8 + 2) 0x87 (imageByte_readByte image imageEq (0x10ca8 + 2) 0x87 h2)
  · simpa using loaded (0x10ca8 + 3) 0x00 (imageByte_readByte image imageEq (0x10ca8 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10cac` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `b3 e7 07 01` there. -/
theorem fetchBytesAt_10cac (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cac) 0xb3#8 0xe7#8 0x07#8 0x01#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10cac
  have pcNat : (BitVec.ofNat 64 0x10cac).toNat = 0x10cac := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cac 0xb3 (imageByte_readByte image imageEq 0x10cac 0xb3 h0)
  · simpa using loaded (0x10cac + 1) 0xe7 (imageByte_readByte image imageEq (0x10cac + 1) 0xe7 h1)
  · simpa using loaded (0x10cac + 2) 0x07 (imageByte_readByte image imageEq (0x10cac + 2) 0x07 h2)
  · simpa using loaded (0x10cac + 3) 0x01 (imageByte_readByte image imageEq (0x10cac + 3) 0x01 h3)
/-- Derive the exact four fetch bytes at `0x10cb0` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 98 08 01` there. -/
theorem fetchBytesAt_10cb0 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cb0) 0x93#8 0x98#8 0x08#8 0x01#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10cb0
  have pcNat : (BitVec.ofNat 64 0x10cb0).toNat = 0x10cb0 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cb0 0x93 (imageByte_readByte image imageEq 0x10cb0 0x93 h0)
  · simpa using loaded (0x10cb0 + 1) 0x98 (imageByte_readByte image imageEq (0x10cb0 + 1) 0x98 h1)
  · simpa using loaded (0x10cb0 + 2) 0x08 (imageByte_readByte image imageEq (0x10cb0 + 2) 0x08 h2)
  · simpa using loaded (0x10cb0 + 3) 0x01 (imageByte_readByte image imageEq (0x10cb0 + 3) 0x01 h3)
/-- Derive the exact four fetch bytes at `0x10cb4` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 92 82 01` there. -/
theorem fetchBytesAt_10cb4 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cb4) 0x93#8 0x92#8 0x82#8 0x01#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10cb4
  have pcNat : (BitVec.ofNat 64 0x10cb4).toNat = 0x10cb4 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cb4 0x93 (imageByte_readByte image imageEq 0x10cb4 0x93 h0)
  · simpa using loaded (0x10cb4 + 1) 0x92 (imageByte_readByte image imageEq (0x10cb4 + 1) 0x92 h1)
  · simpa using loaded (0x10cb4 + 2) 0x82 (imageByte_readByte image imageEq (0x10cb4 + 2) 0x82 h2)
  · simpa using loaded (0x10cb4 + 3) 0x01 (imageByte_readByte image imageEq (0x10cb4 + 3) 0x01 h3)
/-- Derive the exact four fetch bytes at `0x10cb8` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `33 e8 12 01` there. -/
theorem fetchBytesAt_10cb8 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cb8) 0x33#8 0xe8#8 0x12#8 0x01#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10cb8
  have pcNat : (BitVec.ofNat 64 0x10cb8).toNat = 0x10cb8 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cb8 0x33 (imageByte_readByte image imageEq 0x10cb8 0x33 h0)
  · simpa using loaded (0x10cb8 + 1) 0xe8 (imageByte_readByte image imageEq (0x10cb8 + 1) 0xe8 h1)
  · simpa using loaded (0x10cb8 + 2) 0x12 (imageByte_readByte image imageEq (0x10cb8 + 2) 0x12 h2)
  · simpa using loaded (0x10cb8 + 3) 0x01 (imageByte_readByte image imageEq (0x10cb8 + 3) 0x01 h3)
/-- Derive the exact four fetch bytes at `0x10cbc` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `13 06 86 ff` there. -/
theorem fetchBytesAt_10cbc (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cbc) 0x13#8 0x06#8 0x86#8 0xff#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10cbc
  have pcNat : (BitVec.ofNat 64 0x10cbc).toNat = 0x10cbc := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cbc 0x13 (imageByte_readByte image imageEq 0x10cbc 0x13 h0)
  · simpa using loaded (0x10cbc + 1) 0x06 (imageByte_readByte image imageEq (0x10cbc + 1) 0x06 h1)
  · simpa using loaded (0x10cbc + 2) 0x86 (imageByte_readByte image imageEq (0x10cbc + 2) 0x86 h2)
  · simpa using loaded (0x10cbc + 3) 0xff (imageByte_readByte image imageEq (0x10cbc + 3) 0xff h3)
/-- Derive the exact four fetch bytes at `0x10cc0` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 85 85 00` there. -/
theorem fetchBytesAt_10cc0 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cc0) 0x93#8 0x85#8 0x85#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10cc0
  have pcNat : (BitVec.ofNat 64 0x10cc0).toNat = 0x10cc0 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cc0 0x93 (imageByte_readByte image imageEq 0x10cc0 0x93 h0)
  · simpa using loaded (0x10cc0 + 1) 0x85 (imageByte_readByte image imageEq (0x10cc0 + 1) 0x85 h1)
  · simpa using loaded (0x10cc0 + 2) 0x85 (imageByte_readByte image imageEq (0x10cc0 + 2) 0x85 h2)
  · simpa using loaded (0x10cc0 + 3) 0x00 (imageByte_readByte image imageEq (0x10cc0 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10cc4` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `b3 66 d7 00` there. -/
theorem fetchBytesAt_10cc4 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cc4) 0xb3#8 0x66#8 0xd7#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10cc4
  have pcNat : (BitVec.ofNat 64 0x10cc4).toNat = 0x10cc4 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cc4 0xb3 (imageByte_readByte image imageEq 0x10cc4 0xb3 h0)
  · simpa using loaded (0x10cc4 + 1) 0x66 (imageByte_readByte image imageEq (0x10cc4 + 1) 0x66 h1)
  · simpa using loaded (0x10cc4 + 2) 0xd7 (imageByte_readByte image imageEq (0x10cc4 + 2) 0xd7 h2)
  · simpa using loaded (0x10cc4 + 3) 0x00 (imageByte_readByte image imageEq (0x10cc4 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10cc8` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `03 37 05 00` there. -/
theorem fetchBytesAt_10cc8 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cc8) 0x03#8 0x37#8 0x05#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10cc8
  have pcNat : (BitVec.ofNat 64 0x10cc8).toNat = 0x10cc8 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cc8 0x03 (imageByte_readByte image imageEq 0x10cc8 0x03 h0)
  · simpa using loaded (0x10cc8 + 1) 0x37 (imageByte_readByte image imageEq (0x10cc8 + 1) 0x37 h1)
  · simpa using loaded (0x10cc8 + 2) 0x05 (imageByte_readByte image imageEq (0x10cc8 + 2) 0x05 h2)
  · simpa using loaded (0x10cc8 + 3) 0x00 (imageByte_readByte image imageEq (0x10cc8 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10ccc` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `b3 67 f8 00` there. -/
theorem fetchBytesAt_10ccc (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10ccc) 0xb3#8 0x67#8 0xf8#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10ccc
  have pcNat : (BitVec.ofNat 64 0x10ccc).toNat = 0x10ccc := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10ccc 0xb3 (imageByte_readByte image imageEq 0x10ccc 0xb3 h0)
  · simpa using loaded (0x10ccc + 1) 0x67 (imageByte_readByte image imageEq (0x10ccc + 1) 0x67 h1)
  · simpa using loaded (0x10ccc + 2) 0xf8 (imageByte_readByte image imageEq (0x10ccc + 2) 0xf8 h2)
  · simpa using loaded (0x10ccc + 3) 0x00 (imageByte_readByte image imageEq (0x10ccc + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10cd0` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 97 07 02` there. -/
theorem fetchBytesAt_10cd0 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cd0) 0x93#8 0x97#8 0x07#8 0x02#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10cd0
  have pcNat : (BitVec.ofNat 64 0x10cd0).toNat = 0x10cd0 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cd0 0x93 (imageByte_readByte image imageEq 0x10cd0 0x93 h0)
  · simpa using loaded (0x10cd0 + 1) 0x97 (imageByte_readByte image imageEq (0x10cd0 + 1) 0x97 h1)
  · simpa using loaded (0x10cd0 + 2) 0x07 (imageByte_readByte image imageEq (0x10cd0 + 2) 0x07 h2)
  · simpa using loaded (0x10cd0 + 3) 0x02 (imageByte_readByte image imageEq (0x10cd0 + 3) 0x02 h3)
/-- Derive the exact four fetch bytes at `0x10cd4` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `b3 e6 d7 00` there. -/
theorem fetchBytesAt_10cd4 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cd4) 0xb3#8 0xe6#8 0xd7#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10cd4
  have pcNat : (BitVec.ofNat 64 0x10cd4).toNat = 0x10cd4 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cd4 0xb3 (imageByte_readByte image imageEq 0x10cd4 0xb3 h0)
  · simpa using loaded (0x10cd4 + 1) 0xe6 (imageByte_readByte image imageEq (0x10cd4 + 1) 0xe6 h1)
  · simpa using loaded (0x10cd4 + 2) 0xd7 (imageByte_readByte image imageEq (0x10cd4 + 2) 0xd7 h2)
  · simpa using loaded (0x10cd4 + 3) 0x00 (imageByte_readByte image imageEq (0x10cd4 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10cd8` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `b3 46 d7 00` there. -/
theorem fetchBytesAt_10cd8 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cd8) 0xb3#8 0x46#8 0xd7#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10cd8
  have pcNat : (BitVec.ofNat 64 0x10cd8).toNat = 0x10cd8 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cd8 0xb3 (imageByte_readByte image imageEq 0x10cd8 0xb3 h0)
  · simpa using loaded (0x10cd8 + 1) 0x46 (imageByte_readByte image imageEq (0x10cd8 + 1) 0x46 h1)
  · simpa using loaded (0x10cd8 + 2) 0xd7 (imageByte_readByte image imageEq (0x10cd8 + 2) 0xd7 h2)
  · simpa using loaded (0x10cd8 + 3) 0x00 (imageByte_readByte image imageEq (0x10cd8 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10cdc` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `23 30 d5 00` there. -/
theorem fetchBytesAt_10cdc (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cdc) 0x23#8 0x30#8 0xd5#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10cdc
  have pcNat : (BitVec.ofNat 64 0x10cdc).toNat = 0x10cdc := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cdc 0x23 (imageByte_readByte image imageEq 0x10cdc 0x23 h0)
  · simpa using loaded (0x10cdc + 1) 0x30 (imageByte_readByte image imageEq (0x10cdc + 1) 0x30 h1)
  · simpa using loaded (0x10cdc + 2) 0xd5 (imageByte_readByte image imageEq (0x10cdc + 2) 0xd5 h2)
  · simpa using loaded (0x10cdc + 3) 0x00 (imageByte_readByte image imageEq (0x10cdc + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10ce0` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `13 05 85 00` there. -/
theorem fetchBytesAt_10ce0 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10ce0) 0x13#8 0x05#8 0x85#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10ce0
  have pcNat : (BitVec.ofNat 64 0x10ce0).toNat = 0x10ce0 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10ce0 0x13 (imageByte_readByte image imageEq 0x10ce0 0x13 h0)
  · simpa using loaded (0x10ce0 + 1) 0x05 (imageByte_readByte image imageEq (0x10ce0 + 1) 0x05 h1)
  · simpa using loaded (0x10ce0 + 2) 0x85 (imageByte_readByte image imageEq (0x10ce0 + 2) 0x85 h2)
  · simpa using loaded (0x10ce0 + 3) 0x00 (imageByte_readByte image imageEq (0x10ce0 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10ce4` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `e3 18 06 f8` there. -/
theorem fetchBytesAt_10ce4 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10ce4
  have pcNat : (BitVec.ofNat 64 0x10ce4).toNat = 0x10ce4 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10ce4 0xe3 (imageByte_readByte image imageEq 0x10ce4 0xe3 h0)
  · simpa using loaded (0x10ce4 + 1) 0x18 (imageByte_readByte image imageEq (0x10ce4 + 1) 0x18 h1)
  · simpa using loaded (0x10ce4 + 2) 0x06 (imageByte_readByte image imageEq (0x10ce4 + 2) 0x06 h2)
  · simpa using loaded (0x10ce4 + 3) 0xf8 (imageByte_readByte image imageEq (0x10ce4 + 3) 0xf8 h3)
/-- Derive the exact four fetch bytes at `0x10ce8` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `67 80 00 00` there. -/
theorem fetchBytesAt_10ce8 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10ce8) 0x67#8 0x80#8 0x00#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10ce8
  have pcNat : (BitVec.ofNat 64 0x10ce8).toNat = 0x10ce8 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10ce8 0x67 (imageByte_readByte image imageEq 0x10ce8 0x67 h0)
  · simpa using loaded (0x10ce8 + 1) 0x80 (imageByte_readByte image imageEq (0x10ce8 + 1) 0x80 h1)
  · simpa using loaded (0x10ce8 + 2) 0x00 (imageByte_readByte image imageEq (0x10ce8 + 2) 0x00 h2)
  · simpa using loaded (0x10ce8 + 3) 0x00 (imageByte_readByte image imageEq (0x10ce8 + 3) 0x00 h3)

end BinaryFv.Keccak
