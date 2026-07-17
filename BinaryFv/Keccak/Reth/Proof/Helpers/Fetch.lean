import BinaryFv.Keccak.Reth.Artifact.Facts.HelperBytes
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.Platform.Fetch

/-!
# Fetch lifts for the memory helpers

Lifting the helper words the pinned image owns to the generated fetch inputs. These mention machine
`State`, so they are proofs, not artifact facts.
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary
open BinaryFv.RiscV

/-- Derive the exact four fetch bytes at `0x10d18` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 07 00 00` there. -/
theorem fetchBytesAt_10d18 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d18) 0x93#8 0x07#8 0x00#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d18
  have pcNat : (BitVec.ofNat 64 0x10d18).toNat = 0x10d18 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d18 0x93 (imageByte_readByte image imageEq 0x10d18 0x93 h0)
  · simpa using loaded (0x10d18 + 1) 0x07 (imageByte_readByte image imageEq (0x10d18 + 1) 0x07 h1)
  · simpa using loaded (0x10d18 + 2) 0x00 (imageByte_readByte image imageEq (0x10d18 + 2) 0x00 h2)
  · simpa using loaded (0x10d18 + 3) 0x00 (imageByte_readByte image imageEq (0x10d18 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d1c` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `63 94 c7 00` there. -/
theorem fetchBytesAt_10d1c (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d1c) 0x63#8 0x94#8 0xc7#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d1c
  have pcNat : (BitVec.ofNat 64 0x10d1c).toNat = 0x10d1c := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d1c 0x63 (imageByte_readByte image imageEq 0x10d1c 0x63 h0)
  · simpa using loaded (0x10d1c + 1) 0x94 (imageByte_readByte image imageEq (0x10d1c + 1) 0x94 h1)
  · simpa using loaded (0x10d1c + 2) 0xc7 (imageByte_readByte image imageEq (0x10d1c + 2) 0xc7 h2)
  · simpa using loaded (0x10d1c + 3) 0x00 (imageByte_readByte image imageEq (0x10d1c + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d20` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `67 80 00 00` there. -/
theorem fetchBytesAt_10d20 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d20) 0x67#8 0x80#8 0x00#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d20
  have pcNat : (BitVec.ofNat 64 0x10d20).toNat = 0x10d20 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d20 0x67 (imageByte_readByte image imageEq 0x10d20 0x67 h0)
  · simpa using loaded (0x10d20 + 1) 0x80 (imageByte_readByte image imageEq (0x10d20 + 1) 0x80 h1)
  · simpa using loaded (0x10d20 + 2) 0x00 (imageByte_readByte image imageEq (0x10d20 + 2) 0x00 h2)
  · simpa using loaded (0x10d20 + 3) 0x00 (imageByte_readByte image imageEq (0x10d20 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d24` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `b3 86 f5 00` there. -/
theorem fetchBytesAt_10d24 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d24) 0xb3#8 0x86#8 0xf5#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d24
  have pcNat : (BitVec.ofNat 64 0x10d24).toNat = 0x10d24 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d24 0xb3 (imageByte_readByte image imageEq 0x10d24 0xb3 h0)
  · simpa using loaded (0x10d24 + 1) 0x86 (imageByte_readByte image imageEq (0x10d24 + 1) 0x86 h1)
  · simpa using loaded (0x10d24 + 2) 0xf5 (imageByte_readByte image imageEq (0x10d24 + 2) 0xf5 h2)
  · simpa using loaded (0x10d24 + 3) 0x00 (imageByte_readByte image imageEq (0x10d24 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d28` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `83 c6 06 00` there. -/
theorem fetchBytesAt_10d28 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d28) 0x83#8 0xc6#8 0x06#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d28
  have pcNat : (BitVec.ofNat 64 0x10d28).toNat = 0x10d28 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d28 0x83 (imageByte_readByte image imageEq 0x10d28 0x83 h0)
  · simpa using loaded (0x10d28 + 1) 0xc6 (imageByte_readByte image imageEq (0x10d28 + 1) 0xc6 h1)
  · simpa using loaded (0x10d28 + 2) 0x06 (imageByte_readByte image imageEq (0x10d28 + 2) 0x06 h2)
  · simpa using loaded (0x10d28 + 3) 0x00 (imageByte_readByte image imageEq (0x10d28 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d2c` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `33 07 f5 00` there. -/
theorem fetchBytesAt_10d2c (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d2c) 0x33#8 0x07#8 0xf5#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d2c
  have pcNat : (BitVec.ofNat 64 0x10d2c).toNat = 0x10d2c := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d2c 0x33 (imageByte_readByte image imageEq 0x10d2c 0x33 h0)
  · simpa using loaded (0x10d2c + 1) 0x07 (imageByte_readByte image imageEq (0x10d2c + 1) 0x07 h1)
  · simpa using loaded (0x10d2c + 2) 0xf5 (imageByte_readByte image imageEq (0x10d2c + 2) 0xf5 h2)
  · simpa using loaded (0x10d2c + 3) 0x00 (imageByte_readByte image imageEq (0x10d2c + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d30` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 87 17 00` there. -/
theorem fetchBytesAt_10d30 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d30) 0x93#8 0x87#8 0x17#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d30
  have pcNat : (BitVec.ofNat 64 0x10d30).toNat = 0x10d30 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d30 0x93 (imageByte_readByte image imageEq 0x10d30 0x93 h0)
  · simpa using loaded (0x10d30 + 1) 0x87 (imageByte_readByte image imageEq (0x10d30 + 1) 0x87 h1)
  · simpa using loaded (0x10d30 + 2) 0x17 (imageByte_readByte image imageEq (0x10d30 + 2) 0x17 h2)
  · simpa using loaded (0x10d30 + 3) 0x00 (imageByte_readByte image imageEq (0x10d30 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d34` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `23 00 d7 00` there. -/
theorem fetchBytesAt_10d34 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d34) 0x23#8 0x00#8 0xd7#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d34
  have pcNat : (BitVec.ofNat 64 0x10d34).toNat = 0x10d34 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d34 0x23 (imageByte_readByte image imageEq 0x10d34 0x23 h0)
  · simpa using loaded (0x10d34 + 1) 0x00 (imageByte_readByte image imageEq (0x10d34 + 1) 0x00 h1)
  · simpa using loaded (0x10d34 + 2) 0xd7 (imageByte_readByte image imageEq (0x10d34 + 2) 0xd7 h2)
  · simpa using loaded (0x10d34 + 3) 0x00 (imageByte_readByte image imageEq (0x10d34 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d38` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `6f f0 5f fe` there. -/
theorem fetchBytesAt_10d38 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d38) 0x6f#8 0xf0#8 0x5f#8 0xfe#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d38
  have pcNat : (BitVec.ofNat 64 0x10d38).toNat = 0x10d38 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d38 0x6f (imageByte_readByte image imageEq 0x10d38 0x6f h0)
  · simpa using loaded (0x10d38 + 1) 0xf0 (imageByte_readByte image imageEq (0x10d38 + 1) 0xf0 h1)
  · simpa using loaded (0x10d38 + 2) 0x5f (imageByte_readByte image imageEq (0x10d38 + 2) 0x5f h2)
  · simpa using loaded (0x10d38 + 3) 0xfe (imageByte_readByte image imageEq (0x10d38 + 3) 0xfe h3)
/-- Derive the exact four fetch bytes at `0x10d3c` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 07 00 00` there. -/
theorem fetchBytesAt_10d3c (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d3c) 0x93#8 0x07#8 0x00#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d3c
  have pcNat : (BitVec.ofNat 64 0x10d3c).toNat = 0x10d3c := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d3c 0x93 (imageByte_readByte image imageEq 0x10d3c 0x93 h0)
  · simpa using loaded (0x10d3c + 1) 0x07 (imageByte_readByte image imageEq (0x10d3c + 1) 0x07 h1)
  · simpa using loaded (0x10d3c + 2) 0x00 (imageByte_readByte image imageEq (0x10d3c + 2) 0x00 h2)
  · simpa using loaded (0x10d3c + 3) 0x00 (imageByte_readByte image imageEq (0x10d3c + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d40` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `63 94 c7 00` there. -/
theorem fetchBytesAt_10d40 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d40) 0x63#8 0x94#8 0xc7#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d40
  have pcNat : (BitVec.ofNat 64 0x10d40).toNat = 0x10d40 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d40 0x63 (imageByte_readByte image imageEq 0x10d40 0x63 h0)
  · simpa using loaded (0x10d40 + 1) 0x94 (imageByte_readByte image imageEq (0x10d40 + 1) 0x94 h1)
  · simpa using loaded (0x10d40 + 2) 0xc7 (imageByte_readByte image imageEq (0x10d40 + 2) 0xc7 h2)
  · simpa using loaded (0x10d40 + 3) 0x00 (imageByte_readByte image imageEq (0x10d40 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d44` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `67 80 00 00` there. -/
theorem fetchBytesAt_10d44 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d44) 0x67#8 0x80#8 0x00#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d44
  have pcNat : (BitVec.ofNat 64 0x10d44).toNat = 0x10d44 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d44 0x67 (imageByte_readByte image imageEq 0x10d44 0x67 h0)
  · simpa using loaded (0x10d44 + 1) 0x80 (imageByte_readByte image imageEq (0x10d44 + 1) 0x80 h1)
  · simpa using loaded (0x10d44 + 2) 0x00 (imageByte_readByte image imageEq (0x10d44 + 2) 0x00 h2)
  · simpa using loaded (0x10d44 + 3) 0x00 (imageByte_readByte image imageEq (0x10d44 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d48` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `33 07 f5 00` there. -/
theorem fetchBytesAt_10d48 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d48) 0x33#8 0x07#8 0xf5#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d48
  have pcNat : (BitVec.ofNat 64 0x10d48).toNat = 0x10d48 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d48 0x33 (imageByte_readByte image imageEq 0x10d48 0x33 h0)
  · simpa using loaded (0x10d48 + 1) 0x07 (imageByte_readByte image imageEq (0x10d48 + 1) 0x07 h1)
  · simpa using loaded (0x10d48 + 2) 0xf5 (imageByte_readByte image imageEq (0x10d48 + 2) 0xf5 h2)
  · simpa using loaded (0x10d48 + 3) 0x00 (imageByte_readByte image imageEq (0x10d48 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d4c` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `23 00 b7 00` there. -/
theorem fetchBytesAt_10d4c (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d4c) 0x23#8 0x00#8 0xb7#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d4c
  have pcNat : (BitVec.ofNat 64 0x10d4c).toNat = 0x10d4c := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d4c 0x23 (imageByte_readByte image imageEq 0x10d4c 0x23 h0)
  · simpa using loaded (0x10d4c + 1) 0x00 (imageByte_readByte image imageEq (0x10d4c + 1) 0x00 h1)
  · simpa using loaded (0x10d4c + 2) 0xb7 (imageByte_readByte image imageEq (0x10d4c + 2) 0xb7 h2)
  · simpa using loaded (0x10d4c + 3) 0x00 (imageByte_readByte image imageEq (0x10d4c + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d50` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 87 17 00` there. -/
theorem fetchBytesAt_10d50 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d50) 0x93#8 0x87#8 0x17#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d50
  have pcNat : (BitVec.ofNat 64 0x10d50).toNat = 0x10d50 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d50 0x93 (imageByte_readByte image imageEq 0x10d50 0x93 h0)
  · simpa using loaded (0x10d50 + 1) 0x87 (imageByte_readByte image imageEq (0x10d50 + 1) 0x87 h1)
  · simpa using loaded (0x10d50 + 2) 0x17 (imageByte_readByte image imageEq (0x10d50 + 2) 0x17 h2)
  · simpa using loaded (0x10d50 + 3) 0x00 (imageByte_readByte image imageEq (0x10d50 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10d54` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `6f f0 df fe` there. -/
theorem fetchBytesAt_10d54 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10d54) 0x6f#8 0xf0#8 0xdf#8 0xfe#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10d54
  have pcNat : (BitVec.ofNat 64 0x10d54).toNat = 0x10d54 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10d54 0x6f (imageByte_readByte image imageEq 0x10d54 0x6f h0)
  · simpa using loaded (0x10d54 + 1) 0xf0 (imageByte_readByte image imageEq (0x10d54 + 1) 0xf0 h1)
  · simpa using loaded (0x10d54 + 2) 0xdf (imageByte_readByte image imageEq (0x10d54 + 2) 0xdf h2)
  · simpa using loaded (0x10d54 + 3) 0xfe (imageByte_readByte image imageEq (0x10d54 + 3) 0xfe h3)
/-- Derive the exact four fetch bytes at `0x10c44` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `13 87 05 00` there. -/
theorem fetchBytesAt_10c44 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c44) 0x13#8 0x87#8 0x05#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c44
  have pcNat : (BitVec.ofNat 64 0x10c44).toNat = 0x10c44 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c44 0x13 (imageByte_readByte image imageEq 0x10c44 0x13 h0)
  · simpa using loaded (0x10c44 + 1) 0x87 (imageByte_readByte image imageEq (0x10c44 + 1) 0x87 h1)
  · simpa using loaded (0x10c44 + 2) 0x05 (imageByte_readByte image imageEq (0x10c44 + 2) 0x05 h2)
  · simpa using loaded (0x10c44 + 3) 0x00 (imageByte_readByte image imageEq (0x10c44 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c48` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `63 9a d5 00` there. -/
theorem fetchBytesAt_10c48 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c48) 0x63#8 0x9a#8 0xd5#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c48
  have pcNat : (BitVec.ofNat 64 0x10c48).toNat = 0x10c48 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c48 0x63 (imageByte_readByte image imageEq 0x10c48 0x63 h0)
  · simpa using loaded (0x10c48 + 1) 0x9a (imageByte_readByte image imageEq (0x10c48 + 1) 0x9a h1)
  · simpa using loaded (0x10c48 + 2) 0xd5 (imageByte_readByte image imageEq (0x10c48 + 2) 0xd5 h2)
  · simpa using loaded (0x10c48 + 3) 0x00 (imageByte_readByte image imageEq (0x10c48 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c4c` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 05 06 00` there. -/
theorem fetchBytesAt_10c4c (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c4c) 0x93#8 0x05#8 0x06#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c4c
  have pcNat : (BitVec.ofNat 64 0x10c4c).toNat = 0x10c4c := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c4c 0x93 (imageByte_readByte image imageEq 0x10c4c 0x93 h0)
  · simpa using loaded (0x10c4c + 1) 0x05 (imageByte_readByte image imageEq (0x10c4c + 1) 0x05 h1)
  · simpa using loaded (0x10c4c + 2) 0x06 (imageByte_readByte image imageEq (0x10c4c + 2) 0x06 h2)
  · simpa using loaded (0x10c4c + 3) 0x00 (imageByte_readByte image imageEq (0x10c4c + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c50` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `13 06 07 00` there. -/
theorem fetchBytesAt_10c50 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c50) 0x13#8 0x06#8 0x07#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c50
  have pcNat : (BitVec.ofNat 64 0x10c50).toNat = 0x10c50 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c50 0x13 (imageByte_readByte image imageEq 0x10c50 0x13 h0)
  · simpa using loaded (0x10c50 + 1) 0x06 (imageByte_readByte image imageEq (0x10c50 + 1) 0x06 h1)
  · simpa using loaded (0x10c50 + 2) 0x07 (imageByte_readByte image imageEq (0x10c50 + 2) 0x07 h2)
  · simpa using loaded (0x10c50 + 3) 0x00 (imageByte_readByte image imageEq (0x10c50 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c54` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `17 03 00 00` there. -/
theorem fetchBytesAt_10c54 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c54) 0x17#8 0x03#8 0x00#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c54
  have pcNat : (BitVec.ofNat 64 0x10c54).toNat = 0x10c54 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c54 0x17 (imageByte_readByte image imageEq 0x10c54 0x17 h0)
  · simpa using loaded (0x10c54 + 1) 0x03 (imageByte_readByte image imageEq (0x10c54 + 1) 0x03 h1)
  · simpa using loaded (0x10c54 + 2) 0x00 (imageByte_readByte image imageEq (0x10c54 + 2) 0x00 h2)
  · simpa using loaded (0x10c54 + 3) 0x00 (imageByte_readByte image imageEq (0x10c54 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c58` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `67 00 43 0c` there. -/
theorem fetchBytesAt_10c58 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c58) 0x67#8 0x00#8 0x43#8 0x0c#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c58
  have pcNat : (BitVec.ofNat 64 0x10c58).toNat = 0x10c58 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c58 0x67 (imageByte_readByte image imageEq 0x10c58 0x67 h0)
  · simpa using loaded (0x10c58 + 1) 0x00 (imageByte_readByte image imageEq (0x10c58 + 1) 0x00 h1)
  · simpa using loaded (0x10c58 + 2) 0x43 (imageByte_readByte image imageEq (0x10c58 + 2) 0x43 h2)
  · simpa using loaded (0x10c58 + 3) 0x0c (imageByte_readByte image imageEq (0x10c58 + 3) 0x0c h3)
/-- Derive the exact four fetch bytes at `0x10c5c` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `13 05 07 00` there. -/
theorem fetchBytesAt_10c5c (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c5c) 0x13#8 0x05#8 0x07#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c5c
  have pcNat : (BitVec.ofNat 64 0x10c5c).toNat = 0x10c5c := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c5c 0x13 (imageByte_readByte image imageEq 0x10c5c 0x13 h0)
  · simpa using loaded (0x10c5c + 1) 0x05 (imageByte_readByte image imageEq (0x10c5c + 1) 0x05 h1)
  · simpa using loaded (0x10c5c + 2) 0x07 (imageByte_readByte image imageEq (0x10c5c + 2) 0x07 h2)
  · simpa using loaded (0x10c5c + 3) 0x00 (imageByte_readByte image imageEq (0x10c5c + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c60` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `93 85 06 00` there. -/
theorem fetchBytesAt_10c60 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c60) 0x93#8 0x85#8 0x06#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c60
  have pcNat : (BitVec.ofNat 64 0x10c60).toNat = 0x10c60 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c60 0x93 (imageByte_readByte image imageEq 0x10c60 0x93 h0)
  · simpa using loaded (0x10c60 + 1) 0x85 (imageByte_readByte image imageEq (0x10c60 + 1) 0x85 h1)
  · simpa using loaded (0x10c60 + 2) 0x06 (imageByte_readByte image imageEq (0x10c60 + 2) 0x06 h2)
  · simpa using loaded (0x10c60 + 3) 0x00 (imageByte_readByte image imageEq (0x10c60 + 3) 0x00 h3)
/-- Derive the exact four fetch bytes at `0x10c64` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `97 f0 ff ff` there. -/
theorem fetchBytesAt_10c64 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c64) 0x97#8 0xf0#8 0xff#8 0xff#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c64
  have pcNat : (BitVec.ofNat 64 0x10c64).toNat = 0x10c64 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c64 0x97 (imageByte_readByte image imageEq 0x10c64 0x97 h0)
  · simpa using loaded (0x10c64 + 1) 0xf0 (imageByte_readByte image imageEq (0x10c64 + 1) 0xf0 h1)
  · simpa using loaded (0x10c64 + 2) 0xff (imageByte_readByte image imageEq (0x10c64 + 2) 0xff h2)
  · simpa using loaded (0x10c64 + 3) 0xff (imageByte_readByte image imageEq (0x10c64 + 3) 0xff h3)
/-- Derive the exact four fetch bytes at `0x10c68` directly from the persistent code-image assertion
    (`matchesMemory`): given the parsed ELF agrees with sparse memory, the generated fetch reads
    exactly `e7 80 c0 48` there. -/
theorem fetchBytesAt_10c68 (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10c68) 0xe7#8 0x80#8 0xc0#8 0x48#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := imageByte_10c68
  have pcNat : (BitVec.ofNat 64 0x10c68).toNat = 0x10c68 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10c68 0xe7 (imageByte_readByte image imageEq 0x10c68 0xe7 h0)
  · simpa using loaded (0x10c68 + 1) 0x80 (imageByte_readByte image imageEq (0x10c68 + 1) 0x80 h1)
  · simpa using loaded (0x10c68 + 2) 0xc0 (imageByte_readByte image imageEq (0x10c68 + 2) 0xc0 h2)
  · simpa using loaded (0x10c68 + 3) 0x48 (imageByte_readByte image imageEq (0x10c68 + 3) 0x48 h3)

end BinaryFv.Keccak
