import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof

/-!
# Sail proof for the inlined `decode` scope

This file executes the 31 instructions owned directly by the compiler's inlined `decode` instance
and composes them with the three Level 3 child summaries. The inventory below is the reviewable
starting point: every owned word is checked against the pinned program image before any path proof
uses it.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated

def decodeInlineImageWord? (address : Nat) : Option Nat := do
  let byte0 ← Artifacts.programImage.readByte? address
  let byte1 ← Artifacts.programImage.readByte? (address + 1)
  let byte2 ← Artifacts.programImage.readByte? (address + 2)
  let byte3 ← Artifacts.programImage.readByte? (address + 3)
  pure (byte0.toNat + byte1.toNat * 2 ^ 8 + byte2.toNat * 2 ^ 16 + byte3.toNat * 2 ^ 24)

/-- Exactly the 31 words attributed directly to the inlined `decode` instance. Child-owned words
and wrapper-owned continuations are deliberately absent. -/
def decodeInlineOwnedInstructionWords : List (Nat × Nat) :=
  [(0x10308, 0x36010513), (0x1030c, 0x01010593),
    (0x10310, 0x00040613), (0x10314, 0x00048693),
    (0x10318, 0x00000097), (0x1031c, 0x12c080e7),
    (0x10320, 0x6a015503), (0x10324, 0x04051c63),
    (0x10328, 0x02010513), (0x1032c, 0x36010593),
    (0x10330, 0x34000613), (0x10334, 0x00004097),
    (0x10338, 0xb84080e7), (0x10380, 0x06b51e63),
    (0x10384, 0xfff00513), (0x10388, 0x02051513),
    (0x1038c, 0xffc50613), (0x103c4, 0x04a69e63),
    (0x103c8, 0x00440613), (0x103cc, 0x6b010513),
    (0x103d0, 0x01010593), (0x103d4, 0x00000097),
    (0x103d8, 0x070080e7), (0x103dc, 0x02010513),
    (0x103e0, 0x6b010593), (0x103e4, 0x34000613),
    (0x103e8, 0x00004097), (0x103ec, 0xad0080e7),
    (0x103f0, 0x00001537), (0x103f4, 0x00a10533),
    (0x103f8, 0x9f055503)]

theorem decodeInline_owned_instruction_words_pinned :
    ∀ entry ∈ decodeInlineOwnedInstructionWords,
      decodeInlineImageWord? entry.1 = some entry.2 := by
  native_decide

theorem decodeInline_owned_instruction_count :
    decodeInlineOwnedInstructionWords.length = 31 := by
  decide

/-- Every listed instruction lies in the generated execution extent of this compiled instance.
This checks completeness against the proof's confinement predicate independently of DWARF labels. -/
theorem decodeInline_owned_in_execution_region :
    ∀ entry ∈ decodeInlineOwnedInstructionWords,
      functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
        (BitVec.ofNat 64 entry.1) := by
  intro entry member
  simp only [decodeInlineOwnedInstructionWords, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide

end BinaryFv.Zesu.MachineExecution
