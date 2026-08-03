import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level3Contracts
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep

/-!
# Sail proof for the inlined exact-ERE-prefix check

The selected compiler instance is split at two generated outgoing instructions. Eleven body
instructions belong to the child; `bltu` at `0x10394` and the final `or` at `0x103c0` are executed
by the enclosing inlined-`decode` proof. This file first pins that complete 13-word partition to the
immutable image before constructing the two body traces.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Elflings.Generated

/-- One little-endian instruction word read directly from the pinned program image. -/
def hasExactErePrefixImageWord? (address : Nat) : Option Nat := do
  let byte0 ← Artifacts.programImage.readByte? address
  let byte1 ← Artifacts.programImage.readByte? (address + 1)
  let byte2 ← Artifacts.programImage.readByte? (address + 2)
  let byte3 ← Artifacts.programImage.readByte? (address + 3)
  pure (byte0.toNat + byte1.toNat * 2 ^ 8 + byte2.toNat * 2 ^ 16 + byte3.toNat * 2 ^ 24)

/-- All words in the two attributed segments, including the two separately executed outgoing
instructions. Keeping the addresses beside the words makes omissions and shifted boundaries visible. -/
def hasExactErePrefixInstructionWords : List (Nat × Nat) :=
  [(0x10390, 0x00c48633), (0x10394, 0x08a66663),
    (0x10398, 0x00144503), (0x1039c, 0x00044603),
    (0x103a0, 0x00244703), (0x103a4, 0x00344783),
    (0x103a8, 0x00851513), (0x103ac, 0x00c56533),
    (0x103b0, 0xffc48693), (0x103b4, 0x01071713),
    (0x103b8, 0x01879793), (0x103bc, 0x00e7e733),
    (0x103c0, 0x00a76533)]

def hasExactErePrefixBodyPcs : List Nat :=
  [0x10390, 0x10398, 0x1039c, 0x103a0, 0x103a4, 0x103a8,
    0x103ac, 0x103b0, 0x103b4, 0x103b8, 0x103bc]

def hasExactErePrefixOutgoingPcs : List Nat := [0x10394, 0x103c0]

/-- Kernel-checked identity of all 13 words against the pinned image. -/
theorem hasExactErePrefix_instruction_words_pinned :
    ∀ entry ∈ hasExactErePrefixInstructionWords,
      hasExactErePrefixImageWord? entry.1 = some entry.2 := by
  native_decide

/-- The eleven child-body words are exactly in the generated execution region and are not exits. -/
theorem hasExactErePrefix_body_classification :
    ∀ pc ∈ hasExactErePrefixBodyPcs,
      functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35
          (BitVec.ofNat 64 pc) ∧
        ¬ functionInstanceExitPred
          functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35
          (BitVec.ofNat 64 pc) := by
  intro pc member
  simp only [hasExactErePrefixBodyPcs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals first
    | (apply functionInstanceExecutionPcs_iff_ranges.mpr
       apply RegionPcs.iff_inRanges.mpr
       native_decide)
    | simp [functionInstanceExitPred, FunctionInstance.isExit,
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35]

/-- The other two attributed words are the generated outgoing-instruction sources. -/
theorem hasExactErePrefix_outgoing_classification :
    ∀ pc ∈ hasExactErePrefixOutgoingPcs,
      functionInstanceExecutionPcs generatedProgram
          functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35
          (BitVec.ofNat 64 pc) ∧
        functionInstanceExitPred
          functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35
          (BitVec.ofNat 64 pc) := by
  intro pc member
  simp only [hasExactErePrefixOutgoingPcs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals constructor
  all_goals first
    | (apply functionInstanceExecutionPcs_iff_ranges.mpr
       apply RegionPcs.iff_inRanges.mpr
       native_decide)
    | simp [functionInstanceExitPred, FunctionInstance.isExit,
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35]

end BinaryFv.Zesu.MachineExecution
