import BinaryFv.Zesu.Artifact.Image

namespace BinaryFv.Zesu.Artifact

open BinaryFv.RiscV

def zesuDecodeRawName : ByteArray := "zesu_decode_raw".toUTF8

def zesuDecodeRaw : Except ElfError StaticSymbol :=
  parsed.bind fun parsedElf => parsedElf.findUniqueExecutableFunction zesuDecodeRawName

theorem zesu_decode_raw_resolves : zesuDecodeRaw.isOk = true := by
  native_decide

def layoutIsValid : Bool :=
  match parsed with
  | .ok parsedElf =>
    decide (parsedElf.bytes = bytes) &&
      parsedElf.loadSegments.size > 0 &&
      Elf64.loadSegmentsAreDisjoint parsedElf.loadSegments.toList &&
      parsedElf.loadSegments.toList.any (fun segment =>
        segment.executable && segment.containsMemoryRange parsedElf.header.entry 1)
  | .error _ => false

theorem layout_is_valid : layoutIsValid = true := by
  native_decide

theorem elf_layout :
    elf.bytes = bytes ∧ elf.loadSegments.size > 0 ∧
      Elf64.loadSegmentsAreDisjoint elf.loadSegments.toList = true ∧
      (elf.loadSegments.toList.any fun segment =>
        segment.executable && segment.containsMemoryRange elf.header.entry 1) = true := by
  have h := layout_is_valid
  unfold layoutIsValid at h
  rw [parsed_ok] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hLeft, hEntry⟩
  rcases hLeft with ⟨hLeft, hDisjoint⟩
  rcases hLeft with ⟨hBytes, hSegments⟩
  exact ⟨hBytes, hSegments, hDisjoint, hEntry⟩

end BinaryFv.Zesu.Artifact
