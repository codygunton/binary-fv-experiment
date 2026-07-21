import BinaryFv.SSZ.Zesu.Artifact.Image

namespace BinaryFv.SSZ.Zesu.Artifact

open BinaryFv.RiscV

def zesuDecodeRawName : ByteArray := "zesu_decode_raw".toUTF8

def zesuDecodeRaw : Except ElfError StaticSymbol :=
  elf.findUniqueExecutableFunction zesuDecodeRawName

theorem zesu_decode_raw_resolves : zesuDecodeRaw.isOk = true := by
  native_decide

def layoutIsValid : Bool :=
  elf.bytes == bytes &&
    elf.loadSegments.size > 0 &&
    Elf64.loadSegmentsAreDisjoint elf.loadSegments.toList &&
    elf.loadSegments.toList.any (fun segment =>
      segment.executable && segment.containsMemoryRange elf.header.entry 1)

theorem layout_is_valid : layoutIsValid = true := by
  native_decide

end BinaryFv.SSZ.Zesu.Artifact
