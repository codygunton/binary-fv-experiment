import BinaryFv.Zesu.Artifacts.Image

namespace BinaryFv.Zesu.Artifacts

open BinaryFv.RiscV

def zesuDecodeRawName : ByteArray := "zesu_decode_raw".toUTF8

def zesuDecodeRaw : Except ElfError StaticSymbol :=
  parsed.bind fun parsedElf => parsedElf.findUniqueExecutableFunction zesuDecodeRawName

theorem zesu_decode_raw_resolves : zesuDecodeRaw.isOk = true := by
  native_decide

/-- The layout check at an explicit parsed ELF. Named so `elf_layout` can transport it with the
scrutinee already determined: a `match` left stuck on `parsed` forces the kernel to re-parse the
pinned ELF while checking the transport, which costs 23 s. -/
def layoutIsValidAt (parsedElf : Elf64) : Bool :=
  decide (parsedElf.bytes = bytes) &&
    parsedElf.loadSegments.size > 0 &&
    Elf64.loadSegmentsAreDisjoint parsedElf.loadSegments.toList &&
    parsedElf.loadSegments.toList.any (fun segment =>
      segment.executable && segment.containsMemoryRange parsedElf.header.entry 1)

def layoutIsValid : Bool := (parsed.toOption.map layoutIsValidAt).getD false

/-- Transport a `(e.toOption.map f).getD false = true` fact across `e = .ok a`, generically, so the
kernel checks it once against variables rather than against the parsed artifact. -/
private theorem getD_map_toOption_eq_true {ε α : Type _} {e : Except ε α} {f : α → Bool} {a : α}
    (he : e = .ok a) (h : (e.toOption.map f).getD false = true) : f a = true := by
  subst he; simpa using h

theorem layout_is_valid : layoutIsValid = true := by
  native_decide

theorem elf_layout :
    elf.bytes = bytes ∧ elf.loadSegments.size > 0 ∧
      Elf64.loadSegmentsAreDisjoint elf.loadSegments.toList = true ∧
      (elf.loadSegments.toList.any fun segment =>
        segment.executable && segment.containsMemoryRange elf.header.entry 1) = true := by
  have h : layoutIsValidAt elf = true :=
    getD_map_toOption_eq_true (f := layoutIsValidAt) parsed_ok layout_is_valid
  unfold layoutIsValidAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hLeft, hEntry⟩
  rcases hLeft with ⟨hLeft, hDisjoint⟩
  rcases hLeft with ⟨hBytes, hSegments⟩
  exact ⟨hBytes, hSegments, hDisjoint, hEntry⟩

end BinaryFv.Zesu.Artifacts
