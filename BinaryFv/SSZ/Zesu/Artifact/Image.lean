import BinaryFv.RiscV.ELF.Elf64
import ZesuSszElf

namespace BinaryFv.SSZ.Zesu.Artifact

open BinaryFv.RiscV

/-- The full linked ELF produced by the pinned Nix Zesu derivation. -/
def bytes : ByteArray := ZesuSszElf.bytes

def parsed : Except ElfError Elf64 :=
  Elf64.parse bytes

theorem parses : parsed.isOk = true := by
  native_decide

theorem exists_parsed : ∃ elf, parsed = .ok elf := by
  cases parsed with
  | ok elf => exact ⟨elf, rfl⟩
  | error error => simp at parses

noncomputable def elf : Elf64 :=
  exists_parsed.choose

theorem parsed_ok : parsed = .ok elf :=
  exists_parsed.choose_spec

end BinaryFv.SSZ.Zesu.Artifact
