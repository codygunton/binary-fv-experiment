import BinaryFv.RiscV.ELF.Elf64
import ZesuSszElf

namespace BinaryFv.SSZ.Zesu.Artifact

open BinaryFv.RiscV

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- The full linked ELF produced by the pinned Nix Zesu derivation. -/
def bytes : ByteArray := ZesuSszElf.bytes

def parsed : Except ElfError Elf64 :=
  Elf64.parse bytes

theorem parsed_is_ok : parsed.isOk = true := by
  native_decide

theorem exists_parsed : ∃ elf, parsed = .ok elf := by
  match h : parsed with
  | .ok elf => exact ⟨elf, h⟩
  | .error error =>
    rw [h] at parsed_is_ok
    simp at parsed_is_ok

noncomputable def elf : Elf64 :=
  exists_parsed.choose

theorem parsed_ok : parsed = .ok elf :=
  exists_parsed.choose_spec

end BinaryFv.SSZ.Zesu.Artifact
