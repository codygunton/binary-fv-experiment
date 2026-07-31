import BinaryFv.RiscV.ELF.Elf64
import ZesuSszElf

namespace BinaryFv.Zesu.Artifact

open BinaryFv.RiscV

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- The full linked ELF produced by the pinned Nix Zesu derivation. -/
def bytes : ByteArray := ZesuSszElf.bytes

def parsed : Except ElfError Elf64 :=
  Elf64.parse bytes

theorem parsed_is_ok : parsed.isOk = true := by
  native_decide

private theorem exists_ok_of_isOk {ε α : Type} (value : Except ε α)
    (h : value.isOk = true) : ∃ result, value = .ok result := by
  cases value with
  | ok result => exact ⟨result, rfl⟩
  | error _ =>
    simp only [Except.isOk, Except.toBool] at h
    contradiction

theorem exists_parsed : ∃ elf, parsed = .ok elf :=
  exists_ok_of_isOk parsed parsed_is_ok

noncomputable def elf : Elf64 :=
  exists_parsed.choose

theorem parsed_ok : parsed = .ok elf :=
  exists_parsed.choose_spec

end BinaryFv.Zesu.Artifact
