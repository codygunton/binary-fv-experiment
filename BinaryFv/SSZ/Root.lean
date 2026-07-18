import BinaryFv.SSZ.Zesu.Artifact.Layout
import BinaryFv.SSZ.Zesu.Interface

namespace BinaryFv.SSZ

open BinaryFv.RiscV

/-- The one canonical, Nix-built Zesu executable covered by the SSZ proof. -/
noncomputable def binary : RiscvSpec.ValidatedElf := {
  bytes := Zesu.Artifact.bytes
  elf := Zesu.Artifact.elf
  parsed_ok := by exact Zesu.Artifact.parsed_ok
  layout := Zesu.Artifact.elf_layout
}

/-- The final Amsterdam V4 compliance statement, scaffolded until Stages 5–7. -/
theorem root_compliance :
    forall input : ByteArray,
      input.size < 2 * 1024 * 1024 ->
        RiscvSpec.execute binary input = .ok (SszSpec.decode input) := by
  intro _input _inputBound
  sorry

end BinaryFv.SSZ
