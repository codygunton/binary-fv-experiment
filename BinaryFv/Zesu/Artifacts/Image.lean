import ZesuSszDecodeProgramImage
import BinaryFv.Zesu.Elflings.GeneratedLevel1

namespace BinaryFv.Zesu.Artifacts

open BinaryFv.Binary

/-- The exact file-backed load image generated from the production SSZ endpoint ELF. -/
abbrev programImage : ProgramImage := Program.image

theorem programImage_artifactSha256 : Program.artifactSha256 = Elflings.artifactSha256 := by
  decide

end BinaryFv.Zesu.Artifacts
