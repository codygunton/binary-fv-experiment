import ZesuSszDecodeProgramImage
import BinaryFv.Ssz.Generated.Level1

namespace BinaryFv.Ssz.Generated

open BinaryFv.Binary

/-- The exact file-backed load image generated from the production SSZ endpoint ELF. -/
abbrev programImage : ProgramImage := Program.image

theorem programImage_artifactSha256 : Program.artifactSha256 = artifactSha256 := by
  decide

end BinaryFv.Ssz.Generated
