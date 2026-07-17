import BinaryFv.Keccak.Reth.Artifact.Image
import BinaryFv.RiscV.ELF.Decode

/-!
# The artifact's executable word stream

Pure ELF parsing over the pinned image: the executable instruction stream, and the structural
selection of the portable core as the unique largest executable function symbol.

Static by construction — no machine, no decoder, no execution. Decoding these words requires a
configured machine and therefore lives outside `Artifact/`, in `Reth/Analysis/Decode`.
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary
open BinaryFv.RiscV

inductive ArtifactDecodeError where
  | elf (error : ElfError)
  | decode (error : DecodeError)
  | noUniqueLargestFunction
deriving DecidableEq
/-- The complete executable instruction stream, derived solely from the embedded ELF parser. -/
def artifactWords : Except ArtifactDecodeError (Array EncodedWord) := do
  let elf ← Artifact.parsed.mapError .elf
  elf.executableWords.mapError .decode
/-- The portable core is selected structurally from parser-retained executable function symbols. -/
def portableCore : Except ArtifactDecodeError StaticSymbol := do
  let elf ← Artifact.parsed.mapError .elf
  let some core := elf.uniqueLargestExecutableFunction? | throw .noUniqueLargestFunction
  pure core
def portableCoreWords : Except ArtifactDecodeError (Array EncodedWord) := do
  let core ← portableCore
  let words ← artifactWords
  pure (words.filter fun word =>
    core.value ≤ word.address && word.address + 4 ≤ core.value + core.size)

end BinaryFv.Keccak
