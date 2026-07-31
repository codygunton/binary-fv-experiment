import BinaryFv.SSZ.Zesu.Contracts.Catalog
import BinaryFv.SSZ.Zesu.Contracts.CanonicalParams
import BinaryFv.SSZ.Zesu.Artifact.Symbols

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.Binary.Elfling

/-! Canonical-artifact criteria independent of any local-contract decomposition. -/

def IsCanonicalEnvironment (env : DecoderEnvironment) : Prop :=
  env.image = Artifact.programImage ∧ ValidEnvironment env

def sourceProvenanceRecorded (program : Program) : Prop :=
  ∀ functionInstance ∈ program.functionInstances,
    pinnedSourceHash functionInstance.id.function.declaration.file =
        some functionInstance.declProvenance.sourceFileHash ∧
      functionInstance.declProvenance.declSpan.line > 0

def IsCanonicalGeneratedProgram (program : Program) : Prop :=
  program.entry.function = zesuDecodeRawFunctionId ∧
  program.entry.inlineStack = [] ∧
  (∀ functionInstance ∈ program.functionInstances, ∀ range ∈ functionInstance.regions,
    ∀ address, range.start ≤ address → address < range.stop →
      ∃ byte, Artifact.programImage.readByte? address = some byte) ∧
  sourceProvenanceRecorded program ∧
  program.defects = #[]

end BinaryFv.SSZ.Zesu.Contracts
