import BinaryFv.Zesu.Contracts.Catalog
import BinaryFv.Zesu.Artifacts.Symbols

namespace BinaryFv.Zesu.Contracts

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling

/-!
# Canonical Zesu program

Checks that contract proofs refer to the pinned Zesu image, source provenance, and generated program
rather than to a convenient substitute.
-/

/-- The environment is the canonical one: its loaded image is the pinned Zesu ELF image, and its
layout record is internally consistent. Pinning the image here is what stops a proof from choosing a
convenient environment that trivializes framing. -/
def IsCanonicalEnvironment (env : DecoderEnvironment) : Prop :=
  env.image = Artifacts.programImage ∧ ValidEnvironment env

/-- Validated source provenance on every occurrence: the recorded content hash **equals the pinned
source manifest** entry for the occurrence's declaring file, and the declaration line is real
(`> 0`).

This is what preserves source pinning after moving the hash and line out of the stable `FunctionId`.
The hash clause is now an equality against `pinnedSourceManifest`, not merely non-emptiness — so a
recorded hash that does not match the pinned source (a wrong, stale, or placeholder hash), or an
occurrence attributed to a file not in the manifest, fails the obligation. `pinnedSourceHash` returns
`none` off-manifest, and `none = some _` is false, so off-manifest attribution is rejected. -/
def sourceProvenanceRecorded (program : Program) : Prop :=
  ∀ instance_ ∈ program.instances,
    pinnedSourceHash instance_.id.function.declaration.file
        = some instance_.declProvenance.sourceFileHash ∧
      instance_.declProvenance.declSpan.line > 0

/-- The program is the one generated from the canonical ELF: its entry is the `zesu_decode_raw`
occurrence, that entry is emitted (not inlined), every claimed region lies inside the canonical
loaded code, every occurrence carries validated source provenance, and the extraction left no
unresolved attribution.

The byte-exact instruction check is the extraction row's job; what this states is the coverage tie to
the canonical artifact, so a program that ranges outside the real code, or drops source provenance,
cannot pass. -/
def IsCanonicalGeneratedProgram (program : Program) : Prop :=
  program.entry.function = zesuDecodeRawFunctionId ∧
  program.entry.inlineStack = [] ∧
  (∀ instance_ ∈ program.instances, ∀ range ∈ instance_.regions,
    ∀ address, range.start ≤ address → address < range.stop →
      ∃ byte, Artifacts.programImage.readByte? address = some byte) ∧
  sourceProvenanceRecorded program ∧
  program.defects = #[]


end BinaryFv.Zesu.Contracts
