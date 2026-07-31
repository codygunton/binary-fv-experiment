import BinaryFv.Zesu.Contracts.Catalog
import GeneratedProgram

/-!
# Closing the provenance boundary against the independently generated manifest

The handwritten row-1 `pinnedSourceManifest` (in `Contracts/Catalog.lean`) is the address-free
identity layer's record of which pinned source each catalog file hashes to. This module proves it is
not merely *asserted* but *checked* against the manifest the generator emits from the exact source it
read (`Generated.generatedSourceManifest`), and that every function instance's recorded declaration line is
the routine's DWARF-resolved declaration (`Generated.generatedDeclLines`), not merely positive.

Together with `sourceProvenanceRecorded` (which already checks each function instance's `sourceFileHash` for
*equality* with `pinnedSourceManifest`), this ties: handwritten manifest = generated manifest, each
function instance hash = manifest entry, and each function instance declaration line = the resolved declaration —
so a wrong, stale, or placeholder hash or line cannot pass. All checks are small `native_decide`s over
the concrete generated data plus the handwritten catalog; no `sorry`, no axiom.
-/

namespace BinaryFv.Zesu.Elfling.Validation

open BinaryFv.Binary.Elfling
open BinaryFv.Zesu.Contracts (pinnedSourceManifest)
open BinaryFv.Zesu.Elfling.Generated
  (generatedProgram generatedSourceManifest generatedDeclLines)

/-! ## 1. The handwritten manifest is checked against the generated one -/

/-- The handwritten manifest as `(path, hash)` pairs, dropping the `SourceFile` wrapper so it can be
compared to the generator's `(path, hash)` manifest directly. -/
def pinnedManifestPairs : List (String × String) :=
  pinnedSourceManifest.map (fun entry => (entry.1.path, entry.2))

/-- **The handwritten `pinnedSourceManifest` denotes the same `(path, hash)` set as the independently
generated `generatedSourceManifest`**: every handwritten entry is generated and vice versa, with equal
cardinality (both lists are duplicate-free), so the row-1 hashes are validated against the source the
generator actually read rather than trusted. -/
theorem pinned_manifest_matches_generated :
    pinnedManifestPairs.all (fun e => generatedSourceManifest.contains e) = true ∧
    generatedSourceManifest.all (fun e => pinnedManifestPairs.contains e) = true ∧
    pinnedManifestPairs.length = generatedSourceManifest.length := by native_decide

/-! ## 2. Every function instance's declaration line matches its routine's resolved declaration -/

/-- Whether a function instance's declaration line equals the DWARF-resolved declaration line recorded for
its routine in `generatedDeclLines`. -/
def functionInstanceDeclResolved (functionInstance : FunctionInstance) : Bool :=
  generatedDeclLines.contains
    (functionInstance.id.function.declaration.qualifiedName, functionInstance.declProvenance.declSpan.line)

/-- **Every generated function instance's `declSpan` line is its routine's resolved declaration line.** Since
`generatedDeclLines` carries one line per routine (and the generator surfaces a defect if two
function instances of a routine disagree), this is the "declaration span matches the resolved source
declaration" check the review asked for — strictly stronger than `declSpan.line > 0`. -/
theorem every_function_instance_declSpan_matches_resolved :
    generatedProgram.functionInstances.all functionInstanceDeclResolved = true := by native_decide

end BinaryFv.Zesu.Elfling.Validation
