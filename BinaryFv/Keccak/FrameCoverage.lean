import BinaryFv.Keccak.CallClosure
import BinaryFv.RiscV.Analysis.FrameCoverage

/-!
# The pinned artifact's frame-coverage results

Reth inputs to, and computed results of, `BinaryFv.RiscV.Analysis.FrameCoverage`. The closed fact
here uses `native_decide` under the approved fixed-artifact exception.
-/

namespace BinaryFv.Keccak

open BinaryFv.RiscV
open LeanRV64DExecutable.Functions

/-- Parser-owned closure words; absent selected symbols remain `none`. -/
def entrySyntacticClosureWords? : Option (Array DecodedWord) := do
  let sets ← artifactFunctionWordSets?
  let closure ← entrySyntacticFunctionClosure?
  let selected ← closureWordSets? sets closure
  pure (selected.flatMap FunctionWordSet.words)
def entrySyntacticClosureFrameInventory? : Option (Array FrameCoverageEntry) :=
  entrySyntacticClosureWords?.map fun words => words.map fun word =>
    { word
      constructor := executionConstructor word.instruction
      status := x2FrameStatus word.instruction }
def entrySyntacticClosureFrameStatuses? : Option (Array X2FrameStatus) :=
  entrySyntacticClosureFrameInventory?.map fun inventory => inventory.map FrameCoverageEntry.status
/-- No unclassified constructor or unexpected non-adjustment `x2` write occurs in this closure. -/
def entrySyntacticClosureHasOnlyKnownFrameBuckets : Bool :=
  match entrySyntacticClosureFrameStatuses? with
  | some statuses => statuses.all X2FrameStatus.isClassified
  | none => false
/-- Closed parser classification, not a dynamic-reachability claim. -/
theorem entry_syntactic_closure_has_only_known_frame_buckets :
    entrySyntacticClosureHasOnlyKnownFrameBuckets = true := by
  native_decide

end BinaryFv.Keccak
