import BinaryFv.Keccak.Reth.Analysis.StackFlow
import BinaryFv.Keccak.Reth.Artifact.Layout

/-!
# Frontier-truncated stack-flow diagnostics

Parser-derived totals over the entry's call closure, closed with `native_decide` under the approved
fixed-artifact exception.

**These are diagnostic evidence, not a semantic stack bound.** The closure summaries they are built
from are frontier-truncated, so they say nothing about call paths beyond the frontier. The
conditional runtime machinery that *does* carry a real depth budget is
`Reth/Proof/Common/StackWindow.lean`, and the binary-wide stack-safety proof is deferred to the
sponge/caller trace stage, where the actual call paths exist to discharge each budget premise.
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary
open BinaryFv.RiscV

/-- **Diagnostic, not a bound.**  Sum of the per-function `maximumExploredDownwardDelta` over the
    parser-derived entry call closure.

    Each function contributes its truncated maximum once.  This is *evidence*, not an
    over-approximation of any call chain: the summaries are frontier-truncated, so the summands are
    not themselves per-function bounds, and no call-path structure has been established.

    The `none` default deliberately exceeds the page, so the comparisons below also certify that the
    static summaries are available. -/
def frontierSummaryTotalDownwardDelta : Nat :=
  match entryClosureFrontierTruncatedStackStateSummaries? with
  | some summaries =>
    summaries.foldl (fun acc s => acc + s.maximumExploredDownwardDelta) 0
  | none => stackPageSize + 1
/-- **Diagnostic, not a bound.**  The single largest per-function truncated explored downward delta
    across the entry call closure.  Frontier-truncated, so this is not a bound on any function's
    actual frame. -/
def frontierSummaryMaxSingleDownwardDelta : Nat :=
  match entryClosureFrontierTruncatedStackStateSummaries? with
  | some summaries =>
    summaries.foldl (fun acc s => max acc s.maximumExploredDownwardDelta) 0
  | none => stackPageSize + 1
/-- **Diagnostic.**  Closed parser fact: the summed truncated downward-delta figure of the entry
    closure summary.  Evidence about a truncated exploration; not a claim about any call chain. -/
theorem diagnostic_frontierSummaryTotalDownwardDelta_eq :
    frontierSummaryTotalDownwardDelta = 1664 := by
  native_decide
/-- **Diagnostic.**  Closed parser fact: the largest single-function truncated downward-delta
    figure. -/
theorem diagnostic_frontierSummaryMaxSingleDownwardDelta_eq :
    frontierSummaryMaxSingleDownwardDelta = 912 := by
  native_decide
/-- **Diagnostic.**  The summed truncated figure happens to fit within the canonical 4 KiB page.

    This is a comparison of two numbers, and it also certifies that the static summaries parsed
    (the `none` default exceeds the page).  It is **not** the statement that the binary's stack use
    fits in a page, and it does **not** bound the deltas along any call chain: the summands come
    from a truncated exploration.  Proving the real bound is deferred to the sponge/caller trace
    stage. -/
theorem diagnostic_frontierSummaryTotalDownwardDelta_le_stackPageSize :
    frontierSummaryTotalDownwardDelta ≤ stackPageSize := by
  native_decide
/-- **Diagnostic.**  The largest single truncated figure fits within the canonical 4 KiB page.  Same
    caveats as above. -/
theorem diagnostic_frontierSummaryMaxSingleDownwardDelta_le_stackPageSize :
    frontierSummaryMaxSingleDownwardDelta ≤ stackPageSize := by
  native_decide

end BinaryFv.Keccak
