import BinaryFv.Keccak.Reth.Analysis.CallClosure
import BinaryFv.RiscV.Analysis.StackDataFlow

/-!
# The pinned artifact's stack-flow results

Reth inputs to, and computed results of, `BinaryFv.RiscV.Analysis.StackDataFlow`. The closed facts
here use `native_decide` under the approved fixed-artifact exception. They are frontier-truncated
diagnostics, not a binary-wide stack bound.
-/

namespace BinaryFv.Keccak

open BinaryFv.RiscV

def entrySyntacticClosureStackWritesClassified : Bool :=
  match artifactFunctionWordSets?, entrySyntacticFunctionClosure? with
  | some sets, some closure => syntacticClosureStackWritesClassified sets closure
  | _, _ => false
/-- Closed static inspection: all selected closure writes to `sp` are classified adjustments. -/
theorem entry_syntactic_closure_stack_writes_classified :
    entrySyntacticClosureStackWritesClassified = true := by
  native_decide
def entryClosureIntraproceduralStackFlows? :
    Option (Array (Nat × Except StackFlowError IntraproceduralStackFlow)) :=
  match artifactFunctionWordSets?, entrySyntacticFunctionClosure? with
  | some sets, some closure =>
    some <| closure.map fun start =>
      match functionWordSetAtStart? sets start with
      | some set => (start, intraproceduralStackDeltaFlow set)
      | none => (start, .error (.missingNode start))
  | _, _ => none
def entryClosureIntraproceduralStackFlowsSucceed : Bool :=
  match entryClosureIntraproceduralStackFlows? with
  | some flows => flows.all fun flow => flow.2.isOk
  | none => false
def entryClosureFrontierTruncatedStackStateSummaries? :
    Option (Array FrontierTruncatedStackStateSummary) :=
  match entryClosureIntraproceduralStackFlows? with
  | some flows =>
    flows.foldl (fun summaries flow =>
      match summaries, flow.2 with
      | some summaries, .ok result =>
        some <| summaries.push {
          functionStart := flow.1
          maximumExploredDownwardDelta := maximumExploredDownwardDelta result
          frontierCount := result.frontiers.size
        }
      | _, _ => none) (some #[])
  | none => none
def entryClosureFrontierTruncatedStackStateSummariesAvailable : Bool :=
  entryClosureFrontierTruncatedStackStateSummaries?.isSome
/--
Closed availability fact for static frontier-truncated state summaries. It is not a stack-bound
theorem; a later proof must discharge the recorded frontiers before drawing that conclusion.
-/
theorem entry_closure_frontier_truncated_stack_state_summaries_available :
    entryClosureFrontierTruncatedStackStateSummariesAvailable = true := by
  native_decide
/--
Closed static exploration fact. It does not provide a stack bound or establish that generated Sail
execution follows the explored edges.
-/
theorem entry_closure_intraprocedural_stack_flows_succeed :
    entryClosureIntraproceduralStackFlowsSucceed = true := by
  native_decide

end BinaryFv.Keccak
