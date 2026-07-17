import BinaryFv.Keccak.Reth.Artifact.Analysis.FunctionWordSets
import BinaryFv.RiscV.Analysis.CallGraph

/-!
# The pinned artifact's call-closure results

Reth inputs to, and computed results of, `BinaryFv.RiscV.Analysis.CallGraph`. The closed facts here
use `native_decide` under the approved fixed-artifact exception.
-/

namespace BinaryFv.Keccak

open BinaryFv.RiscV

def entrySyntacticFunctionClosure? : Option (Array Nat) :=
  match artifactEntryWordSet?, artifactFunctionWordSets? with
  | some entry, some sets => some (syntacticFunctionClosureFrom sets entry.function.value)
  | _, _ => none
def entrySyntacticClosureResolvesOnlyParserFunctions : Bool :=
  match artifactFunctionWordSets?, entrySyntacticFunctionClosure? with
  | some sets, some closure => syntacticClosureResolvesOnlyParserFunctions sets closure
  | _, _ => false
def entrySyntacticClosureTargetsAreFunctionStarts : Bool :=
  match artifactFunctionWordSets?, entrySyntacticFunctionClosure? with
  | some sets, some closure => syntacticClosureTargetsAreFunctionStarts sets closure
  | _, _ => false
def entrySyntacticClosureReturnLinksHaveAvailableCallLinks : Bool :=
  match artifactFunctionWordSets?, entrySyntacticFunctionClosure? with
  | some sets, some closure => syntacticClosureReturnLinksHaveAvailableCallLinks sets closure
  | _, _ => false
def entrySyntacticClosureNonEntryReturnCandidatesHaveIncomingResolvedCalls : Bool :=
  match artifactEntryWordSet?, artifactFunctionWordSets?, entrySyntacticFunctionClosure? with
  | some entry, some sets, some closure =>
    syntacticClosureNonEntryReturnCandidatesHaveIncomingResolvedCalls sets closure
      entry.function.value
  | _, _, _ => false
/-- Closed artifact fact for static function-level target resolution, not semantic reachability. -/
theorem entry_syntactic_closure_resolves_only_parser_functions :
    entrySyntacticClosureResolvesOnlyParserFunctions = true := by
  native_decide
/-- Closed syntactic target-start fact; it is not a dynamic control-flow theorem. -/
theorem entry_syntactic_closure_targets_are_function_starts :
    entrySyntacticClosureTargetsAreFunctionStarts = true := by
  native_decide
/-- Closed link-availability fact; it is not a caller/return-pairing or execution theorem. -/
theorem entry_syntactic_closure_return_links_have_available_call_links :
    entrySyntacticClosureReturnLinksHaveAvailableCallLinks = true := by
  native_decide
/-- Closed necessary association for non-entry return candidates, not call/return semantics. -/
theorem entry_syntactic_closure_non_entry_return_candidates_have_incoming_resolved_calls :
    entrySyntacticClosureNonEntryReturnCandidatesHaveIncomingResolvedCalls = true := by
  native_decide

end BinaryFv.Keccak
