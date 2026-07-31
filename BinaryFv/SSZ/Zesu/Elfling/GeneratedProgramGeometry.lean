import BinaryFv.SSZ.Zesu.Contracts.ProgramCorrectness
import BinaryFv.SSZ.Zesu.Elfling.GeneratedProgramValidation
import GeneratedProgram

/-!
# Checking the program shape required by composition

`global_of_local` needs two structural facts about the 141 generated function instances: calls and inlining
must form an acyclic dependency graph, and each child's address extent and exits must fit its parent.
This module checks both facts on the canonical generated program without using any local correctness
proof.

*The rank is not invented.* `generatedRank` is the number of identities reachable from a function instance
in the transfer graph. On an acyclic graph a callee's reachable set is a proper subset of its
caller's — the caller reaches everything the callee does, plus itself — so the size strictly
decreases along every edge. If the extraction ever produced a cycle the count would stop decreasing
and `callGraphRanked_check` would evaluate to `false`, which is the point: acyclicity is checked on
the real graph rather than supplied as a convenient witness.

The geometry check includes `calleeExitContainment`: a caller's exit
that lies inside a callee's extent is already an exit of that callee. For a separately emitted callee
this is vacuous (the address sets are disjoint); for an inlined child, whose regions sit inside its
parent's, it is a real constraint on the generated exit inventories, and it is exactly what stops a
spliced child running through its parent's return. `CompositionTests` exhibits a program that fails
it.
-/

namespace BinaryFv.SSZ.Zesu.Elfling.Validation

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedProgram)

/-! ## The function instance inventory is exactly the expected one -/

/-- The canonical program has exactly 141 function instances. Every later count — the manifest's rows, the
local assumption's conjuncts, the coverage report's lines — is checked against this number rather
than against a separately maintained constant. -/
theorem generated_function_function_instance_count : generatedProgram.functionInstances.size = 141 := by native_decide

/-- The canonical program surfaces exactly 12 reachable-but-uncataloged routines, absorbed by their
callers. -/
theorem generated_excluded_count : generatedProgram.excludedFunctionInstances.size = 12 := by native_decide

/-- The entry is the exported `zesu_decode_raw` wrapper, not inlined into anything. -/
theorem generated_entry_is_exported :
    generatedProgram.entry.function = zesuDecodeRawFunctionId ∧
      generatedProgram.entry.inlineStack = [] := ⟨by decide, rfl⟩

/-- Exactly one function instance carries the entry identity. Together with `functionInstanceIdsDistinct_holds` this
is what makes "the entry function instance" a definite description rather than a choice. -/
def entryFunctionInstanceUniqueB : Bool :=
  (generatedProgram.functionInstances.filter fun i => decide (i.id = generatedProgram.entry)).size == 1

theorem entry_function_instance_unique : entryFunctionInstanceUniqueB = true := by native_decide

/-- Every function instance dispatches to a catalog entry, so `functionInstanceObligation` is never the `False`
branch. This is the totality the local assumption depends on: a single function instance with no contract
would make one conjunct unprovable rather than merely unproved. -/
def catalogDispatchTotalB : Bool :=
  generatedProgram.functionInstances.all fun i => (catalogEntryFor i.id.function).isSome

theorem catalog_dispatch_total : catalogDispatchTotalB = true := by native_decide

/-! ## The rank -/

/-- The number of identities a function instance reaches in the transfer graph, itself included. On an
acyclic graph this strictly decreases along every edge, which is what `callGraphRanked_check`
verifies on the real data. -/
def generatedRank (functionInstance : FunctionInstance) : Nat :=
  (Program.transferClosure generatedProgram functionInstance.id).size

theorem callGraphRanked_check : callGraphRankedB generatedProgram generatedRank = true := by
  native_decide

/-- **The generated call/inline graph is acyclic.** -/
theorem generated_call_graph_ranked : CallGraphRanked generatedProgram generatedRank :=
  callGraphRanked_of_check callGraphRanked_check

/-- No function instance is among its own dependencies. A direct consequence of the rank, recorded
separately because it is the specific anti-circularity property the plan asks for. -/
theorem generated_no_self_dependency :
    ∀ functionInstance ∈ generatedProgram.functionInstances,
      functionInstance ∉ calleeFunctionInstances generatedProgram functionInstance := by
  intro functionInstance hinst hself
  have h := generated_call_graph_ranked functionInstance hinst functionInstance hself
  omega

/-! ## The address geometry -/

theorem programGeometry_check : programGeometryB generatedProgram = true := by native_decide

/-- **The generated address geometry holds.** Owned ⊆ execution extent, callee extent ⊆ caller
extent, and every caller exit inside a callee's extent is a callee exit. -/
theorem generated_program_geometry : ProgramGeometry generatedProgram :=
  programGeometry_of_check programGeometry_check

/-! ## Every callee identity resolves -/

/-- Every identity a function instance may transfer to is either another function instance or one of the surfaced
excluded routines. Nothing is reached that the program does not account for. -/
def calleesResolveB : Bool :=
  generatedProgram.functionInstances.all fun i =>
    (i.children ++ i.externalCalls).all fun callee =>
      generatedProgram.functionInstances.any (fun other => decide (other.id = callee)) ||
        generatedProgram.excludedFunctionInstances.any (fun x => decide (x.id = callee))

theorem callees_resolve_check : calleesResolveB = true := by native_decide

theorem generated_callees_resolve :
    ∀ functionInstance ∈ generatedProgram.functionInstances,
      ∀ callee ∈ (functionInstance.children ++ functionInstance.externalCalls),
        (∃ calleeFunctionInstance ∈ generatedProgram.functionInstances, calleeFunctionInstance.id = callee) ∨
          (∃ absorbed ∈ generatedProgram.excludedFunctionInstances, absorbed.id = callee) := by
  intro functionInstance hinst callee hcallee
  have hrow := forall_mem_of_all callees_resolve_check functionInstance hinst
  have h := forall_mem_of_all hrow callee hcallee
  rcases Bool.or_eq_true _ _ |>.mp h with h' | h'
  · obtain ⟨other, hother, heq⟩ := exists_mem_of_any h'
    exact Or.inl ⟨other, hother, of_decide_eq_true heq⟩
  · obtain ⟨x, hx, heq⟩ := exists_mem_of_any h'
    exact Or.inr ⟨x, hx, of_decide_eq_true heq⟩

end BinaryFv.SSZ.Zesu.Elfling.Validation
