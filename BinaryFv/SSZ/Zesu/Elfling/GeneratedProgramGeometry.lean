import BinaryFv.SSZ.Zesu.Contracts.ProgramCorrectness
import BinaryFv.SSZ.Zesu.Elfling.GeneratedProgramValidation
import GeneratedProgram

/-!
# The generated program's dependency graph and address geometry

`global_of_local` composes the 141 local trace obligations into the 141 closed ones, and it consumes
exactly two things about the program besides those obligations: a rank witnessing that the transfer
graph is acyclic, and the `ProgramGeometry` relating each occurrence's owned addresses, its execution
extent, and its exits. This module discharges both for the one canonical generated program, by
evaluation on the generated data — no local correctness is used, and nothing is assumed.

*The rank is not invented.* `generatedRank` is the number of identities reachable from an occurrence
in the transfer graph. On an acyclic graph a callee's reachable set is a proper subset of its
caller's — the caller reaches everything the callee does, plus itself — so the size strictly
decreases along every edge. If the extraction ever produced a cycle the count would stop decreasing
and `callGraphRanked_check` would evaluate to `false`, which is the point: acyclicity is checked on
the real graph rather than supplied as a convenient witness.

*The geometry is where the boundary inventory bites.* `calleeExitContainment` says a caller's exit
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

/-! ## The occurrence inventory is exactly the expected one -/

/-- The canonical program has exactly 141 occurrences. Every later count — the manifest's rows, the
local assumption's conjuncts, the coverage report's lines — is checked against this number rather
than against a separately maintained constant. -/
theorem generated_occurrence_count : generatedProgram.instances.size = 141 := by native_decide

/-- The canonical program surfaces exactly 12 reachable-but-uncataloged routines, absorbed by their
callers. -/
theorem generated_excluded_count : generatedProgram.excluded.size = 12 := by native_decide

/-- The entry is the exported `zesu_decode_raw` wrapper, not inlined into anything. -/
theorem generated_entry_is_exported :
    generatedProgram.entry.function = zesuDecodeRawFunctionId ∧
      generatedProgram.entry.inlineStack = [] := ⟨by decide, rfl⟩

/-- Exactly one occurrence carries the entry identity. Together with `instanceIdsDistinct_holds` this
is what makes "the entry occurrence" a definite description rather than a choice. -/
def entryOccurrenceUniqueB : Bool :=
  (generatedProgram.instances.filter fun i => decide (i.id = generatedProgram.entry)).size == 1

theorem entry_occurrence_unique : entryOccurrenceUniqueB = true := by native_decide

/-- Every occurrence dispatches to a catalog entry, so `instanceObligation` is never the `False`
branch. This is the totality the local assumption depends on: a single occurrence with no contract
would make one conjunct unprovable rather than merely unproved. -/
def catalogDispatchTotalB : Bool :=
  generatedProgram.instances.all fun i => (catalogEntryFor i.id.function).isSome

theorem catalog_dispatch_total : catalogDispatchTotalB = true := by native_decide

/-! ## The rank -/

/-- The number of identities an occurrence reaches in the transfer graph, itself included. On an
acyclic graph this strictly decreases along every edge, which is what `callGraphRanked_check`
verifies on the real data. -/
def generatedRank (instance_ : FunctionInstance) : Nat :=
  (Program.transferClosure generatedProgram instance_.id).size

theorem callGraphRanked_check : callGraphRankedB generatedProgram generatedRank = true := by
  native_decide

/-- **The generated call/inline graph is acyclic.** -/
theorem generated_call_graph_ranked : CallGraphRanked generatedProgram generatedRank :=
  callGraphRanked_of_check callGraphRanked_check

/-- No occurrence is among its own dependencies. A direct consequence of the rank, recorded
separately because it is the specific anti-circularity property the plan asks for. -/
theorem generated_no_self_dependency :
    ∀ instance_ ∈ generatedProgram.instances,
      instance_ ∉ calleeInstances generatedProgram instance_ := by
  intro instance_ hinst hself
  have h := generated_call_graph_ranked instance_ hinst instance_ hself
  omega

/-! ## The address geometry -/

theorem programGeometry_check : programGeometryB generatedProgram = true := by native_decide

/-- **The generated address geometry holds.** Owned ⊆ execution extent, callee extent ⊆ caller
extent, and every caller exit inside a callee's extent is a callee exit. -/
theorem generated_program_geometry : ProgramGeometry generatedProgram :=
  programGeometry_of_check programGeometry_check

/-! ## Every callee identity resolves -/

/-- Every identity an occurrence may transfer to is either another occurrence or one of the surfaced
excluded routines. Nothing is reached that the program does not account for. -/
def calleesResolveB : Bool :=
  generatedProgram.instances.all fun i =>
    (i.children ++ i.externalCalls).all fun callee =>
      generatedProgram.instances.any (fun other => decide (other.id = callee)) ||
        generatedProgram.excluded.any (fun x => decide (x.id = callee))

theorem callees_resolve_check : calleesResolveB = true := by native_decide

theorem generated_callees_resolve :
    ∀ instance_ ∈ generatedProgram.instances,
      ∀ callee ∈ (instance_.children ++ instance_.externalCalls),
        (∃ calleeInstance ∈ generatedProgram.instances, calleeInstance.id = callee) ∨
          (∃ absorbed ∈ generatedProgram.excluded, absorbed.id = callee) := by
  intro instance_ hinst callee hcallee
  have hrow := forall_mem_of_all callees_resolve_check instance_ hinst
  have h := forall_mem_of_all hrow callee hcallee
  rcases Bool.or_eq_true _ _ |>.mp h with h' | h'
  · obtain ⟨other, hother, heq⟩ := exists_mem_of_any h'
    exact Or.inl ⟨other, hother, of_decide_eq_true heq⟩
  · obtain ⟨x, hx, heq⟩ := exists_mem_of_any h'
    exact Or.inr ⟨x, hx, of_decide_eq_true heq⟩

end BinaryFv.SSZ.Zesu.Elfling.Validation
