import BinaryFv.Zesu.Elflings.GeneratedProgramCfg

/-!
# Total edge classification with nothing unclassified (area #5)

The #2 certificate validated that every generated direct edge is a real decoded successor. This module
gives every edge a MEANING: a total classification of the generated edges into exactly the five
categories the review names, with a proof that **nothing is left unclassified** —

* `internal` — source and target are the SAME deepest-inline function instance;
* `inlineChild` — target is inline-nested with the source's function instance (an inlined child's entry, or a
  return up to an inline parent): the two function instances are in an ancestor/descendant `parent?` chain;
* `externalCall` — the target is another emitted function instance's entry that the source function instance calls
  (its identity is in the source's `externalCalls`): a resolved direct call;
* `functionExit` — the source is one of the function instance's generated exit PCs and the edge leaves it
  otherwise (a transfer out that is not a call, an inline move, or an excluded transition);
* `excludedTransition` — the target lies in an excluded routine.

The classifier is a total function into `Option EdgeCategory`; `edges_all_classified` proves it is
`some` for every edge of every function instance — the codomain's `none` (unclassified) is provably empty.
Each `some` branch moreover records the DEFINING fact of its category, so the labels are not arbitrary.
`native_decide` over the concrete edges + the decoded-CFG-validated interface establishes the Bool; the
statements are ordinary bridges.
-/

namespace BinaryFv.Zesu.Elflings.Validation

set_option maxRecDepth 8000

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.Zesu.ControlFlow (controlFlow?)
open BinaryFv.Zesu.Elflings.Generated (generatedProgram generatedExcludedFunctionInstances)

/-! ## Ownership and inline-nesting over the generated function instances -/

/-- The deepest-inline function instance containing `pc`: it contains `pc` and none of its children do. -/
def deepestOwner? (pc : Nat) : Option FunctionInstance :=
  generatedProgram.functionInstances.find? fun functionInstance =>
    inRegions functionInstance pc && functionInstance.children.all fun cid =>
      match generatedProgram.find? cid with
      | some c => !inRegions c pc
      | none => true

/-- `pc` lies inside an excluded routine's region. -/
def inExcluded (pc : Nat) : Bool :=
  generatedExcludedFunctionInstances.any fun x => x.regions.any fun r => decide (r.start ≤ pc ∧ pc < r.stop)

/-- The chain of `parent?` ancestors of a function instance identity (bounded by the function instance count). -/
def ancestorIds : Nat → FunctionInstanceId → List FunctionInstanceId
  | 0, _ => []
  | fuel + 1, id =>
    match generatedProgram.find? id with
    | some functionInstance => match functionInstance.parent? with
      | some pid => pid :: ancestorIds fuel pid
      | none => []
    | none => []

/-- Two function instance identities are in an inline ancestor/descendant relationship. -/
def inlineRelated (a b : FunctionInstanceId) : Bool :=
  (ancestorIds generatedProgram.functionInstances.size a).any (fun x => decide (x = b)) ||
  (ancestorIds generatedProgram.functionInstances.size b).any (fun x => decide (x = a))

/-! ## The five categories and the total classifier -/

inductive EdgeCategory
  | internal
  | inlineChild
  | externalCall
  | functionExit
  | excludedTransition
deriving DecidableEq, Repr

open EdgeCategory

/-- Classify one edge of function instance `functionInstance`. Returns `none` only if the edge fits NONE of the five
categories; `edges_all_classified` proves that never happens. The priority order makes the result a
total function (excluded first, then same-function instance, inline nesting, resolved call, exit). -/
def classifyEdge (functionInstance : FunctionInstance) (e : DirectEdge) : Option EdgeCategory :=
  if inExcluded e.target then some excludedTransition
  else match deepestOwner? e.target with
    | none => none
    | some ot =>
      if ot.id = functionInstance.id then some internal
      else if inlineRelated functionInstance.id ot.id then some inlineChild
      else if e.target = ot.entryPc && functionInstance.externalCalls.any (fun c => decide (c = ot.id)) then
        some externalCall
      else if functionInstance.exitPcs.contains e.source then some functionExit
      else none

/-! ## Nothing is unclassified -/

/-- Every edge of every function instance is classified into one of the five categories. -/
def allClassifiedB : Bool :=
  generatedProgram.functionInstances.all fun functionInstance => functionInstance.edges.all fun e => (classifyEdge functionInstance e).isSome

theorem allClassifiedB_true : allClassifiedB = true := by native_decide

/-- **No edge is left unclassified.** For every function instance and every one of its direct edges, the total
classifier returns a category. -/
theorem edges_all_classified :
    ∀ functionInstance ∈ generatedProgram.functionInstances, ∀ e ∈ functionInstance.edges, (classifyEdge functionInstance e).isSome = true := by
  intro functionInstance ho e he
  exact forall_mem_of_all (forall_mem_of_all allClassifiedB_true functionInstance ho) e he

/-! ## The categories are meaningful (each label records its defining fact) -/

/-- The defining fact an edge's classification records: an `internal` edge's target is the source
function instance itself; an `inlineChild` edge's endpoints are inline-related; an `externalCall` targets a
called function instance's entry; a `functionExit` leaves from a generated exit PC; an `excludedTransition`
targets excluded code. -/
def edgeCategoryJustified (functionInstance : FunctionInstance) (e : DirectEdge) : Bool :=
  match classifyEdge functionInstance e with
  | some internal => match deepestOwner? e.target with
      | some ot => decide (ot.id = functionInstance.id)
      | none => false
  | some inlineChild => match deepestOwner? e.target with
      | some ot => inlineRelated functionInstance.id ot.id
      | none => false
  | some externalCall => match deepestOwner? e.target with
      | some ot => decide (e.target = ot.entryPc) && functionInstance.externalCalls.any (fun c => decide (c = ot.id))
      | none => false
  | some functionExit => functionInstance.exitPcs.contains e.source
  | some excludedTransition => inExcluded e.target
  | none => false

def classificationSoundB : Bool :=
  generatedProgram.functionInstances.all fun functionInstance => functionInstance.edges.all fun e => edgeCategoryJustified functionInstance e

theorem classificationSoundB_true : classificationSoundB = true := by native_decide

/-- **Every classification records the defining fact of its category** — the labels are not arbitrary. -/
theorem classification_sound :
    ∀ functionInstance ∈ generatedProgram.functionInstances, ∀ e ∈ functionInstance.edges, edgeCategoryJustified functionInstance e = true := by
  intro functionInstance ho e he
  exact forall_mem_of_all (forall_mem_of_all classificationSoundB_true functionInstance ho) e he

/-! ## Classification is complete over the decoded successor relation

`edges_all_classified` classifies every EMITTED edge; on its own that would be satisfied even if the
generator had dropped a real edge. Composing it with `edgesComplete_holds` (every decoded direct
successor of every deepest-owned PC is emitted) closes that gap: every decoded direct successor edge
out of a deepest-owned PC is both present in the artifact AND classified into one of the five
categories. There is no decoded edge the classification silently omits. -/

/-- Every decoded direct successor of every deepest-owned PC is an emitted edge that is classified. -/
theorem decoded_successor_edges_classified {nodes : Array ControlFlowNode}
    (hn : controlFlow? = some nodes) :
    ∀ functionInstance ∈ generatedProgram.functionInstances, ∀ r ∈ functionInstance.regions, ∀ k, k < r.size / 4 →
      ownedBy generatedProgram functionInstance (r.start + 4 * k) = true →
        ∀ t ∈ directSuccessorsAt nodes (r.start + 4 * k),
          ∃ e ∈ functionInstance.edges,
            e.source = r.start + 4 * k ∧ e.target = t ∧ (classifyEdge functionInstance e).isSome = true := by
  intro functionInstance ho r hr k hk hown t ht
  obtain ⟨e, he, hbe⟩ := exists_mem_of_any (edgesComplete_holds hn functionInstance ho r hr k hk hown t ht)
  rw [Bool.and_eq_true] at hbe
  exact ⟨e, he, eq_of_beq hbe.1, eq_of_beq hbe.2, edges_all_classified functionInstance ho e he⟩

end BinaryFv.Zesu.Elflings.Validation
