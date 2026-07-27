import BinaryFv.SSZ.Zesu.Elfling.GeneratedProgramCfg
import GeneratedManifest

/-!
# Static boundary satisfiability — is each local obligation even *inhabitable*? (falsification evidence)

Every per-function-instance local obligation is `LocallyImplementsFunctionInstance`, whose conclusion
carries an `EnteredScopedTrace`. That structure and the two splice constructors it admits each impose
a *structural* side condition on the generated artifact, entirely independent of any run:

| condition | where it lives | what it costs if false |
| --- | --- | --- |
| `entryPc` is not one of the instance's own `exitPcs` | `EnteredScopedTrace.entryNotExit` | the trace type is **uninhabited**: the obligation is unprovable (or vacuous, if `pre` is too) |
| a resolved call pc is not one of the caller's `exitPcs` | `CallTransfer.callNotExit` | `ScopedTrace.callStep` cannot fire at that site |
| some parent edge crosses *out of* an inlined child back into the parent | `InlineBoundary.validFor` ∧ `InlineTransfer.exitEdgeMem` | `ScopedTrace.inlineStep` is **dead code** for that pair |

This module decides all three against `generatedProgram`, per instance and per pair, and reports the
violating sets by address. **It is a measurement, not a gate.** All three conditions are red today;
the numbers below are pinned as exact values so that a change to the extractor moves a
kernel-checked constant instead of quietly re-colouring a report.

It lives under `Validation/` because that is what it is: evidence about how the artifact fails to
support the obligations stated over it. Nothing in the theorem graph imports it, and the
validation-import guard in `nix/proof.nix` enforces that mechanically.

## What is *not* claimed

* A `true` here is **satisfiability of one side condition**, never provability of the obligation. The
  contract's `pre`/`post` are not consulted at all — that is `ContractGroundTruth`.
* A `false` here IS conclusive in the other direction: the side condition is decided from the
  generated data alone, so a violation is a real structural defect, not a sampling gap.

## Anti-vacuity

Every column is exhibited going *both* ways over the real artifact, except the inline exit-edge
column, which is `false` 127 times out of 127. A check with no observed pass is exactly the defect
this project keeps finding, so that column additionally carries `inline_exit_edge_repairable_pairs`:
re-attributing the child's own out-edges to the parent makes 56 of the 127 pass. That is the witness
that the predicate is satisfiable in principle and that the zero is a property of the generator's
edge attribution rather than of a check incapable of returning `true`.
-/

namespace BinaryFv.SSZ.Zesu.Validation.Boundary

set_option maxRecDepth 8000

open BinaryFv.Binary.Elfling
open BinaryFv.SSZ.Zesu.ControlFlow (controlFlow?)
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedProgram generatedManifest)
open BinaryFv.SSZ.Zesu.Elfling.Validation (isResolvedCallAt regionPcList)

/-! ## Verdicts

A verdict is never a bare `Bool`: a violation carries the name of the clause it violates, so the
name and the reading cannot drift apart. `gap` is an explicit "not decided here" and is never
reported as a pass. -/

/-- The outcome of one structural check on one row. -/
inductive Verdict where
  /-- The side condition is satisfiable on this row. -/
  | ok
  /-- The side condition is refuted; `clause` names the structure field that becomes uninhabited. -/
  | violated (clause : String)
  /-- Not applicable / not decided here, with the reason. Never a pass. -/
  | gap (why : String)
deriving Repr, DecidableEq, Inhabited

/-- Whether a verdict is a genuine pass. `gap` is deliberately not. -/
def Verdict.isOk : Verdict → Bool
  | .ok => true
  | _ => false

/-- Whether a verdict is a genuine refutation. -/
def Verdict.isViolated : Verdict → Bool
  | .violated _ => true
  | _ => false

def Verdict.render : Verdict → String
  | .ok => "ok"
  | .violated c => "FAIL " ++ c
  | .gap w => "gap(" ++ w ++ ")"

/-! ## Condition 1 — `EnteredScopedTrace.entryNotExit`

`EnteredScopedTrace` requires `¬ exit entry`, and the exit predicate of a generated instance is
exactly `isExit`, i.e. membership in `exitPcs`. So an instance whose `entryPc` appears in its own
`exitPcs` has an uninhabited `EnteredScopedTrace` — its local obligation cannot be discharged at
all, and is *vacuously true* only if its `pre` is additionally unsatisfiable. -/

/-- The instance declares its own entry pc an exit. -/
def entryIsOwnExit (o : FunctionInstance) : Bool := o.exitPcs.contains o.entryPc

def entryNotExitVerdict (o : FunctionInstance) : Verdict :=
  if entryIsOwnExit o then .violated "EnteredScopedTrace.entryNotExit" else .ok

/-- The entry pcs of every instance that declares its own entry an exit. -/
def entryIsOwnExitPcs (program : Program) : Array Nat :=
  (program.functionInstances.filter entryIsOwnExit).map (·.entryPc)

/-! ## Condition 2 — `CallTransfer.callNotExit`

A resolved direct call inside an instance's own regions is a site at which `ScopedTrace.callStep`
could fire; `CallTransfer.callNotExit` requires that pc not be a declared exit of the caller. This
is the condition whose *aggregate* is already pinned in the proof graph
(`generated_call_rows`: 180 rows, 173 satisfiable); here it is resolved per instance so the seven
offenders can be named. -/

/-- Resolved-call pcs inside `o`'s own regions that `o` also declares an exit. -/
def callSitesDeclaredExit (nodes : Array BinaryFv.RiscV.ControlFlowNode) (o : FunctionInstance) : List Nat :=
  (regionPcList o).filter fun pc => isResolvedCallAt nodes pc && o.exitPcs.contains pc

/-- Resolved-call pcs inside `o`'s own regions, whether or not declared exits. -/
def callSites (nodes : Array BinaryFv.RiscV.ControlFlowNode) (o : FunctionInstance) : List Nat :=
  (regionPcList o).filter fun pc => isResolvedCallAt nodes pc

def callNotExitVerdict (nodes : Array BinaryFv.RiscV.ControlFlowNode) (o : FunctionInstance) : Verdict :=
  match callSites nodes o, callSitesDeclaredExit nodes o with
  | [], _ => .gap "no resolved call site"
  | _, [] => .ok
  | _, _ => .violated "CallTransfer.callNotExit"

/-! ## Condition 3 — `InlineBoundary` edge inhabitance

`ScopedTrace.inlineStep` consumes an `InlineTransfer`, which pins an `exitEdge ∈ ib.exits`, and
`InlineBoundary.validFor` requires **every** member of `ib.exits` to be an edge *of the parent*
whose source is owned by the child and whose target is owned by the parent but not the child. A
prover picks `ib.exits`, so the splice is available for a pair exactly when at least one such parent
edge exists. Same shape for `ib.entries` (used by the preceding parent step). -/

/-- `e` crosses INTO the child: parent-owned, non-child source; child-owned target. -/
def crossesIn (parent child : FunctionInstance) (e : DirectEdge) : Bool :=
  parent.containsAddress e.source && !child.containsAddress e.source &&
    child.containsAddress e.target

/-- `e` crosses OUT of the child: child-owned source; target leaves the child and lands in the
parent. -/
def crossesOut (parent child : FunctionInstance) (e : DirectEdge) : Bool :=
  child.containsAddress e.source && !child.containsAddress e.target &&
    parent.containsAddress e.target

/-- Some PARENT edge crosses into the child — `ib.entries` can be nonempty. -/
def inlineEntryInhabited (parent child : FunctionInstance) : Bool :=
  parent.edges.any (crossesIn parent child)

/-- Some PARENT edge crosses out of the child — `ib.exits` can be nonempty, i.e. `inlineStep` is
available for this pair. -/
def inlineExitInhabited (parent child : FunctionInstance) : Bool :=
  parent.edges.any (crossesOut parent child)

/-- The same test with the CHILD's own edge array added to the candidate pool. This is not a valid
`InlineBoundary` — `validFor` demands `e ∈ functionInstance.edges`, the parent's array — it is the
mutant that measures how much of the failure is edge *attribution* rather than absence of a
crossing edge. -/
def inlineExitInhabitedIfChildEdgesCounted (parent child : FunctionInstance) : Bool :=
  (parent.edges ++ child.edges).any (crossesOut parent child)

/-- Every declared (parent, child) inline pair whose child identity resolves to an instance. -/
def inlinePairs (program : Program) : Array (FunctionInstance × FunctionInstance) :=
  program.functionInstances.foldl (fun acc o =>
    o.children.foldl (fun acc cid =>
      match program.find? cid with
      | some c => acc.push (o, c)
      | none => acc) acc) #[]

/-- Declared children whose identity resolves to no instance. A nonzero count would make the pair
counts below a statement about a subset, so it is pinned separately. -/
def unresolvedChildCount (program : Program) : Nat :=
  program.functionInstances.foldl (fun n o =>
    n + (o.children.filter fun cid => (program.find? cid).isNone).size) 0

def inlineEntryVerdict (parent : FunctionInstance) (children : Array FunctionInstance) : Verdict :=
  if children.isEmpty then .gap "no inlined child"
  else if children.all (inlineEntryInhabited parent) then .ok
  else .violated "InlineBoundary.validFor(entries)"

def inlineExitVerdict (parent : FunctionInstance) (children : Array FunctionInstance) : Verdict :=
  if children.isEmpty then .gap "no inlined child"
  else if children.all (inlineExitInhabited parent) then .ok
  else .violated "InlineTransfer.exitEdgeMem"

/-! ## The per-instance report -/

/-- One instance's three structural verdicts, plus the raw material behind them. -/
structure BoundaryRow where
  index : Nat
  qualifiedName : String
  routineTag : String
  entryPc : Nat
  entryNotExit : Verdict
  callNotExit : Verdict
  inlineEntryEdges : Verdict
  inlineExitEdges : Verdict
  /-- Resolved call pcs the caller also declares an exit — the `callNotExit` counterexamples. -/
  offendingCallPcs : List Nat
  /-- Entry pcs of children with no crossing-out parent edge — the `inlineStep` counterexamples. -/
  childrenWithoutExitEdge : Array Nat
  childCount : Nat
deriving Repr, Inhabited

/-- The manifest row at `index`, for the routine tag and qualified name. The row-wise agreement of
the manifest with `generatedProgram` is pinned by `manifest_matches_program_rowwise` below, so this
join is checked rather than assumed. -/
private def manifestAt (index : Nat) : Option BinaryFv.SSZ.Zesu.Elfling.Generated.ManifestRow :=
  generatedManifest[index]?

def boundaryRow (nodes : Array BinaryFv.RiscV.ControlFlowNode) (program : Program) (index : Nat)
    (o : FunctionInstance) : BoundaryRow :=
  let children := o.children.filterMap program.find?
  { index := index
    qualifiedName := (manifestAt index).elim o.id.function.declaration.qualifiedName (·.qualifiedName)
    routineTag := (manifestAt index).elim "?" (·.routineTag)
    entryPc := o.entryPc
    entryNotExit := entryNotExitVerdict o
    callNotExit := callNotExitVerdict nodes o
    inlineEntryEdges := inlineEntryVerdict o children
    inlineExitEdges := inlineExitVerdict o children
    offendingCallPcs := callSitesDeclaredExit nodes o
    childrenWithoutExitEdge :=
      (children.filter fun c => !inlineExitInhabited o c).map (·.entryPc)
    childCount := children.size }

def boundaryRows (nodes : Array BinaryFv.RiscV.ControlFlowNode) (program : Program) : Array BoundaryRow :=
  (program.functionInstances.zipIdx.map fun (o, i) => boundaryRow nodes program i o)

/-! ## Rendering -/

private def pad (n : Nat) (s : String) : String :=
  if s.length ≥ n then s else s ++ String.ofList (List.replicate (n - s.length) ' ')

private def natList (xs : List Nat) : String :=
  match xs with
  | [] => "-"
  | _ => String.intercalate "," (xs.map toString)

def BoundaryRow.render (r : BoundaryRow) : String :=
  String.intercalate " | "
    [ pad 3 (toString r.index)
    , pad 22 r.routineTag
    , pad 6 (toString r.entryPc)
    , pad 34 r.entryNotExit.render
    , pad 26 r.callNotExit.render
    , pad 32 r.inlineEntryEdges.render
    , pad 30 r.inlineExitEdges.render
    , natList r.offendingCallPcs
    , natList r.childrenWithoutExitEdge.toList ]

def header : String :=
  String.intercalate " | "
    [ pad 3 "idx", pad 22 "routineTag", pad 6 "entry", pad 34 "entryNotExit"
    , pad 26 "callNotExit", pad 32 "inline entries", pad 30 "inline exits"
    , "offending call pcs", "children w/o exit edge" ]

/-- The full static table, or an explicit decode failure. Renders as a fixed-width text table inside
a fenced block; the counts underneath it are the ones pinned by `native_decide` below. -/
def report : String :=
  match controlFlow? with
  | none => "control-flow decode FAILED — no rows (this is a gap, not a pass)\n"
  | some nodes =>
    let rows := boundaryRows nodes generatedProgram
    let count (f : BoundaryRow → Verdict) (p : Verdict → Bool) : Nat :=
      (rows.filter fun r => p (f r)).size
    String.intercalate "\n"
      ([ "## 1. Static boundary satisfiability — " ++ toString rows.size ++ " function instances"
       , ""
       , "Decided from `generatedProgram` alone; no run is involved. A `FAIL` here means the named"
       , "structure field has no witness, so the corresponding trace step cannot be taken at all."
       , ""
       , "```"
       , header
       , String.ofList (List.replicate 210 '-') ] ++
       (rows.map BoundaryRow.render).toList ++
       [ "```"
       , ""
       , "totals (ok / violated / gap):"
       , "```"
       , "  entryNotExit    : " ++ toString (count (·.entryNotExit) Verdict.isOk) ++ " / "
           ++ toString (count (·.entryNotExit) Verdict.isViolated) ++ " / "
           ++ toString (count (·.entryNotExit) (fun v => !v.isOk && !v.isViolated))
       , "  callNotExit     : " ++ toString (count (·.callNotExit) Verdict.isOk) ++ " / "
           ++ toString (count (·.callNotExit) Verdict.isViolated) ++ " / "
           ++ toString (count (·.callNotExit) (fun v => !v.isOk && !v.isViolated))
       , "  inline entries  : " ++ toString (count (·.inlineEntryEdges) Verdict.isOk) ++ " / "
           ++ toString (count (·.inlineEntryEdges) Verdict.isViolated) ++ " / "
           ++ toString (count (·.inlineEntryEdges) (fun v => !v.isOk && !v.isViolated))
       , "  inline exits    : " ++ toString (count (·.inlineExitEdges) Verdict.isOk) ++ " / "
           ++ toString (count (·.inlineExitEdges) Verdict.isViolated) ++ " / "
           ++ toString (count (·.inlineExitEdges) (fun v => !v.isOk && !v.isViolated))
       , ""
       , "inline PAIRS (parent,child), not instances:"
       , "  pairs                        : " ++ toString (inlinePairs generatedProgram).size
       , "  unresolved child identities  : " ++ toString (unresolvedChildCount generatedProgram)
       , "  entry edge inhabited         : "
           ++ toString ((inlinePairs generatedProgram).filter
                (fun p => inlineEntryInhabited p.1 p.2)).size
       , "  exit  edge inhabited         : "
           ++ toString ((inlinePairs generatedProgram).filter
                (fun p => inlineExitInhabited p.1 p.2)).size
       , "  exit  edge inhabited IF the child's own edges counted (mutant, not a valid boundary): "
           ++ toString ((inlinePairs generatedProgram).filter
                (fun p => inlineExitInhabitedIfChildEdgesCounted p.1 p.2)).size
       , "```"
       , "" ])

/-! ## Kernel-checked findings

Stated as exact values rather than as `= true` goals. All three conditions are red; the point is to
pin *how* red, by address, so a future extractor change fails the build instead of re-colouring a
report a reader has to re-derive. -/

/-- The manifest and the program agree row for row, so the `routineTag`/`qualifiedName` columns of
the table above name the instance whose addresses the verdicts were computed from. Without this the
join is index arithmetic and the table could confidently mislabel every row. -/
theorem manifest_matches_program_rowwise :
    generatedManifest.size = generatedProgram.functionInstances.size ∧
      (generatedProgram.functionInstances.zipIdx.all fun (o, i) =>
        match generatedManifest[i]? with
        | some m => m.index == i && m.id == o.id && m.entryPc == o.entryPc && m.exitPcs == o.exitPcs
        | none => false) = true := by
  native_decide

/-! ### Condition 1 — 33 instances have an uninhabited `EnteredScopedTrace` -/

/-- **33 of 141 function instances declare their own entry pc an exit.** For each of these,
`EnteredScopedTrace.entryNotExit` is `¬ (entryPc ∈ exitPcs)` and is false, so the structure is
uninhabited and the instance's local obligation cannot be discharged — it is unprovable if its `pre`
is satisfiable and vacuous if it is not. Pinned by ADDRESS, not by index: an index shifts silently
when the extractor changes. -/
theorem entry_is_own_exit_pcs :
    entryIsOwnExitPcs generatedProgram =
      #[66288, 66624, 69564, 72132, 72132, 72232, 72232, 72332, 72332, 73620, 73620, 73688, 73688,
        74300, 74300, 74472, 74472, 74508, 74508, 74888, 74888, 75336, 75336, 76108, 76224, 76592,
        77500, 77672, 77672, 78560, 78868, 78868, 78868] := by
  native_decide

/-- The same fact as a count, alongside the population it is drawn from. `108 + 33 = 141`: the check
is exhibited passing on a majority of the artifact, so a `violated` verdict is a discrimination and
not a constant. -/
theorem entry_not_exit_counts :
    (generatedProgram.functionInstances.filter (fun o => !entryIsOwnExit o)).size = 108 ∧
      (generatedProgram.functionInstances.filter entryIsOwnExit).size = 33 ∧
      generatedProgram.functionInstances.size = 141 := by
  native_decide

/-! ### Condition 2 — 7 resolved call sites are declared exits of their own caller -/

/-- **7 resolved-call rows, spread over 4 calling instances, are declared exits of the caller**, at
these caller-entry / call-pc pairs. `generated_call_rows` in the proof graph pins the aggregate (180 rows, 173
satisfiable); this names the offenders so the seven can be read as tail-position calls rather than
taken on trust. -/
theorem call_sites_declared_exit :
    (controlFlow?.map fun nodes =>
      (generatedProgram.functionInstances.filterMap fun o =>
        match callSitesDeclaredExit nodes o with
        | [] => none
        | pcs => some (o.entryPc, pcs))).getD #[] =
      #[(66312, [66360]), (67084, [75508]), (67352, [73048, 73076, 73104, 73132]),
        (69564, [69584])] := by
  native_decide

/-- Both directions of the `callNotExit` column are witnessed on the real artifact: 4 instances violate
it and 15 satisfy it at a genuine call site. The remaining 122 make no resolved call at all and are
`gap`, never a pass — the distinction matters, because collapsing them into the passing column would
turn a 15-of-19 result into a 137-of-141 one. -/
theorem call_not_exit_counts :
    (controlFlow?.map fun nodes =>
      ((generatedProgram.functionInstances.filter fun o =>
          (callNotExitVerdict nodes o).isOk).size,
       (generatedProgram.functionInstances.filter fun o =>
          (callNotExitVerdict nodes o).isViolated).size,
       (generatedProgram.functionInstances.filter fun o =>
          !(callNotExitVerdict nodes o).isOk && !(callNotExitVerdict nodes o).isViolated).size)).getD
      (0, 0, 0) = (15, 4, 122) := by
  native_decide

/-! ### Condition 3 — `ScopedTrace.inlineStep` is dead code against this artifact -/

/-- **Every one of the 127 declared inline pairs fails the exit-edge condition, and 82 of them also
fail the entry-edge condition.** `InlineBoundary.validFor` requires each `ib.exits` member to be an
edge *of the parent* whose source is child-owned and whose target lands back in the parent; the
generator attributes an edge to its DEEPEST owner, so an edge leaving the child is attributed to the
child and never appears in the parent's array. `ib.exits` is therefore forced to `#[]`,
`InlineTransfer.exitEdgeMem` has no witness, and `ScopedTrace.inlineStep` cannot fire anywhere in
this program. -/
theorem inline_pair_edge_counts :
    (inlinePairs generatedProgram).size = 127 ∧
      unresolvedChildCount generatedProgram = 0 ∧
      ((inlinePairs generatedProgram).filter fun p => inlineEntryInhabited p.1 p.2).size = 45 ∧
      ((inlinePairs generatedProgram).filter fun p => inlineExitInhabited p.1 p.2).size = 0 := by
  native_decide

/-- **The exit-edge check is capable of returning `true`; the artifact is what makes it `false`.**
Counting the child's own edge array as a candidate — which is NOT a valid `InlineBoundary`, since
`validFor` demands membership in the parent's array — inhabits 56 of the 127 pairs. So the zero
above is a fact about the generator's edge attribution, and 71 pairs have no crossing-out edge
anywhere in the artifact (the child leaves by return or tail call, not by a fall-out edge), which no
re-attribution repairs. -/
theorem inline_exit_edge_repairable_pairs :
    ((inlinePairs generatedProgram).filter fun p =>
        inlineExitInhabitedIfChildEdgesCounted p.1 p.2).size = 56 ∧
      ((inlinePairs generatedProgram).filter fun p =>
        !inlineExitInhabitedIfChildEdgesCounted p.1 p.2).size = 71 := by
  native_decide

/-- A pair whose entry edge IS inhabited, named. Without a witness in the passing direction the
entry-edge column would be a check nobody has seen succeed; this is the concrete one, from the entry
instance `zesu_decode_raw` into its inlined `allocator` constructor. -/
theorem inline_entry_edge_witness :
    ((inlinePairs generatedProgram).filterMap fun p =>
        if inlineEntryInhabited p.1 p.2 then some (p.1.entryPc, p.2.entryPc) else none)[0]? =
      some (66224, 66288) := by
  native_decide

/-! ### The verdict columns are not constants

Each column is exhibited taking at least two distinct values over the 141 rows, so no column is a
check incapable of discriminating. The inline-exit column is the exception in the passing direction
and is covered instead by `inline_exit_edge_repairable_pairs` above. -/

theorem verdict_columns_discriminate :
    (controlFlow?.map fun nodes =>
      let rows := boundaryRows nodes generatedProgram
      ((rows.filter (fun r => r.entryNotExit.isOk)).size,
       (rows.filter (fun r => r.entryNotExit.isViolated)).size,
       (rows.filter (fun r => r.inlineEntryEdges.isOk)).size,
       (rows.filter (fun r => r.inlineEntryEdges.isViolated)).size,
       (rows.filter (fun r => r.inlineExitEdges.isOk)).size,
       (rows.filter (fun r => r.inlineExitEdges.isViolated)).size)).getD (0, 0, 0, 0, 0, 0) =
      (108, 33, 10, 55, 0, 65) := by
  native_decide

end BinaryFv.SSZ.Zesu.Validation.Boundary
