import Lean
import BinaryFv.SSZ

/-!
# The theorem-dependency report, mechanically checked

The plan asks for a report showing "the one local seam and every proved non-local dependency", and
for that report to be drift-checked. A prose report would be stale within a day, so the report *is*
this file: the pins below are the report's content, and the `run_cmd` re-derives it from the
environment on every build and refuses to finish when the two disagree.

Two anchors, because the claim has two halves that no single anchor can carry:

* `BinaryFv.SSZ.root_compliance` — the public claim. What is reported about it is its **seam**: every
  declaration reachable from it whose own proof term contains `sorryAx`.
* `…ZesuDecodeRaw.sszComplianceObligations_of_residue` — the conditional theorem beneath it, which
  proves the whole compliance obligation from an explicit residue. What is reported about it is its
  seam (**empty**, and that is the claim) and the decomposition of the obligation it proves into
  named obligations, split into the residue it still assumes and the rest, which it proves.

## Why this is not a re-run of `AxiomHygiene`

`AxiomHygiene` scans the **whole environment** for `sorryAx` and pins the resulting site set. That is
strictly a statement about where `sorry` is *written*. It is blind to the question this file exists
to answer, which is what the root *rests on*: a `sorry` in a module nothing imports scores exactly the
same as one the root descends through, and — more sharply — **a restructure that keeps both `sorry`s
where they are but detaches them from the root would leave `AxiomHygiene` byte-identical.** The seam
here is computed over `root_compliance`'s cone, so that restructure is a diff.

The converse also holds, and is why both are kept: this file cannot see a `sorry` outside the two
anchors' cones, and `AxiomHygiene` can. Neither subsumes the other, in the same way its docstring
records for the textual `nix/proof.nix` grep.

`AxiomHygiene` also pins `rootDoors`, which happens to contain the two seam declarations today — but
it contains them as *doors*, conflated with four `native_decide` facts, because a door is "appeals to
a trust axiom **or** to `sorry`". That set answers "what does the root trust"; this one answers "what
is still unproved, and what has stopped being unproved". They are different questions and the second
is the one the plan bullet asks about.

## What the residue split means, and what makes it valid

`sszComplianceObligations_of_residue` has the shape `H₁ → … → Hₙ → sszComplianceObligations
generatedProgram`. Decompose the conclusion through `∧` — unfolding a definition only when doing so
exposes a conjunction — and you get the obligation's named components; decompose the hypotheses the
same way and you get the components it still assumes. Everything in the first set and not the second
is **proved** by that theorem, *provided the theorem is not itself a `sorry` in disguise* — which is
exactly what its pinned empty seam establishes. The two halves of this file interlock: the seam scan
is what licenses calling the complement "proved", and without it the split would be bookkeeping.

Hypothesis conjuncts are matched to conclusion conjuncts by name after normalisation: a hypothesis
whose head is not already a conclusion component is unfolded until it is. That is how
`LocalContractAssumptions` is recognised as the conclusion's
`∀ functionInstance ∈ …, functionInstanceLocalTraceObligation …` conjunct rather than counted as a
separate obligation. A hypothesis that cannot be resolved this way is a **failure**, not a silent
extra: it would mean the anchor takes a premise that is not part of what it proves, and then
"conclusion minus hypotheses" is not a valid reading of it.

## Assumed is not the same as unproved, and reporting them as one thing would be wrong

A conjunct being a hypothesis of the conditional theorem says only that *that theorem* does not
supply it. It may already be proved elsewhere and simply not threaded in yet:
`knownDivergences_holds` closes both recorded divergences outright, while
`sszComplianceObligations_of_residue` still takes `knownDivergences` as a premise. A report that
listed the divergences as outstanding alongside the local contracts would be describing a residue
three times larger than the real one — the difference between "three things left to do" and "one".

So each residue conjunct is pinned *with its witness*: the closed theorem that already discharges it,
or `none` when nothing does. The witness is not taken on trust — it must exist, take no hypothesis of
its own, conclude the conjunct it claims, and carry no `sorry` in its cone. What survives with `none`
is the genuinely outstanding work, and today that is exactly one conjunct: the per-function-instance
local trace obligation. That is the plan bullet's "one local seam", stated so that it is checked
rather than asserted.

## Granularity

The whole environment is too much and the root alone is too little, so the unit is the **named
conjunct of the compliance obligation** — discovered by unfolding, not listed by hand. Composite
components (`sszProgramCorrectness`, `catalogSemanticObligations`, `LocalToGlobal`, …) are recorded
alongside their leaves, because a component that unfolds straight into a conjunction of anonymous
equations would otherwise vanish from the report entirely: two of `catalogSemanticObligations`'
twenty conjuncts do exactly that. Conjuncts with no project-level name — bare equations, bounds, the
callee-resolution disjunction — are not named, but they are counted, and the count is pinned, so
deleting one still fails the build.

## Anti-vacuity

A report over an empty or wrong scan set must fail rather than pass, and none of the conditions below
is a threshold — an earlier guard in this project used a count floor and was replaced for exactly
that reason. Each is a direct test of a premise the report depends on:

* **Both anchors exist.** Otherwise the pins are anchored on nothing.
* **`sszComplianceObligations` is reachable from `root_compliance`.** The report claims to describe
  what the root rests on *through the compliance obligation*; if the root stops descending through
  it, the seam set is being computed over the wrong spine, and that is reported as a failure rather
  than as a pass.
* **The obligation decomposition actually unfolded** — `sszComplianceObligations` must appear as a
  composite node, never as a leaf. Mark it `irreducible`, change what `unfoldDefinition?` will do, or
  restructure the obligation into an opaque predicate, and the tree collapses to a single leaf; every
  "proved" entry would then be vacuous while the build stayed green. This is the condition that
  catches that.
* **The conditional theorem's conclusion is closed.** Point the anchor at a parametric lemma and the
  report would describe an arbitrary program rather than the pinned generated one.
* **Every hypothesis conjunct resolves to a conclusion conjunct** (see above).
* **The conditional theorem's seam is pinned empty**, which is both a pin and the premise that makes
  the proved/assumed split mean anything.
* **Every residue witness is checked rather than trusted** — hypothesis-free, concluding what it
  claims, and `sorry`-free. Without that, the "already discharged" column would be the easiest place
  in the whole report to make a false claim, because it is the one part a reader is most likely to
  take on the pin's word.

The success line prints counts against their scan sizes, for the reason `ImportHygiene` gives: "0
seam declarations out of 4000 reachable" can be checked by a reader, "0 seam" cannot. Only the pins
are pins — the cone sizes are evidence and are deliberately not pinned, since every unrelated edit
moves them.

## When this fails

It is *meant* to fail on a restructure. The seam today is the two live-run scaffolds in
`Entrypoints/ZesuDecodeRaw/Execution.lean`; the work in flight replaces them with a single assumed
local-contracts premise, and this pin will refuse that change until someone writes the new seam down.
That is the point: the seam is the one thing about this proof that must never move quietly. On drift
the failure prints the discovered set in pin-ready form, so an intended change costs one paste.

The three small environment helpers below are duplicated from `AxiomHygiene` rather than shared.
Three guards that can fail independently are worth more than three guards sharing a helper whose edit
retunes all of them at once.
-/

open Lean Meta Elab Command

namespace BinaryFv.SSZ.DependencyReport

/-! ## Reading the environment -/

/-- Strip compiler-generated components to the user-facing declaration owning a proof term. -/
def ownerOf (n : Name) : Name := Id.run do
  let mut m := n
  while m.isInternal do m := m.getPrefix
  return m

/-- The constants a declaration mentions, in its type and in its value. -/
def mentioned (ci : ConstantInfo) : Array Name :=
  match ci.value? with
  | some v => ci.type.getUsedConstants ++ v.getUsedConstants
  | none => ci.type.getUsedConstants

/-- Transitive reachability from a declaration, over types and values alike. -/
partial def visit (env : Environment) (seen : IO.Ref NameSet) (n : Name) : IO Unit := do
  if (← seen.get).contains n then return
  seen.modify (·.insert n)
  let some ci := env.find? n | return
  for d in mentioned ci do visit env seen d

/-- Everything `anchor`'s proof term reaches. -/
def coneOf (env : Environment) (anchor : Name) : IO NameSet := do
  let seen ← IO.mkRef (∅ : NameSet)
  visit env seen anchor
  seen.get

/-- The declarations in `cone` whose own proof term appeals to `sorry` — the seam, the places where
the proof stops being a proof. -/
def seamOf (env : Environment) (cone : NameSet) : List Name := Id.run do
  let mut seam : NameSet := ∅
  for n in cone.toList do
    if let some ci := env.find? n then
      if (mentioned ci).contains ``sorryAx then seam := seam.insert (ownerOf n)
  return seam.toList

/-! ## Decomposing the obligation

A conjunct is *named* when its head is a declaration of this project. That positive rule replaces a
blacklist of logical connectives: `Or`, `Eq` and `LE.le` are structure, `catalogSatisfiability` is an
obligation, and no list needs maintaining as either side grows. -/

/-- A declaration belonging to this project. -/
def isProjectName (n : Name) : Bool := n.getRoot == `BinaryFv

/-- The project-level obligation a conjunct is *about*: descend through `∀`/`∃` binders to the
innermost body and take its head.

`fuel` controls normalisation and is the whole difference between the two passes. At `0` the
outermost project name wins, which is what the conclusion pass wants: `catalogSatisfiability` should
be reported under that name, not under whatever it unfolds to. Above `0` the head is unfolded until
it lands in `known`, which is what the hypothesis pass wants: `LocalContractAssumptions` has to be
recognised as the conclusion conjunct it is definitionally equal to. -/
partial def obligationName? (known : NameSet) (fuel : Nat) (e : Expr) : MetaM (Option Name) := do
  match e.getAppFnArgs with
  | (``Exists, #[_, p]) => lambdaTelescope p fun _ b => obligationName? known fuel b
  | _ =>
    if e.isForall then forallTelescope e fun _ b => obligationName? known fuel b
    else match e.getAppFn.constName? with
      | none => return none
      | some c =>
        if !isProjectName c then return none
        else if known.contains c || fuel = 0 then return some c
        else match ← unfoldDefinition? e with
          | none => return some c
          | some e' =>
            match ← obligationName? known (fuel - 1) (← whnfCore e') with
            | some c' => return some c'
            | none => return some c

/-- The decomposition of one proposition: its leaf conjuncts (`named` records the ones carrying a
project-level name, `conjuncts` counts all of them) and the composite obligations passed through on
the way (`nodes`). -/
structure Tree where
  named : Array Name := #[]
  conjuncts : Nat := 0
  nodes : NameSet := ∅

/-- Every named obligation the decomposition touched, composite and leaf alike. Composites are
included deliberately: a component that unfolds straight into anonymous equations contributes no leaf
name, and dropping it would remove it from the report without removing it from the obligation. -/
def Tree.vocabulary (t : Tree) : NameSet := t.named.foldl (fun s n => s.insert n) t.nodes

/-- Split `e` on `∧`, unfolding a definition only when the unfolding *is* a conjunction. That rule is
what bounds the decomposition: `sszComplianceObligations` opens up, `catalogSatisfiability` (a `∀`)
does not, and no hand-maintained list of "the obligation definitions" is needed. -/
partial def decompose (known : NameSet) (nameFuel fuel : Nat) (acc : IO.Ref Tree) (e : Expr) :
    MetaM Unit := do
  let leaf : MetaM Unit := do
    let n? ← obligationName? known nameFuel e
    acc.modify fun t =>
      { t with conjuncts := t.conjuncts + 1
               named := match n? with | some c => t.named.push c | none => t.named }
  match e.getAppFnArgs with
  | (``And, #[a, b]) => decompose known nameFuel fuel acc a; decompose known nameFuel fuel acc b
  | _ =>
    if fuel = 0 then leaf else
    match e.getAppFn.constName? with
    | none => leaf
    | some c =>
      match ← unfoldDefinition? e with
      | none => leaf
      | some e' =>
        let e' ← whnfCore e'
        if e'.isAppOf ``And then
          acc.modify fun t => { t with nodes := t.nodes.insert c }
          decompose known nameFuel (fuel - 1) acc e'
        else leaf

def treeOf (known : NameSet) (nameFuel : Nat) (e : Expr) : MetaM Tree := do
  let acc ← IO.mkRef ({} : Tree)
  decompose known nameFuel 32 acc e
  acc.get

/-! ## Reporting -/

/-- The discovered set as a Lean list literal, so an intended change costs one paste. -/
def pinBlock (ns : List Name) : MessageData :=
  MessageData.joinSep (ns.map fun n => m!"   ``{n},") "\n"

/-- Does `witness` close `conjunct` outright — no hypothesis of its own, the conclusion it claims,
and no `sorry` anywhere under it? Returns the reason it does not, or `none` when it does.

The hypothesis-freeness test is the load-bearing one. A *conditional* witness would prove nothing
about whether the conjunct is outstanding, and accepting one would turn this classification into the
very thing it exists to prevent: a claim that a residue entry is already handled, backed by a
theorem that assumes it. -/
def witnessVerdict (env : Environment) (conjunct witness : Name) : MetaM (Option MessageData) := do
  let some ci := env.find? witness
    | return some m!"residue witness {witness} for {conjunct} does not exist"
  let seam := seamOf env (← coneOf env witness)
  unless seam.isEmpty do
    return some m!"residue witness {witness} for {conjunct} is not a proof: it reaches {seam}"
  forallTelescope ci.type fun binders body => do
    for b in binders do
      if ← isProp (← inferType b) then
        return some m!"residue witness {witness} for {conjunct} is conditional — it takes a \
          hypothesis, so it does not establish that the conjunct is already discharged"
    match ← obligationName? ((∅ : NameSet).insert conjunct) 8 body with
    | some c =>
      if c == conjunct then return none
      else return some m!"residue witness {witness} concludes {c}, not {conjunct}"
    | none => return some m!"residue witness {witness}'s conclusion carries no project-level name"

/-- Compare a pin against what was discovered, in both directions: a new entry means the proof grew a
dependency nobody wrote down, a missing one means the pin has gone stale and claims more than the
tree contains. -/
def diagnose (label : String) (expected actual : List Name) : Option MessageData :=
  let missing := expected.filter (fun e => !actual.contains e)
  let extra := actual.filter (fun a => !expected.contains a)
  if missing.isEmpty && extra.isEmpty then none
  else some m!"{label}\n  unexpected (present in the proof, absent from the pin): {extra}\n  \
    absent (the pin claims more than the tree contains): {missing}\n  \
    the discovered set, pin-ready:\n{pinBlock actual}"

/-! ## The anchors -/

/-- The public claim. -/
def rootAnchor : Name := ``BinaryFv.SSZ.root_compliance

/-- The conditional theorem beneath it: the whole compliance obligation from an explicit residue. -/
def conditionalAnchor : Name :=
  ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.sszComplianceObligations_of_residue

/-- The proposition the two anchors meet at. The root consumes it — produced, today, by the seam —
and the conditional theorem proves it. Its reachability from the root is the report's anti-vacuity
premise. -/
def obligationConstant : Name := ``BinaryFv.SSZ.Zesu.Contracts.sszComplianceObligations

/-! ## The pins — the report itself -/

/-- **The seam.** Every declaration reachable from `root_compliance` whose own proof term contains
`sorryAx`. Both are the live-run scaffolds in `Entrypoints/ZesuDecodeRaw/Execution.lean`: they assert
that a specification outcome has a corresponding live run of the machine.

Discovered, not asserted — the check walks the root's cone and compares. The restructure in flight
replaces these two with a single assumed local-contracts premise, and this pin is what makes that
land as a reviewed diff instead of a silent change in what the root rests on. -/
def rootSeam : List Name :=
  [``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.successful_trace_of_spec_accepts,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.rejected_trace_of_spec_rejects]

/-- **The conditional theorem carries no seam at all, and that is the claim.**

What it proves, it proves; what it does not prove it takes as a visible hypothesis. Pinning this as
`[]` is what licenses the split below — "conclusion minus hypotheses is proved" is only true of a
theorem with no `sorry` under it — and it means the day this layer picks up a `sorry`, directly or
through something it starts consuming, the build says so rather than the report quietly beginning to
overstate. -/
def conditionalSeam : List Name := []

/-- **The size of the obligation, counting the conjuncts that have no name.**

Bare equations, numeric bounds and the callee-resolution disjunction carry no project-level name, so
they cannot appear in the two lists below; without this they could be deleted from the obligation
with the report unchanged. An exact equality, not a floor. -/
def obligationConjuncts : Nat := 50

/-- **The residue: what the conditional theorem still assumes.**

Each entry carries the closed theorem that already discharges it, or `none` when nothing does — and
the difference is the whole point of the list.

**The list is now one entry long, and it has no witness.** The three recorded binary/oracle
divergences used to sit here as premises-with-witnesses, purely because the anchor had not been
re-threaded through `knownDivergences_holds`; it has been, so they moved into `provedNonLocal`. What
is left is the per-function-instance local trace obligation — the one local seam D5 is aiming at, and
the remaining row work by design.

Nothing else is here — in particular no oracle-agreement fact and no satisfiability obligation. Those
were premises once and are now discharged inside the anchor itself, which is why they appear in
`provedNonLocal` below instead.

**What this list is about, stated so it is not over-read.** It is the residue of the *obligation*
anchor — what `sszComplianceObligations generatedProgram` still rests on. It is not the residue of the
root: `root_compliance` also consumes a live **run** of the machine, and that half is `rootSeam`
above, which is still two `sorry`s. A reader who took "one assumed obligation, no witness" as "one
hole left in the proof" would be wrong by exactly those two. -/
def assumedResidue : List (Name × Option Name) :=
  [(``BinaryFv.SSZ.Zesu.Contracts.functionInstanceLocalTraceObligation, none)]

/-- **Every proved non-local dependency**: the named components of `sszComplianceObligations
generatedProgram` that `sszComplianceObligations_of_residue` discharges rather than assumes.

Grouped as the obligation itself is. A component moving from this list into `assumedResidue` is the
proof getting weaker, and the pair of pins fails the build in either direction. -/
def provedNonLocal : List Name :=
  -- the obligation and its composite layer
  [``BinaryFv.SSZ.Zesu.Contracts.sszComplianceObligations,
   ``BinaryFv.SSZ.Zesu.Contracts.sszProgramCorrectness,
   -- the canonical program and the canonical environment
   ``BinaryFv.SSZ.Zesu.Contracts.IsCanonicalGeneratedProgram,
   ``BinaryFv.SSZ.Zesu.Contracts.IsCanonicalEnvironment,
   ``BinaryFv.SSZ.Zesu.Contracts.ValidEnvironment,
   -- coverage of the generated program against the catalog
   ``BinaryFv.SSZ.Zesu.Contracts.coverage,
   ``BinaryFv.SSZ.Zesu.Contracts.coverage.extractionDefectFree,
   ``BinaryFv.SSZ.Zesu.Contracts.sourceProvenanceRecorded,
   ``BinaryFv.SSZ.Zesu.Contracts.everyRoutineHasFunctionInstance,
   ``BinaryFv.SSZ.Zesu.Contracts.everyFunctionInstanceIsCataloged,
   ``BinaryFv.SSZ.Zesu.Contracts.excludedRoutinesAbsent,
   ``BinaryFv.SSZ.Zesu.Contracts.functionInstancesDispatchUniquely,
   ``BinaryFv.SSZ.Zesu.Contracts.catalogIdentitiesDistinct,
   ``BinaryFv.SSZ.Zesu.Contracts.readArrayWidthsPresent,
   ``BinaryFv.Binary.Elfling.Program.functionInstanceIdsDistinct,
   -- the semantic obligations
   ``BinaryFv.SSZ.Zesu.Contracts.catalogSemanticObligations,
   ``BinaryFv.SSZ.Zesu.Contracts.sourceShapedDecodeAgreesWithOracle,
   ``BinaryFv.SSZ.Zesu.Contracts.catalogGroundsInSpec,
   ``BinaryFv.SSZ.Zesu.Contracts.retryTailNeverSchemaValid,
   ``BinaryFv.SSZ.Zesu.Contracts.v3ShapeExcludesCanonicalV4,
   ``BinaryFv.SSZ.Zesu.Contracts.sourceShapedContainersAgreeWithOracle,
   ``BinaryFv.SSZ.Zesu.Contracts.canonicalOffsetsCharacterization,
   ``BinaryFv.SSZ.Zesu.Contracts.zeroFirstOffsetAliasRejected,
   ``BinaryFv.SSZ.Zesu.Contracts.bytesAtSucceedsIffFits,
   ``BinaryFv.SSZ.Zesu.Contracts.readOffsetIsWidenedReadU32,
   ``BinaryFv.SSZ.Zesu.Contracts.leafReadsOnlyFailInvalid,
   ``BinaryFv.SSZ.Zesu.Contracts.collectionsNeverUnknownFork,
   ``BinaryFv.SSZ.Zesu.Contracts.emptyByteListListIsEmptyArray,
   ``BinaryFv.SSZ.Zesu.Contracts.onlyForkConfigRaisesUnknownFork,
   ``BinaryFv.SSZ.Zesu.Contracts.fixedContainersNeverAllocate,
   ``BinaryFv.SSZ.Zesu.Contracts.allocatorVtableEntriesAreConstant,
   ``BinaryFv.SSZ.Zesu.Contracts.outOfMemoryUnreachableBelowBound,
   ``BinaryFv.SSZ.Zesu.Contracts.meaningEmptyIsNone,
   ``BinaryFv.SSZ.Zesu.Contracts.meaningTwentyFourIsSome,
   ``BinaryFv.SSZ.Zesu.Contracts.meaningOtherLengthIsInvalid,
   ``BinaryFv.SSZ.Zesu.Contracts.meaningNeverForkOrMemory,
   -- the two recorded binary/oracle divergences, proved and now threaded in rather than assumed
   ``BinaryFv.SSZ.Zesu.Contracts.knownDivergences,
   ``BinaryFv.SSZ.Zesu.Contracts.forkErrorOrderingDiffers,
   ``BinaryFv.SSZ.Zesu.Contracts.ereRetryReachedAboveU32Gate,
   -- precondition satisfiability, discharged in `CatalogSatisfiability.lean`
   ``BinaryFv.SSZ.Zesu.Contracts.catalogSatisfiability,
   -- the local-to-global composition, minus its local premise
   ``BinaryFv.SSZ.Zesu.Contracts.LocalToGlobal,
   ``BinaryFv.SSZ.Zesu.Contracts.CallGraphRanked,
   ``BinaryFv.SSZ.Zesu.Contracts.ProgramGeometry]

run_cmd liftTermElabM do
  let env ← getEnv
  for a in [rootAnchor, conditionalAnchor] do
    if (env.find? a).isNone then
      throwError m!"dependency report: anchor {a} does not exist; the pins are anchored on nothing"

  let mut failures : Array MessageData := #[]

  -- The seam, over each anchor's own cone.
  let rootCone ← coneOf env rootAnchor
  let condCone ← coneOf env conditionalAnchor
  let rootSeamNow := seamOf env rootCone
  let condSeamNow := seamOf env condCone
  if let some msg := diagnose s!"seam reachable from {rootAnchor}" rootSeam rootSeamNow then
    failures := failures.push msg
  if let some msg := diagnose s!"seam reachable from {conditionalAnchor}" conditionalSeam
      condSeamNow then
    failures := failures.push msg
  unless rootCone.contains obligationConstant do
    failures := failures.push m!"{obligationConstant} is not reachable from {rootAnchor}, so the \
      seam is being computed over a spine that no longer carries the compliance obligation — \
      reported as a failure rather than as a pass"

  -- The obligation, decomposed, and split into what the conditional theorem assumes and proves.
  let some ci := env.find? conditionalAnchor | throwError "unreachable: anchor checked above"
  let (closed, tree, assumedNow) ← forallTelescope ci.type fun binders body => do
    let tree ← treeOf ∅ 0 body
    let vocab := tree.vocabulary
    let mut assumed : NameSet := ∅
    for b in binders do
      let bty ← inferType b
      if ← isProp bty then
        for n in (← treeOf vocab 8 bty).vocabulary.toList do assumed := assumed.insert n
    return (!body.hasFVar, tree, assumed)

  let vocab := tree.vocabulary
  unless closed do
    failures := failures.push m!"{conditionalAnchor}'s conclusion is not closed: it is parametric \
      in one of its binders, so this report would describe an arbitrary program rather than the \
      pinned generated one"
  unless tree.nodes.contains obligationConstant do
    failures := failures.push m!"{obligationConstant} appears as a leaf rather than as a composite \
      node, so the obligation did not decompose and every 'proved' entry would be vacuous"
  let unresolved := assumedNow.toList.filter (fun n => !vocab.contains n)
  unless unresolved.isEmpty do
    failures := failures.push m!"{conditionalAnchor} takes premises that are not conjuncts of what \
      it proves, so 'conclusion minus hypotheses' is not a valid reading of it: {unresolved}"
  unless tree.conjuncts == obligationConjuncts do
    failures := failures.push m!"the obligation has {tree.conjuncts} conjuncts, pinned at \
      {obligationConjuncts}: a conjunct was added or removed"
  if let some msg := diagnose "residue still assumed by the conditional theorem"
      (assumedResidue.map Prod.fst) assumedNow.toList then
    failures := failures.push msg
  for (conjunct, witness?) in assumedResidue do
    if let some witness := witness? then
      if let some msg ← witnessVerdict env conjunct witness then
        failures := failures.push msg
  if let some msg := diagnose "proved non-local dependencies" provedNonLocal
      (vocab.toList.filter (fun n => !assumedNow.contains n)) then
    failures := failures.push msg

  unless failures.isEmpty do
    throwError m!"dependency report FAILED\n\n{MessageData.joinSep failures.toList "\n\n"}"
  let outstanding := (assumedResidue.filter (fun p => p.2.isNone)).map Prod.fst
  let witnessed := assumedResidue.length - outstanding.length
  let lines : List MessageData :=
    [m!"dependency report OK",
     m!"  seam of {rootAnchor}: {rootSeamNow.length} of {rootCone.size} reachable declarations"]
    ++ rootSeamNow.map (fun n => m!"    {n}")
    ++ [m!"  seam of {conditionalAnchor}: {condSeamNow.length} of {condCone.size} reachable",
        m!"  obligation: {tree.conjuncts} conjuncts naming {vocab.size} obligations — \
          {provedNonLocal.length} proved, {assumedResidue.length} assumed ({witnessed} of them \
          with a checked closed witness)",
        m!"  outstanding: {outstanding}"]
  logInfo (MessageData.joinSep lines "\n")

end BinaryFv.SSZ.DependencyReport
