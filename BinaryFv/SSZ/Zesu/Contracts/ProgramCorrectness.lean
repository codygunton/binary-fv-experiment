import BinaryFv.SSZ.Zesu.Contracts.Catalog
import BinaryFv.SSZ.Zesu.Contracts.CanonicalParams
import BinaryFv.SSZ.Zesu.Artifact.Symbols

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.RiscV

/-!
# Program correctness

The local-to-global obligation that ties the generated Elfling program, the handwritten contracts,
and the pinned specification into one statement the root theorem descends through.

`sszProgramCorrectness` is not a bag of unrelated propositions. Its load-bearing content is a
*proved composition*: from each function instance's **local trace** obligation, the acyclicity of the
call/inline graph, and the generated address geometry, `global_of_local` derives every function instance's
**closed** obligation — the entry's included. So coverage plus the local obligations *entail* that
every live function instance implements the correctness claim its identity names
(`sszProgramCorrectness_perFunctionInstance`), which is what the name promises.

The local obligation is a statement about a *run*, not about other propositions. It hands the proof
an admitted child-summary relation realizing its callees' contracts (`ChildSummariesAvailable`) and
asks for an `EnteredScopedTrace` confined to what the function instance owns; `functionInstanceObligation` occurs on
neither side of it, so the composition is neither circular nor a rearrangement of already-closed
facts. Its predecessor — `(all callee global obligations) → this global obligation` — was exactly
such a rearrangement and has been removed.
-/

/-- The environment is the canonical one: its loaded image is the pinned Zesu ELF image, and its
layout record is internally consistent. Pinning the image here is what stops a proof from choosing a
convenient environment that trivializes framing. -/
def IsCanonicalEnvironment (env : DecoderEnvironment) : Prop :=
  env.image = Artifact.programImage ∧ ValidEnvironment env

/-- Validated source provenance on every function instance: the recorded content hash **equals the pinned
source manifest** entry for the function instance's declaring file, and the declaration line is real
(`> 0`).

This is what preserves source pinning after moving the hash and line out of the stable `FunctionId`.
The hash clause is now an equality against `pinnedSourceManifest`, not merely non-emptiness — so a
recorded hash that does not match the pinned source (a wrong, stale, or placeholder hash), or an
function instance attributed to a file not in the manifest, fails the obligation. `pinnedSourceHash` returns
`none` off-manifest, and `none = some _` is false, so off-manifest attribution is rejected. -/
def sourceProvenanceRecorded (program : Program) : Prop :=
  ∀ functionInstance ∈ program.functionInstances,
    pinnedSourceHash functionInstance.id.function.declaration.file
        = some functionInstance.declProvenance.sourceFileHash ∧
      functionInstance.declProvenance.declSpan.line > 0

/-- The program is the one generated from the canonical ELF: its entry is the `zesu_decode_raw`
function instance, that entry is emitted (not inlined), every claimed region lies inside the canonical
loaded code, every function instance carries validated source provenance, and the extraction left no
unresolved attribution.

The byte-exact instruction check is the extraction row's job; what this states is the coverage tie to
the canonical artifact, so a program that ranges outside the real code, or drops source provenance,
cannot pass. -/
def IsCanonicalGeneratedProgram (program : Program) : Prop :=
  program.entry.function = zesuDecodeRawFunctionId ∧
  program.entry.inlineStack = [] ∧
  (∀ functionInstance ∈ program.functionInstances, ∀ range ∈ functionInstance.regions,
    ∀ address, range.start ≤ address → address < range.stop →
      ∃ byte, Artifact.programImage.readByte? address = some byte) ∧
  sourceProvenanceRecorded program ∧
  program.defects = #[]

/-- The obligation a single generated function instance owes: the correctness claim for the routine its
identity names, confined to where that function instance executes. `catalogEntryFor` is a single-valued
lookup, so this is a genuine dispatch, not a choice. A function instance with no catalog entry owes
`False`, which coverage forbids from ever arising. -/
def functionInstanceObligation (p : ContractParams) (program : Program) (functionInstance : FunctionInstance) :
    Prop :=
  match catalogEntryFor functionInstance.id.function with
  | some entry => routineObligation p functionInstance (functionInstanceReachedPcs program functionInstance) entry.tag
  | none => False

/-- Every live routine's contract has a satisfiable precondition under a valid environment. Stated
per catalog entry (per routine) rather than per function instance, since satisfiability is a property of the
contract. -/
def catalogSatisfiability (p : ContractParams) : Prop :=
  ∀ entry ∈ catalog, entry.isLive = true → routineSatisfiable p entry.functionId entry.tag

/-! ## Local-to-global composition -/

/-- The function instances this one's correctness depends on: its inline children and its resolved external
calls, taken from the program's instances. By construction a subset of `program.functionInstances`, and it
never contains the function instance itself unless the source genuinely self-calls (which acyclicity then
forbids). -/
def calleeFunctionInstances (program : Program) (functionInstance : FunctionInstance) : Array FunctionInstance :=
  program.functionInstances.filter fun other =>
    (functionInstance.children ++ functionInstance.externalCalls).any fun callee => decide (callee = other.id)

theorem calleeFunctionInstances_subset {program : Program} {functionInstance callee : FunctionInstance}
    (h : callee ∈ calleeFunctionInstances program functionInstance) : callee ∈ program.functionInstances :=
  (Array.mem_filter.mp h).1

/-! ### Child summaries

A local proof does not get to assume its callees' *propositions*; it gets to spend their *runs*. The
relation below is what a `ScopedTrace` splice consumes, and it is deliberately concrete: a witness
names the exact callee function instance, the state it was entered in, the number of machine steps it
consumed, the generated exit it stopped on, the typed arguments it was called with, the typed outcome
its `meaning` prescribes, and its exit binding. Erasing that handoff to a bare state relation before
proving it is exactly how a composition can look sound and say nothing. -/

/-- The summary one cataloged function instance supplies to whoever splices it: a confined entered run of
exactly `used` steps from its generated entry to one of its generated exits, at typed arguments whose
entry binding held and whose exit binding holds at the outcome its `meaning` prescribes. An
function instance with no catalog entry supplies nothing (`False`), so no splice can invent one. -/
def functionInstanceSummary (p : ContractParams) (program : Program) (callee : FunctionInstance)
    (fromStep used : Nat) (s s' : State) : Prop :=
  match catalogEntryFor callee.id.function with
  | some entry =>
      (routineContract p callee.id.function entry.tag).summary
        (functionInstanceExecutionPcs program callee) (functionInstanceExitPred callee) (functionInstanceEntryWord callee)
        fromStep used s s'
  | none => False

/-- The child-summary relation admitted by *one* function instance's local proof: only the function instances it
actually depends on, each summarized as above. Keying it to the parent is what makes the composition
provable — an unrelated function instance's run is not confined to this parent's extent and could not be
spliced into it. -/
def childSummaryOf (p : ContractParams) (program : Program) (functionInstance : FunctionInstance)
    (child : FunctionInstanceId) (fromStep used : Nat) (s s' : State) : Prop :=
  ∃ callee ∈ calleeFunctionInstances program functionInstance,
    callee.id = child ∧ functionInstanceSummary p program callee fromStep used s s'

/-- What a local proof is *given* about the function instances below it: an admitted summary relation that
realizes each callee's own contract. Whenever a callee's entry binding holds at a state, the relation
must contain a run of that callee — within its step bound — ending in a state satisfying its exit
binding at the outcome its `meaning` prescribes.

This is the assume half of the assume/guarantee split, and it is stated in terms of the callees'
*contracts*, never their `ImplementsFunctionInstance` propositions: a local proof is handed behavior, not
closed theorems. -/
def ChildSummariesAvailable (p : ContractParams) (program : Program) (functionInstance : FunctionInstance)
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop) : Prop :=
  ∀ callee ∈ calleeFunctionInstances program functionInstance, ∀ entry : CatalogEntry,
    catalogEntryFor callee.id.function = some entry →
      ∀ (args : (routineContract p callee.id.function entry.tag).Args) (fromStep : Nat) (s : State),
        (routineContract p callee.id.function entry.tag).contract.binding.entry args s →
          ∃ used s',
            used ≤ (routineContract p callee.id.function entry.tag).contract.binding.stepBound args ∧
              childSummary callee.id fromStep used s s' ∧
              (routineContract p callee.id.function entry.tag).contract.binding.exit args
                ((routineContract p callee.id.function entry.tag).contract.spec.meaning args) s s'

/-- **The local obligation.** Given *any* admitted summary relation that realizes its callees'
contracts, the function instance implements its own contract — retiring its own steps only inside what it
owns and spending those summaries at its checked boundaries.

This replaces the previous `functionInstanceLocalObligation`, which was
`(all callee global obligations) → this global obligation`: an implication between already-closed
`ImplementsFunctionInstance` propositions that rearranged global facts and never mentioned a trace. Here the
premise is behavioral (`ChildSummariesAvailable`), the conclusion is an `EnteredScopedTrace`
(`routineLocalObligation` → `LocallyImplementsFunctionInstance`), and `functionInstanceObligation` occurs on neither
side.

Quantifying over the relation rather than fixing it to `childSummaryOf` is what keeps the obligation
genuinely local: the proof may use only what a callee's contract guarantees, never which function instance
happens to sit below it in this program. -/
def functionInstanceLocalTraceObligation (p : ContractParams) (program : Program)
    (functionInstance : FunctionInstance) : Prop :=
  match catalogEntryFor functionInstance.id.function with
  | some entry =>
      ∀ childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop,
        ChildSummariesAvailable p program functionInstance childSummary →
          routineLocalObligation p functionInstance (functionInstanceOwnPcs program functionInstance) childSummary
            entry.tag
  | none => False

/-! ### The geometry the composition rests on

Three facts about the generated address sets. They are `Prop`s here so this module stays independent
of the generated program, and each is a decidable check on it — `Program.rangesSubsume` and
`Program.inRanges` are `Bool`s — so a mutated program fails a check rather than passing silently. -/

/-- The generated geometry a ranked composition needs.

* `ownedWithinExecution` — a function instance owns a subset of where it executes, so its local run is a
  run in its extent. Without it the local obligation could be about addresses the closed one excludes.
* `calleeWithinExecution` — a callee executes inside its caller's extent. This is what makes the
  callee's own confined run spliceable at all.
* `calleeExitContainment` — a caller's exit that lies inside a callee's extent is already an exit of
  that callee. This is the load-bearing one: without it a spliced callee could step straight through
  its caller's `ret` and the reconstruction would claim a confinement the run never had. It is
  vacuous where the two extents are disjoint (a separately emitted callee) and a real check where
  they nest (an inlined child, whose regions lie inside its parent's).
-/
structure ProgramGeometry (program : Program) : Prop where
  ownedWithinExecution : ∀ functionInstance ∈ program.functionInstances, ∀ pc,
    functionInstanceOwnPcs program functionInstance pc → functionInstanceExecutionPcs program functionInstance pc
  calleeWithinExecution : ∀ functionInstance ∈ program.functionInstances,
    ∀ callee ∈ calleeFunctionInstances program functionInstance, ∀ pc,
      functionInstanceExecutionPcs program callee pc → functionInstanceExecutionPcs program functionInstance pc
  calleeExitContainment : ∀ functionInstance ∈ program.functionInstances,
    ∀ callee ∈ calleeFunctionInstances program functionInstance, ∀ pc,
      functionInstanceExecutionPcs program callee pc →
        functionInstanceExitPred functionInstance pc → functionInstanceExitPred callee pc

/-! ### Deciding the geometry

Each geometry clause is a `Bool` computation over the generated program's range arrays, together
with a bridge to the `Prop` the composition consumes. A mutated program — a dropped absorbed routine,
a callee whose extent escapes its caller's, a boundary pointing at the wrong function instance — makes one
of these evaluate to `false`, so the premise fails a check rather than being quietly assumed. -/

/-- The ranges a function instance's execution may occupy, as data: its own regions and its extent. This is
`functionInstanceExecutionPcs` in range form, and `executionPcs_iff_ranges` is the tie. -/
def functionInstanceExecutionRanges (program : Program) (functionInstance : FunctionInstance) :
    Array BinaryFv.Binary.AddressRange :=
  functionInstance.regions ++ Program.extentRanges program functionInstance

theorem executionPcs_iff_ranges {program : Program} {functionInstance : FunctionInstance} {pc : BitVec 64} :
    functionInstanceExecutionPcs program functionInstance pc ↔ RegionPcs (functionInstanceExecutionRanges program functionInstance) pc := by
  simp [functionInstanceExecutionPcs, FunctionInstanceExecutionPcs, functionInstanceReachedPcs, functionInstanceExecutionRanges,
    RegionPcs.append_iff]

/-- Every function instance owns a subset of where it executes. -/
def ownedWithinExecutionB (program : Program) : Bool :=
  program.functionInstances.all fun i =>
    Program.rangesSubsume (functionInstanceExecutionRanges program i) (Program.ownedRanges program i)

/-- Every callee executes inside its caller's execution set. -/
def calleeWithinExecutionB (program : Program) : Bool :=
  program.functionInstances.all fun i =>
    (calleeFunctionInstances program i).all fun c =>
      Program.rangesSubsume (functionInstanceExecutionRanges program i) (functionInstanceExecutionRanges program c)

/-- Every caller exit that lies inside a callee's execution set is itself a callee exit. -/
def calleeExitContainmentB (program : Program) : Bool :=
  program.functionInstances.all fun i =>
    (calleeFunctionInstances program i).all fun c =>
      i.exitPcs.all fun pc =>
        !Program.inRanges (functionInstanceExecutionRanges program c) pc || c.exitPcs.contains pc

/-- All three geometry clauses at once. -/
def programGeometryB (program : Program) : Bool :=
  ownedWithinExecutionB program && calleeWithinExecutionB program && calleeExitContainmentB program

private theorem forall_mem_of_all {α : Type _} {xs : Array α} {f : α → Bool}
    (h : xs.all f = true) : ∀ x ∈ xs, f x = true := by
  intro x hx
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hx
  exact hget ▸ (Array.all_eq_true.mp h) i hi

/-- **The decidable check discharges the geometry.** This is what lets D1 establish
`ProgramGeometry generatedProgram` by evaluation on the generated data, with no assumption. -/
theorem programGeometry_of_check {program : Program} (h : programGeometryB program = true) :
    ProgramGeometry program := by
  obtain ⟨howned, hcallee, hexit⟩ : ownedWithinExecutionB program = true ∧
      calleeWithinExecutionB program = true ∧ calleeExitContainmentB program = true := by
    simpa [programGeometryB, Bool.and_eq_true, and_assoc] using h
  refine ⟨?_, ?_, ?_⟩
  · intro i hi pc hpc
    exact executionPcs_iff_ranges.mpr
      (RegionPcs.of_rangesSubsume (forall_mem_of_all howned i hi) hpc)
  · intro i hi c hc pc hpc
    exact executionPcs_iff_ranges.mpr
      (RegionPcs.of_rangesSubsume (forall_mem_of_all (forall_mem_of_all hcallee i hi) c hc)
        (executionPcs_iff_ranges.mp hpc))
  · intro i hi c hc pc hpc hexitPc
    have hrow := forall_mem_of_all (forall_mem_of_all hexit i hi) c hc
    have hmem := forall_mem_of_all hrow pc.toNat hexitPc
    have hin : Program.inRanges (functionInstanceExecutionRanges program c) pc.toNat = true :=
      RegionPcs.iff_inRanges.mp (executionPcs_iff_ranges.mp hpc)
    simp [hin] at hmem
    simpa [functionInstanceExitPred, FunctionInstance.isExit] using hmem

/-- **A closed child supplies the summary its caller splices.** Given the callee's closed obligation
and typed arguments whose entry binding holds, the callee's own confined run *is* a `childSummaryOf`
witness for the caller — with the callee's exact consumed count, not an invented one.

This is the direction that makes the local obligation dischargeable: a later row proves each
function instance locally, and this turns the function instance below it into the summary the splice needed. -/
theorem childSummariesAvailable_of_closed {p : ContractParams} {program : Program}
    {functionInstance : FunctionInstance}
    (closed : ∀ callee ∈ calleeFunctionInstances program functionInstance, functionInstanceObligation p program callee) :
    ChildSummariesAvailable p program functionInstance (childSummaryOf p program functionInstance) := by
  intro callee hcallee entry found args fromStep s hpre
  have hclosed := closed callee hcallee
  unfold functionInstanceObligation at hclosed
  rw [found] at hclosed
  obtain ⟨used, s', hbound, htrace, hexit⟩ := hclosed args fromStep s hpre
  refine ⟨used, s', hbound, ⟨callee, hcallee, rfl, ?_⟩, hexit⟩
  unfold functionInstanceSummary
  rw [found]
  exact ⟨args, hpre, hbound, htrace, hexit⟩

/-- **The spliced summaries genuinely compose.** Every child summary this function instance admits is a run
inside its extent that cannot have stepped past one of its exits, so appending the parent's
continuation is an honest confined run of the summed length.

This is the program-specific obligation the generic boundary layer leaves open, discharged here from
the generated geometry alone — no local or closed correctness is used. -/
theorem summariesCompose_of_geometry {p : ContractParams} {program : Program}
    {functionInstance : FunctionInstance} (geom : ProgramGeometry program)
    (hmem : functionInstance ∈ program.functionInstances) :
    SummariesCompose (functionInstanceExecutionPcs program functionInstance) (functionInstanceExitPred functionInstance)
      (childSummaryOf p program functionInstance) := by
  intro child fromStep used count s s' s'' hsummary hcont
  obtain ⟨callee, hcallee, _, hsum⟩ := hsummary
  unfold functionInstanceSummary at hsum
  cases found : catalogEntryFor callee.id.function with
  | none => rw [found] at hsum; exact hsum.elim
  | some entry =>
      rw [found] at hsum
      obtain ⟨_, _, _, htrace, _⟩ := hsum
      exact FunctionTrace.append_within
        (geom.calleeWithinExecution functionInstance hmem callee hcallee)
        (geom.calleeExitContainment functionInstance hmem callee hcallee)
        htrace.trace hcont

/-- A rank witnessing that the call/inline graph is acyclic: every callee ranks strictly below its
caller. Its existence is what makes the local-to-global induction well-founded, and it is where a
genuine cycle in the extracted graph would make the obligation unsatisfiable rather than silently
accepted. -/
def CallGraphRanked (program : Program) (rank : FunctionInstance → Nat) : Prop :=
  ∀ functionInstance ∈ program.functionInstances, ∀ callee ∈ calleeFunctionInstances program functionInstance,
    rank callee < rank functionInstance

/-- The ranked-graph check in `Bool` form. -/
def callGraphRankedB (program : Program) (rank : FunctionInstance → Nat) : Bool :=
  program.functionInstances.all fun i => (calleeFunctionInstances program i).all fun c => decide (rank c < rank i)

/-- **The decidable check discharges acyclicity.** The rank is generated data checked here, not a
witness chosen to make an induction close. -/
theorem callGraphRanked_of_check {program : Program} {rank : FunctionInstance → Nat}
    (h : callGraphRankedB program rank = true) : CallGraphRanked program rank := by
  intro i hi c hc
  exact of_decide_eq_true (forall_mem_of_all (forall_mem_of_all h i hi) c hc)


/-- **The local-to-global composition principle, proved.**

If the call/inline graph is acyclic (ranked), the generated geometry holds, and every function instance
satisfies its **local trace** obligation, then every function instance satisfies its **closed** obligation —
in particular the entry's.

Read the two ends: the premise is a family of `EnteredScopedTrace` proofs against admitted child
summaries; the conclusion is a family of `ImplementsFunctionInstance` propositions, each an
`EnteredFunctionTrace` confined to where that function instance executes. The induction is on the generated
rank, so each function instance's callees are closed before it is, and their closed runs are what
`summariesCompose_of_geometry` turns into the summaries its local proof spent. Nothing here
rearranges already-global facts. -/
theorem global_of_local {program : Program} {p : ContractParams} {rank : FunctionInstance → Nat}
    (ranked : CallGraphRanked program rank) (geom : ProgramGeometry program)
    (locals : ∀ functionInstance ∈ program.functionInstances, functionInstanceLocalTraceObligation p program functionInstance) :
    ∀ functionInstance ∈ program.functionInstances, functionInstanceObligation p program functionInstance := by
  have key : ∀ n, ∀ functionInstance, functionInstance ∈ program.functionInstances → rank functionInstance = n →
      functionInstanceObligation p program functionInstance := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n IH =>
      intro functionInstance hinst hrank
      have closed : ∀ callee ∈ calleeFunctionInstances program functionInstance, functionInstanceObligation p program callee := by
        intro callee hcallee
        have hmem : callee ∈ program.functionInstances := calleeFunctionInstances_subset hcallee
        have hlt : rank callee < n := hrank ▸ ranked functionInstance hinst callee hcallee
        exact IH (rank callee) hlt callee hmem rfl
      have hlocal := locals functionInstance hinst
      unfold functionInstanceLocalTraceObligation at hlocal
      unfold functionInstanceObligation
      cases found : catalogEntryFor functionInstance.id.function with
      | none => rw [found] at hlocal; exact hlocal.elim
      | some entry =>
          rw [found] at hlocal
          exact routineObligation_of_local (geom.ownedWithinExecution functionInstance hinst)
            (summariesCompose_of_geometry geom hinst)
            (hlocal (childSummaryOf p program functionInstance) (childSummariesAvailable_of_closed closed))
  intro functionInstance hinst
  exact key (rank functionInstance) functionInstance hinst rfl

/-- The explicit local-to-global composition obligation, non-circular.

The entry is `zesu_decode_raw`; every callee edge resolves to a function instance or to a routine the
extraction surfaced as excluded (which its caller absorbs); the call/inline graph is acyclic (some
rank witnesses it); the generated geometry holds; and **every function instance satisfies its local trace
obligation**. Via `global_of_local` these yield every function instance's closed obligation — the entry's
included — without the entry's obligation ever appearing among its own premises. It also carries
`catalogGroundsInSpec`, tying the entry contract to the public `SszSpec.decode`. -/
def LocalToGlobal (program : Program) (p : ContractParams) : Prop :=
  program.entry.function = zesuDecodeRawFunctionId ∧
  (∀ functionInstance ∈ program.functionInstances, ∀ callee ∈ (functionInstance.children ++ functionInstance.externalCalls),
      (∃ calleeFunctionInstance ∈ program.functionInstances, calleeFunctionInstance.id = callee) ∨
        (∃ absorbed ∈ program.excludedFunctionInstances, absorbed.id = callee)) ∧
  (∃ rank, CallGraphRanked program rank) ∧
  ProgramGeometry program ∧
  (∀ functionInstance ∈ program.functionInstances, functionInstanceLocalTraceObligation p program functionInstance) ∧
  catalogGroundsInSpec

/--
The complete program-correctness obligation for a fixed set of contract parameters.

Its components are exactly the review's required pieces: validated canonical-ELF coverage and source
provenance; semantic correspondence; contract-precondition satisfiability; and the explicit
local-to-global composition (from which the per-function-instance dispatch is *derived* — see
`sszProgramCorrectness_perFunctionInstance` — rather than assumed). `IsCanonicalEnvironment` pins the
environment so none of these can be trivialized.

The container/`RawV4` result representations in `p` are not free: `canonicalContractParams` fixes
every one of them to the concrete ABI memory layout taken from the pinned artifact, so a proof can
neither choose a convenient representation nor leave it open. The per-function-instance obligations are
non-vacuous independently of that, because `ImplementsFunctionInstance` demands an actual entered trace that
reaches a generated exit with frame preservation. -/
def sszProgramCorrectness (program : Program) (p : ContractParams) : Prop :=
  IsCanonicalGeneratedProgram program ∧
  IsCanonicalEnvironment p.env ∧
  coverage program ∧
  catalogSemanticObligations ∧
  catalogSatisfiability p ∧
  LocalToGlobal program p

/-- The per-function-instance **global** obligation is a *consequence* of `sszProgramCorrectness`, derived
through `global_of_local` from the local obligations and acyclicity. This is what makes coverage
entail that every live function instance implements its contract; it is stronger than assuming the
per-function-instance obligation as a conjunct, because here it is proved from the compositional pieces. -/
theorem sszProgramCorrectness_perFunctionInstance {program : Program} {p : ContractParams}
    (correct : sszProgramCorrectness program p) :
    ∀ functionInstance ∈ program.functionInstances, functionInstanceObligation p program functionInstance := by
  obtain ⟨_, _, _, _, _, ltg⟩ := correct
  obtain ⟨_, _, ⟨_, hranked⟩, hgeom, hlocals, _⟩ := ltg
  exact global_of_local hranked hgeom hlocals

/-- Everything the root theorem depends on: program correctness for the **one concrete**
`canonicalContractParams`, plus the two recorded binary/oracle divergences.

This no longer quantifies the parameters existentially: `canonicalContractParams` fixes every
address- and layout-bearing field to a validated pinned artifact (`CanonicalParams`), so a proof can
neither choose a convenient environment nor leave the parameters open. -/
def sszComplianceObligations (program : Program) : Prop :=
  sszProgramCorrectness program canonicalContractParams ∧ knownDivergences

/-- Coverage plus the composition entails that the specific function instance at a cataloged identity
implements its routine's correctness claim. This is the lemma that makes "`sszProgramCorrectness`
means what its name says" a theorem rather than a comment. -/
theorem function_instance_implements_its_contract
    {program : Program} {p : ContractParams}
    (correct : sszProgramCorrectness program p)
    {functionInstance : FunctionInstance} (mem : functionInstance ∈ program.functionInstances)
    {entry : CatalogEntry} (found : catalogEntryFor functionInstance.id.function = some entry) :
    routineObligation p functionInstance (functionInstanceReachedPcs program functionInstance) entry.tag := by
  have h := sszProgramCorrectness_perFunctionInstance correct functionInstance mem
  unfold functionInstanceObligation at h
  rw [found] at h
  exact h

end BinaryFv.SSZ.Zesu.Contracts
