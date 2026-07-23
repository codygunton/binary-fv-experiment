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
*proved composition*: from each occurrence's **local trace** obligation, the acyclicity of the
call/inline graph, and the generated address geometry, `global_of_local` derives every occurrence's
**closed** obligation — the entry's included. So coverage plus the local obligations *entail* that
every live occurrence implements the correctness claim its identity names
(`sszProgramCorrectness_perInstance`), which is what the name promises.

The local obligation is a statement about a *run*, not about other propositions. It hands the proof
an admitted child-summary relation realizing its callees' contracts (`ChildSummariesAvailable`) and
asks for an `EnteredScopedTrace` confined to what the occurrence owns; `instanceObligation` occurs on
neither side of it, so the composition is neither circular nor a rearrangement of already-closed
facts. Its predecessor — `(all callee global obligations) → this global obligation` — was exactly
such a rearrangement and has been removed.
-/

/-- The environment is the canonical one: its loaded image is the pinned Zesu ELF image, and its
layout record is internally consistent. Pinning the image here is what stops a proof from choosing a
convenient environment that trivializes framing. -/
def IsCanonicalEnvironment (env : DecoderEnvironment) : Prop :=
  env.image = Artifact.programImage ∧ ValidEnvironment env

/-- Validated source provenance on every occurrence: the recorded content hash **equals the pinned
source manifest** entry for the occurrence's declaring file, and the declaration line is real
(`> 0`).

This is what preserves source pinning after moving the hash and line out of the stable `FunctionId`.
The hash clause is now an equality against `pinnedSourceManifest`, not merely non-emptiness — so a
recorded hash that does not match the pinned source (a wrong, stale, or placeholder hash), or an
occurrence attributed to a file not in the manifest, fails the obligation. `pinnedSourceHash` returns
`none` off-manifest, and `none = some _` is false, so off-manifest attribution is rejected. -/
def sourceProvenanceRecorded (program : Program) : Prop :=
  ∀ instance_ ∈ program.instances,
    pinnedSourceHash instance_.id.function.declaration.file
        = some instance_.declProvenance.sourceFileHash ∧
      instance_.declProvenance.declSpan.line > 0

/-- The program is the one generated from the canonical ELF: its entry is the `zesu_decode_raw`
occurrence, that entry is emitted (not inlined), every claimed region lies inside the canonical
loaded code, every occurrence carries validated source provenance, and the extraction left no
unresolved attribution.

The byte-exact instruction check is the extraction row's job; what this states is the coverage tie to
the canonical artifact, so a program that ranges outside the real code, or drops source provenance,
cannot pass. -/
def IsCanonicalGeneratedProgram (program : Program) : Prop :=
  program.entry.function = zesuDecodeRawFunctionId ∧
  program.entry.inlineStack = [] ∧
  (∀ instance_ ∈ program.instances, ∀ range ∈ instance_.regions,
    ∀ address, range.start ≤ address → address < range.stop →
      ∃ byte, Artifact.programImage.readByte? address = some byte) ∧
  sourceProvenanceRecorded program ∧
  program.defects = #[]

/-- The obligation a single generated occurrence owes: the correctness claim for the routine its
identity names, confined to where that occurrence executes. `catalogEntryFor` is a single-valued
lookup, so this is a genuine dispatch, not a choice. An occurrence with no catalog entry owes
`False`, which coverage forbids from ever arising. -/
def instanceObligation (p : ContractParams) (program : Program) (instance_ : FunctionInstance) :
    Prop :=
  match catalogEntryFor instance_.id.function with
  | some entry => routineObligation p instance_ (instanceReachedPcs program instance_) entry.tag
  | none => False

/-- Every live routine's contract has a satisfiable precondition under a valid environment. Stated
per catalog entry (per routine) rather than per occurrence, since satisfiability is a property of the
contract. -/
def catalogSatisfiability (p : ContractParams) : Prop :=
  ∀ entry ∈ catalog, entry.isLive = true → routineSatisfiable p entry.functionId entry.tag

/-! ## Local-to-global composition -/

/-- The occurrences this one's correctness depends on: its inline children and its resolved external
calls, taken from the program's instances. By construction a subset of `program.instances`, and it
never contains the occurrence itself unless the source genuinely self-calls (which acyclicity then
forbids). -/
def calleeInstances (program : Program) (instance_ : FunctionInstance) : Array FunctionInstance :=
  program.instances.filter fun other =>
    (instance_.children ++ instance_.externalCalls).any fun callee => decide (callee = other.id)

theorem calleeInstances_subset {program : Program} {instance_ callee : FunctionInstance}
    (h : callee ∈ calleeInstances program instance_) : callee ∈ program.instances :=
  (Array.mem_filter.mp h).1

/-! ### Child summaries

A local proof does not get to assume its callees' *propositions*; it gets to spend their *runs*. The
relation below is what a `ScopedTrace` splice consumes, and it is deliberately concrete: a witness
names the exact callee occurrence, the state it was entered in, the number of machine steps it
consumed, the generated exit it stopped on, the typed arguments it was called with, the typed outcome
its `meaning` prescribes, and its exit binding. Erasing that handoff to a bare state relation before
proving it is exactly how a composition can look sound and say nothing. -/

/-- The summary one cataloged occurrence supplies to whoever splices it: a confined entered run of
exactly `used` steps from its generated entry to one of its generated exits, at typed arguments whose
entry binding held and whose exit binding holds at the outcome its `meaning` prescribes. An
occurrence with no catalog entry supplies nothing (`False`), so no splice can invent one. -/
def instanceSummary (p : ContractParams) (program : Program) (callee : FunctionInstance)
    (fromStep used : Nat) (s s' : State) : Prop :=
  match catalogEntryFor callee.id.function with
  | some entry =>
      (routineContract p callee.id.function entry.tag).summary
        (instanceExecutionPcs program callee) (instanceExitPred callee) (instanceEntryWord callee)
        fromStep used s s'
  | none => False

/-- The child-summary relation admitted by *one* occurrence's local proof: only the occurrences it
actually depends on, each summarized as above. Keying it to the parent is what makes the composition
provable — an unrelated occurrence's run is not confined to this parent's extent and could not be
spliced into it. -/
def childSummaryOf (p : ContractParams) (program : Program) (instance_ : FunctionInstance)
    (child : InstanceId) (fromStep used : Nat) (s s' : State) : Prop :=
  ∃ callee ∈ calleeInstances program instance_,
    callee.id = child ∧ instanceSummary p program callee fromStep used s s'

/-- What a local proof is *given* about the occurrences below it: an admitted summary relation that
realizes each callee's own contract. Whenever a callee's entry binding holds at a state, the relation
must contain a run of that callee — within its step bound — ending in a state satisfying its exit
binding at the outcome its `meaning` prescribes.

This is the assume half of the assume/guarantee split, and it is stated in terms of the callees'
*contracts*, never their `ImplementsInstance` propositions: a local proof is handed behavior, not
closed theorems. -/
def ChildSummariesAvailable (p : ContractParams) (program : Program) (instance_ : FunctionInstance)
    (childSummary : InstanceId → Nat → Nat → State → State → Prop) : Prop :=
  ∀ callee ∈ calleeInstances program instance_, ∀ entry : CatalogEntry,
    catalogEntryFor callee.id.function = some entry →
      ∀ (args : (routineContract p callee.id.function entry.tag).Args) (fromStep : Nat) (s : State),
        (routineContract p callee.id.function entry.tag).contract.binding.entry args s →
          ∃ used s',
            used ≤ (routineContract p callee.id.function entry.tag).contract.binding.stepBound args ∧
              childSummary callee.id fromStep used s s' ∧
              (routineContract p callee.id.function entry.tag).contract.binding.exit args
                ((routineContract p callee.id.function entry.tag).contract.spec.meaning args) s s'

/-- **The local obligation.** Given *any* admitted summary relation that realizes its callees'
contracts, the occurrence implements its own contract — retiring its own steps only inside what it
owns and spending those summaries at its checked boundaries.

This replaces the previous `instanceLocalObligation`, which was
`(all callee global obligations) → this global obligation`: an implication between already-closed
`ImplementsInstance` propositions that rearranged global facts and never mentioned a trace. Here the
premise is behavioral (`ChildSummariesAvailable`), the conclusion is an `EnteredScopedTrace`
(`routineLocalObligation` → `LocallyImplementsInstance`), and `instanceObligation` occurs on neither
side.

Quantifying over the relation rather than fixing it to `childSummaryOf` is what keeps the obligation
genuinely local: the proof may use only what a callee's contract guarantees, never which occurrence
happens to sit below it in this program. -/
def instanceLocalTraceObligation (p : ContractParams) (program : Program)
    (instance_ : FunctionInstance) : Prop :=
  match catalogEntryFor instance_.id.function with
  | some entry =>
      ∀ childSummary : InstanceId → Nat → Nat → State → State → Prop,
        ChildSummariesAvailable p program instance_ childSummary →
          routineLocalObligation p instance_ (instanceOwnPcs program instance_) childSummary
            entry.tag
  | none => False

/-! ### The geometry the composition rests on

Three facts about the generated address sets. They are `Prop`s here so this module stays independent
of the generated program, and each is a decidable check on it — `Program.rangesSubsume` and
`Program.inRanges` are `Bool`s — so a mutated program fails a check rather than passing silently. -/

/-- The generated geometry a ranked composition needs.

* `ownedWithinExecution` — an occurrence owns a subset of where it executes, so its local run is a
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
  ownedWithinExecution : ∀ instance_ ∈ program.instances, ∀ pc,
    instanceOwnPcs program instance_ pc → instanceExecutionPcs program instance_ pc
  calleeWithinExecution : ∀ instance_ ∈ program.instances,
    ∀ callee ∈ calleeInstances program instance_, ∀ pc,
      instanceExecutionPcs program callee pc → instanceExecutionPcs program instance_ pc
  calleeExitContainment : ∀ instance_ ∈ program.instances,
    ∀ callee ∈ calleeInstances program instance_, ∀ pc,
      instanceExecutionPcs program callee pc →
        instanceExitPred instance_ pc → instanceExitPred callee pc

/-! ### Deciding the geometry

Each geometry clause is a `Bool` computation over the generated program's range arrays, together
with a bridge to the `Prop` the composition consumes. A mutated program — a dropped absorbed routine,
a callee whose extent escapes its caller's, a boundary pointing at the wrong occurrence — makes one
of these evaluate to `false`, so the premise fails a check rather than being quietly assumed. -/

/-- The ranges an occurrence's execution may occupy, as data: its own regions and its extent. This is
`instanceExecutionPcs` in range form, and `executionPcs_iff_ranges` is the tie. -/
def instanceExecutionRanges (program : Program) (instance_ : FunctionInstance) :
    Array BinaryFv.Binary.AddressRange :=
  instance_.regions ++ Program.extentRanges program instance_

theorem executionPcs_iff_ranges {program : Program} {instance_ : FunctionInstance} {pc : BitVec 64} :
    instanceExecutionPcs program instance_ pc ↔ RegionPcs (instanceExecutionRanges program instance_) pc := by
  simp [instanceExecutionPcs, InstanceExecutionPcs, instanceReachedPcs, instanceExecutionRanges,
    RegionPcs.append_iff]

/-- Every occurrence owns a subset of where it executes. -/
def ownedWithinExecutionB (program : Program) : Bool :=
  program.instances.all fun i =>
    Program.rangesSubsume (instanceExecutionRanges program i) (Program.ownedRanges program i)

/-- Every callee executes inside its caller's execution set. -/
def calleeWithinExecutionB (program : Program) : Bool :=
  program.instances.all fun i =>
    (calleeInstances program i).all fun c =>
      Program.rangesSubsume (instanceExecutionRanges program i) (instanceExecutionRanges program c)

/-- Every caller exit that lies inside a callee's execution set is itself a callee exit. -/
def calleeExitContainmentB (program : Program) : Bool :=
  program.instances.all fun i =>
    (calleeInstances program i).all fun c =>
      i.exitPcs.all fun pc =>
        !Program.inRanges (instanceExecutionRanges program c) pc || c.exitPcs.contains pc

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
    have hin : Program.inRanges (instanceExecutionRanges program c) pc.toNat = true :=
      RegionPcs.iff_inRanges.mp (executionPcs_iff_ranges.mp hpc)
    simp [hin] at hmem
    simpa [instanceExitPred, FunctionInstance.isExit] using hmem

/-- **A closed child supplies the summary its caller splices.** Given the callee's closed obligation
and typed arguments whose entry binding holds, the callee's own confined run *is* a `childSummaryOf`
witness for the caller — with the callee's exact consumed count, not an invented one.

This is the direction that makes the local obligation dischargeable: a later row proves each
occurrence locally, and this turns the occurrence below it into the summary the splice needed. -/
theorem childSummariesAvailable_of_closed {p : ContractParams} {program : Program}
    {instance_ : FunctionInstance}
    (closed : ∀ callee ∈ calleeInstances program instance_, instanceObligation p program callee) :
    ChildSummariesAvailable p program instance_ (childSummaryOf p program instance_) := by
  intro callee hcallee entry found args fromStep s hpre
  have hclosed := closed callee hcallee
  unfold instanceObligation at hclosed
  rw [found] at hclosed
  obtain ⟨used, s', hbound, htrace, hexit⟩ := hclosed args fromStep s hpre
  refine ⟨used, s', hbound, ⟨callee, hcallee, rfl, ?_⟩, hexit⟩
  unfold instanceSummary
  rw [found]
  exact ⟨args, hpre, hbound, htrace, hexit⟩

/-- **The spliced summaries genuinely compose.** Every child summary this occurrence admits is a run
inside its extent that cannot have stepped past one of its exits, so appending the parent's
continuation is an honest confined run of the summed length.

This is the program-specific obligation the generic boundary layer leaves open, discharged here from
the generated geometry alone — no local or closed correctness is used. -/
theorem summariesCompose_of_geometry {p : ContractParams} {program : Program}
    {instance_ : FunctionInstance} (geom : ProgramGeometry program)
    (hmem : instance_ ∈ program.instances) :
    SummariesCompose (instanceExecutionPcs program instance_) (instanceExitPred instance_)
      (childSummaryOf p program instance_) := by
  intro child fromStep used count s s' s'' hsummary hcont
  obtain ⟨callee, hcallee, _, hsum⟩ := hsummary
  unfold instanceSummary at hsum
  cases found : catalogEntryFor callee.id.function with
  | none => rw [found] at hsum; exact hsum.elim
  | some entry =>
      rw [found] at hsum
      obtain ⟨_, _, _, htrace, _⟩ := hsum
      exact FunctionTrace.append_within
        (geom.calleeWithinExecution instance_ hmem callee hcallee)
        (geom.calleeExitContainment instance_ hmem callee hcallee)
        htrace.trace hcont

/-- A rank witnessing that the call/inline graph is acyclic: every callee ranks strictly below its
caller. Its existence is what makes the local-to-global induction well-founded, and it is where a
genuine cycle in the extracted graph would make the obligation unsatisfiable rather than silently
accepted. -/
def CallGraphRanked (program : Program) (rank : FunctionInstance → Nat) : Prop :=
  ∀ instance_ ∈ program.instances, ∀ callee ∈ calleeInstances program instance_,
    rank callee < rank instance_

/-- The ranked-graph check in `Bool` form. -/
def callGraphRankedB (program : Program) (rank : FunctionInstance → Nat) : Bool :=
  program.instances.all fun i => (calleeInstances program i).all fun c => decide (rank c < rank i)

/-- **The decidable check discharges acyclicity.** The rank is generated data checked here, not a
witness chosen to make an induction close. -/
theorem callGraphRanked_of_check {program : Program} {rank : FunctionInstance → Nat}
    (h : callGraphRankedB program rank = true) : CallGraphRanked program rank := by
  intro i hi c hc
  exact of_decide_eq_true (forall_mem_of_all (forall_mem_of_all h i hi) c hc)


/-- **The local-to-global composition principle, proved.**

If the call/inline graph is acyclic (ranked), the generated geometry holds, and every occurrence
satisfies its **local trace** obligation, then every occurrence satisfies its **closed** obligation —
in particular the entry's.

Read the two ends: the premise is a family of `EnteredScopedTrace` proofs against admitted child
summaries; the conclusion is a family of `ImplementsInstance` propositions, each an
`EnteredFunctionTrace` confined to where that occurrence executes. The induction is on the generated
rank, so each occurrence's callees are closed before it is, and their closed runs are what
`summariesCompose_of_geometry` turns into the summaries its local proof spent. Nothing here
rearranges already-global facts. -/
theorem global_of_local {program : Program} {p : ContractParams} {rank : FunctionInstance → Nat}
    (ranked : CallGraphRanked program rank) (geom : ProgramGeometry program)
    (locals : ∀ instance_ ∈ program.instances, instanceLocalTraceObligation p program instance_) :
    ∀ instance_ ∈ program.instances, instanceObligation p program instance_ := by
  have key : ∀ n, ∀ inst, inst ∈ program.instances → rank inst = n →
      instanceObligation p program inst := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n IH =>
      intro inst hinst hrank
      have closed : ∀ callee ∈ calleeInstances program inst, instanceObligation p program callee := by
        intro callee hcallee
        have hmem : callee ∈ program.instances := calleeInstances_subset hcallee
        have hlt : rank callee < n := hrank ▸ ranked inst hinst callee hcallee
        exact IH (rank callee) hlt callee hmem rfl
      have hlocal := locals inst hinst
      unfold instanceLocalTraceObligation at hlocal
      unfold instanceObligation
      cases found : catalogEntryFor inst.id.function with
      | none => rw [found] at hlocal; exact hlocal.elim
      | some entry =>
          rw [found] at hlocal
          exact routineObligation_of_local (geom.ownedWithinExecution inst hinst)
            (summariesCompose_of_geometry geom hinst)
            (hlocal (childSummaryOf p program inst) (childSummariesAvailable_of_closed closed))
  intro inst hinst
  exact key (rank inst) inst hinst rfl

/-- The explicit local-to-global composition obligation, non-circular.

The entry is `zesu_decode_raw`; every callee edge resolves to an occurrence or to a routine the
extraction surfaced as excluded (which its caller absorbs); the call/inline graph is acyclic (some
rank witnesses it); the generated geometry holds; and **every occurrence satisfies its local trace
obligation**. Via `global_of_local` these yield every occurrence's closed obligation — the entry's
included — without the entry's obligation ever appearing among its own premises. It also carries
`catalogGroundsInSpec`, tying the entry contract to the public `SszSpec.decode`. -/
def LocalToGlobal (program : Program) (p : ContractParams) : Prop :=
  program.entry.function = zesuDecodeRawFunctionId ∧
  (∀ instance_ ∈ program.instances, ∀ callee ∈ (instance_.children ++ instance_.externalCalls),
      (∃ calleeInstance ∈ program.instances, calleeInstance.id = callee) ∨
        (∃ absorbed ∈ program.excluded, absorbed.id = callee)) ∧
  (∃ rank, CallGraphRanked program rank) ∧
  ProgramGeometry program ∧
  (∀ instance_ ∈ program.instances, instanceLocalTraceObligation p program instance_) ∧
  catalogGroundsInSpec

/--
The complete program-correctness obligation for a fixed set of contract parameters.

Its components are exactly the review's required pieces: validated canonical-ELF coverage and source
provenance; semantic correspondence; contract-precondition satisfiability; and the explicit
local-to-global composition (from which the per-instance dispatch is *derived* — see
`sszProgramCorrectness_perInstance` — rather than assumed). `IsCanonicalEnvironment` pins the
environment so none of these can be trivialized.

The container/`RawV4` result representations in `p` are not free: `canonicalContractParams` fixes
every one of them to the concrete ABI memory layout taken from the pinned artifact, so a proof can
neither choose a convenient representation nor leave it open. The per-instance obligations are
non-vacuous independently of that, because `ImplementsInstance` demands an actual entered trace that
reaches a generated exit with frame preservation. -/
def sszProgramCorrectness (program : Program) (p : ContractParams) : Prop :=
  IsCanonicalGeneratedProgram program ∧
  IsCanonicalEnvironment p.env ∧
  coverage program ∧
  catalogSemanticObligations ∧
  catalogSatisfiability p ∧
  LocalToGlobal program p

/-- The per-instance **global** obligation is a *consequence* of `sszProgramCorrectness`, derived
through `global_of_local` from the local obligations and acyclicity. This is what makes coverage
entail that every live occurrence implements its contract; it is stronger than assuming the
per-instance obligation as a conjunct, because here it is proved from the compositional pieces. -/
theorem sszProgramCorrectness_perInstance {program : Program} {p : ContractParams}
    (correct : sszProgramCorrectness program p) :
    ∀ instance_ ∈ program.instances, instanceObligation p program instance_ := by
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

/-- Coverage plus the composition entails that the specific occurrence at a cataloged identity
implements its routine's correctness claim. This is the lemma that makes "`sszProgramCorrectness`
means what its name says" a theorem rather than a comment. -/
theorem instance_implements_its_contract
    {program : Program} {p : ContractParams}
    (correct : sszProgramCorrectness program p)
    {instance_ : FunctionInstance} (mem : instance_ ∈ program.instances)
    {entry : CatalogEntry} (found : catalogEntryFor instance_.id.function = some entry) :
    routineObligation p instance_ (instanceReachedPcs program instance_) entry.tag := by
  have h := sszProgramCorrectness_perInstance correct instance_ mem
  unfold instanceObligation at h
  rw [found] at h
  exact h

end BinaryFv.SSZ.Zesu.Contracts
