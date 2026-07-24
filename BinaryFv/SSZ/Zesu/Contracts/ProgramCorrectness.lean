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
*proved composition*: from each function instance's **local** obligation (it implements its contract given
its callees do) and the acyclicity of the call/inline graph, `global_of_local` derives every
function instance's **global** obligation — the entry's included. So coverage plus the local obligations
*entail* that every live function instance implements the correctness claim its identity names
(`sszProgramCorrectness_perFunctionInstance`), which is what the name promises. Crucially, the entry's local
obligation never contains the entry's own global obligation among its premises, so the composition is
not circular.
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
identity names. `catalogEntryFor` is a single-valued lookup, so this is a genuine dispatch, not a
choice. A function instance with no catalog entry owes `False`, which coverage forbids from ever arising. -/
def functionInstanceObligation (p : ContractParams) (functionInstance : FunctionInstance) : Prop :=
  match catalogEntryFor functionInstance.id.function with
  | some entry => routineObligation p functionInstance entry.tag
  | none => False

/-- Every live routine's contract has a satisfiable precondition under a valid environment. Stated
per catalog entry (per routine) rather than per function instance, since satisfiability is a property of the
contract. -/
def catalogSatisfiability (p : ContractParams) : Prop :=
  ∀ entry ∈ catalog, entry.isLive = true → routineSatisfiable p entry.functionId entry.tag

/-! ## Local-to-global composition -/

/-- The function instances this one's correctness depends on: its inline children and its resolved external
calls, taken from the program's function instances. By construction a subset of `program.functionInstances`, and it
never contains the function instance itself unless the source genuinely self-calls (which acyclicity then
forbids). -/
def calleeFunctionInstances (program : Program) (functionInstance : FunctionInstance) : Array FunctionInstance :=
  program.functionInstances.filter fun other =>
    (functionInstance.children ++ functionInstance.externalCalls).any fun callee => decide (callee = other.id)

theorem calleeFunctionInstances_subset {program : Program} {functionInstance callee : FunctionInstance}
    (h : callee ∈ calleeFunctionInstances program functionInstance) : callee ∈ program.functionInstances :=
  (Array.mem_filter.mp h).1

/-- The **local** obligation: the function instance implements its contract *assuming each of its callees
does*. The premise ranges over `calleeFunctionInstances`, which never contains the function instance itself, so the
entry's local obligation never presumes the entry's own global obligation — this is the fix for the
prior circular statement. A leaf (no callees) reduces to its unconditional obligation. -/
def functionInstanceLocalObligation (p : ContractParams) (program : Program)
    (functionInstance : FunctionInstance) : Prop :=
  (∀ callee ∈ calleeFunctionInstances program functionInstance, functionInstanceObligation p callee) →
    functionInstanceObligation p functionInstance

/-- A rank witnessing that the call/inline graph is acyclic: every callee ranks strictly below its
caller. Its existence is what makes the local-to-global induction well-founded, and it is where a
genuine cycle in the extracted graph would make the obligation unsatisfiable rather than silently
accepted. -/
def CallGraphRanked (program : Program) (rank : FunctionInstance → Nat) : Prop :=
  ∀ functionInstance ∈ program.functionInstances, ∀ callee ∈ calleeFunctionInstances program functionInstance,
    rank callee < rank functionInstance

/-- **The local-to-global composition principle, proved.**

If the call graph is acyclic (ranked) and every function instance satisfies its local obligation, then every
function instance satisfies its global obligation — in particular the entry. This discharges the
composition: per-function correctness *given callees*, assembled along the acyclic graph by strong
induction on the rank, yields whole-program correctness. Because it is a theorem, the local-to-global
step cannot be circular or vacuous. -/
theorem global_of_local {program : Program} {p : ContractParams} {rank : FunctionInstance → Nat}
    (ranked : CallGraphRanked program rank)
    (locals : ∀ functionInstance ∈ program.functionInstances, functionInstanceLocalObligation p program functionInstance) :
    ∀ functionInstance ∈ program.functionInstances, functionInstanceObligation p functionInstance := by
  have key : ∀ n, ∀ functionInstance, functionInstance ∈ program.functionInstances → rank functionInstance = n → functionInstanceObligation p functionInstance := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n IH =>
      intro functionInstance hFunctionInstance hrank
      refine locals functionInstance hFunctionInstance ?_
      intro callee hcallee
      have hmem : callee ∈ program.functionInstances := calleeFunctionInstances_subset hcallee
      have hlt : rank callee < n := hrank ▸ ranked functionInstance hFunctionInstance callee hcallee
      exact IH (rank callee) hlt callee hmem rfl
  intro functionInstance hFunctionInstance
  exact key (rank functionInstance) functionInstance hFunctionInstance rfl

/-- The explicit local-to-global composition obligation, non-circular.

The entry is `zesu_decode_raw`; every callee edge resolves to a function instance; the call graph is
acyclic (some rank witnesses it); and **every function instance satisfies its local obligation**. Via
`global_of_local` these yield every function instance's global obligation — the entry's included — without
the entry's obligation ever appearing among its own premises. It also carries `catalogGroundsInSpec`,
tying the entry contract to the public `SszSpec.decode`. -/
def LocalToGlobal (program : Program) (p : ContractParams) : Prop :=
  program.entry.function = zesuDecodeRawFunctionId ∧
  (∀ functionInstance ∈ program.functionInstances, ∀ callee ∈ (functionInstance.children ++ functionInstance.externalCalls),
      ∃ calleeFunctionInstance ∈ program.functionInstances, calleeFunctionInstance.id = callee) ∧
  (∃ rank, CallGraphRanked program rank) ∧
  (∀ functionInstance ∈ program.functionInstances, functionInstanceLocalObligation p program functionInstance) ∧
  catalogGroundsInSpec

/--
The complete program-correctness obligation for a fixed set of contract parameters.

Its components are exactly the review's required pieces: validated canonical-ELF coverage and source
provenance; semantic correspondence; contract-precondition satisfiability; and the explicit
local-to-global composition (from which the per-function-instance dispatch is *derived* — see
`sszProgramCorrectness_perFunctionInstance` — rather than assumed). `IsCanonicalEnvironment` pins the
environment so none of these can be trivialized.

Note the container/`RawV4` result representations in `p` are still free parameters here; they are
pinned to concrete ABI memory layouts in the containers row. The per-function-instance obligations are
non-vacuous regardless, because `ImplementsFunctionInstance` demands an actual entered trace that reaches a
generated exit with frame preservation — a trivial representation weakens the success arm but cannot
make the obligation vacuous. -/
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
    ∀ functionInstance ∈ program.functionInstances, functionInstanceObligation p functionInstance := by
  obtain ⟨_, _, _, _, _, ltg⟩ := correct
  obtain ⟨_, _, ⟨_, hranked⟩, hlocals, _⟩ := ltg
  exact global_of_local hranked hlocals

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
    routineObligation p functionInstance entry.tag := by
  have h := sszProgramCorrectness_perFunctionInstance correct functionInstance mem
  unfold functionInstanceObligation at h
  rw [found] at h
  exact h

end BinaryFv.SSZ.Zesu.Contracts
