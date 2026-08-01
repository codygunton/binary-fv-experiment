import BinaryFv.Zesu.Contracts.CanonicalProgram
import BinaryFv.Zesu.Contracts.CanonicalParams

namespace BinaryFv.Zesu.Contracts

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.RiscV

/-!
# Contract composition

The local-to-global argument that combines each generated function instance's contract with its
callees' contracts. Acyclicity makes this composition well-founded, so the exported entrypoint's
global obligation is derived rather than assumed.
-/

/-- The obligation a single generated occurrence owes: the correctness claim for the routine its
identity names. `catalogEntryFor` is a single-valued lookup, so this is a genuine dispatch, not a
choice. An occurrence with no catalog entry owes `False`, which coverage forbids from ever arising. -/
def instanceObligation (p : ContractParams) (instance_ : FunctionInstance) : Prop :=
  match catalogEntryFor instance_.id.function with
  | some entry => routineObligation p instance_ entry.tag
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

/-- The **local** obligation: the occurrence implements its contract *assuming each of its callees
does*. The premise ranges over `calleeInstances`, which never contains the occurrence itself, so the
entry's local obligation never presumes the entry's own global obligation — this is the fix for the
prior circular statement. A leaf (no callees) reduces to its unconditional obligation. -/
def instanceLocalObligation (p : ContractParams) (program : Program)
    (instance_ : FunctionInstance) : Prop :=
  (∀ callee ∈ calleeInstances program instance_, instanceObligation p callee) →
    instanceObligation p instance_

/-- A rank witnessing that the call/inline graph is acyclic: every callee ranks strictly below its
caller. Its existence is what makes the local-to-global induction well-founded, and it is where a
genuine cycle in the extracted graph would make the obligation unsatisfiable rather than silently
accepted. -/
def CallGraphRanked (program : Program) (rank : FunctionInstance → Nat) : Prop :=
  ∀ instance_ ∈ program.instances, ∀ callee ∈ calleeInstances program instance_,
    rank callee < rank instance_

/-- **The local-to-global composition principle, proved.**

If the call graph is acyclic (ranked) and every occurrence satisfies its local obligation, then every
occurrence satisfies its global obligation — in particular the entry. This discharges the
composition: per-function correctness *given callees*, assembled along the acyclic graph by strong
induction on the rank, yields whole-program correctness. Because it is a theorem, the local-to-global
step cannot be circular or vacuous. -/
theorem global_of_local {program : Program} {p : ContractParams} {rank : FunctionInstance → Nat}
    (ranked : CallGraphRanked program rank)
    (locals : ∀ instance_ ∈ program.instances, instanceLocalObligation p program instance_) :
    ∀ instance_ ∈ program.instances, instanceObligation p instance_ := by
  have key : ∀ n, ∀ inst, inst ∈ program.instances → rank inst = n → instanceObligation p inst := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n IH =>
      intro inst hinst hrank
      refine locals inst hinst ?_
      intro callee hcallee
      have hmem : callee ∈ program.instances := calleeInstances_subset hcallee
      have hlt : rank callee < n := hrank ▸ ranked inst hinst callee hcallee
      exact IH (rank callee) hlt callee hmem rfl
  intro inst hinst
  exact key (rank inst) inst hinst rfl

/-- The explicit local-to-global composition obligation, non-circular.

The entry is `zesu_decode_raw`; every callee edge resolves to an occurrence; the call graph is
acyclic (some rank witnesses it); and **every occurrence satisfies its local obligation**. Via
`global_of_local` these yield every occurrence's global obligation — the entry's included — without
the entry's obligation ever appearing among its own premises. It also carries `catalogGroundsInSpec`,
tying the entry contract to the public `BinaryFv.Specs.SSZ.decode`. -/
def LocalToGlobal (program : Program) (p : ContractParams) : Prop :=
  program.entry.function = zesuDecodeRawFunctionId ∧
  (∀ instance_ ∈ program.instances, ∀ callee ∈ (instance_.children ++ instance_.externalCalls),
      ∃ calleeInstance ∈ program.instances, calleeInstance.id = callee) ∧
  (∃ rank, CallGraphRanked program rank) ∧
  (∀ instance_ ∈ program.instances, instanceLocalObligation p program instance_) ∧
  catalogGroundsInSpec

/--
The complete program-correctness obligation for a fixed set of contract parameters.

Its components are exactly the review's required pieces: validated canonical-ELF coverage and source
provenance; semantic correspondence; contract-precondition satisfiability; and the explicit
local-to-global composition (from which the per-instance dispatch is *derived* — see
`sszProgramCorrectness_perInstance` — rather than assumed). `IsCanonicalEnvironment` pins the
environment so none of these can be trivialized.

Note the container/`RawV4` result representations in `p` are still free parameters here; they are
pinned to concrete ABI memory layouts in the containers row. The per-instance obligations are
non-vacuous regardless, because `ImplementsInstance` demands an actual entered trace that reaches a
generated exit with frame preservation — a trivial representation weakens the success arm but cannot
make the obligation vacuous. -/
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
    ∀ instance_ ∈ program.instances, instanceObligation p instance_ := by
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

/-- Coverage plus the composition entails that the specific occurrence at a cataloged identity
implements its routine's correctness claim. This is the lemma that makes "`sszProgramCorrectness`
means what its name says" a theorem rather than a comment. -/
theorem instance_implements_its_contract
    {program : Program} {p : ContractParams}
    (correct : sszProgramCorrectness program p)
    {instance_ : FunctionInstance} (mem : instance_ ∈ program.instances)
    {entry : CatalogEntry} (found : catalogEntryFor instance_.id.function = some entry) :
    routineObligation p instance_ entry.tag := by
  have h := sszProgramCorrectness_perInstance correct instance_ mem
  unfold instanceObligation at h
  rw [found] at h
  exact h

end BinaryFv.Zesu.Contracts

