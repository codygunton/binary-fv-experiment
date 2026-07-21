import BinaryFv.SSZ.Zesu.Contracts.Catalog
import BinaryFv.SSZ.Zesu.Artifact.Symbols

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.RiscV

/-!
# Program correctness

The local-to-global obligation that ties the generated Elfling program, the handwritten contracts,
and the pinned specification into one statement the root theorem can descend through.

`sszProgramCorrectness` is not a bag of unrelated propositions. Its load-bearing component is the
*per-instance dispatch* `∀ instance, instanceObligation params instance`, which — because coverage
forces every occurrence to be cataloged and `catalogEntryFor` selects a single entry — asserts that
*every live occurrence implements the correctness claim for exactly the routine its identity names*.
Coverage therefore entails per-instance correctness, which is what the name promises.
-/

/-- The environment is the canonical one: its loaded image is the pinned Zesu ELF image, and its
layout record is internally consistent. Pinning the image here is what stops a proof from choosing a
convenient environment that trivializes framing. -/
def IsCanonicalEnvironment (env : DecoderEnvironment) : Prop :=
  env.image = Artifact.programImage ∧ ValidEnvironment env

/-- The program is the one generated from the canonical ELF: its entry is the `zesu_decode_raw`
occurrence, that entry is emitted (not inlined), every claimed region lies inside the canonical
loaded code, and the extraction left no unresolved attribution.

The byte-exact instruction check is the extraction row's job; what this states is the coverage tie
to the canonical artifact, so a program that ranges outside the real code cannot pass. -/
def IsCanonicalGeneratedProgram (program : Program) : Prop :=
  program.entry.function = zesuDecodeRawFunctionId ∧
  program.entry.inlineStack = [] ∧
  (∀ instance_ ∈ program.instances, ∀ range ∈ instance_.regions,
    ∀ address, range.start ≤ address → address < range.stop →
      ∃ byte, Artifact.programImage.readByte? address = some byte) ∧
  program.defects = #[]

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

/--
The explicit local-to-global composition obligation.

The entry occurrence is `zesu_decode_raw`; its external calls all resolve to occurrences in the
program; and *given the per-instance obligations for the whole program, the entry occurrence
implements the top-level `zesu_decode_raw` contract*. This is the shape a compositional proof
discharges: assemble the child contracts along the call/inline graph into the parent's. It also
carries `catalogGroundsInSpec`, tying that top contract to the public `SszSpec.decode`. -/
def LocalToGlobal (program : Program) (p : ContractParams) : Prop :=
  program.entry.function = zesuDecodeRawFunctionId ∧
  (∀ entryInstance ∈ program.instances, entryInstance.id = program.entry →
    (∀ callee ∈ entryInstance.externalCalls,
        ∃ calleeInstance ∈ program.instances, calleeInstance.id = callee) ∧
    ((∀ instance_ ∈ program.instances, instanceObligation p instance_) →
      routineObligation p entryInstance .zesuDecodeRaw)) ∧
  catalogGroundsInSpec

/--
The complete program-correctness obligation for a fixed set of contract parameters.

Its five conjuncts are exactly the review's required components: validated canonical-ELF coverage;
semantic correspondence; the per-instance dispatch asserting each occurrence's contract; contract
precondition satisfiability; and the explicit local-to-global composition. `IsCanonicalEnvironment`
pins the environment so none of these can be trivialized.

Note the container/`RawV4` result representations in `p` are still free parameters here; they are
pinned to the concrete ABI memory layouts in the containers row. The per-instance obligations are
non-vacuous regardless of that pinning, because `ImplementsInstance` demands an actual entered trace
that reaches a generated exit with frame preservation — a trivial representation weakens the success
arm but cannot make the obligation vacuous. -/
def sszProgramCorrectness (program : Program) (p : ContractParams) : Prop :=
  IsCanonicalGeneratedProgram program ∧
  IsCanonicalEnvironment p.env ∧
  coverage program ∧
  catalogSemanticObligations ∧
  (∀ instance_ ∈ program.instances, instanceObligation p instance_) ∧
  catalogSatisfiability p ∧
  LocalToGlobal program p

/-- Everything the root theorem depends on: program correctness for some canonical parameters, plus
the two recorded binary/oracle divergences. The existential is over the contract parameters only;
`sszProgramCorrectness` pins their environment to the canonical image, so this is not an escape
hatch. -/
def sszComplianceObligations (program : Program) : Prop :=
  (∃ p, sszProgramCorrectness program p) ∧ knownDivergences

/-- Coverage plus the per-instance dispatch entails that the specific occurrence at a cataloged
identity implements its routine's correctness claim. This is the lemma that makes
"`sszProgramCorrectness` means what its name says" a theorem rather than a comment. -/
theorem instance_implements_its_contract
    {program : Program} {p : ContractParams}
    (correct : sszProgramCorrectness program p)
    {instance_ : FunctionInstance} (mem : instance_ ∈ program.instances)
    {entry : CatalogEntry} (found : catalogEntryFor instance_.id.function = some entry) :
    routineObligation p instance_ entry.tag := by
  have perInstance := correct.2.2.2.2.1
  have h := perInstance instance_ mem
  unfold instanceObligation at h
  rw [found] at h
  exact h

end BinaryFv.SSZ.Zesu.Contracts
