import BinaryFv.SSZ.Zesu.Elfling.GeneratedProgramGeometry
import GeneratedManifest

/-!
# Checking the occurrence proof backlog

The generator emits the same 141 rows as Lean data and as the human-readable `MANIFEST.md`. This
module checks that the shared rows describe the actual generated program:

* **one row per occurrence, one occurrence per row, in index order** — a row deleted, duplicated,
  reordered, or pointed at a sibling occurrence fails `manifestIndexed`/`manifestMatchesProgram`;
* **each row's data is the occurrence's data** — identity, qualified name, kind, parent, children,
  external calls, absorbed excluded routines, entry pc and exit pcs, all compared against
  `generatedProgram`;
* **each row's routine tag is the catalog's** — `routineTag` is a string in the generated file (so
  the generator never imports the handwritten catalog), matched here against
  `catalogEntryFor`'s tag through `RoutineTag.name`, which is injective;
* **each row's dependency indices are the occurrence's dependencies** — so a row cannot understate
  what its proof may assume.

`localContractAssumptions_iff_manifest` then connects the quantified local-proof assumption to this
checked backlog, so the proof statement and work assignment cannot drift apart.
-/

namespace BinaryFv.SSZ.Zesu.Elfling.Validation

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedProgram generatedManifest ManifestRow)

/-! ## The manifest indexes the program exactly -/

/-- Exactly one row per occurrence, in occurrence-index order. -/
def manifestIndexedB (m : Array ManifestRow) : Bool :=
  (m.size == generatedProgram.instances.size) &&
    (List.range m.size).all fun k => m[k]!.index == k

theorem manifest_indexed_check : manifestIndexedB generatedManifest = true := by native_decide

theorem manifest_size : generatedManifest.size = generatedProgram.instances.size := by
  have h := manifest_indexed_check
  simp [manifestIndexedB, Bool.and_eq_true] at h
  exact h.1

theorem manifest_row_index (k : Nat) (h : k < generatedManifest.size) :
    generatedManifest[k].index = k := by
  have hall := manifest_indexed_check
  simp only [manifestIndexedB, Bool.and_eq_true] at hall
  have := List.all_eq_true.mp hall.2 k (List.mem_range.mpr h)
  simpa [getElem!_pos, h] using this

/-- Every row's payload is the occurrence's own data. Identity, name, kind, nesting, transfer
targets, entry and exits — a row that describes a sibling occurrence fails here. -/
def manifestMatchesProgramB (m : Array ManifestRow) : Bool :=
  (List.range m.size).all fun k =>
    let r := m[k]!
    let i := generatedProgram.instances[k]!
    decide (r.id = i.id) &&
      decide (r.qualifiedName = i.id.function.declaration.qualifiedName) &&
      decide (r.kind = (if i.parent?.isSome then "inlined" else "emitted")) &&
      decide (r.entryPc = i.entryPc) &&
      decide (r.exitPcs = i.exitPcs) &&
      decide (r.children.size = i.children.size) &&
      (r.children.all fun c =>
        c < generatedProgram.instances.size &&
          i.children.any fun cid => decide (cid = generatedProgram.instances[c]!.id)) &&
      (r.externalCalls.all fun c =>
        c < generatedProgram.instances.size &&
          i.externalCalls.any fun cid => decide (cid = generatedProgram.instances[c]!.id)) &&
      (r.absorbed.all fun x =>
        x < generatedProgram.excluded.size &&
          i.externalCalls.any fun cid => decide (cid = generatedProgram.excluded[x]!.id)) &&
      decide (r.dependencies.size = r.children.size + r.externalCalls.size) &&
      (r.dependencies.all fun d =>
        (r.children.any fun c => c == d) || (r.externalCalls.any fun c => c == d))

theorem manifest_matches_program_check : manifestMatchesProgramB generatedManifest = true := by
  native_decide

/-- Every row's routine tag is the tag the handwritten catalog dispatches its occurrence to. -/
def manifestTagsMatchCatalogB (m : Array ManifestRow) : Bool :=
  (List.range m.size).all fun k =>
    let r := m[k]!
    match catalogEntryFor generatedProgram.instances[k]!.id.function with
    | some entry => decide (r.routineTag = entry.tag.name)
    | none => false

theorem manifest_tags_match_catalog_check : manifestTagsMatchCatalogB generatedManifest = true := by
  native_decide

/-- Theorem names are distinct, so two occurrences cannot be discharged by one proof. -/
def manifestTheoremNamesDistinctB (m : Array ManifestRow) : Bool :=
  (List.range m.size).all fun i =>
    (List.range m.size).all fun j =>
      decide (m[i]!.theoremName ≠ m[j]!.theoremName) || decide (i = j)

theorem manifest_theorem_names_distinct :
    manifestTheoremNamesDistinctB generatedManifest = true := by native_decide

/-- Every row is assigned to one of the plan rows that owns local proofs, and every row still says
`pending` — no occurrence is recorded as proved before its proof exists. -/
def manifestRowsAssignedB (m : Array ManifestRow) : Bool :=
  m.all fun r =>
    (["E", "F", "G", "H", "I"].contains r.owningRow) && (r.proofStatus == "pending")

theorem manifest_rows_assigned : manifestRowsAssignedB generatedManifest = true := by native_decide

/-- The manifest has exactly 141 rows, matching the occurrence count. -/
theorem manifest_row_count : generatedManifest.size = 141 :=
  manifest_size.trans generated_occurrence_count


/-! ## Negative checks: every mutation of the manifest is caught

The manifest is only worth freezing if drift from it fails. Each mutation below is applied to the
real manifest and the corresponding check is shown to evaluate to `false`. Generation applies the
same integrity rules a second time — `manifest_rows` in the generator aborts on a missing,
duplicated, misordered or misattributed row — so a drifted manifest cannot even be emitted. -/

/-- One occurrence dropped from the backlog. -/
def manifestDeletedRow : Array ManifestRow := generatedManifest.eraseIdx! 7

theorem negative_manifest_deleted_row :
    manifestIndexedB manifestDeletedRow = false := by native_decide

/-- One row duplicated, displacing its successor. -/
def manifestDuplicatedRow : Array ManifestRow :=
  generatedManifest.set! 8 generatedManifest[7]!

theorem negative_manifest_duplicated_row :
    manifestIndexedB manifestDuplicatedRow = false := by native_decide

/-- Two rows transposed, so the backlog is no longer in occurrence order. -/
def manifestReorderedRows : Array ManifestRow :=
  (generatedManifest.set! 7 generatedManifest[8]!).set! 8 generatedManifest[7]!

theorem negative_manifest_reordered_rows :
    manifestIndexedB manifestReorderedRows = false := by native_decide

/-- One row's routine tag changed to another live tag. -/
def manifestWrongTag : Array ManifestRow :=
  generatedManifest.set! 7 { generatedManifest[7]! with routineTag := "readU256" }

theorem negative_manifest_wrong_tag :
    manifestTagsMatchCatalogB manifestWrongTag = false := by native_decide

/-- One row pointed at a sibling occurrence's identity and entry. -/
def manifestSiblingRow : Array ManifestRow :=
  generatedManifest.set! 7
    { generatedManifest[7]! with
      id := generatedManifest[9]!.id
      entryPc := generatedManifest[9]!.entryPc }

theorem negative_manifest_sibling_row :
    manifestMatchesProgramB manifestSiblingRow = false := by native_decide

/-- One row's dependency set altered to name an occurrence it does not depend on. -/
def manifestAlteredDependency : Array ManifestRow :=
  generatedManifest.set! 6 { generatedManifest[6]! with dependencies := #[0] }

theorem negative_manifest_altered_dependency :
    manifestMatchesProgramB manifestAlteredDependency = false := by native_decide

/-- One row marked proved before its proof exists. -/
def manifestPrematureStatus : Array ManifestRow :=
  generatedManifest.set! 7 { generatedManifest[7]! with proofStatus := "proved" }

theorem negative_manifest_premature_status :
    manifestRowsAssignedB manifestPrematureStatus = false := by native_decide

/-- Two occurrences sharing one theorem name. -/
def manifestSharedTheorem : Array ManifestRow :=
  generatedManifest.set! 7
    { generatedManifest[7]! with theoremName := generatedManifest[8]!.theoremName }

theorem negative_manifest_shared_theorem :
    manifestTheoremNamesDistinctB manifestSharedTheorem = false := by native_decide

/-! ## The frozen local assumption -/

/--
**The one local assumption Row D's root theorem is conditional on**: every generated occurrence
satisfies its local trace obligation, at the pinned contract parameters and the canonical program.

Nothing else is mixed in — no coverage, no runner, no spec equivalence, no heap bound, no observer
fact. Each of those is proved separately and unconditionally. Unfolded, each conjunct hands a proof
an admitted child-summary relation realizing that occurrence's callees' contracts and asks for an
`EnteredScopedTrace` confined to what the occurrence owns.
-/
def LocalContractAssumptions : Prop :=
  ∀ instance_ ∈ generatedProgram.instances,
    instanceLocalTraceObligation canonicalContractParams generatedProgram instance_

/--
**The assumption and the manifest are the same statement.** One direction says every manifest row's
occurrence is covered by the assumption; the other says the assumption follows from discharging the
manifest row by row. So the backlog cannot silently omit an occurrence the assumption needs, and the
assumption cannot silently need one the backlog does not list.
-/
theorem localContractAssumptions_iff_manifest :
    LocalContractAssumptions ↔
      ∀ k, ∀ h : k < generatedManifest.size,
        instanceLocalTraceObligation canonicalContractParams generatedProgram
          (generatedProgram.instances[k]'(manifest_size ▸ h)) := by
  constructor
  · intro hall k h
    exact hall _ (Array.mem_iff_getElem.mpr ⟨k, manifest_size ▸ h, rfl⟩)
  · intro hrows instance_ hinst
    obtain ⟨k, hk, hget⟩ := Array.mem_iff_getElem.mp hinst
    exact hget ▸ hrows k (manifest_size ▸ hk)

end BinaryFv.SSZ.Zesu.Elfling.Validation
