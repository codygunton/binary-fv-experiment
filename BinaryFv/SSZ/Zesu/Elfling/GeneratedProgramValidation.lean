import BinaryFv.SSZ.Zesu.Elfling.GeneratedValidationBridges
import BinaryFv.SSZ.Zesu.Contracts.ProgramCorrectness
import GeneratedProgram

/-!
# Discharging the row-1 program obligations for the generated program

The deterministic generator emitted `GeneratedProgram.lean` (untrusted, address-bearing). This module
proves the three row-1 obligations for it against the canonical ELF:

* `coverage generatedProgram` — every live catalog routine has an occurrence, every occurrence is
  cataloged, the exclusions stay absent, dispatch is unique (instance ids and catalog identities are
  duplicate-free, and every identity resolves), the required `readArray` widths are present, and the
  extraction is defect-free.
* `sourceProvenanceRecorded generatedProgram` — every occurrence's recorded content hash equals the
  pinned-source manifest entry for its file, and its declaration line is real (`> 0`).
* `IsCanonicalGeneratedProgram generatedProgram` — the entry is the emitted `zesu_decode_raw`
  occurrence, **every byte of every claimed region reads back from the canonical `Artifact.programImage`**,
  provenance is recorded, and no attribution defect remains.

Each obligation is discharged by a `native_decide`d `Bool` over the concrete generated data (and, for
the byte clause, the canonical ELF image) plus an ordinary kernel bridge lemma; no `sorry`, no axiom.
The byte clause's bridge (`bytesReadableIn_elim`) is generic in the image, so instantiating it at
`Artifact.programImage` never reduces the ELF parse inside the kernel — that cost stays in the
compiled `native_decide`. This is the genuine coverage tie: a program ranging outside the real code,
dropping provenance, or missing a routine cannot pass.
-/

namespace BinaryFv.SSZ.Zesu.Elfling.Validation

open BinaryFv.Binary.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedProgram)

/-! ## Coverage: both matching directions -/

/-- Every live catalog entry has a generated occurrence with its identity. -/
def everyRoutineHasInstanceB : Bool :=
  catalog.all fun e =>
    !e.isLive || generatedProgram.instances.any fun i => decide (i.id.function = e.functionId)

theorem everyRoutineHasInstanceB_true : everyRoutineHasInstanceB = true := by native_decide

theorem everyRoutineHasInstance_holds : everyRoutineHasInstance generatedProgram := by
  intro e he hlive
  have hall := forall_mem_of_all everyRoutineHasInstanceB_true e he
  rw [hlive] at hall
  simp only [Bool.not_true, Bool.false_or] at hall
  obtain ⟨i, hi, hdec⟩ := exists_mem_of_any hall
  exact ⟨i, hi, of_decide_eq_true hdec⟩

/-- Every generated occurrence carries a live catalog entry's identity. -/
def everyInstanceIsCatalogedB : Bool :=
  generatedProgram.instances.all fun i =>
    catalog.any fun e => e.isLive && decide (i.id.function = e.functionId)

theorem everyInstanceIsCatalogedB_true : everyInstanceIsCatalogedB = true := by native_decide

theorem everyInstanceIsCataloged_holds : everyInstanceIsCataloged generatedProgram := by
  intro i hi
  have hany := forall_mem_of_all everyInstanceIsCatalogedB_true i hi
  obtain ⟨e, he, hb⟩ := exists_mem_of_any hany
  rw [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨e, he, hb.1, hb.2⟩

/-- No excluded routine is matched by any generated occurrence. -/
def excludedRoutinesAbsentB : Bool :=
  generatedProgram.instances.all fun i =>
    excludedRoutines.all fun x => decide (i.id.function ≠ x.functionId)

theorem excludedRoutinesAbsentB_true : excludedRoutinesAbsentB = true := by native_decide

theorem excludedRoutinesAbsent_holds : excludedRoutinesAbsent generatedProgram := by
  intro i hi x hx
  have h1 := forall_mem_of_all excludedRoutinesAbsentB_true i hi
  have h2 := forall_mem_of_all h1 x hx
  exact of_decide_eq_true h2

/-! ## Unique dispatch: distinctness of instance ids and catalog identities -/

/-- The generated occurrence identities are duplicate-free. -/
theorem instanceIdsNodup_true :
    (decide ((generatedProgram.instances.toList.map (·.id)).Nodup)) = true := by native_decide

theorem instanceIdsDistinct_holds : generatedProgram.instanceIdsDistinct := by
  intro i j hi hj heq
  exact array_key_index_inj generatedProgram.instances (·.id)
    (nodup_of_decide instanceIdsNodup_true) hi hj heq

/-- The catalog identities are duplicate-free. -/
theorem catalogIdsNodup_true :
    (decide ((catalog.toList.map (·.functionId)).Nodup)) = true := by native_decide

theorem catalogIdentitiesDistinct_holds : catalogIdentitiesDistinct := by
  intro i j hi hj heq
  exact array_key_index_inj catalog (·.functionId)
    (nodup_of_decide catalogIdsNodup_true) hi hj heq

/-- Every generated occurrence identity resolves through the catalog dispatch. -/
def dispatchB : Bool :=
  generatedProgram.instances.all fun i => (catalogEntryFor i.id.function).isSome

theorem dispatchB_true : dispatchB = true := by native_decide

theorem dispatch_holds :
    ∀ i ∈ generatedProgram.instances, ∃ e, catalogEntryFor i.id.function = some e := by
  intro i hi
  exact Option.isSome_iff_exists.mp (forall_mem_of_all dispatchB_true i hi)

theorem instancesDispatchUniquely_holds : instancesDispatchUniquely generatedProgram :=
  ⟨instanceIdsDistinct_holds, catalogIdentitiesDistinct_holds, dispatch_holds⟩

/-! ## Required specializations present -/

/-- Every required `readArray` width is a live catalog entry. -/
def readArrayWidthsPresentB : Bool :=
  requiredReadArrayWidths.all fun w =>
    catalog.any fun e =>
      decide (e.tag = RoutineTag.readArray) && decide (readArrayWidthOf e.functionId = w)

theorem readArrayWidthsPresentB_true : readArrayWidthsPresentB = true := by native_decide

theorem readArrayWidthsPresent_holds : readArrayWidthsPresent := by
  intro w hw
  have h := forall_mem_of_all_list readArrayWidthsPresentB_true w hw
  obtain ⟨e, he, hb⟩ := exists_mem_of_any h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb
  exact ⟨e, he, hb.1, hb.2⟩

/-! ## The full coverage obligation -/

theorem coverage_holds : coverage generatedProgram :=
  ⟨everyRoutineHasInstance_holds, everyInstanceIsCataloged_holds, excludedRoutinesAbsent_holds,
   instancesDispatchUniquely_holds, catalogIdentitiesDistinct_holds, readArrayWidthsPresent_holds,
   rfl⟩

/-! ## Source provenance recorded -/

/-- Every occurrence's recorded source-content hash **equals the pinned-source manifest** entry for
its declaring file, and its declaration line is real. This is the strengthened provenance check: the
generated hash must match the pinned source, not merely be non-empty. -/
def sourceProvenanceRecordedB : Bool :=
  generatedProgram.instances.all fun i =>
    decide (pinnedSourceHash i.id.function.declaration.file = some i.declProvenance.sourceFileHash) &&
      decide (0 < i.declProvenance.declSpan.line)

theorem sourceProvenanceRecordedB_true : sourceProvenanceRecordedB = true := by native_decide

theorem sourceProvenanceRecorded_holds : sourceProvenanceRecorded generatedProgram := by
  intro i hi
  have h := forall_mem_of_all sourceProvenanceRecordedB_true i hi
  rw [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

/-! ## Canonical generated program: entry + byte readability against the canonical ELF -/

/-- Every byte of every claimed region reads back from the canonical `Artifact.programImage`. This is
the `native_decide` that ties the generated ranges to the real code; the kernel-side bridge below is
generic in the image. -/
theorem allBytesReadable_true :
    bytesReadableIn Artifact.programImage generatedProgram = true := by native_decide

theorem isCanonicalGeneratedProgram_holds : IsCanonicalGeneratedProgram generatedProgram := by
  refine ⟨by decide, rfl, ?_, sourceProvenanceRecorded_holds, rfl⟩
  intro inst hinst r hr address hlo hhi
  exact bytesReadableIn_elim allBytesReadable_true hinst hr hlo hhi

end BinaryFv.SSZ.Zesu.Elfling.Validation
