import BinaryFv.Zesu.Elflings.GeneratedValidationBridges
import BinaryFv.Zesu.Contracts.ContractComposition
import GeneratedProgram

/-!
# Discharging the generated-program obligations

The deterministic generator emitted `GeneratedProgram.lean` (untrusted, address-bearing). This module
proves the three program obligations against the canonical ELF:

* `coverage generatedProgram` — every live catalog source function has a function instance, every function instance is
  cataloged, the exclusions stay absent, dispatch is unique (function instance ids and catalog identities are
  duplicate-free, and every identity resolves), the required `readArray` widths are present, and the
  extraction is defect-free.
* `sourceProvenanceRecorded generatedProgram` — every function instance's recorded content hash equals the
  pinned-source manifest entry for its file, and its declaration line is real (`> 0`).
* `IsCanonicalGeneratedProgram generatedProgram` — the entry is the emitted `zesu_decode_raw`
  function instance, **every byte of every claimed region reads back from the canonical `Artifacts.programImage`**,
  provenance is recorded, and no attribution defect remains.

Each obligation is discharged by a `native_decide`d `Bool` over the concrete generated data (and, for
the byte clause, the canonical ELF image) plus an ordinary kernel bridge lemma; no `sorry`, no axiom.
The byte clause's bridge (`bytesReadableIn_elim`) is generic in the image, so instantiating it at
`Artifacts.programImage` never reduces the ELF parse inside the kernel — that cost stays in the
compiled `native_decide`. This is the genuine coverage tie: a program ranging outside the real code,
dropping provenance, or missing a source function cannot pass.
-/

namespace BinaryFv.Zesu.Elflings.Validation

open BinaryFv.Binary.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Elflings.Generated (generatedProgram)

/-! ## Coverage: both matching directions -/

/-- Every live catalog entry has a generated function instance with its identity. -/
def everySourceFunctionHasFunctionInstanceB : Bool :=
  catalog.all fun e =>
    !e.isLive || generatedProgram.functionInstances.any fun i => decide (i.id.function = e.functionId)

theorem everySourceFunctionHasFunctionInstanceB_true : everySourceFunctionHasFunctionInstanceB = true := by native_decide

theorem everySourceFunctionHasFunctionInstance_holds : everySourceFunctionHasFunctionInstance generatedProgram := by
  intro e he hlive
  have hall := forall_mem_of_all everySourceFunctionHasFunctionInstanceB_true e he
  rw [hlive] at hall
  simp only [Bool.not_true, Bool.false_or] at hall
  obtain ⟨i, hi, hdec⟩ := exists_mem_of_any hall
  exact ⟨i, hi, of_decide_eq_true hdec⟩

/-- Every generated function instance carries a live catalog entry's identity. -/
def everyFunctionInstanceIsCatalogedB : Bool :=
  generatedProgram.functionInstances.all fun i =>
    catalog.any fun e => e.isLive && decide (i.id.function = e.functionId)

theorem everyFunctionInstanceIsCatalogedB_true : everyFunctionInstanceIsCatalogedB = true := by native_decide

theorem everyFunctionInstanceIsCataloged_holds : everyFunctionInstanceIsCataloged generatedProgram := by
  intro i hi
  have hany := forall_mem_of_all everyFunctionInstanceIsCatalogedB_true i hi
  obtain ⟨e, he, hb⟩ := exists_mem_of_any hany
  rw [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨e, he, hb.1, hb.2⟩

/-- No excluded function instance is matched by any generated function instance. -/
def excludedSourceFunctionsAbsentB : Bool :=
  generatedProgram.functionInstances.all fun i =>
    excludedSourceFunctions.all fun x => decide (i.id.function ≠ x.functionId)

theorem excludedSourceFunctionsAbsentB_true : excludedSourceFunctionsAbsentB = true := by native_decide

theorem excludedSourceFunctionsAbsent_holds : excludedSourceFunctionsAbsent generatedProgram := by
  intro i hi x hx
  have h1 := forall_mem_of_all excludedSourceFunctionsAbsentB_true i hi
  have h2 := forall_mem_of_all h1 x hx
  exact of_decide_eq_true h2

/-! ## Unique dispatch: distinctness of function instance ids and catalog identities -/

/-- The generated function instance identities are duplicate-free. -/
theorem functionInstanceIdsNodup_true :
    (decide ((generatedProgram.functionInstances.toList.map (·.id)).Nodup)) = true := by native_decide

theorem functionInstanceIdsDistinct_holds : generatedProgram.functionInstanceIdsDistinct := by
  intro i j hi hj heq
  exact array_key_index_inj generatedProgram.functionInstances (·.id)
    (nodup_of_decide functionInstanceIdsNodup_true) hi hj heq

/-- The catalog identities are duplicate-free. -/
theorem catalogIdsNodup_true :
    (decide ((catalog.toList.map (·.functionId)).Nodup)) = true := by native_decide

theorem catalogIdentitiesDistinct_holds : catalogIdentitiesDistinct := by
  intro i j hi hj heq
  exact array_key_index_inj catalog (·.functionId)
    (nodup_of_decide catalogIdsNodup_true) hi hj heq

/-- Every generated function instance identity resolves through the catalog dispatch. -/
def dispatchB : Bool :=
  generatedProgram.functionInstances.all fun i => (catalogEntryFor i.id.function).isSome

theorem dispatchB_true : dispatchB = true := by native_decide

theorem dispatch_holds :
    ∀ i ∈ generatedProgram.functionInstances, ∃ e, catalogEntryFor i.id.function = some e := by
  intro i hi
  exact Option.isSome_iff_exists.mp (forall_mem_of_all dispatchB_true i hi)

theorem functionInstancesDispatchUniquely_holds : functionInstancesDispatchUniquely generatedProgram :=
  ⟨functionInstanceIdsDistinct_holds, catalogIdentitiesDistinct_holds, dispatch_holds⟩

/-! ## Required specializations present -/

/-- Every required `readArray` width is a live catalog entry. -/
def readArrayWidthsPresentB : Bool :=
  requiredReadArrayWidths.all fun w =>
    catalog.any fun e =>
      decide (e.tag = ContractTag.readArray) && decide (readArrayWidthOf e.functionId = w)

theorem readArrayWidthsPresentB_true : readArrayWidthsPresentB = true := by native_decide

theorem readArrayWidthsPresent_holds : readArrayWidthsPresent := by
  intro w hw
  have h := forall_mem_of_all_list readArrayWidthsPresentB_true w hw
  obtain ⟨e, he, hb⟩ := exists_mem_of_any h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb
  exact ⟨e, he, hb.1, hb.2⟩

/-! ## The full coverage obligation -/

theorem coverage_holds : coverage generatedProgram :=
  ⟨everySourceFunctionHasFunctionInstance_holds, everyFunctionInstanceIsCataloged_holds, excludedSourceFunctionsAbsent_holds,
   functionInstancesDispatchUniquely_holds, catalogIdentitiesDistinct_holds, readArrayWidthsPresent_holds,
   rfl⟩

/-! ## Source provenance recorded -/

/-- Every function instance's recorded source-content hash **equals the pinned-source manifest** entry for
its declaring file, and its declaration line is real. This is the strengthened provenance check: the
generated hash must match the pinned source, not merely be non-empty. -/
def sourceProvenanceRecordedB : Bool :=
  generatedProgram.functionInstances.all fun i =>
    decide (pinnedSourceHash i.id.function.declaration.file = some i.declProvenance.sourceFileHash) &&
      decide (0 < i.declProvenance.declSpan.line)

theorem sourceProvenanceRecordedB_true : sourceProvenanceRecordedB = true := by native_decide

theorem sourceProvenanceRecorded_holds : sourceProvenanceRecorded generatedProgram := by
  intro i hi
  have h := forall_mem_of_all sourceProvenanceRecordedB_true i hi
  rw [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

/-! ## Canonical generated program: entry + byte readability against the canonical ELF -/

/-- Every byte of every claimed region reads back from the canonical `Artifacts.programImage`. This is
the `native_decide` that ties the generated ranges to the real code; the kernel-side bridge below is
generic in the image. -/
theorem allBytesReadable_true :
    bytesReadableIn Artifacts.programImage generatedProgram = true := by native_decide

theorem isCanonicalGeneratedProgram_holds : IsCanonicalGeneratedProgram generatedProgram := by
  refine ⟨by decide, rfl, ?_, sourceProvenanceRecorded_holds, rfl⟩
  intro functionInstance hFunctionInstance r hr address hlo hhi
  exact bytesReadableIn_elim allBytesReadable_true hFunctionInstance hr hlo hhi

end BinaryFv.Zesu.Elflings.Validation
