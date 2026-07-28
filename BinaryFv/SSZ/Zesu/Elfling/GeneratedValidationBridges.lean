import BinaryFv.Binary.Elfling.Elfling
import BinaryFv.Binary.ProgramImage

/-!
# Bool-check → Prop bridge lemmas for the generated-program validation

The row-1 obligations (`coverage`, `sourceProvenanceRecorded`, `IsCanonicalGeneratedElfling`) and the
extraction-row checks (byte readability, instruction decode, nesting, reachable partition) are ∀/∃
statements over `Array`/`List`, not auto-`Decidable` propositions. Following the reachability
certificate pattern, each is discharged by computing a `Bool` (validated by `native_decide` over the
real generated data / canonical ELF) and an *ordinary kernel* bridge lemma turning that `Bool = true`
into the `Prop`. Everything in this module is a plain kernel proof: no `native_decide`, no axiom, no
`sorry`. The bridges are deliberately generic (e.g. `image`-polymorphic) so that instantiating them at
`Artifact.programImage` never forces the kernel to reduce the expensive ELF parse — that cost stays
inside the compiled `native_decide` that establishes the `Bool` fact.
-/

namespace BinaryFv.SSZ.Zesu.Elfling.Validation

open BinaryFv.Binary
open BinaryFv.Binary.Elfling

/-! ## Generic membership bridges -/

/-- `arr.all p = true` gives `p x = true` for every member. -/
theorem forall_mem_of_all {α : Type} {arr : Array α} {p : α → Bool}
    (h : arr.all p = true) : ∀ x ∈ arr, p x = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
  exact Array.all_eq_true.mp h i hi

/-- `arr.any p = true` produces a member with `p x = true`. -/
theorem exists_mem_of_any {α : Type} {arr : Array α} {p : α → Bool}
    (h : arr.any p = true) : ∃ x ∈ arr, p x = true := by
  obtain ⟨i, hi, hp⟩ := Array.any_eq_true.mp h
  exact ⟨arr[i], Array.getElem_mem hi, hp⟩

/-- `l.all p = true` gives `p x = true` for every list member. -/
theorem forall_mem_of_all_list {α : Type} {l : List α} {p : α → Bool}
    (h : l.all p = true) : ∀ x ∈ l, p x = true :=
  fun _ hx => List.all_eq_true.mp h _ hx

/-! ## Index distinctness from a `Nodup` check -/

/-- A `decide`d `Nodup` fact, reified as the proposition. -/
theorem nodup_of_decide {α : Type} [DecidableEq α] {l : List α}
    (h : (decide l.Nodup) = true) : l.Nodup := of_decide_eq_true h

/-- If the list of a chosen key over an array is duplicate-free, indexing is injective on that key.
This is exactly the shape of the `functionInstanceIdsDistinct` / `catalogIdentitiesDistinct` obligations: two
array positions with equal key must be the same position. -/
theorem array_key_index_inj {α β : Type} [DecidableEq β] (arr : Array α) (key : α → β)
    (h : (arr.toList.map key).Nodup) {i j : Nat} (hi : i < arr.size) (hj : j < arr.size)
    (heq : key arr[i] = key arr[j]) : i = j := by
  have hlen : (arr.toList.map key).length = arr.size := by simp
  have hp := List.pairwise_iff_getElem.mp h
  have hi' : i < (arr.toList.map key).length := by rw [hlen]; exact hi
  have hj' : j < (arr.toList.map key).length := by rw [hlen]; exact hj
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd heq (by
      have hne := hp i j hi' hj' hij
      rwa [List.getElem_map, List.getElem_map, Array.getElem_toList, Array.getElem_toList] at hne)
  · exact hij
  · exact absurd heq.symm (by
      have hne := hp j i hj' hi' hij
      rwa [List.getElem_map, List.getElem_map, Array.getElem_toList, Array.getElem_toList] at hne)

/-! ## Byte readability, generic in the image -/

/-- Every byte of every claimed region reads back in `image`. `List.range r.size` walks the whole
half-open range, so a `true` here certifies readability of every address the region claims. -/
def bytesReadableIn (image : ProgramImage) (program : Elfling) : Bool :=
  program.functionInstances.all fun functionInstance =>
    functionInstance.regions.all fun r =>
      (List.range r.size).all fun k => (image.readByte? (r.start + k)).isSome

/-- The per-address readability the `IsCanonicalGeneratedElfling` byte clause demands, extracted from
the aggregate `Bool`. Generic in `image`: instantiating at `Artifact.programImage` leaves the read
symbolic, so the kernel never reduces the ELF parse. -/
theorem bytesReadableIn_elim {image : ProgramImage} {program : Elfling}
    (h : bytesReadableIn image program = true)
    {functionInstance : FunctionInstance} (hFunctionInstance : functionInstance ∈ program.functionInstances)
    {r : AddressRange} (hr : r ∈ functionInstance.regions)
    {address : Nat} (hlo : r.start ≤ address) (hhi : address < r.stop) :
    ∃ byte, image.readByte? address = some byte := by
  have hf := forall_mem_of_all h functionInstance hFunctionInstance
  have hg := forall_mem_of_all hf r hr
  have hk : address - r.start < r.size := by
    have : address < r.start + r.size := hhi
    omega
  have hmem : address - r.start ∈ List.range r.size := List.mem_range.mpr hk
  have hb := forall_mem_of_all_list hg (address - r.start) hmem
  have haddr : r.start + (address - r.start) = address := by omega
  rw [haddr] at hb
  exact Option.isSome_iff_exists.mp hb

end BinaryFv.SSZ.Zesu.Elfling.Validation
