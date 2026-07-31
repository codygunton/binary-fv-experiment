import BinaryFv.Zesu.Elfling.GeneratedValidationBridges
import GeneratedProgram

/-!
# Nesting and disjointness over the whole generated program

Generalizes the M3 blob-schedule slice's `functionInstanceNestedIn` / `functionInstancesDisjoint` from three
function instances to all 141. Two structural correctness properties of the extracted inline forest:

* **Proper nesting.** Every function instance with a parent has all of its regions contained in a region of
  that parent (found by identity in the program). An optimizer may fragment a child, but every
  fragment lives inside the parent — exactly the containment the deepest-inline ownership rule needs.
* **Sibling disjointness.** Any two distinct function instances that share the same parent have pairwise
  disjoint regions, so no address is ambiguously owned by two siblings. Parent/child chains at the
  same PC (e.g. `readOffset`▷`readU32`) are *not* siblings and are correctly exempt.

Both are `native_decide`d `Bool`s over the concrete generated regions plus ordinary kernel bridges.
Together with the M3 attribution argument this is why the generator emits `defects = #[]` honestly.
-/

namespace BinaryFv.Zesu.Elfling.Validation

set_option maxRecDepth 8000

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.Zesu.Elfling.Generated (generatedProgram)

/-! ## Region containment / disjointness predicates -/

/-- `range` sits inside some region of `functionInstance`. -/
def rangeCoveredBy (functionInstance : FunctionInstance) (range : AddressRange) : Bool :=
  functionInstance.regions.any fun q => q.start ≤ range.start && range.stop ≤ q.stop

/-- Every region of `child` sits inside a region of `parent` (proper inline nesting). -/
def functionInstanceNestedIn (child parent : FunctionInstance) : Bool :=
  child.regions.all (rangeCoveredBy parent)

/-- Two function instances' regions are pairwise disjoint. -/
def functionInstancesDisjoint (a b : FunctionInstance) : Bool :=
  a.regions.all fun r => b.regions.all fun q => q.stop ≤ r.start || r.stop ≤ q.start

/-! ## Proper nesting: every child is contained in its parent -/

/-- For each function instance with a parent, the parent function instance exists (by identity) and contains it. -/
def allChildrenNestedB : Bool :=
  generatedProgram.functionInstances.all fun functionInstance =>
    match functionInstance.parent? with
    | none => true
    | some pid =>
      match generatedProgram.functionInstances.find? (fun q => q.id == pid) with
      | some parent => functionInstanceNestedIn functionInstance parent
      | none => false

theorem allChildrenNestedB_true : allChildrenNestedB = true := by native_decide

/-- Every function instance with a parent has that parent among the program's function instances, and every one of
its regions is contained in a region of the parent. -/
theorem generated_children_nested :
    ∀ functionInstance ∈ generatedProgram.functionInstances, ∀ pid, functionInstance.parent? = some pid →
      ∃ parent ∈ generatedProgram.functionInstances, parent.id = pid ∧
        functionInstanceNestedIn functionInstance parent = true := by
  intro functionInstance hFunctionInstance pid hpid
  have h := forall_mem_of_all allChildrenNestedB_true functionInstance hFunctionInstance
  simp only [hpid] at h
  cases hp : generatedProgram.functionInstances.find? (fun q => q.id == pid) with
  | none => simp only [hp] at h; exact absurd h (by decide)
  | some parent =>
    simp only [hp] at h
    have hpred := Array.find?_some hp
    exact ⟨parent, Array.mem_of_find?_eq_some hp, eq_of_beq hpred, h⟩

/-! ## Sibling disjointness -/

/-- Distinct function instances that share a parent have disjoint regions. -/
def allSiblingsDisjointB : Bool :=
  generatedProgram.functionInstances.all fun a =>
    generatedProgram.functionInstances.all fun b =>
      !(decide (a.id ≠ b.id) && (a.parent? == b.parent?) && a.parent?.isSome) ||
        functionInstancesDisjoint a b

theorem allSiblingsDisjointB_true : allSiblingsDisjointB = true := by native_decide

/-- Any two distinct function instances with the same (present) parent have pairwise disjoint regions: no
address is owned by two siblings. -/
theorem generated_siblings_disjoint :
    ∀ a ∈ generatedProgram.functionInstances, ∀ b ∈ generatedProgram.functionInstances,
      a.id ≠ b.id → a.parent? = b.parent? → a.parent?.isSome = true →
        functionInstancesDisjoint a b = true := by
  intro a ha b hb hne hpar hsome
  have h := forall_mem_of_all (forall_mem_of_all allSiblingsDisjointB_true a ha) b hb
  have hguard : (decide (a.id ≠ b.id) && (a.parent? == b.parent?) && a.parent?.isSome) = true := by
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨decide_eq_true hne, beq_iff_eq.mpr hpar⟩, hsome⟩
  rw [hguard, Bool.not_true, Bool.false_or] at h
  exact h

end BinaryFv.Zesu.Elfling.Validation
