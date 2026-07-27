import BinaryFv.SSZ.Zesu.Elfling.ManifestCheck
import BinaryFv.SSZ.Zesu.Elfling.GeneratedBoundaryInventory

/-!
# Mutation tests: removing a required function instance must break something

The manifest and boundary checks are `native_decide` facts about the *whole* generated array. That
shape is exactly the one this row keeps finding defects in: a predicate can be true of the real data
for reasons far weaker than its name suggests, and nothing in a passing `native_decide` distinguishes
"this check constrains the data" from "this check is satisfiable by almost anything".

So the checks are mutated here and the mutants are required to **fail**. Because a mutant that fails
is a *positive* statement (`… = false`), these live in the file as permanent regression guards rather
than as one-shot probes — unlike a must-fail probe, which can only be run once and reported.

## What the mutation found

The bullet this discharges reads "removing any required function instance from the manifest breaks a
check or proof". That is **true**, but not for the reason the shape of the checks suggests, and the
difference is worth pinning:

* `manifestIndexedB` rejects **every** removal, all 141 of them. Its first conjunct is
  `m.size == generatedProgram.functionInstances.size`, so truncation is caught by arithmetic before
  any row is examined.
* `manifestMatchesProgramB` — the check that actually compares each row's payload against its
  function instance — **does not** reject every removal. It walks `List.range m.size` comparing
  `m[k]` to `functionInstances[k]`, so deleting the **last** row leaves rows `0 … 139` still matching
  function instances `0 … 139`, and the predicate is `true` on the truncated manifest.

Neither fact is a defect: together the two checks reject every removal, which is what the bullet
claims. But the load for truncation is carried entirely by a size equality, and a reader who assumed
the payload comparison was what noticed a missing function instance would be wrong. `manifest_size`
and everything downstream of it depend on that conjunct rather than on the row-by-row match.

`manifest_payload_check_misses_last_removal` records the limitation as a theorem on purpose. If
someone later strengthens `manifestMatchesProgramB` so that it does catch truncation, that theorem
stops compiling and forces this note to be revisited, which a comment would not.

## The boundary inventory admits no such test, and that is a theorem here rather than an observation

The same mutation was attempted against `boundaryTransfersResolvedB` and **cannot work**. All three of
its conjuncts have the shape `nodes.all fun n => …`, with bodies depending only on the individual
node and on the global `ownedOrExcludedPC` — never on which nodes are *present*. So the predicate is
**monotone under removal**: deleting a node deletes conjuncts from three `.all`s and can only make it
easier to satisfy. `boundaryInventory_monotone_under_removal` proves exactly that, so "this check
cannot detect a missing node" is checked by the kernel instead of resting on a reading of three
definitions. An exhaustive sweep over all 3984 nodes would have spent ~40 minutes confirming what the
predicate's shape settles immediately.

Its name was therefore wider than its content, and it is now `boundaryTransfersResolvedB`: the old
name asserted something about the node *set*, while its body constrains each node individually.

**One refinement, found by reading `indirectSites` rather than trusting my own summary.** The
monotonicity result is about the *Bool predicate*. The recorded theorem `boundary_inventory_complete`
carries an extra conjunct, `(indirectSites nodes).size = 3`, and `indirectSites` is a `filter`, so that
conjunct is anti-monotone: removing any of those three nodes falsifies it. So the boundary side is not
uniformly blind to removal — it detects 3 of 3984 nodes and nothing else. "The check cannot detect a
missing node" is true of the predicate and too strong for the theorem. **That is not a soundness gap**, and the
reason is worth recording where the tempting fix would be applied. `controlFlow?` is
`decodedWords?.map controlFlowNodes` — the node array is *derived by decoding the pinned image*, not a
hand-maintained table. "A node went missing" is not a failure mode the artifact can exhibit; it would
require changing the image, which `binary_is_canonical` and `Artifact.programImage.matchesMemory`
pin. Set-completeness is inherited from image pinning, and this check's job is to constrain the nodes
that exist.

The contrast with the manifest is the whole point: `generatedManifest` *is* a generated table that can
lose a row, which is why the size conjunct above is load-bearing there and why the mutation test is
meaningful there and impossible here. One checklist item, two artifacts, only one of which can
exhibit the failure the item describes.
-/

namespace BinaryFv.SSZ.Zesu.Elfling.Validation

open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedManifest ManifestRow)

/-- The generated manifest with row `k` deleted. Mutation is by list surgery so the result is a
genuinely shorter array rather than a masked or zeroed row: a check that only inspects row contents
must still notice. -/
def manifestWithout (k : Nat) : Array ManifestRow :=
  (generatedManifest.toList.eraseIdx k).toArray

/-- **The mutation is real.** Deleting a row shortens the manifest — stated so that a future change
to `manifestWithout` (or to `List.eraseIdx`) that silently produced the original array would fail
here rather than turn every theorem below into a check of nothing. This is the in-source form of the
rule that a mutant must be diffed against its original before its failure means anything. -/
theorem manifestWithout_shrinks (k : Nat) (h : k < generatedManifest.size) :
    (manifestWithout k).size + 1 = generatedManifest.size := by
  have : (manifestWithout k).size = generatedManifest.size - 1 := by
    simp [manifestWithout, List.length_eraseIdx, h]
  omega

/-- **Removing any function instance breaks the index check.** All 141 removals, decided. -/
theorem manifest_removal_breaks_index_check :
    ((List.range generatedManifest.size).all fun k =>
      manifestIndexedB (manifestWithout k) == false) = true := by
  native_decide

/-- **But the payload check alone does not catch truncation.** Deleting the last row leaves every
surviving row still aligned with its own function instance, so this predicate is satisfied by a
manifest that is missing a function instance entirely.

Kept as a theorem rather than a comment so that strengthening `manifestMatchesProgramB` breaks the
build here and forces the module docstring to be corrected. -/
theorem manifest_payload_check_misses_last_removal :
    manifestMatchesProgramB (manifestWithout (generatedManifest.size - 1)) = true := by
  native_decide

/-- The complement, and the reason the pair is sufficient: every removal the payload check misses is
caught by the index check, because the two are conjoined at every use site. -/
theorem manifest_removal_breaks_some_check :
    ((List.range generatedManifest.size).all fun k =>
      (manifestIndexedB (manifestWithout k) && manifestMatchesProgramB (manifestWithout k))
        == false) = true := by
  native_decide

/-! ## Why the boundary inventory cannot be mutation-tested -/

/-- Removing an element from a list cannot falsify a `List.all`: the survivors are a sublist, so every
one of them already satisfied the predicate. -/
theorem list_all_eraseIdx {α : Type} (p : α → Bool) (l : List α) (k : Nat)
    (h : l.all p = true) : (l.eraseIdx k).all p = true := by
  rw [List.all_eq_true] at h ⊢
  intro x hx
  exact h x ((List.eraseIdx_sublist l k).mem hx)

/-- The same for arrays, in the form the mutation helpers produce. -/
theorem array_all_eraseIdx {α : Type} (p : α → Bool) (a : Array α) (k : Nat)
    (h : a.all p = true) : ((a.toList.eraseIdx k).toArray).all p = true := by
  have hl : a.toList.all p = true := by simpa using h
  simpa using list_all_eraseIdx p a.toList k hl

/-- **The boundary inventory check is monotone under node removal, hence incapable of detecting a
missing node.** Not a sampled observation and not a reading of three definitions — the three conjuncts
are per-node `.all`s, so removal only discards conjuncts.

This is the honest discharge of the boundary half of the "removing a required function instance breaks
a check" item: the requested mutation test is impossible against this predicate, and unnecessary,
because the node array is derived by decoding the pinned image rather than maintained by hand. See the
module docstring for why that is not a soundness gap. -/
theorem boundaryInventory_monotone_under_removal (nodes : Array BinaryFv.RiscV.ControlFlowNode)
    (k : Nat) (h : boundaryTransfersResolvedB nodes = true) :
    boundaryTransfersResolvedB ((nodes.toList.eraseIdx k).toArray) = true := by
  simp only [boundaryTransfersResolvedB, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨⟨array_all_eraseIdx _ nodes k h1, array_all_eraseIdx _ nodes k h2⟩,
    array_all_eraseIdx _ nodes k h3⟩

end BinaryFv.SSZ.Zesu.Elfling.Validation
