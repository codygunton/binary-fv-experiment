import BinaryFv.SSZ.Zesu.Elfling.ManifestCheck

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

end BinaryFv.SSZ.Zesu.Elfling.Validation
