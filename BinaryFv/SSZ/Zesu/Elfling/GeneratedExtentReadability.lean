import BinaryFv.SSZ.Zesu.Elfling.GeneratedProgramValidation
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Layout
import BinaryFv.RiscV.Elfling.ProgramGeometry
import GeneratedProgram

/-!
# Readability across the whole execution extent, not just each function instance's own regions

`IsCanonicalGeneratedProgram`'s byte clause is discharged by `bytesReadableIn`, and that predicate
walks `functionInstance.regions` **only**. The address set a closed obligation actually runs against
is `functionInstanceExecutionPcs`, which is `functionInstance.regions` *together with*
`Program.extentRanges` — the transfer closure, pulling in every callee's `ownedRanges` (own regions
plus the *absorbed* excluded-routine ranges) and `rangesOf` for identities that name an excluded
routine rather than a function instance. Nothing checked readability there.

That gap is not cosmetic, and this module proves it is not: `programWithUnloadedExcluded` below is a
program on which `bytesReadableIn` is **`true`** and `executionExtentReadableIn` is **`false`** —
every absorbed routine sits above everything the image loads and the old check does not look.

## Why the sentinel bridge needs exactly this

`RiscV/Elfling/SentinelBridge.lean` takes `regionAvoidsSentinel` and `exitAvoidsSentinel` as
hypotheses and says outright that neither can be discharged generically: "the sentinel is chosen
outside every mapped range, and every region and exit address is inside one". The second half is a
target fact, and `Entrypoints/ZesuDecodeRaw/Layout.lean` already has the first
(`loaded_word_ne_sentinel`: a *loaded* address is not the sentinel, because every runner range sits
above `loadedCeiling`). What was missing is its premise for the pcs the bridge quantifies over. With
`generated_execution_pcs_readable` below, `loaded_word_ne_sentinel` reaches — and
`generated_execution_pcs_avoid_sentinel` / `generated_exit_pcs_avoid_sentinel` are the bridge's two
hypotheses, at the generated program.

## What these checks can and cannot detect

`executionExtentReadableIn` is `functionInstances.all (ranges.all (bytes.all …))`, so it is
**monotone under removal**: dropping an extent range, or a whole function instance, only discards
conjuncts. It therefore cannot detect a *missing* extent range, and nothing here claims the extent is
large enough — that is `Program.extentRanges`' own business (a fuel-bounded closure over the
generated `children`/`externalCalls`; the canonical machine-region database independently checks the
production CFG and unresolved indirect transfers. What this module detects is
a range in the extent that the pinned image cannot read back, which is exactly the failure the
mutation test below exhibits.
-/

namespace BinaryFv.SSZ.Zesu.Elfling.Validation

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedProgram)

/-! ## The check, generic in the image -/

/-- Every byte of every range reads back in `image`. `List.range r.size` walks the whole half-open
range, so a `true` certifies every address the range claims. -/
def rangesReadableIn (image : ProgramImage) (ranges : Array AddressRange) : Bool :=
  ranges.all fun r => (List.range r.size).all fun k => (image.readByte? (r.start + k)).isSome

/-- The per-address readability extracted from the aggregate `Bool`, generic in `image` so that
instantiating at `Artifact.programImage` never makes the kernel reduce the ELF parse. -/
theorem rangesReadableIn_elim {image : ProgramImage} {ranges : Array AddressRange}
    (h : rangesReadableIn image ranges = true)
    {r : AddressRange} (hr : r ∈ ranges)
    {address : Nat} (hlo : r.start ≤ address) (hhi : address < r.stop) :
    ∃ byte, image.readByte? address = some byte := by
  have hg := forall_mem_of_all h r hr
  have hk : address - r.start < r.size := by
    have : address < r.start + r.size := hhi
    omega
  have hb := forall_mem_of_all_list hg (address - r.start) (List.mem_range.mpr hk)
  have haddr : r.start + (address - r.start) = address := by omega
  rw [haddr] at hb
  exact Option.isSome_iff_exists.mp hb

/-- **Readability across each function instance's whole execution extent.** The ranges are
`functionInstanceExecutionRanges`, i.e. exactly the range form of `functionInstanceExecutionPcs`
(`executionPcs_iff_ranges`), so a `true` here covers every pc a closed obligation may confine
execution to — the absorbed excluded routines and the transfer closure included. -/
def executionExtentReadableIn (image : ProgramImage) (program : Program) : Bool :=
  program.functionInstances.all fun functionInstance =>
    rangesReadableIn image (functionInstanceExecutionRanges program functionInstance)

/-- The per-pc form the sentinel bridge consumes, still generic in the image. -/
theorem executionExtentReadableIn_elim {image : ProgramImage} {program : Program}
    (h : executionExtentReadableIn image program = true)
    {functionInstance : FunctionInstance} (hFunctionInstance : functionInstance ∈ program.functionInstances)
    {pc : BitVec 64} (hpc : functionInstanceExecutionPcs program functionInstance pc) :
    ∃ byte, image.readByte? pc.toNat = some byte := by
  obtain ⟨r, hr, hlo, hhi⟩ := functionInstanceExecutionPcs_iff_ranges.mp hpc
  exact rangesReadableIn_elim (forall_mem_of_all h functionInstance hFunctionInstance) hr hlo hhi

/-! ## The generated-data fact -/

/-- Every byte of every function instance's **execution extent** reads back from the canonical
`Artifact.programImage`. This is the fact `bytesReadableIn` does not carry. -/
theorem executionExtentReadable_true :
    executionExtentReadableIn Artifact.programImage generatedProgram = true := by native_decide

/-- **Every pc a generated function instance may execute at is a loaded address.** -/
theorem generated_execution_pcs_readable :
    ∀ functionInstance ∈ generatedProgram.functionInstances, ∀ pc : BitVec 64,
      functionInstanceExecutionPcs generatedProgram functionInstance pc →
        ∃ byte, Artifact.programImage.readByte? pc.toNat = some byte :=
  fun _ hFunctionInstance _ hpc =>
    executionExtentReadableIn_elim executionExtentReadable_true hFunctionInstance hpc

/-! ## The exit pcs, which the bridge quantifies over separately

`FunctionTrace.exitAt` knows only `exit pc`, never `region pc`, which is why `SentinelBridge` takes a
second avoidance hypothesis. So the exits need their own readability, and they get it from being
inside the function instance's own regions — a checked property of the generated inventory, not an
assumption. -/

/-- Every generated exit pc lies inside one of its own function instance's regions. -/
def exitPcsInOwnRegionsB (program : Program) : Bool :=
  program.functionInstances.all fun functionInstance =>
    functionInstance.exitPcs.all fun pc => Program.inRanges functionInstance.regions pc

theorem exitPcsInOwnRegions_true : exitPcsInOwnRegionsB generatedProgram = true := by native_decide

/-- A generated exit pc is a pc the function instance may execute at. -/
theorem generated_exit_pc_is_execution_pc
    {functionInstance : FunctionInstance} (hFunctionInstance : functionInstance ∈ generatedProgram.functionInstances)
    {pc : BitVec 64} (hexit : functionInstanceExitPred functionInstance pc) :
    functionInstanceExecutionPcs generatedProgram functionInstance pc := by
  have hrow := forall_mem_of_all exitPcsInOwnRegions_true functionInstance hFunctionInstance
  have hin := forall_mem_of_all hrow pc.toNat hexit
  exact functionInstanceExecutionPcs_iff_ranges.mpr
    (RegionPcs.append_iff.mpr (Or.inl (RegionPcs.iff_inRanges.mpr hin)))

/-- **Every generated exit pc is a loaded address.** -/
theorem generated_exit_pcs_readable :
    ∀ functionInstance ∈ generatedProgram.functionInstances, ∀ pc : BitVec 64,
      functionInstanceExitPred functionInstance pc →
        ∃ byte, Artifact.programImage.readByte? pc.toNat = some byte :=
  fun _ hFunctionInstance _ hexit =>
    generated_execution_pcs_readable _ hFunctionInstance _
      (generated_exit_pc_is_execution_pc hFunctionInstance hexit)

/-! ## The two sentinel-bridge hypotheses, discharged -/

open BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw in
/-- **`regionAvoidsSentinel` at the generated program.** Every pc a function instance may execute at
misses the return sentinel, because it is loaded and the sentinel is placed above everything the
image loads (`layout_above_loaded`). -/
theorem generated_execution_pcs_avoid_sentinel :
    ∀ functionInstance ∈ generatedProgram.functionInstances, ∀ pc : BitVec 64,
      functionInstanceExecutionPcs generatedProgram functionInstance pc →
        pc ≠ BitVec.ofNat 64 canonicalRunnerLayout.sentinel :=
  fun _ hFunctionInstance pc hpc =>
    loaded_word_ne_sentinel pc (generated_execution_pcs_readable _ hFunctionInstance pc hpc)

open BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw in
/-- **`exitAvoidsSentinel` at the generated program.** The companion the bridge needs for the one pc
`FunctionTrace` knows only as an exit. -/
theorem generated_exit_pcs_avoid_sentinel :
    ∀ functionInstance ∈ generatedProgram.functionInstances, ∀ pc : BitVec 64,
      functionInstanceExitPred functionInstance pc →
        pc ≠ BitVec.ofNat 64 canonicalRunnerLayout.sentinel :=
  fun _ hFunctionInstance pc hexit =>
    loaded_word_ne_sentinel pc (generated_exit_pcs_readable _ hFunctionInstance pc hexit)

/-! ## The mutation test: the extent check is strictly stronger than the region check

A `native_decide`d `= true` over the real data proves nothing about a predicate's *power*. The
mutant below is the diff between the two checks made concrete: one absorbed excluded routine is
moved above `loadedCeiling`, where the image reads nothing back. Its regions are not any function
instance's `regions`, so `bytesReadableIn` — the check
`IsCanonicalGeneratedProgram` actually uses — still passes; they *are* in every absorbing caller's
extent, so the new check fails. -/

/-- The offset that moves a range off the loaded image: `loadedCeiling`, above which
`segments_below_ceiling` says the ELF loads nothing. -/
def unloadedOffset : Nat := Entrypoints.ZesuDecodeRaw.loadedCeiling

/-- The generated program with every absorbed excluded routine relocated above everything the image
loads. Nothing else changes: the function instances keep their own regions verbatim. -/
def programWithUnloadedExcluded : Program :=
  { generatedProgram with
    excludedFunctionInstances := generatedProgram.excludedFunctionInstances.map fun excluded =>
      { excluded with
        regions := excluded.regions.map fun r => { r with start := r.start + unloadedOffset } } }

/-- **The mutation is real.** At least one excluded routine's regions genuinely moved — stated so a
future change that silently produced the original program would fail here rather than turn the two
theorems below into checks of nothing. -/
theorem programWithUnloadedExcluded_moved :
    programWithUnloadedExcluded.excludedFunctionInstances ≠
      generatedProgram.excludedFunctionInstances := by native_decide

/-- **The old check does not notice.** `bytesReadableIn` walks only `functionInstance.regions`, and
those are untouched. -/
theorem unloadedExcluded_passes_regionCheck :
    bytesReadableIn Artifact.programImage programWithUnloadedExcluded = true := by native_decide

/-- **The new check does.** The relocated ranges are in the extent of every caller that absorbs
them, and the image reads nothing there. So the extent clause is not implied by the region clause,
and this module is not restating a fact the tree already had. -/
theorem unloadedExcluded_fails_extentCheck :
    executionExtentReadableIn Artifact.programImage programWithUnloadedExcluded = false := by
  native_decide

end BinaryFv.SSZ.Zesu.Elfling.Validation
