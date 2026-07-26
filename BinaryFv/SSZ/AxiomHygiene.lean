import Lean
import BinaryFv.SSZ

/-!
# Axiom hygiene, mechanically enforced

Every claim this project makes about its own trust surface is checked here, at build time, so that a
new theorem carrying a new trust dependency fails the build instead of waiting for someone to
remember to look.

## Why an axiom *set* check is not enough — and would have hidden a real error

The obvious check is `#print axioms`, asserting the result lies in an allowlist. It is **incapable of
detecting a new door**. `root_compliance` already depends on `Lean.ofReduceBool`,
`Lean.trustCompiler` and `sorryAx`, so adding one more `native_decide` anywhere in its dependency cone
leaves the printed axiom set **byte-identical**. An allowlist over that set therefore passes no matter
how many new appeals to the compiler are introduced. It is a check that cannot fail, which is the
defect this row keeps finding in other guises.

What has power is the **door set**: the declarations that appeal to a trust axiom *directly*, in their
own proof term, reachable from a given anchor. Adding a `native_decide` adds a door even when it adds
no axiom. So the doors are what is pinned below.

This is not hypothetical. The first run of this check found that the recorded provenance of
`catalogSemanticObligations_of_oracleAgreement` was wrong: it was documented as carrying the compiler
pair from *two* sources, `meaningTwentyFourIsSome_holds` through `uint64LE_of_readUInt64LE` **and**
`forkErrorOrderingDiffers_holds`'s `native_decide`. Only the first exists —
`forkErrorOrderingDiffers` is a conjunct of `knownDivergences`, not of `catalogSemanticObligations`,
and is not reachable from that theorem at all. The axiom set is the same either way, so no amount of
`#print axioms` could have caught it.

## What is pinned, and what each pin means

* **Sorry sites.** The declarations whose own proof term contains `sorryAx`. Scanned over the *entire*
  environment, not just `BinaryFv`, so a `sorry` in a pinned upstream module would be caught too
  (there are none). This is strictly stronger than `nix/proof.nix`'s textual per-file `sorry` count,
  which cannot see a `sorry` that arrives through an import and cannot see an axiom at all. Both are
  kept: the textual gate pins *where* they are written, this one pins *what the kernel sees*.
* **Door owners per anchor.** For each anchor, the set of named theorems owning a trust door reachable
  from it. Compiler-generated suffixes are stripped to the owning declaration, because `_proof_1_14`
  is renumbered by unrelated edits and pinning it would produce spurious failures.

Anchors are chosen so that the row's load-bearing content is actually covered. **The root alone is
not enough, and assuming it would have been a green check with almost no power.** `root_compliance`
takes `sszComplianceObligations` as a *hypothesis*, so its cone contains none of the theorems that
discharge those obligations — not the residue theorem, and nothing in `SpecCorrespondence`. Each layer
therefore needs its own anchor.
-/

open Lean Elab Command

namespace BinaryFv.SSZ.AxiomHygiene

/-- The two axioms `native_decide` and `bv_decide` appeal to. -/
def trustAxioms : List Name := [``Lean.ofReduceBool, ``Lean.trustCompiler]

/-- Lean's own classical axioms. A proof reaching only these is what this project calls clean. -/
def classicalAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Strip compiler-generated components to the user-facing declaration owning a proof term. -/
def ownerOf (n : Name) : Name := Id.run do
  let mut m := n
  while m.isInternal do m := m.getPrefix
  return m

/-- The constants a declaration mentions, in its type and in its value. -/
def mentioned (ci : ConstantInfo) : Array Name :=
  match ci.value? with
  | some v => ci.type.getUsedConstants ++ v.getUsedConstants
  | none => ci.type.getUsedConstants

/-- Does this declaration appeal to a trust axiom or to `sorry` in its own term? -/
def isDoor (used : Array Name) : Bool :=
  used.contains ``Lean.ofReduceBool || used.contains ``Lean.trustCompiler
    || used.contains ``sorryAx

/-- The owners of every trust door reachable from `n`. A plain reachability DFS: each constant is
tested once, so the visited set is sound here in a way a *cached axiom set* would not be. -/
partial def doorOwners (env : Environment) (visited : IO.Ref NameSet) (doors : IO.Ref NameSet)
    (n : Name) : IO Unit := do
  if (← visited.get).contains n then return
  visited.modify (·.insert n)
  let some ci := env.find? n | return
  let used := mentioned ci
  if isDoor used then doors.modify (·.insert (ownerOf n))
  for d in used do doorOwners env visited doors d

/-- Compare two name sets and describe the difference, or `none` when they agree. -/
def diagnose (label : String) (expected actual : List Name) : Option MessageData :=
  let missing := expected.filter (fun e => !actual.contains e)
  let extra := actual.filter (fun a => !expected.contains a)
  if missing.isEmpty && extra.isEmpty then none
  else some m!"{label}\n  unexpected (new trust dependency): {extra}\n  \
    absent (pin is stale, tighten it): {missing}"

/-! ## The pins

Each entry is an anchor and the named theorems owning the trust doors reachable from it. A new door
makes the `unexpected` list non-empty; removing one makes `absent` non-empty, so the pin cannot rot
silently in either direction. -/

/-- `raw_acceptance_agrees` — the raw-level intermediate. Its only doors are the `bv_decide` `u32`
encode/decode primitive and its companion; that is what makes the claim "this opens no new trust
dependency" checkable rather than asserted. -/
def rawIntermediateDoors : List Name :=
  [``BinaryFv.SSZ.Zesu.SpecCorrespondence.uint32LE_of_readUInt32LE,
   ``BinaryFv.SSZ.Zesu.SpecCorrespondence.readUInt32LE_uint32LE]

/-- `forkActivation_footprint_abi` — the ownership discipline's footprint layer. Its single door is
the ABI layout reflection, `native_decide` by design, the same one `container_field_offsets_valid`
opens for the representation offsets.

**Pinned before it is load-bearing, deliberately.** Nothing depends on this corollary yet, and none of
the four older anchors reaches `Contracts/Footprint` — so without this entry a door opened here is
invisible to the guard, and would stay invisible right up to the moment the discipline is wired into
the real obligations. That moment is the *least* visible one available: the guard would have been
green across the whole intervening period. Pinning now makes the transition to load-bearing a diff
rather than a silence.

The parametric `forkActivation_footprint_record` deliberately carries **no** door; only the
manifest-instantiated form does. That split is what this pin records. -/
def ownershipFootprintDoors : List Name :=
  [``BinaryFv.SSZ.Zesu.Artifact.fork_activation_layout]

/-- The chain footprints' door: the `forkConfig`/`chainConfig` layout reflection. Added under the
same rule as `ownershipFootprintDoors` — **a module introducing a trust door gets an anchor when the
door is introduced, not when it becomes load-bearing** — applied here without being asked, because a
remedy that depends on being reminded inherits the failure it is meant to prevent. -/
def chainFootprintDoors : List Name :=
  [``BinaryFv.SSZ.Zesu.Artifact.fork_chain_config_layout]

/-- `catalogSemanticObligations_of_oracleAgreement` — a single door, through the `u64` primitive.
See the module docstring: the recorded provenance claimed two. -/
def catalogObligationDoors : List Name :=
  [``BinaryFv.SSZ.Zesu.SpecCorrespondence.uint64LE_of_readUInt64LE]

/-- `sszComplianceObligations_of_residue` — the generated-data validation checks, which are
`native_decide` by design, plus `or_shifts_toNat`, the two pinned canonical layouts, and the two `u32`
`bv_decide` primitives.

The last two arrived when `sourceShapedDecodeAgreesWithOracle_holds` was threaded in, and the guard
**caught the change and refused the build** rather than absorbing it silently. That is the intended
behaviour on a legitimate change too: no new *kind* of trust was introduced — both doors were already
carried by `raw_acceptance_agrees` — but they became reachable from a deeper anchor, and that is a fact
worth being made to confirm rather than one to discover later. -/
def residueDoors : List Name :=
  [``BinaryFv.SSZ.Zesu.Contracts.canonicalOptionalBlobSchedule_pinned,
   ``BinaryFv.SSZ.Zesu.Contracts.canonicalOptionalU64_pinned,
   ``BinaryFv.SSZ.Zesu.Contracts.or_shifts_toNat,
   ``BinaryFv.SSZ.Zesu.SpecCorrespondence.uint64LE_of_readUInt64LE,
   ``BinaryFv.SSZ.Zesu.SpecCorrespondence.uint32LE_of_readUInt32LE,
   ``BinaryFv.SSZ.Zesu.SpecCorrespondence.readUInt32LE_uint32LE,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.allBytesReadable_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.callGraphRanked_check,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.callees_resolve_check,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.catalogIdsNodup_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.dispatchB_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.everyFunctionInstanceIsCatalogedB_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.everyRoutineHasFunctionInstanceB_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.excludedRoutinesAbsentB_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.functionInstanceIdsNodup_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.programGeometry_check,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.readArrayWidthsPresentB_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.sourceProvenanceRecordedB_true]

/-- `root_compliance` — four pinned-artifact `native_decide` facts plus the **two** live-run
scaffolds. Those two are the whole of D5's remaining `sorry` obligation, and they are visible here
rather than only in a grep. -/
def rootDoors : List Name :=
  [``BinaryFv.SSZ.Zesu.Artifact.layout_is_valid,
   ``BinaryFv.SSZ.Zesu.Artifact.parsed_is_ok,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.canonicalResultBuffer_ne_zero,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.runnerSymbols_isSome,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.successful_trace_of_spec_accepts,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.rejected_trace_of_spec_rejects]

/-- The only declarations permitted to contain `sorry` in their own proof term. Both are the live-run
scaffolds in `Entrypoints/ZesuDecodeRaw/Execution.lean`; D5 removes them. -/
def allowedSorrySites : List Name :=
  [``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.successful_trace_of_spec_accepts,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.rejected_trace_of_spec_rejects]

def anchors : List (Name × List Name) :=
  [(``BinaryFv.SSZ.Zesu.SpecCorrespondence.raw_acceptance_agrees, rawIntermediateDoors),
   (``BinaryFv.SSZ.Zesu.Contracts.catalogSemanticObligations_of_oracleAgreement,
     catalogObligationDoors),
   (``BinaryFv.SSZ.Zesu.Elfling.Validation.sszComplianceObligations_of_residue, residueDoors),
   (``BinaryFv.SSZ.Zesu.Contracts.Footprint.forkActivation_footprint_abi, ownershipFootprintDoors),
   (``BinaryFv.SSZ.Zesu.Contracts.Footprint.localTo_canonicalRepChainConfig_record,
     chainFootprintDoors),
   (``BinaryFv.SSZ.Zesu.Contracts.Footprint.localTo_canonicalRepForkConfig_record,
     chainFootprintDoors),
   (``BinaryFv.SSZ.root_compliance, rootDoors)]

run_cmd do
  let env ← getEnv
  let mut failures : Array MessageData := #[]

  -- Sorry sites, over the whole environment including the pinned upstream.
  let sitesRef ← IO.mkRef (∅ : NameSet)
  env.constants.forM fun n ci => do
    if (mentioned ci).contains ``sorryAx then sitesRef.modify (·.insert (ownerOf n))
  let sites := (← sitesRef.get).toList
  if let some msg := diagnose "sorry sites (whole environment)" allowedSorrySites sites then
    failures := failures.push msg

  -- Door owners per anchor.
  for (anchor, expected) in anchors do
    if (env.find? anchor).isNone then
      failures := failures.push m!"anchor {anchor} does not exist; the pin is anchored on nothing"
    else
      let visited ← IO.mkRef (∅ : NameSet)
      let doors ← IO.mkRef (∅ : NameSet)
      doorOwners env visited doors anchor
      if let some msg := diagnose s!"trust doors reachable from {anchor}" expected
          (← doors.get).toList then
        failures := failures.push msg

  unless failures.isEmpty do
    throwError m!"axiom hygiene check FAILED\n\n{MessageData.joinSep failures.toList "\n\n"}"
  logInfo m!"axiom hygiene OK: {sites.length} sorry site(s), {anchors.length} anchors pinned"

end BinaryFv.SSZ.AxiomHygiene
