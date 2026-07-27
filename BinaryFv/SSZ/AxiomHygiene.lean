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
not enough**, and the reason changed under this guard rather than going away. It used to be that
`root_compliance` reached the obligations only through a `sorry`-carrying scaffold, whose cone is
empty — so none of the theorems discharging those obligations was reachable from the root at all. That
is no longer true: the root now descends through the real assembly and its cone is 18,000
declarations. But a single anchor over a cone that large is a coarse instrument — one pin covering
forty-eight doors cannot say *which layer* acquired a new one — so the per-layer anchors are kept, and
they are what make a new door in `SpecCorrespondence` or the footprint layer land as a failure naming
that layer.
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

/-- `heapLayer_footprints_abi` — the heap layer's footprints. Its single door is
`raw_v4_heap_element_sizes_valid`, the compiler-reflected element sizes, already `native_decide` by
design for the guarded native observers.

**One door, where the obvious drafting would have opened two.**
`Artifact.heap_element_size_layout` derives the four sizes *from* that existing check instead of
running a second `native_decide` asserting the same four facts. Two independent reflections of one
manifest can drift; one cannot.

**And one anchor covering the layer, not one theorem.** The anchor is a conjunction reaching all five
manifest-derived footprints here, because an anchor only sees what its declaration reaches — the
chain layer above already needed two anchors for one door, and that does not survive `RawV4Rep`.

**The gap this shape inherits, named rather than left to be discovered.** A footprint added to the
layer and *not* added to the conjunction is invisible to the guard: the anchor's coverage is the
conjunction's cone, not the module's contents, and nothing forces the two to agree. So the
conjunction is not a complete guard standing alone. What closes it is the per-layer rule already in
force above: when such a sibling becomes load-bearing it enters the composition's cone, and the
composition's entry point carries its own anchor, so the transition to load-bearing fires the guard
rather than passing silently. **The conjunction is the right shape given that the entry-point anchor
lands later — it is not a substitute for it.** -/
def heapFootprintDoors : List Name :=
  [``BinaryFv.SSZ.Zesu.Artifact.raw_v4_heap_element_sizes_valid]

/-- `containerLayer_footprints_abi` — the allocating containers' footprints, all five including the
root. **Three** doors: `allocating_container_sizes_valid` for the four container record boundaries,
`raw_v4_heap_element_sizes_valid` for the element strides their regions are measured in, and
`raw_stateless_input_layout` for the root record.

**The guard refused this pin twice, and both times I was the one who was wrong.** First with one
door: a container footprint spans the record *and* the heap arrays it points at, so it inherits the
layer below. Then with two, when `RawV4Rep` landed and brought the root record size with it. Neither
is subtle in hindsight and neither changes the axiom set, so nothing but the door check could have
objected — which is the property this guard exists for, demonstrated twice in one sitting.

Anchored at the layer conjunction. The coverage gap recorded under `heapFootprintDoors` applies here
too: a footprint added to the layer and not to the conjunction is invisible until it enters the
composition's cone. -/
def containerFootprintDoors : List Name :=
  [``BinaryFv.SSZ.Zesu.Artifact.allocating_container_sizes_valid,
   ``BinaryFv.SSZ.Zesu.Artifact.raw_v4_heap_element_sizes_valid,
   ``BinaryFv.SSZ.Zesu.Artifact.raw_stateless_input_layout]

/-- `rawV4_survives_chain` — the ownership composition layer. **An empty door set, and that is the
claim.**

The layer is conditional: it takes the ownership promises and the root record size as premises and
proves they suffice, so it appeals to the compiler nowhere. Pinning that as `[]` makes it checkable —
the guard reports any door reachable from here as `unexpected`, so the day this layer picks up a
`native_decide`, directly or through something it starts consuming, the build says so.

It matters more here than elsewhere because **this layer is the artefact going to the human.** A
conditional theorem that quietly acquired a compiler appeal would still be conditional and still be
true, and no downstream axiom set would change — the one situation `#print axioms` cannot see and
this guard can.

**Coverage, stated rather than implied.** The anchor's cone is `rawV4_survives_chain`'s: the root
corollary, `chain_agrees_on_region`, and the whole `Footprint` chain beneath them. It does **not**
reach the four sibling corollaries or the satisfiability witnesses. That is the same gap recorded
under `heapFootprintDoors`, and it is acceptable for the same reason plus one more: those four are
the same three lines as the root's, so a door could only reach them through machinery this anchor
already covers. -/
def compositionDoors : List Name := []

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
worth being made to confirm rather than one to discover later.

**It happened again, for the same reason, when `knownDivergences` stopped being a premise.**
Threading `knownDivergences_holds` in made `decodeCanonical_forkOrderingWitness` — the `native_decide`
exhibiting the fork-ordering divergence — reachable from this anchor, and the guard refused the build
until it was recorded. No new kind of trust: the module docstring above notes that this very door was
already carried by `forkErrorOrderingDiffers_holds` and was *not* reachable from here, which was the
recorded provenance the first run of this check corrected. Making a premise into a proof is exactly
the change that moves such a door into the cone, so the door list growing here is the signal that the
residue shrank. -/
def residueDoors : List Name :=
  [``BinaryFv.SSZ.Zesu.Contracts.decodeCanonical_forkOrderingWitness,
   ``BinaryFv.SSZ.Zesu.Contracts.canonicalOptionalBlobSchedule_pinned,
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

/-- **`root_compliance_of_local_contracts` — every trust door the conditional root opens, and no
`sorry`.**

The list grew from four to forty-eight in one commit, and the growth is the point rather than a
regression: the root used to reach the machine layer through two `sorry`s, which are *opaque* — a
scaffold's cone is empty, so the doors below it were invisible to this guard. Now the root descends
through the real assembly, and every `native_decide` the generated program, the pinned image, the
CFG, the entry state builder and the three exit inventories rest on is named here.

Read as three groups. The **generated-program validation** facts (`Elfling.Validation.*`) were always
under the obligation half and are unchanged. The **artifact and layout** facts (the two `Artifact`
entries, `programImage_single`, `segments_below_ceiling`, `file_addr_lt`, `configure_normal`,
`configureFetchPinned_sentinelExits`, `buildZesuEntryState_entry_binding_abi`) are the runner's entry
state over the pinned bytes. The **attachment** facts (`controlFlow_some`, the three
`*_function_instance_found`/`_tag`/`_exits` families, `sentinelExitPcs_are_return_sites`,
`retWord_low_byte`, `baseInstructionEncoding_notRVC`) are what the run half needs: which instance the
runner enters, which contract it owes, and where its single exit is.

Discovered by walking the anchor's cone, never asserted — this list is the guard's own output pasted
back. -/
def conditionalRootDoors : List Name :=
  [-- the pinned artifact and the runner's entry state over it
   ``BinaryFv.SSZ.Zesu.Artifact.layout_is_valid,
   ``BinaryFv.SSZ.Zesu.Artifact.parsed_is_ok,
   ``BinaryFv.SSZ.Zesu.Artifact.raw_stateless_input_layout,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.buildZesuEntryState_entry_binding_abi,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.configureFetchPinned_sentinelExits,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.configure_normal,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.file_addr_lt,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.programImage_single,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.runnerSymbols_isSome,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.segments_below_ceiling,
   -- the decoder's private globals, as addresses
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.canonicalResultBuffer_below_ceiling,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.canonicalResultBuffer_ne_zero,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.decoderGlobals_below_ceiling,
   -- the three sentinel attachments: which instance, which contract, which exit
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.controlFlow_some,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.entry_function_instance_tag,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.rawError_function_instance_exits,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.rawError_function_instance_found,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.rawError_function_instance_tag,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.rawResult_function_instance_exits,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.rawResult_function_instance_found,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.rawResult_function_instance_tag,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.retWord_low_byte,
   ``BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.sentinelExitPcs_are_return_sites,
   ``BinaryFv.RiscV.baseInstructionEncoding_notRVC,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.entry_function_instance_exit_is_its_return,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.entry_function_instance_found,
   -- the generated program's own validation
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.allBytesReadable_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.callGraphRanked_check,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.callees_resolve_check,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.catalogIdsNodup_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.dispatchB_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.everyFunctionInstanceIsCatalogedB_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.everyRoutineHasFunctionInstanceB_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.excludedRoutinesAbsentB_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.executionExtentReadable_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.exitPcsInOwnRegions_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.functionInstanceIdsNodup_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.programGeometry_check,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.readArrayWidthsPresentB_true,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.returnExitsAreRet_check,
   ``BinaryFv.SSZ.Zesu.Elfling.Validation.sourceProvenanceRecordedB_true,
   -- the semantic layer's own doors, inherited unchanged
   ``BinaryFv.SSZ.Zesu.Contracts.canonicalOptionalBlobSchedule_pinned,
   ``BinaryFv.SSZ.Zesu.Contracts.canonicalOptionalU64_pinned,
   ``BinaryFv.SSZ.Zesu.Contracts.decodeCanonical_forkOrderingWitness,
   ``BinaryFv.SSZ.Zesu.Contracts.or_shifts_toNat,
   ``BinaryFv.SSZ.Zesu.SpecCorrespondence.readUInt32LE_uint32LE,
   ``BinaryFv.SSZ.Zesu.SpecCorrespondence.uint32LE_of_readUInt32LE,
   ``BinaryFv.SSZ.Zesu.SpecCorrespondence.uint64LE_of_readUInt64LE]

/-- **`root_compliance` — the conditional root's doors, plus exactly one more.**

Written as a `::` rather than as a second literal list, so "the public claim adds nothing to the
conditional one except the assumption" is enforced by the guard rather than by a reader comparing two
lists. If the root ever picks up a door the conditional theorem does not have, this pin fails. -/
def rootDoors : List Name :=
  ``BinaryFv.SSZ.assumedAllLocalContracts :: conditionalRootDoors

/-- The only declaration permitted to contain `sorry` in its own proof term, over the whole
environment: the 141 per-function-instance local trace obligations, assumed as one premise in
`BinaryFv/SSZ/Root.lean`. -/
def allowedSorrySites : List Name := [``BinaryFv.SSZ.assumedAllLocalContracts]

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
   (``BinaryFv.SSZ.Zesu.Contracts.Footprint.heapLayer_footprints_abi, heapFootprintDoors),
   (``BinaryFv.SSZ.Zesu.Contracts.Footprint.containerLayer_footprints_abi,
     containerFootprintDoors),
   (``BinaryFv.SSZ.Zesu.Contracts.OwnershipComposition.rawV4_survives_chain, compositionDoors),
   (``BinaryFv.SSZ.root_compliance_of_local_contracts, conditionalRootDoors),
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
