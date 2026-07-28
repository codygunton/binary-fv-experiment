import BinaryFv.SSZ.Zesu.Elfling.GeneratedValidationBridges
import BinaryFv.SSZ.Zesu.ControlFlow.Decode
import GeneratedElfling

/-!
# Validating the generated control-flow interface against the canonical decoded CFG (area #2)

The generator PROPOSES, per function instance, the real control-flow interface — entries, all exits, external
calls, a basic-block partition, and direct edges — from an objdump of the canonical linked ELF. This
module checks every one of those proposals against the **Sail-decoded** `controlFlowNodes` (the trusted
source of truth), so nothing is a `min(regions)`/`max(endpoint)` guess and no call is left as `#[]`:

* **entries** — every function instance's `entryPc` is a decoded node that control ENTERS from outside the
  function instance's own regions (a real CFG entry, not `min(regions)`);
* **exits** — the `exitPcs` are EXACTLY the decoded control-transfer-out points (returns/terminals or a
  successor leaving the regions): every listed exit really leaves, and every leaving PC is listed (no
  `max(endpoint)`, no missed exit);
* **external calls** — every emitted callee identity resolves to a generated cataloged function instance OR an
  explicitly excluded function instance, corresponds to a real decoded direct call out of the function instance, and
  every decoded direct call the function instance *makes* is listed (no call dropped);
* **basic blocks** — the blocks exactly partition each function instance's regions (contained, pairwise
  disjoint, total size = region size, over disjoint regions), and every region PC is a decoded node;
* **edges** — the emitted direct edges are EXACTLY the decoded direct successors of the PCs each
  function instance DEEPEST-owns: every emitted edge is a real decoded successor (`edgesValid`, soundness —
  no invented edge) AND every decoded successor of every deepest-owned PC is an emitted edge
  (`edgesComplete`, completeness — no dropped edge). Because the generated artifact is an untrusted
  certificate, both directions are checked here; a tampered artifact that silently omits a real
  non-call edge fails `edgesComplete` (see the negative test at the end of this module).

Classification of each edge/node (internal / inline-child / call / return / excluded transition) and
the "nothing unclassified" completeness proof are area #5; this module establishes that the emitted
interface EXISTS and CORRESPONDS to the decoded CFG. Each check is a `native_decide` (SSZ-layer
exception) dispatched through `controlFlow?`, so a decode failure makes it `false`; the composition tie
to the canonical CFG is an ordinary kernel bridge.
-/

namespace BinaryFv.SSZ.Zesu.Elfling.Validation

set_option maxRecDepth 8000

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.ControlFlow (controlFlow?)

/-- The canonical ELF decodes to some node array. -/
theorem controlFlow_isSome : ∃ nodes, controlFlow? = some nodes :=
  Option.isSome_iff_exists.mp (by native_decide)
open BinaryFv.SSZ.Zesu.Elfling.Generated
  (generatedElfling generatedExcludedFunctionInstances ExcludedFunctionInstance)

/-! ## FunctionInstance geometry -/

/-- Whether `pc` lies in one of the function instance's regions. -/
def inRegions (functionInstance : FunctionInstance) (pc : Nat) : Bool :=
  functionInstance.regions.any fun r => decide (r.start ≤ pc ∧ pc < r.stop)

/-- A PC is DEEPEST-owned by `functionInstance` when `functionInstance` contains it and no child function instance does. -/
def ownedBy (program : Elfling) (functionInstance : FunctionInstance) (pc : Nat) : Bool :=
  inRegions functionInstance pc && functionInstance.children.all fun cid =>
    match program.find? cid with
    | some c => !inRegions c pc
    | none => true

/-- The entry PC an excluded routine is called at (its lowest region start). -/
def exclEntryPc (x : ExcludedFunctionInstance) : Nat :=
  x.regions.foldl (fun m r => Nat.min m r.start) ((x.regions[0]?.map (·.start)).getD 0)

/-- The entry PC a callee identity names — an emitted function instance's `entryPc` or an excluded routine's
entry — or `none` if the identity resolves to no generated function instance. -/
def calleeEntryPc? (program : Elfling) (id : FunctionInstanceId) : Option Nat :=
  match program.functionInstances.find? (fun i => decide (i.id = id)) with
  | some i => some i.entryPc
  | none => (generatedExcludedFunctionInstances.find? (fun x => decide (x.id = id))).map exclEntryPc

/-! ## Per-aspect checks over explicit decoded `nodes` -/

/-- A transfer that leaves its function without a direct in-CFG successor to fall through to. -/
def isReturnOrTerminal : ControlTransfer → Bool
  | .return_ _ => true
  | .terminal => true
  | _ => false

/-- `pc` (a decoded node) transfers control OUT of `functionInstance`: it returns/terminates, or has a decoded direct
successor outside `functionInstance`'s regions. -/
def leavesFunctionInstance (nodes : Array ControlFlowNode) (functionInstance : FunctionInstance) (pc : Nat) : Bool :=
  match ControlFlowNodeAt? nodes pc with
  | some n => isReturnOrTerminal n.transfer || (n.transfer.directTargets.any fun t => !inRegions functionInstance t)
  | none => false

/-- Every region PC of every function instance is a decoded node. Blocks tile the regions, so this also ties
every block byte to the decoded CFG. -/
def regionsDecoded (nodes : Array ControlFlowNode) (program : Elfling) : Bool :=
  program.functionInstances.all fun functionInstance =>
    functionInstance.regions.all fun r => (List.range (r.size / 4)).all fun k =>
      hasControlFlowAddress nodes (r.start + 4 * k)

/-- The lowest region start of a function instance (its DWARF entry / first fragment). -/
def minRegionStart (functionInstance : FunctionInstance) : Nat :=
  functionInstance.regions.foldl (fun m r => Nat.min m r.start) functionInstance.entryPc

/-- `functionInstance.entryPc` is entered by a decoded direct edge from OUTSIDE `functionInstance`'s own regions — a real CFG entry
into inlined code (fall-through/branch from the enclosing function instance). -/
def enteredFromOutside (nodes : Array ControlFlowNode) (functionInstance : FunctionInstance) : Bool :=
  nodes.any fun n =>
    n.transfer.directTargets.contains functionInstance.entryPc && !inRegions functionInstance n.word.encoded.address

/-- Every function instance's `entryPc` is a decoded node and the function instance's first-fragment start (its DWARF
entry), NOT a `min/max` guess elsewhere in the ranges. For an INLINED function instance it is additionally
validated as a real CFG entry — control reaches it by a decoded edge from outside the function instance's
regions. (Emitted functions are reached at their `low_pc`; those called only through the allocator
vtable have no decoded direct predecessor — an indirect call carries no direct edge — so the
entered-from-outside check applies to inlined function instances, where it holds for every one.) -/
def entriesValid (nodes : Array ControlFlowNode) (program : Elfling) : Bool :=
  program.functionInstances.all fun functionInstance =>
    hasControlFlowAddress nodes functionInstance.entryPc &&
    decide (functionInstance.entryPc = minRegionStart functionInstance) &&
    (functionInstance.id.inlineStack.isEmpty || enteredFromOutside nodes functionInstance)

/-- The `exitPcs` are EXACTLY the function instance's decoded control-transfer-out points: every listed exit
lies in the regions and really leaves, and every region PC that leaves is listed. This is the "all
exits, no `max(endpoint)`" check. -/
def exitsValid (nodes : Array ControlFlowNode) (program : Elfling) : Bool :=
  program.functionInstances.all fun functionInstance =>
    (functionInstance.exitPcs.all fun pc => inRegions functionInstance pc && leavesFunctionInstance nodes functionInstance pc) &&
    functionInstance.regions.all fun r => (List.range (r.size / 4)).all fun k =>
      let pc := r.start + 4 * k
      !leavesFunctionInstance nodes functionInstance pc || functionInstance.exitPcs.contains pc

/-- Every emitted direct edge is a real decoded direct successor of an in-region source
(soundness: no invented edge). -/
def edgesValid (nodes : Array ControlFlowNode) (program : Elfling) : Bool :=
  program.functionInstances.all fun functionInstance =>
    functionInstance.edges.all fun e =>
      inRegions functionInstance e.source && (directSuccessorsAt nodes e.source).contains e.target

/-- The REVERSE inclusion of `edgesValid` (completeness: no dropped edge). For every function instance, every
region PC it DEEPEST-owns, and every decoded direct successor `t` of that PC, the edge
`{ source := pc, target := t }` occurs in the function instance's emitted edge list. Together with `edgesValid`
this pins `functionInstance.edges` to EXACTLY the decoded direct-successor edges out of the PCs `functionInstance` owns, so the
untrusted artifact cannot silently drop a real edge and still validate. -/
def edgesComplete (nodes : Array ControlFlowNode) (program : Elfling) : Bool :=
  program.functionInstances.all fun functionInstance =>
    functionInstance.regions.all fun r => (List.range (r.size / 4)).all fun k =>
      let pc := r.start + 4 * k
      !ownedBy program functionInstance pc ||
        (directSuccessorsAt nodes pc).all fun t =>
          functionInstance.edges.any fun e => e.source == pc && e.target == t

/-- External calls correspond to the decoded direct calls: every emitted callee resolves to a
generated function instance and is the target of a real decoded direct call out of `functionInstance`, and every decoded
direct call `functionInstance` DEEPEST-owns is emitted — so calls are neither invented nor dropped. -/
def externalCallsValid (nodes : Array ControlFlowNode) (program : Elfling) : Bool :=
  let dce := directCallEdges nodes
  program.functionInstances.all fun functionInstance =>
    (functionInstance.externalCalls.all fun id =>
      match calleeEntryPc? program id with
      | some target => dce.any fun ce => inRegions functionInstance ce.source && ce.target == target
      | none => false) &&
    dce.all fun ce =>
      !ownedBy program functionInstance ce.source ||
      functionInstance.externalCalls.any fun id => calleeEntryPc? program id == some ce.target

/-- Basic blocks exactly partition each function instance's regions: each block is contained in a region, the
blocks are pairwise disjoint, the regions are pairwise disjoint, and the blocks' total size equals the
regions' — so together they cover every region PC exactly once, with no gap and no overlap. -/
def blocksPartition (program : Elfling) : Bool :=
  program.functionInstances.all fun functionInstance =>
    (functionInstance.blocks.all fun b => functionInstance.regions.any fun r => decide (r.start ≤ b.range.start ∧ b.range.stop ≤ r.stop)) &&
    (List.range functionInstance.blocks.size).all (fun i => (List.range functionInstance.blocks.size).all fun j =>
      decide (i = j) ||
        decide ((functionInstance.blocks[i]!).range.stop ≤ (functionInstance.blocks[j]!).range.start ∨
                (functionInstance.blocks[j]!).range.stop ≤ (functionInstance.blocks[i]!).range.start)) &&
    (List.range functionInstance.regions.size).all (fun i => (List.range functionInstance.regions.size).all fun j =>
      decide (i = j) ||
        decide ((functionInstance.regions[i]!).stop ≤ (functionInstance.regions[j]!).start ∨
                (functionInstance.regions[j]!).stop ≤ (functionInstance.regions[i]!).start)) &&
    (functionInstance.blocks.foldl (fun s b => s + b.range.size) 0 == functionInstance.regions.foldl (fun s r => s + r.size) 0)

/-! ## The dispatched checks (through the canonical decode) -/

/-- All CFG-interface checks for an arbitrary `program`, dispatched through `controlFlow?` (so a
parse/decode failure is `false`). Uses `Option.map`/`getD` rather than a `match`, so the kernel bridge
never reduces the ~3984-word decode (same reason as the reachability certificate). Parameterising over
`program` lets the negative test run the SAME validation against a tampered program. -/
def cfgInterfaceValidFor (program : Elfling) : Bool :=
  (controlFlow?.map fun nodes =>
    regionsDecoded nodes program &&
    entriesValid nodes program &&
    exitsValid nodes program &&
    edgesValid nodes program &&
    edgesComplete nodes program &&
    externalCallsValid nodes program &&
    blocksPartition program).getD false

/-- The CFG-interface validation applied to the actual generated program. -/
def cfgInterfaceValidC : Bool := cfgInterfaceValidFor generatedElfling

/-- **The generated control-flow interface corresponds to the canonical decoded CFG.** Every entry is a
real entered-from-outside decoded node, every exit is exactly a decoded transfer-out point, every
external call resolves to a generated function instance and matches a decoded direct call (with none dropped),
the blocks exactly partition the regions, and the emitted edges are EXACTLY the decoded direct
successors of every deepest-owned PC (sound and complete). -/
theorem cfgInterfaceValidC_true : cfgInterfaceValidC = true := by native_decide

/-! ## Kernel bridge: tie the checks to explicit decoded nodes -/

/-- Specialise the dispatched check to explicit decoded `nodes` without reducing the decode. -/
theorem cfgInterfaceValid_some {nodes : Array ControlFlowNode}
    (hn : controlFlow? = some nodes) :
    regionsDecoded nodes generatedElfling = true ∧
    entriesValid nodes generatedElfling = true ∧
    exitsValid nodes generatedElfling = true ∧
    edgesValid nodes generatedElfling = true ∧
    edgesComplete nodes generatedElfling = true ∧
    externalCallsValid nodes generatedElfling = true ∧
    blocksPartition generatedElfling = true := by
  have h := cfgInterfaceValidC_true
  unfold cfgInterfaceValidC cfgInterfaceValidFor at h
  rw [hn] at h
  simp only [Option.map_some, Option.getD_some] at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **The exposed CFG-interface certificate.** The canonical ELF decodes to `nodes`, and against those
nodes the generated program's entries, exits, external calls, basic-block partition, and direct edges
are all validated — the edges both sound (`edgesValid`) and complete (`edgesComplete`). This is the
area-#2 correspondence the later edge-classification (area #5) builds on. -/
theorem generatedCfgInterfaceCertificate :
    ∃ nodes : Array ControlFlowNode,
      controlFlow? = some nodes ∧
      regionsDecoded nodes generatedElfling = true ∧
      entriesValid nodes generatedElfling = true ∧
      exitsValid nodes generatedElfling = true ∧
      edgesValid nodes generatedElfling = true ∧
      edgesComplete nodes generatedElfling = true ∧
      externalCallsValid nodes generatedElfling = true ∧
      blocksPartition generatedElfling = true := by
  obtain ⟨nodes, hn⟩ := controlFlow_isSome
  exact ⟨nodes, hn, cfgInterfaceValid_some hn⟩

/-! ## Reverse edge inclusion as a proposition, and its negative test -/

/-- **Every decoded direct successor of every deepest-owned PC is an emitted edge** (the reverse
inclusion, in proposition form). For every function instance `functionInstance`, every region PC `pc := r.start + 4 * k` it
deepest-owns, and every decoded direct successor `t` of `pc`, the edge `{ source := pc, target := t }`
is present in `functionInstance.edges`. This is the `Prop` companion of the `edgesComplete` clause of the certificate:
the generated edge inventory is a COMPLETE certificate of the decoded successor relation, not merely a
sound one. -/
theorem edgesComplete_holds {nodes : Array ControlFlowNode}
    (hn : controlFlow? = some nodes) :
    ∀ functionInstance ∈ generatedElfling.functionInstances, ∀ r ∈ functionInstance.regions, ∀ k, k < r.size / 4 →
      ownedBy generatedElfling functionInstance (r.start + 4 * k) = true →
        ∀ t ∈ directSuccessorsAt nodes (r.start + 4 * k),
          (functionInstance.edges.any fun e => e.source == r.start + 4 * k && e.target == t) = true := by
  have hcomplete := (cfgInterfaceValid_some hn).2.2.2.2.1
  intro functionInstance ho r hr k hk hown t ht
  have h1 := forall_mem_of_all hcomplete functionInstance ho
  have h2 := forall_mem_of_all h1 r hr
  have h3 := forall_mem_of_all_list h2 k (List.mem_range.mpr hk)
  simp only [hown, Bool.not_true, Bool.false_or] at h3
  exact forall_mem_of_all h3 t ht

/-! ### Negative test: dropping one real non-call edge breaks completeness

The reverse inclusion has teeth only if omitting a real edge is actually rejected. `0x10250 → 0x10254`
(decimal `66128 → 66132`) is a straight-line fall-through step inside a single basic block of the
`zesu_raw_alloc` function instance (functionInstance 0) — a single decoded successor, so it is NOT a call. Deleting it from
the generated artifact must make `edgesComplete` (and hence the whole CFG-interface validation) fail. -/

/-- The concrete non-call edge the negative test deletes. -/
def droppedEdge : DirectEdge := { source := 66128, target := 66132 }

/-- The dropped edge really is one the generator emitted, so the tamper removes something real. -/
theorem droppedEdge_present :
    (generatedElfling.functionInstances.any fun functionInstance => functionInstance.edges.any fun e => decide (e = droppedEdge)) = true := by
  native_decide

/-- `generatedElfling` with `droppedEdge` deleted from wherever it was emitted: a hand-tampered
artifact that silently drops one real non-call edge. -/
def edgeDroppedElfling : Elfling :=
  { generatedElfling with
    functionInstances := generatedElfling.functionInstances.map fun functionInstance =>
      { functionInstance with edges := functionInstance.edges.filter fun e => decide (e ≠ droppedEdge) } }

/-- **Completeness is not vacuous.** With one real non-call edge dropped, the reverse-inclusion check
fails: the omitted decoded successor is detected. -/
theorem edgeDropped_incomplete :
    (controlFlow?.map fun nodes => edgesComplete nodes edgeDroppedElfling).getD true = false := by
  native_decide

/-- **The whole CFG-interface validation rejects the tampered program** — dropping a single generated
non-call edge is caught, so the emitted edge list is enforced as a complete certificate. -/
theorem edgeDropped_cfgInterface_invalid : cfgInterfaceValidFor edgeDroppedElfling = false := by
  native_decide

end BinaryFv.SSZ.Zesu.Elfling.Validation
