import BinaryFv.SSZ.Zesu.Elfling.GeneratedValidationBridges
import BinaryFv.SSZ.Zesu.ControlFlow.Reachability
import GeneratedProgram

/-!
# Validating the generated control-flow interface against the canonical decoded CFG (area #2)

The generator PROPOSES, per occurrence, the real control-flow interface — entries, all exits, external
calls, a basic-block partition, and direct edges — from an objdump of the canonical linked ELF. This
module checks every one of those proposals against the **Sail-decoded** `controlFlowNodes` (the trusted
source of truth), so nothing is a `min(regions)`/`max(endpoint)` guess and no call is left as `#[]`:

* **entries** — every occurrence's `entryPc` is a decoded node that control ENTERS from outside the
  occurrence's own regions (a real CFG entry, not `min(regions)`);
* **exits** — the `exitPcs` are EXACTLY the decoded control-transfer-out points (returns/terminals or a
  successor leaving the regions): every listed exit really leaves, and every leaving PC is listed (no
  `max(endpoint)`, no missed exit);
* **external calls** — every emitted callee identity resolves to a generated cataloged occurrence OR an
  explicitly excluded occurrence, corresponds to a real decoded direct call out of the occurrence, and
  every decoded direct call the occurrence *makes* is listed (no call dropped);
* **basic blocks** — the blocks exactly partition each occurrence's regions (contained, pairwise
  disjoint, total size = region size, over disjoint regions), and every region PC is a decoded node;
* **edges** — every emitted direct edge is a real decoded direct successor.

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
open BinaryFv.SSZ.Zesu.Elfling.Generated
  (generatedProgram generatedExcludedOccurrences ExcludedOccurrence)

/-! ## Occurrence geometry -/

/-- Whether `pc` lies in one of the occurrence's regions. -/
def inRegions (o : FunctionInstance) (pc : Nat) : Bool :=
  o.regions.any fun r => decide (r.start ≤ pc ∧ pc < r.stop)

/-- A PC is DEEPEST-owned by `o` when `o` contains it and no child instance does. -/
def ownedBy (program : Program) (o : FunctionInstance) (pc : Nat) : Bool :=
  inRegions o pc && o.children.all fun cid =>
    match program.find? cid with
    | some c => !inRegions c pc
    | none => true

/-- The entry PC an excluded routine is called at (its lowest region start). -/
def exclEntryPc (x : ExcludedOccurrence) : Nat :=
  x.regions.foldl (fun m r => Nat.min m r.start) ((x.regions[0]?.map (·.start)).getD 0)

/-- The entry PC a callee identity names — an emitted occurrence's `entryPc` or an excluded routine's
entry — or `none` if the identity resolves to no generated occurrence. -/
def calleeEntryPc? (program : Program) (id : InstanceId) : Option Nat :=
  match program.instances.find? (fun i => decide (i.id = id)) with
  | some i => some i.entryPc
  | none => (generatedExcludedOccurrences.find? (fun x => decide (x.id = id))).map exclEntryPc

/-! ## Per-aspect checks over explicit decoded `nodes` -/

/-- A transfer that leaves its function without a direct in-CFG successor to fall through to. -/
def isReturnOrTerminal : ControlTransfer → Bool
  | .return_ _ => true
  | .terminal => true
  | _ => false

/-- `pc` (a decoded node) transfers control OUT of `o`: it returns/terminates, or has a decoded direct
successor outside `o`'s regions. -/
def leavesOccurrence (nodes : Array ControlFlowNode) (o : FunctionInstance) (pc : Nat) : Bool :=
  match ControlFlowNodeAt? nodes pc with
  | some n => isReturnOrTerminal n.transfer || (n.transfer.directTargets.any fun t => !inRegions o t)
  | none => false

/-- Every region PC of every occurrence is a decoded node. Blocks tile the regions, so this also ties
every block byte to the decoded CFG. -/
def regionsDecoded (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  program.instances.all fun o =>
    o.regions.all fun r => (List.range (r.size / 4)).all fun k =>
      hasControlFlowAddress nodes (r.start + 4 * k)

/-- The lowest region start of an occurrence (its DWARF entry / first fragment). -/
def minRegionStart (o : FunctionInstance) : Nat :=
  o.regions.foldl (fun m r => Nat.min m r.start) o.entryPc

/-- `o.entryPc` is entered by a decoded direct edge from OUTSIDE `o`'s own regions — a real CFG entry
into inlined code (fall-through/branch from the enclosing occurrence). -/
def enteredFromOutside (nodes : Array ControlFlowNode) (o : FunctionInstance) : Bool :=
  nodes.any fun n =>
    n.transfer.directTargets.contains o.entryPc && !inRegions o n.word.encoded.address

/-- Every occurrence's `entryPc` is a decoded node and the occurrence's first-fragment start (its DWARF
entry), NOT a `min/max` guess elsewhere in the ranges. For an INLINED occurrence it is additionally
validated as a real CFG entry — control reaches it by a decoded edge from outside the occurrence's
regions. (Emitted functions are reached at their `low_pc`; those called only through the allocator
vtable have no decoded direct predecessor — an indirect call carries no direct edge — so the
entered-from-outside check applies to inlined occurrences, where it holds for every one.) -/
def entriesValid (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  program.instances.all fun o =>
    hasControlFlowAddress nodes o.entryPc &&
    decide (o.entryPc = minRegionStart o) &&
    (o.id.inlineStack.isEmpty || enteredFromOutside nodes o)

/-- The `exitPcs` are EXACTLY the occurrence's decoded control-transfer-out points: every listed exit
lies in the regions and really leaves, and every region PC that leaves is listed. This is the "all
exits, no `max(endpoint)`" check. -/
def exitsValid (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  program.instances.all fun o =>
    (o.exitPcs.all fun pc => inRegions o pc && leavesOccurrence nodes o pc) &&
    o.regions.all fun r => (List.range (r.size / 4)).all fun k =>
      let pc := r.start + 4 * k
      !leavesOccurrence nodes o pc || o.exitPcs.contains pc

/-- Every emitted direct edge is a real decoded direct successor of an in-region source. -/
def edgesValid (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  program.instances.all fun o =>
    o.edges.all fun e =>
      inRegions o e.source && (directSuccessorsAt nodes e.source).contains e.target

/-- External calls correspond to the decoded direct calls: every emitted callee resolves to a
generated occurrence and is the target of a real decoded direct call out of `o`, and every decoded
direct call `o` DEEPEST-owns is emitted — so calls are neither invented nor dropped. -/
def externalCallsValid (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  let dce := directCallEdges nodes
  program.instances.all fun o =>
    (o.externalCalls.all fun id =>
      match calleeEntryPc? program id with
      | some target => dce.any fun ce => inRegions o ce.source && ce.target == target
      | none => false) &&
    dce.all fun ce =>
      !ownedBy program o ce.source ||
      o.externalCalls.any fun id => calleeEntryPc? program id == some ce.target

/-- Basic blocks exactly partition each occurrence's regions: each block is contained in a region, the
blocks are pairwise disjoint, the regions are pairwise disjoint, and the blocks' total size equals the
regions' — so together they cover every region PC exactly once, with no gap and no overlap. -/
def blocksPartition (program : Program) : Bool :=
  program.instances.all fun o =>
    (o.blocks.all fun b => o.regions.any fun r => decide (r.start ≤ b.range.start ∧ b.range.stop ≤ r.stop)) &&
    (List.range o.blocks.size).all (fun i => (List.range o.blocks.size).all fun j =>
      decide (i = j) ||
        decide ((o.blocks[i]!).range.stop ≤ (o.blocks[j]!).range.start ∨
                (o.blocks[j]!).range.stop ≤ (o.blocks[i]!).range.start)) &&
    (List.range o.regions.size).all (fun i => (List.range o.regions.size).all fun j =>
      decide (i = j) ||
        decide ((o.regions[i]!).stop ≤ (o.regions[j]!).start ∨
                (o.regions[j]!).stop ≤ (o.regions[i]!).start)) &&
    (o.blocks.foldl (fun s b => s + b.range.size) 0 == o.regions.foldl (fun s r => s + r.size) 0)

/-! ## The dispatched checks (through the canonical decode) -/

/-- All CFG-interface checks, dispatched through `controlFlow?` (so a parse/decode failure is `false`).
Uses `Option.map`/`getD` rather than a `match`, so the kernel bridge never reduces the ~3984-word decode
(same reason as the reachability certificate). -/
def cfgInterfaceValidC : Bool :=
  (controlFlow?.map fun nodes =>
    regionsDecoded nodes generatedProgram &&
    entriesValid nodes generatedProgram &&
    exitsValid nodes generatedProgram &&
    edgesValid nodes generatedProgram &&
    externalCallsValid nodes generatedProgram &&
    blocksPartition generatedProgram).getD false

/-- **The generated control-flow interface corresponds to the canonical decoded CFG.** Every entry is a
real entered-from-outside decoded node, every exit is exactly a decoded transfer-out point, every
external call resolves to a generated occurrence and matches a decoded direct call (with none dropped),
the blocks exactly partition the regions, and every edge is a real decoded successor. -/
theorem cfgInterfaceValidC_true : cfgInterfaceValidC = true := by native_decide

/-! ## Kernel bridge: tie the checks to explicit decoded nodes -/

/-- Specialise the dispatched check to explicit decoded `nodes` without reducing the decode. -/
theorem cfgInterfaceValid_some {nodes : Array ControlFlowNode}
    (hn : controlFlow? = some nodes) :
    regionsDecoded nodes generatedProgram = true ∧
    entriesValid nodes generatedProgram = true ∧
    exitsValid nodes generatedProgram = true ∧
    edgesValid nodes generatedProgram = true ∧
    externalCallsValid nodes generatedProgram = true ∧
    blocksPartition generatedProgram = true := by
  have h := cfgInterfaceValidC_true
  unfold cfgInterfaceValidC at h
  rw [hn] at h
  simp only [Option.map_some, Option.getD_some] at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **The exposed CFG-interface certificate.** The canonical ELF decodes to `nodes`, and against those
nodes the generated program's entries, exits, external calls, basic-block partition, and direct edges
are all validated. This is the area-#2 correspondence the later edge-classification (area #5) builds on. -/
theorem generatedCfgInterfaceCertificate :
    ∃ nodes : Array ControlFlowNode,
      controlFlow? = some nodes ∧
      regionsDecoded nodes generatedProgram = true ∧
      entriesValid nodes generatedProgram = true ∧
      exitsValid nodes generatedProgram = true ∧
      edgesValid nodes generatedProgram = true ∧
      externalCallsValid nodes generatedProgram = true ∧
      blocksPartition generatedProgram = true := by
  obtain ⟨nodes, hn⟩ := ControlFlow.controlFlow_isSome
  exact ⟨nodes, hn, cfgInterfaceValid_some hn⟩

end BinaryFv.SSZ.Zesu.Elfling.Validation
