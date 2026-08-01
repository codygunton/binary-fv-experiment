import BinaryFv.Zesu.Elflings.GeneratedValidationBridges
import BinaryFv.Zesu.ControlFlow.Decode
import GeneratedProgram

/-!
# Validating the generated control-flow interface against the canonical decoded CFG (area #2)

The generator PROPOSES, per function instance, the real control-flow interface — entries, all exits, external
calls, a basic-block partition, and direct edges — from an objdump of the canonical linked ELF. This
module checks every one of those proposals against the **Sail-decoded** `controlFlowNodes` (the trusted
source of truth), so nothing is a `min(regions)`/`max(endpoint)` guess and no call is left as `#[]`:

* **entries** — every function instance's `entryPc` is a decoded node that control ENTERS from outside the
  function instance's own regions (a real CFG entry, not `min(regions)`);
* **exits** — the `exitPcs` are EXACTLY the decoded control-transfer-out points (returns/terminals or a
  CONTINUATION leaving the regions): every listed exit really leaves, and every leaving PC is listed (no
  `max(endpoint)`, no missed exit). A resolved call's continuation is its fall-through, not its callee
  (see `exitContinuations`), so a call is an exit only in tail position;
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

namespace BinaryFv.Zesu.Elflings.Validation

set_option maxRecDepth 8000

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.Zesu.ControlFlow (controlFlow?)

/-- The canonical ELF decodes to some node array. -/
theorem controlFlow_isSome : ∃ nodes, controlFlow? = some nodes :=
  Option.isSome_iff_exists.mp (by native_decide)
open BinaryFv.Zesu.Elflings.Generated
  (generatedProgram generatedExcludedFunctionInstances)

/-! ## Function instance geometry -/

/-- Whether `pc` lies in one of the function instance's regions. -/
def inRegions (o : FunctionInstance) (pc : Nat) : Bool :=
  o.regions.any fun r => decide (r.start ≤ pc ∧ pc < r.stop)

/-- A PC is DEEPEST-owned by `o` when `o` contains it and no child instance does. -/
def ownedBy (program : Program) (o : FunctionInstance) (pc : Nat) : Bool :=
  inRegions o pc && o.children.all fun cid =>
    match program.find? cid with
    | some c => !inRegions c pc
    | none => true

/-- The entry PC an excluded function instance is called at (its lowest region start). -/
def exclEntryPc (x : BinaryFv.Binary.Elfling.Program.ExcludedFunctionInstance) : Nat :=
  x.regions.foldl (fun m r => Nat.min m r.start) ((x.regions[0]?.map (·.start)).getD 0)

/-- The entry PC a callee identity names — an emitted function instance's `entryPc` or an excluded function instance's
entry — or `none` if the identity resolves to no generated function instance. -/
def calleeEntryPc? (program : Program) (id : FunctionInstanceId) : Option Nat :=
  match program.functionInstances.find? (fun i => decide (i.id = id)) with
  | some i => some i.entryPc
  | none => (generatedExcludedFunctionInstances.find? (fun x => decide (x.id = id))).map exclEntryPc

/-! ## Per-aspect checks over explicit decoded `nodes` -/

/-- A transfer that leaves its function without a direct in-CFG successor to fall through to. -/
def isReturnOrTerminal : ControlTransfer → Bool
  | .return_ _ => true
  | .terminal => true
  | _ => false

/-- The successors that decide whether a transfer LEAVES its function instance — its *continuations*,
i.e. the addresses control is at next **and stays at**.

For every transfer but a call this is exactly `directTargets`. For a `call` it is the return address
ALONE: the callee edge is a direct successor of the pc, but control comes back to `pc + 4`, so a call
site does not leave its caller unless its own fall-through does (a tail-position call). Counting the
callee edge here is what `FunctionInstance.exitPcs`' docstring rules out when it says the exits are
"returns and tail-calls that leave this function instance", and it is not a cosmetic difference:
`FunctionTrace.step` carries `¬ exit pc`, so an exit at every call site would stop every caller's
trace at its first call. -/
def exitContinuations : ControlTransfer → Array Nat
  | .call _ returnAddress _ => #[returnAddress]
  | t => t.directTargets

/-- `pc` (a decoded node) transfers control OUT of `o`: it returns/terminates, or has a decoded
continuation outside `o`'s regions. Mirrors the generator's exit rule exactly, `exitContinuations`
included. -/
def leavesFunctionInstance (nodes : Array ControlFlowNode) (o : FunctionInstance) (pc : Nat) : Bool :=
  match ControlFlowNodeAt? nodes pc with
  | some n => isReturnOrTerminal n.transfer || ((exitContinuations n.transfer).any fun t => !inRegions o t)
  | none => false

/-- Every region PC of every function instance is a decoded node. Blocks tile the regions, so this also ties
every block byte to the decoded CFG. -/
def regionsDecoded (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  program.functionInstances.all fun o =>
    o.regions.all fun r => (List.range (r.size / 4)).all fun k =>
      hasControlFlowAddress nodes (r.start + 4 * k)

/-- The lowest region start of a function instance (its DWARF entry / first fragment). -/
def minRegionStart (o : FunctionInstance) : Nat :=
  o.regions.foldl (fun m r => Nat.min m r.start) o.entryPc

/-- `o.entryPc` is entered by a decoded direct edge from OUTSIDE `o`'s own regions — a real CFG entry
into inlined code (fall-through/branch from the enclosing function instance). -/
def enteredFromOutside (nodes : Array ControlFlowNode) (o : FunctionInstance) : Bool :=
  nodes.any fun n =>
    n.transfer.directTargets.contains o.entryPc && !inRegions o n.word.encoded.address

/-- Every function instance's `entryPc` is a decoded node and the function instance's first-fragment start (its DWARF
entry), NOT a `min/max` guess elsewhere in the ranges. For an INLINED function instance it is additionally
validated as a real CFG entry — control reaches it by a decoded edge from outside the function instance's
regions. (Emitted functions are reached at their `low_pc`; those called only through the allocator
vtable have no decoded direct predecessor — an indirect call carries no direct edge — so the
entered-from-outside check applies to inlined function instances, where it holds for every one.) -/
def entriesValid (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  program.functionInstances.all fun o =>
    hasControlFlowAddress nodes o.entryPc &&
    decide (o.entryPc = minRegionStart o) &&
    (o.id.inlineStack.isEmpty || enteredFromOutside nodes o)

/-- The `exitPcs` are EXACTLY the function instance's decoded control-transfer-out points: every listed exit
lies in the regions and really leaves, and every region PC that leaves is listed. This is the "all
exits, no `max(endpoint)`" check. -/
def exitsValid (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  program.functionInstances.all fun o =>
    (o.exitPcs.all fun pc => inRegions o pc && leavesFunctionInstance nodes o pc) &&
    o.regions.all fun r => (List.range (r.size / 4)).all fun k =>
      let pc := r.start + 4 * k
      !leavesFunctionInstance nodes o pc || o.exitPcs.contains pc

/-- Every emitted direct edge is a real decoded direct successor of an in-region source
(soundness: no invented edge). -/
def edgesValid (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  program.functionInstances.all fun o =>
    o.edges.all fun e =>
      inRegions o e.source && (directSuccessorsAt nodes e.source).contains e.target

/-- The REVERSE inclusion of `edgesValid` (completeness: no dropped edge). For every function instance, every
region PC it DEEPEST-owns, and every decoded direct successor `t` of that PC, the edge
`{ source := pc, target := t }` occurs in the function instance's emitted edge list. Together with `edgesValid`
this pins `o.edges` to EXACTLY the decoded direct-successor edges out of the PCs `o` owns, so the
untrusted artifact cannot silently drop a real edge and still validate. -/
def edgesComplete (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  program.functionInstances.all fun o =>
    o.regions.all fun r => (List.range (r.size / 4)).all fun k =>
      let pc := r.start + 4 * k
      !ownedBy program o pc ||
        (directSuccessorsAt nodes pc).all fun t =>
          o.edges.any fun e => e.source == pc && e.target == t

/-- External calls correspond to the decoded direct calls: every emitted callee resolves to a
generated function instance and is the target of a real decoded direct call out of `o`, and every decoded
direct call `o` DEEPEST-owns is emitted — so calls are neither invented nor dropped. -/
def externalCallsValid (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  let dce := directCallEdges nodes
  program.functionInstances.all fun o =>
    (o.externalCalls.all fun id =>
      match calleeEntryPc? program id with
      | some target => dce.any fun ce => inRegions o ce.source && ce.target == target
      | none => false) &&
    dce.all fun ce =>
      !ownedBy program o ce.source ||
      o.externalCalls.any fun id => calleeEntryPc? program id == some ce.target

/-- Basic blocks exactly partition each function instance's regions: each block is contained in a region, the
blocks are pairwise disjoint, the regions are pairwise disjoint, and the blocks' total size equals the
regions' — so together they cover every region PC exactly once, with no gap and no overlap. -/
def blocksPartition (program : Program) : Bool :=
  program.functionInstances.all fun o =>
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

/-- All CFG-interface checks for an arbitrary `program`, dispatched through `controlFlow?` (so a
parse/decode failure is `false`). Uses `Option.map`/`getD` rather than a `match`, so the kernel bridge
never reduces the ~3984-word decode (same reason as the reachability certificate). Parameterising over
`program` lets the negative test run the SAME validation against a tampered program. -/
def cfgInterfaceValidFor (program : Program) : Bool :=
  (controlFlow?.map fun nodes =>
    regionsDecoded nodes program &&
    entriesValid nodes program &&
    exitsValid nodes program &&
    edgesValid nodes program &&
    edgesComplete nodes program &&
    externalCallsValid nodes program &&
    blocksPartition program).getD false

/-- The CFG-interface validation applied to the actual generated program. -/
def cfgInterfaceValidC : Bool := cfgInterfaceValidFor generatedProgram

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
    regionsDecoded nodes generatedProgram = true ∧
    entriesValid nodes generatedProgram = true ∧
    exitsValid nodes generatedProgram = true ∧
    edgesValid nodes generatedProgram = true ∧
    edgesComplete nodes generatedProgram = true ∧
    externalCallsValid nodes generatedProgram = true ∧
    blocksPartition generatedProgram = true := by
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
      regionsDecoded nodes generatedProgram = true ∧
      entriesValid nodes generatedProgram = true ∧
      exitsValid nodes generatedProgram = true ∧
      edgesValid nodes generatedProgram = true ∧
      edgesComplete nodes generatedProgram = true ∧
      externalCallsValid nodes generatedProgram = true ∧
      blocksPartition generatedProgram = true := by
  obtain ⟨nodes, hn⟩ := controlFlow_isSome
  exact ⟨nodes, hn, cfgInterfaceValid_some hn⟩

/-! ## Reverse edge inclusion as a proposition, and its negative test -/

/-- **Every decoded direct successor of every deepest-owned PC is an emitted edge** (the reverse
inclusion, in proposition form). For every function instance `o`, every region PC `pc := r.start + 4 * k` it
deepest-owns, and every decoded direct successor `t` of `pc`, the edge `{ source := pc, target := t }`
is present in `o.edges`. This is the `Prop` companion of the `edgesComplete` clause of the certificate:
the generated edge inventory is a COMPLETE certificate of the decoded successor relation, not merely a
sound one. -/
theorem edgesComplete_holds {nodes : Array ControlFlowNode}
    (hn : controlFlow? = some nodes) :
    ∀ o ∈ generatedProgram.functionInstances, ∀ r ∈ o.regions, ∀ k, k < r.size / 4 →
      ownedBy generatedProgram o (r.start + 4 * k) = true →
        ∀ t ∈ directSuccessorsAt nodes (r.start + 4 * k),
          (o.edges.any fun e => e.source == r.start + 4 * k && e.target == t) = true := by
  have hcomplete := (cfgInterfaceValid_some hn).2.2.2.2.1
  intro o ho r hr k hk hown t ht
  have h1 := forall_mem_of_all hcomplete o ho
  have h2 := forall_mem_of_all h1 r hr
  have h3 := forall_mem_of_all_list h2 k (List.mem_range.mpr hk)
  simp only [hown, Bool.not_true, Bool.false_or] at h3
  exact forall_mem_of_all h3 t ht

/-! ### Negative test: dropping one real non-call edge breaks completeness

The reverse inclusion has teeth only if omitting a real edge is actually rejected. `0x10250 → 0x10254`
(decimal `66128 → 66132`) is a straight-line fall-through step inside a single basic block of the
`zesu_raw_alloc` function instance (function instance 0) — a single decoded successor, so it is NOT a call. Deleting it from
the generated artifact must make `edgesComplete` (and hence the whole CFG-interface validation) fail. -/

/-- The concrete non-call edge the negative test deletes. -/
def droppedEdge : DirectEdge := { source := 66128, target := 66132 }

/-- The dropped edge really is one the generator emitted, so the tamper removes something real. -/
theorem droppedEdge_present :
    (generatedProgram.functionInstances.any fun o => o.edges.any fun e => decide (e = droppedEdge)) = true := by
  native_decide

/-- `generatedProgram` with `droppedEdge` deleted from wherever it was emitted: a hand-tampered
artifact that silently drops one real non-call edge. -/
def edgeDroppedProgram : Program :=
  { generatedProgram with
    functionInstances := generatedProgram.functionInstances.map fun o =>
      { o with edges := o.edges.filter fun e => decide (e ≠ droppedEdge) } }

/-- **Completeness is not vacuous.** With one real non-call edge dropped, the reverse-inclusion check
fails: the omitted decoded successor is detected. -/
theorem edgeDropped_incomplete :
    (controlFlow?.map fun nodes => edgesComplete nodes edgeDroppedProgram).getD true = false := by
  native_decide

/-- **The whole CFG-interface validation rejects the tampered program** — dropping a single generated
non-call edge is caught, so the emitted edge list is enforced as a complete certificate. -/
theorem edgeDropped_cfgInterface_invalid : cfgInterfaceValidFor edgeDroppedProgram = false := by
  native_decide

/-! ## The exit rule earns its purpose: reachable exits, and call sites that are not exits

`exitsValid` pins `exitPcs` to the transfer-out points of `leavesFunctionInstance` in both directions,
but a rule can be pinned faithfully and still be the WRONG rule — the correspondence check is a
statement about the generator agreeing with this module, not about either being right. Two further
things must hold, and neither follows from the correspondence:

* **a resolved call site is not an exit of its caller.** `FunctionTrace.step` carries `¬ exit pc`, so
  an exit at every call site stops each caller's trace at its first call, before it has written
  anything its postcondition talks about; `CallTransfer.callNotExit` becomes unsatisfiable and
  `ScopedTrace.callStep` dead code. That is exactly what the old rule did: it treated a resolved
  call's callee edge as a continuation, making all **180** call rows exits.
* **every function instance can actually reach one of its declared exits.** Otherwise the exit
  predicate a `FunctionTrace` runs against is unsatisfiable and the local obligation is not vacuous
  but unprovable — the opposite failure, and no better.

The two pull against each other, which is why the fix is the fall-through test and not a blanket
"calls are never exits": that naive rule strands the `readArray` instance at `0x10fbc`, whose only
transfer out of its own regions IS a tail call. Both facts are decided below, and the naive rule is
run as a mutant so the reachability check is known to be capable of failing. -/

/-- `pc` decodes to a RESOLVED direct call — the sites `CallSite`/`CallTransfer` are built at. -/
def isResolvedCallAt (nodes : Array ControlFlowNode) (pc : Nat) : Bool :=
  match ControlFlowNodeAt? nodes pc with
  | some n => match n.transfer with
              | .call (some _) _ _ => true
              | _ => false
  | none => false

/-- Every region PC of a function instance, in address order. -/
def regionPcList (o : FunctionInstance) : List Nat :=
  o.regions.foldl (fun acc r => acc ++ (List.range (r.size / 4)).map fun k => r.start + 4 * k) []

/-- Resolved-call ROWS: one per (function instance, region pc) at which the artifact makes a resolved
direct call. A pc inside an inlined child is counted once for the child and once for each enclosing
instance, which is the granularity `callNotExit` is discharged at. -/
def callRows (nodes : Array ControlFlowNode) (program : Program) : Nat :=
  program.functionInstances.foldl
    (fun n o => n + ((regionPcList o).filter fun pc => isResolvedCallAt nodes pc).length) 0

/-- The call rows whose calling function instance does NOT declare them an exit — the rows at which
`CallTransfer.callNotExit` is satisfiable. -/
def nonExitCallRows (nodes : Array ControlFlowNode) (program : Program) : Nat :=
  program.functionInstances.foldl
    (fun n o => n + ((regionPcList o).filter fun pc =>
      isResolvedCallAt nodes pc && !o.exitPcs.contains pc).length) 0

/-- **`callNotExit` is satisfiable at 173 of the artifact's 180 resolved-call rows.** Under the old
exit rule the second number was 0 and `ScopedTrace.callStep` was dead against this artifact. The
seven that remain exits are tail-position calls, whose fall-through really does leave the caller. -/
theorem generated_call_rows :
    ∀ nodes, controlFlow? = some nodes →
      callRows nodes generatedProgram = 180 ∧ nonExitCallRows nodes generatedProgram = 173 := by
  intro nodes hn
  have h : (controlFlow?.map fun ns =>
      (callRows ns generatedProgram == 180) && (nonExitCallRows ns generatedProgram == 173)).getD
      false = true := by native_decide
  rw [hn] at h
  simp only [Option.map_some, Option.getD_some, Bool.and_eq_true, beq_iff_eq] at h
  exact h

/-- `FunctionInstance.isExit` is the `Prop` the trace machinery runs against; the checks above speak
`Array.contains`. This is the bridge, in the direction the satisfiability witness needs. -/
theorem not_isExit_of_contains_false {o : FunctionInstance} {a : Nat}
    (h : o.exitPcs.contains a = false) : ¬ o.isExit a := by
  simp only [FunctionInstance.isExit, ← Array.contains_iff_mem, h, Bool.false_eq_true,
    not_false_eq_true]

/-- The entry identity resolves, so the witness below is not a statement about nothing. -/
theorem entry_function_instance_resolves :
    (Program.find? generatedProgram generatedProgram.entry).isSome = true := by native_decide

/-- **The concrete witness `CallTransfer.callNotExit` was missing.** The entry function instance
`zesu_decode_raw` makes a resolved call at `0x1031c` (decimal `66332`), inside its own regions, and
that pc is NOT one of its exits. Under the old rule it *was* one — the first of six — so the entry's
`FunctionTrace` halted there, with `status` and `storedResult` still unwritten, and every clause of
`postZesuDecodeRaw` was assumed at a state that could not satisfy it. -/
theorem entry_call_site_is_not_an_exit :
    ∀ nodes, controlFlow? = some nodes →
      ∀ entry, Program.find? generatedProgram generatedProgram.entry = some entry →
        inRegions entry 66332 = true ∧ isResolvedCallAt nodes 66332 = true ∧
          entry.exitPcs.contains 66332 = false ∧ ¬ entry.isExit 66332 := by
  intro nodes hn entry he
  have h : (controlFlow?.map fun ns =>
      ((Program.find? generatedProgram generatedProgram.entry).map fun e =>
        inRegions e 66332 && isResolvedCallAt ns 66332 && !e.exitPcs.contains 66332).getD
        false).getD false = true := by native_decide
  rw [hn, he] at h
  simp only [Option.map_some, Option.getD_some, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2, not_isExit_of_contains_false h.2⟩

/-! ### Every function instance can still reach an exit -/

/-- One pop of the in-instance frontier: stop at a declared exit, otherwise push the in-region
continuations not yet seen. `fuel` bounds the pops, and every pc enters the frontier at most once, so
the instance's region pc count is enough. -/
def reachesExitAux (nodes : Array ControlFlowNode) (o : FunctionInstance) :
    Nat → List Nat → Array Nat → Bool
  | 0, _, _ => false
  | _ + 1, [], _ => false
  | fuel + 1, pc :: rest, seen =>
    if o.exitPcs.contains pc then true
    else
      match ControlFlowNodeAt? nodes pc with
      | none => reachesExitAux nodes o fuel rest seen
      | some n =>
        let next := (exitContinuations n.transfer).foldl
          (fun acc t =>
            if inRegions o t && !seen.contains t && !acc.contains t then acc.push t else acc) #[]
        reachesExitAux nodes o fuel (rest ++ next.toList) (seen ++ next)

/-- **Some declared exit of `o` is reachable from its entry**, walking only continuations that stay
inside `o`'s regions and halting at every declared exit — the walk a `FunctionTrace` for `o` performs.
An instance for which this is `false` has an unsatisfiable exit predicate: its trace obligation would
be unprovable rather than merely unproved. -/
def reachesAnExit (nodes : Array ControlFlowNode) (o : FunctionInstance) : Bool :=
  reachesExitAux nodes o (o.coveredBytes / 4 + 1) [o.entryPc] #[o.entryPc]

def everyFunctionInstanceReachesAnExit (nodes : Array ControlFlowNode) (program : Program) : Bool :=
  program.functionInstances.all fun o => reachesAnExit nodes o

/-- **No function instance is stranded.** All 141 reach a declared exit from their entry, so narrowing
the exit rule bought non-vacuity without buying unprovability. -/
theorem generated_every_function_instance_reaches_an_exit :
    ∀ nodes, controlFlow? = some nodes →
      everyFunctionInstanceReachesAnExit nodes generatedProgram = true := by
  intro nodes hn
  have h : (controlFlow?.map fun ns =>
      everyFunctionInstanceReachesAnExit ns generatedProgram).getD false = true := by native_decide
  rw [hn] at h; simpa using h

/-- The naive repair this fix did NOT adopt: drop EVERY resolved call site from the exit inventories
instead of testing its fall-through. -/
def programWithoutCallExits (nodes : Array ControlFlowNode) : Program :=
  { generatedProgram with
    functionInstances := generatedProgram.functionInstances.map fun o =>
      { o with exitPcs := o.exitPcs.filter fun pc => !isResolvedCallAt nodes pc } }

/-- **The reachability check can fail, and the naive rule is what makes it fail.** Dropping every call
site from the exit inventories strands exactly one function instance — the `readArray` instance
entered at `0x10fbc` (decimal `69564`), 24 bytes whose single transfer out is the tail call at
`0x10fd0`. Naming the instance rather than only counting is deliberate: it is the witness that the
fall-through test in the generator's exit rule is load-bearing and not decoration. -/
theorem naive_call_exit_removal_strands_readArray :
    (controlFlow?.map fun nodes =>
      ((programWithoutCallExits nodes).functionInstances.filter fun o =>
        !reachesAnExit nodes o).map (fun o => o.entryPc)).getD #[] = #[69564] := by
  native_decide

/-! ### `exitsValid` rejects both wrong rules

The rule is *enforced* rather than merely *applied*: both neighbouring inventories — the one the
generator used to emit, and the naive repair — are rejected by the correspondence check itself, each
by a different half of it. -/

/-- The OLD exit rule, reconstructed on top of the current data: every resolved call site inside a
function instance's regions declared an exit of it. -/
def programWithAllCallExits (nodes : Array ControlFlowNode) : Program :=
  { generatedProgram with
    functionInstances := generatedProgram.functionInstances.map fun o =>
      { o with exitPcs :=
          (regionPcList o).foldl (fun acc pc =>
            if isResolvedCallAt nodes pc && !acc.contains pc then acc.push pc else acc) o.exitPcs } }

/-- **The old inventory is rejected.** A non-tail call site does not leave its caller — control comes
back to `pc + 4`, in region — so declaring it an exit fails the "every listed exit really leaves"
half of `exitsValid`. -/
theorem old_call_exit_inventory_is_rejected :
    (controlFlow?.map fun nodes => exitsValid nodes (programWithAllCallExits nodes)).getD true
      = false := by native_decide

/-- **The naive removal is rejected too, by the other half.** A tail call's fall-through really does
leave the regions, so dropping the 7 tail-position call exits fails "every leaving PC is listed".
With the theorem above, `exitsValid` pins the fall-through test itself and not either extreme. -/
theorem naive_call_exit_removal_is_rejected :
    (controlFlow?.map fun nodes => exitsValid nodes (programWithoutCallExits nodes)).getD true
      = false := by native_decide

end BinaryFv.Zesu.Elflings.Validation
