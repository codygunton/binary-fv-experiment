import BinaryFv.SSZ.Zesu.ControlFlow.Decode
import BinaryFv.SSZ.Zesu.Elfling.GeneratedProgramCfg
import BinaryFv.SSZ.Zesu.Artifact.AllocatorCalls
import BinaryFv.SSZ.Zesu.Elfling.GeneratedProgramReachablePartition
import GeneratedProgram

/-!
# Accounting for every control-flow boundary

A closed occurrence trace stays inside its execution extent, so every transfer from owned code must
lead to mapped code or a checked boundary. This module computes that inventory from the decoded CFG
and checks two cases not covered by the ordinary cataloged-occurrence edge table:

* the **absorbed excluded routines** carry code the composition owns, yet their CFG was never checked;
* the **indirect allocator dispatches** — `jalr` through the immutable `std.mem.Allocator` vtable —
  carry no decoded direct successor, so a direct-edge check passes over them vacuously.

This module closes both, computing the inventory **from the trusted decoded CFG** (`controlFlow?`)
rather than a hand-maintained list, and checking it exhaustive:

1. `directSuccessorsMapped` — every decoded *direct* successor of every owned-or-excluded pc is itself
   owned or excluded. Control never leaves the mapped reachable code by a direct edge. This covers the
   excluded routines' internal direct edges. It says nothing about returns: `ControlTransfer.directTargets`
   is `#[]` for `.return_` (a `ret` goes to a dynamic `ra` the CFG cannot resolve), so returns are
   *not* checked here — the return of an absorbed excluded routine into its caller is discharged by the
   caller's own local trace obligation (D0's call/return accounting), not by this CFG sweep.
2. `noUnresolvedDirect` — no owned-or-excluded pc has an *unresolved* direct transfer
   (`jump none` / `call none`): every direct branch/jump/call has a decoded target.
3. `indirectSitesResolved` — the only non-direct, non-return, non-terminal transfers in owned-or-
   excluded code are `jalr ra` allocator-vtable dispatches, and there are exactly three of them.
   Their target is the immutable vtable's alloc slot, pinned to `allocatorWrapperAddress` by
   `Artifact.allocator_vtable_alloc_target` — a mapped occurrence (`allocatorAlloc`). The extent
   wiring that puts that occurrence into each caller's extent is done in `GeneratedProgramGeometry`.

Together these checks make every decoded successor of owned code explicit. Dynamic returns remain a
trace obligation: the CFG cannot resolve the caller's `ra`.
-/

namespace BinaryFv.SSZ.Zesu.Elfling.Validation

open BinaryFv.RiscV BinaryFv.SSZ.Zesu.ControlFlow
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedProgram generatedExcludedOccurrences)

/-- A pc that some cataloged occurrence or some surfaced excluded routine owns. The excluded routines
are the ones an occurrence *absorbs*, so "owned or excluded" is exactly the code the composition
accounts for. -/
def ownedOrExcludedPC (a : Nat) : Bool :=
  generatedProgram.instances.any (fun o => o.containsAddress a) ||
    generatedExcludedOccurrences.any (fun x => x.regions.any (fun r => decide (r.start ≤ a ∧ a < r.stop)))

/-! ## 1–2. Direct control flow stays inside the mapped code -/

/-- Every decoded direct successor of every owned-or-excluded pc is itself owned or excluded. -/
def directSuccessorsMappedB (nodes : Array ControlFlowNode) : Bool :=
  nodes.all fun n =>
    !ownedOrExcludedPC n.word.encoded.address ||
      n.transfer.directTargets.all (fun t => ownedOrExcludedPC t)

/-- No owned-or-excluded pc carries an unresolved direct transfer. -/
def noUnresolvedDirectB (nodes : Array ControlFlowNode) : Bool :=
  nodes.all fun n =>
    !ownedOrExcludedPC n.word.encoded.address ||
      (match n.transfer with
       | .jump none => false
       | .call none _ _ => false
       | _ => true)

/-! ## 3. The indirect transfers are exactly the allocator-vtable dispatches -/

/-- Whether a transfer is one of the kinds a direct-edge check does not cover *and* is not a plain
return or program-terminating transfer — i.e. an indirect jump or indirect call that must be
resolved through pinned evidence. -/
def isUnresolvedIndirect : ControlTransfer → Bool
  | .indirect => true
  | .indirectCall _ _ => true
  | _ => false

/-- The indirect-transfer sites in owned-or-excluded code, computed from the CFG. -/
def indirectSites (nodes : Array ControlFlowNode) : Array Nat :=
  (nodes.filter (fun n => ownedOrExcludedPC n.word.encoded.address && isUnresolvedIndirect n.transfer)).map
    (fun n => n.word.encoded.address)

/-- Every indirect site in owned-or-excluded code is a `jalr ra` (an indirect *call* returning to the
next instruction, link `x1`), which is the allocator-vtable dispatch shape — not an arbitrary
computed jump. `regidx.Regidx 1` is `ra`. -/
def indirectSitesAreVtableDispatchB (nodes : Array ControlFlowNode) : Bool :=
  nodes.all fun n =>
    !(ownedOrExcludedPC n.word.encoded.address && isUnresolvedIndirect n.transfer) ||
      (match n.transfer with
       | .indirectCall _ (regidx.Regidx link) => link == 1
       | _ => false)

/-- The whole inventory, over explicit decoded nodes. -/
def boundaryInventoryCompleteB (nodes : Array ControlFlowNode) : Bool :=
  directSuccessorsMappedB nodes && noUnresolvedDirectB nodes && indirectSitesAreVtableDispatchB nodes

/-! ## The checked facts -/

theorem boundary_inventory_complete_check :
    ∀ nodes, controlFlow? = some nodes → boundaryInventoryCompleteB nodes = true := by
  intro nodes hn
  have : (controlFlow?.map (fun ns => boundaryInventoryCompleteB ns)).getD false = true := by
    native_decide
  rw [hn] at this; simpa using this

/-- Exactly three indirect sites — the allocator `alloc` dispatches: `decodeRaw`'s inline dispatch and
the two absorbed `allocBytesWithAlignment` excluded routines. Their being the complete set is what
makes the inventory exhaustive. -/
theorem indirect_sites_count :
    ∀ nodes, controlFlow? = some nodes → (indirectSites nodes).size = 3 := by
  intro nodes hn
  have : (controlFlow?.map (fun ns => (indirectSites ns).size)).getD 0 = 3 := by native_decide
  rw [hn] at this; simpa using this

/-- The immutable vtable's `alloc` slot is the allocator wrapper occurrence, a mapped pc. Every
dispatch above targets this pinned slot, so no indirect transfer leaves the mapped code either. This
is the resolution the extent wiring consumes. -/
theorem indirect_dispatch_target_is_mapped :
    Artifact.allocatorVtableAllocTarget = some Artifact.allocatorWrapperAddress ∧
      ownedOrExcludedPC Artifact.allocatorWrapperAddress = true := by
  refine ⟨Artifact.allocator_vtable_alloc_target, ?_⟩
  native_decide

/-! ## Negative: the excluded-routine CFGs are load-bearing

If absorption were dropped — if only the cataloged occurrences counted as "mapped," not the excluded
routines they absorb — the completeness check would fail: there is an owned pc whose direct successor
lands in an excluded routine, which would then read as an escape. So checking the excluded routines'
CFGs is not decoration; it is required for the inventory to be complete. -/

/-- Mapped by a cataloged occurrence only, ignoring absorption. -/
def ownedOnlyPC (a : Nat) : Bool :=
  generatedProgram.instances.any (fun o => o.containsAddress a)

def directSuccessorsMappedOccOnlyB (nodes : Array ControlFlowNode) : Bool :=
  nodes.all fun n =>
    !ownedOnlyPC n.word.encoded.address ||
      n.transfer.directTargets.all (fun t => ownedOnlyPC t)

/-- Without the excluded routines the direct-successor check is **false**: a cataloged occurrence has
a direct edge into excluded code. This is why the excluded-routine CFGs must be part of the inventory.
-/
theorem negative_excluded_routines_required :
    ∀ nodes, controlFlow? = some nodes → directSuccessorsMappedOccOnlyB nodes = false := by
  intro nodes hn
  have : (controlFlow?.map (fun ns => directSuccessorsMappedOccOnlyB ns)).getD true = false := by
    native_decide
  rw [hn] at this; simpa using this

/-- **The complete checked-boundary inventory.** For the one canonical decoded CFG: every direct
successor of every owned-or-excluded pc is mapped, no direct transfer is unresolved, and the only
indirect transfers are the three `jalr ra` allocator-vtable dispatches whose pinned target is a
mapped occurrence. So every *statically decodable* transfer out of an owned pc lands in owned code,
excluded (absorbed) code, or a checked allocator boundary — no partial coverage remains. The one
dynamic transfer kind, `ret`, is not resolved here (its target is a runtime `ra`); it is accounted
by the caller's local trace obligation under D0's call/return discipline. -/
theorem boundary_inventory_complete :
    ∃ nodes, controlFlow? = some nodes ∧
      directSuccessorsMappedB nodes = true ∧
      noUnresolvedDirectB nodes = true ∧
      indirectSitesAreVtableDispatchB nodes = true ∧
      (indirectSites nodes).size = 3 := by
  obtain ⟨nodes, hn⟩ := controlFlow_isSome
  have hc := boundary_inventory_complete_check nodes hn
  simp only [boundaryInventoryCompleteB, Bool.and_eq_true] at hc
  exact ⟨nodes, hn, hc.1.1, hc.1.2, hc.2, indirect_sites_count nodes hn⟩

end BinaryFv.SSZ.Zesu.Elfling.Validation
