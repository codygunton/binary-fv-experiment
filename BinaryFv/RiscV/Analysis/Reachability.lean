import BinaryFv.RiscV.ELF.CFG

/-!
# Static direct reachability

The direct-edge inventory of a decoded control-flow graph, and the boundaries (indirect transfer,
indirect call, return) at which purely-syntactic direct reachability stops.

Parameterized by `(nodes : Array ControlFlowNode)`. Which nodes a binary has, and whether its
inventory is well-formed, are target facts.
-/

namespace BinaryFv.RiscV

open LeanRV64DExecutable.Functions

/--
A static boundary intentionally not traversed by `directReachable`. A resolved direct call still
contributes its callee and return-address summary edges; this does not establish call/return
semantics or generated-Sail execution.
-/
inductive StaticDirectReachabilityBoundaryKind where
  | unresolvedConditionalTarget (notTaken : Nat)
  | unresolvedJumpTarget
  | unresolvedDirectCallTarget (returnAddress : Nat) (link : regidx)
  | indirectTransfer
  | indirectCall (returnAddress : Nat) (link : regidx)
  | return_ (link : regidx)
  | terminal
  deriving Repr

structure StaticDirectReachabilityBoundary where
  address : Nat
  kind : StaticDirectReachabilityBoundaryKind
  deriving Repr

def staticDirectReachabilityBoundary? (node : ControlFlowNode) :
    Option StaticDirectReachabilityBoundaryKind :=
  match node.transfer with
  | .conditional none notTaken => some (.unresolvedConditionalTarget notTaken)
  | .jump none => some .unresolvedJumpTarget
  | .call none returnAddress link => some (.unresolvedDirectCallTarget returnAddress link)
  | .indirect => some .indirectTransfer
  | .indirectCall returnAddress link => some (.indirectCall returnAddress link)
  | .return_ link => some (.return_ link)
  | .terminal => some .terminal
  | _ => none

def staticDirectReachabilityBoundaries (nodes : Array ControlFlowNode) :
    Array StaticDirectReachabilityBoundary :=
  nodes.foldl (fun boundaries node =>
    match staticDirectReachabilityBoundary? node with
    | some kind => boundaries.push { address := node.word.encoded.address, kind }
    | none => boundaries) #[]

/--
The parser-owned, static direct-edge inventory from one entry. `nodes` retains each decoded
instruction, `directEdges` retains every decoded direct successor, and `boundaries` retains every
unresolved, indirect, return, or terminal case. It makes no generated-Sail reachability claim.
-/
structure StaticDirectReachabilityInventory where
  addresses : Array Nat
  nodes : Array ControlFlowNode
  directEdges : Array DirectControlEdge
  boundaries : Array StaticDirectReachabilityBoundary
  deriving Repr

def staticDirectReachabilityInventory (nodes : Array ControlFlowNode) (entry : Nat) :
    StaticDirectReachabilityInventory :=
  let addresses := directReachable nodes entry
  let reachableNodes := nodes.filter fun node =>
    addresses.any fun address => address == node.word.encoded.address
  {
    addresses
    nodes := reachableNodes
    directEdges := directControlEdges reachableNodes
    boundaries := staticDirectReachabilityBoundaries reachableNodes
  }

def StaticDirectReachabilityInventory.directEdgesStayWithinInventory
    (inventory : StaticDirectReachabilityInventory) : Bool :=
  inventory.directEdges.all fun edge =>
    inventory.addresses.any fun address => address == edge.target

def StaticDirectReachabilityInventory.addressesHaveInventoriedNodes
    (inventory : StaticDirectReachabilityInventory) : Bool :=
  inventory.addresses.all fun address =>
    inventory.nodes.any fun node => node.word.encoded.address == address

def StaticDirectReachabilityInventory.hasBoundary
    (inventory : StaticDirectReachabilityInventory)
    (predicate : StaticDirectReachabilityBoundary → Bool) : Bool :=
  inventory.boundaries.any predicate

def StaticDirectReachabilityBoundary.isIndirectTransfer :
    StaticDirectReachabilityBoundary → Bool
  | { kind := .indirectTransfer, .. } => true
  | _ => false

def StaticDirectReachabilityBoundary.isIndirectCall : StaticDirectReachabilityBoundary → Bool
  | { kind := .indirectCall _ _, .. } => true
  | _ => false

def StaticDirectReachabilityBoundary.isReturn : StaticDirectReachabilityBoundary → Bool
  | { kind := .return_ _, .. } => true
  | _ => false

/-!
## Reachability over-approximation

`directReachable` is a least-fixpoint search: it seeds with the entry and repeatedly adds decoded
direct successors until closure. These lemmas certify the *forward* direction — any address the
search returns is contained in any set that holds the entry and is closed under
`directSuccessorsAt`. A materialized candidate set can therefore be validated cheaply (entry ∈ set,
set closed) and this lemma turns that into a sound over-approximation of `directReachable` itself,
without ever running the (expensive) fixpoint. The reverse direction (minimality) needs per-address
reachability witnesses and is supplied by the generated certificate instead.
-/

/-- Every element of `appendKnownAddresses` came from `known` or from the appended `candidates`. -/
theorem mem_appendKnownAddresses (nodes : Array ControlFlowNode) (known candidates : Array Nat) :
    ∀ x, x ∈ appendKnownAddresses nodes known candidates → x ∈ known ∨ x ∈ candidates := by
  unfold appendKnownAddresses
  refine Array.foldl_induction
    (motive := fun _ acc => ∀ x, x ∈ acc → x ∈ known ∨ x ∈ candidates) ?base ?step
  · intro x hx; exact Or.inl hx
  · intro i acc ih x hx
    split at hx
    · rcases Array.mem_push.mp hx with h | h
      · exact ih x h
      · exact Or.inr (h ▸ Array.getElem_mem i.isLt)
    · exact ih x hx

/-- Every element of one expansion pass is old, or a decoded direct successor of an old address. -/
theorem mem_expandDirectReachability (nodes : Array ControlFlowNode) (known : Array Nat) :
    ∀ x, x ∈ expandDirectReachability nodes known →
      x ∈ known ∨ ∃ a, a ∈ known ∧ x ∈ directSuccessorsAt nodes a := by
  unfold expandDirectReachability
  refine Array.foldl_induction
    (motive := fun _ acc => ∀ x, x ∈ acc →
      x ∈ known ∨ ∃ a, a ∈ known ∧ x ∈ directSuccessorsAt nodes a) ?base ?step
  · intro x hx; exact Or.inl hx
  · intro i acc ih x hx
    rcases mem_appendKnownAddresses nodes acc (directSuccessorsAt nodes known[i]) x hx with h | h
    · exact ih x h
    · exact Or.inr ⟨known[i], Array.getElem_mem i.isLt, h⟩

/-- A closed superset of `known` stays a superset after one expansion pass. -/
theorem expandDirectReachability_subset (nodes : Array ControlFlowNode) (R : Nat → Prop)
    (hClosed : ∀ a, R a → ∀ t, t ∈ directSuccessorsAt nodes a → R t) (known : Array Nat)
    (hknown : ∀ x, x ∈ known → R x) :
    ∀ x, x ∈ expandDirectReachability nodes known → R x := by
  intro x hx
  rcases mem_expandDirectReachability nodes known x hx with h | ⟨a, ha, ht⟩
  · exact hknown x h
  · exact hClosed a (hknown a ha) x ht

/-- The bounded fixpoint search never leaves a closed superset of its seed. -/
theorem directReachableLoop_subset (nodes : Array ControlFlowNode) (R : Nat → Prop)
    (hClosed : ∀ a, R a → ∀ t, t ∈ directSuccessorsAt nodes a → R t) :
    ∀ fuel known, (∀ x, x ∈ known → R x) →
      ∀ x, x ∈ directReachableLoop nodes fuel known → R x := by
  intro fuel
  induction fuel with
  | zero => intro known hknown x hx; simpa [directReachableLoop] using hknown x hx
  | succ f ih =>
    intro known hknown x hx
    rw [directReachableLoop] at hx
    split at hx
    · exact hknown x hx
    · exact ih _ (expandDirectReachability_subset nodes R hClosed known hknown) x hx

/--
Forward reachability over-approximation: if `R` holds the entry (when the entry is decoded) and is
closed under `directSuccessorsAt`, then `R` contains every address `directReachable` returns.
-/
theorem directReachable_subset (nodes : Array ControlFlowNode) (entry : Nat) (R : Nat → Prop)
    (hClosed : ∀ a, R a → ∀ t, t ∈ directSuccessorsAt nodes a → R t)
    (hEntry : hasControlFlowAddress nodes entry = true → R entry) :
    ∀ x, x ∈ directReachable nodes entry → R x := by
  intro x hx
  unfold directReachable at hx
  split at hx
  · rename_i hcond
    refine directReachableLoop_subset nodes R hClosed (nodes.size + 1) #[entry] ?_ x hx
    intro y hy
    rw [Array.mem_singleton] at hy
    exact hy ▸ hEntry hcond
  · exact absurd hx (Array.not_mem_empty x)

end BinaryFv.RiscV
