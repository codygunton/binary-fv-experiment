import BinaryFv.Keccak.Decode

namespace BinaryFv.Keccak

open BinaryFv.RISCV
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

def entryStaticDirectReachabilityInventory? : Option StaticDirectReachabilityInventory :=
  match Artifact.entryAddress, artifactControlFlow? with
  | .ok entry, some nodes => some (staticDirectReachabilityInventory nodes entry)
  | _, _ => none

def entryStaticDirectReachabilityInventoryAvailable : Bool :=
  entryStaticDirectReachabilityInventory?.isSome

def entryStaticDirectReachabilityDirectEdgesStayWithinInventory : Bool :=
  match entryStaticDirectReachabilityInventory? with
  | some inventory => inventory.directEdgesStayWithinInventory
  | none => false

def entryStaticDirectReachabilityAddressesHaveInventoriedNodes : Bool :=
  match entryStaticDirectReachabilityInventory? with
  | some inventory => inventory.addressesHaveInventoriedNodes
  | none => false

def entryStaticDirectReachabilityHasIndirectTransferBoundary : Bool :=
  match entryStaticDirectReachabilityInventory? with
  | some inventory => inventory.hasBoundary StaticDirectReachabilityBoundary.isIndirectTransfer
  | none => false

def entryStaticDirectReachabilityHasIndirectCallBoundary : Bool :=
  match entryStaticDirectReachabilityInventory? with
  | some inventory => inventory.hasBoundary StaticDirectReachabilityBoundary.isIndirectCall
  | none => false

def entryStaticDirectReachabilityHasReturnBoundary : Bool :=
  match entryStaticDirectReachabilityInventory? with
  | some inventory => inventory.hasBoundary StaticDirectReachabilityBoundary.isReturn
  | none => false

/-- Closed parser-owned availability fact, not a generated-Sail execution theorem. -/
theorem entry_static_direct_reachability_inventory_available :
    entryStaticDirectReachabilityInventoryAvailable = true := by
  native_decide

/-- Closed static-edge fact: every inventoried direct successor is another inventoried node. -/
theorem entry_static_direct_reachability_direct_edges_stay_within_inventory :
    entryStaticDirectReachabilityDirectEdgesStayWithinInventory = true := by
  native_decide

/-- Closed static coverage fact: every direct-reachable address retains its decoded node. -/
theorem entry_static_direct_reachability_addresses_have_inventoried_nodes :
    entryStaticDirectReachabilityAddressesHaveInventoriedNodes = true := by
  native_decide

/-- Closed static frontier fact; it does not resolve the runtime target. -/
theorem entry_static_direct_reachability_has_indirect_transfer_boundary :
    entryStaticDirectReachabilityHasIndirectTransferBoundary = true := by
  native_decide

/-- Closed static frontier fact; it does not resolve the runtime target or call result. -/
theorem entry_static_direct_reachability_has_indirect_call_boundary :
    entryStaticDirectReachabilityHasIndirectCallBoundary = true := by
  native_decide

/-- Closed static frontier fact; it does not establish dynamic return pairing or a return value. -/
theorem entry_static_direct_reachability_has_return_boundary :
    entryStaticDirectReachabilityHasReturnBoundary = true := by
  native_decide

end BinaryFv.Keccak
