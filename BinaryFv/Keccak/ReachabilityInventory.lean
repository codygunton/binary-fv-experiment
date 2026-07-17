import BinaryFv.Keccak.Decode
import BinaryFv.RiscV.Analysis.Reachability

/-!
# The pinned artifact's static reachability results

Reth inputs to, and computed results of, `BinaryFv.RiscV.Analysis.Reachability`. The closed facts
here use `native_decide` under the approved fixed-artifact exception.
-/

namespace BinaryFv.Keccak

open BinaryFv.RiscV
open LeanRV64DExecutable.Functions

def entryStaticDirectReachabilityInventory? : Option StaticDirectReachabilityInventory :=
  match Artifact.entryAddress, artifactControlFlow? with
  | .ok entry, some nodes => some (staticDirectReachabilityInventory nodes entry)
  | _, _ => none
def entryStaticDirectReachabilityInventoryWellFormed : Bool :=
  match entryStaticDirectReachabilityInventory? with
  | some inventory =>
    inventory.directEdgesStayWithinInventory && inventory.addressesHaveInventoriedNodes
  | none => false
/--
Diagnostic frontier queries. They deliberately have no artifact-specific existence theorem: a
frontier's presence is not an invariant needed by the later proof stack.
-/
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
/--
Closed parser-owned inventory fact: the inventory exists, every direct successor remains inside it,
and every retained address has a decoded node. This is not a generated-Sail execution theorem.
-/
theorem entry_static_direct_reachability_inventory_well_formed :
    entryStaticDirectReachabilityInventoryWellFormed = true := by
  native_decide

end BinaryFv.Keccak
