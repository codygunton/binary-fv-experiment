import BinaryFv.SSZ.Zesu.ControlFlow.FunctionWords
import BinaryFv.RiscV.Analysis.Reachability

namespace BinaryFv.SSZ.Zesu.ControlFlow

open BinaryFv.RiscV

def entryStaticDirectReachabilityInventory? : Option StaticDirectReachabilityInventory := do
  let entry ← entryFunction?
  let nodes ← controlFlow?
  pure (staticDirectReachabilityInventory nodes entry.value)

def entryStaticDirectReachabilityInventoryWellFormed : Bool :=
  match entryStaticDirectReachabilityInventory? with
  | some inventory => inventory.directEdgesStayWithinInventory && inventory.addressesHaveInventoriedNodes
  | none => false

theorem entry_static_direct_reachability_inventory_well_formed :
    entryStaticDirectReachabilityInventoryWellFormed = true := by
  native_decide

end BinaryFv.SSZ.Zesu.ControlFlow
