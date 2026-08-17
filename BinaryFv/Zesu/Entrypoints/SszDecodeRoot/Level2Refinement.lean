import BinaryFv.Zesu.MachineExecution.Level1DecodeInputSteps
import BinaryFv.Zesu.MachineExecution.Level1WriteContracts
import BinaryFv.Zesu.MachineExecution.Level1WriteSuccessSteps
import BinaryFv.Zesu.MachineExecution.Level2RuntimeLeaves

/-!
# Level 2 to Level 1 refinement

This module is the explicit edge from the selected Level 2 contracts to the six immediate Level 1
contracts consumed by the exported endpoint proof. Parent-owned instructions and the four closed
leaves are supplied here rather than retained in `Level2ContractAssumptions`.
-/

namespace BinaryFv.Zesu

/-- Resolve every selected Level 2 contract into the six immediate Level 1 contracts. -/
theorem level1Contracts_of_level2
    (hLevel2 : Level2ContractAssumptions) : Level1ContractAssumptions := by
  refine {
    readInput := MachineExecution.readInputInstanceContract
    zkvmExit := MachineExecution.zkvmExitInstanceContract
    allocatorGet := MachineExecution.allocatorGetInstanceContract
    sszDecode := MachineExecution.decodeInstanceContract_of_level2 hLevel2.sszDecode
    writeSuccess := MachineExecution.writeSuccessInstanceContract_of_level2 hLevel2
    writeFailure := MachineExecution.writeFailureInstanceContract_of_level2
      hLevel2.writeFailureRecord }

end BinaryFv.Zesu
