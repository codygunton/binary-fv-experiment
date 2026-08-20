import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.MemcpyProof
import BinaryFv.Zesu.MachineExecution.Level0MainSteps
import BinaryFv.RiscV.Elfling.Seg
import BinaryFv.Zesu.DecodedValue.Representation
import BinaryFv.Option

/-! Compile-time checks for declarations named by the hLevel3 guidance catalogue. -/

#check BinaryFv.Zesu.MachineExecution.ExactInstructionSite
#check BinaryFv.RiscV.ConfiguredMachinePre.decodeContext
#check BinaryFv.RiscV.ConfiguredMachinePre.storeDecodeContext
#check BinaryFv.Zesu.MachineExecution.configuredRegisterWriteStep
#check BinaryFv.Zesu.MachineExecution.configuredDwordLoadStep
#check BinaryFv.Zesu.MachineExecution.configuredDwordStoreStep
#check BinaryFv.Zesu.MachineExecution.configuredJStep
#check BinaryFv.Zesu.MachineExecution.configuredRetStep
#check BinaryFv.Zesu.configuredAuipcStep
#check BinaryFv.Zesu.configuredJalrCallStep
#check BinaryFv.RiscV.Seg.step
#check BinaryFv.RiscV.Seg.stepStore
#check BinaryFv.RiscV.Seg.stepJump
#check BinaryFv.RiscV.Seg.forget
#check BinaryFv.RiscV.WritesOnlyRegs.get
#check BinaryFv.RiscV.WritesOnlyWithin
#check BinaryFv.Zesu.BytesRep.of_writesOnlyWithin
#check BinaryFv.Zesu.ByteWindowRelocation.atOffset
#check BinaryFv.Option.getD_map_of_eq_some
