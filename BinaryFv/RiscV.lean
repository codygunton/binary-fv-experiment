import BinaryFv.RiscV.Address
import BinaryFv.RiscV.BTypeFrame
import BinaryFv.RiscV.BlockStep
import BinaryFv.RiscV.CFG
import BinaryFv.RiscV.ClintFrame
import BinaryFv.RiscV.ControlDispatchFrame
import BinaryFv.RiscV.ControlFlowStep
import BinaryFv.RiscV.Decode
import BinaryFv.RiscV.DecodeFrame
import BinaryFv.RiscV.Elf64
import BinaryFv.RiscV.EnabledFrame
import BinaryFv.RiscV.ExecuteContract
import BinaryFv.RiscV.FenceFrame
import BinaryFv.RiscV.FetchContract
import BinaryFv.RiscV.FetchMemoryContract
import BinaryFv.RiscV.FetchMmioContract
import BinaryFv.RiscV.FetchMmioLayout
import BinaryFv.RiscV.Framing
import BinaryFv.RiscV.HartContract
import BinaryFv.RiscV.HartPrimitives
import BinaryFv.RiscV.HtifFrame
import BinaryFv.RiscV.ITypeFrame
import BinaryFv.RiscV.InstructionContracts
import BinaryFv.RiscV.IntegerDispatchFrame
import BinaryFv.RiscV.JalFrame
import BinaryFv.RiscV.LoadExecuteContract
import BinaryFv.RiscV.LoadFrame
import BinaryFv.RiscV.Machine
import BinaryFv.RiscV.MulDivFrame
import BinaryFv.RiscV.PhysicalAccessContract
import BinaryFv.RiscV.PmpContract
import BinaryFv.RiscV.PostludePrimitives
import BinaryFv.RiscV.ProgramImage
import BinaryFv.RiscV.RTypeFrame
import BinaryFv.RiscV.ReadFrame
import BinaryFv.RiscV.RegisterFrame
import BinaryFv.RiscV.RegisterOpExecuteContract
import BinaryFv.RiscV.SailEnumAux
import BinaryFv.RiscV.SepLogic
import BinaryFv.RiscV.ShiftIopFrame
import BinaryFv.RiscV.ShiftOrExecuteContract
import BinaryFv.RiscV.Stack
import BinaryFv.RiscV.StackStepContract
import BinaryFv.RiscV.StepContract
import BinaryFv.RiscV.StoreByteExecuteContract
import BinaryFv.RiscV.StoreExecuteContract
import BinaryFv.RiscV.StoreFrame
import BinaryFv.RiscV.StoreMemoryWriteContract
import BinaryFv.RiscV.StoreTranslationContract
import BinaryFv.RiscV.Trace
import BinaryFv.RiscV.TranslationContract
import BinaryFv.RiscV.TranslationFrameAudit
import BinaryFv.RiscV.TryStepFetchMemoryContract
import BinaryFv.RiscV.TryStepStackAddiContract

/-!
# `BinaryFv.RiscV`

Umbrella for the architecture-generic RISC-V layer: bounded ELF parsing, program-image loading,
generated-Sail model support, framing and separation logic, platform (PMP/PMA, translation, MMIO)
contracts, per-instruction frames and execute contracts, and `try_step` packaging.

Nothing in this layer may depend on `BinaryFv.Keccak`.
-/
