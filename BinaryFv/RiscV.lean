import BinaryFv.RiscV.Analysis.CallGraph
import BinaryFv.RiscV.Analysis.FrameCoverage
import BinaryFv.RiscV.Analysis.FunctionWords
import BinaryFv.RiscV.Analysis.Reachability
import BinaryFv.RiscV.Analysis.StackDataFlow
import BinaryFv.RiscV.Analysis.StackFlow
import BinaryFv.RiscV.ELF.CFG
import BinaryFv.RiscV.ELF.Decode
import BinaryFv.RiscV.ELF.Elf64
import BinaryFv.RiscV.Execution.ImageLoad
import BinaryFv.RiscV.Execution.Machine
import BinaryFv.RiscV.Execution.MemoryIo
import BinaryFv.RiscV.Execution.Runner
import BinaryFv.RiscV.Instruction.Decode
import BinaryFv.RiscV.Instruction.Execute.ControlFlow
import BinaryFv.RiscV.Instruction.Execute.Load
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Instruction.Execute.ShiftOr
import BinaryFv.RiscV.Instruction.Execute.StackAddi
import BinaryFv.RiscV.Instruction.Execute.StackAddiDispatch
import BinaryFv.RiscV.Instruction.Execute.Store
import BinaryFv.RiscV.Instruction.Execute.StoreByte
import BinaryFv.RiscV.Instruction.Frame.BType
import BinaryFv.RiscV.Instruction.Frame.ControlDispatch
import BinaryFv.RiscV.Instruction.Frame.Decode
import BinaryFv.RiscV.Instruction.Frame.Fence
import BinaryFv.RiscV.Instruction.Frame.IType
import BinaryFv.RiscV.Instruction.Frame.IntegerDispatch
import BinaryFv.RiscV.Instruction.Frame.Jump
import BinaryFv.RiscV.Instruction.Frame.Load
import BinaryFv.RiscV.Instruction.Frame.Load.Calculus
import BinaryFv.RiscV.Instruction.Frame.Load.Frame
import BinaryFv.RiscV.Instruction.Frame.Load.Memory
import BinaryFv.RiscV.Instruction.Frame.Load.Platform
import BinaryFv.RiscV.Instruction.Frame.Load.Translation
import BinaryFv.RiscV.Instruction.Frame.MulDiv
import BinaryFv.RiscV.Instruction.Frame.RType
import BinaryFv.RiscV.Instruction.Frame.Register
import BinaryFv.RiscV.Instruction.Frame.ShiftIop
import BinaryFv.RiscV.Instruction.Frame.StackPointer
import BinaryFv.RiscV.Instruction.Frame.Store
import BinaryFv.RiscV.Instruction.Frame.Store.Calculus
import BinaryFv.RiscV.Instruction.Frame.Store.Frame
import BinaryFv.RiscV.Instruction.Frame.Store.Platform
import BinaryFv.RiscV.Instruction.Frame.Store.Pmp
import BinaryFv.RiscV.Instruction.Frame.Store.Translation
import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Logic.Framing
import BinaryFv.RiscV.Logic.ImageMemory
import BinaryFv.RiscV.Logic.LoopInduction
import BinaryFv.RiscV.Logic.MemFrame
import BinaryFv.RiscV.Logic.ReadFrame
import BinaryFv.RiscV.Logic.RegisterAgree
import BinaryFv.RiscV.Logic.SentinelTrace
import BinaryFv.RiscV.Logic.SepLogic
import BinaryFv.RiscV.Logic.StackPointerFrame
import BinaryFv.RiscV.Logic.Trace
import BinaryFv.RiscV.Model.Abi
import BinaryFv.RiscV.Model.Address
import BinaryFv.RiscV.Model.SailEnumAux
import BinaryFv.RiscV.Model.State
import BinaryFv.RiscV.Platform.ClintFrame
import BinaryFv.RiscV.Platform.ExtensionFrame
import BinaryFv.RiscV.Platform.Fetch
import BinaryFv.RiscV.Platform.FetchMemory
import BinaryFv.RiscV.Platform.FetchMmio
import BinaryFv.RiscV.Platform.HtifFrame
import BinaryFv.RiscV.Platform.NormalState
import BinaryFv.RiscV.Platform.PhysicalAccess
import BinaryFv.RiscV.Platform.Pmp
import BinaryFv.RiscV.Platform.StoreMemoryWrite
import BinaryFv.RiscV.Platform.StoreTranslation
import BinaryFv.RiscV.Platform.Translation
import BinaryFv.RiscV.Platform.TranslationFrame
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.Proof.RunnerCorrespondence
import BinaryFv.RiscV.Step.AbstractPremise
import BinaryFv.RiscV.Step.Call
import BinaryFv.RiscV.Step.Context
import BinaryFv.RiscV.Step.ControlFlow
import BinaryFv.RiscV.Step.FallThrough
import BinaryFv.RiscV.Step.GenericRetire
import BinaryFv.RiscV.Step.Hart
import BinaryFv.RiscV.Step.LandingPad
import BinaryFv.RiscV.Step.Postlude
import BinaryFv.RiscV.Step.StackAddi
import BinaryFv.RiscV.Step.TryStep
import BinaryFv.RiscV.Step.TryStepStackAddi
import BinaryFv.RiscV.Step.TryStepStackAddiMemory

/-!
# `BinaryFv.RiscV`

Umbrella for the architecture-generic RISC-V layer, in dependency order:

* `Model` — generated-Sail state/monad, ISA initialization, and the RV64 address/ABI constants.
* `ELF` — RISC-V ELF validation, instruction decoding, and the control-flow graph.
* `Logic` — framing, the stack-pointer calculus, separation logic, traces, and loop induction.
* `Platform` — PMP/PMA, address translation, MMIO, and the fetch/load/store environment.
* `Instruction` — per-instruction frames (`Frame/`) and execute contracts (`Execute/`).
* `Step` — hart, postlude, and `try_step` packaging.
* `Execution` — executable image loading and runners.
* `Analysis` — static reachability, call-graph, and stack-flow algorithms.

Nothing in this layer may depend on `BinaryFv.Keccak`; the layer is generic over the binary under
analysis. Enforced by the import audit in `nix/proof.nix`.
-/
