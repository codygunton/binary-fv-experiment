import BinaryFv.Zesu.Contracts.Machine
import BinaryFv.Zesu.DecodedValue.Representation
import BinaryFv.Zesu.Elflings.GeneratedLevel1
import BinaryFv.Zesu.Artifacts.Image
import BinaryFv.RiscV.Logic.MemoryWriteFrame
import BinaryFv.RiscV.Logic.RegisterAgree
import BinaryFv.RiscV.Logic.LoadedImage
import BinaryFv.RiscV.Platform.NormalState

/-!
# Execution of the linked bare-metal endpoint

Every instruction is an ordinary extracted Sail-RISCV step. Three distinguished instructions also
update the semantic input/output/exit observation carried beside the machine: the `read_input`
return, the `write_output` return, and the exit-code store before the terminal self-loop.
-/

namespace BinaryFv.Zesu

open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.RiscV

structure EndpointState where
  machine : MachineState
  stdin : Array UInt8
  stdinCursor : Nat
  stdout : Array UInt8
  exitCode : Option Nat

def EndpointPc (state : EndpointState) : Option (BitVec 64) :=
  MachinePc state.machine

/-- The linked Linux process may execute any mapped endpoint instruction selected at a later proof
depth. Concrete instruction theorems still prove exact ownership separately. -/
def EndpointMachinePc (_pc : BitVec 64) : Prop := True

/-- Registers preserved by a returning RV64 ABI call, including the machine-platform registers used
by the parent instruction proofs. -/
def abiCalleePreserved : Register → Prop := fun register =>
  register = x1 ∨ register = hart_state ∨ register = cur_privilege ∨ register = satp ∨
    register = mideleg ∨ register = mie ∨ register = mip ∨ register = pmpcfg_n ∨
    register = pmpaddr_n ∨ register = mcountinhibit ∨ register = minstretcfg ∨
    register = elp ∨ register = misa ∨ register = mstatus ∨ register = sig_meip ∨
    register = pma_regions ∨ register = mseccfg ∨ register = htif_tohost_base ∨
    register = x2 ∨ register = x8 ∨ register = x9 ∨
    register = x18 ∨ register = x19 ∨ register = x20 ∨ register = x21 ∨
    register = x22 ∨ register = x23 ∨ register = x24 ∨ register = x25 ∨
    register = x26 ∨ register = x27

/-- State preserved by every returning Level 1 ABI boundary. Memory permissions are contract-specific. -/
def EndpointCallFrame (before after : EndpointState) : Prop :=
  Agree abiCalleePreserved before.machine after.machine ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  after.machine.choiceState = before.machine.choiceState ∧
  after.machine.tags = before.machine.tags ∧
  after.machine.sailOutput = before.machine.sailOutput

abbrev readContextReturnPc : Nat := 0x1015c
abbrev writeContextReturnPc : Nat := 0x101a0
abbrev exitContextStorePc : Nat := 0x101cc

def BareMetalHostTransitionPc (pc : BitVec 64) : Prop :=
  pc.toNat = readContextReturnPc ∨ pc.toNat = writeContextReturnPc ∨
    pc.toNat = exitContextStorePc

def InputChunk (state : EndpointState) (count : Nat) : Array UInt8 :=
  state.stdin.extract state.stdinCursor (state.stdinCursor + count)

def BareMetalReadStep (stepNo : Nat) (before after : EndpointState) : Prop :=
  before.machine.regs.get? PC = some (BitVec.ofNat 64 readContextReturnPc) ∧
  BytesRep before.machine.mem Elflings.inputBufferAddress before.stdin ∧
  MachineStep stepNo before.machine after.machine ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdin.size ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode

def BareMetalWriteStep (stepNo : Nat) (before after : EndpointState) : Prop :=
  ∃ buffer count chunk,
    before.machine.regs.get? PC = some (BitVec.ofNat 64 writeContextReturnPc) ∧
    before.machine.regs.get? x10 = some (BitVec.ofNat 64 buffer) ∧
    before.machine.regs.get? x11 = some (BitVec.ofNat 64 count) ∧
    chunk.size = count ∧ BytesRep before.machine.mem buffer chunk ∧
    MachineStep stepNo before.machine after.machine ∧
    after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
    after.stdout = before.stdout ++ chunk ∧ after.exitCode = before.exitCode

def BareMetalExitStep (stepNo : Nat) (before after : EndpointState) : Prop :=
  ∃ code,
    before.machine.regs.get? PC = some (BitVec.ofNat 64 exitContextStorePc) ∧
    before.machine.regs.get? x10 = some (BitVec.ofNat 64 code) ∧
    MachineStep stepNo before.machine after.machine ∧
    after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
    after.stdout = before.stdout ∧ after.exitCode = some code ∧
    after.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.zkvmExitTerminalPc)

inductive EndpointStep (stepNo : Nat) (before after : EndpointState) : Prop where
  | sail
      (notSyscall : ∀ pc, EndpointPc before = some pc → ¬ BareMetalHostTransitionPc pc)
      (machineStep : MachineStep stepNo before.machine after.machine)
      (stdin : after.stdin = before.stdin)
      (stdinCursor : after.stdinCursor = before.stdinCursor)
      (stdout : after.stdout = before.stdout)
      (exitCode : after.exitCode = before.exitCode) : EndpointStep stepNo before after
  | read (step : BareMetalReadStep stepNo before after) : EndpointStep stepNo before after
  | write (step : BareMetalWriteStep stepNo before after) : EndpointStep stepNo before after
  | exit (step : BareMetalExitStep stepNo before after) : EndpointStep stepNo before after

/-- Lift an ordinary non-observation instruction while retaining the semantic I/O fields. -/
theorem endpointStep_sail (stepNo : Nat) (before : EndpointState) (after : MachineState)
    (notSyscall : ∀ pc, EndpointPc before = some pc → ¬ BareMetalHostTransitionPc pc)
    (step : MachineStep stepNo before.machine after) :
    EndpointStep stepNo before { before with machine := after } := by
  exact .sail notSyscall step rfl rfl rfl rfl

end BinaryFv.Zesu
