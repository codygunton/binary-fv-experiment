import BinaryFv.Zesu.Contracts.Machine
import BinaryFv.Zesu.DecodedValue.Representation
import BinaryFv.Zesu.Elflings.GeneratedLevel1
import BinaryFv.Zesu.Artifacts.Image
import BinaryFv.RiscV.Logic.MemoryWriteFrame
import BinaryFv.RiscV.Logic.RegisterAgree
import BinaryFv.RiscV.Logic.LoadedImage
import BinaryFv.RiscV.Platform.NormalState

/-!
# Execution of the linked Linux endpoint

The production SSZ endpoint is a static Linux RV64 executable. Ordinary instructions use the
extracted Sail-RISCV `try_step`; its three Linux syscall sites use the explicit relations below.
Treating `ecall` as an ordinary Sail step would instead enter the bare-machine trap handler and does
not describe the shipped program observed under QEMU user mode.
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

abbrev readEcallPc : Nat := Elflings.readInputEcallPc
abbrev writeEcallPc : Nat := Elflings.writeOutputEcallPc
abbrev exitEcallPc : Nat := Elflings.zkvmExitEcallPc

def LinuxSyscallPc (pc : BitVec 64) : Prop :=
  pc.toNat = readEcallPc ∨ pc.toNat = writeEcallPc ∨ pc.toNat = exitEcallPc

def hostWrittenRegisters : Register → Prop := fun register =>
  register = PC ∨ register = nextPC ∨ register = x10 ∨ register = minstret

/-- State components advanced or retained by one host-handled `ecall`. -/
def HostMachineFrame (before after : MachineState) : Prop :=
  WritesOnlyRegs hostWrittenRegisters before after ∧
  after.choiceState = before.choiceState ∧
  after.tags = before.tags ∧
  after.cycleCount = before.cycleCount + 1 ∧
  after.sailOutput = before.sailOutput

def InputChunk (state : EndpointState) (count : Nat) : Array UInt8 :=
  state.stdin.extract state.stdinCursor (state.stdinCursor + count)

/-- Linux `read(0, buffer, requested)` at the runtime's exact `ecall` instruction. -/
def LinuxReadStep (before after : EndpointState) : Prop :=
  ∃ buffer requested count,
    before.machine.regs.get? PC = some (BitVec.ofNat 64 readEcallPc) ∧
    before.machine.regs.get? x17 = some (BitVec.ofNat 64 63) ∧
    before.machine.regs.get? x10 = some (BitVec.ofNat 64 0) ∧
    before.machine.regs.get? x11 = some (BitVec.ofNat 64 buffer) ∧
    before.machine.regs.get? x12 = some (BitVec.ofNat 64 requested) ∧
    count ≤ requested ∧ before.stdinCursor + count ≤ before.stdin.size ∧
    after.stdin = before.stdin ∧
    after.stdinCursor = before.stdinCursor + count ∧
    after.stdout = before.stdout ∧ after.exitCode = before.exitCode ∧
    HostMachineFrame before.machine after.machine ∧
    after.machine.regs.get? PC = some (BitVec.ofNat 64 (readEcallPc + 4)) ∧
    after.machine.regs.get? x10 = some (BitVec.ofNat 64 count) ∧
    BytesRep after.machine.mem buffer (InputChunk before count) ∧
    WritesOnlyWithin (byteRange buffer count) before.machine after.machine

/-- Linux `write(1, buffer, requested)` at the runtime's exact `ecall` instruction. -/
def LinuxWriteStep (before after : EndpointState) : Prop :=
  ∃ buffer requested count chunk,
    before.machine.regs.get? PC = some (BitVec.ofNat 64 writeEcallPc) ∧
    before.machine.regs.get? x17 = some (BitVec.ofNat 64 64) ∧
    before.machine.regs.get? x10 = some (BitVec.ofNat 64 1) ∧
    before.machine.regs.get? x11 = some (BitVec.ofNat 64 buffer) ∧
    before.machine.regs.get? x12 = some (BitVec.ofNat 64 requested) ∧
    0 < count ∧ count ≤ requested ∧
    chunk.size = count ∧ BytesRep before.machine.mem buffer chunk ∧
    after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
    after.stdout = before.stdout ++ chunk ∧
    after.exitCode = before.exitCode ∧
    HostMachineFrame before.machine after.machine ∧
    after.machine.mem = before.machine.mem ∧
    after.machine.regs.get? PC = some (BitVec.ofNat 64 (writeEcallPc + 4)) ∧
    after.machine.regs.get? x10 = some (BitVec.ofNat 64 count)

/-- Linux `exit(code)`. The terminal state remains at the consumed `ecall` PC and records the code. -/
def LinuxExitStep (before after : EndpointState) : Prop :=
  ∃ code,
    before.machine.regs.get? PC = some (BitVec.ofNat 64 exitEcallPc) ∧
    before.machine.regs.get? x17 = some (BitVec.ofNat 64 93) ∧
    before.machine.regs.get? x10 = some (BitVec.ofNat 64 code) ∧
    after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
    after.stdout = before.stdout ∧ after.exitCode = some code ∧
    HostMachineFrame before.machine after.machine ∧
    after.machine.mem = before.machine.mem ∧
    after.machine.regs.get? PC = some (BitVec.ofNat 64 exitEcallPc)

inductive EndpointStep (stepNo : Nat) (before after : EndpointState) : Prop where
  | sail
      (notSyscall : ∀ pc, EndpointPc before = some pc → ¬ LinuxSyscallPc pc)
      (machineStep : MachineStep stepNo before.machine after.machine)
      (stdin : after.stdin = before.stdin)
      (stdinCursor : after.stdinCursor = before.stdinCursor)
      (stdout : after.stdout = before.stdout)
      (exitCode : after.exitCode = before.exitCode) : EndpointStep stepNo before after
  | read (step : LinuxReadStep before after) : EndpointStep stepNo before after
  | write (step : LinuxWriteStep before after) : EndpointStep stepNo before after
  | exit (step : LinuxExitStep before after) : EndpointStep stepNo before after

/-- Lift an ordinary production instruction into the linked Linux endpoint while retaining every
host component. Concrete Level 0 instruction wrappers supply the `try_step` run. -/
theorem endpointStep_sail (stepNo : Nat) (before : EndpointState) (after : MachineState)
    (notSyscall : ∀ pc, EndpointPc before = some pc → ¬ LinuxSyscallPc pc)
    (step : MachineStep stepNo before.machine after) :
    EndpointStep stepNo before { before with machine := after } := by
  exact .sail notSyscall step rfl rfl rfl rfl

end BinaryFv.Zesu
