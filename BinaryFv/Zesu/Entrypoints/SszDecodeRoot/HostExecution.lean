import BinaryFv.Zesu.Contracts.Machine
import BinaryFv.Zesu.DecodedValue.Representation
import BinaryFv.Zesu.Elflings.GeneratedLevel1
import BinaryFv.Zesu.Artifacts.Image
import BinaryFv.RiscV.Logic.MemoryWriteFrame
import BinaryFv.RiscV.Logic.RegisterAgree
import BinaryFv.RiscV.Logic.LoadedImage
import BinaryFv.RiscV.Platform.NormalState
import BinaryFv.RiscV.Step.ControlFlow

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

@[ext] theorem EndpointState.ext {left right : EndpointState}
    (machine : left.machine = right.machine) (stdin : left.stdin = right.stdin)
    (stdinCursor : left.stdinCursor = right.stdinCursor) (stdout : left.stdout = right.stdout)
    (exitCode : left.exitCode = right.exitCode) : left = right := by
  cases left
  cases right
  simp_all

def EndpointPc (state : EndpointState) : Option (BitVec 64) :=
  MachinePc state.machine

/-- Aligned file-backed addresses of the linked endpoint. Function contracts narrow this set to
their generated execution ranges; the machine configuration must not quantify over impossible
unaligned or non-image program counters. -/
def EndpointMachinePc (pc : BitVec 64) : Prop :=
  pc.toNat % 4 = 0 ∧ ∃ byte, Artifacts.programImage.readFileByte? pc.toNat = some byte

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

/-- The architectural integer registers represented in the extracted Sail machine state. -/
def architecturalIntegerRegisters : List Register :=
  [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16,
    x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]

/-- Every architectural integer register has a value. A real instruction can replace a value, but
it cannot remove the register from the machine register file. -/
def GeneralRegistersPresent (state : MachineState) : Prop :=
  ∀ register ∈ architecturalIntegerRegisters,
    ∃ value, state.regs.get? register = some value

theorem GeneralRegistersPresent.read {state : MachineState}
    (present : GeneralRegistersPresent state) {register : Register}
    (member : register ∈ architecturalIntegerRegisters) :
    ∃ value, state.regs.get? register = some value :=
  present register member

/-- A register write frame preserves the complete integer-register domain when every possibly
written integer register remains present. -/
theorem GeneralRegistersPresent.of_writesOnlyRegs {written : RegSet} {before after : MachineState}
    (present : GeneralRegistersPresent before) (frame : WritesOnlyRegs written before after)
    (writtenPresent : ∀ register ∈ architecturalIntegerRegisters, written register →
      ∃ value, after.regs.get? register = some value) :
    GeneralRegistersPresent after := by
  intro register member
  by_cases changed : written register
  · exact writtenPresent register member changed
  · obtain ⟨value, read⟩ := present register member
    exact ⟨value, (frame.get register changed).trans read⟩

/-- One ordinary integer-register write preserves the complete integer-register domain. -/
theorem GeneralRegistersPresent.of_one_general_write {written : RegSet}
    {before after : MachineState} {destination : Register} {value : RegisterType destination}
    (present : GeneralRegistersPresent before) (frame : WritesOnlyRegs written before after)
    (onlyDestination : ∀ register ∈ architecturalIntegerRegisters,
      written register → register = destination)
    (destinationAt : after.regs.get? destination = some value) :
    GeneralRegistersPresent after := by
  apply present.of_writesOnlyRegs frame
  intro register member changed
  have equal := onlyDestination register member changed
  subst register
  exact ⟨value, destinationAt⟩

theorem GeneralRegistersPresent.of_bookkeeping_write {before after : MachineState}
    {destination : Register} {value : RegisterType destination}
    (present : GeneralRegistersPresent before)
    (frame : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only destination)) before after)
    (destinationAt : after.regs.get? destination = some value) :
    GeneralRegistersPresent after := by
  apply present.of_one_general_write frame _ destinationAt
  intro register member changed
  rcases changed with bookkeeping | destination
  · simp only [stepBookkeeping] at bookkeeping
    rcases bookkeeping with rfl | rfl | rfl | rfl <;>
      simp [architecturalIntegerRegisters] at member
  · exact destination

theorem GeneralRegistersPresent.of_bookkeeping {before after : MachineState}
    (present : GeneralRegistersPresent before)
    (frame : WritesOnlyRegs stepBookkeeping before after) :
    GeneralRegistersPresent after := by
  apply present.of_writesOnlyRegs frame
  intro register member changed
  simp only [stepBookkeeping] at changed
  rcases changed with rfl | rfl | rfl | rfl <;>
    simp [architecturalIntegerRegisters] at member

theorem not_generalRegistersPresent_of_missing_x17 {state : MachineState}
    (missing : state.regs.get? x17 = none) : ¬GeneralRegistersPresent state := by
  intro present
  obtain ⟨value, read⟩ := present.read (register := x17)
    (by simp [architecturalIntegerRegisters])
  rw [missing] at read
  contradiction

/-- State preserved by every returning Level 1 ABI boundary. Memory permissions are contract-specific. -/
def EndpointCallFrame (before after : EndpointState) : Prop :=
  Agree abiCalleePreserved before.machine after.machine ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  after.machine.choiceState = before.machine.choiceState ∧
  after.machine.tags = before.machine.tags ∧
  after.machine.sailOutput = before.machine.sailOutput

/-- Nonarchitectural Sail interpreter fields retained while composing machine-code contracts. -/
def EndpointMachineAuxAgree (before after : MachineState) : Prop :=
  after.choiceState = before.choiceState ∧ after.tags = before.tags ∧
    after.sailOutput = before.sailOutput

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
    buffer < 2 ^ 64 ∧ count < 2 ^ 64 ∧
    chunk.size = count ∧ BytesRep before.machine.mem buffer chunk ∧
    MachineStep stepNo before.machine after.machine ∧
    after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
    after.stdout = before.stdout ++ chunk ∧ after.exitCode = before.exitCode

def BareMetalExitStep (stepNo : Nat) (before after : EndpointState) : Prop :=
  ∃ code,
    before.machine.regs.get? PC = some (BitVec.ofNat 64 exitContextStorePc) ∧
    before.machine.regs.get? x10 = some (BitVec.ofNat 64 code) ∧
    code < 2 ^ 64 ∧
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
