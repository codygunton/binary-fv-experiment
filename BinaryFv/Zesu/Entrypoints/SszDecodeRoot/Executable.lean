import BinaryFv.Zesu.Contracts.CanonicalOutcome
import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.HostExecution
import BinaryFv.RiscV.Execution.ImageLoad

/-! Executable interpreter for the linked bare-metal Zesu endpoint. -/

namespace BinaryFv.Zesu

open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.RiscV

def writeMemoryBytes (address : Nat) : List UInt8 → SailM Unit
  | [] => pure ()
  | byte :: bytes => do
      let _ ← PreSail.writeByte address (BitVec.ofNat 8 byte.toNat)
      writeMemoryBytes (address + 1) bytes

def canonicalStackPointer : Nat := Elflings.inputBufferAddress - 0x1000

/-- Readable, writable, executable platform region containing the linked image, endpoint stack,
input buffer, arena, and bare-metal observation context. -/
def endpointPmaRegion : PMA_Region :=
  { base := 0#64, size := 0x40000000#64,
    attributes := { (default : PMA) with executable := true, readable := true, writable := true },
    include_in_device_tree := false }

def endpointConfiguredMachine : State :=
  let regs := initialState.regs
  let regs := regs.insert hart_state (HartState.HART_ACTIVE ())
  let regs := regs.insert cur_privilege Privilege.Machine
  let regs := regs.insert satp (0 : BitVec 64)
  let regs := regs.insert mideleg (0 : BitVec 64)
  let regs := regs.insert mie (0 : BitVec 64)
  let regs := regs.insert mip (0 : BitVec 64)
  let regs := regs.insert pmpcfg_n (default : Vector (BitVec 8) 64)
  let regs := regs.insert pmpaddr_n (default : Vector (BitVec 64) 64)
  let regs := regs.insert mcountinhibit (0 : BitVec 32)
  let regs := regs.insert minstretcfg (0 : BitVec 64)
  let regs := regs.insert elp (landing_pad_bits_backwards landing_pad_expectation.NO_LP_EXPECTED)
  let regs := regs.insert misa (BitVec.ofNat 64 (2 ^ 12))
  let regs := regs.insert minstret (0 : BitVec 64)
  let regs := regs.insert mstatus (0 : BitVec 64)
  let regs := regs.insert mseccfg (0 : BitVec 64)
  let regs := regs.insert sig_meip (0 : BitVec 1)
  let regs := regs.insert htif_tohost_base none
  let regs := regs.insert pma_regions [endpointPmaRegion]
  let regs := regs.insert x8 (0 : BitVec 64)
  let regs := regs.insert x9 (0 : BitVec 64)
  let regs := regs.insert x18 (0 : BitVec 64)
  let regs := regs.insert x19 (0 : BitVec 64)
  let regs := regs.insert x20 (0 : BitVec 64)
  let regs := regs.insert x21 (0 : BitVec 64)
  let regs := regs.insert x22 (0 : BitVec 64)
  let regs := regs.insert x23 (0 : BitVec 64)
  let regs := regs.insert x24 (0 : BitVec 64)
  let regs := regs.insert x25 (0 : BitVec 64)
  let regs := regs.insert x26 (0 : BitVec 64)
  let regs := regs.insert x27 (0 : BitVec 64)
  { initialState with regs }

def initializeEndpointBaseMachine : SailM Unit :=
  loadFileBackedImage Artifacts.programImage

def stateOfResult {ε α : Type} (result : EStateM.Result ε State α) : State :=
  match result with | .ok _ state | .error _ state => state

theorem stateOfResult_eq_of_runs {action : SailM Unit} {start finish : State}
    (run : Runs action start finish ()) : stateOfResult (action.run start) = finish := by
  rw [run]
  rfl

def endpointProgramMemory : Std.ExtHashMap Nat (BitVec 8) :=
  (stateOfResult (initializeEndpointBaseMachine.run endpointConfiguredMachine)).mem

theorem endpointProgramMemory_eq_of_runs {finish : State}
    (run : Runs initializeEndpointBaseMachine endpointConfiguredMachine finish ()) :
    endpointProgramMemory = finish.mem := by
  unfold endpointProgramMemory
  exact congrArg (fun state : State => state.mem) (stateOfResult_eq_of_runs run)

def endpointBaseMachine : State :=
  { endpointConfiguredMachine with mem := endpointProgramMemory }

def initializeEndpointInput (input : Array UInt8) : SailM Unit := do
  writeMemoryBytes Elflings.inputBufferAddress input.toList
  let _ ← PreSail.writeBytes (n := 8) Elflings.ioContextAddress (BitVec.ofNat 64 input.size)
  writeReg PC (BitVec.ofNat 64 Elflings.mainEntry)
  writeReg x1 (0 : BitVec 64)
  writeReg x2 (BitVec.ofNat 64 (canonicalStackPointer + 0x380))

def initialEndpointState (input : Array UInt8) : EndpointState :=
  let machine := match (initializeEndpointInput input).run endpointBaseMachine with
    | .ok _ state | .error _ state => state
  { machine, stdin := input, stdinCursor := 0, stdout := #[], exitCode := none }

def readMemoryBytes (memory : Std.ExtHashMap Nat (BitVec 8)) (address : Nat) :
    Nat → Option (Array UInt8)
  | 0 => some #[]
  | count + 1 => do
      let previous ← readMemoryBytes memory address count
      let byte ← memory.get? (address + count)
      pure (previous.push (UInt8.ofNat byte.toNat))

def endpointStep (stepNo : Nat) (before : EndpointState) : Except Unit EndpointState :=
  match (try_step stepNo false).run before.machine with
  | .error _ _ => .error ()
  | .ok true _ => .error ()
  | .ok false machine =>
      let ordinary := { before with machine }
      match before.machine.regs.get? PC with
      | some pc =>
          if pc.toNat = readContextReturnPc then
            .ok { ordinary with stdinCursor := before.stdin.size }
          else if pc.toNat = writeContextReturnPc then
            match before.machine.regs.get? x10, before.machine.regs.get? x11 with
            | some buffer, some count =>
                match readMemoryBytes before.machine.mem buffer.toNat count.toNat with
                | some bytes => .ok { ordinary with stdout := before.stdout ++ bytes }
                | none => .error ()
            | _, _ => .error ()
          else if pc.toNat = exitContextStorePc then
            match before.machine.regs.get? x10 with
            | some code => .ok { ordinary with exitCode := some code.toNat }
            | none => .error ()
          else
            .ok ordinary
      | none => .ok ordinary

def finishEndpoint (state : EndpointState) : ZesuDecodeOutcome :=
  if state.machine.regs.get? PC ≠ some (BitVec.ofNat 64 Elflings.zkvmExitTerminalPc) then
    .invalidObservation
  else if state.exitCode ≠ some 0 then
    .invalidObservation
  else
    match decodeZesuObservation state.stdout with
    | some .failure => .rejected
    | some (.success decoded) => .decoded decoded
    | none => .invalidObservation

def runEndpoint : Nat → Nat → EndpointState → ZesuDecodeOutcome
  | 0, _, _ => .fuelExhausted
  | fuel + 1, stepNo, state =>
      if state.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.zkvmExitTerminalPc) then
        finishEndpoint state
      else
        match endpointStep stepNo state with
        | .error _ => .machineError
        | .ok next => runEndpoint fuel (stepNo + 1) next

namespace RiscvSpec

structure Binary where
  initialState : Array UInt8 → EndpointState
  fuel : Nat

def execute (binary : Binary) (input : Array UInt8) : ZesuDecodeOutcome :=
  runEndpoint binary.fuel 0 (binary.initialState input)

end RiscvSpec

def zesuSszBinary : RiscvSpec.Binary := {
  initialState := initialEndpointState
  fuel := 2 ^ 192
}

end BinaryFv.Zesu
