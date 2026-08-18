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

def writeNat64LE (address value : Nat) : SailM Unit :=
  writeMemoryBytes address ((List.range 8).map fun index =>
    UInt8.ofNat ((value / 256 ^ index) % 256))

def canonicalStackPointer : Nat := Elflings.inputBufferAddress - 0x1000

/-- Readable, writable, executable platform region containing the linked image, endpoint stack,
input buffer, arena, and bare-metal observation context. -/
def endpointPmaRegion : PMA_Region :=
  { base := 0#64, size := 0x40000000#64,
    attributes := { (default : PMA) with executable := true, readable := true, writable := true },
    include_in_device_tree := false }

def initializeEndpointMachine (input : Array UInt8) : SailM Unit := do
  initializeModel
  enableMExtension
  writeReg pma_regions [endpointPmaRegion]
  loadFileBackedImage Artifacts.programImage
  writeMemoryBytes Elflings.inputBufferAddress input.toList
  writeNat64LE Elflings.ioContextAddress input.size
  writeReg PC (BitVec.ofNat 64 Elflings.mainEntry)
  writeReg x1 (0 : BitVec 64)
  writeReg x2 (BitVec.ofNat 64 (canonicalStackPointer + 0x380))

def initialEndpointState (input : Array UInt8) : EndpointState :=
  let machine := match (initializeEndpointMachine input).run initialState with
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
