import BinaryFv.Keccak.Artifact
import BinaryFv.RISCV.Machine

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RISCV

def loadBytes (base : Nat) (bytes : ByteArray) : SailM Unit := do
  for h : index in [:bytes.size] do
    writeByte (base + index) (BitVec.ofNat 8 bytes[index].toNat)

def readByteArray (base length : Nat) : SailM ByteArray := do
  let mut result := ByteArray.emptyWithCapacity length
  for index in [:length] do
    result := result.push (UInt8.ofNat (← readByte (base + index)).toNat)
  pure result

/-- Materialize a sparse Sail memory range with a known byte value. -/
def loadFilledBytes (base count : Nat) (value : UInt8) : SailM Unit := do
  for index in [:count] do
    writeByte (base + index) (BitVec.ofNat 8 value.toNat)

/-- Materialize zeroed sparse memory required by the generated Sail memory model. -/
def loadZeroBytes (base count : Nat) : SailM Unit :=
  loadFilledBytes base count 0

/-- Keep a valid mapped input pointer even for an empty direct call. -/
def messageStorageSize (message : ByteArray) : Nat :=
  max 1 message.size

def messageStorage (message : ByteArray) : ByteArray :=
  if message.size == 0 then ByteArray.mk #[0] else message

def guardSize : Nat := 16

def guardByte : UInt8 := 0xa5

def guardBytes : ByteArray :=
  ByteArray.mk <| Array.replicate guardSize guardByte

def outputPrefixAddress (code : AddressRange) : Word :=
  outputAddress code - guardSize

def outputSuffixAddress (code : AddressRange) : Word :=
  outputAddress code + digestSize

def messagePrefixAddress (code : AddressRange) : Word :=
  messageAddress code - guardSize

def messageSuffixAddress (code : AddressRange) (message : ByteArray) : Word :=
  messageAddress code + messageStorageSize message

/-- Inert platform state for normal direct execution; ABI and memory predicates remain separate. -/
def NormalExecutionState (state : State) : Prop :=
  state.regs.get? hart_state = some (HartState.HART_ACTIVE ()) ∧
    state.regs.get? cur_privilege = some Privilege.Machine ∧
      state.regs.get? satp = some (0 : BitVec 64) ∧
        state.regs.get? mideleg = some (0 : BitVec 64) ∧
          state.regs.get? mie = some (0 : BitVec 64) ∧
            state.regs.get? mip = some (0 : BitVec 64) ∧
              state.regs.get? pmpcfg_n = some (default : Vector (BitVec 8) 64) ∧
                state.regs.get? pmpaddr_n = some (default : Vector (BitVec 64) 64) ∧
                  state.regs.get? mcountinhibit = some (0 : BitVec 32) ∧
                    state.regs.get? minstretcfg = some (0 : BitVec 64) ∧
                      state.regs.get? elp = some
                        (landing_pad_bits_backwards landing_pad_expectation.NO_LP_EXPECTED) ∧
                        match state.regs.get? misa with
                        | some misaBits => Sail.BitVec.access misaBits 12 = 1#1
                        | none => False

def initializeIntegerRegisters : SailM Unit := do
  writeReg x3 (0 : BitVec 64)
  writeReg x4 (0 : BitVec 64)
  writeReg x5 (0 : BitVec 64)
  writeReg x6 (0 : BitVec 64)
  writeReg x7 (0 : BitVec 64)
  writeReg x8 (0 : BitVec 64)
  writeReg x9 (0 : BitVec 64)
  writeReg x10 (0 : BitVec 64)
  writeReg x11 (0 : BitVec 64)
  writeReg x12 (0 : BitVec 64)
  writeReg x13 (0 : BitVec 64)
  writeReg x14 (0 : BitVec 64)
  writeReg x15 (0 : BitVec 64)
  writeReg x16 (0 : BitVec 64)
  writeReg x17 (0 : BitVec 64)
  writeReg x18 (0 : BitVec 64)
  writeReg x19 (0 : BitVec 64)
  writeReg x20 (0 : BitVec 64)
  writeReg x21 (0 : BitVec 64)
  writeReg x22 (0 : BitVec 64)
  writeReg x23 (0 : BitVec 64)
  writeReg x24 (0 : BitVec 64)
  writeReg x25 (0 : BitVec 64)
  writeReg x26 (0 : BitVec 64)
  writeReg x27 (0 : BitVec 64)
  writeReg x28 (0 : BitVec 64)
  writeReg x29 (0 : BitVec 64)
  writeReg x30 (0 : BitVec 64)
  writeReg x31 (0 : BitVec 64)

def configureDirectCallMachine : SailM Unit := do
  initializeModel
  enableMExtension
  let some mainMemory := (← readReg pma_regions).getLast? | throw Sail.Error.Unreachable
  writeReg pma_regions [
    { mainMemory with
      base := BitVec.ofNat 64 lowPmaRange.start
      size := BitVec.ofNat 64 lowPmaRange.size },
    { mainMemory with
      base := BitVec.ofNat 64 stackRange.start
      size := BitVec.ofNat 64 stackRange.size }
  ]
  writeReg pmpcfg_n default
  writeReg pmpaddr_n default
  writeReg mcountinhibit (0 : BitVec 32)
  writeReg minstretcfg (0 : BitVec 64)
  writeReg minstret (0 : BitVec 64)
  writeReg minstret_increment false
  writeReg mideleg (0 : BitVec 64)
  writeReg mip (0 : BitVec 64)
  writeReg mie (0 : BitVec 64)
  writeReg satp (0 : BitVec 64)
  writeReg cur_privilege Privilege.Machine
  reset_elp ()
  initializeIntegerRegisters

/-- Run only generated Sail `try_step` calls until the direct-call return sentinel is reached. -/
def runToSentinel (sentinel : BitVec 64) : Nat → Nat → SailM Nat
  | 0, _ => throw Sail.Error.Unreachable
  | fuel + 1, steps => do
    if (← readReg PC) == sentinel then
      pure steps
    else
      let waiting ← try_step steps false
      if waiting then throw Sail.Error.Unreachable
      else runToSentinel sentinel fuel (steps + 1)

structure DirectCallResult where
  digest : ByteArray
  steps : Nat
  returnCode : Nat
  pc : Word
  ra : Word
  sp : Word
  codeUnchanged : Bool
  messageUnchanged : Bool
  outputGuardsUnchanged : Bool
  messageGuardsUnchanged : Bool
  stackBottomGuardUnchanged : Bool

def executeDirect (image : ProgramImage) (code : AddressRange) (entry : Word) (message : ByteArray)
    (fuel : Nat) : SailM DirectCallResult := do
  configureDirectCallMachine
  loadProgramImage image
  loadZeroBytes stackRange.start stackRange.size
  loadFilledBytes stackRange.start guardSize guardByte
  loadFilledBytes (outputPrefixAddress code) guardSize guardByte
  loadFilledBytes (outputAddress code) digestSize guardByte
  loadFilledBytes (outputSuffixAddress code) guardSize guardByte
  loadFilledBytes (messagePrefixAddress code) guardSize guardByte
  writeByte (messageAddress code) (0 : BitVec 8)
  loadBytes (messageAddress code) message
  loadFilledBytes (messageSuffixAddress code message) guardSize guardByte
  writeReg x1 (BitVec.ofNat 64 (returnAddress code))
  writeReg x2 (BitVec.ofNat 64 stackTop)
  writeReg x10 (BitVec.ofNat 64 (messageAddress code))
  writeReg x11 (BitVec.ofNat 64 message.size)
  writeReg x12 (BitVec.ofNat 64 (outputAddress code))
  writeReg PC (BitVec.ofNat 64 entry)
  writeReg nextPC (BitVec.ofNat 64 entry)
  let steps ← runToSentinel (BitVec.ofNat 64 (returnAddress code)) fuel 0
  let returnCode := (← readReg x10).toNat
  let pc := (← readReg PC).toNat
  let ra := (← readReg x1).toNat
  let sp := (← readReg x2).toNat
  let digest ← readByteArray (outputAddress code) digestSize
  let codeUnchanged ← image.checkUnchanged
  let messageBytes ← readByteArray (messageAddress code) (messageStorageSize message)
  let outputPrefix ← readByteArray (outputPrefixAddress code) guardSize
  let outputSuffix ← readByteArray (outputSuffixAddress code) guardSize
  let messagePrefix ← readByteArray (messagePrefixAddress code) guardSize
  let messageSuffix ← readByteArray (messageSuffixAddress code message) guardSize
  let stackBottomGuard ← readByteArray stackRange.start guardSize
  pure {
    digest
    steps
    returnCode
    pc
    ra
    sp
    codeUnchanged
    messageUnchanged := messageBytes == messageStorage message
    outputGuardsUnchanged := outputPrefix == guardBytes && outputSuffix == guardBytes
    messageGuardsUnchanged := messagePrefix == guardBytes && messageSuffix == guardBytes
    stackBottomGuardUnchanged := stackBottomGuard == guardBytes
  }

inductive ConcreteRunError where
  | unsupportedMessage
  | invalidArtifact
  | sailFailure
deriving DecidableEq, Repr

/-- Run the fixed artifact from the canonical empty Sail state and retain concrete observations. -/
def runConcrete (message : ByteArray) (fuel : Nat) : Except ConcreteRunError DirectCallResult :=
  if message.size < maxMessageSize then
    match Artifact.programImage, Artifact.codeRange, Artifact.entryAddress with
    | .ok image, .ok code, .ok entry =>
      match (executeDirect image code entry message fuel).run initialState with
      | .ok result _ => .ok result
      | .error _ _ => .error .sailFailure
    | _, _, _ => .error .invalidArtifact
  else
    .error .unsupportedMessage

end BinaryFv.Keccak
