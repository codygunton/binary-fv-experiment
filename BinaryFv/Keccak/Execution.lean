import BinaryFv.RiscV.Execution.MemoryIo
import BinaryFv.RiscV.Execution.Machine
import BinaryFv.RiscV.Execution.Runner
import BinaryFv.RiscV.Platform.NormalState
import BinaryFv.RiscV.Execution.ImageLoad
import BinaryFv.Keccak.Artifact
import BinaryFv.RiscV.Model.State

namespace BinaryFv.Keccak

open BinaryFv.Binary

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV

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
