import LeanRV64DExecutable
import ShaFv.RISCV.ABI
import ShaFv.RISCV.ProgramImage

namespace ShaFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open ExecutionResult FetchResult

abbrev State := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

def initialState : State := default

def initializeModel : SailM Unit :=
  sail_model_init ()

def runUserStep : SailM Unit := do
  let .F_Base bits ← fetch ()
    | throw Sail.Error.Unreachable
  writeReg nextPC (Sail.BitVec.addInt (← readReg PC) 4)
  let .Retire_Success () ← execute (← ext_decode bits)
    | throw Sail.Error.Unreachable
  tick_pc ()

def runSteps : Nat → SailM Unit
  | 0 => pure ()
  | fuel + 1 => do
      runUserStep
      runSteps fuel

/-- Initialize a direct internal-`sha3` call after the loader proves its ELF symbol address. -/
def prepareSha3Call (sha3Symbol : Word) (messageSize : Nat) (_symbolH : sha3Symbol < addressLimit)
    (_messageH : messageSize < maxMessageSize) : SailM Unit := do
  let abi := sha3Abi messageSize
  let ⟨raH, spH, a0H, a1H, a2H, a3H⟩ := sha3Abi_wellFormed _messageH
  let ⟨lowBaseH, lowSizeH⟩ := lowPmaRange_wordBounds
  let ⟨highBaseH, highSizeH⟩ := highPmaRange_wordBounds
  sail_model_init ()
  let some mainMemory := (← readReg pma_regions).getLast?
    | throw Sail.Error.Unreachable
  writeReg pma_regions [
    { mainMemory with
      base := rv64Word lowPmaRange.start lowBaseH
      size := rv64Word lowPmaRange.size lowSizeH },
    { mainMemory with
      base := rv64Word highPmaRange.start highBaseH
      size := rv64Word highPmaRange.size highSizeH }
  ]
  writeReg pmpcfg_n default
  writeReg pmpaddr_n default
  writeReg mcountinhibit (0 : BitVec 32)
  writeReg minstretcfg (0 : BitVec 64)
  writeReg minstret (0 : BitVec 64)
  writeReg minstret_increment false
  writeReg satp (0 : BitVec 64)
  writeReg cur_privilege Privilege.Machine
  writeReg x1 (rv64Word abi.ra raH)
  writeReg x2 (rv64Word abi.sp spH)
  writeReg x10 (rv64Word abi.a0 a0H)
  writeReg x11 (rv64Word abi.a1 a1H)
  writeReg x12 (rv64Word abi.a2 a2H)
  writeReg x13 (rv64Word abi.a3 a3H)
  writeReg PC (rv64Word sha3Symbol _symbolH)
  writeReg nextPC (rv64Word sha3Symbol _symbolH)

def loadSegmentPrefix (segment : LoadSegment) : Nat → SailM Unit
  | 0 => pure ()
  | count + 1 => do
    let index := count
    let byte := (segment.initialBytes[index]?).getD 0
    let _ ← PreSail.writeByte (segment.virtualAddress + index) (BitVec.ofNat 8 byte.toNat)
    loadSegmentPrefix segment count

def loadSegment (segment : LoadSegment) : SailM Unit :=
  loadSegmentPrefix segment segment.memorySize

def loadSegments : List LoadSegment → SailM Unit
  | [] => pure ()
  | segment :: remaining => do
    loadSegment segment
    loadSegments remaining

/-- Load every byte of a parsed image, including zero-fill after a segment's file bytes. -/
def loadProgramImage (image : ProgramImage) : SailM Unit :=
  loadSegments image.segments.toList.reverse

def prepareZeroLengthSha3Call (sha3Symbol : Word) : SailM Unit := do
  if symbolH : sha3Symbol < addressLimit then
    prepareSha3Call sha3Symbol 0 symbolH (by decide)
  else
    throw Sail.Error.Unreachable

def fetchLoadedSha3 (image : ProgramImage) (sha3Symbol : Word) : SailM FetchResult := do
  prepareZeroLengthSha3Call sha3Symbol
  loadProgramImage image
  fetch ()

end ShaFv.RISCV
