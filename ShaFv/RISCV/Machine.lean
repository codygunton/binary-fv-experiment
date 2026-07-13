import LeanRV64DExecutable
import ShaFv.RISCV.ABI

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

def sha3EntryPoint : Nat := 0x101b8

def prepareEntryInstruction : SailM Unit := do
  prepareSha3Call sha3EntryPoint 0 (by decide) (by decide)
  let _ ← PreSail.writeBytes (n := 4) sha3EntryPoint (0x00002197 : BitVec 32)

def executeEntryInstruction : SailM (BitVec 64 × BitVec 64) := do
  prepareEntryInstruction
  runUserStep
  return (← readReg x3, ← readReg PC)

def entryInstructionResult : Except (Sail.Error exception) (BitVec 64 × BitVec 64) :=
  match executeEntryInstruction.run initialState with
  | .ok value _ => .ok value
  | .error error _ => .error error

def entryInstructionCorrect : Bool :=
  match entryInstructionResult with
  | .ok (gp, pc) => gp == (0x121b8 : BitVec 64) && pc == (0x101bc : BitVec 64)
  | .error _ => false

theorem entryInstructionCorrect_eq_true : entryInstructionCorrect = true := by
  native_decide

end ShaFv.RISCV
