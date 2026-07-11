import LeanRV64DExecutable

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

def sha3EntryPoint : Nat := 0x101b8

def prepareEntryInstruction : SailM Unit := do
  sail_model_init ()
  let some mainMemory := (← readReg pma_regions).getLast?
    | throw Sail.Error.Unreachable
  writeReg pma_regions [{ mainMemory with
    base := (0 : BitVec 64)
    size := (0x20000 : BitVec 64) }]
  writeReg pmpcfg_n default
  writeReg pmpaddr_n default
  writeReg mcountinhibit (0 : BitVec 32)
  writeReg minstretcfg (0 : BitVec 64)
  writeReg minstret (0 : BitVec 64)
  writeReg minstret_increment false
  writeReg satp (0 : BitVec 64)
  writeReg PC (BitVec.ofNat 64 sha3EntryPoint)
  writeReg nextPC (BitVec.ofNat 64 sha3EntryPoint)
  writeReg cur_privilege Privilege.Machine
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
