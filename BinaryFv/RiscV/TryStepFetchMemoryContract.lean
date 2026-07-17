import BinaryFv.RiscV.FetchMemoryContract
import BinaryFv.RiscV.TryStepStackAddiContract

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- Lift the exact Machine sparse-RAM fetch path through the generated stack-adjustment `try_step`. -/
theorem tryStepStackAddiRetiresWithFetchMemory (stepNo : Nat) (state : State) (pc : BitVec 64)
    (immediate : BitVec 12) (stackValue retired : BitVec 64) (inhibit : BitVec 32)
    (config : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (platform : FetchBasePlatform (tryStepStackAddiAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepStackAddiAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepStackAddiAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled (tryStepStackAddiAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepStackAddiAfterIncrement state) (tryStepStackAddiAfterIncrement state)
      (.ITYPE (immediate, stackPointer, stackPointer, .ADDI)))
    (notExpected : LandingPadNotExpected (tryStepStackAddiAfterIncrement state))
    (stackRead : (stackAddiNextState (tryStepStackAddiAfterIncrement state) pc).regs.get? x2 =
      some stackValue)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false)
      state (tryStepStackAddiAfterRetired state pc immediate stackValue retired) false := by
  have fetchBytes : FetchBytesBaseContract (tryStepStackAddiAfterIncrement state) pc
      byte0 byte1 byte2 byte3 :=
    fetch_bytes_machine_instructionFetch_fetch_word_run (tryStepStackAddiAfterIncrement state) pc
      byte0 byte1 byte2 byte3 platform noMMIO bytes
  exact tryStepStackAddiRetires stepNo state pc immediate stackValue retired inhibit config
    byte0 byte1 byte2 byte3 platform interrupts base fetchBytes decode notExpected stackRead hartRead
    inhibitRead configRead notInhibited machineEnabled retiredRead

end BinaryFv.RiscV
