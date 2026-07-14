import BinaryFv.RISCV.ExecuteContract
import BinaryFv.RISCV.FetchContract
import BinaryFv.RISCV.HartPrimitives

namespace BinaryFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open FetchBytes_Result
open FetchResult

/-- The state after the generated base-instruction path writes `nextPC`. -/
def stackAddiNextState (state : State) (pc : BitVec 64) : State :=
  { state with regs := state.regs.insert nextPC (Sail.BitVec.addInt pc 4) }

/-- The state after the generated `addi sp, sp, immediate` retirement. -/
def stackAddiRetiredState (state : State) (pc : BitVec 64) (immediate : BitVec 12)
    (stackValue : BitVec 64) : State :=
  { stackAddiNextState state pc with
    regs := (stackAddiNextState state pc).regs.insert x2
      (stackValue + sign_extend (m := 64) immediate) }

/-- Compose generated fetch, decode, next-PC, and execute contracts for `addi sp, sp, immediate`. -/
theorem runHartActiveStackAddiRetires (stepNo : Nat) (state : State) (pc : BitVec 64)
    (immediate : BitVec 12) (stackValue : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (platform : FetchBasePlatform state pc)
    (interrupts : InterruptDisabled state)
    (base : BaseInstructionEncoding byte0)
    (fetchBytes : FetchBytesBaseContract state pc byte0 byte1 byte2 byte3)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3)) state state
      (.ITYPE (immediate, stackPointer, stackPointer, .ADDI)))
    (notExpected : LandingPadNotExpected state)
    (stackRead : (stackAddiNextState state pc).regs.get? x2 = some stackValue) :
    Runs (run_hart_active stepNo) state
      (stackAddiRetiredState state pc immediate stackValue)
      (.Step_Execute (.Retire_Success (),
        zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3))) := by
  have fetch : Runs (fetch ()) state state (.F_Base (fetchWord byte0 byte1 byte2 byte3)) :=
    fetch_base_of_fetchBytes state pc byte0 byte1 byte2 byte3 platform base fetchBytes
  rcases platform with ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeRead,
    pcLow0, pcLow1, alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩
  have dispatch : Runs (dispatchInterrupt Privilege.Machine) state state none := by
    unfold Runs
    exact dispatchInterrupt_disabled state Privilege.Machine interrupts
  have landingPad : Runs (is_landing_pad_expected ()) state state false :=
    landingPad_notExpected state notExpected
  have nextPc : Runs (Sail.writeReg nextPC (Sail.BitVec.addInt pc 4)) state
      (stackAddiNextState state pc) PUnit.unit := by
    simpa [stackAddiNextState] using writeNextPc_run state pc
  have execute : Runs (execute (.ITYPE (immediate, stackPointer, stackPointer, .ADDI)))
      (stackAddiNextState state pc) (stackAddiRetiredState state pc immediate stackValue)
      (.Retire_Success ()) := by
    simpa [stackAddiRetiredState] using
      executeStackAddiDispatchRuns (stackAddiNextState state pc) immediate stackValue stackRead
  exact runHartActiveBaseRetires stepNo state state (stackAddiNextState state pc)
    (stackAddiRetiredState state pc immediate stackValue) Privilege.Machine
    (fetchWord byte0 byte1 byte2 byte3) (.ITYPE (immediate, stackPointer, stackPointer, .ADDI)) pc
    privilegeRead dispatch fetch decode landingPad pcRead nextPc execute

end BinaryFv.RISCV
