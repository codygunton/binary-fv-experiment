import BinaryFv.RiscV.Step.Hart
import BinaryFv.Keccak.Contracts
import BinaryFv.RiscV.Platform.Fetch
import BinaryFv.RiscV.Step.LandingPad

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open FetchBytes_Result
open FetchResult

/-- Lift a fixed generated XOR instruction slice through the `execute` dispatcher. -/
theorem executeCoreXorDispatch (state : State) (left right : BitVec 64)
    (leftRead : state.regs.get? x19 = some left)
    (rightRead : state.regs.get? x29 = some right) :
    (execute (.RTYPE (Contracts.r29, Contracts.r19, Contracts.r16, .XOR))).run state =
      .ok (.Retire_Success ()) { state with regs := state.regs.insert x16 (left ^^^ right) } := by
  change (execute_RTYPE Contracts.r29 Contracts.r19 Contracts.r16 .XOR).run state = _
  exact Contracts.execute_core_xor state left right leftRead rightRead

/-- Package the fixed XOR dispatcher lift as a generated Sail action contract. -/
theorem executeCoreXorDispatchRuns (state : State) (left right : BitVec 64)
    (leftRead : state.regs.get? x19 = some left)
    (rightRead : state.regs.get? x29 = some right) :
    Runs (execute (.RTYPE (Contracts.r29, Contracts.r19, Contracts.r16, .XOR))) state
      { state with regs := state.regs.insert x16 (left ^^^ right) } (.Retire_Success ()) := by
  unfold Runs
  exact executeCoreXorDispatch state left right leftRead rightRead

/-- The state after the base-instruction path writes the generated next PC. -/
def coreXorNextState (state : State) (pc : BitVec 64) : State :=
  { state with regs := state.regs.insert nextPC (Sail.BitVec.addInt pc 4) }

/-- The state after the fixed XOR instruction slice retires. -/
def coreXorRetiredState (state : State) (pc left right : BitVec 64) : State :=
  { coreXorNextState state pc with
    regs := (coreXorNextState state pc).regs.insert x16 (left ^^^ right) }

/-- Compose explicit base-fetch and decoder premises with the fixed XOR instruction-slice path. -/
theorem runHartActiveCoreXorRetires (stepNo : Nat) (state : State) (pc left right : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8) (platform : FetchBasePlatform state pc)
    (interrupts : InterruptDisabled state) (base : BaseInstructionEncoding byte0)
    (fetchBytes : FetchBytesBaseContract state pc byte0 byte1 byte2 byte3)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3)) state state
      (.RTYPE (Contracts.r29, Contracts.r19, Contracts.r16, .XOR)))
    (notExpected : LandingPadNotExpected state)
    (leftRead : (coreXorNextState state pc).regs.get? x19 = some left)
    (rightRead : (coreXorNextState state pc).regs.get? x29 = some right) :
    Runs (run_hart_active stepNo) state (coreXorRetiredState state pc left right)
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
      (coreXorNextState state pc) PUnit.unit := by
    simpa [coreXorNextState] using writeNextPc_run state pc
  have execute : Runs (execute (.RTYPE (Contracts.r29, Contracts.r19, Contracts.r16, .XOR)))
      (coreXorNextState state pc) (coreXorRetiredState state pc left right)
      (.Retire_Success ()) := by
    simpa [coreXorRetiredState] using
      executeCoreXorDispatchRuns (coreXorNextState state pc) left right leftRead rightRead
  exact runHartActiveBaseRetires stepNo state state (coreXorNextState state pc)
    (coreXorRetiredState state pc left right) Privilege.Machine
    (fetchWord byte0 byte1 byte2 byte3)
    (.RTYPE (Contracts.r29, Contracts.r19, Contracts.r16, .XOR)) pc privilegeRead dispatch fetch
    decode landingPad pcRead nextPc execute

end BinaryFv.Keccak
