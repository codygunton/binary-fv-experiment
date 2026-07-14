import BinaryFv.Keccak.CoreFetchMemoryContract
import BinaryFv.RISCV.PostludePrimitives
import BinaryFv.RISCV.StepContract

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RISCV

/-- The state after the generated `try_step` counter-increment write. -/
def tryStepCoreXorAfterIncrement (state : State) : State :=
  { state with regs := state.regs.insert minstret_increment true }

/-- The state after the active-hart parser-selected core XOR retirement. -/
def tryStepCoreXorAfterActive (state : State) (pc left right : BitVec 64) : State :=
  coreXorRetiredState (tryStepCoreXorAfterIncrement state) pc left right

/-- The state after the generated `try_step` PC-tick postlude. -/
def tryStepCoreXorAfterTick (state : State) (pc left right : BitVec 64) : State :=
  { tryStepCoreXorAfterActive state pc left right with
    regs := (tryStepCoreXorAfterActive state pc left right).regs.insert PC
      (Sail.BitVec.addInt pc 4) }

/-- The state after the generated `try_step` retired-counter write. -/
def tryStepCoreXorAfterRetired (state : State) (pc left right retired : BitVec 64) : State :=
  { tryStepCoreXorAfterTick state pc left right with
    regs := (tryStepCoreXorAfterTick state pc left right).regs.insert minstret
      (Sail.BitVec.addInt retired 1) }

/--
Lift the parser-selected generated core XOR retirement through generated `try_step`.

The explicit premises describe one runtime state and do not establish that the parser-selected
instruction is reachable at that state.
-/
theorem tryStepCoreXorRetiresWithFetchMemory (stepNo : Nat) (state : State)
    (pc left right retired : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (platform : FetchBasePlatform (tryStepCoreXorAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepCoreXorAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepCoreXorAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled (tryStepCoreXorAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepCoreXorAfterIncrement state) (tryStepCoreXorAfterIncrement state)
      (.RTYPE (Contracts.r29, Contracts.r19, Contracts.r16, .XOR)))
    (notExpected : LandingPadNotExpected (tryStepCoreXorAfterIncrement state))
    (leftRead : (coreXorNextState (tryStepCoreXorAfterIncrement state) pc).regs.get? x19 =
      some left)
    (rightRead : (coreXorNextState (tryStepCoreXorAfterIncrement state) pc).regs.get? x29 =
      some right)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepCoreXorAfterRetired state pc left right retired) false := by
  have active := runHartActiveCoreXorRetiresWithFetchMemory stepNo
    (tryStepCoreXorAfterIncrement state) pc left right byte0 byte1 byte2 byte3 platform noMMIO
    bytes interrupts base decode notExpected leftRead rightRead
  rcases platform with ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeAfterInc,
    pcLow0, pcLow1, alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩
  have privilege : state.regs.get? cur_privilege = some Privilege.Machine := by
    calc
      state.regs.get? cur_privilege =
          (tryStepCoreXorAfterIncrement state).regs.get? cur_privilege := by
            symm
            simpa [tryStepCoreXorAfterIncrement] using
              writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := privilegeAfterInc
  have shouldIncrement : Runs (should_inc_minstret Privilege.Machine) state state true :=
    shouldIncMinstretMachine state inhibit config inhibitRead configRead notInhibited machineEnabled
  have increment : Runs (Sail.writeReg minstret_increment true) state
      (tryStepCoreXorAfterIncrement state) PUnit.unit := by
    simpa [tryStepCoreXorAfterIncrement] using writeReg_run state minstret_increment true
  have hartAfterIncrement :
      (tryStepCoreXorAfterIncrement state).regs.get? hart_state = some (.HART_ACTIVE ()) := by
    calc
      (tryStepCoreXorAfterIncrement state).regs.get? hart_state = state.regs.get? hart_state := by
        simpa [tryStepCoreXorAfterIncrement] using
          writeReg_read_unchanged state minstret_increment hart_state true (by decide)
      _ = some (.HART_ACTIVE ()) := hartRead
  have hartAfterActive :
      (tryStepCoreXorAfterActive state pc left right).regs.get? hart_state =
        some (.HART_ACTIVE ()) := by
    calc
      (tryStepCoreXorAfterActive state pc left right).regs.get? hart_state =
          (coreXorNextState (tryStepCoreXorAfterIncrement state) pc).regs.get? hart_state := by
            simpa [tryStepCoreXorAfterActive, coreXorRetiredState] using
              writeReg_read_unchanged
                (coreXorNextState (tryStepCoreXorAfterIncrement state) pc) x16 hart_state
                (left ^^^ right) (by decide)
      _ = (tryStepCoreXorAfterIncrement state).regs.get? hart_state := by
        simpa [coreXorNextState] using
          writeReg_read_unchanged (tryStepCoreXorAfterIncrement state) nextPC hart_state
            (Sail.BitVec.addInt pc 4) (by decide)
      _ = some (.HART_ACTIVE ()) := hartAfterIncrement
  have nextPcAfterActive :
      (tryStepCoreXorAfterActive state pc left right).regs.get? nextPC =
        some (Sail.BitVec.addInt pc 4) := by
    calc
      (tryStepCoreXorAfterActive state pc left right).regs.get? nextPC =
          (coreXorNextState (tryStepCoreXorAfterIncrement state) pc).regs.get? nextPC := by
            simpa [tryStepCoreXorAfterActive, coreXorRetiredState] using
              writeReg_read_unchanged
                (coreXorNextState (tryStepCoreXorAfterIncrement state) pc) x16 nextPC
                (left ^^^ right) (by decide)
      _ = some (Sail.BitVec.addInt pc 4) := by
        change
          ((tryStepCoreXorAfterIncrement state).regs.insert nextPC (Sail.BitVec.addInt pc 4)).get?
              nextPC =
            some (Sail.BitVec.addInt pc 4)
        rw [Std.ExtDHashMap.get?_insert]
        simp
  have tick : Runs (tick_pc ()) (tryStepCoreXorAfterActive state pc left right)
      (tryStepCoreXorAfterTick state pc left right) () := by
    simpa [tryStepCoreXorAfterTick] using
      tickPc_run (tryStepCoreXorAfterActive state pc left right)
        (Sail.BitVec.addInt pc 4) nextPcAfterActive
  have incrementAfterWrite :
      (tryStepCoreXorAfterIncrement state).regs.get? minstret_increment = some true := by
    change (state.regs.insert minstret_increment true).get? minstret_increment = some true
    rw [Std.ExtDHashMap.get?_insert]
    simp
  have incrementAfterTick :
      (tryStepCoreXorAfterTick state pc left right).regs.get? minstret_increment = some true := by
    calc
      (tryStepCoreXorAfterTick state pc left right).regs.get? minstret_increment =
          (tryStepCoreXorAfterActive state pc left right).regs.get? minstret_increment := by
            simpa [tryStepCoreXorAfterTick] using
              writeReg_read_unchanged
                (tryStepCoreXorAfterActive state pc left right) PC minstret_increment
                (Sail.BitVec.addInt pc 4) (by decide)
      _ = (coreXorNextState (tryStepCoreXorAfterIncrement state) pc).regs.get?
          minstret_increment := by
        simpa [tryStepCoreXorAfterActive, coreXorRetiredState] using
          writeReg_read_unchanged
            (coreXorNextState (tryStepCoreXorAfterIncrement state) pc) x16 minstret_increment
            (left ^^^ right) (by decide)
      _ = (tryStepCoreXorAfterIncrement state).regs.get? minstret_increment := by
        simpa [coreXorNextState] using
          writeReg_read_unchanged (tryStepCoreXorAfterIncrement state) nextPC minstret_increment
            (Sail.BitVec.addInt pc 4) (by decide)
      _ = some true := incrementAfterWrite
  have retiredAfterTick :
      (tryStepCoreXorAfterTick state pc left right).regs.get? minstret = some retired := by
    calc
      (tryStepCoreXorAfterTick state pc left right).regs.get? minstret =
          (tryStepCoreXorAfterActive state pc left right).regs.get? minstret := by
            simpa [tryStepCoreXorAfterTick] using
              writeReg_read_unchanged
                (tryStepCoreXorAfterActive state pc left right) PC minstret
                (Sail.BitVec.addInt pc 4) (by decide)
      _ = (coreXorNextState (tryStepCoreXorAfterIncrement state) pc).regs.get? minstret := by
        simpa [tryStepCoreXorAfterActive, coreXorRetiredState] using
          writeReg_read_unchanged
            (coreXorNextState (tryStepCoreXorAfterIncrement state) pc) x16 minstret
            (left ^^^ right) (by decide)
      _ = (tryStepCoreXorAfterIncrement state).regs.get? minstret := by
        simpa [coreXorNextState] using
          writeReg_read_unchanged (tryStepCoreXorAfterIncrement state) nextPC minstret
            (Sail.BitVec.addInt pc 4) (by decide)
      _ = state.regs.get? minstret := by
        simpa [tryStepCoreXorAfterIncrement] using
          writeReg_read_unchanged state minstret_increment minstret true (by decide)
      _ = some retired := retiredRead
  have writeRetired : Runs (Sail.writeReg minstret (Sail.BitVec.addInt retired 1))
      (tryStepCoreXorAfterTick state pc left right)
      (tryStepCoreXorAfterRetired state pc left right retired) PUnit.unit := by
    simpa [tryStepCoreXorAfterRetired] using
      writeReg_run (tryStepCoreXorAfterTick state pc left right) minstret
        (Sail.BitVec.addInt retired 1)
  exact tryStepRetires stepNo state (tryStepCoreXorAfterIncrement state)
    (tryStepCoreXorAfterActive state pc left right) (tryStepCoreXorAfterTick state pc left right)
    (tryStepCoreXorAfterRetired state pc left right retired) Privilege.Machine retired
    (zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3)) privilege shouldIncrement increment
    hartAfterIncrement active hartAfterActive tick incrementAfterTick retiredAfterTick writeRetired

end BinaryFv.Keccak
