import BinaryFv.RiscV.Step.Postlude
import BinaryFv.RiscV.Step.StackAddi
import BinaryFv.RiscV.Step.TryStep

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The state after the generated `try_step` counter-increment write. -/
def tryStepStackAddiAfterIncrement (state : State) : State :=
  { state with regs := state.regs.insert minstret_increment true }

/-- The state after the active-hart `addi sp, sp, immediate` retirement. -/
def tryStepStackAddiAfterActive (state : State) (pc : BitVec 64) (immediate : BitVec 12)
    (stackValue : BitVec 64) : State :=
  stackAddiRetiredState (tryStepStackAddiAfterIncrement state) pc immediate stackValue

/-- The state after the generated `try_step` PC-tick postlude. -/
def tryStepStackAddiAfterTick (state : State) (pc : BitVec 64) (immediate : BitVec 12)
    (stackValue : BitVec 64) : State :=
  { tryStepStackAddiAfterActive state pc immediate stackValue with
    regs := (tryStepStackAddiAfterActive state pc immediate stackValue).regs.insert PC
      (Sail.BitVec.addInt pc 4) }

/-- The state after the generated `try_step` retired-counter write. -/
def tryStepStackAddiAfterRetired (state : State) (pc : BitVec 64) (immediate : BitVec 12)
    (stackValue retired : BitVec 64) : State :=
  { tryStepStackAddiAfterTick state pc immediate stackValue with
    regs := (tryStepStackAddiAfterTick state pc immediate stackValue).regs.insert minstret
      (Sail.BitVec.addInt retired 1) }

/-- Lift an arbitrary generated `addi sp, sp, immediate` retirement through generated `try_step`. -/
theorem tryStepStackAddiRetires (stepNo : Nat) (state : State) (pc : BitVec 64)
    (immediate : BitVec 12) (stackValue retired : BitVec 64) (inhibit : BitVec 32)
    (config : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (platform : FetchBasePlatform (tryStepStackAddiAfterIncrement state) pc)
    (interrupts : InterruptDisabled (tryStepStackAddiAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (fetchBytes : FetchBytesBaseContract (tryStepStackAddiAfterIncrement state) pc
      byte0 byte1 byte2 byte3)
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
    Runs (try_step stepNo false) state
      (tryStepStackAddiAfterRetired state pc immediate stackValue retired) false := by
  have active := runHartActiveStackAddiRetires stepNo (tryStepStackAddiAfterIncrement state) pc
    immediate stackValue byte0 byte1 byte2 byte3 platform interrupts base fetchBytes decode
    notExpected stackRead
  rcases platform with ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeAfterInc,
    pcLow0, pcLow1, alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩
  have privilege : state.regs.get? cur_privilege = some Privilege.Machine := by
    calc
      state.regs.get? cur_privilege =
          (tryStepStackAddiAfterIncrement state).regs.get? cur_privilege := by
            symm
            simpa [tryStepStackAddiAfterIncrement] using
              writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := privilegeAfterInc
  have shouldIncrement : Runs (should_inc_minstret Privilege.Machine) state state true :=
    shouldIncMinstretMachine state inhibit config inhibitRead configRead notInhibited machineEnabled
  have increment : Runs (Sail.writeReg minstret_increment true) state
      (tryStepStackAddiAfterIncrement state) PUnit.unit := by
    simpa [tryStepStackAddiAfterIncrement] using writeReg_run state minstret_increment true
  have hartAfterIncrement :
      (tryStepStackAddiAfterIncrement state).regs.get? hart_state = some (.HART_ACTIVE ()) := by
    calc
      (tryStepStackAddiAfterIncrement state).regs.get? hart_state = state.regs.get? hart_state := by
        simpa [tryStepStackAddiAfterIncrement] using
          writeReg_read_unchanged state minstret_increment hart_state true (by decide)
      _ = some (.HART_ACTIVE ()) := hartRead
  have hartAfterActive :
      (tryStepStackAddiAfterActive state pc immediate stackValue).regs.get? hart_state =
        some (.HART_ACTIVE ()) := by
    calc
      (tryStepStackAddiAfterActive state pc immediate stackValue).regs.get? hart_state =
          (stackAddiNextState (tryStepStackAddiAfterIncrement state) pc).regs.get? hart_state := by
            simpa [tryStepStackAddiAfterActive, stackAddiRetiredState] using
              writeReg_read_unchanged
                (stackAddiNextState (tryStepStackAddiAfterIncrement state) pc) x2 hart_state
                (stackValue + sign_extend (m := 64) immediate) (by decide)
      _ = (tryStepStackAddiAfterIncrement state).regs.get? hart_state := by
        simpa [stackAddiNextState] using
          writeReg_read_unchanged (tryStepStackAddiAfterIncrement state) nextPC hart_state
            (Sail.BitVec.addInt pc 4) (by decide)
      _ = some (.HART_ACTIVE ()) := hartAfterIncrement
  have nextPcAfterActive :
      (tryStepStackAddiAfterActive state pc immediate stackValue).regs.get? nextPC =
        some (Sail.BitVec.addInt pc 4) := by
    calc
      (tryStepStackAddiAfterActive state pc immediate stackValue).regs.get? nextPC =
          (stackAddiNextState (tryStepStackAddiAfterIncrement state) pc).regs.get? nextPC := by
            simpa [tryStepStackAddiAfterActive, stackAddiRetiredState] using
              writeReg_read_unchanged
                (stackAddiNextState (tryStepStackAddiAfterIncrement state) pc) x2 nextPC
                (stackValue + sign_extend (m := 64) immediate) (by decide)
      _ = some (Sail.BitVec.addInt pc 4) := by
        change
          ((tryStepStackAddiAfterIncrement state).regs.insert nextPC (Sail.BitVec.addInt pc 4)).get?
              nextPC =
            some (Sail.BitVec.addInt pc 4)
        rw [Std.ExtDHashMap.get?_insert]
        simp
  have tick : Runs (tick_pc ()) (tryStepStackAddiAfterActive state pc immediate stackValue)
      (tryStepStackAddiAfterTick state pc immediate stackValue) () := by
    simpa [tryStepStackAddiAfterTick] using
      tickPc_run (tryStepStackAddiAfterActive state pc immediate stackValue)
        (Sail.BitVec.addInt pc 4) nextPcAfterActive
  have incrementAfterWrite :
      (tryStepStackAddiAfterIncrement state).regs.get? minstret_increment = some true := by
    change (state.regs.insert minstret_increment true).get? minstret_increment = some true
    rw [Std.ExtDHashMap.get?_insert]
    simp
  have incrementAfterTick :
      (tryStepStackAddiAfterTick state pc immediate stackValue).regs.get? minstret_increment =
        some true := by
    calc
      (tryStepStackAddiAfterTick state pc immediate stackValue).regs.get? minstret_increment =
          (tryStepStackAddiAfterActive state pc immediate stackValue).regs.get?
            minstret_increment := by
            simpa [tryStepStackAddiAfterTick] using
              writeReg_read_unchanged
                (tryStepStackAddiAfterActive state pc immediate stackValue) PC minstret_increment
                (Sail.BitVec.addInt pc 4) (by decide)
      _ = (stackAddiNextState (tryStepStackAddiAfterIncrement state) pc).regs.get?
          minstret_increment := by
        simpa [tryStepStackAddiAfterActive, stackAddiRetiredState] using
          writeReg_read_unchanged
            (stackAddiNextState (tryStepStackAddiAfterIncrement state) pc) x2 minstret_increment
            (stackValue + sign_extend (m := 64) immediate) (by decide)
      _ = (tryStepStackAddiAfterIncrement state).regs.get? minstret_increment := by
        simpa [stackAddiNextState] using
          writeReg_read_unchanged (tryStepStackAddiAfterIncrement state) nextPC minstret_increment
            (Sail.BitVec.addInt pc 4) (by decide)
      _ = some true := incrementAfterWrite
  have retiredAfterTick :
      (tryStepStackAddiAfterTick state pc immediate stackValue).regs.get? minstret =
        some retired := by
    calc
      (tryStepStackAddiAfterTick state pc immediate stackValue).regs.get? minstret =
          (tryStepStackAddiAfterActive state pc immediate stackValue).regs.get? minstret := by
            simpa [tryStepStackAddiAfterTick] using
              writeReg_read_unchanged
                (tryStepStackAddiAfterActive state pc immediate stackValue) PC minstret
                (Sail.BitVec.addInt pc 4) (by decide)
      _ = (stackAddiNextState (tryStepStackAddiAfterIncrement state) pc).regs.get? minstret := by
        simpa [tryStepStackAddiAfterActive, stackAddiRetiredState] using
          writeReg_read_unchanged
            (stackAddiNextState (tryStepStackAddiAfterIncrement state) pc) x2 minstret
            (stackValue + sign_extend (m := 64) immediate) (by decide)
      _ = (tryStepStackAddiAfterIncrement state).regs.get? minstret := by
        simpa [stackAddiNextState] using
          writeReg_read_unchanged (tryStepStackAddiAfterIncrement state) nextPC minstret
            (Sail.BitVec.addInt pc 4) (by decide)
      _ = state.regs.get? minstret := by
        simpa [tryStepStackAddiAfterIncrement] using
          writeReg_read_unchanged state minstret_increment minstret true (by decide)
      _ = some retired := retiredRead
  have writeRetired : Runs (Sail.writeReg minstret (Sail.BitVec.addInt retired 1))
      (tryStepStackAddiAfterTick state pc immediate stackValue)
      (tryStepStackAddiAfterRetired state pc immediate stackValue retired) PUnit.unit := by
    simpa [tryStepStackAddiAfterRetired] using
      writeReg_run (tryStepStackAddiAfterTick state pc immediate stackValue) minstret
        (Sail.BitVec.addInt retired 1)
  exact tryStepRetires stepNo state (tryStepStackAddiAfterIncrement state)
    (tryStepStackAddiAfterActive state pc immediate stackValue)
    (tryStepStackAddiAfterTick state pc immediate stackValue)
    (tryStepStackAddiAfterRetired state pc immediate stackValue retired) Privilege.Machine retired
    (zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3)) privilege shouldIncrement increment
    hartAfterIncrement active hartAfterActive tick incrementAfterTick retiredAfterTick writeRetired

end BinaryFv.RiscV
