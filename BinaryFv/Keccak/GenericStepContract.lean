import BinaryFv.Keccak.CoreBranchStepContract

/-!
# A generic normal-execution `try_step` postlude for any retiring instruction

The stage-3 `tryStepControlFlowRetires` packages the branch/`ret` execute contracts through the
authoritative generated `try_step`, but its `agree` premise demands that *every* register other than
`nextPC` be unchanged by `execute`.  That holds for branches and `ret` (which write no
general-purpose register, or only the discarded `x0` link), but not for the arithmetic / load / byte
store instructions in the memcpy/memset/`copy_from_slice` loop bodies, whose `execute` writes a
destination register or a memory byte.

Inspecting that proof shows the blanket `agree` is only ever *used* at three registers —
`hart_state`, `minstret_increment`, and `minstret` — because those are the only reads the `try_step`
counter/postlude bookkeeping performs on the post-execute state.  This module factors that out: the
same postlude, but with `agree` replaced by three targeted preservation premises.  It therefore lifts
*any* retiring instruction whose `execute` leaves those three registers (and `nextPC`, exposed as
`targetPC`) determined, covering both the control-flow instructions (as a specialization) and the
straight-line body instructions of the memory helpers.

The definitions `tryStepControlFlowAfterIncrement / …Tick / …Retired` and `coreControlFlowNextState`
are reused verbatim from `CoreBranchStepContract`; only the packaging premise shape changes.
-/

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV

/--
Generic `try_step` postlude, parameterized by the opaque post-execute state `afterExec`.

`afterExec` is constrained only by what the counter/postlude bookkeeping actually reads: its `nextPC`
holds `targetPC` (copied into `PC` by `tick_pc`), and its `hart_state` / `minstret_increment` /
`minstret` agree with the post-increment state (the `execute` touched none of them).  This subsumes
`tryStepControlFlowRetires` (whose blanket `agree` implies all three) and additionally applies to
GP-register-writing and memory-writing fall-through instructions.
-/
theorem tryStepGenericRetires (stepNo : Nat) (state afterExec : State)
    (targetPC retired : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64) (instbits : BitVec 32)
    (privilegeAfterInc :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (active : Runs (run_hart_active stepNo) (tryStepControlFlowAfterIncrement state) afterExec
      (.Step_Execute (.Retire_Success (), instbits)))
    (nextPcAfterExec : afterExec.regs.get? nextPC = some targetPC)
    (hartAgree :
      afterExec.regs.get? hart_state =
        (tryStepControlFlowAfterIncrement state).regs.get? hart_state)
    (incAgree :
      afterExec.regs.get? minstret_increment =
        (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment)
    (retAgree :
      afterExec.regs.get? minstret = (tryStepControlFlowAfterIncrement state).regs.get? minstret)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired afterExec targetPC retired) false := by
  have privilege : state.regs.get? cur_privilege = some Privilege.Machine := by
    calc
      state.regs.get? cur_privilege =
          (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege := by
            symm
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := privilegeAfterInc
  have shouldIncrement : Runs (should_inc_minstret Privilege.Machine) state state true :=
    shouldIncMinstretMachine state inhibit config inhibitRead configRead notInhibited machineEnabled
  have increment : Runs (Sail.writeReg minstret_increment true) state
      (tryStepControlFlowAfterIncrement state) PUnit.unit := by
    simpa [tryStepControlFlowAfterIncrement] using writeReg_run state minstret_increment true
  have hartAfterIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? hart_state = some (.HART_ACTIVE ()) := by
    calc
      (tryStepControlFlowAfterIncrement state).regs.get? hart_state =
          state.regs.get? hart_state := by
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment hart_state true (by decide)
      _ = some (.HART_ACTIVE ()) := hartRead
  have hartAfterActive : afterExec.regs.get? hart_state = some (.HART_ACTIVE ()) := by
    rw [hartAgree]; exact hartAfterIncrement
  have tick : Runs (tick_pc ()) afterExec (tryStepControlFlowAfterTick afterExec targetPC) () := by
    simpa [tryStepControlFlowAfterTick] using tickPc_run afterExec targetPC nextPcAfterExec
  have incrementAfterInc :
      (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment = some true := by
    change (state.regs.insert minstret_increment true).get? minstret_increment = some true
    rw [Std.ExtDHashMap.get?_insert]
    simp
  have incrementAfterTick :
      (tryStepControlFlowAfterTick afterExec targetPC).regs.get? minstret_increment = some true := by
    calc
      (tryStepControlFlowAfterTick afterExec targetPC).regs.get? minstret_increment =
          afterExec.regs.get? minstret_increment := by
            simpa [tryStepControlFlowAfterTick] using
              writeReg_read_unchanged afterExec PC minstret_increment targetPC (by decide)
      _ = (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment := incAgree
      _ = some true := incrementAfterInc
  have retiredAfterTick :
      (tryStepControlFlowAfterTick afterExec targetPC).regs.get? minstret = some retired := by
    calc
      (tryStepControlFlowAfterTick afterExec targetPC).regs.get? minstret =
          afterExec.regs.get? minstret := by
            simpa [tryStepControlFlowAfterTick] using
              writeReg_read_unchanged afterExec PC minstret targetPC (by decide)
      _ = (tryStepControlFlowAfterIncrement state).regs.get? minstret := retAgree
      _ = state.regs.get? minstret := by
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment minstret true (by decide)
      _ = some retired := retiredRead
  have writeRetired : Runs (Sail.writeReg minstret (Sail.BitVec.addInt retired 1))
      (tryStepControlFlowAfterTick afterExec targetPC)
      (tryStepControlFlowAfterRetired afterExec targetPC retired) PUnit.unit := by
    simpa [tryStepControlFlowAfterRetired] using
      writeReg_run (tryStepControlFlowAfterTick afterExec targetPC) minstret
        (Sail.BitVec.addInt retired 1)
  exact tryStepRetires stepNo state (tryStepControlFlowAfterIncrement state) afterExec
    (tryStepControlFlowAfterTick afterExec targetPC)
    (tryStepControlFlowAfterRetired afterExec targetPC retired) Privilege.Machine retired instbits
    privilege shouldIncrement increment hartAfterIncrement active hartAfterActive tick
    incrementAfterTick retiredAfterTick writeRetired

/-- `tryStepControlFlowRetires` is the special case where `execute` leaves *every* register but
`nextPC` unchanged; the three targeted preservation premises follow from the blanket `agree`. -/
theorem tryStepControlFlowRetires_of_generic (stepNo : Nat) (state afterExec : State)
    (targetPC retired : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64) (instbits : BitVec 32)
    (privilegeAfterInc :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (active : Runs (run_hart_active stepNo) (tryStepControlFlowAfterIncrement state) afterExec
      (.Step_Execute (.Retire_Success (), instbits)))
    (nextPcAfterExec : afterExec.regs.get? nextPC = some targetPC)
    (agree : ∀ r : Register, r ≠ nextPC →
      afterExec.regs.get? r = (tryStepControlFlowAfterIncrement state).regs.get? r)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired afterExec targetPC retired) false :=
  tryStepGenericRetires stepNo state afterExec targetPC retired inhibit config instbits
    privilegeAfterInc active nextPcAfterExec (agree hart_state (by decide))
    (agree minstret_increment (by decide)) (agree minstret (by decide)) hartRead inhibitRead
    configRead notInhibited machineEnabled retiredRead

end BinaryFv.Keccak
