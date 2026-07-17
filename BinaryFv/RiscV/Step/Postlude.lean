import BinaryFv.RiscV.Logic.Framing

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The generated `tick_pc` reads `nextPC`, writes `PC`, and invokes its pure callback. -/
theorem tickPc_run (state : State) (next : BitVec 64)
    (nextRead : state.regs.get? nextPC = some next) :
    Runs (tick_pc ()) state { state with regs := state.regs.insert PC next } () := by
  unfold tick_pc
  apply Runs.bind (readReg_run state nextPC next nextRead)
  apply Runs.bind (writeReg_run state PC next)
  have pcRead :
      ({ state with regs := state.regs.insert PC next } : State).regs.get? PC = some next := by
    change (state.regs.insert PC next).get? PC = some next
    rw [Std.ExtDHashMap.get?_insert]
    simp
  apply Runs.bind (readReg_run { state with regs := state.regs.insert PC next } PC next pcRead)
  unfold Runs
  rfl

/-- Exact generated result of the counter-increment predicate after its two register reads. -/
theorem shouldIncMinstret_run (state : State) (privilege : Privilege)
    (inhibit : BitVec 32) (config : BitVec 64)
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config) :
    Runs (should_inc_minstret privilege) state state
      (_get_Counterin_IR inhibit == 0#1 && counter_priv_filter_bit config privilege == 0#1) := by
  unfold should_inc_minstret
  apply Runs.bind (readReg_run state mcountinhibit inhibit inhibitRead)
  apply Runs.bind (readReg_run state minstretcfg config configRead)
  unfold Runs
  rfl

/-- Machine-mode specialization of generated `should_inc_minstret` for an enabled retirement. -/
theorem shouldIncMinstretMachine (state : State) (inhibit : BitVec 32) (config : BitVec 64)
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1) :
    Runs (should_inc_minstret .Machine) state state true := by
  have exact := shouldIncMinstret_run state .Machine inhibit config inhibitRead configRead
  simpa [counter_priv_filter_bit, notInhibited, machineEnabled] using exact

end BinaryFv.RiscV
