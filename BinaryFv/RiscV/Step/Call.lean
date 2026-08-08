import BinaryFv.RiscV.Instruction.Frame.Register
import BinaryFv.RiscV.Step.ControlFlow
import BinaryFv.RiscV.Step.FallThrough
import BinaryFv.RiscV.Instruction.Decode

/-!
# Generic `try_step` packaging for calls and tail calls

Target-independent packaging of a link-writing call through the authoritative generated `try_step`:
the generalized postlude `tryStepCallRetires`, the post-execute `callLinkState` and its register
reads, and the three call shapes — a genuine `jalr` call, a direct `jal` call, and a tail call
`jr off(rs1)` (`jalr x0, …`) that discards its link.

Everything here is parameterized by pc, target, and link register. Pinning those to the addresses of
a particular binary is the target's job.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-! ## Concrete compatibility names for register-parameterized run lemmas -/

theorem wX_bits_run_x1 (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 1#5) data) s { s with regs := s.regs.insert x1 data } () :=
  wX_bits_run_nonzero .r1 s data

theorem rX_bits_run_x1 (s : State) (data : BitVec 64)
    (stored : s.regs.get? x1 = some data) :
    Runs (rX_bits (.Regidx 1#5)) s s data :=
  rX_bits_run_nonzero .r1 s data stored

theorem wX_bits_run_x5 (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 5#5) data) s { s with regs := s.regs.insert x5 data } () :=
  wX_bits_run_nonzero .r5 s data

theorem wX_bits_run_x10 (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 10#5) data) s { s with regs := s.regs.insert x10 data } () :=
  wX_bits_run_nonzero .r10 s data

theorem rX_bits_run_x10 (s : State) (data : BitVec 64)
    (stored : s.regs.get? x10 = some data) :
    Runs (rX_bits (.Regidx 10#5)) s s data :=
  rX_bits_run_nonzero .r10 s data stored

theorem rX_bits_run_x2 (s : State) (data : BitVec 64)
    (stored : s.regs.get? x2 = some data) :
    Runs (rX_bits (.Regidx 2#5)) s s data :=
  rX_bits_run_nonzero .r2 s data stored

theorem wX_bits_run_x11 (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 11#5) data) s { s with regs := s.regs.insert x11 data } () :=
  wX_bits_run_nonzero .r11 s data

theorem rX_bits_run_x11 (s : State) (data : BitVec 64)
    (stored : s.regs.get? x11 = some data) :
    Runs (rX_bits (.Regidx 11#5)) s s data :=
  rX_bits_run_nonzero .r11 s data stored

theorem rX_bits_run_x18 (s : State) (data : BitVec 64)
    (stored : s.regs.get? x18 = some data) :
    Runs (rX_bits (.Regidx 18#5)) s s data :=
  rX_bits_run_nonzero .r18 s data stored

/-- `get_next_pc ()` reads the current `nextPC`; used to pin the saved link to the return address. -/
theorem get_next_pc_run (s : State) (v : BitVec 64) (stored : s.regs.get? nextPC = some v) :
    Runs (get_next_pc ()) s s v := by
  unfold Runs
  exact readReg_run s nextPC v stored

/-! ## Shared post-increment reads -/

theorem preInc_hart (state : State) (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ())) :
    (tryStepControlFlowAfterIncrement state).regs.get? hart_state = some (.HART_ACTIVE ()) := by
  calc
    (tryStepControlFlowAfterIncrement state).regs.get? hart_state = state.regs.get? hart_state := by
      simpa [tryStepControlFlowAfterIncrement] using
        writeReg_read_unchanged state minstret_increment hart_state true (by decide)
    _ = some (.HART_ACTIVE ()) := hartRead

theorem preInc_increment (state : State) :
    (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment = some true := by
  change (state.regs.insert minstret_increment true).get? minstret_increment = some true
  rw [Std.ExtDHashMap.get?_insert]
  simp

theorem preInc_minstret (state : State) (retired : BitVec 64)
    (retiredRead : state.regs.get? minstret = some retired) :
    (tryStepControlFlowAfterIncrement state).regs.get? minstret = some retired := by
  calc
    (tryStepControlFlowAfterIncrement state).regs.get? minstret = state.regs.get? minstret := by
      simpa [tryStepControlFlowAfterIncrement] using
        writeReg_read_unchanged state minstret_increment minstret true (by decide)
    _ = some retired := retiredRead

/-! ## Generalized `try_step` postlude for a link-writing call

Identical bookkeeping to `tryStepControlFlowRetires`, but the three facts it derives from `agree`
(hart active, `minstret_increment`, `minstret` preserved across the execute) are taken as direct
premises about `afterExec`.  This accommodates the extra link-register write that a taken branch
does not perform, while still threading the exact generated postlude (`tryStepRetires`). -/
theorem tryStepCallRetires (stepNo : Nat) (state afterExec : State)
    (targetPC retired : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64) (instbits : BitVec 32)
    (privilegeAfterInc :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (active : Runs (run_hart_active stepNo) (tryStepControlFlowAfterIncrement state) afterExec
      (.Step_Execute (.Retire_Success (), instbits)))
    (nextPcAfterExec : afterExec.regs.get? nextPC = some targetPC)
    (hartAfterExec : afterExec.regs.get? hart_state = some (.HART_ACTIVE ()))
    (incrementAfterExec : afterExec.regs.get? minstret_increment = some true)
    (retiredAfterExec : afterExec.regs.get? minstret = some retired)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1) :
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
      (tryStepControlFlowAfterIncrement state).regs.get? hart_state = some (.HART_ACTIVE ()) :=
    preInc_hart state hartRead
  have tick : Runs (tick_pc ()) afterExec (tryStepControlFlowAfterTick afterExec targetPC) () := by
    simpa [tryStepControlFlowAfterTick] using tickPc_run afterExec targetPC nextPcAfterExec
  have incrementAfterTick :
      (tryStepControlFlowAfterTick afterExec targetPC).regs.get? minstret_increment = some true := by
    calc
      (tryStepControlFlowAfterTick afterExec targetPC).regs.get? minstret_increment =
          afterExec.regs.get? minstret_increment := by
            simpa [tryStepControlFlowAfterTick] using
              writeReg_read_unchanged afterExec PC minstret_increment targetPC (by decide)
      _ = some true := incrementAfterExec
  have retiredAfterTick :
      (tryStepControlFlowAfterTick afterExec targetPC).regs.get? minstret = some retired := by
    calc
      (tryStepControlFlowAfterTick afterExec targetPC).regs.get? minstret =
          afterExec.regs.get? minstret := by
            simpa [tryStepControlFlowAfterTick] using
              writeReg_read_unchanged afterExec PC minstret targetPC (by decide)
      _ = some retired := retiredAfterExec
  have writeRetired : Runs (Sail.writeReg minstret (Sail.BitVec.addInt retired 1))
      (tryStepControlFlowAfterTick afterExec targetPC)
      (tryStepControlFlowAfterRetired afterExec targetPC retired) PUnit.unit := by
    simpa [tryStepControlFlowAfterRetired] using
      writeReg_run (tryStepControlFlowAfterTick afterExec targetPC) minstret
        (Sail.BitVec.addInt retired 1)
  exact tryStepRetires stepNo state (tryStepControlFlowAfterIncrement state) afterExec
    (tryStepControlFlowAfterTick afterExec targetPC)
    (tryStepControlFlowAfterRetired afterExec targetPC retired) Privilege.Machine retired instbits
    privilege shouldIncrement increment hartAfterIncrement active hartAfterExec tick
    incrementAfterTick retiredAfterTick writeRetired

/-! ## The link-writing post-execute state and its register reads -/

/-- Post-execute state of a link-writing call: the taken-jump state (`nextPC ↦ target`) with the
return address additionally written into the link register. -/
def callLinkState (state : State) (pc target : BitVec 64) (linkReg : Register)
    (linkVal : RegisterType linkReg) : State :=
  { controlFlowJumpState state pc target with
    regs := (controlFlowJumpState state pc target).regs.insert linkReg linkVal }

/-- Any register other than `nextPC` and the link register reads through `callLinkState` to the
pre-execute (post-increment) value. -/
theorem callLinkState_read (state : State) (pc target : BitVec 64) (linkReg : Register)
    (linkVal : RegisterType linkReg) (r : Register) (hrLink : r ≠ linkReg) (hrNext : r ≠ nextPC) :
    (callLinkState state pc target linkReg linkVal).regs.get? r = state.regs.get? r := by
  calc
    (callLinkState state pc target linkReg linkVal).regs.get? r =
        (controlFlowJumpState state pc target).regs.get? r := by
          simpa [callLinkState] using
            writeReg_read_unchanged (controlFlowJumpState state pc target) linkReg r linkVal hrLink
    _ = (coreControlFlowNextState state pc).regs.get? r := by
          simpa [controlFlowJumpState] using
            writeReg_read_unchanged (coreControlFlowNextState state pc) nextPC r target hrNext
    _ = state.regs.get? r := by
          simpa [coreControlFlowNextState] using
            writeReg_read_unchanged state nextPC r (Sail.BitVec.addInt pc 4) hrNext

/-- `nextPC` reads through `callLinkState` to the jump target (the link write leaves it alone). -/
theorem callLinkState_nextPc (state : State) (pc target : BitVec 64) (linkReg : Register)
    (linkVal : RegisterType linkReg) (hLinkNext : linkReg ≠ nextPC) :
    (callLinkState state pc target linkReg linkVal).regs.get? nextPC = some target := by
  calc
    (callLinkState state pc target linkReg linkVal).regs.get? nextPC =
        (controlFlowJumpState state pc target).regs.get? nextPC := by
          simpa [callLinkState] using
            writeReg_read_unchanged (controlFlowJumpState state pc target) linkReg nextPC linkVal
              (Ne.symm hLinkNext)
    _ = some target := by
          change ((coreControlFlowNextState state pc).regs.insert nextPC target).get? nextPC =
            some target
          rw [Std.ExtDHashMap.get?_insert]
          simp

/-- The link register reads through `callLinkState` to the saved link value. -/
theorem callLinkState_link (state : State) (pc target : BitVec 64) (linkReg : Register)
    (linkVal : RegisterType linkReg) :
    (callLinkState state pc target linkReg linkVal).regs.get? linkReg = some linkVal := by
  change ((controlFlowJumpState state pc target).regs.insert linkReg linkVal).get? linkReg =
    some linkVal
  rw [Std.ExtDHashMap.get?_insert]
  simp

/-- A retired link-writing call preserves every register outside its link, control-flow, and
retirement bookkeeping registers. -/
theorem jalrCallAfterRetired_agree_of {P : Register → Prop} (state : State)
    (pc target retired : BitVec 64) (linkReg : Register) (linkVal : RegisterType linkReg)
    (notLink : ¬ P linkReg) (notPc : ¬ P PC) (notNextPc : ¬ P nextPC)
    (notIncrement : ¬ P minstret_increment) (notRetired : ¬ P minstret) :
    Agree P state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) pc target linkReg linkVal)
        target retired) := by
  intro register preserved
  have differentLink : linkReg ≠ register := by
    intro equal
    exact notLink (equal ▸ preserved)
  have differentPc : PC ≠ register := by
    intro equal
    exact notPc (equal ▸ preserved)
  have differentNextPc : nextPC ≠ register := by
    intro equal
    exact notNextPc (equal ▸ preserved)
  have differentIncrement : minstret_increment ≠ register := by
    intro equal
    exact notIncrement (equal ▸ preserved)
  have differentRetired : minstret ≠ register := by
    intro equal
    exact notRetired (equal ▸ preserved)
  simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, callLinkState,
    controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
    Std.ExtDHashMap.get?_insert, differentLink, differentPc, differentNextPc,
    differentIncrement, differentRetired]

theorem jalrCallAfterRetired_mem (state : State) (pc target retired : BitVec 64)
    (linkReg : Register) (linkVal : RegisterType linkReg) :
    (tryStepControlFlowAfterRetired
      (callLinkState (tryStepControlFlowAfterIncrement state) pc target linkReg linkVal)
      target retired).mem = state.mem := rfl

/-! ## Genuine `jalr` call, lifted through `try_step`

The auipc-relative target is `Sail.BitVec.update (rs1Val + sext imm) 0 0#1`, where `rs1Val` is the
value the preceding `auipc` wrote into the base register.  The link `linkVal` is the pre-execute
`nextPC` (`= pc + 4`, the return address).  `rd`, `linkReg`, and its disjointness from the
counter/hart registers are explicit, so any concrete link register (`ra`, `t0`, …) applies. -/
theorem tryStepJalrCallRetires (stepNo : Nat) (state : State)
    (pc rs1Val retired linkVal : BitVec 64) (imm : BitVec 12) (rs1 rd : regidx)
    (linkReg : Register) (linkRegVal : RegisterType linkReg)
    (inhibit : BitVec 32) (config : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (zcaEnabled : Bool)
    (hwrite : Runs (wX_bits rd linkVal)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1))
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) linkReg linkRegVal) ())
    (linkNeNext : linkReg ≠ nextPC) (linkNeHart : linkReg ≠ hart_state)
    (linkNeInc : linkReg ≠ minstret_increment) (linkNeRetired : linkReg ≠ minstret)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (imm, rs1, rd)))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (helpElp : Runs (update_elp_state rs1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) ())
    (hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) linkVal)
    (hrs1 : Runs (rX_bits rs1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) rs1Val)
    (hbit1 : Sail.BitVec.access (rs1Val + sign_extend (m := 64) imm) 1 = 0#1)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) zcaEnabled)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) pc
          (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) linkReg linkRegVal)
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) retired) false := by
  have exec : Runs (execute (.JALR (imm, rs1, rd)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) linkReg linkRegVal)
      (.Retire_Success ()) := by
    change Runs (execute_JALR imm rs1 rd) _ _ _
    exact execute_JALR_run (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) linkReg linkRegVal)
      imm rs1 rd linkVal rs1Val helpElp hlink hrs1 hbit1 zcaEnabled hzca hwrite
  have active := runHartActiveControlFlow stepNo (tryStepControlFlowAfterIncrement state)
    (callLinkState (tryStepControlFlowAfterIncrement state) pc
      (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) linkReg linkRegVal)
    pc byte0 byte1 byte2 byte3 (.JALR (imm, rs1, rd)) platform noMMIO bytes interrupts base decode
    notExpected exec
  have nextPcAfterExec :
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) linkReg
        linkRegVal).regs.get? nextPC =
        some (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) :=
    callLinkState_nextPc (tryStepControlFlowAfterIncrement state) pc _ linkReg linkRegVal linkNeNext
  have hartAfterExec :
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) linkReg
        linkRegVal).regs.get? hart_state = some (.HART_ACTIVE ()) := by
    rw [callLinkState_read (tryStepControlFlowAfterIncrement state) pc _ linkReg linkRegVal
      hart_state (Ne.symm linkNeHart) (by decide)]
    exact preInc_hart state hartRead
  have incrementAfterExec :
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) linkReg
        linkRegVal).regs.get? minstret_increment = some true := by
    rw [callLinkState_read (tryStepControlFlowAfterIncrement state) pc _ linkReg linkRegVal
      minstret_increment (Ne.symm linkNeInc) (by decide)]
    exact preInc_increment state
  have retiredAfterExec :
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) linkReg
        linkRegVal).regs.get? minstret = some retired := by
    rw [callLinkState_read (tryStepControlFlowAfterIncrement state) pc _ linkReg linkRegVal
      minstret (Ne.symm linkNeRetired) (by decide)]
    exact preInc_minstret state retired retiredRead
  rcases platform with ⟨_, _, _, _, _, privilegeAfterInc, _⟩
  exact tryStepCallRetires stepNo state
    (callLinkState (tryStepControlFlowAfterIncrement state) pc
      (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) linkReg linkRegVal)
    (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) retired inhibit config
    (zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3)) privilegeAfterInc active
    nextPcAfterExec hartAfterExec incrementAfterExec retiredAfterExec hartRead inhibitRead
    configRead notInhibited machineEnabled

/-! ## Genuine `jal` call, lifted through `try_step`

Same shape, but the target is `PC + sext imm` (no register base, no bit-0 clear), and `PC` is read
during execute rather than a source register. -/
theorem tryStepJalCallRetires (stepNo : Nat) (state : State)
    (pc pcVal retired linkVal : BitVec 64) (imm : BitVec 21) (rd : regidx)
    (linkReg : Register) (linkRegVal : RegisterType linkReg)
    (inhibit : BitVec 32) (config : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (zcaEnabled : Bool)
    (hwrite : Runs (wX_bits rd linkVal)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (pcVal + sign_extend (m := 64) imm))
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (pcVal + sign_extend (m := 64) imm) linkReg linkRegVal) ())
    (linkNeNext : linkReg ≠ nextPC) (linkNeHart : linkReg ≠ hart_state)
    (linkNeInc : linkReg ≠ minstret_increment) (linkNeRetired : linkReg ≠ minstret)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (imm, rd)))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) linkVal)
    (hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) pcVal)
    (halign : Sail.BitVec.access (pcVal + sign_extend (m := 64) imm) 0 = 0#1)
    (hbit1 : Sail.BitVec.access (pcVal + sign_extend (m := 64) imm) 1 = 0#1)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) zcaEnabled)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) pc
          (pcVal + sign_extend (m := 64) imm) linkReg linkRegVal)
        (pcVal + sign_extend (m := 64) imm) retired) false := by
  have exec : Runs (execute (.JAL (imm, rd)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (pcVal + sign_extend (m := 64) imm) linkReg linkRegVal) (.Retire_Success ()) := by
    change Runs (execute_JAL imm rd) _ _ _
    exact execute_JAL_run (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (pcVal + sign_extend (m := 64) imm) linkReg linkRegVal)
      imm rd linkVal pcVal hlink hpc halign hbit1 zcaEnabled hzca hwrite
  have active := runHartActiveControlFlow stepNo (tryStepControlFlowAfterIncrement state)
    (callLinkState (tryStepControlFlowAfterIncrement state) pc
      (pcVal + sign_extend (m := 64) imm) linkReg linkRegVal)
    pc byte0 byte1 byte2 byte3 (.JAL (imm, rd)) platform noMMIO bytes interrupts base decode
    notExpected exec
  have nextPcAfterExec :
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (pcVal + sign_extend (m := 64) imm) linkReg linkRegVal).regs.get? nextPC =
        some (pcVal + sign_extend (m := 64) imm) :=
    callLinkState_nextPc (tryStepControlFlowAfterIncrement state) pc _ linkReg linkRegVal linkNeNext
  have hartAfterExec :
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (pcVal + sign_extend (m := 64) imm) linkReg linkRegVal).regs.get? hart_state =
        some (.HART_ACTIVE ()) := by
    rw [callLinkState_read (tryStepControlFlowAfterIncrement state) pc _ linkReg linkRegVal
      hart_state (Ne.symm linkNeHart) (by decide)]
    exact preInc_hart state hartRead
  have incrementAfterExec :
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (pcVal + sign_extend (m := 64) imm) linkReg linkRegVal).regs.get? minstret_increment =
        some true := by
    rw [callLinkState_read (tryStepControlFlowAfterIncrement state) pc _ linkReg linkRegVal
      minstret_increment (Ne.symm linkNeInc) (by decide)]
    exact preInc_increment state
  have retiredAfterExec :
      (callLinkState (tryStepControlFlowAfterIncrement state) pc
        (pcVal + sign_extend (m := 64) imm) linkReg linkRegVal).regs.get? minstret = some retired := by
    rw [callLinkState_read (tryStepControlFlowAfterIncrement state) pc _ linkReg linkRegVal
      minstret (Ne.symm linkNeRetired) (by decide)]
    exact preInc_minstret state retired retiredRead
  rcases platform with ⟨_, _, _, _, _, privilegeAfterInc, _⟩
  exact tryStepCallRetires stepNo state
    (callLinkState (tryStepControlFlowAfterIncrement state) pc
      (pcVal + sign_extend (m := 64) imm) linkReg linkRegVal)
    (pcVal + sign_extend (m := 64) imm) retired inhibit config
    (zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3)) privilegeAfterInc active
    nextPcAfterExec hartAfterExec incrementAfterExec retiredAfterExec hartRead inhibitRead
    configRead notInhibited machineEnabled

/-! ## Tail call `jr off(rs1)` (`jalr x0, off(rs1)`), lifted through `try_step`

The link is written to `x0` and discarded, so `afterExec` touches only `nextPC` and the branch
postlude `tryStepControlFlowRetires` applies directly.  Generalizes `tryStepRetRetires` to a
nonzero offset (`ret` is the `off = 0`, `rs1 = ra` special case). -/
theorem tryStepJrDiscardRetires (stepNo : Nat) (state : State)
    (pc rs1Val retired : BitVec 64) (imm : BitVec 12) (rs1 : regidx) (linkVal : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (zcaEnabled : Bool)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (imm, rs1, .Regidx 0#5)))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (helpElp : Runs (update_elp_state rs1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) ())
    (hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) linkVal)
    (hrs1 : Runs (rX_bits rs1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) rs1Val)
    (hbit1 : Sail.BitVec.access (rs1Val + sign_extend (m := 64) imm) 1 = 0#1)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) zcaEnabled)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
          (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1))
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) retired) false := by
  have exec : Runs (execute (.JALR (imm, rs1, .Regidx 0#5)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)) (.Retire_Success ()) := by
    change Runs (execute_JALR imm rs1 (.Regidx 0#5)) _ _ _
    unfold controlFlowJumpState
    exact execute_JALR_run (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) _
      imm rs1 (.Regidx 0#5) linkVal rs1Val helpElp hlink hrs1 hbit1 zcaEnabled hzca
      (wX_bits_run_zero _ linkVal)
  have active := runHartActiveControlFlow stepNo (tryStepControlFlowAfterIncrement state)
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
      (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)) pc byte0 byte1 byte2 byte3
    (.JALR (imm, rs1, .Regidx 0#5)) platform noMMIO bytes interrupts base decode notExpected exec
  have nextPcAfterExec :
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)).regs.get? nextPC =
        some (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) := by
    change ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert nextPC
      (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)).get? nextPC =
      some (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)
    rw [Std.ExtDHashMap.get?_insert]
    simp
  have agree : ∀ r : Register, r ≠ nextPC →
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)).regs.get? r =
        (tryStepControlFlowAfterIncrement state).regs.get? r := by
    intro r hr
    calc
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
          (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)).regs.get? r =
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? r := by
            simpa [controlFlowJumpState] using
              writeReg_read_unchanged
                (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) nextPC r
                (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) hr
      _ = (tryStepControlFlowAfterIncrement state).regs.get? r := by
            simpa [coreControlFlowNextState] using
              writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC r
                (Sail.BitVec.addInt pc 4) hr
  rcases platform with ⟨_, _, _, _, _, privilegeAfterInc, _⟩
  exact tryStepControlFlowRetires stepNo state
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
      (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1))
    (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) retired inhibit config
    (zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3)) privilegeAfterInc active
    nextPcAfterExec agree hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

end BinaryFv.RiscV
