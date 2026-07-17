import BinaryFv.Keccak.CoreTryStepContract
import BinaryFv.RISCV.ControlFlowStep
import BinaryFv.RISCV.SailEnumAux

/-!
# Normal-execution `try_step` rules for control-flow instructions

This module packages the delivered control-flow execute contracts (`execute_BTYPE_taken_run`,
`execute_BTYPE_notTaken_run`, `ret_run` from `ControlFlowStep`) through the authoritative generated
`try_step`, exactly mirroring how the fixed XOR slice (`CoreTryStepContract`) and the real-ELF store
(`CoreStoreStepContract`) are packaged.

These are the control-flow analogue of `tryStepCoreStoreRetires`: a conditional `BTYPE` (both taken
and not-taken) and the `ret` pseudo-instruction (`jalr x0, 0(rs1)`), lifted through the generated
`try_step` postlude.  They are the rules the `xor_block` loop's `bnez`/`beqz`/`ret` need.

The one structural difference from the store/XOR packaging is that a *taken* branch (or `ret`)
overwrites `nextPC` (set to `pc+4` by the generated base path) with the jump *target*, so the
postlude `tick_pc` copies `PC := nextPC = target` rather than the fall-through `pc+4`.  The register
bookkeeping is otherwise identical: the control-flow execute writes only `nextPC` (branch) or
`nextPC` plus a discarded `x0` link (ret), so the increment/tick/retired framing carries over.  This
is captured once by `tryStepControlFlowRetires`, whose only per-instruction inputs are the exact
`nextPC` value in the post-execute state and the fact that every other register agrees with the
pre-execute state.

Unlike the store contract these lemmas are kept fully generic over `pc`/`word`: the fetch bytes and
the `ext_decode` result are explicit premises, so the same rule applies at any control-flow site.
-/

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RISCV

/-! ## Post-states of the generated base path -/

/-- The state after the base-instruction path writes the generated next PC (`pc+4`); shared by every
control-flow instruction before its own execute overwrites `nextPC` on a taken jump. -/
def coreControlFlowNextState (state : State) (pc : BitVec 64) : State :=
  { state with regs := state.regs.insert nextPC (Sail.BitVec.addInt pc 4) }

/-- The state after a taken branch (or `ret`) overwrites `nextPC` with the jump `target`. -/
def controlFlowJumpState (state : State) (pc target : BitVec 64) : State :=
  { coreControlFlowNextState state pc with
    regs := (coreControlFlowNextState state pc).regs.insert nextPC target }

/-! ## Lifting the control-flow execute contracts through the `execute` dispatcher -/

/-- Taken conditional branch, lifted through the `execute` dispatcher. -/
theorem executeBranchTakenDispatchRuns (s : State) (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop)
    (pcVal : BitVec 64)
    (hcond : Runs (bTypeTaken rs2 rs1 op) s s true)
    (hpc : Runs (readReg PC) s s pcVal)
    (halign : Sail.BitVec.access (pcVal + sign_extend (m := 64) imm) 0 = 0#1)
    (hbit1 : Sail.BitVec.access (pcVal + sign_extend (m := 64) imm) 1 = 0#1)
    (zcaEnabled : Bool)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca) s s zcaEnabled) :
    Runs (execute (.BTYPE (imm, rs2, rs1, op))) s
      { s with regs := s.regs.insert nextPC (pcVal + sign_extend (m := 64) imm) }
      (.Retire_Success ()) := by
  change Runs (execute_BTYPE imm rs2 rs1 op) s _ _
  exact execute_BTYPE_taken_run s imm rs2 rs1 op pcVal hcond hpc halign hbit1 zcaEnabled hzca

/-- Not-taken conditional branch, lifted through the `execute` dispatcher (state unchanged). -/
theorem executeBranchNotTakenDispatchRuns (s : State) (imm : BitVec 13) (rs2 rs1 : regidx)
    (op : bop) (hcond : Runs (bTypeTaken rs2 rs1 op) s s false) :
    Runs (execute (.BTYPE (imm, rs2, rs1, op))) s s (.Retire_Success ()) := by
  change Runs (execute_BTYPE imm rs2 rs1 op) s _ _
  exact execute_BTYPE_notTaken_run s imm rs2 rs1 op hcond

/-- `ret` (`jalr x0, 0(rs1)`), lifted through the `execute` dispatcher. -/
theorem executeRetDispatchRuns (s : State) (rs1 : regidx) (linkVal rs1Val : BitVec 64)
    (helpElp : Runs (update_elp_state rs1) s s ())
    (hlink : Runs (get_next_pc ()) s s linkVal)
    (hrs1 : Runs (rX_bits rs1) s s rs1Val)
    (hbit1 : Sail.BitVec.access rs1Val 1 = 0#1)
    (zcaEnabled : Bool)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca) s s zcaEnabled) :
    Runs (execute (.JALR (0#12, rs1, zreg))) s
      { s with regs := s.regs.insert nextPC (Sail.BitVec.update rs1Val 0 0#1) }
      (.Retire_Success ()) := by
  change Runs (execute_JALR 0#12 rs1 zreg) s _ _
  exact ret_run s rs1 linkVal rs1Val helpElp hlink hrs1 hbit1 zcaEnabled hzca

/-! ## Shared active-hart retirement -/

/-- Compose explicit base-fetch/decoder premises with an arbitrary control-flow execute contract.

This is the control-flow analogue of `runHartActiveCoreXorRetiresWithFetchMemory`: the fetch,
interrupt-dispatch, landing-pad and `nextPC`-write bookkeeping is identical; only the `execute`
premise (and the decoded `instruction`/post-execute state it produces) is instruction-specific. -/
theorem runHartActiveControlFlow (stepNo : Nat) (state afterExec : State) (pc : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8) (inst : instruction)
    (platform : FetchBasePlatform state pc) (noMMIO : FetchMemoryNoMMIO state pc)
    (bytes : FetchBytesAt state pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled state) (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3)) state state inst)
    (notExpected : LandingPadNotExpected state)
    (execute : Runs (execute inst) (coreControlFlowNextState state pc) afterExec
      (.Retire_Success ())) :
    Runs (run_hart_active stepNo) state afterExec
      (.Step_Execute (.Retire_Success (),
        zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3))) := by
  have fetchBytes : FetchBytesBaseContract state pc byte0 byte1 byte2 byte3 :=
    fetch_bytes_machine_instructionFetch_fetch_word_run state pc byte0 byte1 byte2 byte3 platform
      noMMIO bytes
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
      (coreControlFlowNextState state pc) PUnit.unit := by
    simpa [coreControlFlowNextState] using writeNextPc_run state pc
  exact runHartActiveBaseRetires stepNo state state (coreControlFlowNextState state pc) afterExec
    Privilege.Machine (fetchWord byte0 byte1 byte2 byte3) inst pc privilegeRead dispatch fetch decode
    landingPad pcRead nextPc execute

/-! ## `try_step` packaging -/

/-- The state after the generated `try_step` counter-increment write. -/
def tryStepControlFlowAfterIncrement (state : State) : State :=
  { state with regs := state.regs.insert minstret_increment true }

/-- The state after the generated `try_step` PC-tick postlude copies `PC := nextPC = targetPC`. -/
def tryStepControlFlowAfterTick (afterExec : State) (targetPC : BitVec 64) : State :=
  { afterExec with regs := afterExec.regs.insert PC targetPC }

/-- The state after the generated `try_step` retired-counter write. -/
def tryStepControlFlowAfterRetired (afterExec : State) (targetPC retired : BitVec 64) : State :=
  { tryStepControlFlowAfterTick afterExec targetPC with
    regs := (tryStepControlFlowAfterTick afterExec targetPC).regs.insert minstret
      (Sail.BitVec.addInt retired 1) }

/--
Shared `try_step` postlude for a control-flow instruction.

The post-execute state `afterExec` is abstracted by two facts: its `nextPC` holds `targetPC` (the
value `tick_pc` copies into `PC`), and every register other than `nextPC` agrees with the
pre-execute (`tryStepControlFlowAfterIncrement`) state.  Both hold for a fall-through (`nextPC`
untouched at `pc+4`) and a jump (`nextPC` overwritten with the target); the control-flow execute
touches no other register (branch) or only the discarded `x0` link (ret).
-/
theorem tryStepControlFlowRetires (stepNo : Nat) (state afterExec : State)
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
    rw [agree hart_state (by decide)]; exact hartAfterIncrement
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
      _ = (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment :=
          agree minstret_increment (by decide)
      _ = some true := incrementAfterInc
  have retiredAfterTick :
      (tryStepControlFlowAfterTick afterExec targetPC).regs.get? minstret = some retired := by
    calc
      (tryStepControlFlowAfterTick afterExec targetPC).regs.get? minstret =
          afterExec.regs.get? minstret := by
            simpa [tryStepControlFlowAfterTick] using
              writeReg_read_unchanged afterExec PC minstret targetPC (by decide)
      _ = (tryStepControlFlowAfterIncrement state).regs.get? minstret :=
          agree minstret (by decide)
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

/-! ### Taken conditional branch -/

/--
Lift a taken conditional `BTYPE` branch through the authoritative generated `try_step`.

The decoded `.BTYPE (imm, rs2, rs1, op)`, the branch condition (`bTypeTaken … true`), the read of
`PC`, the target alignment and the `Ext_Zca` read are all explicit premises about the post-increment
/ post-`nextPC` state, so they can be discharged at the `Triple` layer.  The final state has
`nextPC = PC = pc + sext imm`, `minstret = retired+1`, `minstret_increment = true`, all other
registers preserved.
-/
theorem tryStepBranchTakenRetires (stepNo : Nat) (state : State)
    (pc pcVal retired : BitVec 64) (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop)
    (inhibit : BitVec 32) (config : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (zcaEnabled : Bool)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (imm, rs2, rs1, op)))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (hcond : Runs (bTypeTaken rs2 rs1 op)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) true)
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
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
          (pcVal + sign_extend (m := 64) imm))
        (pcVal + sign_extend (m := 64) imm) retired) false := by
  have exec : Runs (execute (.BTYPE (imm, rs2, rs1, op)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (pcVal + sign_extend (m := 64) imm)) (.Retire_Success ()) := by
    unfold controlFlowJumpState
    exact executeBranchTakenDispatchRuns
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) imm rs2 rs1 op pcVal
      hcond hpc halign hbit1 zcaEnabled hzca
  have active := runHartActiveControlFlow stepNo (tryStepControlFlowAfterIncrement state)
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
      (pcVal + sign_extend (m := 64) imm)) pc byte0 byte1 byte2 byte3 (.BTYPE (imm, rs2, rs1, op))
    platform noMMIO bytes interrupts base decode notExpected exec
  have nextPcAfterExec :
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (pcVal + sign_extend (m := 64) imm)).regs.get? nextPC =
        some (pcVal + sign_extend (m := 64) imm) := by
    change ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert nextPC
      (pcVal + sign_extend (m := 64) imm)).get? nextPC = some (pcVal + sign_extend (m := 64) imm)
    rw [Std.ExtDHashMap.get?_insert]
    simp
  have agree : ∀ r : Register, r ≠ nextPC →
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (pcVal + sign_extend (m := 64) imm)).regs.get? r =
        (tryStepControlFlowAfterIncrement state).regs.get? r := by
    intro r hr
    calc
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
          (pcVal + sign_extend (m := 64) imm)).regs.get? r =
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? r := by
            simpa [controlFlowJumpState] using
              writeReg_read_unchanged
                (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) nextPC r
                (pcVal + sign_extend (m := 64) imm) hr
      _ = (tryStepControlFlowAfterIncrement state).regs.get? r := by
            simpa [coreControlFlowNextState] using
              writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC r
                (Sail.BitVec.addInt pc 4) hr
  rcases platform with ⟨_, _, _, _, _, privilegeAfterInc, _⟩
  exact tryStepControlFlowRetires stepNo state
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
      (pcVal + sign_extend (m := 64) imm)) (pcVal + sign_extend (m := 64) imm) retired inhibit config
    (zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3)) privilegeAfterInc active
    nextPcAfterExec agree hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ### Not-taken conditional branch -/

/--
Lift a not-taken conditional `BTYPE` branch through the authoritative generated `try_step`.

Identical bookkeeping to the store/XOR fall-through: the branch retires without touching `nextPC`
(still `pc+4`), so the final state has `nextPC = PC = pc+4`, `minstret = retired+1`,
`minstret_increment = true`, all other registers preserved.
-/
theorem tryStepBranchNotTakenRetires (stepNo : Nat) (state : State)
    (pc retired : BitVec 64) (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop)
    (inhibit : BitVec 32) (config : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (imm, rs2, rs1, op)))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (hcond : Runs (bTypeTaken rs2 rs1 op)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) false)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
        (Sail.BitVec.addInt pc 4) retired) false := by
  have exec : Runs (execute (.BTYPE (imm, rs2, rs1, op)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) (.Retire_Success ()) :=
    executeBranchNotTakenDispatchRuns
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) imm rs2 rs1 op hcond
  have active := runHartActiveControlFlow stepNo (tryStepControlFlowAfterIncrement state)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) pc byte0 byte1 byte2 byte3
    (.BTYPE (imm, rs2, rs1, op)) platform noMMIO bytes interrupts base decode notExpected exec
  have nextPcAfterExec :
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? nextPC =
        some (Sail.BitVec.addInt pc 4) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt pc 4)).get? nextPC = some (Sail.BitVec.addInt pc 4)
    rw [Std.ExtDHashMap.get?_insert]
    simp
  have agree : ∀ r : Register, r ≠ nextPC →
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? r =
        (tryStepControlFlowAfterIncrement state).regs.get? r := by
    intro r hr
    simpa [coreControlFlowNextState] using
      writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC r
        (Sail.BitVec.addInt pc 4) hr
  rcases platform with ⟨_, _, _, _, _, privilegeAfterInc, _⟩
  exact tryStepControlFlowRetires stepNo state
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) (Sail.BitVec.addInt pc 4)
    retired inhibit config (zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3))
    privilegeAfterInc active nextPcAfterExec agree hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-! ### `ret` -/

/--
Lift `ret` (`jalr x0, 0(rs1)`) through the authoritative generated `try_step`.

The decoded `.JALR (0, rs1, x0)`, the ELP update, the link read, the `rs1` read, the target
alignment and the `Ext_Zca` read are explicit premises about the post-increment / post-`nextPC`
state.  The final state has `nextPC = PC = rs1 with bit 0 cleared`, `minstret = retired+1`,
`minstret_increment = true`, all other registers preserved (the `x0` link write is discarded).
-/
theorem tryStepRetRetires (stepNo : Nat) (state : State)
    (pc retired : BitVec 64) (rs1 : regidx) (linkVal rs1Val : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (zcaEnabled : Bool)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0#12, rs1, zreg)))
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
    (hbit1 : Sail.BitVec.access rs1Val 1 = 0#1)
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
          (Sail.BitVec.update rs1Val 0 0#1))
        (Sail.BitVec.update rs1Val 0 0#1) retired) false := by
  have exec : Runs (execute (.JALR (0#12, rs1, zreg)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update rs1Val 0 0#1)) (.Retire_Success ()) := by
    unfold controlFlowJumpState
    exact executeRetDispatchRuns
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) rs1 linkVal rs1Val
      helpElp hlink hrs1 hbit1 zcaEnabled hzca
  have active := runHartActiveControlFlow stepNo (tryStepControlFlowAfterIncrement state)
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
      (Sail.BitVec.update rs1Val 0 0#1)) pc byte0 byte1 byte2 byte3 (.JALR (0#12, rs1, zreg))
    platform noMMIO bytes interrupts base decode notExpected exec
  have nextPcAfterExec :
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update rs1Val 0 0#1)).regs.get? nextPC =
        some (Sail.BitVec.update rs1Val 0 0#1) := by
    change ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert nextPC
      (Sail.BitVec.update rs1Val 0 0#1)).get? nextPC = some (Sail.BitVec.update rs1Val 0 0#1)
    rw [Std.ExtDHashMap.get?_insert]
    simp
  have agree : ∀ r : Register, r ≠ nextPC →
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update rs1Val 0 0#1)).regs.get? r =
        (tryStepControlFlowAfterIncrement state).regs.get? r := by
    intro r hr
    calc
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
          (Sail.BitVec.update rs1Val 0 0#1)).regs.get? r =
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? r := by
            simpa [controlFlowJumpState] using
              writeReg_read_unchanged
                (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) nextPC r
                (Sail.BitVec.update rs1Val 0 0#1) hr
      _ = (tryStepControlFlowAfterIncrement state).regs.get? r := by
            simpa [coreControlFlowNextState] using
              writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC r
                (Sail.BitVec.addInt pc 4) hr
  rcases platform with ⟨_, _, _, _, _, privilegeAfterInc, _⟩
  exact tryStepControlFlowRetires stepNo state
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
      (Sail.BitVec.update rs1Val 0 0#1)) (Sail.BitVec.update rs1Val 0 0#1) retired inhibit config
    (zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3)) privilegeAfterInc active
    nextPcAfterExec agree hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

end BinaryFv.Keccak
