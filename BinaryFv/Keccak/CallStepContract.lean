import BinaryFv.Keccak.CallArtifactFetch
import BinaryFv.Keccak.CoreBranchStepContract
import BinaryFv.RiscV.RegisterFrame

/-!
# Artifact-backed CALL step contracts

This module packages the delivered control-flow *link-writing* execute contracts
(`execute_JAL_run`, `execute_JALR_run` from `ControlFlowStep`) through the authoritative generated
`try_step`, driven from the real Reth Keccak ELF via the parser-derived fetch facts
(`CallArtifactFetch`).  It is the CALL analogue of the store step contract
(`CoreStoreStepContract`) and of the branch/ret packagings (`CoreBranchStepContract`), covering the
`jal` / `jalr` instructions that *save a return link*.

Unlike a taken branch, a genuine call overwrites `nextPC` with the jump target **and** writes the
return address into a link register `rd`.  Because the generated integer-register write lands in
`State.regs` (`wX_bits`), `afterExec` now differs from the pre-execute state at *both* `nextPC` and
`rd`, so the branch postlude `tryStepControlFlowRetires` (whose `agree` hypothesis fixes every
register but `nextPC`) does not apply directly.  We instead package through the same underlying
primitive it uses (`tryStepRetires`), via the generalized postlude `tryStepCallRetires`, which takes
the three counter/hart facts about `afterExec` as direct premises — exactly the shape the XOR
register-writer (`tryStepCoreXorRetiresWithFetchMemory`) already uses.

The nonstandard link-register cases the binary exercises are all covered:

* `tryStepXorBlockCallRetires`  — `auipc ra; jalr 408(ra)` (0x10ad4/0x10ad8): standard `ra` call,
  auipc-relative target `xor_block` (0x10c6c).
* `tryStepNegAuipcCallRetires`  — `auipc ra,0xfffff; jalr 1164(ra)` (0x10c64/0x10c68): `ra` call
  through a *negative* auipc, target 0x100f0.
* `tryStepT0CallRetires`        — `auipc t0; jalr t0,1192(t0)` (0x10844/0x10848): genuine call
  writing a *non-`ra`* link register `t0`, target `OUTLINED_FUNCTION_0` (0x10cec).
* `tryStepJalCallRetires`       — `jal ra,reth_keccak256` (0x101f8): direct `jal` link-writing call,
  target 0x10a2c.
* `tryStepT1TailRetires`        — `auipc t1; jr 196(t1)` (0x10c54/0x10c58): tail call that *discards*
  the link (`rd = x0`), `t1`-relative target `memcpy` (0x10d18); reuses `tryStepControlFlowRetires`.

Each capstone proves the exact jump TARGET, the PC update (`PC := nextPC := target`), and the
link-register write (`rd := old nextPC = return address = pc+4`).
-/

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV

/-! ## Decode facts for the representative CALL words

Built exactly as `StoreDecodeFact.ext_decode_sd_run`: the generated decoder reduces (after the
`Ext_Zicfilp` prelude, which needs `cur_privilege = Machine` + `mseccfg` present) to the concrete
AST node.  No `native_decide` — these are clean definitional decodes. -/

theorem ext_decode_xorCallAuipc_run (state : State)
    (privRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x00000097 : BitVec 32)) state state
      (.UTYPE (0#20, .Regidx 1#5, .AUIPC)) := by
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
    privRead, mseccfgRead]
  rfl

theorem ext_decode_xorCallJalr_run (state : State)
    (privRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x198080e7 : BitVec 32)) state state
      (.JALR (0x198#12, .Regidx 1#5, .Regidx 1#5)) := by
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
    privRead, mseccfgRead]
  rfl

theorem ext_decode_negCallAuipc_run (state : State)
    (privRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0xfffff097 : BitVec 32)) state state
      (.UTYPE (0xfffff#20, .Regidx 1#5, .AUIPC)) := by
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
    privRead, mseccfgRead]
  rfl

theorem ext_decode_negCallJalr_run (state : State)
    (privRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x48c080e7 : BitVec 32)) state state
      (.JALR (0x48c#12, .Regidx 1#5, .Regidx 1#5)) := by
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
    privRead, mseccfgRead]
  rfl

theorem ext_decode_t0CallAuipc_run (state : State)
    (privRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x00000297 : BitVec 32)) state state
      (.UTYPE (0#20, .Regidx 5#5, .AUIPC)) := by
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
    privRead, mseccfgRead]
  rfl

theorem ext_decode_t0CallJalr_run (state : State)
    (privRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x4a8282e7 : BitVec 32)) state state
      (.JALR (0x4a8#12, .Regidx 5#5, .Regidx 5#5)) := by
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
    privRead, mseccfgRead]
  rfl

theorem ext_decode_t1TailAuipc_run (state : State)
    (privRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x00000317 : BitVec 32)) state state
      (.UTYPE (0#20, .Regidx 6#5, .AUIPC)) := by
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
    privRead, mseccfgRead]
  rfl

theorem ext_decode_t1TailJr_run (state : State)
    (privRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x0c430067 : BitVec 32)) state state
      (.JALR (0xc4#12, .Regidx 6#5, .Regidx 0#5)) := by
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
    privRead, mseccfgRead]
  rfl

theorem ext_decode_jalCall_run (state : State)
    (privRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x035000ef : BitVec 32)) state state
      (.JAL (0x834#21, .Regidx 1#5)) := by
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
    privRead, mseccfgRead]
  rfl

/-! ## Concrete link-register write run-lemmas

`wX_bits (Regidx k) data` (for `k ≠ 0`) reduces to `writeReg xk data` plus the no-op
`xreg_write_callback`, so it inserts `xk ↦ data`.  For `k = 0` it is a no-op (`x0` is hardwired). -/

private theorem wX_bits_run_x1 (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 1#5) data) s { s with regs := s.regs.insert x1 data } () := by
  have hidx : (Sail.BitVec.toNatInt (1#5)).toNat = 1 := rfl
  unfold Runs
  simp only [wX_bits, wX, hidx, regval_into_reg, PreSail.writeReg, EStateM.run,
    EStateM.bind, EStateM.modifyGet, EStateM.instMonad, MonadState.modifyGet,
    MonadStateOf.modifyGet, modify]
  rw [if_pos (by decide)]
  exact xreg_write_callback_run _ _ _

private theorem wX_bits_run_x5 (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 5#5) data) s { s with regs := s.regs.insert x5 data } () := by
  have hidx : (Sail.BitVec.toNatInt (5#5)).toNat = 5 := rfl
  unfold Runs
  simp only [wX_bits, wX, hidx, regval_into_reg, PreSail.writeReg, EStateM.run,
    EStateM.bind, EStateM.modifyGet, EStateM.instMonad, MonadState.modifyGet,
    MonadStateOf.modifyGet, modify]
  rw [if_pos (by decide)]
  exact xreg_write_callback_run _ _ _

private theorem wX_bits_run_zero (s : State) (data : BitVec 64) :
    Runs (wX_bits (.Regidx 0#5) data) s s () := by
  have hidx : (Sail.BitVec.toNatInt (0#5)).toNat = 0 := rfl
  unfold Runs
  simp only [wX_bits, wX, hidx, EStateM.run, EStateM.bind, EStateM.instMonad]
  rw [if_neg (by decide)]
  rfl

/-- `get_next_pc ()` reads the current `nextPC`; used to pin the saved link to the return address. -/
theorem get_next_pc_run (s : State) (v : BitVec 64) (stored : s.regs.get? nextPC = some v) :
    Runs (get_next_pc ()) s s v := by
  unfold Runs
  exact readReg_run s nextPC v stored

/-! ## Shared post-increment reads -/

private theorem preInc_hart (state : State) (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ())) :
    (tryStepControlFlowAfterIncrement state).regs.get? hart_state = some (.HART_ACTIVE ()) := by
  calc
    (tryStepControlFlowAfterIncrement state).regs.get? hart_state = state.regs.get? hart_state := by
      simpa [tryStepControlFlowAfterIncrement] using
        writeReg_read_unchanged state minstret_increment hart_state true (by decide)
    _ = some (.HART_ACTIVE ()) := hartRead

private theorem preInc_increment (state : State) :
    (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment = some true := by
  change (state.regs.insert minstret_increment true).get? minstret_increment = some true
  rw [Std.ExtDHashMap.get?_insert]
  simp

private theorem preInc_minstret (state : State) (retired : BitVec 64)
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

/-! ## Per-site capstones: exact target / PC / link at real ELF CALL sites

Each capstone drives one CALL instruction from the embedded ELF (fetch bytes from
`CallArtifactFetch`, decode from the facts above) through `try_step`, pinning the exact jump target
(the auipc-relative callee address), the PC update (`PC := nextPC := target`), and the saved link
(`= old nextPC = pc + 4`, the return address).  The base-register value `rs1Val` supplied by `hrs1`
is exactly what the preceding `auipc` writes (its own fetch+decode facts are provided alongside), so
the target is genuinely auipc-relative. -/

/-- `xor_block` call: `auipc ra,0x0` (0x10ad4) then `jalr 408(ra)` (0x10ad8).  `ra` holds the auipc
base 0x10ad4, so the jump targets `0x10ad4 + 408 = 0x10c6c` (`xor_block`) and saves the return
address 0x10adc into `ra`. -/
theorem tryStepXorBlockCallRetires (stepNo : Nat) (state : State) (retired : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64) (zcaEnabled : Bool) (mseccfgBits : BitVec 64)
    (image : ProgramImage) (imageEq : Artifact.programImage = .ok image)
    (loaded : image.matchesMemory (tryStepControlFlowAfterIncrement state).mem)
    (privRead :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgRead : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (0x10ad8#64))
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) (0x10ad8#64))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (helpElp : Runs (update_elp_state (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10ad8#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10ad8#64)) ())
    (hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10ad8#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10ad8#64)) (0x10ad4#64))
    (hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10ad8#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10ad8#64)) zcaEnabled)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) (0x10ad8#64) (0x10c6c#64) x1
          (Sail.BitVec.addInt (0x10ad8#64) 4)) (0x10c6c#64) retired) false := by
  have bytes := callWord_fetchBytesAt (tryStepControlFlowAfterIncrement state) image imageEq loaded
    0x10ad8 (by decide) 0xe7 0x80 0x80 0x19 xorCallJalr_owned
  have fwEq : fetchWord (BitVec.ofNat 8 (0xe7 : UInt8).toNat) (BitVec.ofNat 8 (0x80 : UInt8).toNat)
      (BitVec.ofNat 8 (0x80 : UInt8).toNat) (BitVec.ofNat 8 (0x19 : UInt8).toNat) =
      (0x198080e7 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 (0xe7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x80 : UInt8).toNat) (BitVec.ofNat 8 (0x80 : UInt8).toNat)
      (BitVec.ofNat 8 (0x19 : UInt8).toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0x198#12, .Regidx 1#5, .Regidx 1#5)) := by
    rw [fwEq]
    exact ext_decode_xorCallJalr_run (tryStepControlFlowAfterIncrement state) privRead mseccfgBits
      mseccfgRead
  have hnextpc :
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10ad8#64)).regs.get?
        nextPC = some (Sail.BitVec.addInt (0x10ad8#64) 4) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (0x10ad8#64) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]; simp
  have hlink := get_next_pc_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10ad8#64))
    (Sail.BitVec.addInt (0x10ad8#64) 4) hnextpc
  have htarget : Sail.BitVec.update ((0x10ad4#64) + sign_extend (m := 64) (0x198#12)) 0 0#1 =
      (0x10c6c#64) := by
    simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.update, Sail.BitVec.updateSubrange']
    bv_decide
  have h := tryStepJalrCallRetires stepNo state (0x10ad8#64) (0x10ad4#64) retired
    (Sail.BitVec.addInt (0x10ad8#64) 4) (0x198#12) (.Regidx 1#5) (.Regidx 1#5) x1
    (Sail.BitVec.addInt (0x10ad8#64) 4) inhibit config
    (BitVec.ofNat 8 (0xe7 : UInt8).toNat) (BitVec.ofNat 8 (0x80 : UInt8).toNat)
    (BitVec.ofNat 8 (0x80 : UInt8).toNat) (BitVec.ofNat 8 (0x19 : UInt8).toNat) zcaEnabled
    (wX_bits_run_x1 _ _) (by decide) (by decide) (by decide) (by decide)
    platform noMMIO bytes interrupts (by unfold BaseInstructionEncoding; decide) decode notExpected
    helpElp hlink hrs1
    (by simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.access, getElem!_pos,
      Nat.reduceLT]; bv_decide)
    hzca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  rw [htarget] at h
  exact h

/-- `ra`-link call through a *negative* auipc: `auipc ra,0xfffff` (0x10c64) then `jalr 1164(ra)`
(0x10c68).  `ra` holds `0x10c64 - 0x1000 = 0xfc64`, so the jump targets `0xfc64 + 1164 = 0x100f0`
and saves the return address 0x10c6c into `ra`. -/
theorem tryStepNegAuipcCallRetires (stepNo : Nat) (state : State) (retired : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64) (zcaEnabled : Bool) (mseccfgBits : BitVec 64)
    (image : ProgramImage) (imageEq : Artifact.programImage = .ok image)
    (loaded : image.matchesMemory (tryStepControlFlowAfterIncrement state).mem)
    (privRead :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgRead : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (0x10c68#64))
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) (0x10c68#64))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (helpElp : Runs (update_elp_state (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c68#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c68#64)) ())
    (hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c68#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c68#64)) (0xfc64#64))
    (hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c68#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c68#64)) zcaEnabled)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) (0x10c68#64) (0x100f0#64) x1
          (Sail.BitVec.addInt (0x10c68#64) 4)) (0x100f0#64) retired) false := by
  have bytes := callWord_fetchBytesAt (tryStepControlFlowAfterIncrement state) image imageEq loaded
    0x10c68 (by decide) 0xe7 0x80 0xc0 0x48 negCallJalr_owned
  have fwEq : fetchWord (BitVec.ofNat 8 (0xe7 : UInt8).toNat) (BitVec.ofNat 8 (0x80 : UInt8).toNat)
      (BitVec.ofNat 8 (0xc0 : UInt8).toNat) (BitVec.ofNat 8 (0x48 : UInt8).toNat) =
      (0x48c080e7 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 (0xe7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x80 : UInt8).toNat) (BitVec.ofNat 8 (0xc0 : UInt8).toNat)
      (BitVec.ofNat 8 (0x48 : UInt8).toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0x48c#12, .Regidx 1#5, .Regidx 1#5)) := by
    rw [fwEq]
    exact ext_decode_negCallJalr_run (tryStepControlFlowAfterIncrement state) privRead mseccfgBits
      mseccfgRead
  have hnextpc :
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c68#64)).regs.get?
        nextPC = some (Sail.BitVec.addInt (0x10c68#64) 4) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (0x10c68#64) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]; simp
  have hlink := get_next_pc_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c68#64))
    (Sail.BitVec.addInt (0x10c68#64) 4) hnextpc
  have htarget : Sail.BitVec.update ((0xfc64#64) + sign_extend (m := 64) (0x48c#12)) 0 0#1 =
      (0x100f0#64) := by
    simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.update, Sail.BitVec.updateSubrange']
    bv_decide
  have h := tryStepJalrCallRetires stepNo state (0x10c68#64) (0xfc64#64) retired
    (Sail.BitVec.addInt (0x10c68#64) 4) (0x48c#12) (.Regidx 1#5) (.Regidx 1#5) x1
    (Sail.BitVec.addInt (0x10c68#64) 4) inhibit config
    (BitVec.ofNat 8 (0xe7 : UInt8).toNat) (BitVec.ofNat 8 (0x80 : UInt8).toNat)
    (BitVec.ofNat 8 (0xc0 : UInt8).toNat) (BitVec.ofNat 8 (0x48 : UInt8).toNat) zcaEnabled
    (wX_bits_run_x1 _ _) (by decide) (by decide) (by decide) (by decide)
    platform noMMIO bytes interrupts (by unfold BaseInstructionEncoding; decide) decode notExpected
    helpElp hlink hrs1
    (by simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.access, getElem!_pos,
      Nat.reduceLT]; bv_decide)
    hzca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  rw [htarget] at h
  exact h

/-- Genuine call writing a *non-`ra`* link register `t0`: `auipc t0,0x0` (0x10844) then
`jalr t0,1192(t0)` (0x10848).  `t0` holds the auipc base 0x10844, so the jump targets
`0x10844 + 1192 = 0x10cec` (`OUTLINED_FUNCTION_0`) and saves the return address 0x1084c into `t0`. -/
theorem tryStepT0CallRetires (stepNo : Nat) (state : State) (retired : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64) (zcaEnabled : Bool) (mseccfgBits : BitVec 64)
    (image : ProgramImage) (imageEq : Artifact.programImage = .ok image)
    (loaded : image.matchesMemory (tryStepControlFlowAfterIncrement state).mem)
    (privRead :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgRead : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (0x10848#64))
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) (0x10848#64))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (helpElp : Runs (update_elp_state (.Regidx 5#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10848#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10848#64)) ())
    (hrs1 : Runs (rX_bits (.Regidx 5#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10848#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10848#64)) (0x10844#64))
    (hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10848#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10848#64)) zcaEnabled)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) (0x10848#64) (0x10cec#64) x5
          (Sail.BitVec.addInt (0x10848#64) 4)) (0x10cec#64) retired) false := by
  have bytes := callWord_fetchBytesAt (tryStepControlFlowAfterIncrement state) image imageEq loaded
    0x10848 (by decide) 0xe7 0x82 0x82 0x4a t0CallJalr_owned
  have fwEq : fetchWord (BitVec.ofNat 8 (0xe7 : UInt8).toNat) (BitVec.ofNat 8 (0x82 : UInt8).toNat)
      (BitVec.ofNat 8 (0x82 : UInt8).toNat) (BitVec.ofNat 8 (0x4a : UInt8).toNat) =
      (0x4a8282e7 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 (0xe7 : UInt8).toNat)
      (BitVec.ofNat 8 (0x82 : UInt8).toNat) (BitVec.ofNat 8 (0x82 : UInt8).toNat)
      (BitVec.ofNat 8 (0x4a : UInt8).toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0x4a8#12, .Regidx 5#5, .Regidx 5#5)) := by
    rw [fwEq]
    exact ext_decode_t0CallJalr_run (tryStepControlFlowAfterIncrement state) privRead mseccfgBits
      mseccfgRead
  have hnextpc :
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10848#64)).regs.get?
        nextPC = some (Sail.BitVec.addInt (0x10848#64) 4) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (0x10848#64) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]; simp
  have hlink := get_next_pc_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10848#64))
    (Sail.BitVec.addInt (0x10848#64) 4) hnextpc
  have htarget : Sail.BitVec.update ((0x10844#64) + sign_extend (m := 64) (0x4a8#12)) 0 0#1 =
      (0x10cec#64) := by
    simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.update, Sail.BitVec.updateSubrange']
    bv_decide
  have h := tryStepJalrCallRetires stepNo state (0x10848#64) (0x10844#64) retired
    (Sail.BitVec.addInt (0x10848#64) 4) (0x4a8#12) (.Regidx 5#5) (.Regidx 5#5) x5
    (Sail.BitVec.addInt (0x10848#64) 4) inhibit config
    (BitVec.ofNat 8 (0xe7 : UInt8).toNat) (BitVec.ofNat 8 (0x82 : UInt8).toNat)
    (BitVec.ofNat 8 (0x82 : UInt8).toNat) (BitVec.ofNat 8 (0x4a : UInt8).toNat) zcaEnabled
    (wX_bits_run_x5 _ _) (by decide) (by decide) (by decide) (by decide)
    platform noMMIO bytes interrupts (by unfold BaseInstructionEncoding; decide) decode notExpected
    helpElp hlink hrs1
    (by simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.access, getElem!_pos,
      Nat.reduceLT]; bv_decide)
    hzca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  rw [htarget] at h
  exact h

/-- Direct `jal ra,reth_keccak256` (0x101f8): a link-writing `jal`.  Target `PC + 0x834 = 0x10a2c`
(`reth_keccak256`), return address 0x101fc saved into `ra`. -/
theorem tryStepJalCallRethRetires (stepNo : Nat) (state : State) (retired : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64) (zcaEnabled : Bool) (mseccfgBits : BitVec 64)
    (image : ProgramImage) (imageEq : Artifact.programImage = .ok image)
    (loaded : image.matchesMemory (tryStepControlFlowAfterIncrement state).mem)
    (privRead :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgRead : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (0x101f8#64))
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) (0x101f8#64))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x101f8#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x101f8#64)) (0x101f8#64))
    (hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x101f8#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x101f8#64)) zcaEnabled)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) (0x101f8#64) (0x10a2c#64) x1
          (Sail.BitVec.addInt (0x101f8#64) 4)) (0x10a2c#64) retired) false := by
  have bytes := callWord_fetchBytesAt (tryStepControlFlowAfterIncrement state) image imageEq loaded
    0x101f8 (by decide) 0xef 0x00 0x50 0x03 jalCall_owned
  have fwEq : fetchWord (BitVec.ofNat 8 (0xef : UInt8).toNat) (BitVec.ofNat 8 (0x00 : UInt8).toNat)
      (BitVec.ofNat 8 (0x50 : UInt8).toNat) (BitVec.ofNat 8 (0x03 : UInt8).toNat) =
      (0x035000ef : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 (0xef : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) (BitVec.ofNat 8 (0x50 : UInt8).toNat)
      (BitVec.ofNat 8 (0x03 : UInt8).toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x834#21, .Regidx 1#5)) := by
    rw [fwEq]
    exact ext_decode_jalCall_run (tryStepControlFlowAfterIncrement state) privRead mseccfgBits
      mseccfgRead
  have hnextpc :
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x101f8#64)).regs.get?
        nextPC = some (Sail.BitVec.addInt (0x101f8#64) 4) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (0x101f8#64) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]; simp
  have hlink := get_next_pc_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x101f8#64))
    (Sail.BitVec.addInt (0x101f8#64) 4) hnextpc
  have htarget : (0x101f8#64) + sign_extend (m := 64) (0x834#21) = (0x10a2c#64) := by
    simp only [sign_extend, Sail.BitVec.signExtend]
    bv_decide
  have h := tryStepJalCallRetires stepNo state (0x101f8#64) (0x101f8#64) retired
    (Sail.BitVec.addInt (0x101f8#64) 4) (0x834#21) (.Regidx 1#5) x1
    (Sail.BitVec.addInt (0x101f8#64) 4) inhibit config
    (BitVec.ofNat 8 (0xef : UInt8).toNat) (BitVec.ofNat 8 (0x00 : UInt8).toNat)
    (BitVec.ofNat 8 (0x50 : UInt8).toNat) (BitVec.ofNat 8 (0x03 : UInt8).toNat) zcaEnabled
    (wX_bits_run_x1 _ _) (by decide) (by decide) (by decide) (by decide)
    platform noMMIO bytes interrupts (by unfold BaseInstructionEncoding; decide) decode notExpected
    hlink hpc
    (by simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.access, getElem!_pos,
      Nat.reduceLT]; bv_decide)
    (by simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.access, getElem!_pos,
      Nat.reduceLT]; bv_decide)
    hzca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  rw [htarget] at h
  exact h

/-- Tail call that *discards* the link (`rd = x0`), `t1`-relative: `auipc t1,0x0` (0x10c54) then
`jr 196(t1)` = `jalr x0,196(t1)` (0x10c58).  `t1` holds the auipc base 0x10c54, so the jump targets
`0x10c54 + 196 = 0x10d18` (`memcpy`); no register is written. -/
theorem tryStepT1TailRetires (stepNo : Nat) (state : State) (retired : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64) (zcaEnabled : Bool) (mseccfgBits : BitVec 64)
    (image : ProgramImage) (imageEq : Artifact.programImage = .ok image)
    (loaded : image.matchesMemory (tryStepControlFlowAfterIncrement state).mem)
    (privRead :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgRead : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (0x10c58#64))
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) (0x10c58#64))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (helpElp : Runs (update_elp_state (.Regidx 6#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c58#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c58#64)) ())
    (hrs1 : Runs (rX_bits (.Regidx 6#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c58#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c58#64)) (0x10c54#64))
    (hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c58#64))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c58#64)) zcaEnabled)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (0x10c58#64) (0x10d18#64))
        (0x10d18#64) retired) false := by
  have bytes := callWord_fetchBytesAt (tryStepControlFlowAfterIncrement state) image imageEq loaded
    0x10c58 (by decide) 0x67 0x00 0x43 0x0c t1TailJr_owned
  have fwEq : fetchWord (BitVec.ofNat 8 (0x67 : UInt8).toNat) (BitVec.ofNat 8 (0x00 : UInt8).toNat)
      (BitVec.ofNat 8 (0x43 : UInt8).toNat) (BitVec.ofNat 8 (0x0c : UInt8).toNat) =
      (0x0c430067 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 (0x67 : UInt8).toNat)
      (BitVec.ofNat 8 (0x00 : UInt8).toNat) (BitVec.ofNat 8 (0x43 : UInt8).toNat)
      (BitVec.ofNat 8 (0x0c : UInt8).toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0xc4#12, .Regidx 6#5, .Regidx 0#5)) := by
    rw [fwEq]
    exact ext_decode_t1TailJr_run (tryStepControlFlowAfterIncrement state) privRead mseccfgBits
      mseccfgRead
  have hnextpc :
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c58#64)).regs.get?
        nextPC = some (Sail.BitVec.addInt (0x10c58#64) 4) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (0x10c58#64) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]; simp
  have hlink := get_next_pc_run
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x10c58#64))
    (Sail.BitVec.addInt (0x10c58#64) 4) hnextpc
  have htarget : Sail.BitVec.update ((0x10c54#64) + sign_extend (m := 64) (0xc4#12)) 0 0#1 =
      (0x10d18#64) := by
    simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.update, Sail.BitVec.updateSubrange']
    bv_decide
  have h := tryStepJrDiscardRetires stepNo state (0x10c58#64) (0x10c54#64) retired (0xc4#12)
    (.Regidx 6#5) (Sail.BitVec.addInt (0x10c58#64) 4) inhibit config
    (BitVec.ofNat 8 (0x67 : UInt8).toNat) (BitVec.ofNat 8 (0x00 : UInt8).toNat)
    (BitVec.ofNat 8 (0x43 : UInt8).toNat) (BitVec.ofNat 8 (0x0c : UInt8).toNat) zcaEnabled
    platform noMMIO bytes interrupts (by unfold BaseInstructionEncoding; decide) decode notExpected
    helpElp hlink hrs1
    (by simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.access, getElem!_pos,
      Nat.reduceLT]; bv_decide)
    hzca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  rw [htarget] at h
  exact h

end BinaryFv.Keccak
