import BinaryFv.RiscV.Step.Call
import BinaryFv.RiscV.Instruction.Decode
import BinaryFv.Keccak.Reth.Proof.Common.CallFetch
import BinaryFv.RiscV.Step.ControlFlow
import BinaryFv.RiscV.Instruction.Frame.Register

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
the three counter/hart facts about `afterExec` as direct premises.

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

open BinaryFv.Binary

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
