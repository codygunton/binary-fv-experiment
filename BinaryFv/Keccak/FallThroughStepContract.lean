import BinaryFv.Keccak.GenericStepContract

/-!
# `try_step` packagings for the straight-line body and back-edge of the helper loops

Stage 3 packaged the *taken*/​*not-taken* conditional branch and `ret` through `try_step`; stage 4's
memcpy/memset loop bodies additionally need:

* the **fall-through** arithmetic / load / byte-store instructions (`add`, `lbu`, `sb`, `addi`), whose
  `execute` writes a destination register or a memory byte but leaves `nextPC` at `pc + 4`; and
* the unconditional **back-edge** `j` (a `JAL` with `rd = x0`), whose `execute` overwrites `nextPC`
  with the jump target and discards the `x0` link.

Both are thin instances of the generic postlude `tryStepGenericRetires`: the fall-through case has
`targetPC = pc + 4`; the `j` case has `targetPC = pc + sext imm`.  The active-hart retirement is the
already-generic `runHartActiveControlFlow` (its `execute` premise is any instruction whose execute
runs from `coreControlFlowNextState`).  These two theorems, together with stage 3's
`tryStepBranchTakenRetires` / `tryStepBranchNotTakenRetires` / `tryStepRetRetires`, cover every
instruction class appearing in `memcpy` and `memset`.
-/

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RISCV

/-! ## Fall-through: any retiring instruction that leaves `nextPC = pc + 4` -/

/--
Lift any fall-through instruction (one whose `execute` retires with `nextPC` still `pc + 4`) through
the authoritative generated `try_step`.

The decoded `inst`, its fetch bytes, and the `execute` contract (running from the post-`nextPC`
state `coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc` to the opaque
`afterExec`) are explicit premises.  `afterExec` is constrained only by what the postlude reads: its
`nextPC` is `pc + 4` (the instruction did not jump) and its `hart_state` / `minstret_increment` /
`minstret` agree with the post-increment state (the instruction touched none of them — it wrote at
most a general-purpose register or a memory byte).  The final state has `PC = nextPC = pc + 4`,
`minstret = retired + 1`, `minstret_increment = true`, and the instruction's own register/memory
effect carried in `afterExec`.
-/
theorem tryStepFallThroughRetires (stepNo : Nat) (state afterExec : State)
    (pc retired : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8) (inst : instruction)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) inst)
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (exec : Runs (execute inst)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) afterExec
      (.Retire_Success ()))
    (nextPcAfterExec : afterExec.regs.get? nextPC = some (Sail.BitVec.addInt pc 4))
    (hartAgree : afterExec.regs.get? hart_state =
      (tryStepControlFlowAfterIncrement state).regs.get? hart_state)
    (incAgree : afterExec.regs.get? minstret_increment =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment)
    (retAgree : afterExec.regs.get? minstret =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired afterExec (Sail.BitVec.addInt pc 4) retired) false := by
  have active := runHartActiveControlFlow stepNo (tryStepControlFlowAfterIncrement state) afterExec
    pc byte0 byte1 byte2 byte3 inst platform noMMIO bytes interrupts base decode notExpected exec
  rcases platform with ⟨_, _, _, _, _, privilegeAfterInc, _⟩
  exact tryStepGenericRetires stepNo state afterExec (Sail.BitVec.addInt pc 4) retired inhibit config
    (zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3)) privilegeAfterInc active
    nextPcAfterExec hartAgree incAgree retAgree hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-! ## Back-edge: `j target` (`JAL` with `rd = x0`) -/

/-- Writing register `x0` (`zreg`) is a no-op (local copy of the stage-3 private lemma). -/
private theorem wX_bits_zero_run (s : State) (data : BitVec 64) :
    Runs (wX_bits zreg data) s s () := by
  unfold wX_bits zreg wX
  rfl

/-- `j (pc + sext imm)` = `JAL imm x0`, lifted through the `execute` dispatcher: it reads the link
and `PC`, overwrites `nextPC` with the target, and discards the `x0` link, so the post-state is the
jump state at `pc + sext imm`. -/
theorem executeJDispatchRuns (s : State) (imm : BitVec 21) (pcVal linkVal : BitVec 64)
    (hlink : Runs (get_next_pc ()) s s linkVal)
    (hpc : Runs (readReg PC) s s pcVal)
    (halign : Sail.BitVec.access (pcVal + sign_extend (m := 64) imm) 0 = 0#1)
    (hbit1 : Sail.BitVec.access (pcVal + sign_extend (m := 64) imm) 1 = 0#1)
    (zcaEnabled : Bool)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca) s s zcaEnabled) :
    Runs (execute (.JAL (imm, zreg))) s
      { s with regs := s.regs.insert nextPC (pcVal + sign_extend (m := 64) imm) }
      (.Retire_Success ()) := by
  change Runs (execute_JAL imm zreg) s _ _
  exact execute_JAL_run s _ imm zreg linkVal pcVal hlink hpc halign hbit1 zcaEnabled hzca
    (wX_bits_zero_run _ linkVal)

/--
Lift the unconditional back-edge `j (pc + sext imm)` (`JAL imm x0`) through the authoritative
generated `try_step`.

Structurally identical to stage 3's `tryStepBranchTakenRetires`: the jump overwrites `nextPC` with
`pc + sext imm` and the `x0` link write is discarded, so the final state has
`nextPC = PC = pc + sext imm`, `minstret = retired + 1`, `minstret_increment = true`, all other
registers preserved.
-/
theorem tryStepJRetires (stepNo : Nat) (state : State)
    (pc pcVal retired : BitVec 64) (imm : BitVec 21) (inhibit : BitVec 32) (config : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8) (linkVal : BitVec 64) (zcaEnabled : Bool)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (imm, zreg)))
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
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
          (pcVal + sign_extend (m := 64) imm))
        (pcVal + sign_extend (m := 64) imm) retired) false := by
  have exec : Runs (execute (.JAL (imm, zreg)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (pcVal + sign_extend (m := 64) imm)) (.Retire_Success ()) := by
    unfold controlFlowJumpState
    exact executeJDispatchRuns
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) imm pcVal linkVal
      hlink hpc halign hbit1 zcaEnabled hzca
  have active := runHartActiveControlFlow stepNo (tryStepControlFlowAfterIncrement state)
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
      (pcVal + sign_extend (m := 64) imm)) pc byte0 byte1 byte2 byte3 (.JAL (imm, zreg))
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
  exact tryStepGenericRetires stepNo state
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
      (pcVal + sign_extend (m := 64) imm)) (pcVal + sign_extend (m := 64) imm) retired inhibit config
    (zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3)) privilegeAfterInc active
    nextPcAfterExec (agree hart_state (by decide)) (agree minstret_increment (by decide))
    (agree minstret (by decide)) hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead

end BinaryFv.Keccak
