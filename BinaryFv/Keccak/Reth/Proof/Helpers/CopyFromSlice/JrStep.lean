import BinaryFv.Keccak.Reth.Proof.Helpers.CopyFromSlice.Framing

/-!
# `jr off(rs1)` through the generated `try_step`

The general-immediate `jalr rd = x0` tail jump the setup uses.
-/

namespace BinaryFv.Keccak
open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## `jr` (general-immediate `jalr rd = x0`) through the generated `try_step`

`tryStepRetRetires` fixes the `jalr` immediate to `0`; the copy_from_slice tail-call `jr 196(t1)` is
`jalr x0, 196(t1)` with a *general* immediate, so we package the general case here.  The jump target
is `(rs1Val + sext imm)` with bit 0 cleared (`Sail.BitVec.update _ 0 0#1`), the link write to `x0`
is discarded, and everything else mirrors `tryStepRetRetires`. -/

/-- Writing register `x0` (`zreg`) is a no-op (local copy of the stage-3 private lemma). -/
theorem wX_bits_zero_run (s : State) (data : BitVec 64) :
    Runs (wX_bits zreg data) s s () := by
  unfold wX_bits zreg wX
  rfl

/-- `jr imm(rs1)` = `jalr x0, imm(rs1)`, lifted through the `execute` dispatcher: reads the link and
`rs1`, forms the target `(rs1 + sext imm)` with bit 0 cleared, and discards the `x0` link. -/
theorem executeJrDispatchRuns (s : State) (imm : BitVec 12) (rs1 : regidx)
    (linkVal rs1Val : BitVec 64)
    (helpElp : Runs (update_elp_state rs1) s s ())
    (hlink : Runs (get_next_pc ()) s s linkVal)
    (hrs1 : Runs (rX_bits rs1) s s rs1Val)
    (hbit1 : Sail.BitVec.access (rs1Val + sign_extend (m := 64) imm) 1 = 0#1)
    (zcaEnabled : Bool)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca) s s zcaEnabled) :
    Runs (execute (.JALR (imm, rs1, zreg))) s
      { s with regs :=
        s.regs.insert nextPC (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1) }
      (.Retire_Success ()) := by
  change Runs (execute_JALR imm rs1 zreg) s _ _
  exact execute_JALR_run s _ imm rs1 zreg linkVal rs1Val helpElp hlink hrs1 hbit1 zcaEnabled hzca
    (wX_bits_zero_run _ linkVal)

/--
Lift the general-immediate `jr imm(rs1)` (`jalr x0, imm(rs1)`) through the authoritative generated
`try_step`.  Structurally identical to `tryStepRetRetires`, but keeping `imm` general: the jump
overwrites `nextPC` with `(rs1Val + sext imm)` bit-0-cleared, the `x0` link write is discarded, so
the final state has `nextPC = PC = (rs1Val + sext imm) with bit 0 cleared`, `minstret = retired+1`,
`minstret_increment = true`, all other registers preserved.
-/
theorem tryStepJrRetires (stepNo : Nat) (state : State)
    (pc retired : BitVec 64) (rs1 : regidx) (imm : BitVec 12) (linkVal rs1Val : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (zcaEnabled : Bool)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (imm, rs1, zreg)))
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
  have exec : Runs (execute (.JALR (imm, rs1, zreg)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
        (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)) (.Retire_Success ()) := by
    unfold controlFlowJumpState
    exact executeJrDispatchRuns
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) imm rs1 linkVal rs1Val
      helpElp hlink hrs1 hbit1 zcaEnabled hzca
  have active := runHartActiveControlFlow stepNo (tryStepControlFlowAfterIncrement state)
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc
      (Sail.BitVec.update (rs1Val + sign_extend (m := 64) imm) 0 0#1)) pc byte0 byte1 byte2 byte3
    (.JALR (imm, rs1, zreg)) platform noMMIO bytes interrupts base decode notExpected exec
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

end BinaryFv.Keccak
