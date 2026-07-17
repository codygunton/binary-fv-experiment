import BinaryFv.Keccak.Reth.Proof.XorBlock.Steps.Memory

/-!
# `xor_block` control-flow body steps (`bnez` / `ret`)
-/

namespace BinaryFv.Keccak.XorBlock
open BinaryFv.Binary
open BinaryFv.Keccak.SpecBridge
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open BinaryFv.Keccak
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Deliverable 2c: control-flow body step lemmas (`bnez` / `ret`) and entry (`li` / `beqz`) -/

/-- Reading `x0` yields the hard-wired zero register. -/
theorem rX_x0_run (s : State) : Runs (rX_bits (.Regidx (BitVec.ofNat 5 0))) s s zero_reg := by
  have rk : (Sail.BitVec.toNatInt (BitVec.ofNat 5 0)).toNat = 0 := by decide
  unfold Runs
  simp [rX_bits, rX, rk, EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad,
    regval_from_reg]

/-- `bnez a2` = `bne a2, x0`: runs to `a2v != zero_reg`. -/
theorem bTypeTaken_bnez_run (s : State) (a2v : BitVec 64) (h12 : s.regs.get? x12 = some a2v) :
    Runs (bTypeTaken (.Regidx 0#5) (.Regidx 12#5) .BNE) s s (a2v != zero_reg) := by
  unfold bTypeTaken
  refine Runs.bind (rX_x12_run s a2v h12) ?_
  refine Runs.bind (rX_x0_run s) ?_
  rfl

/-- `beqz a2` = `beq a2, x0`: runs to `a2v == zero_reg`. -/
theorem bTypeTaken_beqz_run (s : State) (a2v : BitVec 64) (h12 : s.regs.get? x12 = some a2v) :
    Runs (bTypeTaken (.Regidx 0#5) (.Regidx 12#5) .BEQ) s s (a2v == zero_reg) := by
  unfold bTypeTaken
  refine Runs.bind (rX_x12_run s a2v h12) ?_
  refine Runs.bind (rX_x0_run s) ?_
  rfl

/-- `bnez a2, 0x10c74` at 0x10ce4, taken (`a2 ≠ 0`): back-edge to the loop head. -/
theorem step_bnez_taken (stepNo : Nat) (state : State) (pcVal a2v retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10ce4)).regs.get? x12 = some a2v)
    (hne : a2v ≠ zero_reg)
    (hpcRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10ce4)).regs.get? PC = some pcVal)
    (misaBits : BitVec 64)
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10ce4)).regs.get? misa = some misaBits)
    (halign : Sail.BitVec.access (pcVal + sign_extend (m := 64) (0x1f90#13)) 0 = 0#1)
    (hbit1 : Sail.BitVec.access (pcVal + sign_extend (m := 64) (0x1f90#13)) 1 = 0#1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10ce4) (pcVal + sign_extend (m := 64) (0x1f90#13)))
        (pcVal + sign_extend (m := 64) (0x1f90#13)) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0xe3#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0xe3#8 0x18#8 0x06#8 0xf8#8 = (0xf80618e3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xe3#8 0x18#8 0x06#8 0xf8#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x1f90#13, .Regidx 0#5, .Regidx 12#5, .BNE)) := by
    rw [wordEq]; exact ext_decode_bnez_a2_run _ privRead mseccfgBits mseccfgRead
  have hcondEq : (a2v != zero_reg) = true := by rw [bne_iff_ne]; exact hne
  have hcond : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 12#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      true := by
    have := bTypeTaken_bnez_run _ a2v h12; rwa [hcondEq] at this
  have hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      pcVal :=
    readReg_run _ PC pcVal hpcRead
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisa]
  exact tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x10ce4) pcVal retired
    (0x1f90#13) (.Regidx 0#5) (.Regidx 12#5) .BNE inhibit config 0xe3#8 0x18#8 0x06#8 0xf8#8
    (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected
    hcond hpc halign hbit1 hzca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead

/-- `bnez a2, 0x10c74` at 0x10ce4, NOT taken (`a2 = 0`): falls through to `ret` at 0x10ce8. -/
theorem step_bnez_not_taken (stepNo : Nat) (state : State) (a2v retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ce4) 0xe3#8 0x18#8 0x06#8 0xf8#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10ce4)).regs.get? x12 = some a2v)
    (heq : a2v = zero_reg) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce4) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0xe3#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0xe3#8 0x18#8 0x06#8 0xf8#8 = (0xf80618e3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xe3#8 0x18#8 0x06#8 0xf8#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x1f90#13, .Regidx 0#5, .Regidx 12#5, .BNE)) := by
    rw [wordEq]; exact ext_decode_bnez_a2_run _ privRead mseccfgBits mseccfgRead
  have hcond : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 12#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce4))
      false := by
    have := bTypeTaken_bnez_run _ a2v h12
    rwa [show (a2v != zero_reg) = false by rw [heq]; simp] at this
  exact tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x10ce4) retired
    (0x1f90#13) (.Regidx 0#5) (.Regidx 12#5) .BNE inhibit config 0xe3#8 0x18#8 0x06#8 0xf8#8
    platform noMMIO bytes interrupts base decode notExpected hcond hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- `ret` (`jalr x0, 0(ra)`) at 0x10ce8: returns with `PC = ra` (bit 0 cleared). -/
theorem step_ret (stepNo : Nat) (state : State)
    (rs1Val retired mseccfgBits misaBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ce8) 0x67#8 0x80#8 0x00#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      rs1Val)
    (hbit1 : Sail.BitVec.access rs1Val 1 = 0#1)
    (hElp : Runs (update_elp_state (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      ())
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10ce8)).regs.get? misa = some misaBits) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8)
          (Sail.BitVec.update rs1Val 0 0#1))
        (Sail.BitVec.update rs1Val 0 0#1) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x67#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x67#8 0x80#8 0x00#8 0x00#8 = (0x00008067 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x67#8 0x80#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0#12, .Regidx 1#5, zreg)) := by
    rw [wordEq]; exact ext_decode_ret_run _ privRead mseccfgBits mseccfgRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce8) 4) := by
    unfold get_next_pc; exact readReg_run _ nextPC _ (coreNextPc _ _)
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ce8))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisa]
  exact tryStepRetRetires stepNo state (BitVec.ofNat 64 0x10ce8) retired (.Regidx 1#5)
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ce8) 4) rs1Val inhibit config
    0x67#8 0x80#8 0x00#8 0x00#8 (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base
    decode notExpected hElp hlink hrs1 hbit1 hzca hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead

/-- Entry `li a2, 136` (`addi a2, x0, 136`) at 0x10c6c. -/
theorem step_li_a2 (stepNo : Nat) (state : State) (retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c6c) 0x13#8 0x06#8 0x80#8 0x08#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c6c)) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c6c)).regs.insert x12 (zero_reg + sign_extend (m := 64) 136#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c6c) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x13#8 0x06#8 0x80#8 0x08#8 = (0x08800613 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x06#8 0x80#8 0x08#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (136#12, .Regidx 0#5, .Regidx 12#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_li_a2_136_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (136#12, .Regidx 0#5, .Regidx 12#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c6c))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c6c)) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c6c)).regs.insert x12 (zero_reg + sign_extend (m := 64) 136#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 136#12 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    exact execute_ITYPE_addi_run _ _ 136#12 (.Regidx 0#5) (.Regidx 12#5) zero_reg (rX_x0_run _)
      (wX_x12_run _ (zero_reg + sign_extend (m := 64) 136#12))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c6c) retired mseccfgBits inhibit config
    0x13#8 0x06#8 0x80#8 0x08#8 (.ITYPE (136#12, .Regidx 0#5, .Regidx 12#5, .ADDI))
    x12 (zero_reg + sign_extend (m := 64) 136#12) plat counters
    (by unfold BaseInstructionEncoding; decide) decode exec (by decide) (by decide) (by decide)
    (by decide)

/-- Entry `beqz a2, 0x10ce8` at 0x10c70, NOT taken (`a2 = 136 ≠ 0`): falls through to the loop
head at 0x10c74. -/
theorem step_beqz_not_taken (stepNo : Nat) (state : State) (a2v retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c70) 0x63#8 0x0c#8 0x06#8 0x06#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c70)).regs.get? x12 = some a2v)
    (hne : a2v ≠ zero_reg) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c70))
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c70) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x63#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x63#8 0x0c#8 0x06#8 0x06#8 = (0x06060c63 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x0c#8 0x06#8 0x06#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x78#13, .Regidx 0#5, .Regidx 12#5, .BEQ)) := by
    rw [wordEq]; exact ext_decode_beqz_a2_run _ privRead mseccfgBits mseccfgRead
  have hcond : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 12#5) .BEQ)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c70))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c70))
      false := by
    have := bTypeTaken_beqz_run _ a2v h12
    rwa [show (a2v == zero_reg) = false by
      rw [beq_eq_false_iff_ne]; exact hne] at this
  exact tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x10c70) retired
    (0x78#13) (.Regidx 0#5) (.Regidx 12#5) .BEQ inhibit config 0x63#8 0x0c#8 0x06#8 0x06#8
    platform noMMIO bytes interrupts base decode notExpected hcond hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

end BinaryFv.Keccak.XorBlock
