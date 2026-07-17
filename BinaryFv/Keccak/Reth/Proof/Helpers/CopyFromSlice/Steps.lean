import BinaryFv.Keccak.Reth.Proof.Helpers.CopyFromSlice.Context

/-!
# The six `copy_from_slice` setup step lemmas
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

/-! ## The six setup step lemmas -/

/-- Step 1: `mv a4, a1` at `0x10c44` (`a4 = dst_len`).  Fetch bytes `13 87 05 00` (`00058713`);
writes `x14 ↦ a1Val + sext 0`. -/
theorem cfs_step_mv_a4_a1 (stepNo : Nat) (state : State)
    (a1Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c44) 0x13#8 0x87#8 0x05#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h11 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c44)).regs.get? x11 = some a1Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c44) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c44)).regs.insert x14 (a1Val + sign_extend (m := 64) 0#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c44) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x13#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x13#8 0x87#8 0x05#8 0x00#8 = (0x00058713 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x87#8 0x05#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 11#5, .Regidx 14#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_mv_a4_a1_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (0#12, .Regidx 11#5, .Regidx 14#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c44))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c44) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c44)).regs.insert x14 (a1Val + sign_extend (m := 64) 0#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0#12 (.Regidx 11#5) (.Regidx 14#5) .ADDI) _ _ _
    unfold Runs
    exact execute_mv_a4_a1 _ a1Val h11
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10c44) retired inhibit config
    0x13#8 0x87#8 0x05#8 0x00#8 (.ITYPE (0#12, .Regidx 11#5, .Regidx 14#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpNextPc _ _ x14 _ (by decide))
    (gpGet _ _ x14 _ hart_state (by decide) (by decide))
    (gpGet _ _ x14 _ minstret_increment (by decide) (by decide))
    (gpGet _ _ x14 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- Step 2: `bne a1, a3, 0x10c5c` at `0x10c48`, NOT taken (`a1 = a3`).  Fetch bytes `63 9a d5 00`
(`00d59a63`); retires with `PC = pc + 4 = 0x10c4c`, skipping the panic branch. -/
theorem cfs_step_bne_not_taken (stepNo : Nat) (state : State)
    (a1v a3v retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c48) 0x63#8 0x9a#8 0xd5#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h11 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c48)).regs.get? x11 = some a1v)
    (h13 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c48)).regs.get? x13 = some a3v)
    (heq : a1v = a3v) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c48))
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c48) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x63#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x63#8 0x9a#8 0xd5#8 0x00#8 = (0x00d59a63 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x9a#8 0xd5#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (20#13, .Regidx 13#5, .Regidx 11#5, .BNE)) := by
    rw [wordEq]; exact ext_decode_bne_a1_a3_run _ privRead mseccfgBits mseccfgRead
  have hcond : Runs (bTypeTaken (.Regidx 13#5) (.Regidx 11#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c48))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c48))
      false := by
    have h := bTypeTaken_bne_a1_a3_run _ a1v a3v h11 h13
    rwa [show (a1v != a3v) = false by rw [heq]; simp] at h
  exact tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x10c48) retired
    (20#13) (.Regidx 13#5) (.Regidx 11#5) .BNE inhibit config 0x63#8 0x9a#8 0xd5#8 0x00#8
    platform noMMIO bytes interrupts base decode notExpected hcond hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- Step 3: `mv a1, a2` at `0x10c4c` (`a1 = src_ptr`).  Fetch bytes `93 05 06 00` (`00060593`);
writes `x11 ↦ a2Val + sext 0`. -/
theorem cfs_step_mv_a1_a2 (stepNo : Nat) (state : State)
    (a2Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c4c) 0x93#8 0x05#8 0x06#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c4c)).regs.get? x12 = some a2Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c4c) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c4c)).regs.insert x11 (a2Val + sign_extend (m := 64) 0#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c4c) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x93#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x93#8 0x05#8 0x06#8 0x00#8 = (0x00060593 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x06#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 12#5, .Regidx 11#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_mv_a1_a2_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (0#12, .Regidx 12#5, .Regidx 11#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c4c))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c4c) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c4c)).regs.insert x11 (a2Val + sign_extend (m := 64) 0#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0#12 (.Regidx 12#5) (.Regidx 11#5) .ADDI) _ _ _
    unfold Runs
    exact execute_mv_a1_a2 _ a2Val h12
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10c4c) retired inhibit config
    0x93#8 0x05#8 0x06#8 0x00#8 (.ITYPE (0#12, .Regidx 12#5, .Regidx 11#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpNextPc _ _ x11 _ (by decide))
    (gpGet _ _ x11 _ hart_state (by decide) (by decide))
    (gpGet _ _ x11 _ minstret_increment (by decide) (by decide))
    (gpGet _ _ x11 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- Step 4: `mv a2, a4` at `0x10c50` (`a2 = len`).  Fetch bytes `13 06 07 00` (`00070613`);
writes `x12 ↦ a4Val + sext 0`. -/
theorem cfs_step_mv_a2_a4 (stepNo : Nat) (state : State)
    (a4Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c50) 0x13#8 0x06#8 0x07#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h14 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c50)).regs.get? x14 = some a4Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c50) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c50)).regs.insert x12 (a4Val + sign_extend (m := 64) 0#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c50) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x13#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x13#8 0x06#8 0x07#8 0x00#8 = (0x00070613 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x06#8 0x07#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 14#5, .Regidx 12#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_mv_a2_a4_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (0#12, .Regidx 14#5, .Regidx 12#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c50))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c50) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c50)).regs.insert x12 (a4Val + sign_extend (m := 64) 0#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0#12 (.Regidx 14#5) (.Regidx 12#5) .ADDI) _ _ _
    unfold Runs
    exact execute_mv_a2_a4 _ a4Val h14
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10c50) retired inhibit config
    0x13#8 0x06#8 0x07#8 0x00#8 (.ITYPE (0#12, .Regidx 14#5, .Regidx 12#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpNextPc _ _ x12 _ (by decide))
    (gpGet _ _ x12 _ hart_state (by decide) (by decide))
    (gpGet _ _ x12 _ minstret_increment (by decide) (by decide))
    (gpGet _ _ x12 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- Step 5: `auipc t1, 0x0` at `0x10c54` (`t1 = 0x10c54`).  Fetch bytes `17 03 00 00` (`00000317`);
writes `x6 ↦ pcVal + sext (0 ++ 0)`. -/
theorem cfs_step_auipc (stepNo : Nat) (state : State)
    (pcVal retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c54) 0x17#8 0x03#8 0x00#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hpc : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c54)).regs.get? PC = some pcVal) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c54) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10c54)).regs.insert x6
              (pcVal + sign_extend (m := 64) (0#20 ++ 0x000#12)) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c54) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x17#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x17#8 0x03#8 0x00#8 0x00#8 = (0x00000317 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x17#8 0x03#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0#20, .Regidx 6#5, .AUIPC)) := by
    rw [wordEq]; exact ext_decode_auipc_t1_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.UTYPE (0#20, .Regidx 6#5, .AUIPC)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c54))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c54) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10c54)).regs.insert x6
            (pcVal + sign_extend (m := 64) (0#20 ++ 0x000#12)) }
      (.Retire_Success ()) := by
    change Runs (execute_UTYPE 0#20 (.Regidx 6#5) .AUIPC) _ _ _
    exact execute_UTYPE_auipc_run _ _ 0#20 (.Regidx 6#5) pcVal
      (readReg_run _ PC pcVal hpc) (wX_bits_x6_run _ _)
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10c54) retired inhibit config
    0x17#8 0x03#8 0x00#8 0x00#8 (.UTYPE (0#20, .Regidx 6#5, .AUIPC))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpNextPc _ _ x6 _ (by decide))
    (gpGet _ _ x6 _ hart_state (by decide) (by decide))
    (gpGet _ _ x6 _ minstret_increment (by decide) (by decide))
    (gpGet _ _ x6 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- Step 6: `jr 196(t1)` at `0x10c58` (`jalr x0, 196(t1)`, tail-call `memcpy`).  Fetch bytes
`67 00 43 0c` (`0c430067`); jumps to `(t1Val + sext 196) with bit 0 cleared`. -/
theorem cfs_step_jr (stepNo : Nat) (state : State)
    (t1Val retired mseccfgBits misaBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c58) 0x67#8 0x00#8 0x43#8 0x0c#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hrs1 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c58)).regs.get? x6 = some t1Val)
    (hbit1 : Sail.BitVec.access (t1Val + sign_extend (m := 64) 0xc4#12) 1 = 0#1)
    (hElp : Runs (update_elp_state (.Regidx 6#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58))
      ())
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10c58)).regs.get? misa = some misaBits) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58)
          (Sail.BitVec.update (t1Val + sign_extend (m := 64) 0xc4#12) 0 0#1))
        (Sail.BitVec.update (t1Val + sign_extend (m := 64) 0xc4#12) 0 0#1) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x67#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x67#8 0x00#8 0x43#8 0x0c#8 = (0x0c430067 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x67#8 0x00#8 0x43#8 0x0c#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0xc4#12, .Regidx 6#5, zreg)) := by
    rw [wordEq]; exact ext_decode_jr_t1_run _ privRead mseccfgBits mseccfgRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c58) 4) := by
    unfold get_next_pc; exact readReg_run _ nextPC _ (coreNextPc _ _)
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c58))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisa]
  exact tryStepJrRetires stepNo state (BitVec.ofNat 64 0x10c58) retired (.Regidx 6#5) (0xc4#12)
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c58) 4) t1Val inhibit config
    0x67#8 0x00#8 0x43#8 0x0c#8 (_get_Misa_C misaBits == 1#1)
    platform noMMIO bytes interrupts base decode notExpected hElp hlink
    (rX_bits_x6_run _ _ hrs1) hbit1 hzca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead

end BinaryFv.Keccak
