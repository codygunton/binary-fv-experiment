import BinaryFv.Keccak.Reth.Proof.Helpers.Memcpy.RegOps

/-!
# `memcpy` fall-through framing helpers
-/

namespace BinaryFv.Keccak
open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Fall-through framing helpers

A fall-through body instruction retires with `nextPC` still at `pc + 4` and writes at most one
general-purpose register `rd` (or a memory byte, handled via `writeBytes_preserves_regs`).  These two
lemmas read the post-execute register file `(coreControlFlowNextState Y pc).regs.insert rd v` — the
`nextPC` slot at `pc + 4`, and any other stable slot back to `Y`. -/

/-- The `nextPC` slot of the post-execute state of a GP-writing fall-through instruction is `pc+4`. -/
theorem gpFrameNextPc (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
    (hrd : nextPC ≠ rd) :
    ((coreControlFlowNextState Y pc).regs.insert rd v).get? nextPC =
      some (Sail.BitVec.addInt pc 4) := by
  calc ((coreControlFlowNextState Y pc).regs.insert rd v).get? nextPC
      = (coreControlFlowNextState Y pc).regs.get? nextPC :=
        writeReg_read_unchanged (coreControlFlowNextState Y pc) rd nextPC v hrd
    _ = some (Sail.BitVec.addInt pc 4) := by
        change (Y.regs.insert nextPC (Sail.BitVec.addInt pc 4)).get? nextPC = _
        rw [Std.ExtDHashMap.get?_insert]; simp

/-- Any register other than `nextPC` and `rd` reads through the post-execute state of a GP-writing
fall-through instruction back to the pre-`nextPC` state `Y`. -/
theorem gpFrameGet (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
    (r : Register) (hrd : r ≠ rd) (hnp : r ≠ nextPC) :
    ((coreControlFlowNextState Y pc).regs.insert rd v).get? r = Y.regs.get? r := by
  calc ((coreControlFlowNextState Y pc).regs.insert rd v).get? r
      = (coreControlFlowNextState Y pc).regs.get? r :=
        writeReg_read_unchanged (coreControlFlowNextState Y pc) rd r v hrd
    _ = Y.regs.get? r := by
        simpa [coreControlFlowNextState] using
          writeReg_read_unchanged Y nextPC r (Sail.BitVec.addInt pc 4) hnp

/-- Bridge a register read from the pre-step state through the counter-increment and `nextPC` writes
to the execute state `coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc`. -/
theorem xGet (state : State) (pc : BitVec 64) (r : Register)
    (hnp : r ≠ nextPC) (hmi : r ≠ minstret_increment) :
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? r =
      state.regs.get? r := by
  calc (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? r
      = (tryStepControlFlowAfterIncrement state).regs.get? r := by
        simpa [coreControlFlowNextState] using
          writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC r
            (Sail.BitVec.addInt pc 4) hnp
    _ = state.regs.get? r := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment r true hmi

/-! ## Step 2: `add a3, a1, a5` at `0x10d24` (`a3 = src + i`) -/

/-- The `add a3, a1, a5` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d24` are `b3 86 f5 00` (`00f586b3`); the destination write is `x13 ↦ srcVal + a5Val`. -/
theorem memcpy_step_add_a3 (stepNo : Nat) (state : State)
    (srcVal a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d24) 0xb3#8 0x86#8 0xf5#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h11 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d24)).regs.get? x11 = some srcVal)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d24)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d24) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d24)).regs.insert x13 (srcVal + a5Val) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d24) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0xb3#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0xb3#8 0x86#8 0xf5#8 0x00#8 = (0x00f586b3 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xb3#8 0x86#8 0xf5#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 15#5, .Regidx 11#5, .Regidx 13#5, .ADD)) := by
    rw [wordEq]; exact ext_decode_add_a3_a1_a5_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.RTYPE (.Regidx 15#5, .Regidx 11#5, .Regidx 13#5, .ADD)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d24))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d24) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d24)).regs.insert x13 (srcVal + a5Val) }
      (.Retire_Success ()) := by
    change Runs (execute_RTYPE (.Regidx 15#5) (.Regidx 11#5) (.Regidx 13#5) .ADD) _ _ _
    unfold Runs
    exact execute_add_a3_a1_a5 _ srcVal a5Val h11 h15
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d24) retired inhibit config
    0xb3#8 0x86#8 0xf5#8 0x00#8 (.RTYPE (.Regidx 15#5, .Regidx 11#5, .Regidx 13#5, .ADD))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpFrameNextPc _ _ x13 _ (by decide))
    (gpFrameGet _ _ x13 _ hart_state (by decide) (by decide))
    (gpFrameGet _ _ x13 _ minstret_increment (by decide) (by decide))
    (gpFrameGet _ _ x13 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 4: `add a4, a0, a5` at `0x10d2c` (`a4 = dst + i`) -/

/-- The `add a4, a0, a5` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d2c` are `33 07 f5 00` (`00f50733`); the destination write is `x14 ↦ dstVal + a5Val`. -/
theorem memcpy_step_add_a4 (stepNo : Nat) (state : State)
    (dstVal a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d2c) 0x33#8 0x07#8 0xf5#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h10 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d2c)).regs.get? x10 = some dstVal)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d2c)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d2c) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d2c)).regs.insert x14 (dstVal + a5Val) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d2c) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x33#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x33#8 0x07#8 0xf5#8 0x00#8 = (0x00f50733 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x07#8 0xf5#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD)) := by
    rw [wordEq]; exact ext_decode_add_a4_a0_a5_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d2c))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d2c) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d2c)).regs.insert x14 (dstVal + a5Val) }
      (.Retire_Success ()) := by
    change Runs (execute_RTYPE (.Regidx 15#5) (.Regidx 10#5) (.Regidx 14#5) .ADD) _ _ _
    unfold Runs
    exact execute_add_a4_a0_a5 _ dstVal a5Val h10 h15
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d2c) retired inhibit config
    0x33#8 0x07#8 0xf5#8 0x00#8 (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpFrameNextPc _ _ x14 _ (by decide))
    (gpFrameGet _ _ x14 _ hart_state (by decide) (by decide))
    (gpFrameGet _ _ x14 _ minstret_increment (by decide) (by decide))
    (gpFrameGet _ _ x14 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 5: `addi a5, a5, 1` at `0x10d30` (`i++`) -/

/-- The `addi a5, a5, 1` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d30` are `93 87 17 00` (`00178793`); the destination write is `x15 ↦ a5Val + sext 1`. -/
theorem memcpy_step_addi_a5 (stepNo : Nat) (state : State)
    (a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d30) 0x93#8 0x87#8 0x17#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d30)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d30) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d30)).regs.insert x15 (a5Val + sign_extend (m := 64) 1#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d30) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x93#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x93#8 0x87#8 0x17#8 0x00#8 = (0x00178793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x87#8 0x17#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_addi_a5_a5_1_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d30))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d30) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d30)).regs.insert x15 (a5Val + sign_extend (m := 64) 1#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 1#12 (.Regidx 15#5) (.Regidx 15#5) .ADDI) _ _ _
    unfold Runs
    exact execute_addi_a5_a5_1 _ a5Val h15
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d30) retired inhibit config
    0x93#8 0x87#8 0x17#8 0x00#8 (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpFrameNextPc _ _ x15 _ (by decide))
    (gpFrameGet _ _ x15 _ hart_state (by decide) (by decide))
    (gpFrameGet _ _ x15 _ minstret_increment (by decide) (by decide))
    (gpFrameGet _ _ x15 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 7: `j 0x10d1c` at `0x10d38` (unconditional back-edge) -/

/-- `nextPC` slot of `coreControlFlowNextState Y pc` is `pc + 4`. -/
theorem coreNextPc (Y : State) (pc : BitVec 64) :
    (coreControlFlowNextState Y pc).regs.get? nextPC = some (Sail.BitVec.addInt pc 4) := by
  change (Y.regs.insert nextPC (Sail.BitVec.addInt pc 4)).get? nextPC = _
  rw [Std.ExtDHashMap.get?_insert]; simp

/-- Any register other than `nextPC` reads through `coreControlFlowNextState Y pc` back to `Y`. -/
theorem coreGetInc (Y : State) (pc : BitVec 64) (r : Register) (hnp : r ≠ nextPC) :
    (coreControlFlowNextState Y pc).regs.get? r = Y.regs.get? r := by
  simpa [coreControlFlowNextState] using
    writeReg_read_unchanged Y nextPC r (Sail.BitVec.addInt pc 4) hnp

/-- The `j 0x10d1c` back-edge (`JAL imm x0`, `imm` byte-offset `-28`), lifted through the generated
`try_step`.  Fetch bytes at `0x10d38` are `6f f0 5f fe` (`fe5ff06f`); the jump target is
`pc + sext imm = 0x10d1c`. -/
theorem memcpy_step_j (stepNo : Nat) (state : State)
    (retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d38) 0x6f#8 0xf0#8 0x5f#8 0xfe#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d38)
          (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21)))
        (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21)) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  obtain ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeRead, pcLow0, pcLow1,
    alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩ := platform
  have base : BaseInstructionEncoding 0x6f#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x6f#8 0xf0#8 0x5f#8 0xfe#8 = (0xfe5ff06f : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x6f#8 0xf0#8 0x5f#8 0xfe#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1FFFE4#21, zreg)) := by
    rw [wordEq]; exact ext_decode_j_memcpy_run _ privRead mseccfgBits mseccfgRead
  have hPCx : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d38)).regs.get? PC = some (BitVec.ofNat 64 0x10d38) := by
    simpa [coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC PC
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d38) 4) (by decide)).trans pcRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d38))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d38))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d38) 4) := by
    unfold get_next_pc
    exact readReg_run _ nextPC _ (coreNextPc _ _)
  have hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d38))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d38))
      (BitVec.ofNat 64 0x10d38) :=
    readReg_run _ PC _ hPCx
  have hmisax : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d38)).regs.get? misa = some misaBits := by
    simpa [coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC misa
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d38) 4) (by decide)).trans misaRead
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d38))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d38))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisax]
  have hsum : (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21))
      = BitVec.ofNat 64 0x10d1c := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  have halign : Sail.BitVec.access
      (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21)) 0 = 0#1 := by
    rw [hsum]; decide
  have hbit1 : Sail.BitVec.access
      (BitVec.ofNat 64 0x10d38 + sign_extend (m := 64) (0x1FFFE4#21)) 1 = 0#1 := by
    rw [hsum]; decide
  exact tryStepJRetires stepNo state (BitVec.ofNat 64 0x10d38) (BitVec.ofNat 64 0x10d38) retired
    (0x1FFFE4#21) inhibit config 0x6f#8 0xf0#8 0x5f#8 0xfe#8
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d38) 4) (_get_Misa_C misaBits == 1#1)
    ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeRead, pcLow0, pcLow1,
      alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩
    noMMIO bytes interrupts base decode notExpected hlink hpc halign hbit1 hzca
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

end BinaryFv.Keccak
