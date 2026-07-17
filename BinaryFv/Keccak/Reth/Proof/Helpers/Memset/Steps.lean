import BinaryFv.Keccak.Reth.Proof.Helpers.Memset.Defs

/-!
# `memset` step lemmas

One lemma per instruction of the `memset` loop body, each lifting the generated `try_step`.
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

/-! ## Step 0: `bne a5, a2, 0x10d48` at the loop head `L = 0x10d40` (taken while `i ≠ n`) -/

/-- The loop-head conditional branch, taken (`a5 = i ≠ n = a2`), lifted through the generated
`try_step`.  Fetch bytes at `0x10d40` are `63 94 c7 00` (`00c79463 = bne a5,a2,+8`); the target is
`pc + 8 = 0x10d48`. -/
theorem memset_step_bne_taken (stepNo : Nat) (state : State)
    (pcVal a2v retired : BitVec 64) (mseccfgBits : BitVec 64) (inhibit : BitVec 32)
    (config : BitVec 64) (i : Nat)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d40) 0x63#8 0x94#8 0xc7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d40)).regs.get? x15 = some (BitVec.ofNat 64 i))
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d40)).regs.get? x12 = some a2v)
    (hneq : BitVec.ofNat 64 i ≠ a2v)
    (hpcRead : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d40)).regs.get? PC = some pcVal)
    (misaBits : BitVec 64)
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d40)).regs.get? misa = some misaBits)
    (halign : Sail.BitVec.access (pcVal + sign_extend (m := 64) (8#13)) 0 = 0#1)
    (hbit1 : Sail.BitVec.access (pcVal + sign_extend (m := 64) (8#13)) 1 = 0#1) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d40) (pcVal + sign_extend (m := 64) (8#13)))
        (pcVal + sign_extend (m := 64) (8#13)) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x63#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8 = (0x00c79463 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (8#13, .Regidx 12#5, .Regidx 15#5, .BNE)) := by
    rw [wordEq]; exact ext_decode_bne_a5_a2_run _ privRead mseccfgBits mseccfgRead
  have hcondEq : (BitVec.ofNat 64 i != a2v) = true := by
    rw [bne_iff_ne]; exact hneq
  have hcond : Runs (bTypeTaken (.Regidx 12#5) (.Regidx 15#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      true := by
    have := bTypeTaken_bne_run _ (BitVec.ofNat 64 i) a2v h15 h12
    rwa [hcondEq] at this
  have hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      pcVal :=
    readReg_run _ PC pcVal hpcRead
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisa]
  exact tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x10d40) pcVal retired
    (8#13) (.Regidx 12#5) (.Regidx 15#5) .BNE inhibit config 0x63#8 0x94#8 0xc7#8 0x00#8
    (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected
    hcond hpc halign hbit1 hzca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead

/-! ## Step 1: `add a4, a0, a5` at `0x10d48` (`a4 = dst + i`) -/

/-- The `add a4, a0, a5` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d48` are `33 07 f5 00` (`00f50733`); the destination write is `x14 ↦ dstVal + a5Val`. -/
theorem memset_step_add_a4 (stepNo : Nat) (state : State)
    (dstVal a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d48) 0x33#8 0x07#8 0xf5#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h10 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d48)).regs.get? x10 = some dstVal)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d48)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d48) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d48)).regs.insert x14 (dstVal + a5Val) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d48) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x33#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x33#8 0x07#8 0xf5#8 0x00#8 = (0x00f50733 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x33#8 0x07#8 0xf5#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD)) := by
    rw [wordEq]; exact ext_decode_add_a4_a0_a5_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d48))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d48) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d48)).regs.insert x14 (dstVal + a5Val) }
      (.Retire_Success ()) := by
    change Runs (execute_RTYPE (.Regidx 15#5) (.Regidx 10#5) (.Regidx 14#5) .ADD) _ _ _
    unfold Runs
    exact execute_add_a4_a0_a5 _ dstVal a5Val h10 h15
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d48) retired inhibit config
    0x33#8 0x07#8 0xf5#8 0x00#8 (.RTYPE (.Regidx 15#5, .Regidx 10#5, .Regidx 14#5, .ADD))
    platform noMMIO bytes interrupts base decode notExpected exec
    (msGpFrameNextPc _ _ x14 _ (by decide))
    (msGpFrameGet _ _ x14 _ hart_state (by decide) (by decide))
    (msGpFrameGet _ _ x14 _ minstret_increment (by decide) (by decide))
    (msGpFrameGet _ _ x14 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 2: `sb a1, 0(a4)` at `0x10d4c` (`mem[dst + i] = low byte of a1`) -/

/-- The `sb a1, 0(a4)` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d4c` are `23 00 b7 00` (`00b70023`); the low byte of `a1 = byteval` (`storedByte =
setWidth₈ byteval`) is written to `dstAddrBits = dst + i`, yielding the opaque post-write state
`s'`. -/
theorem memset_step_sb (stepNo : Nat) (state s' : State)
    (dstAddrBits mstatusBits retired mseccfgBits byteval : BitVec 64) (storedByte : BitVec (8 * 1))
    (hstored : storedByte = BitVec.setWidth 8 byteval)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d4c) 0x23#8 0x00#8 0xb7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d4c)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d4c)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hx11 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d4c)).regs.get? x11 = some byteval)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 14#5) (sign_extend (m := 64) 0#12)
      (Store Data) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstAddrBits)))
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstAddrBits) 1 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      none)
    (noMMIOw : Runs (within_mmio_writable (physaddr.Physaddr dstAddrBits) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      false)
    (hwrite : Runs (PreSail.writeBytes dstAddrBits.toNat storedByte)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      s' true) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d4c) 4) retired)
      false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x23#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x23#8 0x00#8 0xb7#8 0x00#8 = (0x00b70023 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x23#8 0x00#8 0xb7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (0#12, .Regidx 11#5, .Regidx 14#5, 1)) := by
    rw [wordEq]; exact ext_decode_sb_a1_a4_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.STORE (0#12, .Regidx 11#5, .Regidx 14#5, 1)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d4c))
      s' (.Retire_Success ()) := by
    change Runs (execute_STORE 0#12 (.Regidx 11#5) (.Regidx 14#5) 1) _ _ _
    exact execute_STORE_sb_full_run _ s' (.Regidx 11#5) (.Regidx 14#5) 0#12 dstAddrBits mstatusBits
      byteval storedByte (hstored.trans (extractLsb_lowbyte byteval).symm) mstatusReadX privReadX
      mprvZero (rX_bits_x11_run _ _ hx11) addrReg physAccess noMMIOw hwrite
  have regsEq : s'.regs =
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x10d4c)).regs :=
    writeBytes_preserves_regs dstAddrBits.toNat storedByte _ s' hwrite
  refine tryStepFallThroughRetires stepNo state s' (BitVec.ofNat 64 0x10d4c) retired inhibit config
    0x23#8 0x00#8 0xb7#8 0x00#8 (.STORE (0#12, .Regidx 11#5, .Regidx 14#5, 1))
    platform noMMIO bytes interrupts base decode notExpected exec ?_ ?_ ?_ ?_
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  · rw [regsEq]; exact msCoreNextPc _ _
  · rw [regsEq]; exact msCoreGetInc _ _ hart_state (by decide)
  · rw [regsEq]; exact msCoreGetInc _ _ minstret_increment (by decide)
  · rw [regsEq]; exact msCoreGetInc _ _ minstret (by decide)

/-! ## Step 3: `addi a5, a5, 1` at `0x10d50` (`i++`) -/

/-- The `addi a5, a5, 1` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d50` are `93 87 17 00` (`00178793`); the destination write is `x15 ↦ a5Val + sext 1`. -/
theorem memset_step_addi_a5 (stepNo : Nat) (state : State)
    (a5Val retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d50) 0x93#8 0x87#8 0x17#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d50)).regs.get? x15 = some a5Val) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d50) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d50)).regs.insert x15 (a5Val + sign_extend (m := 64) 1#12) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d50) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x93#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x93#8 0x87#8 0x17#8 0x00#8 = (0x00178793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x87#8 0x17#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_addi_a5_a5_1_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d50))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d50) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d50)).regs.insert x15 (a5Val + sign_extend (m := 64) 1#12) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 1#12 (.Regidx 15#5) (.Regidx 15#5) .ADDI) _ _ _
    unfold Runs
    exact execute_addi_a5_a5_1 _ a5Val h15
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d50) retired inhibit config
    0x93#8 0x87#8 0x17#8 0x00#8 (.ITYPE (1#12, .Regidx 15#5, .Regidx 15#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (msGpFrameNextPc _ _ x15 _ (by decide))
    (msGpFrameGet _ _ x15 _ hart_state (by decide) (by decide))
    (msGpFrameGet _ _ x15 _ minstret_increment (by decide) (by decide))
    (msGpFrameGet _ _ x15 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 4: `j 0x10d40` at `0x10d54` (unconditional back-edge) -/

/-- The `j 0x10d40` back-edge (`JAL imm x0`, `imm` byte-offset `-20`), lifted through the generated
`try_step`.  Fetch bytes at `0x10d54` are `6f f0 df fe` (`fedff06f`); the jump target is
`pc + sext imm = 0x10d40`. -/
theorem memset_step_j (stepNo : Nat) (state : State)
    (retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d54) 0x6f#8 0xf0#8 0xdf#8 0xfe#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d54)
          (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21)))
        (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21)) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  obtain ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeRead, pcLow0, pcLow1,
    alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩ := platform
  have base : BaseInstructionEncoding 0x6f#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x6f#8 0xf0#8 0xdf#8 0xfe#8 = (0xfedff06f : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x6f#8 0xf0#8 0xdf#8 0xfe#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1FFFEC#21, zreg)) := by
    rw [wordEq]; exact ext_decode_j_memset_run _ privRead mseccfgBits mseccfgRead
  have hPCx : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d54)).regs.get? PC = some (BitVec.ofNat 64 0x10d54) := by
    simpa [coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC PC
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d54) 4) (by decide)).trans pcRead
  have hlink : Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d54))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d54))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d54) 4) := by
    unfold get_next_pc
    exact readReg_run _ nextPC _ (msCoreNextPc _ _)
  have hpc : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d54))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d54))
      (BitVec.ofNat 64 0x10d54) :=
    readReg_run _ PC _ hPCx
  have hmisax : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d54)).regs.get? misa = some misaBits := by
    simpa [coreControlFlowNextState] using
      (writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC misa
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d54) 4) (by decide)).trans misaRead
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d54))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d54))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisax]
  have hsum : (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21))
      = BitVec.ofNat 64 0x10d40 := by
    simp only [sign_extend, Sail.BitVec.signExtend]; bv_decide
  have halign : Sail.BitVec.access
      (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21)) 0 = 0#1 := by
    rw [hsum]; decide
  have hbit1 : Sail.BitVec.access
      (BitVec.ofNat 64 0x10d54 + sign_extend (m := 64) (0x1FFFEC#21)) 1 = 0#1 := by
    rw [hsum]; decide
  exact tryStepJRetires stepNo state (BitVec.ofNat 64 0x10d54) (BitVec.ofNat 64 0x10d54) retired
    (0x1FFFEC#21) inhibit config 0x6f#8 0xf0#8 0xdf#8 0xfe#8
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d54) 4) (_get_Misa_C misaBits == 1#1)
    ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeRead, pcLow0, pcLow1,
      alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩
    noMMIO bytes interrupts base decode notExpected hlink hpc halign hbit1 hzca
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Exit step lemmas: `bne` not taken, then `ret` -/

/-- The loop-head `bne a5, a2` NOT taken (`a5 = i = n = a2`): retires with `PC = pc + 4 = 0x10d44`. -/
theorem memset_step_bne_not_taken (stepNo : Nat) (state : State)
    (a2v retired mseccfgBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64) (i : Nat)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d40) 0x63#8 0x94#8 0xc7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (h15 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d40)).regs.get? x15 = some (BitVec.ofNat 64 i))
    (h12 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d40)).regs.get? x12 = some a2v)
    (heq : BitVec.ofNat 64 i = a2v) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d40) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x63#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8 = (0x00c79463 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x94#8 0xc7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (8#13, .Regidx 12#5, .Regidx 15#5, .BNE)) := by
    rw [wordEq]; exact ext_decode_bne_a5_a2_run _ privRead mseccfgBits mseccfgRead
  have hcond : Runs (bTypeTaken (.Regidx 12#5) (.Regidx 15#5) .BNE)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d40))
      false := by
    have h := bTypeTaken_bne_run _ (BitVec.ofNat 64 i) a2v h15 h12
    rwa [show (BitVec.ofNat 64 i != a2v) = false by rw [heq]; simp] at h
  exact tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 0x10d40) retired
    (8#13) (.Regidx 12#5) (.Regidx 15#5) .BNE inhibit config 0x63#8 0x94#8 0xc7#8 0x00#8
    platform noMMIO bytes interrupts base decode notExpected hcond hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- `ret` (`jalr x0, 0(ra)`) at `0x10d44`: retires with `PC = ra` (bit 0 cleared).  Fetch bytes are
`67 80 00 00` (`00008067`). -/
theorem memset_step_ret (stepNo : Nat) (state : State)
    (rs1Val retired mseccfgBits misaBits : BitVec 64) (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d44) 0x67#8 0x80#8 0x00#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      rs1Val)
    (hbit1 : Sail.BitVec.access rs1Val 1 = 0#1)
    (hElp : Runs (update_elp_state (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      ())
    (hmisa : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d44)).regs.get? misa = some misaBits) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44)
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
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d44) 4) := by
    unfold get_next_pc; exact readReg_run _ nextPC _ (msCoreNextPc _ _)
  have hzca : Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d44))
      (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, hmisa]
  exact tryStepRetRetires stepNo state (BitVec.ofNat 64 0x10d44) retired (.Regidx 1#5)
    (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d44) 4) rs1Val inhibit config 0x67#8 0x80#8 0x00#8 0x00#8
    (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts base decode notExpected hElp hlink
    hrs1 hbit1 hzca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Entry step lemma: `li a5, 0` -/

/-- The entry `li a5, 0` at `0x10d3c` (`a5 ↦ 0`), lifted through the generated `try_step`.  Fetch
bytes are `93 07 00 00` (`00000793`); `PC` ticks to the loop head `0x10d40`. -/
theorem memset_step_li (stepNo : Nat) (state : State) (retired mseccfgBits : BitVec 64)
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d3c) 0x93#8 0x07#8 0x00#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d3c) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d3c)).regs.insert x15 (BitVec.ofNat 64 0) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d3c) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x93#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x93#8 0x07#8 0x00#8 0x00#8 = (0x00000793 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x07#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI)) := by
    rw [wordEq]; exact ext_decode_li_a5_0_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d3c))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d3c) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d3c)).regs.insert x15 (BitVec.ofNat 64 0) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0#12 (.Regidx 0#5) (.Regidx 15#5) .ADDI) _ _ _
    unfold Runs
    exact execute_li_a5_0 _
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d3c) retired inhibit config
    0x93#8 0x07#8 0x00#8 0x00#8 (.ITYPE (0#12, .Regidx 0#5, .Regidx 15#5, .ADDI))
    platform noMMIO bytes interrupts base decode notExpected exec
    (msGpFrameNextPc _ _ x15 _ (by decide))
    (msGpFrameGet _ _ x15 _ hart_state (by decide) (by decide))
    (msGpFrameGet _ _ x15 _ minstret_increment (by decide) (by decide))
    (msGpFrameGet _ _ x15 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

end BinaryFv.Keccak
