import BinaryFv.Keccak.Reth.Proof.XorBlock.Steps.Alu

/-!
# `xor_block` memory body steps (`lbu` / `ld` / `sd`)
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

/-! ## Deliverable 2b: memory body step lemmas (`lbu` / `ld` / `sd`)

The load/store data-access preconditions — effective-address resolution, alignment, byte ownership,
`phys_access_check`, MMIO decision, and the physical read/write — are carried abstractly, exactly the
stage-2 trust boundary. -/

/-- `lbu` at 0x10c74 into `x13` from `1(a1)`. -/
theorem step_lbu_10c74 (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c74) 0x83#8 0xc6#8 0x15#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 1#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)).regs.insert x13 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c74) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x83#8 0xc6#8 0x15#8 0x00#8 = (0x0015c683 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc6#8 0x15#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (1#12, .Regidx 11#5, .Regidx 13#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a3_a1_1_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (1#12, .Regidx 11#5, .Regidx 13#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c74)).regs.insert x13 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 1#12 (.Regidx 11#5) (.Regidx 13#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 1#12 (.Regidx 11#5) (.Regidx 13#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x13_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c74) retired mseccfgBits inhibit config
    0x83#8 0xc6#8 0x15#8 0x00#8 (.LOAD (1#12, .Regidx 11#5, .Regidx 13#5, true, 1))
    x13 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10c78 into `x14` from `2(a1)`. -/
theorem step_lbu_10c78 (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c78) 0x03#8 0xc7#8 0x25#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 2#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)).regs.insert x14 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c78) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x03#8 0xc7#8 0x25#8 0x00#8 = (0x0025c703 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc7#8 0x25#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (2#12, .Regidx 11#5, .Regidx 14#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a4_a1_2_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (2#12, .Regidx 11#5, .Regidx 14#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c78)).regs.insert x14 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 2#12 (.Regidx 11#5) (.Regidx 14#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 2#12 (.Regidx 11#5) (.Regidx 14#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x14_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c78) retired mseccfgBits inhibit config
    0x03#8 0xc7#8 0x25#8 0x00#8 (.LOAD (2#12, .Regidx 11#5, .Regidx 14#5, true, 1))
    x14 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10c7c into `x15` from `3(a1)`. -/
theorem step_lbu_10c7c (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c7c) 0x83#8 0xc7#8 0x35#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 3#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)).regs.insert x15 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c7c) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x83#8 0xc7#8 0x35#8 0x00#8 = (0x0035c783 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc7#8 0x35#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (3#12, .Regidx 11#5, .Regidx 15#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a5_a1_3_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (3#12, .Regidx 11#5, .Regidx 15#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c7c)).regs.insert x15 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 3#12 (.Regidx 11#5) (.Regidx 15#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 3#12 (.Regidx 11#5) (.Regidx 15#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x15_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c7c) retired mseccfgBits inhibit config
    0x83#8 0xc7#8 0x35#8 0x00#8 (.LOAD (3#12, .Regidx 11#5, .Regidx 15#5, true, 1))
    x15 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10c80 into `x16` from `0(a1)`. -/
theorem step_lbu_10c80 (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c80) 0x03#8 0xc8#8 0x05#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 0#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)).regs.insert x16 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c80) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x03#8 0xc8#8 0x05#8 0x00#8 = (0x0005c803 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc8#8 0x05#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0#12, .Regidx 11#5, .Regidx 16#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a6_a1_0_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (0#12, .Regidx 11#5, .Regidx 16#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c80)).regs.insert x16 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 0#12 (.Regidx 11#5) (.Regidx 16#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 0#12 (.Regidx 11#5) (.Regidx 16#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x16_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c80) retired mseccfgBits inhibit config
    0x03#8 0xc8#8 0x05#8 0x00#8 (.LOAD (0#12, .Regidx 11#5, .Regidx 16#5, true, 1))
    x16 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10c98 into `x15` from `5(a1)`. -/
theorem step_lbu_10c98 (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c98) 0x83#8 0xc7#8 0x55#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 5#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)).regs.insert x15 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c98) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x83#8 0xc7#8 0x55#8 0x00#8 = (0x0055c783 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc7#8 0x55#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (5#12, .Regidx 11#5, .Regidx 15#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a5_a1_5_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (5#12, .Regidx 11#5, .Regidx 15#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c98)).regs.insert x15 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 5#12 (.Regidx 11#5) (.Regidx 15#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 5#12 (.Regidx 11#5) (.Regidx 15#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x15_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c98) retired mseccfgBits inhibit config
    0x83#8 0xc7#8 0x55#8 0x00#8 (.LOAD (5#12, .Regidx 11#5, .Regidx 15#5, true, 1))
    x15 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10c9c into `x16` from `4(a1)`. -/
theorem step_lbu_10c9c (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10c9c) 0x03#8 0xc8#8 0x45#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 4#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)).regs.insert x16 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10c9c) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x03#8 0xc8#8 0x45#8 0x00#8 = (0x0045c803 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x03#8 0xc8#8 0x45#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (4#12, .Regidx 11#5, .Regidx 16#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a6_a1_4_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (4#12, .Regidx 11#5, .Regidx 16#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10c9c)).regs.insert x16 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 4#12 (.Regidx 11#5) (.Regidx 16#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 4#12 (.Regidx 11#5) (.Regidx 16#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x16_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10c9c) retired mseccfgBits inhibit config
    0x03#8 0xc8#8 0x45#8 0x00#8 (.LOAD (4#12, .Regidx 11#5, .Regidx 16#5, true, 1))
    x16 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10ca0 into `x17` from `6(a1)`. -/
theorem step_lbu_10ca0 (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ca0) 0x83#8 0xc8#8 0x65#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 6#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)).regs.insert x17 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca0) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x83#8 0xc8#8 0x65#8 0x00#8 = (0x0065c883 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc8#8 0x65#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (6#12, .Regidx 11#5, .Regidx 17#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a7_a1_6_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (6#12, .Regidx 11#5, .Regidx 17#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca0)).regs.insert x17 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 6#12 (.Regidx 11#5) (.Regidx 17#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 6#12 (.Regidx 11#5) (.Regidx 17#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x17_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10ca0) retired mseccfgBits inhibit config
    0x83#8 0xc8#8 0x65#8 0x00#8 (.LOAD (6#12, .Regidx 11#5, .Regidx 17#5, true, 1))
    x17 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `lbu` at 0x10ca4 into `x5` from `7(a1)`. -/
theorem step_lbu_10ca4 (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10ca4) 0x83#8 0xc2#8 0x75#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) 7#12)
      (Load Data) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)).regs.insert x5 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10ca4) 4) retired) false := by
  have privRead := plat.2.2.2.2.2.1
  have mseccfgRead := plat.2.2.2.2.2.2
  have wordEq : fetchWord 0x83#8 0xc2#8 0x75#8 0x00#8 = (0x0075c283 : BitVec 32) := by
    decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc2#8 0x75#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (7#12, .Regidx 11#5, .Regidx 5#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_t0_a1_7_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (7#12, .Regidx 11#5, .Regidx 5#5, true, 1))) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4))
      { (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)) with regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10ca4)).regs.insert x5 (zero_extend (m := 64) v) } (.Retire_Success ()) := by
    change Runs (execute_LOAD 7#12 (.Regidx 11#5) (.Regidx 5#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 7#12 (.Regidx 11#5) (.Regidx 5#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg (is_aligned_vaddr_one _) physAccess noMMIOr hmem
      (wX_x5_run _ (zero_extend (m := 64) v))
  exact gpStep stepNo state (BitVec.ofNat 64 0x10ca4) retired mseccfgBits inhibit config
    0x83#8 0xc2#8 0x75#8 0x00#8 (.LOAD (7#12, .Regidx 11#5, .Regidx 5#5, true, 1))
    x5 (zero_extend (m := 64) v) plat counters (by unfold BaseInstructionEncoding; decide)
    decode exec (by decide) (by decide) (by decide) (by decide)

/-- `ld a4, 0(a0)` (aligned double-word load, `rd = a4 = x14`, `rs1 = a0 = x10`). -/
theorem ldStep (stepNo : Nat) (state : State)
    (pc srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 8))
    (inhibit : BitVec 32) (config : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (plat : StepPlatform state pc b0 b1 b2 b3 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (base : BaseInstructionEncoding b0)
    (decode : Runs (ext_decode (fetchWord b0 b1 b2 b3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0#12, .Regidx 10#5, .Regidx 14#5, false, 8)))
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get?
      mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get?
      cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 10#5) (sign_extend (m := 64) 0#12)
      (Load Data) 8)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcAddrBits) 8 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 8 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 8)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 8 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).mem.get?
        (srcAddrBits.toNat + i) = some (leBytes 8 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
            x14 v }
        (Sail.BitVec.addInt pc 4) retired) false := by
  have exec : Runs (execute (.LOAD (0#12, .Regidx 10#5, .Regidx 14#5, false, 8)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
          x14 v } (.Retire_Success ()) := by
    change Runs (execute_LOAD 0#12 (.Regidx 10#5) (.Regidx 14#5) false 8) _ _ _
    exact execute_LOAD_ld_run _ _ 0#12 (.Regidx 10#5) (.Regidx 14#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg aligned physAccess noMMIOr hmem
      (wX_x14_run _ v)
  exact gpStep stepNo state pc retired mseccfgBits inhibit config b0 b1 b2 b3
    (.LOAD (0#12, .Regidx 10#5, .Regidx 14#5, false, 8)) x14 v
    plat counters base decode exec (by decide) (by decide) (by decide) (by decide)

/-- `sd a3, 0(a0)` (aligned double-word store, data `a3 = x13`, address `a0 = x10`); opaque
post-write state `s'`. -/
theorem sdStep (stepNo : Nat) (state s' : State)
    (pc dstAddrBits mstatusBits retired mseccfgBits : BitVec 64) (dataBits : BitVec (8 * 8))
    (inhibit : BitVec 32) (config : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (plat : StepPlatform state pc b0 b1 b2 b3 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (base : BaseInstructionEncoding b0)
    (decode : Runs (ext_decode (fetchWord b0 b1 b2 b3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (0#12, .Regidx 13#5, .Regidx 10#5, 8)))
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get?
      mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get?
      cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hx13 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? x13
      = some dataBits)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 10#5) (sign_extend (m := 64) 0#12)
      (Store Data) 8)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstAddrBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr dstAddrBits) 8 = true)
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstAddrBits) 8 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) none)
    (noMMIOw : Runs (within_mmio_writable (physaddr.Physaddr dstAddrBits) 8)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) false)
    (hwrite : Runs (PreSail.writeBytes dstAddrBits.toNat dataBits)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) s' true) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt pc 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, _privRead, _mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have exec : Runs (execute (.STORE (0#12, .Regidx 13#5, .Regidx 10#5, 8)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) s'
      (.Retire_Success ()) := by
    change Runs (execute_STORE 0#12 (.Regidx 13#5) (.Regidx 10#5) 8) _ _ _
    exact execute_STORE_dword_run _ s' (.Regidx 13#5) (.Regidx 10#5) dstAddrBits mstatusBits dataBits
      mstatusReadX privReadX mprvZero (rX_x13_run _ dataBits hx13) addrReg aligned physAccess
      noMMIOw hwrite
  have regsEq : s'.regs = (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs :=
    writeBytes_preserves_regs dstAddrBits.toNat dataBits _ s' hwrite
  refine tryStepFallThroughRetires stepNo state s' pc retired inhibit config b0 b1 b2 b3
    (.STORE (0#12, .Regidx 13#5, .Regidx 10#5, 8)) platform noMMIO bytes interrupts base decode
    notExpected exec ?_ ?_ ?_ ?_ hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead
  · rw [regsEq]; exact coreNextPc _ _
  · rw [regsEq]; exact coreGetInc _ _ hart_state (by decide)
  · rw [regsEq]; exact coreGetInc _ _ minstret_increment (by decide)
  · rw [regsEq]; exact coreGetInc _ _ minstret (by decide)

end BinaryFv.Keccak.XorBlock
