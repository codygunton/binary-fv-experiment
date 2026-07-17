import BinaryFv.Keccak.Reth.Proof.Helpers.Memcpy.Framing

/-!
# `memcpy` byte load/store steps

The `lbu`/`sb` pair that moves one byte per iteration.
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

/-! ## Step 3: `lbu a3, 0(a3)` at `0x10d28` (`a3 = mem[src + i]`)

The genuine load data-access preconditions — the effective-address resolution to `src + i`, the byte
alignment (trivial), `phys_access_check` yielding no fault, the no-MMIO decision, and byte ownership
of `mem[src+i] = v` — are carried abstractly, exactly the stage-2 trust boundary. -/

/-- The `lbu a3, 0(a3)` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d28` are `83 c6 06 00` (`0006c683`); the destination write is `x13 ↦ zext₆₄ v` where `v` is the
owned source byte at `srcAddrBits` (`= src + i`). -/
theorem memcpy_step_lbu (stepNo : Nat) (state : State)
    (srcAddrBits mstatusBits retired mseccfgBits : BitVec 64) (v : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d28) 0x83#8 0xc6#8 0x06#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d28)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d28)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr (.Regidx 13#5) (sign_extend (m := 64) 0#12)
      (Load Data) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcAddrBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcAddrBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcAddrBits) 1 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      none)
    (noMMIOr : Runs (within_mmio_readable (physaddr.Physaddr srcAddrBits) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x10d28)).mem.get? (srcAddrBits.toNat + i) = some (leBytes 1 v)[i]) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d28) with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x10d28)).regs.insert x13 (zero_extend (m := 64) v) }
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d28) 4) retired) false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x83#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x83#8 0xc6#8 0x06#8 0x00#8 = (0x0006c683 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x83#8 0xc6#8 0x06#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0#12, .Regidx 13#5, .Regidx 13#5, true, 1)) := by
    rw [wordEq]; exact ext_decode_lbu_a3_a3_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.LOAD (0#12, .Regidx 13#5, .Regidx 13#5, true, 1)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d28))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d28) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10d28)).regs.insert x13 (zero_extend (m := 64) v) }
      (.Retire_Success ()) := by
    change Runs (execute_LOAD 0#12 (.Regidx 13#5) (.Regidx 13#5) true 1) _ _ _
    exact execute_LOAD_lbu_run _ _ 0#12 (.Regidx 13#5) (.Regidx 13#5) srcAddrBits mstatusBits v
      mstatusReadX privReadX mprvZero addrReg aligned physAccess noMMIOr hmem
      (wX_bits_x13_run _ (zero_extend (m := 64) v))
  refine tryStepFallThroughRetires stepNo state _ (BitVec.ofNat 64 0x10d28) retired inhibit config
    0x83#8 0xc6#8 0x06#8 0x00#8 (.LOAD (0#12, .Regidx 13#5, .Regidx 13#5, true, 1))
    platform noMMIO bytes interrupts base decode notExpected exec
    (gpFrameNextPc _ _ x13 _ (by decide))
    (gpFrameGet _ _ x13 _ hart_state (by decide) (by decide))
    (gpFrameGet _ _ x13 _ minstret_increment (by decide) (by decide))
    (gpFrameGet _ _ x13 _ minstret (by decide) (by decide))
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-! ## Step 6: `sb a3, 0(a4)` at `0x10d34` (`mem[dst + i] = a3`)

The store data/address preconditions — the effective address resolving to `dst + i`, the byte
`phys_access_check`, no-MMIO, and the physical `writeBytes` — are carried abstractly (stage-2 trust
boundary).  The store's post-write state `s'` is opaque; `writeBytes_preserves_regs` recovers the
register frame. -/

/-- The `sb a3, 0(a4)` fall-through, lifted through the generated `try_step`.  Fetch bytes at
`0x10d34` are `23 00 d7 00` (`00d70023`); the low byte of `a3 = dataBits` is written to
`dstAddrBits = dst + i`, yielding the opaque post-write state `s'`. -/
theorem memcpy_step_sb (stepNo : Nat) (state s' : State)
    (dstAddrBits mstatusBits retired mseccfgBits : BitVec 64) (dataBits : BitVec (8 * 1))
    (inhibit : BitVec 32) (config : BitVec 64)
    (plat : StepPlatform state (BitVec.ofNat 64 0x10d34) 0x23#8 0x00#8 0xd7#8 0x00#8 mseccfgBits)
    (counters : StepCounters state retired inhibit config)
    (mstatusReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d34)).regs.get? mstatus = some mstatusBits)
    (privReadX : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d34)).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hx13 : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10d34)).regs.get? x13 = some (BitVec.setWidth 64 dataBits))
    (addrReg : Runs (get_transformed_data_addr (.Regidx 14#5) (sign_extend (m := 64) 0#12)
      (Store Data) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstAddrBits)))
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstAddrBits) 1 false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      none)
    (noMMIOw : Runs (within_mmio_writable (physaddr.Physaddr dstAddrBits) 1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      false)
    (hwrite : Runs (PreSail.writeBytes dstAddrBits.toNat dataBits)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      s' true) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired s' (Sail.BitVec.addInt (BitVec.ofNat 64 0x10d34) 4) retired)
      false := by
  obtain ⟨platform, noMMIO, bytes, interrupts, notExpected, privRead, mseccfgRead⟩ := plat
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have base : BaseInstructionEncoding 0x23#8 := by unfold BaseInstructionEncoding; decide
  have wordEq : fetchWord 0x23#8 0x00#8 0xd7#8 0x00#8 = (0x00d70023 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x23#8 0x00#8 0xd7#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (0#12, .Regidx 13#5, .Regidx 14#5, 1)) := by
    rw [wordEq]; exact ext_decode_sb_a3_a4_run _ privRead mseccfgBits mseccfgRead
  have exec : Runs (execute (.STORE (0#12, .Regidx 13#5, .Regidx 14#5, 1)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10d34))
      s' (.Retire_Success ()) := by
    change Runs (execute_STORE 0#12 (.Regidx 13#5) (.Regidx 14#5) 1) _ _ _
    exact execute_STORE_byte_run _ s' (.Regidx 13#5) (.Regidx 14#5) 0#12 dstAddrBits mstatusBits
      dataBits mstatusReadX privReadX mprvZero (rX_bits_x13_run _ _ hx13) addrReg physAccess
      noMMIOw hwrite
  have regsEq : s'.regs =
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x10d34)).regs :=
    writeBytes_preserves_regs dstAddrBits.toNat dataBits _ s' hwrite
  refine tryStepFallThroughRetires stepNo state s' (BitVec.ofNat 64 0x10d34) retired inhibit config
    0x23#8 0x00#8 0xd7#8 0x00#8 (.STORE (0#12, .Regidx 13#5, .Regidx 14#5, 1))
    platform noMMIO bytes interrupts base decode notExpected exec ?_ ?_ ?_ ?_
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead
  · rw [regsEq]; exact coreNextPc _ _
  · rw [regsEq]; exact coreGetInc _ _ hart_state (by decide)
  · rw [regsEq]; exact coreGetInc _ _ minstret_increment (by decide)
  · rw [regsEq]; exact coreGetInc _ _ minstret (by decide)

end BinaryFv.Keccak
