import BinaryFv.RiscV.Instruction.Execute.Store

/-!
# Aligned byte store execution contract

This module proves that the generated `execute_STORE` for a width-1 (byte) store runs to
`RETIRE_SUCCESS` and that its only state effect is the physical `writeBytes` at the destination
address.  It is the width-1 analogue of `execute_STORE_dword_run` in `StoreExecuteContract`, and it
reuses the same `RunsME` calculus, the same reduced chain lemmas, and the same abstracted foundation
contracts (`translateAddr_machine_store_run`, `mem_write_value_priv_store_run`, threaded via
`mem_write_value_store_run`).

The only structural difference from the double-word case is that a byte store is aligned for *every*
address (`addr mod 1 = 0`), so the alignment obligation is discharged internally
(`is_aligned_vaddr_one`) rather than taken as a hypothesis.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType
open mem_payload
open page_based_mem_type
open write_kind

/-! ## Byte-specific facts -/

/-- Every address is aligned to a byte: `addr mod 1 = 0`. -/
theorem is_aligned_vaddr_one (v : virtaddr) : is_aligned_vaddr v 1 = true := by
  obtain ⟨addr⟩ := v
  unfold is_aligned_vaddr
  simp [Int.tmod_one]

/-- A full width-8 extraction is the identity (byte analogue of `extractLsb_full`). -/
theorem extractLsb_full_byte (x : BitVec 8) : Sail.BitVec.extractLsb x 7 0 = x := by
  unfold Sail.BitVec.extractLsb
  bv_decide

/-- A one-byte generated memory write has exactly one sparse-memory insertion as its effect. -/
theorem writeBytes_byte_run (state : State) (address : Nat) (value : BitVec 8) :
    Runs (PreSail.writeBytes (n := 1) address value) state
      { state with mem := state.mem.insert address value } true := by
  unfold PreSail.writeBytes
  let updated : State := { state with mem := state.mem.insert address value }
  have write : Runs (PreSail.writeByte address value) state updated () :=
    writeByte_run state address value
  have finish : Runs (pure true) updated updated true := rfl
  have bound : Runs (PreSail.writeByte address value >>= fun _ => pure true)
      state updated true := Runs.bind write finish
  simpa [List.ofFn_succ, updated] using bound

/-! ## Aligned byte store -/

/-- Under the configured Machine-mode, Bare-translation, pointer-masking-disabled setup, a store
effective address is exactly its base register plus its signed offset. -/
theorem get_transformed_data_addr_machine_store_run (state : State) (rs : regidx) (width : Nat)
    (base offset mstatusBits mseccfgBits : BitVec 64)
    (baseRead : Runs (rX_bits rs) state state base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled) :
    Runs (get_transformed_data_addr rs offset (Store Data) width) state state
      (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + offset))) := by
  have address : Runs (ext_data_get_addr rs offset (Store Data) width) state state
      (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + offset))) := by
    unfold ext_data_get_addr
    exact Runs.bind baseRead rfl
  unfold get_transformed_data_addr
  refine Runs.bind address ?_
  have transformed : Runs (transform_effective_address (virtaddr.Virtaddr (base + offset))
      (Store Data)) state state (virtaddr.Virtaddr (base + offset)) := by
    have machineEq : (Privilege.Machine == Privilege.Machine) = true := rfl
    have bareEq : (SATPMode.Bare == SATPMode.Bare) = true := rfl
    have pointerMaskingBase :
        (Store Data != InstructionFetch ()) = true ∧
          (Store Data != Load PageTableEntry) = true ∧
            (Store Data != Store PageTableEntry) = true ∧
              LeanRV64DExecutable.Functions.xlen = 64 :=
      ⟨by decide, by decide, by decide, rfl⟩
    unfold Runs transform_effective_address get_pmlen is_pmm_applicable get_pmm translationMode
    simp [PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
      EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable, MonadState.get,
      MonadStateOf.get, getThe, mstatusRead, privilegeRead, mseccfgRead, mprvZero, pmmDisabled,
      pointerMaskingBase, machineEq, bareEq, effectivePrivilege, pm_transform_PA]
    change zero_extend (Sail.BitVec.extractLsb (base + offset) 63 0) = base + offset
    unfold zero_extend Sail.BitVec.zeroExtend
    rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq, extractLsb_full]
  exact Runs.bind transformed rfl

theorem vmem_write_addr_byte_run (s s' : State) (dstBits mstatusBits : BitVec 64)
    (data : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (physAccess :
      Runs (phys_access_check (Store Data) PBMT_PMA .Machine (physaddr.Physaddr dstBits) 1 false)
        s s none)
    (noMMIO : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 1) s s false)
    (hwrite : Runs (PreSail.writeBytes dstBits.toNat data) s s' true) :
    Runs (vmem_write_addr (virtaddr.Virtaddr dstBits) 1 data (Store Data) false false false)
      s s' (.Ok true) := by
  have aligned : is_aligned_vaddr (virtaddr.Virtaddr dstBits) 1 = true := is_aligned_vaddr_one _
  unfold vmem_write_addr
  have hguard : LeanRV64DExecutable.Functions.not (is_aligned_vaddr (virtaddr.Virtaddr dstBits) 1)
      = false := by rw [aligned]; rfl
  simp only [is_store_conditional, Bool.false_eq_true, Bool.false_and, ↓reduceIte, hguard]
  apply RunsME.run
  refine RunsME.bind (RunsME.pure () s) ?_
  refine RunsME.bind
    (RunsME.lift _ s s (1, 1)
      (split_misaligned_aligned_run s (virtaddr.Virtaddr dstBits) 1 aligned)) ?_
  refine RunsME.bind (middle := s') (value := (true, 0, true)) ?loop ?tail
  case tail => exact RunsME.pure (Sail.Ok true) s'
  case loop =>
    refine RunsME.bind (middle := s') (value := (true, 0, true)) ?loopFuel
      (RunsME.pure (true, 0, true) s')
    refine RunsME.untilFuelM_one _ _ _ s s' s' (true, 0, true) ?hBody ?hCond
    case hCond => exact RunsME.pure true s'
    case hBody =>
      simp only [misaligned_order, sys_misaligned_order_decreasing, bits_of_virtaddr, addInt_zero,
        Bool.false_eq_true, ↓reduceIte, Int.reduceSub, Int.reduceMul, Int.reduceToNat,
        Int.toNat_zero, Int.ofNat_zero, Nat.reduceMul, beq_self_eq_true]
      refine RunsME.bind (RunsME.lift _ s s () (assert_true_run s _)) ?_
      refine RunsME.bind (middle := s') (value := true) ?inner ?final
      case final => exact RunsME.pure (true, 0, true) s'
      case inner =>
        refine RunsME.bind
          (RunsME.lift _ s s (Sail.Ok (physaddr.Physaddr dstBits, PBMT_PMA, init_ext_ptw))
            (translateAddr_machine_store_run s dstBits mstatusBits mstatusRead privRead mprvZero)) ?_
        refine RunsME.bind (RunsME.lift _ s s () (assert_true_run s _)) ?_
        refine RunsME.bind
          (RunsME.lift _ s s (Sail.Ok ()) (mem_write_ea_store_run s dstBits _)) ?_
        refine RunsME.bind
          (RunsME.lift _ s s' (Sail.Ok true)
            (mem_write_value_store_run s s' (physaddr.Physaddr dstBits) _ mstatusBits mstatusRead
              privRead mprvZero physAccess noMMIO ?hw)) ?_
        case hw =>
          change Runs (PreSail.writeBytes dstBits.toNat
            (BitVec.setWidth 8 (Sail.BitVec.extractLsb data 7 0))) s s' true
          rw [extractLsb_full_byte, BitVec.setWidth_eq]
          exact hwrite
        exact RunsME.pure true s'

/-- The generated `vmem_write` for an aligned byte store: once the effective address has been
resolved to `dstBits`, the write runs to `.Ok true` with only the `writeBytes` effect. -/
theorem vmem_write_byte_run (s s' : State) (rs1 : regidx) (offset dstBits mstatusBits : BitVec 64)
    (data : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 offset (Store Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)))
    (physAccess :
      Runs (phys_access_check (Store Data) PBMT_PMA .Machine (physaddr.Physaddr dstBits) 1 false)
        s s none)
    (noMMIO : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 1) s s false)
    (hwrite : Runs (PreSail.writeBytes dstBits.toNat data) s s' true) :
    Runs (vmem_write rs1 offset 1 data (Store Data) false false false) s s' (.Ok true) := by
  unfold vmem_write
  apply RunsME.run
  refine RunsME.bind (middle := s) (value := virtaddr.Virtaddr dstBits) ?vaddr ?writeAddr
  case vaddr =>
    refine RunsME.bind (RunsME.lift _ s s (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)) addrReg) ?_
    exact RunsME.pure (virtaddr.Virtaddr dstBits) s
  case writeAddr =>
    exact RunsME.lift _ s s' (Sail.Ok true)
      (vmem_write_addr_byte_run s s' dstBits mstatusBits data mstatusRead privRead mprvZero
        physAccess noMMIO hwrite)

/-! ## Aligned byte store instruction -/

theorem execute_STORE_byte_run (s s' : State) (rs2 rs1 : regidx) (imm : BitVec 12)
    (dstBits mstatusBits dataBits : BitVec 64)
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (dataReg : Runs (rX_bits rs2) s s dataBits)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Store Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)))
    (physAccess :
      Runs (phys_access_check (Store Data) PBMT_PMA .Machine (physaddr.Physaddr dstBits) 1 false)
        s s none)
    (noMMIO : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 1) s s false)
    (hwrite : Runs (PreSail.writeBytes (n := 1) dstBits.toNat
      (Sail.BitVec.extractLsb dataBits 7 0)) s s' true) :
    Runs (execute_STORE imm rs2 rs1 1) s s' (.Retire_Success ()) := by
  unfold execute_STORE
  refine Runs.bind (assert_true_run s _) ?_
  refine Runs.bind dataReg ?_
  refine Runs.bind (run_pure s _) ?_
  refine Runs.bind
    (vmem_write_byte_run s s' rs1 (sign_extend (m := 64) imm) dstBits mstatusBits _
      mstatusRead privRead mprvZero addrReg physAccess noMMIO ?hw) ?_
  case hw =>
    change Runs (PreSail.writeBytes dstBits.toNat
      (BitVec.setWidth 8 (Sail.BitVec.extractLsb dataBits 7 0))) s s' true
    simpa [BitVec.setWidth_eq] using hwrite
  exact run_pure s' _

end BinaryFv.RiscV
