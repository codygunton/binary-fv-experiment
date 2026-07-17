import BinaryFv.RiscV.Platform.StoreTranslation
import BinaryFv.RiscV.Platform.StoreMemoryWrite

/-!
# Aligned double-word store execution contract

This module proves that the generated `execute_STORE` for an aligned, width-8 (double-word)
store runs to `RETIRE_SUCCESS` and that its only state effect is the physical `writeBytes` at the
destination address.

The two abstracted foundation contracts are reused directly:

* `translateAddr_machine_store_run` (Machine-mode Bare identity translation of a store-data
  access), from `StoreTranslationContract`;
* `mem_write_value_priv_store_run` (the physical write chain down to `writeBytes`), from
  `StoreMemoryWriteContract`.

Everything between them — `effectivePrivilege`, `mem_write_value`, `mem_write_ea`, the
`untilFuelM` single-chunk loop inside `vmem_write_addr`, `vmem_write`, and `execute_STORE` — is
threaded here with a small `Runs`-in-`SailME` calculus (`RunsME`) mirroring `StoreFrame`'s
`PreservesX2E` decomposition, but tracking the concrete post-state pinned by the `writeBytes`
hypothesis.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType
open mem_payload
open page_based_mem_type
open write_kind

/-! ## `RunsME`: a `Runs` calculus for the `SailME` error monad -/

/-- A `SailME` action completes normally (no `throw`) from `before` to `after`, returning
`result`.  `SailME ε α = ExceptT (Error ⊕ ε) SailM α`; running it to a successful `Except.ok`
value is exactly the non-throwing case. -/
def RunsME {ε α : Type} (action : SailME ε α) (before after : State) (result : α) : Prop :=
  Runs (ExceptT.run action) before after (Except.ok result)

/-- Composing two normally-completing `SailME` actions. -/
theorem RunsME.bind {ε α β : Type} {first : SailME ε α} {next : α → SailME ε β}
    {before middle after : State} {value : α} {result : β}
    (hFirst : RunsME first before middle value)
    (hNext : RunsME (next value) middle after result) :
    RunsME (first >>= next) before after result := by
  change Runs (ExceptT.run first >>= ExceptT.bindCont next) before after (Except.ok result)
  exact Runs.bind hFirst hNext

/-- A pure `SailME` value leaves the state fixed. -/
theorem RunsME.pure {ε α : Type} (value : α) (s : State) :
    RunsME (Pure.pure value : SailME ε α) s s value := rfl

/-- Lift a normally-completing ordinary Sail action into `RunsME`. -/
theorem RunsME.lift {ε α : Type} (action : SailM α) (before after : State) (value : α)
    (hAction : Runs action before after value) :
    RunsME (liftM action : SailME ε α) before after value := by
  change Runs (ExceptT.run (liftM action : SailME ε α)) before after (Except.ok value)
  change Runs (Except.ok <$> action) before after (Except.ok value)
  unfold Runs at hAction ⊢
  simp only [EStateM.run, EStateM.instMonad, EStateM.map] at hAction ⊢
  rw [hAction]

/-- Unwrap the generated `SailME.run` around a normally-completing action. -/
theorem RunsME.run {α : Type} (action : SailME α α) (before after : State) (result : α)
    (h : RunsME action before after result) :
    Runs (Sail.SailME.run action) before after result := by
  unfold Sail.SailME.run PreSail.PreSailME.run
  refine Runs.bind h ?_
  rfl

/-- A one-iteration `untilFuelM` (fuel `1`, condition true after the body) runs the body once. -/
theorem RunsME.untilFuelM_one {ε α : Type} (cond : α → SailME ε Bool) (init : α)
    (body : α → SailME ε α) (before middle after : State) (xval : α)
    (hBody : RunsME (body init) before middle xval)
    (hCond : RunsME (cond xval) middle after true) :
    RunsME (untilFuelM 1 cond init body) before after xval := by
  simp only [untilFuelM]
  refine RunsME.bind hBody ?_
  refine RunsME.bind hCond ?_
  exact RunsME.pure xval after

/-! ## Reused facts and small primitive contracts -/

/-- Machine-mode store-data access keeps its effective privilege when `mstatus.MPRV = 0`
(re-derived; `StoreTranslationContract`'s copy is private). -/
theorem effectivePrivilege_store_machine_run (state : State) (mstatusBits : BitVec 64)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1) :
    Runs (effectivePrivilege (MemoryAccessType.Store mem_payload.Data) mstatusBits .Machine)
      state state .Machine := by
  unfold Runs effectivePrivilege
  rw [mprvZero]
  rfl

/-- A satisfied `assert` is a no-op. -/
theorem assert_true_run (state : State) (message : String) :
    Runs (PreSail.assert true message) state state () := rfl

/-- `mem_write_ea` for a plain (non-release, non-conditional) store runs to `.Ok ()`. -/
theorem mem_write_ea_store_run (state : State) (addr : BitVec 64) (width : Nat) :
    Runs (mem_write_ea (physaddr.Physaddr addr) width false false false) state state (.Ok ()) := by
  unfold mem_write_ea
  simp only [Bool.or_self, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine Runs.bind (write_kind_of_flags_plain_run state) ?_
  rfl

/-- The `mem_write_value` entry point for a Machine-mode store: reads privilege, then runs the
physical write chain to `.Ok true` with only the `writeBytes` effect. -/
theorem mem_write_value_store_run (s s' : State) (paddr : physaddr) {width : Nat}
    (data : BitVec (8 * width)) (mstatusBits : BitVec 64)
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (physAccess :
      Runs (phys_access_check (Store Data) PBMT_PMA .Machine paddr width false) s s none)
    (noMMIO : Runs (within_mmio_writable paddr width) s s false)
    (hwrite : Runs (PreSail.writeBytes (bits_of_physaddr paddr).toNat data) s s' true) :
    Runs (mem_write_value paddr width data (Store Data) PBMT_PMA false false false) s s'
      (.Ok true) := by
  unfold mem_write_value mem_write_value_meta
  refine Runs.bind (readReg_run s mstatus mstatusBits mstatusRead) ?_
  refine Runs.bind (readReg_run s cur_privilege .Machine privRead) ?_
  refine Runs.bind (effectivePrivilege_store_machine_run s mstatusBits mprvZero) ?_
  exact mem_write_value_priv_store_run s s' paddr data PBMT_PMA .Machine physAccess noMMIO hwrite

/-- Reducing an aligned width-8 store to a single-chunk write: `split_misaligned` yields `(1, 8)`. -/
theorem split_misaligned_aligned_run (state : State) (vaddr : virtaddr) (width : Nat)
    (aligned : is_aligned_vaddr vaddr width = true) :
    Runs (split_misaligned vaddr width) state state (1, width) := by
  unfold split_misaligned
  simp only [aligned, Bool.true_or, ↓reduceIte]
  rfl

/-- A full-width extraction is the identity. -/
theorem extractLsb_full (x : BitVec 64) : Sail.BitVec.extractLsb x 63 0 = x := by
  unfold Sail.BitVec.extractLsb
  bv_decide

/-- Adding the integer `0` to a bitvector is the identity. -/
theorem addInt_zero (x : BitVec 64) : Sail.BitVec.addInt x 0 = x := by
  unfold Sail.BitVec.addInt
  simp

/-! ## Aligned double-word store -/

theorem vmem_write_addr_dword_run (s s' : State) (dstBits mstatusBits : BitVec 64)
    (data : BitVec (8 * 8))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr dstBits) 8 = true)
    (physAccess :
      Runs (phys_access_check (Store Data) PBMT_PMA .Machine (physaddr.Physaddr dstBits) 8 false)
        s s none)
    (noMMIO : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 8) s s false)
    (hwrite : Runs (PreSail.writeBytes dstBits.toNat data) s s' true) :
    Runs (vmem_write_addr (virtaddr.Virtaddr dstBits) 8 data (Store Data) false false false)
      s s' (.Ok true) := by
  unfold vmem_write_addr
  have hguard : LeanRV64DExecutable.Functions.not (is_aligned_vaddr (virtaddr.Virtaddr dstBits) 8)
      = false := by rw [aligned]; rfl
  simp only [is_store_conditional, Bool.false_eq_true, Bool.false_and, ↓reduceIte, hguard]
  apply RunsME.run
  refine RunsME.bind (RunsME.pure () s) ?_
  refine RunsME.bind
    (RunsME.lift _ s s (1, 8)
      (split_misaligned_aligned_run s (virtaddr.Virtaddr dstBits) 8 aligned)) ?_
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
            (BitVec.setWidth 64 (Sail.BitVec.extractLsb data 63 0))) s s' true
          rw [extractLsb_full, BitVec.setWidth_eq]
          exact hwrite
        exact RunsME.pure true s'

/-- The generated `vmem_write` for an aligned double-word store: once the effective address has
been resolved to `dstBits`, the write runs to `.Ok true` with only the `writeBytes` effect. -/
theorem vmem_write_dword_run (s s' : State) (rs1 : regidx) (offset dstBits mstatusBits : BitVec 64)
    (data : BitVec (8 * 8))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 offset (Store Data) 8) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr dstBits) 8 = true)
    (physAccess :
      Runs (phys_access_check (Store Data) PBMT_PMA .Machine (physaddr.Physaddr dstBits) 8 false)
        s s none)
    (noMMIO : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 8) s s false)
    (hwrite : Runs (PreSail.writeBytes dstBits.toNat data) s s' true) :
    Runs (vmem_write rs1 offset 8 data (Store Data) false false false) s s' (.Ok true) := by
  unfold vmem_write
  apply RunsME.run
  refine RunsME.bind (middle := s) (value := virtaddr.Virtaddr dstBits) ?vaddr ?writeAddr
  case vaddr =>
    refine RunsME.bind (RunsME.lift _ s s (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)) addrReg) ?_
    exact RunsME.pure (virtaddr.Virtaddr dstBits) s
  case writeAddr =>
    exact RunsME.lift _ s s' (Sail.Ok true)
      (vmem_write_addr_dword_run s s' dstBits mstatusBits data mstatusRead privRead mprvZero
        aligned physAccess noMMIO hwrite)

/-! ## Aligned double-word store instruction -/

theorem execute_STORE_dword_run (s s' : State) (rs2 rs1 : regidx)
    (dstBits mstatusBits : BitVec 64) (dataBits : BitVec (8 * 8))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (dataReg : Runs (rX_bits rs2) s s dataBits)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) 0#12) (Store Data) 8) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr dstBits) 8 = true)
    (physAccess :
      Runs (phys_access_check (Store Data) PBMT_PMA .Machine (physaddr.Physaddr dstBits) 8 false)
        s s none)
    (noMMIO : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 8) s s false)
    (hwrite : Runs (PreSail.writeBytes dstBits.toNat dataBits) s s' true) :
    Runs (execute_STORE 0#12 rs2 rs1 8) s s' (.Retire_Success ()) := by
  unfold execute_STORE
  refine Runs.bind (assert_true_run s _) ?_
  refine Runs.bind dataReg ?_
  refine Runs.bind (run_pure s _) ?_
  refine Runs.bind
    (vmem_write_dword_run s s' rs1 (sign_extend (m := 64) 0#12) dstBits mstatusBits _
      mstatusRead privRead mprvZero addrReg aligned physAccess noMMIO ?hw) ?_
  case hw =>
    change Runs (PreSail.writeBytes dstBits.toNat
      (BitVec.setWidth 64 (Sail.BitVec.extractLsb dataBits 63 0))) s s' true
    rw [extractLsb_full, BitVec.setWidth_eq]
    exact hwrite
  exact run_pure s' _

end BinaryFv.RiscV
