import BinaryFv.RiscV.Instruction.Execute.DataAddress
import BinaryFv.RiscV.Logic.SepLogic

/-!
# Aligned load execution contracts

This module is the read-side analogue of `BinaryFv.RiscV.Instruction.Execute.Store`.  It proves that the
generated `execute_LOAD` runs to `RETIRE_SUCCESS` for two widths
(`ld`, width 8; `lbu`, width 1), and that the only state effect is the `wX_bits rd` register write
of the loaded value.

The physical read is discharged with `SepLogic.readBytes_run_exact`; the platform checks
(alignment, `phys_access_check`, no-MMIO, Machine-mode Bare translation) are abstracted as clean
premises exactly like the store contract, and the effective-address resolution is threaded as a
`get_transformed_data_addr … → Ext_DataAddr_OK` premise.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType
open mem_payload
open page_based_mem_type
open read_kind
open BinaryFv.RiscV.Sep

/-! ## Physical read chain -/

/-- The physical `read_ram` for a plain load returns the little-endian recomposition of the owned
bytes with dropped metadata, leaving the state unchanged. -/
theorem read_ram_plain_run (s : State) (addr : BitVec 64) (vs : List (BitVec 8))
    (hmem : ∀ (i : Nat) (h : i < vs.length), s.mem.get? (addr.toNat + i) = some vs[i]) :
    Runs (read_ram Read_plain (physaddr.Physaddr addr) vs.length false) s s
      (leWord vs, default_meta) := by
  unfold LeanRV64DExecutable.Functions.read_ram
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Runs.bind (run_pure s _) ?_
  refine Runs.bind (middle := s) (value := Sail.Ok (leWord vs, none)) ?smr ?_
  case smr =>
    unfold Sail.ConcurrencyInterfaceV1.sail_mem_read
    exact Runs.bind (readBytes_run_exact s vs addr.toNat hmem) rfl
  rfl

/-- A plain (non-acquire, non-release, non-reserved) load selects `Read_plain`. -/
theorem read_kind_of_flags_plain_run (s : State) :
    Runs (read_kind_of_flags false false false) s s Read_plain := by
  unfold read_kind_of_flags
  rfl

/-- `checked_mem_read` for a Machine-mode plain load: with no access fault and no MMIO overlap the
read descends to `read_ram` and returns the little-endian recomposition of the owned bytes. -/
theorem checked_mem_read_load_run (s : State) (srcBits : BitVec 64) (vs : List (BitVec 8))
    (hmem : ∀ (i : Nat) (h : i < vs.length), s.mem.get? (srcBits.toNat + i) = some vs[i])
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) vs.length false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) vs.length) s s false) :
    Runs (checked_mem_read (Load Data) PBMT_PMA .Machine (physaddr.Physaddr srcBits) vs.length
      false false false false) s s (Sail.Ok (leWord vs, default_meta)) := by
  unfold checked_mem_read
  refine Runs.bind physAccess ?_
  refine Runs.bind noMMIO ?_
  refine Runs.bind (read_kind_of_flags_plain_run s) ?_
  refine Runs.bind (read_ram_plain_run s srcBits vs hmem) ?_
  rfl

/-- Machine-mode load-data access keeps its effective privilege when `mstatus.MPRV = 0`. -/
theorem effectivePrivilege_load_machine_run (state : State) (mstatusBits : BitVec 64)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1) :
    Runs (effectivePrivilege (MemoryAccessType.Load mem_payload.Data) mstatusBits .Machine)
      state state .Machine := by
  unfold Runs effectivePrivilege
  rw [mprvZero]
  rfl

/-- `mem_read_priv_meta` for an aligned Machine-mode plain load: the alignment guard and the
release/acquire cases are skipped, so the read is exactly `checked_mem_read`. -/
theorem mem_read_priv_meta_load_run (s : State) (srcBits : BitVec 64) (vs : List (BitVec 8))
    (hmem : ∀ (i : Nat) (h : i < vs.length), s.mem.get? (srcBits.toNat + i) = some vs[i])
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) vs.length false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) vs.length) s s false) :
    Runs (mem_read_priv_meta (Load Data) PBMT_PMA .Machine (physaddr.Physaddr srcBits) vs.length
      false false false false) s s (Sail.Ok (leWord vs, default_meta)) := by
  unfold mem_read_priv_meta
  simp only [Bool.or_self, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine Runs.bind (checked_mem_read_load_run s srcBits vs hmem physAccess noMMIO) ?_
  rfl

/-- `mem_read_priv` drops the metadata component from the result of `mem_read_priv_meta`. -/
theorem mem_read_priv_load_run (s : State) (srcBits : BitVec 64) (vs : List (BitVec 8))
    (hmem : ∀ (i : Nat) (h : i < vs.length), s.mem.get? (srcBits.toNat + i) = some vs[i])
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) vs.length false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) vs.length) s s false) :
    Runs (mem_read_priv (Load Data) PBMT_PMA .Machine (physaddr.Physaddr srcBits) vs.length
      false false false) s s (Sail.Ok (leWord vs)) := by
  unfold mem_read_priv
  refine Runs.bind (mem_read_priv_meta_load_run s srcBits vs hmem physAccess noMMIO) ?_
  rfl

/-- `mem_read` reads `mstatus`/`cur_privilege`, keeps Machine privilege (`MPRV = 0`), then runs the
Machine-mode privileged read to `Ok (leWord vs)`. -/
theorem mem_read_load_run (s : State) (srcBits mstatusBits : BitVec 64) (vs : List (BitVec 8))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hmem : ∀ (i : Nat) (h : i < vs.length), s.mem.get? (srcBits.toNat + i) = some vs[i])
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) vs.length false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) vs.length) s s false) :
    Runs (mem_read (Load Data) PBMT_PMA (physaddr.Physaddr srcBits) vs.length false false false)
      s s (Sail.Ok (leWord vs)) := by
  unfold mem_read
  refine Runs.bind (readReg_run s mstatus mstatusBits mstatusRead) ?_
  refine Runs.bind (readReg_run s cur_privilege .Machine privRead) ?_
  refine Runs.bind (effectivePrivilege_load_machine_run s mstatusBits mprvZero) ?_
  exact mem_read_priv_load_run s srcBits vs hmem physAccess noMMIO

/-! ## Machine-mode Bare translation of a load-data access -/

/-- Machine-mode translation selects the generated Bare mode. -/
private theorem translationMode_machine_run' (state : State) :
    Runs (translationMode .Machine) state state .Bare := by
  rfl

/-- A load-data access is not a generated shadow-stack access. -/
private theorem load_not_shadow_stack_run (state : State) :
    Runs (is_shadow_stack_access (MemoryAccessType.Load mem_payload.Data)) state state false := by
  rfl

/-- Generated Machine-mode load-data translation is the identity Bare translation. -/
theorem translateAddr_machine_load_run (state : State) (vaddr mstatusBits : BitVec 64)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1) :
    Runs (translateAddr (virtaddr.Virtaddr vaddr) (MemoryAccessType.Load mem_payload.Data))
      state state (.Ok (physaddr.Physaddr vaddr, .PBMT_PMA, init_ext_ptw)) := by
  have hMstatus : Runs (Sail.readReg mstatus) state state mstatusBits :=
    readReg_run state mstatus mstatusBits mstatusRead
  have hPrivilege : Runs (Sail.readReg cur_privilege) state state .Machine :=
    readReg_run state cur_privilege .Machine privilegeRead
  have hEffective : Runs (effectivePrivilege (MemoryAccessType.Load mem_payload.Data)
      mstatusBits .Machine) state state .Machine :=
    effectivePrivilege_load_machine_run state mstatusBits mprvZero
  have hMode : Runs (translationMode .Machine) state state .Bare :=
    translationMode_machine_run' state
  have hShadow : Runs (is_shadow_stack_access (MemoryAccessType.Load mem_payload.Data))
      state state false :=
    load_not_shadow_stack_run state
  unfold translateAddr
  refine runsFetchSailMELift (action := Sail.readReg mstatus) (next := ?_)
    (before := state) (middle := state) (after := state) (value := mstatusBits)
    (result := (.Ok (physaddr.Physaddr vaddr, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hMstatus ?_
  refine runsFetchSailMELift (action := Sail.readReg cur_privilege) (next := ?_)
    (before := state) (middle := state) (after := state) (value := .Machine)
    (result := (.Ok (physaddr.Physaddr vaddr, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hPrivilege ?_
  refine runsFetchSailMELift
    (action := effectivePrivilege (MemoryAccessType.Load mem_payload.Data) mstatusBits .Machine)
    (next := ?_)
    (before := state) (middle := state) (after := state) (value := .Machine)
    (result := (.Ok (physaddr.Physaddr vaddr, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hEffective ?_
  refine runsFetchSailMELift (action := translationMode .Machine) (next := ?_)
    (before := state) (middle := state) (after := state) (value := .Bare)
    (result := (.Ok (physaddr.Physaddr vaddr, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hMode ?_
  refine runsFetchSailMELift
    (action := is_shadow_stack_access (MemoryAccessType.Load mem_payload.Data)) (next := ?_)
    (before := state) (middle := state) (after := state) (value := false)
    (result := (.Ok (physaddr.Physaddr vaddr, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hShadow ?_
  have bareEq : ((SATPMode.Bare == SATPMode.Bare) : Bool) = true := rfl
  rw [bareEq]
  rfl

/-- Compatibility wrapper for callers that carry the five machine-address facts separately. -/
theorem get_transformed_data_addr_machine_load_run (state : State) (rs : regidx)
    (base offset mstatusBits mseccfgBits : BitVec 64)
    (baseRead : Runs (rX_bits rs) state state base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled) :
    Runs (get_transformed_data_addr rs offset (Load Data) 1) state state
      (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + offset))) :=
  get_transformed_data_addr_machine_data_run .load state rs 1 base offset mstatusBits mseccfgBits
    baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled

/-! ## Aligned single-chunk read loop -/

/-- Adding the integer `0` to a bitvector is the identity. -/
private theorem addInt_zero' (x : BitVec 64) : Sail.BitVec.addInt x 0 = x := by
  unfold Sail.BitVec.addInt
  simp

/-- Overwriting all 64 bits of the zero word with `v` yields `v`. -/
private theorem updateSubrange_zeros_setWidth64 (v : BitVec 64) :
    Sail.BitVec.updateSubrange (zeros : BitVec 64) 63 0 (BitVec.setWidth 64 v) = v := by
  unfold Sail.BitVec.updateSubrange Sail.BitVec.updateSubrange' zeros
  bv_decide

/-- Overwriting all 8 bits of the zero byte with `v` yields `v`. -/
private theorem updateSubrange_zeros_setWidth8 (v : BitVec 8) :
    Sail.BitVec.updateSubrange (zeros : BitVec 8) 7 0 (BitVec.setWidth 8 v) = v := by
  unfold Sail.BitVec.updateSubrange Sail.BitVec.updateSubrange' zeros
  bv_decide

/-- Overwriting all 32 bits of the zero word with `v` yields `v`. -/
private theorem updateSubrange_zeros_setWidth32 (v : BitVec 32) :
    Sail.BitVec.updateSubrange (zeros : BitVec 32) 31 0 (BitVec.setWidth 32 v) = v := by
  unfold Sail.BitVec.updateSubrange Sail.BitVec.updateSubrange' zeros
  bv_decide

/-- Overwriting all 16 bits of the zero half-word with `v` yields `v`. -/
private theorem updateSubrange_zeros_setWidth16 (v : BitVec 16) :
    Sail.BitVec.updateSubrange (zeros : BitVec 16) 15 0 (BitVec.setWidth 16 v) = v := by
  unfold Sail.BitVec.updateSubrange Sail.BitVec.updateSubrange' zeros
  bv_decide

/-- `bits_of_virtaddr` of `Virtaddr b` is `b`. -/
private theorem bits_of_virtaddr_mk (b : BitVec 64) :
    bits_of_virtaddr (virtaddr.Virtaddr b) = b := rfl

/-- `vmem_read` only adds effective-address resolution around `vmem_read_addr`; this composition is
independent of the scalar load width. -/
theorem vmem_read_of_addr_run (width : Nat) (s : State) (rs : regidx)
    (offset srcBits : BitVec 64) (v : BitVec (8 * width))
    (addrReg : Runs (get_transformed_data_addr rs offset (Load Data) width) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (readAddr : Runs
      (vmem_read_addr (virtaddr.Virtaddr srcBits) width (Load Data) false false false)
      s s (.Ok v)) :
    Runs (vmem_read rs offset width (Load Data) false false false) s s (.Ok v) := by
  unfold vmem_read
  apply RunsME.run
  refine RunsME.bind (middle := s) (value := virtaddr.Virtaddr srcBits) ?vaddr ?readAddr
  case vaddr =>
    refine RunsME.bind
      (RunsME.lift _ s s (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)) addrReg) ?_
    exact RunsME.pure (virtaddr.Virtaddr srcBits) s
  case readAddr => exact RunsME.lift _ s s (Sail.Ok v) readAddr

theorem vmem_read_addr_dword_run (s : State) (srcBits mstatusBits : BitVec 64)
    (v : BitVec (8 * 8))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 8 = true)
    (hread : Runs (mem_read (Load Data) PBMT_PMA (physaddr.Physaddr srcBits) 8 false false false)
      s s (Sail.Ok v)) :
    Runs (vmem_read_addr (virtaddr.Virtaddr srcBits) 8 (Load Data) false false false) s s
      (.Ok v) := by
  unfold vmem_read_addr
  have hguard : LeanRV64DExecutable.Functions.not (is_aligned_vaddr (virtaddr.Virtaddr srcBits) 8)
      = false := by rw [aligned]; rfl
  simp only [Bool.false_eq_true, ↓reduceIte, hguard]
  apply RunsME.run
  refine RunsME.bind (RunsME.pure () s) ?_
  refine RunsME.bind
    (RunsME.lift _ s s (1, 8)
      (split_misaligned_aligned_run s (virtaddr.Virtaddr srcBits) 8 aligned)) ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, Bool.false_eq_true, ↓reduceIte,
    Int.reduceToNat, Int.reduceMul, Int.reduceSub, Nat.reduceMul, BitVec.setWidth_eq]
  refine RunsME.bind (middle := s)
    (value := (Sail.BitVec.updateSubrange (zeros : BitVec 64) 63 0 (BitVec.setWidth 64 v),
      true, 0)) ?loopwrap ?tail
  case tail =>
    show RunsME
      (Pure.pure (Sail.Ok
        (Sail.BitVec.updateSubrange (zeros : BitVec 64) 63 0 (BitVec.setWidth 64 v)))) s s
      (Sail.Ok v)
    rw [updateSubrange_zeros_setWidth64]
    exact RunsME.pure _ s
  case loopwrap =>
    refine RunsME.bind (middle := s)
      (value := (Sail.BitVec.updateSubrange (zeros : BitVec 64) 63 0 (BitVec.setWidth 64 v),
        true, 0)) ?fuel ?wrap
    case wrap => exact RunsME.pure _ s
    case fuel =>
      refine RunsME.untilFuelM_one _ _ _ s s s
        (Sail.BitVec.updateSubrange (zeros : BitVec 64) 63 0 (BitVec.setWidth 64 v), true, 0)
        ?hBody ?hCond
      case hCond => exact RunsME.pure true s
      case hBody =>
        dsimp only [bits_of_virtaddr_mk]
        simp only [Int.ofNat_zero, Int.zero_mul, addInt_zero', Int.reduceMul, Int.reduceSub,
          Int.reduceToNat, Int.reduceAdd, Nat.reduceMul, beq_self_eq_true, ↓reduceIte]
        refine RunsME.bind (RunsME.lift _ s s () (assert_true_run s _)) ?_
        refine RunsME.bind (middle := s)
          (value := Sail.BitVec.updateSubrange (zeros : BitVec 64) 63 0 (BitVec.setWidth 64 v))
          ?blk ?out
        case out => exact RunsME.pure _ s
        case blk =>
          refine RunsME.bind
            (RunsME.lift _ s s (Sail.Ok (physaddr.Physaddr srcBits, PBMT_PMA, init_ext_ptw))
              (translateAddr_machine_load_run s srcBits mstatusBits mstatusRead privRead
                mprvZero)) ?_
          refine RunsME.bind (RunsME.lift _ s s (Sail.Ok v) hread) ?_
          refine RunsME.bind (RunsME.pure () s) ?_
          exact RunsME.pure _ s

/-- `vmem_read` for an aligned double word: once the effective address resolves to `srcBits`, the
read runs to `Ok v` with the state unchanged. -/
theorem vmem_read_dword_run (s : State) (rs : regidx) (offset srcBits mstatusBits : BitVec 64)
    (v : BitVec (8 * 8))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs offset (Load Data) 8) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 8 = true)
    (hread : Runs (mem_read (Load Data) PBMT_PMA (physaddr.Physaddr srcBits) 8 false false false)
      s s (Sail.Ok v)) :
    Runs (vmem_read rs offset 8 (Load Data) false false false) s s (.Ok v) := by
  exact vmem_read_of_addr_run 8 s rs offset srcBits v addrReg
    (vmem_read_addr_dword_run s srcBits mstatusBits v mstatusRead privRead mprvZero aligned hread)

/-! ## Aligned word read loop -/

theorem vmem_read_addr_word_run (s : State) (srcBits mstatusBits : BitVec 64)
    (v : BitVec (8 * 4))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 4 = true)
    (hread : Runs (mem_read (Load Data) PBMT_PMA (physaddr.Physaddr srcBits) 4 false false false)
      s s (Sail.Ok v)) :
    Runs (vmem_read_addr (virtaddr.Virtaddr srcBits) 4 (Load Data) false false false) s s
      (.Ok v) := by
  unfold vmem_read_addr
  have hguard : LeanRV64DExecutable.Functions.not (is_aligned_vaddr (virtaddr.Virtaddr srcBits) 4)
      = false := by rw [aligned]; rfl
  simp only [Bool.false_eq_true, ↓reduceIte, hguard]
  apply RunsME.run
  refine RunsME.bind (RunsME.pure () s) ?_
  refine RunsME.bind
    (RunsME.lift _ s s (1, 4)
      (split_misaligned_aligned_run s (virtaddr.Virtaddr srcBits) 4 aligned)) ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, Bool.false_eq_true, ↓reduceIte,
    Int.reduceToNat, Int.reduceMul, Int.reduceSub, Nat.reduceMul, BitVec.setWidth_eq]
  refine RunsME.bind (middle := s)
    (value := (Sail.BitVec.updateSubrange (zeros : BitVec 32) 31 0 (BitVec.setWidth 32 v),
      true, 0)) ?loopwrap ?tail
  case tail =>
    show RunsME
      (Pure.pure (Sail.Ok
        (Sail.BitVec.updateSubrange (zeros : BitVec 32) 31 0 (BitVec.setWidth 32 v)))) s s
      (Sail.Ok v)
    rw [updateSubrange_zeros_setWidth32]
    exact RunsME.pure _ s
  case loopwrap =>
    refine RunsME.bind (middle := s)
      (value := (Sail.BitVec.updateSubrange (zeros : BitVec 32) 31 0 (BitVec.setWidth 32 v),
        true, 0)) ?fuel ?wrap
    case wrap => exact RunsME.pure _ s
    case fuel =>
      refine RunsME.untilFuelM_one _ _ _ s s s
        (Sail.BitVec.updateSubrange (zeros : BitVec 32) 31 0 (BitVec.setWidth 32 v), true, 0)
        ?hBody ?hCond
      case hCond => exact RunsME.pure true s
      case hBody =>
        dsimp only [bits_of_virtaddr_mk]
        simp only [Int.ofNat_zero, Int.zero_mul, addInt_zero', Int.reduceMul, Int.reduceSub,
          Int.reduceToNat, Int.reduceAdd, Nat.reduceMul, beq_self_eq_true, ↓reduceIte]
        refine RunsME.bind (RunsME.lift _ s s () (assert_true_run s _)) ?_
        refine RunsME.bind (middle := s)
          (value := Sail.BitVec.updateSubrange (zeros : BitVec 32) 31 0 (BitVec.setWidth 32 v))
          ?blk ?out
        case out => exact RunsME.pure _ s
        case blk =>
          refine RunsME.bind
            (RunsME.lift _ s s (Sail.Ok (physaddr.Physaddr srcBits, PBMT_PMA, init_ext_ptw))
              (translateAddr_machine_load_run s srcBits mstatusBits mstatusRead privRead
                mprvZero)) ?_
          refine RunsME.bind (RunsME.lift _ s s (Sail.Ok v) hread) ?_
          refine RunsME.bind (RunsME.pure () s) ?_
          exact RunsME.pure _ s

private theorem leWord_leBytes_id4 (v : BitVec (8 * 4)) : leWord (leBytes 4 v) = v := by
  have h := leWord_leBytes 4 v
  simpa using h

theorem vmem_read_word_run (s : State) (rs : regidx) (offset srcBits mstatusBits : BitVec 64)
    (v : BitVec (8 * 4))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs offset (Load Data) 4) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 4 = true)
    (hread : Runs (mem_read (Load Data) PBMT_PMA (physaddr.Physaddr srcBits) 4 false false false)
      s s (Sail.Ok v)) :
    Runs (vmem_read rs offset 4 (Load Data) false false false) s s (.Ok v) := by
  exact vmem_read_of_addr_run 4 s rs offset srcBits v addrReg
    (vmem_read_addr_word_run s srcBits mstatusBits v mstatusRead privRead mprvZero aligned hread)

/-- An aligned four-byte load from explicitly represented little-endian memory. -/
theorem vmem_read_word_from_bytes_run (s : State) (rs : regidx)
    (offset srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 4))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs offset (Load Data) 4) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 4 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 4 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 4) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 4 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 4 v)[i]) :
    Runs (vmem_read rs offset 4 (Load Data) false false false) s s (.Ok v) := by
  have hread := mem_read_load_run s srcBits mstatusBits (leBytes 4 v) mstatusRead privRead
    mprvZero hmem physAccess noMMIO
  rw [leWord_leBytes_id4] at hread
  exact vmem_read_word_run s rs offset srcBits mstatusBits v mstatusRead privRead mprvZero
    addrReg aligned hread

/-! ## Aligned half-word read loop -/

theorem vmem_read_addr_half_run (s : State) (srcBits mstatusBits : BitVec 64)
    (v : BitVec (8 * 2))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 2 = true)
    (hread : Runs (mem_read (Load Data) PBMT_PMA (physaddr.Physaddr srcBits) 2 false false false)
      s s (Sail.Ok v)) :
    Runs (vmem_read_addr (virtaddr.Virtaddr srcBits) 2 (Load Data) false false false) s s
      (.Ok v) := by
  unfold vmem_read_addr
  have hguard : LeanRV64DExecutable.Functions.not
      (is_aligned_vaddr (virtaddr.Virtaddr srcBits) 2) = false := by
    rw [aligned]
    rfl
  simp only [Bool.false_eq_true, ↓reduceIte, hguard]
  apply RunsME.run
  refine RunsME.bind (RunsME.pure () s) ?_
  refine RunsME.bind
    (RunsME.lift _ s s (1, 2)
      (split_misaligned_aligned_run s (virtaddr.Virtaddr srcBits) 2 aligned)) ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, Bool.false_eq_true, ↓reduceIte,
    Int.reduceToNat, Int.reduceMul, Int.reduceSub, Nat.reduceMul, BitVec.setWidth_eq]
  refine RunsME.bind (middle := s)
    (value := (Sail.BitVec.updateSubrange (zeros : BitVec 16) 15 0 (BitVec.setWidth 16 v),
      true, 0)) ?loopwrap ?tail
  case tail =>
    show RunsME
      (Pure.pure (Sail.Ok
        (Sail.BitVec.updateSubrange (zeros : BitVec 16) 15 0 (BitVec.setWidth 16 v)))) s s
      (Sail.Ok v)
    rw [updateSubrange_zeros_setWidth16]
    exact RunsME.pure _ s
  case loopwrap =>
    refine RunsME.bind (middle := s)
      (value := (Sail.BitVec.updateSubrange (zeros : BitVec 16) 15 0 (BitVec.setWidth 16 v),
        true, 0)) ?fuel ?wrap
    case wrap => exact RunsME.pure _ s
    case fuel =>
      refine RunsME.untilFuelM_one _ _ _ s s s
        (Sail.BitVec.updateSubrange (zeros : BitVec 16) 15 0 (BitVec.setWidth 16 v), true, 0)
        ?hBody ?hCond
      case hCond => exact RunsME.pure true s
      case hBody =>
        dsimp only [bits_of_virtaddr_mk]
        simp only [Int.ofNat_zero, Int.zero_mul, addInt_zero', Int.reduceMul, Int.reduceSub,
          Int.reduceToNat, Int.reduceAdd, Nat.reduceMul, beq_self_eq_true, ↓reduceIte]
        refine RunsME.bind (RunsME.lift _ s s () (assert_true_run s _)) ?_
        refine RunsME.bind (middle := s)
          (value := Sail.BitVec.updateSubrange (zeros : BitVec 16) 15 0 (BitVec.setWidth 16 v))
          ?blk ?out
        case out => exact RunsME.pure _ s
        case blk =>
          refine RunsME.bind
            (RunsME.lift _ s s (Sail.Ok (physaddr.Physaddr srcBits, PBMT_PMA, init_ext_ptw))
              (translateAddr_machine_load_run s srcBits mstatusBits mstatusRead privRead
                mprvZero)) ?_
          refine RunsME.bind (RunsME.lift _ s s (Sail.Ok v) hread) ?_
          refine RunsME.bind (RunsME.pure () s) ?_
          exact RunsME.pure _ s

private theorem leWord_leBytes_id2 (v : BitVec (8 * 2)) : leWord (leBytes 2 v) = v := by
  have h := leWord_leBytes 2 v
  simpa using h

theorem vmem_read_half_run (s : State) (rs : regidx) (offset srcBits mstatusBits : BitVec 64)
    (v : BitVec (8 * 2))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs offset (Load Data) 2) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 2 = true)
    (hread : Runs (mem_read (Load Data) PBMT_PMA (physaddr.Physaddr srcBits) 2 false false false)
      s s (Sail.Ok v)) :
    Runs (vmem_read rs offset 2 (Load Data) false false false) s s (.Ok v) := by
  exact vmem_read_of_addr_run 2 s rs offset srcBits v addrReg
    (vmem_read_addr_half_run s srcBits mstatusBits v mstatusRead privRead mprvZero aligned hread)

/-- An aligned two-byte load from explicitly represented little-endian memory. -/
theorem vmem_read_half_from_bytes_run (s : State) (rs : regidx)
    (offset srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 2))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs offset (Load Data) 2) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 2 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 2 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 2) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 2 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 2 v)[i]) :
    Runs (vmem_read rs offset 2 (Load Data) false false false) s s (.Ok v) := by
  have hread := mem_read_load_run s srcBits mstatusBits (leBytes 2 v) mstatusRead privRead
    mprvZero hmem physAccess noMMIO
  rw [leWord_leBytes_id2] at hread
  exact vmem_read_half_run s rs offset srcBits mstatusBits v mstatusRead privRead mprvZero
    addrReg aligned hread

/-! ## Aligned double-word load instruction (`ld`) -/

/-- Signed extension of a full-width 64-bit value is the identity. -/
private theorem extend_value_signed_64 (v : BitVec (8 * 8)) :
    extend_value false v = v := by
  unfold extend_value
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

/-- `leWord` recomposes the little-endian bytes of a 64-bit word back to itself. -/
private theorem leWord_leBytes_id8 (v : BitVec (8 * 8)) : leWord (leBytes 8 v) = v := by
  have h := leWord_leBytes 8 v
  simpa using h

/-- `leWord` recomposes the little-endian bytes of an 8-bit byte back to itself. -/
private theorem leWord_leBytes_id1 (v : BitVec (8 * 1)) : leWord (leBytes 1 v) = v := by
  have h := leWord_leBytes 1 v
  simpa using h

/-- `ld rd, imm(rs1)` (width 8): reads the 64-bit little-endian word held (as its little-endian
bytes) at the resolved effective address and writes it (unchanged, since a full-width load neither
zero- nor sign-extends) into `rd`, retiring successfully.

The platform checks are abstracted as clean premises exactly like `execute_STORE_dword_run`:
effective-address resolution (`addrReg`), alignment, Machine-mode translation
(`mstatusRead`/`privRead`/`mprvZero`), `phys_access_check` returning no fault (`physAccess`), no
MMIO overlap (`noMMIO`), and ownership of the source bytes (`hmem`, a `readBytes_run_exact`-style
hypothesis over the little-endian bytes of `v`).  The register write is threaded as a
`Runs (wX_bits rd v) · · ()` premise. -/
theorem execute_LOAD_ld_run (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 8))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 8) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 8 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 8 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 8) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 8 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 8 v)[i])
    (hwrite : Runs (wX_bits rd v) s s' ()) :
    Runs (execute_LOAD imm rs1 rd false 8) s s' (.Retire_Success ()) := by
  have hread : Runs (mem_read (Load Data) PBMT_PMA (physaddr.Physaddr srcBits) 8 false false false)
      s s (Sail.Ok v) := by
    have h := mem_read_load_run s srcBits mstatusBits (leBytes 8 v) mstatusRead privRead mprvZero
      hmem physAccess noMMIO
    rw [leWord_leBytes_id8] at h
    exact h
  unfold execute_LOAD
  refine Runs.bind (assert_true_run s _) ?_
  refine Runs.bind
    (vmem_read_dword_run s rs1 (sign_extend (m := 64) imm) srcBits mstatusBits v
      mstatusRead privRead mprvZero addrReg aligned hread) ?_
  refine Runs.bind (middle := s') (value := ()) ?hw ?tail
  case hw =>
    rw [extend_value_signed_64]
    exact hwrite
  case tail => exact run_pure s' _

/-! ## Aligned single-byte read loop -/

theorem vmem_read_addr_byte_run (s : State) (srcBits mstatusBits : BitVec 64)
    (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (hread : Runs (mem_read (Load Data) PBMT_PMA (physaddr.Physaddr srcBits) 1 false false false)
      s s (Sail.Ok v)) :
    Runs (vmem_read_addr (virtaddr.Virtaddr srcBits) 1 (Load Data) false false false) s s
      (.Ok v) := by
  unfold vmem_read_addr
  have hguard : LeanRV64DExecutable.Functions.not (is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1)
      = false := by rw [aligned]; rfl
  simp only [Bool.false_eq_true, ↓reduceIte, hguard]
  apply RunsME.run
  refine RunsME.bind (RunsME.pure () s) ?_
  refine RunsME.bind
    (RunsME.lift _ s s (1, 1)
      (split_misaligned_aligned_run s (virtaddr.Virtaddr srcBits) 1 aligned)) ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, Bool.false_eq_true, ↓reduceIte,
    Int.reduceToNat, Int.reduceMul, Int.reduceSub, Nat.reduceMul, BitVec.setWidth_eq]
  refine RunsME.bind (middle := s)
    (value := (Sail.BitVec.updateSubrange (zeros : BitVec 8) 7 0 (BitVec.setWidth 8 v),
      true, 0)) ?loopwrap ?tail
  case tail =>
    show RunsME
      (Pure.pure (Sail.Ok
        (Sail.BitVec.updateSubrange (zeros : BitVec 8) 7 0 (BitVec.setWidth 8 v)))) s s
      (Sail.Ok v)
    rw [updateSubrange_zeros_setWidth8]
    exact RunsME.pure _ s
  case loopwrap =>
    refine RunsME.bind (middle := s)
      (value := (Sail.BitVec.updateSubrange (zeros : BitVec 8) 7 0 (BitVec.setWidth 8 v),
        true, 0)) ?fuel ?wrap
    case wrap => exact RunsME.pure _ s
    case fuel =>
      refine RunsME.untilFuelM_one _ _ _ s s s
        (Sail.BitVec.updateSubrange (zeros : BitVec 8) 7 0 (BitVec.setWidth 8 v), true, 0)
        ?hBody ?hCond
      case hCond => exact RunsME.pure true s
      case hBody =>
        dsimp only [bits_of_virtaddr_mk]
        simp only [Int.ofNat_zero, Int.zero_mul, addInt_zero', Int.reduceMul, Int.reduceSub,
          Int.reduceToNat, Int.reduceAdd, Nat.reduceMul, beq_self_eq_true, ↓reduceIte]
        refine RunsME.bind (RunsME.lift _ s s () (assert_true_run s _)) ?_
        refine RunsME.bind (middle := s)
          (value := Sail.BitVec.updateSubrange (zeros : BitVec 8) 7 0 (BitVec.setWidth 8 v))
          ?blk ?out
        case out => exact RunsME.pure _ s
        case blk =>
          refine RunsME.bind
            (RunsME.lift _ s s (Sail.Ok (physaddr.Physaddr srcBits, PBMT_PMA, init_ext_ptw))
              (translateAddr_machine_load_run s srcBits mstatusBits mstatusRead privRead
                mprvZero)) ?_
          refine RunsME.bind (RunsME.lift _ s s (Sail.Ok v) hread) ?_
          refine RunsME.bind (RunsME.pure () s) ?_
          exact RunsME.pure _ s

/-- `vmem_read` for an aligned byte: once the effective address resolves to `srcBits`, the read
runs to `Ok v` with the state unchanged. -/
theorem vmem_read_byte_run (s : State) (rs : regidx) (offset srcBits mstatusBits : BitVec 64)
    (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs offset (Load Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (hread : Runs (mem_read (Load Data) PBMT_PMA (physaddr.Physaddr srcBits) 1 false false false)
      s s (Sail.Ok v)) :
    Runs (vmem_read rs offset 1 (Load Data) false false false) s s (.Ok v) := by
  exact vmem_read_of_addr_run 1 s rs offset srcBits v addrReg
    (vmem_read_addr_byte_run s srcBits mstatusBits v mstatusRead privRead mprvZero aligned hread)

/-! ## Aligned unsigned-byte load instruction (`lbu`) -/

/-- `lbu rd, imm(rs1)` (width 1, unsigned): reads the single byte held at the resolved effective
address and writes its zero-extension to 64 bits into `rd`, retiring successfully.  Premises mirror
`execute_LOAD_ld_run` at width 1; the register write is threaded as
`Runs (wX_bits rd (zero_extend 64 v)) · · ()`. -/
theorem execute_LOAD_lbu_run (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 1 v)[i])
    (hwrite : Runs (wX_bits rd (zero_extend (m := 64) v)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd true 1) s s' (.Retire_Success ()) := by
  have hread : Runs (mem_read (Load Data) PBMT_PMA (physaddr.Physaddr srcBits) 1 false false false)
      s s (Sail.Ok v) := by
    have h := mem_read_load_run s srcBits mstatusBits (leBytes 1 v) mstatusRead privRead mprvZero
      hmem physAccess noMMIO
    rw [leWord_leBytes_id1] at h
    exact h
  unfold execute_LOAD
  refine Runs.bind (assert_true_run s _) ?_
  refine Runs.bind
    (vmem_read_byte_run s rs1 (sign_extend (m := 64) imm) srcBits mstatusBits v
      mstatusRead privRead mprvZero addrReg aligned hread) ?_
  refine Runs.bind (middle := s') (value := ()) ?hw ?tail
  case hw =>
    show Runs (wX_bits rd (extend_value true v)) s s' ()
    unfold extend_value
    simp only [↓reduceIte]
    exact hwrite
  case tail => exact run_pure s' _

end BinaryFv.RiscV
