import BinaryFv.RiscV.Instruction.Frame.Store.Platform

/-!
# `x2` framing through address translation and page-table walks
-/

namespace BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

theorem preservesX2_pmaCheck_store_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (reservation : Bool) :
    PreservesX2 (pmaCheck address width (MemoryAccessType.Store mem_payload.PageTableEntry) pbmt
      reservation) := by
  unfold pmaCheck
  apply PreservesX2.bind
  · exact preservesX2_readReg pma_regions
  · intro regions
    cases hPma : matching_pma_region regions address width with
    | none =>
      simp only
      apply PreservesX2.bind
          (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.PageTableEntry))
      · exact preservesX2_accessFault_store_pte
      · intro _
        exact PreservesX2.pure _
    | some region =>
      rcases region with ⟨base, size, attributes, includeInDeviceTree⟩
      apply PreservesX2.bind
      · apply PreservesX2.ite
        · exact PreservesX2.pure _
        · unfold pma_misaligned_exception
          exact PreservesX2.pure _
      · intro exception
        cases exception with
        | none =>
          apply PreservesX2.bind
          · apply PreservesX2.bind (Sail.assert _ _)
            · exact preservesX2_assert _ _
            · intro _
              exact PreservesX2.pure _
          · intro canAccess
            apply PreservesX2.ite
            · exact PreservesX2.pure _
            · apply PreservesX2.bind
                (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.PageTableEntry))
              · exact preservesX2_accessFault_store_pte
              · intro _
                exact PreservesX2.pure _
        | some exception =>
          cases exception with
          | AccessFault =>
            apply PreservesX2.bind
                (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.PageTableEntry))
            · exact preservesX2_accessFault_store_pte
            · intro _
              exact PreservesX2.pure _
          | AlignmentException =>
            apply PreservesX2.bind
                (alignmentFaultFromAccessType (MemoryAccessType.Store mem_payload.PageTableEntry))
            · exact preservesX2_alignmentFault_store_pte
            · intro _
              exact PreservesX2.pure _

theorem preservesX2_phys_access_check (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (privilege : Privilege)
    (reservation : Bool) (pmpFrame : PreservesX2 (pmpCheck address width access privilege))
    (pmaFrame : PreservesX2 (pmaCheck address width access pbmt reservation)) :
    PreservesX2 (phys_access_check access pbmt privilege address width reservation) := by
  unfold phys_access_check
  apply PreservesX2.bind
  · exact pmpFrame
  · intro pmpError
    apply PreservesX2.bind
    · exact pmaFrame
    · intro pmaError
      cases pmpError <;> cases pmaError
      · exact PreservesX2.pure _
      · exact PreservesX2.pure _
      · exact PreservesX2.pure _
      · apply PreservesX2.bind
        · exact preservesX2_highestPriorityAlignmentOrAccessFault _ _
        · intro _
          exact PreservesX2.pure _

theorem preservesX2_phys_access_check_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) (reservation : Bool) :
    PreservesX2
      (phys_access_check (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address
        width reservation) :=
  preservesX2_phys_access_check address width (MemoryAccessType.Load mem_payload.PageTableEntry)
    pbmt privilege reservation (preservesX2_pmpCheck_load_pte address width privilege)
    (preservesX2_pmaCheck_load_pte address width pbmt reservation)

theorem preservesX2_phys_access_check_store_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) (reservation : Bool) :
    PreservesX2
      (phys_access_check (MemoryAccessType.Store mem_payload.PageTableEntry) pbmt privilege address
        width reservation) :=
  preservesX2_phys_access_check address width (MemoryAccessType.Store mem_payload.PageTableEntry)
    pbmt privilege reservation (preservesX2_pmpCheck_store_pte address width privilege)
    (preservesX2_pmaCheck_store_pte address width pbmt reservation)

theorem preservesX2_read_then_pure (register : Register)
    (next : RegisterType register → α) :
    PreservesX2 (do
      let value ← readReg register
      pure (next value)) := by
  apply PreservesX2.bind (readReg register)
  · exact preservesX2_readReg register
  · intro _
    exact PreservesX2.pure _

theorem preservesX2_within_htif_readable (address : physaddr) (width : Nat) :
    PreservesX2 (within_htif_readable address width) := by
  exact preservesX2_within_htif_writable address width

theorem preservesX2_within_mmio_readable (address : physaddr) (width : Nat) :
    PreservesX2 (within_mmio_readable address width) := by
  unfold within_mmio_readable
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · apply PreservesX2.bind
    · exact preservesX2_within_clint address width
    · intro _
      apply PreservesX2.bind
      · exact preservesX2_within_sig address width
      · intro _
        apply PreservesX2.bind
        · exact preservesX2_within_htif_readable address width
        · intro _
          exact PreservesX2.pure _

theorem preservesX2_sig_load (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access)) :
    PreservesX2 (sig_load access address width) := by
  unfold sig_load
  apply PreservesX2.ite
  · apply PreservesX2.bind (accessFaultFromAccessType access)
    · exact accessFaultFrame
    · intro _
      exact PreservesX2.pure _
  · apply PreservesX2.ite
    · exact PreservesX2.pure _
    · apply PreservesX2.ite
      · exact PreservesX2.pure _
      · apply PreservesX2.bind (accessFaultFromAccessType access)
        · exact accessFaultFrame
        · intro _
          exact PreservesX2.pure _

theorem preservesX2_clint_load (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access)) :
    PreservesX2 (clint_load access address width) := by
  unfold clint_load
  simp only [get_config_print_clint]
  apply PreservesX2.ite
  · exact preservesX2_read_then_pure mip _
  · apply PreservesX2.ite
    · exact preservesX2_read_then_pure mtimecmp _
    · apply PreservesX2.ite
      · exact preservesX2_read_then_pure mtimecmp _
      · apply PreservesX2.ite
        · exact preservesX2_read_then_pure mtimecmp _
        · apply PreservesX2.ite
          · exact preservesX2_read_then_pure mtime _
          · apply PreservesX2.ite
            · exact preservesX2_read_then_pure mtime _
            · apply PreservesX2.ite
              · exact preservesX2_read_then_pure mtime _
              · apply PreservesX2.bind (accessFaultFromAccessType access)
                · exact accessFaultFrame
                · intro _
                  exact PreservesX2.pure _

theorem preservesX2_htif_load (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat) :
    PreservesX2 (htif_load access address width) := by
  simpa only [PreservesX2, PreservesStackPointer] using
    htif_load_preserves_stack_pointer access address width

theorem preservesX2_mmio_read (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access)) :
    PreservesX2 (mmio_read access address width) := by
  unfold mmio_read
  apply PreservesX2.bind
  · exact preservesX2_within_clint address width
  · intro inClint
    apply PreservesX2.ite
    · exact preservesX2_clint_load access address width accessFaultFrame
    · apply PreservesX2.bind
      · exact preservesX2_within_sig address width
      · intro inSig
        apply PreservesX2.ite
        · exact preservesX2_sig_load access address width accessFaultFrame
        · apply PreservesX2.bind
          · exact preservesX2_within_htif_readable address width
          · intro inHtif
            apply PreservesX2.ite
            · exact preservesX2_htif_load access address width
            · apply PreservesX2.bind (accessFaultFromAccessType access)
              · exact accessFaultFrame
              · intro _
                exact PreservesX2.pure _

theorem preservesX2_mmio_read_load_pte (address : physaddr) (width : Nat) :
    PreservesX2 (mmio_read (MemoryAccessType.Load mem_payload.PageTableEntry) address width) :=
  preservesX2_mmio_read (MemoryAccessType.Load mem_payload.PageTableEntry) address width
    preservesX2_accessFault_load_pte

theorem preservesX2_checked_mem_read_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesX2
      (checked_mem_read (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address
        width false false false false) := by
  unfold checked_mem_read
  apply PreservesX2.bind
      (phys_access_check (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address
        width false)
  · exact preservesX2_phys_access_check_load_pte address width pbmt privilege false
  · intro exception
    cases exception with
    | some exception => exact PreservesX2.pure _
    | none =>
      apply PreservesX2.bind
      · exact preservesX2_within_mmio_readable address width
      · intro inMmio
        apply PreservesX2.ite
        · apply PreservesX2.bind
            (mmio_read (MemoryAccessType.Load mem_payload.PageTableEntry) address width)
          · exact preservesX2_mmio_read_load_pte address width
          · intro _
            exact PreservesX2.pure _
        · simp only [read_kind_of_flags]
          apply PreservesX2.bind (read_ram .Read_plain address width false)
          · exact preservesX2_read_ram_plain address width
          · intro _
            exact PreservesX2.pure _

theorem preservesX2_mem_read_priv_meta_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesX2
      (mem_read_priv_meta (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address
        width false false false false) := by
  unfold mem_read_priv_meta
  simp only
  apply PreservesX2.bind
      (checked_mem_read (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address
        width false false false false)
  · exact preservesX2_checked_mem_read_load_pte address width pbmt privilege
  · intro _
    exact PreservesX2.pure _

theorem preservesX2_mem_read_priv_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesX2
      (mem_read_priv (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address width
        false false false) := by
  unfold mem_read_priv
  apply PreservesX2.bind
      (mem_read_priv_meta (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address
        width false false false false)
  · exact preservesX2_mem_read_priv_meta_load_pte address width pbmt privilege
  · intro _
    exact PreservesX2.pure _

theorem preservesX2_read_pte (address : physaddr) (width : Nat) :
    PreservesX2 (read_pte address width) := by
  unfold read_pte
  exact preservesX2_mem_read_priv_load_pte address width .PBMT_PMA .Supervisor

theorem preservesX2_checked_mem_write_store_pte (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesX2
      (checked_mem_write address width data (MemoryAccessType.Store mem_payload.PageTableEntry)
        pbmt privilege default_meta false false false) := by
  unfold checked_mem_write
  apply PreservesX2.bind
      (phys_access_check (MemoryAccessType.Store mem_payload.PageTableEntry) pbmt privilege address
        width false)
  · exact preservesX2_phys_access_check_store_pte address width pbmt privilege false
  · intro exception
    cases exception with
    | some exception => exact PreservesX2.pure _
    | none =>
      apply PreservesX2.bind
      · exact preservesX2_within_mmio_writable address width
      · intro inMmio
        apply PreservesX2.ite
        · exact preservesX2_mmio_write address width data
        · simp only [write_kind_of_flags]
          apply PreservesX2.bind (write_ram .Write_plain address width data default_meta)
          · exact preservesX2_write_ram .Write_plain address width data default_meta
          · intro _
            exact PreservesX2.pure _

theorem preservesX2_mem_write_value_priv_meta_store_pte (address : physaddr)
    (width : Nat) (data : BitVec (8 * width)) (pbmt : page_based_mem_type)
    (privilege : Privilege) :
      PreservesX2
        (mem_write_value_priv_meta address width data
          (MemoryAccessType.Store mem_payload.PageTableEntry) pbmt privilege default_meta
          false false false) := by
  unfold mem_write_value_priv_meta
  simp only
  apply PreservesX2.bind
      (checked_mem_write address width data (MemoryAccessType.Store mem_payload.PageTableEntry)
        pbmt privilege default_meta false false false)
  · exact preservesX2_checked_mem_write_store_pte address width data pbmt privilege
  · intro _
    exact PreservesX2.pure _

theorem preservesX2_mem_write_value_priv_store_pte (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) (privilege : Privilege) (pbmt : page_based_mem_type) :
    PreservesX2
      (mem_write_value_priv address width data privilege
        (MemoryAccessType.Store mem_payload.PageTableEntry) pbmt false false false) := by
  unfold mem_write_value_priv
  exact preservesX2_mem_write_value_priv_meta_store_pte address width data pbmt privilege

theorem preservesX2_write_pte (address : physaddr) (width : Nat)
    (data : BitVec (width * 8)) :
    PreservesX2 (write_pte address width data) := by
  unfold write_pte
  exact preservesX2_mem_write_value_priv_store_pte address width _ .Supervisor .PBMT_PMA

theorem preservesX2_update_and_write_pte_store_data (address : physaddr) (width : Nat)
    (pte : BitVec (width * 8)) :
    PreservesX2
      (update_and_write_pte address width pte (MemoryAccessType.Store mem_payload.Data)) := by
  unfold update_and_write_pte
  cases hUpdate : update_PTE_Bits pte (MemoryAccessType.Store mem_payload.Data) with
  | none => exact PreservesX2.pure _
  | some updated =>
    apply PreservesX2.bind (currentlyEnabled extension.Ext_Svadu)
    · exact preservesX2_currentlyEnabled_Svadu
    · intro _
      apply PreservesX2.bind (readReg menvcfg)
      · exact preservesX2_readReg menvcfg
      · intro _
        apply PreservesX2.bind (currentlyEnabled extension.Ext_Svadu)
        · exact preservesX2_currentlyEnabled_Svadu
        · intro _
          apply PreservesX2.bind (currentlyEnabled extension.Ext_Svade)
          · exact preservesX2_currentlyEnabled_Svade
          · intro _
            apply PreservesX2.ite
            · apply PreservesX2.bind (write_pte address width updated)
              · exact preservesX2_write_pte address width updated
              · intro result
                cases result <;> exact PreservesX2.pure _
            · exact PreservesX2.pure _

theorem preservesX2_write_TLB (index : Nat) (entry : TLB_Entry) :
    PreservesX2 (write_TLB index entry) := by
  unfold write_TLB
  apply PreservesX2.bind
  · exact preservesX2_readReg tlb
  · intro entries
    exact PreservesX2.writeReg tlb _ (by decide)

theorem preservesX2_lookup_TLB (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16)) (vpn : BitVec (svWidth - 12)) :
    PreservesX2 (lookup_TLB svWidth asid vpn) := by
  unfold lookup_TLB
  apply PreservesX2.bind
  · exact preservesX2_readReg tlb
  · intro entries
    cases entry : GetElem?.getElem! entries (tlb_hash svWidth vpn) with
    | none => exact PreservesX2.pure _
    | some entry =>
      apply PreservesX2.ite <;> exact PreservesX2.pure _

theorem preservesX2_add_to_TLB (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16)) (vpn : BitVec (svWidth - 12))
    (ppn : BitVec (if (svWidth == 32 : Bool) then 22 else 44))
    (pte : BitVec (if (svWidth == 32 : Bool) then 32 else 64)) (pteAddress : physaddr)
    (level : Nat) (global : Bool) :
    PreservesX2 (add_to_TLB svWidth asid vpn ppn pte pteAddress level global) := by
  unfold add_to_TLB
  apply PreservesX2.bind
  · exact preservesX2_readReg tlb
  · intro entries
    apply PreservesX2.bind
    · exact PreservesX2.writeReg tlb _ (by decide)
    · intro _
      apply PreservesX2.bind
      · exact preservesX2_readReg tlb
      · intro updatedEntries
        exact PreservesX2.pure _

theorem preservesX2_page_based_mem_type_forwards (bits : BitVec 2) :
    PreservesX2 (page_based_mem_type_forwards bits) := by
  have cases : bits.toNat = 0 ∨ bits.toNat = 1 ∨ bits.toNat = 2 ∨ bits.toNat = 3 := by
    omega
  rcases cases with h | h | h | h
  all_goals
    have value : bits = BitVec.ofNat 2 bits.toNat := by
      rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
      omega
    rw [value]
    simp [page_based_mem_type_forwards, h, EStateM.instMonad]
    all_goals first | exact PreservesX2.pure _ | exact PreservesX2.throw _

theorem preservesX2_tlb_get_pbmt (entry : TLB_Entry) :
    PreservesX2 (tlb_get_pbmt entry) := by
  unfold tlb_get_pbmt
  exact preservesX2_page_based_mem_type_forwards _

theorem preservesX2_translate_TLB_hit_store_data (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16)) (vpn : BitVec (svWidth - 12))
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit) (index : Nat) (entry : TLB_Entry) :
    PreservesX2
      (translate_TLB_hit svWidth asid vpn (MemoryAccessType.Store mem_payload.Data) privilege mxr
        doSum external index entry) := by
  apply preservesX2_of_preservesStackPointer
  exact translate_tlb_hit_preserves_stack_pointer_of svWidth asid vpn
    (MemoryAccessType.Store mem_payload.Data) privilege mxr doSum external index entry
    (fun flags extensions =>
      preservesStackPointer_of_preservesX2
        (preservesX2_check_PTE_permission_store_data privilege mxr doSum flags extensions external))
    (fun address width pte =>
      preservesStackPointer_of_preservesX2
        (preservesX2_update_and_write_pte_store_data address width pte))
    (fun index entry =>
      preservesStackPointer_of_preservesX2 (preservesX2_write_TLB index entry))
    (preservesStackPointer_of_preservesX2 (preservesX2_tlb_get_pbmt entry))

theorem preservesX2_pt_walk_store_data (svWidth : Nat) (vpn : BitVec (svWidth - 12))
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit)
    (ptBase : BitVec (if (svWidth == 32 : Bool) then 22 else 44)) (level : Nat) (global : Bool) :
      PreservesX2
        (pt_walk svWidth vpn (MemoryAccessType.Store mem_payload.Data) privilege mxr doSum
          ptBase level global external) := by
  apply preservesX2_of_preservesStackPointer
  apply pt_walk_preserves_stack_pointer_of svWidth vpn (MemoryAccessType.Store mem_payload.Data)
      privilege mxr doSum external
  · intro address width
    exact preservesStackPointer_of_preservesX2 (preservesX2_read_pte address width)
  · intro flags extensions
    exact preservesStackPointer_of_preservesX2 (preservesX2_pte_is_invalid flags extensions)
  · intro flags extensions
    exact preservesStackPointer_of_preservesX2
      (preservesX2_check_PTE_permission_store_data privilege mxr doSum flags extensions external)
  · exact preservesStackPointer_of_preservesX2 preservesX2_currentlyEnabled_Svnapot

theorem preservesX2_translate_TLB_miss_store_data (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16))
    (basePpn : BitVec (if (svWidth == 32 : Bool) then 22 else 44)) (vpn : BitVec (svWidth - 12))
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit) :
    PreservesX2
      (translate_TLB_miss svWidth asid basePpn vpn (MemoryAccessType.Store mem_payload.Data)
        privilege mxr doSum external) := by
  apply preservesX2_of_preservesStackPointer
  apply translate_tlb_miss_preserves_stack_pointer_of svWidth asid basePpn vpn
      (MemoryAccessType.Store mem_payload.Data) privilege mxr doSum external
  · intro ptBase level global
    exact preservesStackPointer_of_preservesX2
      (preservesX2_pt_walk_store_data svWidth vpn privilege mxr doSum external ptBase level global)
  · intro address width pte
    exact preservesStackPointer_of_preservesX2
      (preservesX2_update_and_write_pte_store_data address width pte)
  · intro ppn pte pteAddress level global
    exact preservesStackPointer_of_preservesX2
      (preservesX2_add_to_TLB svWidth asid vpn ppn pte pteAddress level global)

theorem preservesX2_translate_store_data (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16))
    (basePpn : BitVec (if (svWidth == 32 : Bool) then 22 else 44)) (vpn : BitVec (svWidth - 12))
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit) :
    PreservesX2
      (translate svWidth asid basePpn vpn (MemoryAccessType.Store mem_payload.Data) privilege mxr
        doSum external) := by
  apply preservesX2_of_preservesStackPointer
  apply translate_preserves_stack_pointer_of svWidth asid basePpn vpn
      (MemoryAccessType.Store mem_payload.Data) privilege mxr doSum external
  · exact preservesStackPointer_of_preservesX2 (preservesX2_lookup_TLB svWidth asid vpn)
  · intro index entry
    exact preservesStackPointer_of_preservesX2
      (preservesX2_translate_TLB_hit_store_data svWidth asid vpn privilege mxr doSum external
        index entry)
  · exact preservesStackPointer_of_preservesX2
      (preservesX2_translate_TLB_miss_store_data svWidth asid basePpn vpn privilege mxr doSum
        external)

theorem preservesX2_translateAddr_store_data (vaddr : virtaddr) :
    PreservesX2 (translateAddr vaddr (MemoryAccessType.Store mem_payload.Data)) := by
  apply preservesX2_of_preservesStackPointer
  apply translate_addr_preserves_stack_pointer_of vaddr (MemoryAccessType.Store mem_payload.Data)
  · intro mstatusBits privilege
    exact preservesStackPointer_of_preservesX2
      (preservesX2_effectivePrivilege
        (MemoryAccessType.Store mem_payload.Data) mstatusBits privilege)
  · intro privilege
    exact preservesStackPointer_of_preservesX2 (preservesX2_translationMode privilege)
  · exact preservesStackPointer_of_preservesX2
      (preservesX2_is_shadow_stack_access (MemoryAccessType.Store mem_payload.Data))
  · intro mode
    exact preservesStackPointer_of_preservesX2 (preservesX2_satp_mode_width_forwards mode)
  · intro svWidth
    exact preservesStackPointer_of_preservesX2 (preservesX2_get_satp svWidth)
  · intro failure
    exact preservesStackPointer_of_preservesX2
      (preservesX2_translationException_store_data failure)
  · intro svWidth asid basePpn vpn privilege mxr doSum
    exact preservesStackPointer_of_preservesX2
      (preservesX2_translate_store_data svWidth asid basePpn vpn privilege mxr doSum init_ext_ptw)

theorem preservesX2E_throw_memory_exception (address : virtaddr)
    (exception : ExceptionType) :
    PreservesX2E (do
      let result ← liftM (memory_exception address exception)
      let error ← pure (Sail.Err result)
      Sail.SailME.throw error : SailME (Sail.Result Bool ExecutionResult) α) := by
  apply PreservesX2E.bind
  · exact PreservesX2E.lift (memory_exception address exception)
      (preservesX2_memory_exception address exception)
  · intro result
    apply PreservesX2E.bind
    · exact PreservesX2E.pure (Sail.Err result)
    · intro error
      exact PreservesX2E.throw error

def vmemWriteStoreStep (bytes last step : Int) (baseVaddr : BitVec 64)
    (data : BitVec (8 * width)) (state : Bool × Nat × Bool) :
    SailME (Sail.Result Bool ExecutionResult) (Bool × Nat × Bool) :=
  (fun (finished, index, writeSuccess) => do
    liftM (Sail.assert true "loop dummy assert")
    let offset := index
    let vaddr := Sail.BitVec.addInt baseVaddr (offset *i bytes)
    let writeSuccess ← ((do
        match
          (← translateAddr (virtaddr.Virtaddr vaddr)
            (MemoryAccessType.Store mem_payload.Data)) with
      | .Err (exception, _) =>
        Sail.SailME.throw (← do
          pure (Sail.Err (← memory_exception (virtaddr.Virtaddr vaddr) exception)))
      | .Ok (paddr, pbmt, _) =>
        (do
          liftM (Sail.assert (false == false) "sys/vmem_utils.sail:197.50-197.51")
          (do
            match (← mem_write_ea paddr bytes false false false) with
            | .Err exception =>
              Sail.SailME.throw (← do
                pure (Sail.Err (← memory_exception (virtaddr.Virtaddr vaddr) exception)))
            | .Ok () =>
              (do
                let writeValue := Sail.BitVec.extractLsb data
                  (((8 *i (offset +i 1)) *i bytes) -i 1) ((8 *i offset) *i bytes)
                match (← mem_write_value paddr bytes writeValue
                    (MemoryAccessType.Store mem_payload.Data) pbmt false false false) with
                | .Err exception =>
                  Sail.SailME.throw (← do
                    pure (Sail.Err (← memory_exception (virtaddr.Virtaddr vaddr) exception)))
                | .Ok success => pure (writeSuccess && success))))) : SailME
        (Sail.Result Bool ExecutionResult) Bool)
    let (finished, index) : Bool × Nat :=
      if ((offset == last) : Bool)
      then
        (let finished : Bool := true
        (finished, index))
      else
        (let index : Nat := offset +i step
        (finished, index))
    pure (finished, index, writeSuccess)) state

theorem preservesX2E_vmemWriteStoreStep (bytes last step : Int) (baseVaddr : BitVec 64)
    (data : BitVec (8 * width)) (state : Bool × Nat × Bool)
    (translateFrame : ∀ address,
      PreservesX2 (translateAddr address (MemoryAccessType.Store mem_payload.Data))) :
    PreservesX2E (vmemWriteStoreStep bytes last step baseVaddr data state) := by
  unfold vmemWriteStoreStep
  apply PreservesX2E.bind
  · exact PreservesX2E.lift (PreSail.assert true "loop dummy assert")
      (preservesX2_assert true "loop dummy assert")
  · intro _
    apply PreservesX2E.bind
    · apply PreservesX2E.bind
      · exact PreservesX2E.lift
          (translateAddr (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes)))
            (MemoryAccessType.Store mem_payload.Data))
          (translateFrame _)
      · intro translation
        cases translation with
        | Err failure =>
          apply PreservesX2E.bind
          · apply PreservesX2E.bind
            · exact PreservesX2E.lift
                (memory_exception
                  (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes))) failure.1)
                (preservesX2_memory_exception
                  (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes))) failure.1)
            · intro result
              exact PreservesX2E.pure (Sail.Err result)
          · intro error
            exact PreservesX2E.throw error
        | Ok translation =>
          rcases translation with ⟨paddr, pbmt, extensionState⟩
          apply PreservesX2E.bind
          · exact PreservesX2E.lift
              (PreSail.assert (false == false) "sys/vmem_utils.sail:197.50-197.51")
              (preservesX2_assert (false == false) "sys/vmem_utils.sail:197.50-197.51")
          · intro _
            apply PreservesX2E.bind
            · exact PreservesX2E.lift (mem_write_ea paddr bytes false false false)
                (preservesX2_mem_write_ea paddr bytes)
            · intro writeEa
              cases writeEa with
              | Err exception =>
                apply PreservesX2E.bind
                · apply PreservesX2E.bind
                  · exact PreservesX2E.lift
                      (memory_exception
                        (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes)))
                        exception)
                      (preservesX2_memory_exception
                        (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes)))
                        exception)
                  · intro result
                    exact PreservesX2E.pure (Sail.Err result)
                · intro error
                  exact PreservesX2E.throw error
              | Ok _ =>
                apply PreservesX2E.bind
                · exact PreservesX2E.lift
                    (mem_write_value paddr bytes
                      (Sail.BitVec.extractLsb data
                        (((8 *i (state.2.1 +i 1)) *i bytes) -i 1)
                        ((8 *i state.2.1) *i bytes))
                      (MemoryAccessType.Store mem_payload.Data) pbmt false false false)
                    (preservesX2_mem_write_value_store paddr bytes _ pbmt)
                · intro writeResult
                  cases writeResult with
                  | Err exception =>
                    apply PreservesX2E.bind
                    · apply PreservesX2E.bind
                      · exact PreservesX2E.lift
                          (memory_exception
                            (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes)))
                            exception)
                          (preservesX2_memory_exception
                            (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes)))
                            exception)
                      · intro result
                        exact PreservesX2E.pure (Sail.Err result)
                    · intro error
                      exact PreservesX2E.throw error
                  | Ok success =>
                    exact PreservesX2E.pure _
    · intro writeSuccess
      exact PreservesX2E.pure _

theorem preservesX2_vmem_write_addr_store_of_translate (address : virtaddr) (width : Nat)
    (data : BitVec (8 * width))
    (translateFrame : ∀ vaddr,
      PreservesX2 (translateAddr vaddr (MemoryAccessType.Store mem_payload.Data))) :
    PreservesX2 (vmem_write_addr address width data
      (MemoryAccessType.Store mem_payload.Data) false false false) := by
  unfold vmem_write_addr
  simp only [is_store_conditional, Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  apply preservesX2_sailMERun
  apply PreservesX2E.iteBind
  · exact preservesX2E_vmem_write_store_misaligned_then address
  · exact PreservesX2E.pure _
  · intro _
    apply PreservesX2E.bind
    · exact PreservesX2E.lift (split_misaligned address width)
        (preservesX2_split_misaligned address width)
    · rintro ⟨n, bytes⟩
      apply PreservesX2E.bind
      · apply PreservesX2E.bind
        · exact preservesX2E_untilFuelM n.toNat
            (fun state : Bool × Nat × Bool => pure state.1)
            (false, (misaligned_order n).1.toNat, true)
            (vmemWriteStoreStep bytes (misaligned_order n).2.1 (misaligned_order n).2.2
              (bits_of_virtaddr address) data)
            (fun _ => PreservesX2E.pure _)
            (fun state => preservesX2E_vmemWriteStoreStep bytes (misaligned_order n).2.1
              (misaligned_order n).2.2 (bits_of_virtaddr address) data state translateFrame)
        · intro loopVars
          exact PreservesX2E.pure loopVars
      · rintro ⟨finished, index, writeSuccess⟩
        exact PreservesX2E.pure (Sail.Ok writeSuccess)

theorem preservesX2_vmem_write_store_of_translate (base : regidx) (offset : BitVec 64)
    (width : Nat) (data : BitVec (8 * width))
    (translateFrame : ∀ vaddr,
      PreservesX2 (translateAddr vaddr (MemoryAccessType.Store mem_payload.Data))) :
    PreservesX2 (vmem_write base offset width data
      (MemoryAccessType.Store mem_payload.Data) false false false) := by
  unfold vmem_write
  apply preservesX2_sailMERun
  apply PreservesX2E.bind
  · apply PreservesX2E.bind
    · exact PreservesX2E.lift
        (get_transformed_data_addr base offset (MemoryAccessType.Store mem_payload.Data) width)
        (preservesX2_get_transformed_data_addr base offset
          (MemoryAccessType.Store mem_payload.Data) width)
    · intro transformed
      cases transformed with
      | Ext_DataAddr_Error error =>
        exact PreservesX2E.throw (Sail.Err (ExecutionResult.Ext_DataAddr_Check_Failure error))
      | Ext_DataAddr_OK address => exact PreservesX2E.pure address
  · intro address
    exact PreservesX2E.lift
      (vmem_write_addr address width data (MemoryAccessType.Store mem_payload.Data)
        false false false)
      (preservesX2_vmem_write_addr_store_of_translate address width data translateFrame)

theorem preservesX2_execute_STORE_of_translate (immediate : BitVec 12)
    (sourceData sourceAddress : regidx) (width : Nat)
    (translateFrame : ∀ vaddr,
      PreservesX2 (translateAddr vaddr (MemoryAccessType.Store mem_payload.Data))) :
    PreservesX2 (execute_STORE immediate sourceData sourceAddress width) := by
  unfold execute_STORE
  apply PreservesX2.bind
  · exact preservesX2_assert _ _
  · intro _
    apply PreservesX2.bind
    · exact preservesX2_rX_bits sourceData
    · intro bits
      apply PreservesX2.bind
      · exact PreservesX2.pure (Sail.BitVec.extractLsb bits ((width *i 8) -i 1) 0)
      · intro data
        apply PreservesX2.bind
        · exact preservesX2_vmem_write_store_of_translate sourceAddress
            (sign_extend (m := 64) immediate) width data translateFrame
        · intro writeResult
          cases writeResult <;> exact PreservesX2.pure _

theorem execute_STORE_dispatch_preservesX2_of_translate (state : State)
    (immediate : BitVec 12) (sourceData sourceAddress : regidx) (width : Nat)
    (translateFrame : ∀ vaddr,
      PreservesX2 (translateAddr vaddr (MemoryAccessType.Store mem_payload.Data))) :
    (match (execute (.STORE (immediate, sourceData, sourceAddress, width))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_STORE immediate sourceData sourceAddress width).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  cases hStore : execute_STORE immediate sourceData sourceAddress width state with
  | error error after =>
    simpa [EStateM.run, hStore] using
      (preservesX2_execute_STORE_of_translate immediate sourceData sourceAddress width
        translateFrame state)
  | ok value after =>
    simpa [EStateM.run, hStore] using
      (preservesX2_execute_STORE_of_translate immediate sourceData sourceAddress width
        translateFrame state)


end BinaryFv.RiscV
