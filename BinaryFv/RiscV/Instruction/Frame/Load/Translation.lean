import BinaryFv.RiscV.Instruction.Frame.Load.Platform

/-!
# LOAD framing through address translation and page-table walks
-/

namespace BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType

theorem load_preserves_read_pte (address : physaddr) (width : Nat) :
    PreservesStackPointer (read_pte address width) := by
  unfold read_pte
  exact load_preserves_mem_read_priv_load_pte address width .PBMT_PMA .Supervisor

theorem load_preserves_write_TLB (index : Nat) (entry : TLB_Entry) :
    PreservesStackPointer (write_TLB index entry) := by
  unfold write_TLB
  apply load_preserves_bind (readReg tlb)
  · exact load_preserves_readReg tlb
  · intro entries
    exact load_preserves_writeReg tlb _ (by decide)

theorem load_preserves_lookup_TLB (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16)) (vpn : BitVec (svWidth - 12)) :
    PreservesStackPointer (lookup_TLB svWidth asid vpn) := by
  unfold lookup_TLB
  apply load_preserves_bind (readReg tlb)
  · exact load_preserves_readReg tlb
  · intro entries
    cases entry : GetElem?.getElem! entries (tlb_hash svWidth vpn) with
    | none => exact load_preserves_pure _
    | some entry =>
      apply load_preserves_ite <;> exact load_preserves_pure _

theorem load_preserves_add_to_TLB (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16)) (vpn : BitVec (svWidth - 12))
    (ppn : BitVec (if (svWidth == 32 : Bool) then 22 else 44))
    (pte : BitVec (if (svWidth == 32 : Bool) then 32 else 64)) (pteAddress : physaddr)
    (level : Nat) (global : Bool) :
    PreservesStackPointer (add_to_TLB svWidth asid vpn ppn pte pteAddress level global) := by
  unfold add_to_TLB
  apply load_preserves_bind (readReg tlb)
  · exact load_preserves_readReg tlb
  · intro entries
    apply load_preserves_bind (writeReg tlb _)
    · exact load_preserves_writeReg tlb _ (by decide)
    · intro _
      apply load_preserves_bind (readReg tlb)
      · exact load_preserves_readReg tlb
      · intro updatedEntries
        exact load_preserves_pure _

theorem load_preserves_page_based_mem_type_forwards (bits : BitVec 2) :
    PreservesStackPointer (page_based_mem_type_forwards bits) := by
  have cases : bits.toNat = 0 ∨ bits.toNat = 1 ∨ bits.toNat = 2 ∨ bits.toNat = 3 := by
    omega
  rcases cases with h | h | h | h
  all_goals
    have value : bits = BitVec.ofNat 2 bits.toNat := by
      rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
      omega
    rw [value]
    simp [page_based_mem_type_forwards, h, EStateM.instMonad]
    all_goals first | exact load_preserves_pure _ | exact load_preserves_throw _

theorem load_preserves_tlb_get_pbmt (entry : TLB_Entry) :
    PreservesStackPointer (tlb_get_pbmt entry) := by
  unfold tlb_get_pbmt
  exact load_preserves_page_based_mem_type_forwards _

theorem load_preserves_translate_TLB_hit_load_data (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16)) (vpn : BitVec (svWidth - 12))
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit) (index : Nat) (entry : TLB_Entry) :
    PreservesStackPointer
      (translate_TLB_hit svWidth asid vpn (.Load mem_payload.Data) privilege mxr doSum external
        index entry) := by
  exact translate_tlb_hit_preserves_stack_pointer_of svWidth asid vpn (.Load mem_payload.Data)
    privilege mxr doSum external index entry
    (fun flags extensions =>
      load_preserves_check_PTE_permission_load_data privilege mxr doSum flags extensions external)
    (fun address width pte => load_preserves_update_and_write_pte_load_data address width pte)
    (fun index entry => load_preserves_write_TLB index entry) (load_preserves_tlb_get_pbmt entry)

theorem load_preserves_pt_walk_load_data (svWidth : Nat) (vpn : BitVec (svWidth - 12))
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit)
    (ptBase : BitVec (if (svWidth == 32 : Bool) then 22 else 44)) (level : Nat) (global : Bool) :
    PreservesStackPointer
      (pt_walk svWidth vpn (.Load mem_payload.Data) privilege mxr doSum ptBase level global
        external) := by
  apply pt_walk_preserves_stack_pointer_of svWidth vpn (.Load mem_payload.Data) privilege mxr doSum
    external
  · exact load_preserves_read_pte
  · exact load_preserves_pte_is_invalid
  · exact fun flags extensions =>
      load_preserves_check_PTE_permission_load_data privilege mxr doSum flags extensions external
  · exact load_preserves_currentlyEnabled_Svnapot

theorem load_preserves_translate_TLB_miss_load_data (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16))
    (basePpn : BitVec (if (svWidth == 32 : Bool) then 22 else 44))
    (vpn : BitVec (svWidth - 12)) (privilege : Privilege) (mxr doSum : Bool) (external : Unit) :
    PreservesStackPointer
      (translate_TLB_miss svWidth asid basePpn vpn (.Load mem_payload.Data) privilege mxr doSum
        external) := by
  apply translate_tlb_miss_preserves_stack_pointer_of svWidth asid basePpn vpn
      (.Load mem_payload.Data) privilege mxr doSum external
  · exact load_preserves_pt_walk_load_data svWidth vpn privilege mxr doSum external
  · intro address width pte
    exact load_preserves_update_and_write_pte_load_data address width pte
  · intro ppn pte pteAddress level global
    exact load_preserves_add_to_TLB svWidth asid vpn ppn pte pteAddress level global

theorem load_preserves_translate_load_data (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16))
    (basePpn : BitVec (if (svWidth == 32 : Bool) then 22 else 44))
    (vpn : BitVec (svWidth - 12)) (privilege : Privilege) (mxr doSum : Bool) (external : Unit) :
    PreservesStackPointer
      (translate svWidth asid basePpn vpn (.Load mem_payload.Data) privilege mxr doSum
        external) := by
  apply translate_preserves_stack_pointer_of svWidth asid basePpn vpn (.Load mem_payload.Data)
      privilege mxr doSum external
  · exact load_preserves_lookup_TLB svWidth asid vpn
  · exact load_preserves_translate_TLB_hit_load_data svWidth asid vpn privilege mxr doSum external
  · exact load_preserves_translate_TLB_miss_load_data svWidth asid basePpn vpn privilege mxr doSum
      external

theorem load_preserves_translateAddr_load_data (vaddr : virtaddr) :
    PreservesStackPointer (translateAddr vaddr (.Load mem_payload.Data)) := by
  apply translate_addr_preserves_stack_pointer_of vaddr (.Load mem_payload.Data)
  · exact load_preserves_effectivePrivilege (.Load mem_payload.Data)
  · exact load_preserves_translationMode
  · exact load_preserves_is_shadow_stack_access (.Load mem_payload.Data)
  · exact load_preserves_satp_mode_width_forwards
  · exact load_preserves_get_satp
  · exact load_preserves_translationException_load_data
  · intro svWidth asid basePpn vpn privilege mxr doSum
    exact load_preserves_translate_load_data svWidth asid basePpn vpn privilege mxr doSum
      init_ext_ptw

theorem load_preserves_vmem_read_misaligned_then (vaddr : virtaddr) (width : Nat) :
    LoadPreservesExcept (do
      match ← ExceptT.lift (plat_misaligned_exception (.Load mem_payload.Data) false) with
      | some .AccessFault =>
        let result ← ExceptT.lift
          (memory_exception vaddr (ExceptionType.E_Load_Access_Fault ()))
        Sail.SailME.throw (Sail.Result.Err result)
      | some .AlignmentException =>
        let result ← ExceptT.lift
          (memory_exception vaddr (ExceptionType.E_Load_Addr_Align ()))
        Sail.SailME.throw (Sail.Result.Err result)
      | none => pure () : SailME (Sail.Result (BitVec (8 * width)) ExecutionResult) PUnit) := by
  apply load_preserves_except_lift_bind
      (plat_misaligned_exception (.Load mem_payload.Data) false)
  · exact load_preserves_plat_misaligned_exception (.Load mem_payload.Data) false
  · intro result
    cases result with
    | none => exact load_preserves_except_pure _
    | some result =>
      cases result with
      | AccessFault =>
        apply load_preserves_except_lift_bind
            (memory_exception vaddr (ExceptionType.E_Load_Access_Fault ()))
        · exact load_preserves_memory_exception _ _
        · intro exception
          exact load_preserves_except_throw (Sail.Result.Err exception)
      | AlignmentException =>
        apply load_preserves_except_lift_bind
            (memory_exception vaddr (ExceptionType.E_Load_Addr_Align ()))
        · exact load_preserves_memory_exception _ _
        · intro exception
          exact load_preserves_except_throw (Sail.Result.Err exception)

theorem load_preserves_vmem_read_addr_load_data (vaddr : virtaddr) (width : Nat) :
    PreservesStackPointer
      (vmem_read_addr vaddr width (.Load mem_payload.Data) false false false) := by
  unfold vmem_read_addr
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply load_preserves_sailME_run
  apply load_preserves_except_ite_bind
  · exact load_preserves_vmem_read_misaligned_then vaddr width
  · exact load_preserves_except_pure _
  · intro _
    apply load_preserves_except_lift_bind (split_misaligned vaddr width)
    · exact load_preserves_split_misaligned vaddr width
    · rintro ⟨n, bytes⟩
      apply load_preserves_except_bind
      · apply load_preserves_except_bind
        · apply load_preserves_untilFuelM
          · intro loopVars
            exact load_preserves_except_pure loopVars.2.1
          · rintro ⟨data, finished, i⟩
            apply load_preserves_except_lift_bind (Sail.assert true "loop dummy assert")
            · exact load_preserves_assert _ _
            · intro _
              apply load_preserves_except_bind
              · apply load_preserves_except_bind
                · exact load_preserves_except_lift _
                    (load_preserves_translateAddr_load_data _)
                · intro translation
                  cases translation with
                  | Err failure =>
                    rcases failure with ⟨failure, extensionState⟩
                    simp only
                    apply load_preserves_except_bind
                    · apply load_preserves_except_lift_bind
                        (memory_exception
                          (virtaddr.Virtaddr
                            (Sail.BitVec.addInt (bits_of_virtaddr vaddr) (i *i bytes))) failure)
                      · exact load_preserves_memory_exception _ _
                      · intro result
                        exact load_preserves_except_pure (Sail.Result.Err result)
                    · intro error
                      exact load_preserves_except_throw error
                  | Ok translation =>
                    rcases translation with ⟨address, pbmt, extensionState⟩
                    simp only
                    apply load_preserves_except_bind
                    · exact load_preserves_except_lift _
                        (load_preserves_mem_read_load_data address bytes.toNat pbmt)
                    · intro read
                      cases read with
                      | Err failure =>
                        simp only
                        apply load_preserves_except_bind
                        · apply load_preserves_except_lift_bind
                            (memory_exception
                              (virtaddr.Virtaddr
                                (Sail.BitVec.addInt
                                  (bits_of_virtaddr vaddr) (i *i bytes))) failure)
                          · exact load_preserves_memory_exception _ _
                          · intro result
                            exact load_preserves_except_pure (Sail.Result.Err result)
                        · intro error
                          exact load_preserves_except_throw error
                      | Ok value =>
                        simp only
                        apply load_preserves_except_bind
                        · exact load_preserves_except_pure ()
                        · intro _
                          exact load_preserves_except_pure _
              · intro updated
                exact load_preserves_except_pure _
        · intro loopVars
          exact (load_preserves_except_pure loopVars : LoadPreservesExcept
            (pure loopVars : SailME (Sail.Result (BitVec (8 * width)) ExecutionResult)
              (BitVec ((8 *i n) *i bytes) × Bool × Nat)))
      · rintro ⟨data, finished, i⟩
        exact load_preserves_except_pure
          (Sail.Result.Ok (BitVec.setWidth (8 * width) data) :
            Sail.Result (BitVec (8 * width)) ExecutionResult)

theorem load_preserves_vmem_read_load_data (source : regidx) (offset : BitVec 64)
    (width : Nat) :
    PreservesStackPointer
      (vmem_read source offset width (.Load mem_payload.Data) false false false) := by
  unfold vmem_read
  apply load_preserves_sailME_run
  apply load_preserves_except_bind
  · apply load_preserves_except_bind
    · exact load_preserves_except_lift _
        (load_preserves_get_transformed_data_addr source offset (.Load mem_payload.Data) width)
    · intro transformed
      cases transformed with
      | Ext_DataAddr_Error error =>
        exact load_preserves_except_throw
          (Sail.Result.Err (ExecutionResult.Ext_DataAddr_Check_Failure error))
      | Ext_DataAddr_OK address => exact load_preserves_except_pure address
  · intro address
    exact load_preserves_except_lift _
      (load_preserves_vmem_read_addr_load_data address width)

theorem load_preserves_wX_bits (destination : regidx) (data : BitVec 64)
    (notStack : destination ≠ stackPointer) :
    PreservesStackPointer (wX_bits destination data) := by
  intro state
  cases hAction : (wX_bits destination data).run state <;>
    simpa [hAction] using wX_bits_preserves_stack_pointer state destination data notStack


end BinaryFv.RiscV
