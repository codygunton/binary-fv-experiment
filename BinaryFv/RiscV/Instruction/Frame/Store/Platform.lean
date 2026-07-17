import BinaryFv.RiscV.Instruction.Frame.Store.Pmp

/-!
# `x2` framing through the CLINT, HTIF, and signature store paths
-/

namespace BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

def sigStoreAfterSsi (interrupts : Minterrupts) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := do
  let supervisorEnabled ← currentlyEnabled extension.Ext_S
  if ((_get_Minterrupts_SSI interrupts == 1#1) && supervisorEnabled) then do
    let currentMip ← Sail.readReg mip
    Sail.writeReg mip (Sail.BitVec.updateSubrange currentMip 1 1 value)
  else pure ()
  let mipValue ← read_mip XipReadType.IncludePlatformInterrupts
  csr_name_write_callback "mip" mipValue
  pure (Sail.Ok true)

theorem preservesX2_sigStoreAfterSsi (interrupts : Minterrupts) (value : BitVec 1) :
    PreservesX2 (sigStoreAfterSsi interrupts value) := by
  unfold sigStoreAfterSsi
  apply PreservesX2.bind
  · exact preservesX2_currentlyEnabled_S
  · intro supervisorEnabled
    apply PreservesX2.ite
    · apply PreservesX2.bind
      · exact preservesX2_readReg mip
      · intro currentMip
        apply PreservesX2.bind
        · exact PreservesX2.writeReg mip _ (by decide)
        · intro _
          exact preservesX2_mip_callback_ok
    · apply PreservesX2.bind
      · exact PreservesX2.pure _
      · intro _
        exact preservesX2_mip_callback_ok

def sigStoreAfterMsi (interrupts : Minterrupts) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := do
  if _get_Minterrupts_MSI interrupts == 1#1 then do
    let currentMip ← Sail.readReg mip
    Sail.writeReg mip (Sail.BitVec.updateSubrange currentMip 3 3 value)
  else pure ()
  sigStoreAfterSsi interrupts value

theorem preservesX2_sigStoreAfterMsi (interrupts : Minterrupts) (value : BitVec 1) :
    PreservesX2 (sigStoreAfterMsi interrupts value) := by
  unfold sigStoreAfterMsi
  apply PreservesX2.ite
  · apply PreservesX2.bind
    · exact preservesX2_readReg mip
    · intro currentMip
      apply PreservesX2.bind
      · exact PreservesX2.writeReg mip _ (by decide)
      · intro _
        exact preservesX2_sigStoreAfterSsi interrupts value
  · apply PreservesX2.bind
    · exact PreservesX2.pure _
    · intro _
      exact preservesX2_sigStoreAfterSsi interrupts value

def sigStoreAfterSei (interrupts : Minterrupts) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := do
  if _get_Minterrupts_SEI interrupts == 1#1 then
    Sail.writeReg sig_seip value
  else pure ()
  sigStoreAfterMsi interrupts value

theorem preservesX2_sigStoreAfterSei (interrupts : Minterrupts) (value : BitVec 1) :
    PreservesX2 (sigStoreAfterSei interrupts value) := by
  unfold sigStoreAfterSei
  apply PreservesX2.ite
  · apply PreservesX2.bind
    · exact PreservesX2.writeReg sig_seip value (by decide)
    · intro _
      exact preservesX2_sigStoreAfterMsi interrupts value
  · apply PreservesX2.bind
    · exact PreservesX2.pure _
    · intro _
      exact preservesX2_sigStoreAfterMsi interrupts value

def sigStoreAfterMei (interrupts : Minterrupts) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := do
  if _get_Minterrupts_MEI interrupts == 1#1 then
    Sail.writeReg sig_meip value
  else pure ()
  sigStoreAfterSei interrupts value

theorem preservesX2_sigStoreAfterMei (interrupts : Minterrupts) (value : BitVec 1) :
    PreservesX2 (sigStoreAfterMei interrupts value) := by
  unfold sigStoreAfterMei
  apply PreservesX2.ite
  · apply PreservesX2.bind
    · exact PreservesX2.writeReg sig_meip value (by decide)
    · intro _
      exact preservesX2_sigStoreAfterSei interrupts value
  · apply PreservesX2.bind
    · exact PreservesX2.pure _
    · intro _
      exact preservesX2_sigStoreAfterSei interrupts value

def sigStorePlatformAction (data : BitVec (8 * width)) :
    SailM (Sail.Result Bool ExceptionType) := do
  let value := Sail.BitVec.access data 31
  let interrupts : Minterrupts := Mk_Minterrupts (zero_extend (m := 64) data)
  if Sail.BitVec.extractLsb
      (_update_Minterrupts_SSI
        (_update_Minterrupts_MSI
          (_update_Minterrupts_SEI (_update_Minterrupts_MEI interrupts 0#1) 0#1) 0#1) 0#1)
      30 0 != zeros then
    pure (Sail.Err (ExceptionType.E_SAMO_Access_Fault ()))
  else
    sigStoreAfterMei interrupts value

theorem preservesX2_sigStorePlatformAction (data : BitVec (8 * width)) :
    PreservesX2 (sigStorePlatformAction data) := by
  unfold sigStorePlatformAction
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · exact preservesX2_sigStoreAfterMei _ _

theorem preservesX2_sig_store (app_0 : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesX2 (sig_store app_0 width data) := by
  unfold sig_store
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · apply PreservesX2.ite
    · exact PreservesX2.pure _
    · apply PreservesX2.ite
      · exact preservesX2_sigStorePlatformAction data
      · exact PreservesX2.pure _

theorem preservesX2_htif_store (app_0 : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesX2 (htif_store app_0 width data) := by
  intro state
  cases hStore : htif_store app_0 width data state with
  | error error after =>
    simpa [EStateM.run, hStore] using
      (htif_store_preserves_stack_pointer app_0 width data state)
  | ok value after =>
    simpa [EStateM.run, hStore] using
      (htif_store_preserves_stack_pointer app_0 width data state)

theorem preservesX2_within_clint (address : physaddr) (width : Nat) :
    PreservesX2 (within_clint address width) := by
  unfold within_clint
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · exact PreservesX2.pure _

theorem preservesX2_within_sig (address : physaddr) (width : Nat) :
    PreservesX2 (within_sig address width) := by
  unfold within_sig
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · exact PreservesX2.pure _

theorem preservesX2_within_htif_writable (address : physaddr) (width : Nat) :
    PreservesX2 (within_htif_writable address width) := by
  unfold within_htif_writable
  apply PreservesX2.bind
  · exact preservesX2_readReg htif_tohost_base
  · intro base
    cases base <;> exact PreservesX2.pure _

theorem preservesX2_mmio_write (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesX2 (mmio_write address width data) := by
  unfold mmio_write
  apply PreservesX2.bind
  · exact preservesX2_within_clint address width
  · intro inClint
    apply PreservesX2.ite
    · exact preservesX2_clint_store address width data
    · apply PreservesX2.bind
      · exact preservesX2_within_sig address width
      · intro inSig
        apply PreservesX2.ite
        · exact preservesX2_sig_store address width data
        · apply PreservesX2.bind
          · exact preservesX2_within_htif_writable address width
          · intro inHtif
            apply PreservesX2.ite
            · exact preservesX2_htif_store address width data
            · exact PreservesX2.pure _

theorem preservesX2_within_mmio_writable (address : physaddr) (width : Nat) :
    PreservesX2 (within_mmio_writable address width) := by
  unfold within_mmio_writable
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · apply PreservesX2.bind
    · exact preservesX2_within_clint address width
    · intro inClint
      apply PreservesX2.bind
      · exact preservesX2_within_sig address width
      · intro inSig
        apply PreservesX2.bind
        · exact preservesX2_within_htif_writable address width
        · intro inHtif
          exact PreservesX2.pure _

theorem preservesX2_checked_mem_write_store (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) (pbmt : page_based_mem_type) (privilege : Privilege)
    (metadata : Unit) :
    PreservesX2 (checked_mem_write address width data (MemoryAccessType.Store mem_payload.Data)
      pbmt privilege metadata false false false) := by
  unfold checked_mem_write
  apply PreservesX2.bind
  · exact preservesX2_phys_access_check_store address width pbmt privilege
  · intro fault
    cases fault with
    | some fault => exact PreservesX2.pure _
    | none =>
      apply PreservesX2.bind
      · exact preservesX2_within_mmio_writable address width
      · intro mmioWritable
        apply PreservesX2.ite
        · exact preservesX2_mmio_write address width data
        · apply PreservesX2.bind
          · exact PreservesX2.pure _
          · intro kind
            apply PreservesX2.bind
            · exact preservesX2_write_ram kind address width data metadata
            · intro result
              exact PreservesX2.pure _

theorem preservesX2_mem_write_value_priv_meta_store (address : physaddr) (width : Nat)
    (value : BitVec (8 * width)) (pbmt : page_based_mem_type) (privilege : Privilege)
    (metadata : Unit) :
    PreservesX2 (mem_write_value_priv_meta address width value
      (MemoryAccessType.Store mem_payload.Data) pbmt privilege metadata false false false) := by
  unfold mem_write_value_priv_meta
  simp only [Bool.false_or, Bool.false_and]
  apply PreservesX2.bind
  · exact preservesX2_checked_mem_write_store address width value pbmt privilege metadata
  · intro result
    cases result <;> exact PreservesX2.pure _

theorem preservesX2_mem_write_value_meta_store (address : physaddr) (width : Nat)
    (value : BitVec (8 * width)) (pbmt : page_based_mem_type) (metadata : Unit) :
    PreservesX2 (mem_write_value_meta address width value
      (MemoryAccessType.Store mem_payload.Data) pbmt metadata false false false) := by
  unfold mem_write_value_meta
  apply PreservesX2.bind
  · exact preservesX2_readReg mstatus
  · intro mstatusBits
    apply PreservesX2.bind
    · exact preservesX2_readReg cur_privilege
    · intro privilege
      apply PreservesX2.bind
      · exact preservesX2_effectivePrivilege (MemoryAccessType.Store mem_payload.Data)
          mstatusBits privilege
      · intro effectivePrivilege
        exact preservesX2_mem_write_value_priv_meta_store address width value pbmt
          effectivePrivilege metadata

theorem preservesX2_mem_write_value_store (address : physaddr) (width : Nat)
    (value : BitVec (8 * width)) (pbmt : page_based_mem_type) :
    PreservesX2 (mem_write_value address width value
      (MemoryAccessType.Store mem_payload.Data) pbmt false false false) := by
  unfold mem_write_value
  exact preservesX2_mem_write_value_meta_store address width value pbmt default_meta

theorem preservesX2_split_misaligned (address : virtaddr) (width : Nat) :
    PreservesX2 (split_misaligned address width) := by
  unfold split_misaligned
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · apply PreservesX2.ite
    · exact PreservesX2.pure _
    · apply PreservesX2.bind
      · exact preservesX2_assert _ _
      · intro _
        exact PreservesX2.pure _

theorem preservesX2_misaligned_order (count : Int) :
    PreservesX2 (misaligned_order count |> pure) := by
  unfold misaligned_order
  exact PreservesX2.pure _

theorem preservesX2_trap (exception : sync_exception) : PreservesX2 (trap exception) := by
  unfold trap
  apply PreservesX2.bind
  · exact preservesX2_readReg cur_privilege
  · intro privilege
    apply PreservesX2.bind
    · exact preservesX2_readReg PC
    · intro pc
      exact PreservesX2.pure _

theorem preservesX2_memory_exception (address : virtaddr) (exception : ExceptionType) :
    PreservesX2 (memory_exception address exception) := by
  unfold memory_exception
  exact preservesX2_trap _

theorem preservesX2_plat_misaligned_exception (access : MemoryAccessType mem_payload)
    (reservation : Bool) : PreservesX2 (plat_misaligned_exception access reservation) := by
  unfold plat_misaligned_exception
  apply PreservesX2.bind
  · exact preservesX2_assert _ _
  · intro _
    exact PreservesX2.ite reservation (EStateM.pure (some plat_misaligned_access.lrsc))
      (if is_vector_access access then EStateM.pure plat_misaligned_access.vector
      else EStateM.pure plat_misaligned_access.load_store)
      (PreservesX2.pure _) (PreservesX2.ite _ _ _ (PreservesX2.pure _) (PreservesX2.pure _))

theorem preservesX2E_vmem_write_store_misaligned_then (address : virtaddr) :
    PreservesX2E (do
      match (← plat_misaligned_exception (MemoryAccessType.Store mem_payload.Data) false) with
      | some .AccessFault =>
        Sail.SailME.throw (← do
          pure (Sail.Err (← memory_exception address (ExceptionType.E_SAMO_Access_Fault ()))))
      | some .AlignmentException =>
        Sail.SailME.throw (← do
          pure (Sail.Err (← memory_exception address (ExceptionType.E_SAMO_Addr_Align ()))))
      | none => pure () : SailME (Sail.Result Bool ExecutionResult) PUnit) := by
  apply PreservesX2E.bind
  · exact PreservesX2E.lift
      (plat_misaligned_exception (MemoryAccessType.Store mem_payload.Data) false)
      (preservesX2_plat_misaligned_exception (MemoryAccessType.Store mem_payload.Data) false)
  · intro exception
    cases exception with
    | none => exact PreservesX2E.pure _
    | some exception =>
      cases exception with
      | AccessFault =>
        apply PreservesX2E.bind
        · apply PreservesX2E.bind
          · exact PreservesX2E.lift
              (memory_exception address (ExceptionType.E_SAMO_Access_Fault ()))
              (preservesX2_memory_exception address (ExceptionType.E_SAMO_Access_Fault ()))
          · intro result
            exact PreservesX2E.pure (Sail.Err result)
        · intro error
          exact PreservesX2E.throw error
      | AlignmentException =>
        apply PreservesX2E.bind
        · apply PreservesX2E.bind
          · exact PreservesX2E.lift
              (memory_exception address (ExceptionType.E_SAMO_Addr_Align ()))
              (preservesX2_memory_exception address (ExceptionType.E_SAMO_Addr_Align ()))
          · intro result
            exact PreservesX2E.pure (Sail.Err result)
        · intro error
          exact PreservesX2E.throw error

theorem preservesX2E_vmem_write_store_misaligned (address : virtaddr) (width : Nat) :
    PreservesX2E (if LeanRV64DExecutable.Functions.not (is_aligned_vaddr address width) then
      (do
        match (← plat_misaligned_exception (MemoryAccessType.Store mem_payload.Data) false) with
        | some .AccessFault =>
          Sail.SailME.throw (← do
            pure (Sail.Err (← memory_exception address (ExceptionType.E_SAMO_Access_Fault ()))) )
        | some .AlignmentException =>
          Sail.SailME.throw (← do
            pure (Sail.Err (← memory_exception address (ExceptionType.E_SAMO_Addr_Align ()))) )
        | none => pure ())
      else pure () : SailME (Sail.Result Bool ExecutionResult) PUnit) := by
  apply PreservesX2E.ite
  · exact preservesX2E_vmem_write_store_misaligned_then address
  · exact PreservesX2E.pure _

theorem preservesX2_is_shadow_stack_access (access : MemoryAccessType mem_payload) :
    PreservesX2 (is_shadow_stack_access access) := by
  unfold is_shadow_stack_access
  cases access with
  | InstructionFetch _ => exact PreservesX2.pure _
  | Load payload =>
    cases payload <;> exact PreservesX2.pure _
  | LoadReserved payload =>
    cases payload <;> first | exact PreservesX2.pure _ | exact preservesX2_internal_error _ _ _
  | Store payload =>
    cases payload <;> exact PreservesX2.pure _
  | StoreConditional payload =>
    cases payload <;> first | exact PreservesX2.pure _ | exact preservesX2_internal_error _ _ _
  | Atomic payload =>
    rcases payload with ⟨operation, readPayload, writePayload⟩
    cases readPayload <;> cases writePayload <;>
      first | exact PreservesX2.pure _ | exact preservesX2_internal_error _ _ _
  | CacheAccess _ => exact PreservesX2.pure _

theorem preservesX2_satp_mode_width_forwards (mode : SATPMode) :
    PreservesX2 (satp_mode_width_forwards mode) := by
  cases mode <;> unfold satp_mode_width_forwards
  all_goals first
    | exact PreservesX2.pure _
    | exact PreservesX2.bind (Sail.assert false "Pattern match failure at unknown location")
        (fun _ => EStateM.throw Sail.Error.Exit) (preservesX2_assert _ _)
        (fun _ => PreservesX2.throw _)

theorem preservesX2_get_satp (svWidth : Nat) :
    PreservesX2 (get_satp svWidth) := by
  unfold get_satp
  apply PreservesX2.bind
      (Sail.assert ((svWidth == 32) || (LeanRV64DExecutable.Functions.xlen == 64))
        "sys/vmem.sail:395.30-395.31")
  · exact preservesX2_assert _ _
  · intro _
    by_cases hWidth : svWidth = 32
    · subst svWidth
      simp
      apply PreservesX2.bind (readReg satp)
      · exact preservesX2_readReg satp
      · intro _
        exact PreservesX2.pure _
    · have hWidthBool : (svWidth == 32) = false := beq_eq_false_iff_ne.mpr hWidth
      rw [hWidthBool]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply PreservesX2.bind (readReg satp)
      · exact preservesX2_readReg satp
      · intro _
        exact PreservesX2.pure _

theorem preservesX2_translationException_store_data (failure : PTW_Error) :
    PreservesX2 (translationException (MemoryAccessType.Store mem_payload.Data) failure) := by
  unfold translationException
  cases failure <;> exact PreservesX2.pure _

theorem preservesX2_currentlyEnabled_Svade :
    PreservesX2 (currentlyEnabled extension.Ext_Svade) := by
  simpa only [PreservesX2, PreservesStackPointer] using
    currentlyEnabled_svade_preserves_stack_pointer

theorem preservesX2_currentlyEnabled_Svadu :
    PreservesX2 (currentlyEnabled extension.Ext_Svadu) := by
  simpa only [PreservesX2, PreservesStackPointer] using
    currentlyEnabled_svadu_preserves_stack_pointer

theorem preservesX2_currentlyEnabled_Svnapot :
    PreservesX2 (currentlyEnabled extension.Ext_Svnapot) := by
  simpa only [PreservesX2, PreservesStackPointer] using
    currentlyEnabled_svnapot_preserves_stack_pointer

theorem preservesX2_currentlyEnabled_Svrsw60t59b :
    PreservesX2 (currentlyEnabled extension.Ext_Svrsw60t59b) := by
  simpa only [PreservesX2, PreservesStackPointer] using
    currentlyEnabled_svrsw60t59b_preserves_stack_pointer

theorem preservesX2_pte_is_invalid (flags : BitVec 8) (extensions : BitVec 10) :
    PreservesX2 (pte_is_invalid flags extensions) := by
  unfold pte_is_invalid
  apply PreservesX2.bind
  · exact preservesX2_readReg menvcfg
  · intro _
    apply PreservesX2.bind
    · exact preservesX2_currentlyEnabled_Svnapot
    · intro _
      apply PreservesX2.bind
      · exact preservesX2_readReg menvcfg
      · intro _
        apply PreservesX2.bind
        · exact preservesX2_currentlyEnabled_Svrsw60t59b
        · intro _
          exact PreservesX2.pure _

theorem preservesX2E_check_pte_priv_ok_store_data (privilege : Privilege) (pteU : Bool)
    (doSum : Bool) :
    PreservesX2E ((match privilege with
      | .User => pure pteU
      | .Supervisor => pure ((LeanRV64DExecutable.Functions.not pteU) || (doSum && true))
      | .Machine => internal_error "sys/vmem_pte.sail" 151 "m-mode mem perm check"
      | .VirtualUser => internal_error "sys/vmem_pte.sail" 152 "Hypervisor extension not supported"
      | .VirtualSupervisor =>
        internal_error "sys/vmem_pte.sail" 153 "Hypervisor extension not supported") :
      SailME PTE_Check Bool) := by
  cases privilege with
  | User => exact PreservesX2E.pure pteU
  | Supervisor => exact PreservesX2E.pure _
  | Machine =>
    exact PreservesX2E.lift (internal_error "sys/vmem_pte.sail" 151 "m-mode mem perm check")
      (preservesX2_internal_error _ _ _)
  | VirtualUser =>
    exact PreservesX2E.lift
      (internal_error "sys/vmem_pte.sail" 152 "Hypervisor extension not supported")
      (preservesX2_internal_error _ _ _)
  | VirtualSupervisor =>
    exact PreservesX2E.lift
      (internal_error "sys/vmem_pte.sail" 153 "Hypervisor extension not supported")
      (preservesX2_internal_error _ _ _)

theorem preservesX2E_check_pte_finish_store_data (pteW : Bool) :
    PreservesX2E (do
      let writable := pteW
      if LeanRV64DExecutable.Functions.not writable then
        pure (PTE_Check.PTE_Check_Failure ((), pte_check_failure.PTE_No_Permission ()))
      else pure (PTE_Check.PTE_Check_Success ()) : SailME PTE_Check PTE_Check) := by
  apply PreservesX2E.ite
  · exact PreservesX2E.pure _
  · exact PreservesX2E.pure _

theorem preservesX2E_check_pte_reserved_store_data :
    PreservesX2E (do
      let environment ← ExceptT.lift (readReg menvcfg)
      ExceptT.lift (Sail.assert (bool_bit_backwards (_get_MEnvcfg_SSE environment))
        "sys/vmem_pte.sail:162.33-162.34")
      let shadowStackOk ← pure false
      if LeanRV64DExecutable.Functions.not shadowStackOk then
        Sail.SailME.throw (PTE_Check.PTE_Check_Failure ((), pte_check_failure.PTE_No_Access ()))
      else pure () : SailME PTE_Check PUnit) := by
  apply PreservesX2E.bind
  · exact PreservesX2E.lift (readReg menvcfg) (preservesX2_readReg menvcfg)
  · intro environment
    apply PreservesX2E.bind
    · exact PreservesX2E.lift
        (Sail.assert (bool_bit_backwards (_get_MEnvcfg_SSE environment))
          "sys/vmem_pte.sail:162.33-162.34")
        (preservesX2_assert _ _)
    · intro _
      apply PreservesX2E.bind
      · exact PreservesX2E.pure false
      · intro shadowStackOk
        apply PreservesX2E.ite
        · exact PreservesX2E.throw _
        · exact PreservesX2E.pure _

theorem preservesX2E_check_pte_nonreserved_store_data (flags : BitVec 8) :
    PreservesX2E (do
      let shadowStack ← ExceptT.lift
        (is_shadow_stack_access (MemoryAccessType.Store mem_payload.Data))
      if shadowStack then
        Sail.SailME.throw (PTE_Check.PTE_Check_Failure ((),
          if (bit_to_bool (_get_PTE_Flags_R flags)) &&
              (LeanRV64DExecutable.Functions.not (bit_to_bool (_get_PTE_Flags_W flags)) &&
                LeanRV64DExecutable.Functions.not (bit_to_bool (_get_PTE_Flags_X flags))) then
            pte_check_failure.PTE_No_Permission ()
          else pte_check_failure.PTE_No_Access ()))
      else pure () : SailME PTE_Check PUnit) := by
  apply PreservesX2E.bind
  · exact PreservesX2E.lift
      (is_shadow_stack_access (MemoryAccessType.Store mem_payload.Data))
      (preservesX2_is_shadow_stack_access (MemoryAccessType.Store mem_payload.Data))
  · intro shadowStack
    apply PreservesX2E.ite
    · exact PreservesX2E.throw _
    · exact PreservesX2E.pure _

theorem preservesX2_check_PTE_permission_store_data (privilege : Privilege)
    (mxr doSum : Bool) (flags : BitVec 8) (extensions : BitVec 10) (external : Unit) :
    PreservesX2
      (check_PTE_permission (MemoryAccessType.Store mem_payload.Data) privilege mxr doSum flags
        extensions external) := by
  unfold check_PTE_permission
  apply preservesX2_sailMERun
  apply PreservesX2E.bind
  · exact PreservesX2E.lift (Sail.assert _ _) (preservesX2_assert _ _)
  · intro _
    apply PreservesX2E.bind
    · exact preservesX2E_check_pte_priv_ok_store_data privilege
        (bit_to_bool (_get_PTE_Flags_U flags)) doSum
    · intro privOk
      apply PreservesX2E.ite
      · exact PreservesX2E.pure _
      · apply PreservesX2E.ite
        · apply PreservesX2E.bind
          · exact preservesX2E_check_pte_reserved_store_data
          · intro _
            exact preservesX2E_check_pte_finish_store_data (bit_to_bool (_get_PTE_Flags_W flags))
        · apply PreservesX2E.bind
          · exact preservesX2E_check_pte_nonreserved_store_data flags
          · intro _
            exact preservesX2E_check_pte_finish_store_data (bit_to_bool (_get_PTE_Flags_W flags))

theorem preservesX2_readByte (address : Nat) :
    PreservesX2 (PreSail.readByte address : SailM (BitVec 8)) := by
  intro state
  unfold PreSail.readByte
  simp only [EStateM.instMonad, EStateM.bind, instMonadStateOfMonadStateOf,
    EStateM.instMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe]
  unfold EStateM.get
  simp only
  cases hRead : state.mem.get? address <;> rfl

theorem preservesX2_readBytes (size address : Nat) :
    PreservesX2 (PreSail.readBytes size address) := by
  induction size generalizing address with
  | zero => exact PreservesX2.pure _
  | succ size ih =>
    cases size with
    | zero =>
      simp only [PreSail.readBytes]
      apply PreservesX2.bind (PreSail.readByte address)
      · exact preservesX2_readByte address
      · intro _
        exact PreservesX2.pure _
    | succ size =>
      simp only [PreSail.readBytes]
      apply PreservesX2.bind (PreSail.readByte address)
      · exact preservesX2_readByte address
      · intro _
        apply PreservesX2.bind (PreSail.readBytes (size + 1) (address + 1))
        · exact ih (address := address + 1)
        · intro _
          exact PreservesX2.pure _

def storeReadRamPlainRequest (address : physaddrbits) (width : Nat) :
    SailM (Sail.ConcurrencyInterfaceV1.Mem_read_request width 64 physaddrbits Unit
      RISCV_strong_access) := do
  let accessKind ← pure (Sail.ConcurrencyInterfaceV1.AK_explicit
    { variety := Sail.ConcurrencyInterfaceV1.AV_plain
      strength := Sail.ConcurrencyInterfaceV1.AS_normal })
  pure { access_kind := accessKind
         va := none
         pa := address
         translation := ()
         size := width
         tag := false }

theorem preservesX2_storeReadRamPlainRequest (address : physaddrbits) (width : Nat) :
    PreservesX2 (storeReadRamPlainRequest address width) := by
  unfold storeReadRamPlainRequest
  apply PreservesX2.bind (pure (Sail.ConcurrencyInterfaceV1.AK_explicit
    { variety := Sail.ConcurrencyInterfaceV1.AV_plain
      strength := Sail.ConcurrencyInterfaceV1.AS_normal }))
  · exact PreservesX2.pure _
  · intro _
    exact PreservesX2.pure _

theorem preservesX2_plain_sail_mem_read
    (request : Sail.ConcurrencyInterfaceV1.Mem_read_request width 64 physaddrbits Unit
      RISCV_strong_access) :
    PreservesX2 (Sail.ConcurrencyInterfaceV1.sail_mem_read request) := by
  delta Sail.ConcurrencyInterfaceV1.sail_mem_read
  unfold PreSail.ConcurrencyInterfaceV1.sail_mem_read
  apply PreservesX2.bind (PreSail.readBytes width request.pa.toNat)
  · exact preservesX2_readBytes width request.pa.toNat
  · intro _
    exact PreservesX2.pure _

theorem storeReadRamPlainUnfold (address : physaddrbits) (width : Nat) :
    read_ram .Read_plain (.Physaddr address) width false = (do
      let request ← storeReadRamPlainRequest address width
      match ← Sail.ConcurrencyInterfaceV1.sail_mem_read request with
      | .Ok (value, _) => pure (value, default_meta)
      | .Err () => EStateM.throw Sail.Error.Exit) := by
  rfl

theorem preservesX2_read_ram_plain (address : physaddr) (width : Nat) :
    PreservesX2 (read_ram .Read_plain address width false) := by
  rcases address with ⟨address⟩
  rw [storeReadRamPlainUnfold]
  apply PreservesX2.bind (storeReadRamPlainRequest address width)
  · exact preservesX2_storeReadRamPlainRequest address width
  · intro request
    apply PreservesX2.bind (Sail.ConcurrencyInterfaceV1.sail_mem_read request)
    · exact preservesX2_plain_sail_mem_read request
    · intro result
      cases result with
      | Ok value => exact PreservesX2.pure _
      | Err error => exact PreservesX2.throw _

theorem preservesX2_accessFault_load_pte :
    PreservesX2 (accessFaultFromAccessType (MemoryAccessType.Load mem_payload.PageTableEntry)) := by
  unfold accessFaultFromAccessType
  exact PreservesX2.pure _

theorem preservesX2_accessFault_store_pte :
    PreservesX2
      (accessFaultFromAccessType
        (MemoryAccessType.Store mem_payload.PageTableEntry)) := by
  unfold accessFaultFromAccessType
  exact PreservesX2.pure _

theorem preservesX2_alignmentFault_load_pte :
    PreservesX2
      (alignmentFaultFromAccessType
        (MemoryAccessType.Load mem_payload.PageTableEntry)) := by
  unfold alignmentFaultFromAccessType
  exact PreservesX2.pure _

theorem preservesX2_alignmentFault_store_pte :
    PreservesX2
      (alignmentFaultFromAccessType
        (MemoryAccessType.Store mem_payload.PageTableEntry)) := by
  unfold alignmentFaultFromAccessType
  exact PreservesX2.pure _

theorem preservesX2_pmpCheckRWX_load_pte (config : BitVec 8) :
    PreservesX2 (pmpCheckRWX config (MemoryAccessType.Load mem_payload.PageTableEntry)) := by
  unfold pmpCheckRWX
  exact PreservesX2.pure _

theorem preservesX2_pmpCheckRWX_store_pte (config : BitVec 8) :
    PreservesX2 (pmpCheckRWX config (MemoryAccessType.Store mem_payload.PageTableEntry)) := by
  unfold pmpCheckRWX
  exact PreservesX2.pure _

theorem preservesX2E_pmpLoopAfterPrev (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) (index : Int)
    (previousPmpaddr : BitVec 64) (loopVars : Unit)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesX2 (pmpCheckRWX config access)) :
    PreservesX2E
      (pmpLoopAfterPrev address width access privilege index previousPmpaddr loopVars) := by
  unfold pmpLoopAfterPrev
  apply PreservesX2E.bind
  · exact PreservesX2E.lift (Sail.readReg pmpcfg_n) (preservesX2_readReg pmpcfg_n)
  · intro rawConfig
    apply PreservesX2E.bind
    · exact PreservesX2E.pure _
    · intro config
      apply PreservesX2E.bind
      · exact PreservesX2E.lift (pmpReadAddrReg index.toNat)
          (preservesX2_pmpReadAddrReg index.toNat)
      · intro currentPmpaddr
        apply PreservesX2E.bind
        · exact PreservesX2E.lift
            (pmpMatchAddr address width config currentPmpaddr previousPmpaddr)
            (preservesX2_pmpMatchAddr address width config currentPmpaddr previousPmpaddr)
        · intro matched
          cases matched with
          | PMP_NoMatch => exact PreservesX2E.pure _
          | PMP_PartialMatch =>
            apply PreservesX2E.bind
            · apply PreservesX2E.bind
              · exact PreservesX2E.lift (accessFaultFromAccessType access) accessFaultFrame
              · intro fault
                exact PreservesX2E.pure (some fault)
            · intro fault
              exact PreservesX2E.throw fault
          | PMP_Match =>
            apply PreservesX2E.bind
            · apply PreservesX2E.bind
              · exact PreservesX2E.lift (pmpCheckRWX config access) (rwxFrame config)
              · intro permitted
                apply PreservesX2E.ite
                · exact PreservesX2E.pure none
                · apply PreservesX2E.bind
                  · exact PreservesX2E.lift (accessFaultFromAccessType access) accessFaultFrame
                  · intro fault
                    exact PreservesX2E.pure (some fault)
            · intro fault
              exact PreservesX2E.throw fault

theorem preservesX2E_pmpLoopBody (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) (index : Int)
    (inRange : index ∈ pmpLoopRange) (loopVars : Unit)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesX2 (pmpCheckRWX config access)) :
    PreservesX2E (pmpLoopBody address width access privilege index inRange loopVars) := by
  unfold pmpLoopBody
  apply PreservesX2E.ite
  · apply PreservesX2E.bind
    · exact PreservesX2E.lift (pmpReadAddrReg (index - 1).toNat)
        (preservesX2_pmpReadAddrReg (index - 1).toNat)
    · intro previousPmpaddr
      exact preservesX2E_pmpLoopAfterPrev address width access privilege index previousPmpaddr
        loopVars accessFaultFrame rwxFrame
  · exact preservesX2E_pmpLoopAfterPrev address width access privilege index zeros loopVars
      accessFaultFrame rwxFrame

theorem preservesX2E_pmpLoop (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesX2 (pmpCheckRWX config access)) :
    PreservesX2E
      (IntRange.forIn' pmpLoopRange () (pmpLoopBody address width access privilege)) := by
  unfold IntRange.forIn'
  exact preservesX2E_pmpLoopInvariant
    (pmpLoopBody address width access privilege)
    (fun index inRange =>
      preservesX2E_pmpLoopBody address width access privilege index inRange () accessFaultFrame
        rwxFrame)
    pmpLoopRange.start (by simp)

theorem preservesX2_pmpCheck (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesX2 (pmpCheckRWX config access)) :
    PreservesX2 (pmpCheck address width access privilege) := by
  rw [pmpCheck_loop_eq]
  unfold pmpCheckLoop
  apply preservesX2_sailMERun
  apply PreservesX2E.bind
  · exact preservesX2E_pmpLoop address (to_bits width) access privilege accessFaultFrame rwxFrame
  · intro loopVars
    apply PreservesX2E.bind
    · exact PreservesX2E.pure loopVars
    · intro _
      apply PreservesX2E.ite
      · exact PreservesX2E.pure _
      · apply PreservesX2E.bind
        · exact PreservesX2E.lift (accessFaultFromAccessType access) accessFaultFrame
        · intro fault
          exact PreservesX2E.pure (some fault)

theorem preservesX2_pmpCheck_load_pte (address : physaddr) (width : Nat)
    (privilege : Privilege) :
    PreservesX2 (pmpCheck address width (MemoryAccessType.Load mem_payload.PageTableEntry)
      privilege) :=
  preservesX2_pmpCheck address width (MemoryAccessType.Load mem_payload.PageTableEntry) privilege
    preservesX2_accessFault_load_pte preservesX2_pmpCheckRWX_load_pte

theorem preservesX2_pmpCheck_store_pte (address : physaddr) (width : Nat)
    (privilege : Privilege) :
    PreservesX2 (pmpCheck address width (MemoryAccessType.Store mem_payload.PageTableEntry)
      privilege) :=
  preservesX2_pmpCheck address width (MemoryAccessType.Store mem_payload.PageTableEntry) privilege
    preservesX2_accessFault_store_pte preservesX2_pmpCheckRWX_store_pte

theorem preservesX2_pmaCheck_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (reservation : Bool) :
    PreservesX2 (pmaCheck address width (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt
      reservation) := by
  unfold pmaCheck
  apply PreservesX2.bind
  · exact preservesX2_readReg pma_regions
  · intro regions
    cases hPma : matching_pma_region regions address width with
    | none =>
      simp only
      apply PreservesX2.bind
        (accessFaultFromAccessType
          (MemoryAccessType.Load mem_payload.PageTableEntry))
      · exact preservesX2_accessFault_load_pte
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
                (accessFaultFromAccessType (MemoryAccessType.Load mem_payload.PageTableEntry))
              · exact preservesX2_accessFault_load_pte
              · intro _
                exact PreservesX2.pure _
        | some exception =>
          cases exception with
          | AccessFault =>
            apply PreservesX2.bind
                (accessFaultFromAccessType (MemoryAccessType.Load mem_payload.PageTableEntry))
            · exact preservesX2_accessFault_load_pte
            · intro _
              exact PreservesX2.pure _
          | AlignmentException =>
            apply PreservesX2.bind
                (alignmentFaultFromAccessType (MemoryAccessType.Load mem_payload.PageTableEntry))
            · exact preservesX2_alignmentFault_load_pte
            · intro _
              exact PreservesX2.pure _

end BinaryFv.RiscV
