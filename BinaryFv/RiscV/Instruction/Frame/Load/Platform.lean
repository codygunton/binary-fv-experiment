import BinaryFv.RiscV.Instruction.Frame.Load.Memory

/-!
# LOAD framing through the HTIF, CLINT, and MMIO paths
-/

namespace BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType

theorem load_preserves_htif_base :
    PreservesStackPointer ((do
      match (← readReg htif_tohost_base) with
      | some base => pure base
      | none => (internal_error "sys/platform.sail" 268
        "HTIF load while HTIF isn't enabled" : SailM physaddrbits)) : SailM physaddrbits) := by
  apply load_preserves_bind (readReg htif_tohost_base)
  · exact load_preserves_readReg htif_tohost_base
  · intro base
    cases base with
    | some base => exact load_preserves_pure base
    | none =>
      exact load_preserves_internal_error (α := physaddrbits)
        "sys/platform.sail" 268 "HTIF load while HTIF isn't enabled"

theorem load_preserves_htif_load (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access)) :
    PreservesStackPointer (htif_load access address width) := by
  unfold htif_load
  simp only [get_config_print_htif, Bool.false_eq_true, ↓reduceIte]
  apply load_preserves_bind (pure ())
  · exact load_preserves_pure _
  · intro _
    apply load_preserves_bind
    · exact load_preserves_htif_base
    · intro base
      apply load_preserves_ite
      · exact load_preserves_read_then_pure htif_tohost _
      · apply load_preserves_ite
        · exact load_preserves_read_then_pure htif_tohost _
        · apply load_preserves_ite
          · exact load_preserves_read_then_pure htif_tohost _
          · apply load_preserves_bind (accessFaultFromAccessType access)
            · exact accessFaultFrame
            · intro _
              exact load_preserves_pure _

theorem load_preserves_mmio_read (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access)) :
    PreservesStackPointer (mmio_read access address width) := by
  unfold mmio_read
  apply load_preserves_bind (within_clint address width)
  · exact load_preserves_within_clint address width
  · intro inClint
    apply load_preserves_ite
    · exact load_preserves_clint_load access address width accessFaultFrame
    · apply load_preserves_bind (within_sig address width)
      · exact load_preserves_within_sig address width
      · intro inSig
        apply load_preserves_ite
        · exact load_preserves_sig_load access address width accessFaultFrame
        · apply load_preserves_bind (within_htif_readable address width)
          · exact load_preserves_within_htif_readable address width
          · intro inHtif
            apply load_preserves_ite
            · exact load_preserves_htif_load access address width accessFaultFrame
            · apply load_preserves_bind (accessFaultFromAccessType access)
              · exact accessFaultFrame
              · intro _
                exact load_preserves_pure _

theorem load_preserves_mmio_read_load_data (address : physaddr) (width : Nat) :
    PreservesStackPointer (mmio_read (.Load mem_payload.Data) address width) :=
  load_preserves_mmio_read (.Load mem_payload.Data) address width
    load_preserves_access_fault_load_data

theorem load_preserves_mmio_read_load_pte (address : physaddr) (width : Nat) :
    PreservesStackPointer (mmio_read (.Load mem_payload.PageTableEntry) address width) :=
  load_preserves_mmio_read (.Load mem_payload.PageTableEntry) address width
    load_preserves_access_fault_load_pte

theorem load_preserves_checked_mem_read_load_data (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (checked_mem_read (.Load mem_payload.Data) pbmt privilege address width
        false false false false) := by
  unfold checked_mem_read
  apply load_preserves_bind
      (phys_access_check (.Load mem_payload.Data) pbmt privilege address width false)
  · exact load_preserves_phys_access_check_load_data address width pbmt privilege false
  · intro exception
    cases exception with
    | some exception => exact load_preserves_pure _
    | none =>
      apply load_preserves_bind (within_mmio_readable address width)
      · exact load_preserves_within_mmio_readable address width
      · intro inMmio
        apply load_preserves_ite
        · apply load_preserves_bind (mmio_read (.Load mem_payload.Data) address width)
          · exact load_preserves_mmio_read_load_data address width
          · intro _
            exact load_preserves_pure _
        · simp only [read_kind_of_flags]
          apply load_preserves_bind (read_ram .Read_plain address width false)
          · exact load_preserves_read_ram_plain address width
          · intro _
            exact load_preserves_pure _

theorem load_preserves_checked_mem_read_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (checked_mem_read (.Load mem_payload.PageTableEntry) pbmt privilege address width
        false false false false) := by
  unfold checked_mem_read
  apply load_preserves_bind
      (phys_access_check (.Load mem_payload.PageTableEntry) pbmt privilege address width false)
  · exact load_preserves_phys_access_check_load_pte address width pbmt privilege false
  · intro exception
    cases exception with
    | some exception => exact load_preserves_pure _
    | none =>
      apply load_preserves_bind (within_mmio_readable address width)
      · exact load_preserves_within_mmio_readable address width
      · intro inMmio
        apply load_preserves_ite
        · apply load_preserves_bind (mmio_read (.Load mem_payload.PageTableEntry) address width)
          · exact load_preserves_mmio_read_load_pte address width
          · intro _
            exact load_preserves_pure _
        · simp only [read_kind_of_flags]
          apply load_preserves_bind (read_ram .Read_plain address width false)
          · exact load_preserves_read_ram_plain address width
          · intro _
            exact load_preserves_pure _

theorem load_preserves_mem_read_priv_meta_load_data (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (mem_read_priv_meta (.Load mem_payload.Data) pbmt privilege address width
        false false false false) := by
  unfold mem_read_priv_meta
  simp only
  apply load_preserves_bind
      (checked_mem_read (.Load mem_payload.Data) pbmt privilege address width
        false false false false)
  · exact load_preserves_checked_mem_read_load_data address width pbmt privilege
  · intro _
    exact load_preserves_pure _

theorem load_preserves_mem_read_priv_meta_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (mem_read_priv_meta (.Load mem_payload.PageTableEntry) pbmt privilege address width
        false false false false) := by
  unfold mem_read_priv_meta
  simp only
  apply load_preserves_bind
      (checked_mem_read (.Load mem_payload.PageTableEntry) pbmt privilege address width
        false false false false)
  · exact load_preserves_checked_mem_read_load_pte address width pbmt privilege
  · intro _
    exact load_preserves_pure _

theorem load_preserves_mem_read_priv_load_data (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (mem_read_priv (.Load mem_payload.Data) pbmt privilege address width false false false) := by
  unfold mem_read_priv
  apply load_preserves_bind
      (mem_read_priv_meta (.Load mem_payload.Data) pbmt privilege address width
        false false false false)
  · exact load_preserves_mem_read_priv_meta_load_data address width pbmt privilege
  · intro _
    exact load_preserves_pure _

theorem load_preserves_mem_read_priv_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (mem_read_priv (.Load mem_payload.PageTableEntry) pbmt privilege address width
        false false false) := by
  unfold mem_read_priv
  apply load_preserves_bind
      (mem_read_priv_meta (.Load mem_payload.PageTableEntry) pbmt privilege address width
        false false false false)
  · exact load_preserves_mem_read_priv_meta_load_pte address width pbmt privilege
  · intro _
    exact load_preserves_pure _

theorem load_preserves_mem_read_load_data (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) :
    PreservesStackPointer
      (mem_read (.Load mem_payload.Data) pbmt address width false false false) := by
  unfold mem_read
  apply load_preserves_bind (readReg mstatus)
  · exact load_preserves_readReg mstatus
  · intro mstatusBits
    apply load_preserves_bind (readReg cur_privilege)
    · exact load_preserves_readReg cur_privilege
    · intro privilege
      apply load_preserves_bind (effectivePrivilege (.Load mem_payload.Data) mstatusBits privilege)
      · exact load_preserves_effectivePrivilege (.Load mem_payload.Data) mstatusBits privilege
      · intro effectivePrivilege
        exact load_preserves_mem_read_priv_load_data address width pbmt effectivePrivilege

theorem load_preserves_writeByte (address : Nat) (value : BitVec 8) :
    PreservesStackPointer (PreSail.writeByte address value : SailM PUnit) := by
  intro state
  rfl

theorem load_preserves_list_forM (values : List α) (action : α → SailM PUnit)
    (actionFrame : ∀ value, PreservesStackPointer (action value)) :
    PreservesStackPointer (values.forM action) := by
  induction values with
  | nil => exact load_preserves_pure _
  | cons value remaining induction =>
    simp only [List.forM]
    exact load_preserves_bind (action value) (fun _ => remaining.forM action)
      (actionFrame value) (fun _ => induction)

theorem load_preserves_writeBytes (address : Nat) (value : BitVec (8 * width)) :
    PreservesStackPointer (PreSail.writeBytes address value : SailM Bool) := by
  unfold PreSail.writeBytes
  apply load_preserves_bind
  · apply load_preserves_list_forM
    intro byte
    exact load_preserves_writeByte byte.1 byte.2
  · intro _
    exact load_preserves_pure _

theorem load_preserves_sail_mem_write [Sail.ConcurrencyInterfaceV1.Arch]
    (request : Sail.ConcurrencyInterfaceV1.Mem_write_request n vasize (BitVec pa_size) ts Arch) :
    PreservesStackPointer (PreSail.ConcurrencyInterfaceV1.sail_mem_write request) := by
  unfold PreSail.ConcurrencyInterfaceV1.sail_mem_write
  cases hValue : request.value with
  | none =>
    exact load_preserves_pure _
  | some value =>
    apply load_preserves_bind (PreSail.writeBytes request.pa.toNat value)
    · exact load_preserves_writeBytes request.pa.toNat value
    · intro _
      exact load_preserves_pure _

def load_write_ram_plain_request (address : physaddrbits) (width : Nat)
    (data : BitVec (8 * width)) :
    SailM (Sail.ConcurrencyInterfaceV1.Mem_write_request width 64 physaddrbits Unit
      RISCV_strong_access) := do
  let accessKind ← pure (Sail.ConcurrencyInterfaceV1.AK_explicit
    { variety := Sail.ConcurrencyInterfaceV1.AV_plain
      strength := Sail.ConcurrencyInterfaceV1.AS_normal })
  pure { access_kind := accessKind
         va := none
         pa := address
         translation := ()
         size := width
         value := some data
         tag := none }

theorem load_preserves_write_ram_plain_request (address : physaddrbits) (width : Nat)
    (data : BitVec (8 * width)) :
    PreservesStackPointer (load_write_ram_plain_request address width data) := by
  unfold load_write_ram_plain_request
  apply load_preserves_bind (pure (Sail.ConcurrencyInterfaceV1.AK_explicit
    { variety := Sail.ConcurrencyInterfaceV1.AV_plain
      strength := Sail.ConcurrencyInterfaceV1.AS_normal }))
  · exact load_preserves_pure _
  · intro _
    exact load_preserves_pure _

theorem load_write_ram_plain_unfold (address : physaddrbits) (width : Nat)
    (data : BitVec (8 * width)) (metadata : Unit) :
    write_ram .Write_plain (.Physaddr address) width data metadata = (do
      let request ← load_write_ram_plain_request address width data
      match ← Sail.ConcurrencyInterfaceV1.sail_mem_write request with
      | .Ok _ => pure true
      | .Err () => pure false) := by
  rfl

theorem load_preserves_write_ram_plain (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) (metadata : Unit) :
    PreservesStackPointer (write_ram .Write_plain address width data metadata) := by
  rcases address with ⟨address⟩
  rw [load_write_ram_plain_unfold]
  apply load_preserves_bind (load_write_ram_plain_request address width data)
  · exact load_preserves_write_ram_plain_request address width data
  · intro request
    apply load_preserves_bind (Sail.ConcurrencyInterfaceV1.sail_mem_write request)
    · exact load_preserves_sail_mem_write request
    · intro result
      cases result <;> exact load_preserves_pure _

theorem load_preserves_within_mmio_writable (address : physaddr) (width : Nat) :
    PreservesStackPointer (within_mmio_writable address width) := by
  unfold within_mmio_writable
  apply load_preserves_ite
  · exact load_preserves_pure _
  · apply load_preserves_bind (within_clint address width)
    · exact load_preserves_within_clint address width
    · intro _
      apply load_preserves_bind (within_sig address width)
      · exact load_preserves_within_sig address width
      · intro _
        apply load_preserves_bind (within_htif_writable address width)
        · exact load_preserves_within_htif_writable address width
        · intro _
          exact load_preserves_pure _

theorem load_preserves_external_seip :
    PreservesStackPointer ((do
      let enabled ← currentlyEnabled extension.Ext_S
      if enabled then readReg sig_seip else pure 0#1) : SailM (BitVec 1)) := by
  apply load_preserves_bind (currentlyEnabled extension.Ext_S)
  · exact load_preserves_currentlyEnabled_S
  · intro enabled
    apply load_preserves_ite
    · exact load_preserves_readReg sig_seip
    · exact load_preserves_pure _

theorem load_preserves_external_interrupts_pending :
    PreservesStackPointer (external_interrupts_pending ()) := by
  unfold external_interrupts_pending
  apply load_preserves_bind (readReg sig_meip)
  · exact load_preserves_readReg sig_meip
  · intro _
    apply load_preserves_bind
    · exact load_preserves_external_seip
    · intro _
      exact load_preserves_pure _

theorem load_preserves_read_mip (readType : XipReadType) :
    PreservesStackPointer (read_mip readType) := by
  cases readType
  · unfold read_mip
    apply load_preserves_bind (readReg mip)
    · exact load_preserves_readReg mip
    · intro mipBits
      apply load_preserves_bind (external_interrupts_pending ())
      · exact load_preserves_external_interrupts_pending
      · intro _
        exact load_preserves_pure _
  · unfold read_mip
    exact load_preserves_readReg mip

theorem load_preserves_csr_name_map_backwards_mip :
    PreservesStackPointer (csr_name_map_backwards "mip") := by
  unfold csr_name_map_backwards
  exact load_preserves_pure _

theorem load_preserves_csr_name_write_callback_mip (value : BitVec 64) :
    PreservesStackPointer (csr_name_write_callback "mip" value) := by
  unfold csr_name_write_callback
  apply load_preserves_bind (csr_name_map_backwards "mip")
  · exact load_preserves_csr_name_map_backwards_mip
  · intro _
    exact load_preserves_pure _

theorem load_preserves_clint_dispatch_tail (oldMip : BitVec 64) (mipWasWritten : Bool) :
    PreservesStackPointer (do
      let _ ← (pure () : SailM PUnit)
      let currentMip ← readReg mip
      if (oldMip != currentMip || mipWasWritten) then do
        let mipValue ← read_mip XipReadType.IncludePlatformInterrupts
        csr_name_write_callback "mip" mipValue
      else pure ()) := by
  apply load_preserves_bind (pure ())
  · exact load_preserves_pure _
  · intro _
    apply load_preserves_bind (readReg mip)
    · exact load_preserves_readReg mip
    · intro currentMip
      apply load_preserves_ite
      · apply load_preserves_bind (read_mip XipReadType.IncludePlatformInterrupts)
        · exact load_preserves_read_mip XipReadType.IncludePlatformInterrupts
        · intro mipValue
          exact load_preserves_csr_name_write_callback_mip mipValue
      · exact load_preserves_pure _

theorem load_preserves_clint_dispatch (mipWasWritten : Bool) :
    PreservesStackPointer (clint_dispatch mipWasWritten) :=
  clint_dispatch_preserves_stack_pointer mipWasWritten

theorem load_preserves_read_then_write (written : Register)
    (update : RegisterType written → RegisterType written) (notStack : x2 ≠ written) :
    PreservesStackPointer (readReg written >>= fun value => writeReg written (update value)) := by
  apply load_preserves_bind (readReg written)
  · exact load_preserves_readReg written
  · intro value
    exact load_preserves_writeReg written (update value) notStack

theorem load_preserves_then_clint_dispatch (initial : SailM α)
    (initialFrame : PreservesStackPointer initial) (mipWasWritten : Bool) :
    PreservesStackPointer (initial >>= fun _ => clint_dispatch mipWasWritten >>= fun _ =>
      (pure (Sail.Result.Ok true) : SailM (Sail.Result Bool ExceptionType))) := by
  apply load_preserves_bind initial
  · exact initialFrame
  · intro _
    apply load_preserves_bind (clint_dispatch mipWasWritten)
    · exact load_preserves_clint_dispatch mipWasWritten
    · intro _
      exact load_preserves_pure _

theorem load_preserves_clint_result (mipWasWritten : Bool) :
    PreservesStackPointer (clint_dispatch mipWasWritten >>= fun _ =>
      (pure (Sail.Result.Ok true) : SailM (Sail.Result Bool ExceptionType))) := by
  apply load_preserves_bind (clint_dispatch mipWasWritten)
  · exact load_preserves_clint_dispatch mipWasWritten
  · intro _
    exact load_preserves_pure _

theorem load_preserves_clint_store (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesStackPointer (clint_store address width data) := by
  unfold clint_store
  apply load_preserves_ite
  · apply load_preserves_bind (Sail.readReg mip)
    · exact load_preserves_readReg mip
    · intro current
      apply load_preserves_bind (Sail.writeReg mip (Sail.BitVec.updateSubrange current 3 3
        (Sail.BitVec.join1 [Sail.BitVec.access data 0])))
      · exact load_preserves_writeReg mip _ (by decide)
      · intro _
        exact load_preserves_clint_result true
  · apply load_preserves_ite
    · exact load_preserves_then_clint_dispatch (writeReg mtimecmp (zero_extend (m := 64) data))
        (load_preserves_writeReg mtimecmp _ (by decide)) false
    · apply load_preserves_ite
      · apply load_preserves_bind (readReg mtimecmp)
        · exact load_preserves_readReg mtimecmp
        · intro current
          apply load_preserves_bind (writeReg mtimecmp _)
          · exact load_preserves_writeReg mtimecmp _ (by decide)
          · intro _
            exact load_preserves_clint_result false
      · apply load_preserves_ite
        · apply load_preserves_bind (readReg mtimecmp)
          · exact load_preserves_readReg mtimecmp
          · intro current
            apply load_preserves_bind (writeReg mtimecmp _)
            · exact load_preserves_writeReg mtimecmp _ (by decide)
            · intro _
              exact load_preserves_clint_result false
        · apply load_preserves_ite
          · exact load_preserves_then_clint_dispatch (writeReg mtime data)
              (load_preserves_writeReg mtime _ (by decide)) false
          · apply load_preserves_ite
            · apply load_preserves_bind (readReg mtime)
              · exact load_preserves_readReg mtime
              · intro current
                apply load_preserves_bind (writeReg mtime _)
                · exact load_preserves_writeReg mtime _ (by decide)
                · intro _
                  exact load_preserves_clint_result false
            · apply load_preserves_ite
              · apply load_preserves_bind (readReg mtime)
                · exact load_preserves_readReg mtime
                · intro current
                  apply load_preserves_bind (writeReg mtime _)
                  · exact load_preserves_writeReg mtime _ (by decide)
                  · intro _
                    exact load_preserves_clint_result false
              · exact load_preserves_pure _

theorem load_preserves_mip_callback_ok :
    PreservesStackPointer (read_mip XipReadType.IncludePlatformInterrupts >>= fun value =>
      csr_name_write_callback "mip" value >>= fun _ =>
        (pure (Sail.Result.Ok true) : SailM (Sail.Result Bool ExceptionType))) := by
  apply load_preserves_bind (read_mip XipReadType.IncludePlatformInterrupts)
  · exact load_preserves_read_mip XipReadType.IncludePlatformInterrupts
  · intro value
    apply load_preserves_bind (csr_name_write_callback "mip" value)
    · exact load_preserves_csr_name_write_callback_mip value
    · intro _
      exact load_preserves_pure _

def load_sig_after_ssi (interrupts : BitVec 64) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := do
  let enabled ← currentlyEnabled extension.Ext_S
  if ((_get_Minterrupts_SSI interrupts == 1#1) && enabled) then do
    let current ← readReg mip
    let _ ← writeReg mip (Sail.BitVec.updateSubrange current 1 1 value)
    let mipValue ← read_mip XipReadType.IncludePlatformInterrupts
    csr_name_write_callback "mip" mipValue
    pure (Sail.Result.Ok true)
  else do
    let _ ← (pure () : SailM PUnit)
    let mipValue ← read_mip XipReadType.IncludePlatformInterrupts
    csr_name_write_callback "mip" mipValue
    pure (Sail.Result.Ok true)

def load_sig_after_msi (interrupts : BitVec 64) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := if _get_Minterrupts_MSI interrupts == 1#1 then do
      let current ← readReg mip
      let _ ← writeReg mip (Sail.BitVec.updateSubrange current 3 3 value)
      load_sig_after_ssi interrupts value
    else do
      let _ ← (pure () : SailM PUnit)
      load_sig_after_ssi interrupts value

def load_sig_after_sei (interrupts : BitVec 64) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := if _get_Minterrupts_SEI interrupts == 1#1 then do
      let _ ← writeReg sig_seip value
      load_sig_after_msi interrupts value
    else do
      let _ ← (pure () : SailM PUnit)
      load_sig_after_msi interrupts value

def load_sig_after_mei (interrupts : BitVec 64) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := if _get_Minterrupts_MEI interrupts == 1#1 then do
      let _ ← writeReg sig_meip value
      load_sig_after_sei interrupts value
    else do
      let _ ← (pure () : SailM PUnit)
      load_sig_after_sei interrupts value

theorem load_preserves_sig_after_ssi (interrupts : BitVec 64) (value : BitVec 1) :
    PreservesStackPointer (load_sig_after_ssi interrupts value) := by
  unfold load_sig_after_ssi
  apply load_preserves_bind (currentlyEnabled extension.Ext_S)
  · exact load_preserves_currentlyEnabled_S
  · intro enabled
    apply load_preserves_ite
    · apply load_preserves_bind (readReg mip)
      · exact load_preserves_readReg mip
      · intro current
        apply load_preserves_bind (writeReg mip _)
        · exact load_preserves_writeReg mip _ (by decide)
        · intro _
          exact load_preserves_mip_callback_ok
    · apply load_preserves_bind (pure ())
      · exact load_preserves_pure _
      · intro _
        exact load_preserves_mip_callback_ok

theorem load_preserves_sig_after_msi (interrupts : BitVec 64) (value : BitVec 1) :
    PreservesStackPointer (load_sig_after_msi interrupts value) := by
  unfold load_sig_after_msi
  apply load_preserves_ite
  · apply load_preserves_bind (readReg mip)
    · exact load_preserves_readReg mip
    · intro current
      apply load_preserves_bind (writeReg mip _)
      · exact load_preserves_writeReg mip _ (by decide)
      · intro _
        exact load_preserves_sig_after_ssi interrupts value
  · apply load_preserves_bind (pure ())
    · exact load_preserves_pure _
    · intro _
      exact load_preserves_sig_after_ssi interrupts value

theorem load_preserves_sig_after_sei (interrupts : BitVec 64) (value : BitVec 1) :
    PreservesStackPointer (load_sig_after_sei interrupts value) := by
  unfold load_sig_after_sei
  apply load_preserves_ite
  · apply load_preserves_bind (writeReg sig_seip value)
    · exact load_preserves_writeReg sig_seip value (by decide)
    · intro _
      exact load_preserves_sig_after_msi interrupts value
  · apply load_preserves_bind (pure ())
    · exact load_preserves_pure _
    · intro _
      exact load_preserves_sig_after_msi interrupts value

theorem load_preserves_sig_after_mei (interrupts : BitVec 64) (value : BitVec 1) :
    PreservesStackPointer (load_sig_after_mei interrupts value) := by
  unfold load_sig_after_mei
  apply load_preserves_ite
  · apply load_preserves_bind (writeReg sig_meip value)
    · exact load_preserves_writeReg sig_meip value (by decide)
    · intro _
      exact load_preserves_sig_after_sei interrupts value
  · apply load_preserves_bind (pure ())
    · exact load_preserves_pure _
    · intro _
      exact load_preserves_sig_after_sei interrupts value

theorem load_preserves_sig_store (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesStackPointer (sig_store address width data) := by
  unfold sig_store
  apply load_preserves_ite
  · exact load_preserves_pure _
  · apply load_preserves_ite
    · exact load_preserves_pure _
    · apply load_preserves_ite
      · apply load_preserves_ite
        · exact load_preserves_pure _
        · exact load_preserves_sig_after_mei (Mk_Minterrupts (zero_extend data))
            (Sail.BitVec.access data 31)
      · exact load_preserves_pure _

theorem load_preserves_except_readReg (register : Register) :
    LoadPreservesExcept (ExceptT.lift (readReg register) : SailME ε (RegisterType register)) :=
  load_preserves_except_lift (readReg register) (load_preserves_readReg register)

theorem load_preserves_except_writeReg (written : Register) (value : RegisterType written)
    (notStack : x2 ≠ written) :
    LoadPreservesExcept (ExceptT.lift (writeReg written value) : SailME ε PUnit) :=
  load_preserves_except_lift (writeReg written value)
    (load_preserves_writeReg written value notStack)

theorem load_preserves_except_read_then_write (written : Register)
    (update : RegisterType written → RegisterType written) (notStack : x2 ≠ written) :
    LoadPreservesExcept (do
      let value ← ExceptT.lift (readReg written)
      ExceptT.lift (writeReg written (update value)) : SailME ε PUnit) := by
  apply load_preserves_except_bind
  · exact load_preserves_except_readReg written
  · intro value
    exact load_preserves_except_writeReg written (update value) notStack

theorem load_preserves_reset_htif : PreservesStackPointer (reset_htif ()) := by
  unfold reset_htif
  apply load_preserves_bind (writeReg htif_cmd_write _)
  · exact load_preserves_writeReg htif_cmd_write _ (by decide)
  · intro _
    apply load_preserves_bind (writeReg htif_payload_writes _)
    · exact load_preserves_writeReg htif_payload_writes _ (by decide)
    · intro _
      exact load_preserves_writeReg htif_tohost _ (by decide)

theorem load_preserves_plat_term_write (value : BitVec 8) :
    PreservesStackPointer (plat_term_write value) := by
  intro state
  rfl

theorem load_preserves_htif_store (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesStackPointer (htif_store address width data) :=
  htif_store_preserves_stack_pointer address width data

theorem load_preserves_mmio_write (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) :
    PreservesStackPointer (mmio_write address width data) := by
  unfold mmio_write
  apply load_preserves_bind (within_clint address width)
  · exact load_preserves_within_clint address width
  · intro inClint
    apply load_preserves_ite
    · exact load_preserves_clint_store address width data
    · apply load_preserves_bind (within_sig address width)
      · exact load_preserves_within_sig address width
      · intro inSig
        apply load_preserves_ite
        · exact load_preserves_sig_store address width data
        · apply load_preserves_bind (within_htif_writable address width)
          · exact load_preserves_within_htif_writable address width
          · intro inHtif
            apply load_preserves_ite
            · exact load_preserves_htif_store address width data
            · exact load_preserves_pure _

theorem load_preserves_checked_mem_write_store_pte (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (checked_mem_write address width data (.Store mem_payload.PageTableEntry) pbmt privilege
        default_meta false false false) := by
  unfold checked_mem_write
  apply load_preserves_bind
      (phys_access_check (.Store mem_payload.PageTableEntry) pbmt privilege address width false)
  · exact load_preserves_phys_access_check_store_pte address width pbmt privilege false
  · intro exception
    cases exception with
    | some exception => exact load_preserves_pure _
    | none =>
      apply load_preserves_bind (within_mmio_writable address width)
      · exact load_preserves_within_mmio_writable address width
      · intro inMmio
        apply load_preserves_ite
        · exact load_preserves_mmio_write address width data
        · simp only [write_kind_of_flags]
          apply load_preserves_bind (write_ram .Write_plain address width data default_meta)
          · exact load_preserves_write_ram_plain address width data default_meta
          · intro _
            exact load_preserves_pure _

theorem load_preserves_mem_write_value_priv_meta_store_pte (address : physaddr)
    (width : Nat) (data : BitVec (8 * width)) (pbmt : page_based_mem_type)
    (privilege : Privilege) :
    PreservesStackPointer
      (mem_write_value_priv_meta address width data (.Store mem_payload.PageTableEntry) pbmt
        privilege default_meta false false false) := by
  unfold mem_write_value_priv_meta
  simp only
  apply load_preserves_bind
      (checked_mem_write address width data (.Store mem_payload.PageTableEntry) pbmt privilege
        default_meta false false false)
  · exact load_preserves_checked_mem_write_store_pte address width data pbmt privilege
  · intro _
    exact load_preserves_pure _

theorem load_preserves_mem_write_value_priv_store_pte (address : physaddr)
    (width : Nat) (data : BitVec (8 * width)) (privilege : Privilege)
    (pbmt : page_based_mem_type) :
    PreservesStackPointer
      (mem_write_value_priv address width data privilege (.Store mem_payload.PageTableEntry) pbmt
        false false false) := by
  unfold mem_write_value_priv
  exact load_preserves_mem_write_value_priv_meta_store_pte address width data pbmt privilege

theorem load_preserves_write_pte_native (address : physaddr) (width : Nat)
    (data : BitVec (width * 8)) :
    PreservesStackPointer (write_pte address width data) := by
  unfold write_pte
  exact load_preserves_mem_write_value_priv_store_pte address width _ .Supervisor .PBMT_PMA

theorem load_preserves_pte_is_invalid (flags : BitVec 8) (extensions : BitVec 10) :
    PreservesStackPointer (pte_is_invalid flags extensions) := by
  unfold pte_is_invalid
  apply load_preserves_bind (readReg menvcfg)
  · exact load_preserves_readReg menvcfg
  · intro _
    apply load_preserves_bind (currentlyEnabled extension.Ext_Svnapot)
    · exact load_preserves_currentlyEnabled_Svnapot
    · intro _
      apply load_preserves_bind (readReg menvcfg)
      · exact load_preserves_readReg menvcfg
      · intro _
        apply load_preserves_bind (currentlyEnabled extension.Ext_Svrsw60t59b)
        · exact load_preserves_currentlyEnabled_Svrsw60t59b
        · intro _
          exact load_preserves_pure _

theorem load_preserves_check_pte_priv_ok (privilege : Privilege) (pteU : Bool)
    (doSum : Bool) :
    LoadPreservesExcept ((match privilege with
      | .User => pure pteU
      | .Supervisor => pure ((LeanRV64DExecutable.Functions.not pteU) || (doSum && true))
      | .Machine => internal_error "sys/vmem_pte.sail" 151 "m-mode mem perm check"
      | .VirtualUser => internal_error "sys/vmem_pte.sail" 152 "Hypervisor extension not supported"
      | .VirtualSupervisor =>
        internal_error "sys/vmem_pte.sail" 153 "Hypervisor extension not supported") :
      SailME PTE_Check Bool) := by
  cases privilege with
  | User => exact load_preserves_except_pure pteU
  | Supervisor => exact load_preserves_except_pure _
  | Machine => exact load_preserves_except_lift (internal_error "sys/vmem_pte.sail" 151
      "m-mode mem perm check" : SailM Bool) (load_preserves_internal_error _ _ _)
  | VirtualUser => exact load_preserves_except_lift (internal_error "sys/vmem_pte.sail" 152
      "Hypervisor extension not supported" : SailM Bool) (load_preserves_internal_error _ _ _)
  | VirtualSupervisor => exact load_preserves_except_lift (internal_error "sys/vmem_pte.sail" 153
      "Hypervisor extension not supported" : SailM Bool) (load_preserves_internal_error _ _ _)

theorem load_preserves_check_pte_finish_load_data (pteR pteX mxr : Bool) :
    LoadPreservesExcept (do
      let readable := pteR || (pteX && mxr)
      if LeanRV64DExecutable.Functions.not readable then
        pure (PTE_Check.PTE_Check_Failure ((), pte_check_failure.PTE_No_Permission ()))
      else pure (PTE_Check.PTE_Check_Success ()) : SailME PTE_Check PTE_Check) := by
  apply load_preserves_except_ite
  · exact load_preserves_except_pure _
  · exact load_preserves_except_pure _

theorem load_preserves_check_pte_reserved_load_data :
    LoadPreservesExcept (do
      let environment ← ExceptT.lift (readReg menvcfg)
      ExceptT.lift (Sail.assert (bool_bit_backwards (_get_MEnvcfg_SSE environment))
        "sys/vmem_pte.sail:162.33-162.34")
      let shadowStackOk ← pure true
      if LeanRV64DExecutable.Functions.not shadowStackOk then
        Sail.SailME.throw (PTE_Check.PTE_Check_Failure ((), pte_check_failure.PTE_No_Access ()))
      else pure () : SailME PTE_Check PUnit) := by
  apply load_preserves_except_lift_bind (readReg menvcfg)
  · exact load_preserves_readReg menvcfg
  · intro environment
    apply load_preserves_except_lift_bind
        (Sail.assert (bool_bit_backwards (_get_MEnvcfg_SSE environment))
          "sys/vmem_pte.sail:162.33-162.34")
    · exact load_preserves_assert _ _
    · intro _
      apply load_preserves_except_bind
      · exact load_preserves_except_pure true
      · intro shadowStackOk
        apply load_preserves_except_ite
        · exact load_preserves_except_throw _
        · exact load_preserves_except_pure _

theorem load_preserves_check_pte_nonreserved_load_data (flags : BitVec 8) :
    LoadPreservesExcept (do
      let shadowStack ← ExceptT.lift (is_shadow_stack_access (.Load mem_payload.Data))
      if shadowStack then
        Sail.SailME.throw (PTE_Check.PTE_Check_Failure ((),
          if (bit_to_bool (_get_PTE_Flags_R flags)) &&
              (LeanRV64DExecutable.Functions.not (bit_to_bool (_get_PTE_Flags_W flags)) &&
                LeanRV64DExecutable.Functions.not (bit_to_bool (_get_PTE_Flags_X flags))) then
            pte_check_failure.PTE_No_Permission ()
          else pte_check_failure.PTE_No_Access ()))
      else pure () : SailME PTE_Check PUnit) := by
  apply load_preserves_except_lift_bind (is_shadow_stack_access (.Load mem_payload.Data))
  · exact load_preserves_is_shadow_stack_access (.Load mem_payload.Data)
  · intro shadowStack
    apply load_preserves_except_ite
    · exact load_preserves_except_throw _
    · exact load_preserves_except_pure _

theorem load_preserves_check_PTE_permission_load_data (privilege : Privilege)
    (mxr doSum : Bool) (flags : BitVec 8) (extensions : BitVec 10) (external : Unit) :
    PreservesStackPointer
      (check_PTE_permission (.Load mem_payload.Data) privilege mxr doSum flags extensions
        external) := by
  unfold check_PTE_permission
  apply load_preserves_sailME_run
  apply load_preserves_except_lift_bind
  · exact load_preserves_assert _ _
  · intro _
    apply load_preserves_except_bind
    · exact load_preserves_check_pte_priv_ok privilege (bit_to_bool (_get_PTE_Flags_U flags)) doSum
    · intro privOk
      apply load_preserves_except_ite
      · exact load_preserves_except_pure _
      · apply load_preserves_except_ite
        · apply load_preserves_except_bind
          · exact load_preserves_check_pte_reserved_load_data
          · intro _
            exact load_preserves_check_pte_finish_load_data
              (bit_to_bool (_get_PTE_Flags_R flags)) (bit_to_bool (_get_PTE_Flags_X flags)) mxr
        · apply load_preserves_except_bind
          · exact load_preserves_check_pte_nonreserved_load_data flags
          · intro _
            exact load_preserves_check_pte_finish_load_data
              (bit_to_bool (_get_PTE_Flags_R flags)) (bit_to_bool (_get_PTE_Flags_X flags)) mxr

theorem load_preserves_update_and_write_pte_load_data (address : physaddr) (width : Nat)
    (pte : BitVec (width * 8)) :
    PreservesStackPointer
      (update_and_write_pte address width pte (.Load mem_payload.Data)) := by
  unfold update_and_write_pte
  cases hUpdate : update_PTE_Bits pte
      (.Load mem_payload.Data) with
  | none => exact load_preserves_pure _
  | some updated =>
    apply load_preserves_bind (currentlyEnabled extension.Ext_Svadu)
    · exact load_preserves_currentlyEnabled_Svadu
    · intro _
      apply load_preserves_bind (readReg menvcfg)
      · exact load_preserves_readReg menvcfg
      · intro _
        apply load_preserves_bind (currentlyEnabled extension.Ext_Svadu)
        · exact load_preserves_currentlyEnabled_Svadu
        · intro _
          apply load_preserves_bind (currentlyEnabled extension.Ext_Svade)
          · exact load_preserves_currentlyEnabled_Svade
          · intro _
            apply load_preserves_ite
            · apply load_preserves_bind (write_pte address width updated)
              · exact load_preserves_write_pte_native address width updated
              · intro result
                cases result <;> exact load_preserves_pure _
            · exact load_preserves_pure _

end BinaryFv.RiscV
