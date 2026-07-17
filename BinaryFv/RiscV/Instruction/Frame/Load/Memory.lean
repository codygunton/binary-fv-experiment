import BinaryFv.RiscV.Instruction.Frame.Load.Calculus

/-!
# LOAD framing through the sparse-RAM read path
-/

namespace BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType

theorem load_preserves_split_misaligned (address : virtaddr) (width : Nat) :
    PreservesStackPointer (split_misaligned address width) := by
  unfold split_misaligned
  apply load_preserves_ite
  · exact load_preserves_pure _
  · apply load_preserves_ite
    · exact load_preserves_pure _
    · apply load_preserves_bind (Sail.assert
          (width == (Int.tdiv width
            (2 ^i Sail.BitVec.countTrailingZeros (bits_of_virtaddr address)) *i
            (2 ^i Sail.BitVec.countTrailingZeros (bits_of_virtaddr address))).toNat)
          "sys/vmem_utils.sail:63.51-63.52")
      · exact load_preserves_assert _ _
      · intro _
        exact load_preserves_pure _

theorem load_preserves_access_fault_load_data :
    PreservesStackPointer (accessFaultFromAccessType (.Load mem_payload.Data)) := by
  unfold accessFaultFromAccessType
  exact load_preserves_pure _

theorem load_preserves_access_fault_load_pte :
    PreservesStackPointer (accessFaultFromAccessType (.Load mem_payload.PageTableEntry)) := by
  unfold accessFaultFromAccessType
  exact load_preserves_pure _

theorem load_preserves_access_fault_store_pte :
    PreservesStackPointer (accessFaultFromAccessType (.Store mem_payload.PageTableEntry)) := by
  unfold accessFaultFromAccessType
  exact load_preserves_pure _

theorem load_preserves_alignment_fault_load_data :
    PreservesStackPointer (alignmentFaultFromAccessType (.Load mem_payload.Data)) := by
  unfold alignmentFaultFromAccessType
  exact load_preserves_pure _

theorem load_preserves_alignment_fault_load_pte :
    PreservesStackPointer (alignmentFaultFromAccessType (.Load mem_payload.PageTableEntry)) := by
  unfold alignmentFaultFromAccessType
  exact load_preserves_pure _

theorem load_preserves_alignment_fault_store_pte :
    PreservesStackPointer (alignmentFaultFromAccessType (.Store mem_payload.PageTableEntry)) := by
  unfold alignmentFaultFromAccessType
  exact load_preserves_pure _

theorem load_preserves_readByte (address : Nat) :
    PreservesStackPointer (PreSail.readByte address : SailM (BitVec 8)) := by
  intro state
  unfold PreSail.readByte
  simp only [EStateM.run, EStateM.instMonad, EStateM.bind, instMonadStateOfMonadStateOf,
    EStateM.instMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe]
  unfold EStateM.get
  simp only
  cases hRead : state.mem.get? address with
  | none => rfl
  | some value => rfl

theorem load_preserves_readBytes (size address : Nat) :
    PreservesStackPointer (PreSail.readBytes size address) := by
  induction size generalizing address with
  | zero => exact load_preserves_pure _
  | succ size ih =>
    cases size with
    | zero =>
      simp only [PreSail.readBytes]
      apply load_preserves_bind (PreSail.readByte address)
      · exact load_preserves_readByte address
      · intro _
        exact load_preserves_pure _
    | succ size =>
      simp only [PreSail.readBytes]
      apply load_preserves_bind (PreSail.readByte address)
      · exact load_preserves_readByte address
      · intro _
        apply load_preserves_bind (PreSail.readBytes (size + 1) (address + 1))
        · exact ih (address := address + 1)
        · intro _
          exact load_preserves_pure _

def load_read_ram_plain_request (address : physaddrbits) (width : Nat) :
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

theorem load_preserves_read_ram_plain_request (address : physaddrbits) (width : Nat) :
    PreservesStackPointer (load_read_ram_plain_request address width) := by
  unfold load_read_ram_plain_request
  apply load_preserves_bind (pure (Sail.ConcurrencyInterfaceV1.AK_explicit
    { variety := Sail.ConcurrencyInterfaceV1.AV_plain
      strength := Sail.ConcurrencyInterfaceV1.AS_normal }))
  · exact load_preserves_pure _
  · intro _
    exact load_preserves_pure _

theorem load_preserves_plain_sail_mem_read
    (request : Sail.ConcurrencyInterfaceV1.Mem_read_request width 64 physaddrbits Unit
      RISCV_strong_access) :
    PreservesStackPointer (Sail.ConcurrencyInterfaceV1.sail_mem_read request) := by
  delta Sail.ConcurrencyInterfaceV1.sail_mem_read
  unfold PreSail.ConcurrencyInterfaceV1.sail_mem_read
  apply load_preserves_bind (PreSail.readBytes width request.pa.toNat)
  · exact load_preserves_readBytes width request.pa.toNat
  · intro _
    exact load_preserves_pure _

theorem load_read_ram_plain_unfold (address : physaddrbits) (width : Nat) :
    read_ram .Read_plain (.Physaddr address) width false = (do
      let request ← load_read_ram_plain_request address width
      match ← Sail.ConcurrencyInterfaceV1.sail_mem_read request with
      | .Ok (value, _) => pure (value, default_meta)
      | .Err () => throw Sail.Error.Exit) := by
  rfl

theorem load_preserves_read_ram_plain (address : physaddr) (width : Nat) :
    PreservesStackPointer (read_ram .Read_plain address width false) := by
  rcases address with ⟨address⟩
  rw [load_read_ram_plain_unfold]
  apply load_preserves_bind (load_read_ram_plain_request address width)
  · exact load_preserves_read_ram_plain_request address width
  · intro request
    apply load_preserves_bind (Sail.ConcurrencyInterfaceV1.sail_mem_read request)
    · exact load_preserves_plain_sail_mem_read request
    · intro result
      cases result with
      | Ok value => exact load_preserves_pure _
      | Err error => exact load_preserves_throw _

theorem load_preserves_pmpCheckRWX_load_data (config : BitVec 8) :
    PreservesStackPointer (pmpCheckRWX config (.Load mem_payload.Data)) := by
  unfold pmpCheckRWX
  exact load_preserves_pure _

theorem load_preserves_pmpCheckRWX_load_pte (config : BitVec 8) :
    PreservesStackPointer (pmpCheckRWX config (.Load mem_payload.PageTableEntry)) := by
  unfold pmpCheckRWX
  exact load_preserves_pure _

theorem load_preserves_pmpCheckRWX_store_pte (config : BitVec 8) :
    PreservesStackPointer (pmpCheckRWX config (.Store mem_payload.PageTableEntry)) := by
  unfold pmpCheckRWX
  exact load_preserves_pure _

theorem load_preserves_pmpReadAddrReg (index : Nat) :
    PreservesStackPointer (pmpReadAddrReg index) := by
  unfold pmpReadAddrReg
  apply load_preserves_bind (readReg pmpcfg_n)
  · exact load_preserves_readReg pmpcfg_n
  · intro config
    apply load_preserves_bind (pure _)
    · exact load_preserves_pure _
    · intro matchType
      apply load_preserves_bind (readReg pmpaddr_n)
      · exact load_preserves_readReg pmpaddr_n
      · intro addresses
        apply load_preserves_bind (pure _)
        · exact load_preserves_pure _
        · intro address
          have bitCases : (Sail.BitVec.access matchType 1).toNat = 0 ∨
              (Sail.BitVec.access matchType 1).toNat = 1 := by
            omega
          rcases bitCases with hBit | hBit
          all_goals
            have bitValue : Sail.BitVec.access matchType 1 =
                BitVec.ofNat 1 (Sail.BitVec.access matchType 1).toNat := by
              rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
              omega
            rw [bitValue]
            simp [hBit]
            all_goals split <;> exact load_preserves_pure _

theorem load_preserves_pmpMatchAddr (address : physaddr) (width : BitVec 64)
    (config : BitVec 8) (current previous : BitVec 64) :
    PreservesStackPointer (pmpMatchAddr address width config current previous) := by
  unfold pmpMatchAddr
  cases hMatch : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A config)
  · exact load_preserves_pure _
  · apply load_preserves_ite <;> exact load_preserves_pure _
  · apply load_preserves_bind (Sail.assert _ _)
    · exact load_preserves_assert _ _
    · intro _
      exact load_preserves_pure _
  · exact load_preserves_pure _

def load_pmp_loop_range : IntRange := {
  start := 0
  stop := sys_pmp_count - 1
  step := 1
  step_pos := by omega
}

def load_pmp_loop_after_prev (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) (index : Int)
    (previousPmpaddr : BitVec 64) (loopVars : Unit) :
    SailME (Option ExceptionType) (ForInStep Unit) := do
  let rawConfig ← liftM (Sail.readReg pmpcfg_n)
  let config ← pure (GetElem?.getElem! rawConfig index)
  let currentPmpaddr ← liftM (pmpReadAddrReg index.toNat)
  match (← liftM (pmpMatchAddr address width config currentPmpaddr previousPmpaddr)) with
  | .PMP_NoMatch => pure ()
  | .PMP_PartialMatch =>
    Sail.SailME.throw (← do pure (some (← liftM (accessFaultFromAccessType access))))
  | .PMP_Match =>
    Sail.SailME.throw (← do
      if (((← liftM (pmpCheckRWX config access)) ||
          ((privilege == .Machine) &&
            LeanRV64DExecutable.Functions.not (pmpLocked config))) : Bool) then
        pure none
      else pure (some (← liftM (accessFaultFromAccessType access))))
  pure PUnit.unit
  pure (.yield loopVars)

theorem load_preserves_pmp_loop_after_prev (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) (index : Int)
    (previousPmpaddr : BitVec 64) (loopVars : Unit)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesStackPointer (pmpCheckRWX config access)) :
    LoadPreservesExcept
      (load_pmp_loop_after_prev address width access privilege index previousPmpaddr loopVars) := by
  unfold load_pmp_loop_after_prev
  apply load_preserves_except_bind
  · exact load_preserves_except_lift (Sail.readReg pmpcfg_n)
      (load_preserves_readReg pmpcfg_n)
  · intro rawConfig
    apply load_preserves_except_bind
    · exact load_preserves_except_pure _
    · intro config
      apply load_preserves_except_bind
      · exact load_preserves_except_lift (pmpReadAddrReg index.toNat)
          (load_preserves_pmpReadAddrReg index.toNat)
      · intro currentPmpaddr
        apply load_preserves_except_bind
        · exact load_preserves_except_lift
            (pmpMatchAddr address width config currentPmpaddr previousPmpaddr)
            (load_preserves_pmpMatchAddr address width config currentPmpaddr previousPmpaddr)
        · intro matched
          cases matched with
          | PMP_NoMatch => exact load_preserves_except_pure _
          | PMP_PartialMatch =>
            apply load_preserves_except_bind
            · apply load_preserves_except_bind
              · exact load_preserves_except_lift (accessFaultFromAccessType access)
                  accessFaultFrame
              · intro fault
                exact load_preserves_except_pure (some fault)
            · intro fault
              exact load_preserves_except_throw fault
          | PMP_Match =>
            apply load_preserves_except_bind
            · apply load_preserves_except_bind
              · exact load_preserves_except_lift (pmpCheckRWX config access) (rwxFrame config)
              · intro permitted
                apply load_preserves_except_ite
                · exact load_preserves_except_pure none
                · apply load_preserves_except_bind
                  · exact load_preserves_except_lift (accessFaultFromAccessType access)
                      accessFaultFrame
                  · intro fault
                    exact load_preserves_except_pure (some fault)
            · intro fault
              exact load_preserves_except_throw fault

def load_pmp_loop_body (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (index : Int) (_ : index ∈ load_pmp_loop_range) (loopVars : Unit) :
    SailME (Option ExceptionType) (ForInStep Unit) := do
  let () := loopVars
  if ((index >b 0) : Bool) then do
    let previousPmpaddr ← liftM (pmpReadAddrReg (index - 1).toNat)
    load_pmp_loop_after_prev address width access privilege index previousPmpaddr loopVars
  else load_pmp_loop_after_prev address width access privilege index zeros loopVars

theorem load_preserves_pmp_loop_body (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (index : Int) (inRange : index ∈ load_pmp_loop_range) (loopVars : Unit)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesStackPointer (pmpCheckRWX config access)) :
    LoadPreservesExcept
      (load_pmp_loop_body address width access privilege index inRange loopVars) := by
  unfold load_pmp_loop_body
  apply load_preserves_except_ite
  · apply load_preserves_except_bind
    · exact load_preserves_except_lift (pmpReadAddrReg (index - 1).toNat)
        (load_preserves_pmpReadAddrReg (index - 1).toNat)
    · intro previousPmpaddr
      exact load_preserves_pmp_loop_after_prev address width access privilege index previousPmpaddr
        loopVars accessFaultFrame rwxFrame
  · exact load_preserves_pmp_loop_after_prev address width access privilege index zeros loopVars
      accessFaultFrame rwxFrame

theorem load_preserves_pmp_loop_invariant
    (body : (index : Int) → index ∈ load_pmp_loop_range → Unit →
      SailME (Option ExceptionType) (ForInStep Unit))
    (bodyFrame : ∀ (index : Int) (inRange : index ∈ load_pmp_loop_range),
      LoadPreservesExcept (body index inRange ()))
    (index : Int) (stepDiv : (index - load_pmp_loop_range.start) % load_pmp_loop_range.step = 0) :
    LoadPreservesExcept (IntRange.forIn'.loop load_pmp_loop_range body () index stepDiv) := by
  unfold IntRange.forIn'.loop
  by_cases inRange : index ∈ load_pmp_loop_range
  · simp only [dif_pos inRange]
    apply load_preserves_except_bind
    · exact bodyFrame index inRange
    · intro result
      cases result with
      | done loopVars => exact load_preserves_except_pure _
      | yield loopVars =>
        exact load_preserves_pmp_loop_invariant body bodyFrame
          (index + load_pmp_loop_range.step) (by
            rw [Int.add_comm, Int.add_sub_assoc]
            simp_all)
  · simp only [dif_neg inRange]
    exact load_preserves_except_pure _
termination_by (sys_pmp_count - index).toNat
decreasing_by
  change (sys_pmp_count - (index + 1)).toNat < (sys_pmp_count - index).toNat
  have bounds : (0 : Int) ≤ index ∧ index ≤ sys_pmp_count - 1 := by
    simpa [load_pmp_loop_range, IntRange.instMemIntRange] using inRange
  omega

theorem load_preserves_pmp_loop (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesStackPointer (pmpCheckRWX config access)) :
    LoadPreservesExcept (IntRange.forIn' load_pmp_loop_range ()
      (load_pmp_loop_body address width access privilege)) := by
  unfold IntRange.forIn'
  exact load_preserves_pmp_loop_invariant
    (load_pmp_loop_body address width access privilege)
    (fun index inRange =>
      load_preserves_pmp_loop_body address width access privilege index inRange () accessFaultFrame
        rwxFrame)
    load_pmp_loop_range.start (by simp)

def load_pmp_check_loop (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) :
    SailM (Option ExceptionType) := Sail.SailME.run do
  let loopVars ← IntRange.forIn' load_pmp_loop_range ()
    (load_pmp_loop_body address (to_bits width) access privilege)
  pure loopVars
  if ((privilege == .Machine) : Bool) then pure none
  else pure (some (← liftM (accessFaultFromAccessType access)))

theorem load_pmpCheck_loop_eq (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) :
    pmpCheck address width access privilege =
      load_pmp_check_loop address width access privilege := by
  unfold pmpCheck load_pmp_check_loop load_pmp_loop_range load_pmp_loop_body
    load_pmp_loop_after_prev
  simp only [sys_pmp_count]
  have countNotZero : ((16 : Int) == 0) = false := rfl
  simp only [countNotZero, Bool.false_eq_true, ↓reduceIte]
  rw [forIn_eq_forIn']
  rfl

theorem load_preserves_pmpCheck (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesStackPointer (pmpCheckRWX config access)) :
    PreservesStackPointer (pmpCheck address width access privilege) := by
  rw [load_pmpCheck_loop_eq]
  unfold load_pmp_check_loop
  apply load_preserves_sailME_run
  apply load_preserves_except_bind
  · exact load_preserves_pmp_loop address (to_bits width) access privilege accessFaultFrame rwxFrame
  · intro loopVars
    apply load_preserves_except_bind
    · exact load_preserves_except_pure loopVars
    · intro _
      apply load_preserves_except_ite
      · exact load_preserves_except_pure _
      · apply load_preserves_except_bind
        · exact load_preserves_except_lift (accessFaultFromAccessType access) accessFaultFrame
        · intro fault
          exact load_preserves_except_pure (some fault)

theorem load_preserves_pmpCheck_load_data (address : physaddr) (width : Nat)
    (privilege : Privilege) :
    PreservesStackPointer (pmpCheck address width (.Load mem_payload.Data) privilege) :=
  load_preserves_pmpCheck address width (.Load mem_payload.Data) privilege
    load_preserves_access_fault_load_data load_preserves_pmpCheckRWX_load_data

theorem load_preserves_pmpCheck_load_pte (address : physaddr) (width : Nat)
    (privilege : Privilege) :
    PreservesStackPointer (pmpCheck address width (.Load mem_payload.PageTableEntry) privilege) :=
  load_preserves_pmpCheck address width (.Load mem_payload.PageTableEntry) privilege
    load_preserves_access_fault_load_pte load_preserves_pmpCheckRWX_load_pte

theorem load_preserves_pmpCheck_store_pte (address : physaddr) (width : Nat)
    (privilege : Privilege) :
    PreservesStackPointer (pmpCheck address width (.Store mem_payload.PageTableEntry) privilege) :=
  load_preserves_pmpCheck address width (.Store mem_payload.PageTableEntry) privilege
    load_preserves_access_fault_store_pte load_preserves_pmpCheckRWX_store_pte

theorem load_preserves_pmaCheck_load_data (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (reservation : Bool) :
    PreservesStackPointer
      (pmaCheck address width (.Load mem_payload.Data) pbmt reservation) := by
  unfold pmaCheck
  apply load_preserves_bind (readReg pma_regions)
  · exact load_preserves_readReg pma_regions
  · intro regions
    cases hPma : matching_pma_region regions address width with
    | none =>
      apply load_preserves_bind (accessFaultFromAccessType (.Load mem_payload.Data))
      · exact load_preserves_access_fault_load_data
      · intro _
        exact load_preserves_pure _
    | some region =>
      rcases region with ⟨base, size, attributes, includeInDeviceTree⟩
      apply load_preserves_bind
      · apply load_preserves_ite
        · exact load_preserves_pure _
        · unfold pma_misaligned_exception
          exact load_preserves_pure _
      · intro exception
        cases exception with
        | none =>
          apply load_preserves_bind
          · apply load_preserves_bind (Sail.assert _ _)
            · exact load_preserves_assert _ _
            · intro _
              exact load_preserves_pure _
          · intro canAccess
            apply load_preserves_ite
            · exact load_preserves_pure _
            · apply load_preserves_bind (accessFaultFromAccessType (.Load mem_payload.Data))
              · exact load_preserves_access_fault_load_data
              · intro _
                exact load_preserves_pure _
        | some exception =>
          cases exception with
          | AccessFault =>
            apply load_preserves_bind (accessFaultFromAccessType (.Load mem_payload.Data))
            · exact load_preserves_access_fault_load_data
            · intro _
              exact load_preserves_pure _
          | AlignmentException =>
            apply load_preserves_bind (alignmentFaultFromAccessType (.Load mem_payload.Data))
            · exact load_preserves_alignment_fault_load_data
            · intro _
              exact load_preserves_pure _

theorem load_preserves_pmaCheck_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (reservation : Bool) :
    PreservesStackPointer
      (pmaCheck address width (.Load mem_payload.PageTableEntry) pbmt reservation) := by
  unfold pmaCheck
  apply load_preserves_bind (readReg pma_regions)
  · exact load_preserves_readReg pma_regions
  · intro regions
    cases hPma : matching_pma_region regions address width with
    | none =>
      apply load_preserves_bind (accessFaultFromAccessType (.Load mem_payload.PageTableEntry))
      · exact load_preserves_access_fault_load_pte
      · intro _
        exact load_preserves_pure _
    | some region =>
      rcases region with ⟨base, size, attributes, includeInDeviceTree⟩
      apply load_preserves_bind
      · apply load_preserves_ite
        · exact load_preserves_pure _
        · unfold pma_misaligned_exception
          exact load_preserves_pure _
      · intro exception
        cases exception with
        | none =>
          apply load_preserves_bind
          · apply load_preserves_bind (Sail.assert _ _)
            · exact load_preserves_assert _ _
            · intro _
              exact load_preserves_pure _
          · intro canAccess
            apply load_preserves_ite
            · exact load_preserves_pure _
            · apply load_preserves_bind
                (accessFaultFromAccessType (.Load mem_payload.PageTableEntry))
              · exact load_preserves_access_fault_load_pte
              · intro _
                exact load_preserves_pure _
        | some exception =>
          cases exception with
          | AccessFault =>
            apply load_preserves_bind
                (accessFaultFromAccessType (.Load mem_payload.PageTableEntry))
            · exact load_preserves_access_fault_load_pte
            · intro _
              exact load_preserves_pure _
          | AlignmentException =>
            apply load_preserves_bind
                (alignmentFaultFromAccessType (.Load mem_payload.PageTableEntry))
            · exact load_preserves_alignment_fault_load_pte
            · intro _
              exact load_preserves_pure _

theorem load_preserves_pmaCheck_store_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (reservation : Bool) :
    PreservesStackPointer
      (pmaCheck address width (.Store mem_payload.PageTableEntry) pbmt reservation) := by
  unfold pmaCheck
  apply load_preserves_bind (readReg pma_regions)
  · exact load_preserves_readReg pma_regions
  · intro regions
    cases hPma : matching_pma_region regions address width with
    | none =>
      apply load_preserves_bind (accessFaultFromAccessType (.Store mem_payload.PageTableEntry))
      · exact load_preserves_access_fault_store_pte
      · intro _
        exact load_preserves_pure _
    | some region =>
      rcases region with ⟨base, size, attributes, includeInDeviceTree⟩
      apply load_preserves_bind
      · apply load_preserves_ite
        · exact load_preserves_pure _
        · unfold pma_misaligned_exception
          exact load_preserves_pure _
      · intro exception
        cases exception with
        | none =>
          apply load_preserves_bind
          · apply load_preserves_bind (Sail.assert _ _)
            · exact load_preserves_assert _ _
            · intro _
              exact load_preserves_pure _
          · intro canAccess
            apply load_preserves_ite
            · exact load_preserves_pure _
            · apply load_preserves_bind
                (accessFaultFromAccessType (.Store mem_payload.PageTableEntry))
              · exact load_preserves_access_fault_store_pte
              · intro _
                exact load_preserves_pure _
        | some exception =>
          cases exception with
          | AccessFault =>
            apply load_preserves_bind
                (accessFaultFromAccessType (.Store mem_payload.PageTableEntry))
            · exact load_preserves_access_fault_store_pte
            · intro _
              exact load_preserves_pure _
          | AlignmentException =>
            apply load_preserves_bind
                (alignmentFaultFromAccessType (.Store mem_payload.PageTableEntry))
            · exact load_preserves_alignment_fault_store_pte
            · intro _
              exact load_preserves_pure _

theorem load_preserves_alignmentOrAccessFaultPriority (exception : ExceptionType) :
    PreservesStackPointer (alignmentOrAccessFaultPriority exception) := by
  cases exception <;>
    simp [alignmentOrAccessFaultPriority, internal_error, Sail.sailThrow, PreSail.sailThrow,
      EStateM.instMonad]
  all_goals first | exact load_preserves_pure _ | exact load_preserves_throw _

theorem load_preserves_highestPriorityAlignmentOrAccessFault
    (left right : ExceptionType) :
    PreservesStackPointer (highestPriorityAlignmentOrAccessFault left right) := by
  unfold highestPriorityAlignmentOrAccessFault
  apply load_preserves_bind (alignmentOrAccessFaultPriority left)
  · exact load_preserves_alignmentOrAccessFaultPriority left
  · intro leftPriority
    apply load_preserves_bind (alignmentOrAccessFaultPriority right)
    · exact load_preserves_alignmentOrAccessFaultPriority right
    · intro rightPriority
      apply load_preserves_ite <;> exact load_preserves_pure _

theorem load_preserves_phys_access_check (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (privilege : Privilege)
    (reservation : Bool)
    (pmpFrame : PreservesStackPointer (pmpCheck address width access privilege))
    (pmaFrame : PreservesStackPointer (pmaCheck address width access pbmt reservation)) :
    PreservesStackPointer (phys_access_check access pbmt privilege address width reservation) := by
  unfold phys_access_check
  apply load_preserves_bind (pmpCheck address width access privilege)
  · exact pmpFrame
  · intro pmpError
    apply load_preserves_bind (pmaCheck address width access pbmt reservation)
    · exact pmaFrame
    · intro pmaError
      cases pmpError <;> cases pmaError
      · exact load_preserves_pure _
      · exact load_preserves_pure _
      · exact load_preserves_pure _
      · apply load_preserves_bind (highestPriorityAlignmentOrAccessFault _ _)
        · exact load_preserves_highestPriorityAlignmentOrAccessFault _ _
        · intro _
          exact load_preserves_pure _

theorem load_preserves_phys_access_check_load_data (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) (reservation : Bool) :
    PreservesStackPointer
      (phys_access_check (.Load mem_payload.Data) pbmt privilege address width reservation) :=
  load_preserves_phys_access_check address width (.Load mem_payload.Data) pbmt privilege reservation
    (load_preserves_pmpCheck_load_data address width privilege)
    (load_preserves_pmaCheck_load_data address width pbmt reservation)

theorem load_preserves_phys_access_check_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) (reservation : Bool) :
    PreservesStackPointer
      (phys_access_check (.Load mem_payload.PageTableEntry) pbmt privilege address width
        reservation) :=
  load_preserves_phys_access_check address width (.Load mem_payload.PageTableEntry) pbmt privilege
    reservation (load_preserves_pmpCheck_load_pte address width privilege)
    (load_preserves_pmaCheck_load_pte address width pbmt reservation)

theorem load_preserves_phys_access_check_store_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) (reservation : Bool) :
    PreservesStackPointer
      (phys_access_check (.Store mem_payload.PageTableEntry) pbmt privilege address width
        reservation) :=
  load_preserves_phys_access_check address width (.Store mem_payload.PageTableEntry) pbmt privilege
    reservation (load_preserves_pmpCheck_store_pte address width privilege)
    (load_preserves_pmaCheck_store_pte address width pbmt reservation)

theorem load_preserves_within_clint (address : physaddr) (width : Nat) :
    PreservesStackPointer (within_clint address width) := by
  unfold within_clint
  exact load_preserves_ite _ _ _ (load_preserves_pure _) (load_preserves_pure _)

theorem load_preserves_within_sig (address : physaddr) (width : Nat) :
    PreservesStackPointer (within_sig address width) := by
  unfold within_sig
  exact load_preserves_ite _ _ _ (load_preserves_pure _) (load_preserves_pure _)

theorem load_preserves_within_htif_writable (address : physaddr) (width : Nat) :
    PreservesStackPointer (within_htif_writable address width) := by
  unfold within_htif_writable
  apply load_preserves_bind (readReg htif_tohost_base)
  · exact load_preserves_readReg htif_tohost_base
  · intro base
    cases base <;> exact load_preserves_pure _

theorem load_preserves_within_htif_readable (address : physaddr) (width : Nat) :
    PreservesStackPointer (within_htif_readable address width) :=
  load_preserves_within_htif_writable address width

theorem load_preserves_within_mmio_readable (address : physaddr) (width : Nat) :
    PreservesStackPointer (within_mmio_readable address width) := by
  unfold within_mmio_readable
  apply load_preserves_ite
  · exact load_preserves_pure _
  · apply load_preserves_bind (within_clint address width)
    · exact load_preserves_within_clint address width
    · intro _
      apply load_preserves_bind (within_sig address width)
      · exact load_preserves_within_sig address width
      · intro _
        apply load_preserves_bind (within_htif_readable address width)
        · exact load_preserves_within_htif_readable address width
        · intro _
          exact load_preserves_pure _

theorem load_preserves_sig_load (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access)) :
    PreservesStackPointer (sig_load access address width) := by
  unfold sig_load
  apply load_preserves_ite
  · apply load_preserves_bind (accessFaultFromAccessType access)
    · exact accessFaultFrame
    · intro _
      exact load_preserves_pure _
  · apply load_preserves_ite
    · exact load_preserves_pure _
    · apply load_preserves_ite
      · exact load_preserves_pure _
      · apply load_preserves_bind (accessFaultFromAccessType access)
        · exact accessFaultFrame
        · intro _
          exact load_preserves_pure _

theorem load_preserves_clint_load (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access)) :
    PreservesStackPointer (clint_load access address width) := by
  unfold clint_load
  simp only [get_config_print_clint]
  apply load_preserves_ite
  · exact load_preserves_read_then_pure mip _
  · apply load_preserves_ite
    · exact load_preserves_read_then_pure mtimecmp _
    · apply load_preserves_ite
      · exact load_preserves_read_then_pure mtimecmp _
      · apply load_preserves_ite
        · exact load_preserves_read_then_pure mtimecmp _
        · apply load_preserves_ite
          · exact load_preserves_read_then_pure mtime _
          · apply load_preserves_ite
            · exact load_preserves_read_then_pure mtime _
            · apply load_preserves_ite
              · exact load_preserves_read_then_pure mtime _
              · apply load_preserves_bind (accessFaultFromAccessType access)
                · exact accessFaultFrame
                · intro _
                  exact load_preserves_pure _

end BinaryFv.RiscV
