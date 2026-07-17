import BinaryFv.RiscV.Instruction.Frame.Store.Calculus

/-!
# `x2` framing through the PMP/PMA store checks
-/

namespace BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

theorem preservesX2_pmaCheck_store (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) :
    PreservesX2 (pmaCheck address width (MemoryAccessType.Store mem_payload.Data)
      pbmt false) := by
  unfold pmaCheck
  apply PreservesX2.bind
  · exact preservesX2_readReg pma_regions
  · intro regions
    cases hPma : matching_pma_region regions address width with
    | none =>
      simp only [accessFaultFromAccessType]
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
          · apply PreservesX2.bind
            · exact preservesX2_assert _ _
            · intro _
              exact PreservesX2.pure _
          · intro canAccess
            apply PreservesX2.ite
            · exact PreservesX2.pure _
            · apply PreservesX2.bind
              · unfold accessFaultFromAccessType
                exact PreservesX2.pure _
              · intro _
                exact PreservesX2.pure _
        | some exception =>
          cases exception
          · apply PreservesX2.bind
            · unfold accessFaultFromAccessType
              exact PreservesX2.pure _
            · intro _
              exact PreservesX2.pure _
          · apply PreservesX2.bind
            · unfold alignmentFaultFromAccessType
              exact PreservesX2.pure _
            · intro _
              exact PreservesX2.pure _

theorem preservesX2_pmpReadAddrReg (index : Nat) :
    PreservesX2 (pmpReadAddrReg index) := by
  unfold pmpReadAddrReg
  apply PreservesX2.bind
  · exact preservesX2_readReg pmpcfg_n
  · intro config
    apply PreservesX2.bind
    · exact PreservesX2.pure _
    · intro matchType
      apply PreservesX2.bind
      · exact preservesX2_readReg pmpaddr_n
      · intro addresses
        apply PreservesX2.bind
        · exact PreservesX2.pure _
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
            all_goals split <;> exact PreservesX2.pure _

theorem preservesX2_pmpMatchAddr (address : physaddr) (width : BitVec 64)
    (config : BitVec 8) (current previous : BitVec 64) :
    PreservesX2 (pmpMatchAddr address width config current previous) := by
  unfold pmpMatchAddr
  cases hMatch : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A config)
  · exact PreservesX2.pure _
  · apply PreservesX2.ite <;> exact PreservesX2.pure _
  · apply PreservesX2.bind
    · exact preservesX2_assert _ _
    · intro _
      exact PreservesX2.pure _
  · exact PreservesX2.pure _

theorem preservesX2_pmpCheckRWX_store (config : BitVec 8) :
    PreservesX2 (pmpCheckRWX config (MemoryAccessType.Store mem_payload.Data)) := by
  unfold pmpCheckRWX
  exact PreservesX2.pure _

def pmpLoopRange : IntRange := {
  start := 0
  stop := sys_pmp_count - 1
  step := 1
  step_pos := by omega
}

def pmpLoopAfterPrev (address : physaddr) (width : xlenbits)
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

def pmpLoopBody (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (index : Int) (_ : index ∈ pmpLoopRange) (loopVars : Unit) :
    SailME (Option ExceptionType) (ForInStep Unit) := do
  let () := loopVars
  if ((index >b 0) : Bool) then do
    let previousPmpaddr ← liftM (pmpReadAddrReg (index - 1).toNat)
    pmpLoopAfterPrev address width access privilege index previousPmpaddr loopVars
  else pmpLoopAfterPrev address width access privilege index zeros loopVars

def pmpCheckLoop (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) :
    SailM (Option ExceptionType) := Sail.SailME.run do
  let loopVars ← IntRange.forIn' pmpLoopRange ()
    (pmpLoopBody address (to_bits width) access privilege)
  pure loopVars
  if ((privilege == .Machine) : Bool) then pure none
  else pure (some (← liftM (accessFaultFromAccessType access)))

theorem pmpCheck_loop_eq (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) :
    pmpCheck address width access privilege = pmpCheckLoop address width access privilege := by
  unfold pmpCheck pmpCheckLoop pmpLoopRange pmpLoopBody pmpLoopAfterPrev
  simp only [sys_pmp_count]
  have countNotZero : ((16 : Int) == 0) = false := rfl
  simp only [countNotZero, Bool.false_eq_true, ↓reduceIte]
  rw [forIn_eq_forIn']
  rfl

theorem preservesX2_accessFault_store :
    PreservesX2 (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.Data)) := by
  unfold accessFaultFromAccessType
  exact PreservesX2.pure _

theorem preservesX2E_pmpLoopAfterPrev_store (address : physaddr) (width : xlenbits)
    (privilege : Privilege) (index : Int) (previousPmpaddr : BitVec 64) (loopVars : Unit) :
    PreservesX2E
      (pmpLoopAfterPrev address width (MemoryAccessType.Store mem_payload.Data) privilege index
        previousPmpaddr loopVars) := by
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
              · exact PreservesX2E.lift
                  (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.Data))
                  preservesX2_accessFault_store
              · intro fault
                exact PreservesX2E.pure (some fault)
            · intro fault
              exact PreservesX2E.throw fault
          | PMP_Match =>
            apply PreservesX2E.bind
            · apply PreservesX2E.bind
              · exact PreservesX2E.lift
                  (pmpCheckRWX config (MemoryAccessType.Store mem_payload.Data))
                  (preservesX2_pmpCheckRWX_store config)
              · intro permitted
                apply PreservesX2E.ite
                · exact PreservesX2E.pure none
                · apply PreservesX2E.bind
                  · exact PreservesX2E.lift
                      (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.Data))
                      preservesX2_accessFault_store
                  · intro fault
                    exact PreservesX2E.pure (some fault)
            · intro fault
              exact PreservesX2E.throw fault

theorem preservesX2E_pmpLoopBody_store (address : physaddr) (width : xlenbits)
    (privilege : Privilege) (index : Int) (inRange : index ∈ pmpLoopRange) (loopVars : Unit) :
    PreservesX2E
      (pmpLoopBody address width (MemoryAccessType.Store mem_payload.Data) privilege index
        inRange loopVars) := by
  unfold pmpLoopBody
  apply PreservesX2E.ite
  · apply PreservesX2E.bind
    · exact PreservesX2E.lift (pmpReadAddrReg (index - 1).toNat)
        (preservesX2_pmpReadAddrReg (index - 1).toNat)
    · intro previousPmpaddr
      exact preservesX2E_pmpLoopAfterPrev_store address width privilege index previousPmpaddr
        loopVars
  · exact preservesX2E_pmpLoopAfterPrev_store address width privilege index zeros loopVars

theorem preservesX2E_pmpLoopInvariant
    (body : (index : Int) → index ∈ pmpLoopRange → Unit →
      SailME (Option ExceptionType) (ForInStep Unit))
    (bodyFrame : ∀ (index : Int) (inRange : index ∈ pmpLoopRange),
      PreservesX2E (body index inRange ()))
    (index : Int) (stepDiv : (index - pmpLoopRange.start) % pmpLoopRange.step = 0) :
    PreservesX2E (IntRange.forIn'.loop pmpLoopRange body () index stepDiv) := by
  unfold IntRange.forIn'.loop
  by_cases inRange : index ∈ pmpLoopRange
  · simp only [dif_pos inRange]
    apply PreservesX2E.bind
    · exact bodyFrame index inRange
    · intro result
      cases result with
      | done loopVars => exact PreservesX2E.pure _
      | yield loopVars =>
        exact preservesX2E_pmpLoopInvariant body bodyFrame
          (index + pmpLoopRange.step) (by
            rw [Int.add_comm, Int.add_sub_assoc]
            simp_all)
  · simp only [dif_neg inRange]
    exact PreservesX2E.pure _
termination_by (16 - index).toNat
decreasing_by
  change (16 - (index + 1)).toNat < (16 - index).toNat
  have bounds : (0 : Int) ≤ index ∧ index ≤ 15 := by
    simpa [pmpLoopRange, sys_pmp_count, IntRange.instMemIntRange] using inRange
  omega

theorem preservesX2E_pmpLoop_store (address : physaddr) (width : xlenbits)
    (privilege : Privilege) :
    PreservesX2E (IntRange.forIn' pmpLoopRange ()
      (pmpLoopBody address width (MemoryAccessType.Store mem_payload.Data) privilege)) := by
  unfold IntRange.forIn'
  exact preservesX2E_pmpLoopInvariant
    (pmpLoopBody address width (MemoryAccessType.Store mem_payload.Data) privilege)
    (fun index inRange =>
      preservesX2E_pmpLoopBody_store address width privilege index inRange ())
    pmpLoopRange.start (by simp)

theorem preservesX2_pmpCheck_store (address : physaddr) (width : Nat)
    (privilege : Privilege) :
    PreservesX2 (pmpCheck address width (MemoryAccessType.Store mem_payload.Data) privilege) := by
  rw [pmpCheck_loop_eq]
  unfold pmpCheckLoop
  apply preservesX2_sailMERun
  apply PreservesX2E.bind
  · exact preservesX2E_pmpLoop_store address (to_bits width) privilege
  · intro loopVars
    apply PreservesX2E.bind
    · exact PreservesX2E.pure loopVars
    · intro _
      apply PreservesX2E.ite
      · exact PreservesX2E.pure _
      · apply PreservesX2E.bind
        · exact PreservesX2E.lift
            (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.Data))
            preservesX2_accessFault_store
        · intro fault
          exact PreservesX2E.pure (some fault)

theorem preservesX2_alignmentOrAccessFaultPriority (exception : ExceptionType) :
    PreservesX2 (alignmentOrAccessFaultPriority exception) := by
  cases exception <;>
    simp [alignmentOrAccessFaultPriority, internal_error, Sail.sailThrow, PreSail.sailThrow,
      EStateM.instMonad]
  all_goals first | exact PreservesX2.pure _ | exact PreservesX2.throw _

theorem preservesX2_highestPriorityAlignmentOrAccessFault (left right : ExceptionType) :
    PreservesX2 (highestPriorityAlignmentOrAccessFault left right) := by
  unfold highestPriorityAlignmentOrAccessFault
  apply PreservesX2.bind
  · exact preservesX2_alignmentOrAccessFaultPriority left
  · intro leftPriority
    apply PreservesX2.bind
    · exact preservesX2_alignmentOrAccessFaultPriority right
    · intro rightPriority
      apply PreservesX2.ite <;> exact PreservesX2.pure _

theorem preservesX2_phys_access_check_store (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
      PreservesX2
        (phys_access_check (MemoryAccessType.Store mem_payload.Data) pbmt privilege address
          width false) := by
  unfold phys_access_check
  apply PreservesX2.bind
  · exact preservesX2_pmpCheck_store address width privilege
  · intro pmpError
    apply PreservesX2.bind
    · exact preservesX2_pmaCheck_store address width pbmt
    · intro pmaError
      cases pmpError <;> cases pmaError
      · exact PreservesX2.pure _
      · exact PreservesX2.pure _
      · exact PreservesX2.pure _
      · apply PreservesX2.bind
        · exact preservesX2_highestPriorityAlignmentOrAccessFault _ _
        · intro _
          exact PreservesX2.pure _

theorem preservesX2_mem_write_ea (address : physaddr) (width : Nat) :
    PreservesX2 (mem_write_ea address width false false false) := by
  intro state
  simp [mem_write_ea, write_kind_of_flags, write_ram_ea, EStateM.bind,
    EStateM.pure, EStateM.instMonad]

theorem preservesX2_rX_bits (source : regidx) : PreservesX2 (rX_bits source) := by
  intro state
  cases hRead : (rX_bits source).run state with
  | error error afterRead =>
    change rX_bits source state = .error error afterRead at hRead
    have hState := rX_bits_state_projection state source
    change (match rX_bits source state with
      | .ok _ state' => state'
      | .error _ state' => state') = state at hState
    have afterReadEq : afterRead = state := by
      simpa only [hRead] using hState
    subst afterRead
    simp only [hRead]
  | ok value afterRead =>
    change rX_bits source state = .ok value afterRead at hRead
    have hState := rX_bits_state_projection state source
    change (match rX_bits source state with
      | .ok _ state' => state'
      | .error _ state' => state') = state at hState
    have afterReadEq : afterRead = state := by
      simpa only [hRead] using hState
    subst afterRead
    simp only [hRead]

theorem preservesX2_currentlyEnabled_Zicsr :
    PreservesX2 (currentlyEnabled extension.Ext_Zicsr) := by
  simp only [currentlyEnabled.eq_61]
  exact PreservesX2.pure _

theorem preservesX2_currentlyEnabled_S :
    PreservesX2 (currentlyEnabled extension.Ext_S) := by
  rw [currentlyEnabled.eq_20]
  apply PreservesX2.bind
  · exact preservesX2_readReg misa
  · intro misaBits
    apply PreservesX2.bind
    · exact preservesX2_currentlyEnabled_Zicsr
    · intro zicsr
      exact PreservesX2.pure _

theorem preservesX2_currentlyEnabled_Sstc :
    PreservesX2 (currentlyEnabled extension.Ext_Sstc) := by
  simpa only [PreservesX2, PreservesStackPointer] using
    currentlyEnabled_sstc_preserves_stack_pointer

theorem preservesX2_effectivePrivilege (access : MemoryAccessType mem_payload)
    (mstatus : BitVec 64) (privilege : Privilege) :
    PreservesX2 (effectivePrivilege access mstatus privilege) := by
  unfold effectivePrivilege
  exact PreservesX2.ite _ (privLevel_bits_forwards (_get_Mstatus_MPP mstatus, 0#1))
    (EStateM.pure privilege) (preservesX2_privLevel_bits_forwards _)
    (PreservesX2.pure _)

theorem preservesX2_is_pmm_applicable (access : MemoryAccessType mem_payload)
    (privilege : Privilege) : PreservesX2 (is_pmm_applicable access privilege) := by
  unfold is_pmm_applicable
  apply PreservesX2.bind
  · exact preservesX2_readReg mstatus
  · intro mstatusBits
    exact PreservesX2.pure _

theorem preservesX2_read_senvcfg : PreservesX2 (read_senvcfg ()) := by
  unfold read_senvcfg
  apply PreservesX2.bind
  · exact preservesX2_readReg senvcfg
  · intro senvcfgFirst
    apply PreservesX2.bind
    · exact preservesX2_readReg menvcfg
    · intro menvcfgBits
      apply PreservesX2.bind
      · exact preservesX2_readReg senvcfg
      · intro senvcfgSecond
        exact PreservesX2.pure _

theorem preservesX2_internal_error (file : String) (line : Int) (message : String) :
    PreservesX2 (internal_error file line message : SailM α) := by
  unfold internal_error Sail.sailThrow PreSail.sailThrow
  exact PreservesX2.throw _

theorem preservesX2_get_pmm (privilege : Privilege) : PreservesX2 (get_pmm privilege) := by
  cases privilege <;> unfold get_pmm
  · apply PreservesX2.bind
    · exact preservesX2_currentlyEnabled_S
    · intro enabled
      apply PreservesX2.ite
      · exact PreservesX2.bind (read_senvcfg ())
          (fun senvcfgBits => EStateM.pure (pmm_mode_backwards (_get_SEnvcfg_PMM senvcfgBits)))
          preservesX2_read_senvcfg (fun _ => PreservesX2.pure _)
      · exact PreservesX2.bind (readReg menvcfg)
          (fun menvcfgBits => EStateM.pure (pmm_mode_backwards (_get_MEnvcfg_PMM menvcfgBits)))
          (preservesX2_readReg menvcfg) (fun _ => PreservesX2.pure _)
  · exact preservesX2_internal_error _ _ _
  · apply PreservesX2.bind
    · exact preservesX2_readReg menvcfg
    · intro menvcfgBits
      exact PreservesX2.pure _
  · exact preservesX2_internal_error _ _ _
  · apply PreservesX2.bind
    · exact preservesX2_readReg mseccfg
    · intro mseccfgBits
      exact PreservesX2.pure _

theorem preservesX2_pmm_length (pmm : PointerMaskingMode) :
    PreservesX2 (match pmm with
    | .PMM_Disabled => EStateM.pure 0
    | .PMM_PMLEN_7 => EStateM.pure 7
    | .PMM_PMLEN_16 => EStateM.pure 16
    | .PMM_Reserved =>
      (internal_error "extensions/pointer_masking/pm_utils.sail" 32
        "Invalid pointer masking mode" : SailM Unit) >>= fun (_ : Unit) => EStateM.pure 0) := by
  cases pmm
  · exact PreservesX2.pure _
  · exact PreservesX2.bind
      (internal_error "extensions/pointer_masking/pm_utils.sail" 32
        "Invalid pointer masking mode")
      (fun _ => EStateM.pure 0)
      (preservesX2_internal_error _ _ _) (fun _ => PreservesX2.pure _)
  · exact PreservesX2.pure _
  · exact PreservesX2.pure _

theorem preservesX2_get_pmlen (access : MemoryAccessType mem_payload)
    (privilege : Privilege) : PreservesX2 (get_pmlen access privilege) := by
  unfold get_pmlen
  apply PreservesX2.bind
  · exact preservesX2_is_pmm_applicable access privilege
  · intro applicable
    apply PreservesX2.ite
    · apply PreservesX2.bind
      · exact preservesX2_get_pmm privilege
      · intro pmm
        cases pmm
        · exact PreservesX2.pure _
        · apply PreservesX2.bind
          · exact preservesX2_internal_error _ _ _
          · intro _
            exact PreservesX2.pure _
        · exact PreservesX2.pure _
        · exact PreservesX2.pure _
    · exact PreservesX2.pure _

theorem preservesX2_architecture_bits_backwards (bits : BitVec 2) :
    PreservesX2 (architecture_bits_backwards bits) := by
  have bitCases : bits.toNat = 0 ∨ bits.toNat = 1 ∨ bits.toNat = 2 ∨ bits.toNat = 3 := by
    omega
  rcases bitCases with hBits | hBits | hBits | hBits
  all_goals
    have bitsValue : bits = BitVec.ofNat 2 bits.toNat := by
      rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
      omega
    rw [bitsValue]
    simp [architecture_bits_backwards, hBits, internal_error, Sail.sailThrow,
      PreSail.sailThrow, EStateM.instMonad]
    all_goals first | exact PreservesX2.pure _ | exact PreservesX2.throw _

theorem preservesX2_architecture_supervisor :
    PreservesX2 (architecture Privilege.Supervisor) := by
  rw [architecture.eq_2]
  apply PreservesX2.bind
  · apply PreservesX2.bind
    · exact preservesX2_readReg mstatus
    · intro mstatusBits
      exact PreservesX2.pure _
  · intro satpArchitecture
    exact preservesX2_architecture_bits_backwards satpArchitecture

theorem preservesX2_translation_mbits (architecture : Architecture) :
    PreservesX2 (match architecture with
    | .RV64 => do
      PreSail.assert (LeanRV64DExecutable.Functions.xlen ≥b 64) "sys/vmem.sail:254.25-254.26"
      let satpBits ← readReg satp
      EStateM.pure (_get_Satp64_Mode (Mk_Satp64 satpBits))
    | .RV32 => do
      let satpBits ← readReg satp
      EStateM.pure
        (0b000#3 ++ (_get_Satp32_Mode (Mk_Satp32 (Sail.BitVec.extractLsb satpBits 31 0))))
    | .RV128 => internal_error "sys/vmem.sail" 258 "RV128 not supported") := by
  cases architecture
  · apply PreservesX2.bind
    · exact preservesX2_readReg satp
    · intro satpBits
      exact PreservesX2.pure _
  · apply PreservesX2.bind
    · exact preservesX2_assert _ _
    · intro _
      apply PreservesX2.bind
      · exact preservesX2_readReg satp
      · intro satpBits
        exact PreservesX2.pure _
  · exact preservesX2_internal_error _ _ _

theorem preservesX2_satp_mode_result (architecture : Architecture) (bits : satp_mode) :
    PreservesX2 (match satpMode_of_bits architecture bits with
    | .some mode => EStateM.pure mode
    | none => internal_error "sys/vmem.sail" 263 "invalid translation mode in satp") := by
  cases hMode : satpMode_of_bits architecture bits
  · simpa [hMode] using
      (preservesX2_internal_error "sys/vmem.sail" 263 "invalid translation mode in satp")
  · simpa [hMode] using (PreservesX2.pure _)

theorem preservesX2_translationMode (privilege : Privilege) :
    PreservesX2 (translationMode privilege) := by
  unfold translationMode
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · apply PreservesX2.bind
    · exact preservesX2_architecture_supervisor
    · intro architecture
      apply PreservesX2.bind
      · exact preservesX2_translation_mbits architecture
      · intro bits
        exact preservesX2_satp_mode_result architecture bits

theorem preservesX2_transform_effective_address (address : virtaddr)
    (access : MemoryAccessType mem_payload) :
    PreservesX2 (transform_effective_address address access) := by
  unfold transform_effective_address
  apply PreservesX2.bind
  · exact preservesX2_readReg mstatus
  · intro mstatusBits
    apply PreservesX2.bind
    · exact preservesX2_readReg cur_privilege
    · intro privilege
      apply PreservesX2.bind
      · exact preservesX2_effectivePrivilege access mstatusBits privilege
      · intro effectivePrivilege
        apply PreservesX2.bind
        · exact preservesX2_get_pmlen access effectivePrivilege
        · intro pmlen
          apply PreservesX2.bind
          · exact preservesX2_translationMode effectivePrivilege
          · intro mode
            exact PreservesX2.ite (mode == SATPMode.Bare)
              (EStateM.pure (pm_transform_PA address pmlen.toNat))
              (EStateM.pure (pm_transform_VA address pmlen.toNat))
              (PreservesX2.pure _) (PreservesX2.pure _)

theorem preservesX2_ext_data_get_addr (base : regidx) (offset : BitVec 64)
    (access : MemoryAccessType mem_payload) (width : Nat) :
    PreservesX2 (ext_data_get_addr base offset access width) := by
  unfold ext_data_get_addr
  apply PreservesX2.bind
  · exact preservesX2_rX_bits base
  · intro bits
    exact PreservesX2.pure _

theorem preservesX2_get_transformed_data_addr (base : regidx) (offset : BitVec 64)
    (access : MemoryAccessType mem_payload) (width : Nat) :
    PreservesX2 (get_transformed_data_addr base offset access width) := by
  unfold get_transformed_data_addr
  apply PreservesX2.bind
  · exact preservesX2_ext_data_get_addr base offset access width
  · intro result
    cases result with
    | Ext_DataAddr_Error error => exact PreservesX2.pure _
    | Ext_DataAddr_OK address =>
      apply PreservesX2.bind
      · exact preservesX2_transform_effective_address address access
      · intro transformed
        exact PreservesX2.pure _

theorem preservesX2_external_seip :
    PreservesX2 (do
      let supervisorEnabled ← currentlyEnabled extension.Ext_S
      if supervisorEnabled then readReg sig_seip else pure 0#1) := by
  apply PreservesX2.bind
  · exact preservesX2_currentlyEnabled_S
  · intro supervisorEnabled
    apply PreservesX2.ite
    · exact preservesX2_readReg sig_seip
    · exact PreservesX2.pure _

theorem preservesX2_external_interrupts_pending :
    PreservesX2 (external_interrupts_pending ()) := by
  unfold external_interrupts_pending
  apply PreservesX2.bind
  · exact preservesX2_readReg sig_meip
  · intro meip
    apply PreservesX2.bind
    · exact preservesX2_external_seip
    · intro seip
      exact PreservesX2.pure _

theorem preservesX2_read_mip (readType : XipReadType) :
    PreservesX2 (read_mip readType) := by
  cases readType
  · unfold read_mip
    apply PreservesX2.bind
    · exact preservesX2_readReg mip
    · intro mipBits
      apply PreservesX2.bind
      · exact preservesX2_external_interrupts_pending
      · intro externalBits
        exact PreservesX2.pure _
  · unfold read_mip
    exact preservesX2_readReg mip

theorem preservesX2_csr_name_map_backwards_mip :
    PreservesX2 (csr_name_map_backwards "mip") := by
  exact PreservesX2.pure _

theorem preservesX2_csr_name_write_callback_mip (value : BitVec 64) :
    PreservesX2 (csr_name_write_callback "mip" value) := by
  unfold csr_name_write_callback
  apply PreservesX2.bind
  · exact preservesX2_csr_name_map_backwards_mip
  · intro _
    exact PreservesX2.pure _

theorem preservesX2_clint_postlude (oldMip : BitVec 64) (mipWasWritten : Bool) :
    PreservesX2 (do
      pure ()
      let currentMip ← Sail.readReg mip
      if (oldMip != currentMip || mipWasWritten) then do
        let mipValue ← read_mip XipReadType.IncludePlatformInterrupts
        csr_name_write_callback "mip" mipValue
      else pure ()) := by
  apply PreservesX2.bind
  · exact PreservesX2.pure _
  · intro _
    apply PreservesX2.bind
    · exact preservesX2_readReg mip
    · intro currentMip
      apply PreservesX2.ite
      · apply PreservesX2.bind
        · exact preservesX2_read_mip XipReadType.IncludePlatformInterrupts
        · intro mipValue
          exact preservesX2_csr_name_write_callback_mip mipValue
      · exact PreservesX2.pure _

theorem preservesX2_clint_dispatch (mipWasWritten : Bool) :
    PreservesX2 (clint_dispatch mipWasWritten) := by
  unfold clint_dispatch
  simp only [get_config_print_clint, Bool.false_eq_true, ↓reduceIte]
  apply PreservesX2.bind
  · exact preservesX2_readReg mip
  · intro oldMip
    apply PreservesX2.bind
    · exact preservesX2_readReg mip
    · intro mipForTimer
      apply PreservesX2.bind
      · exact preservesX2_readReg mtimecmp
      · intro timerCompare
        apply PreservesX2.bind
        · exact preservesX2_readReg mtime
        · intro time
          apply PreservesX2.bind
          · exact PreservesX2.writeReg mip _ (by decide)
          · intro _
            apply PreservesX2.bind
            · exact preservesX2_currentlyEnabled_Sstc
            · intro supervisorTimeCompare
              apply PreservesX2.bind
              · exact preservesX2_readReg menvcfg
              · intro environmentConfig
                apply PreservesX2.ite
                · apply PreservesX2.bind
                  · exact preservesX2_readReg mip
                  · intro mipForSupervisorTimer
                    apply PreservesX2.bind
                    · exact preservesX2_readReg stimecmp
                    · intro supervisorTimerCompare
                      apply PreservesX2.bind
                      · exact preservesX2_readReg mtime
                      · intro supervisorTime
                        apply PreservesX2.bind
                        · exact PreservesX2.writeReg mip _ (by decide)
                        · intro _
                          exact preservesX2_clint_postlude oldMip mipWasWritten
                · exact preservesX2_clint_postlude oldMip mipWasWritten

theorem preservesX2_read_then_write (written : Register)
    (update : RegisterType written → RegisterType written) (doesNotWriteX2 : x2 ≠ written) :
    PreservesX2 (readReg written >>= fun value => writeReg written (update value)) := by
  apply PreservesX2.bind
  · exact preservesX2_readReg written
  · intro value
    exact PreservesX2.writeReg written (update value) doesNotWriteX2

theorem preservesX2_then_clint_dispatch (initial : SailM α)
    (initialFrame : PreservesX2 initial) (mipWasWritten : Bool) :
    PreservesX2 (initial >>= fun _ => clint_dispatch mipWasWritten >>= fun _ =>
      (pure (Sail.Ok true) : SailM (Sail.Result Bool ExceptionType))) := by
  apply PreservesX2.bind
  · exact initialFrame
  · intro _
    apply PreservesX2.bind
    · exact preservesX2_clint_dispatch mipWasWritten
    · intro _
      exact PreservesX2.pure _

theorem preservesX2_after_clint_dispatch (mipWasWritten : Bool) :
    PreservesX2 (do
      clint_dispatch mipWasWritten
      pure (Sail.Ok true) : SailM (Sail.Result Bool ExceptionType)) := by
  apply PreservesX2.bind
  · exact preservesX2_clint_dispatch mipWasWritten
  · intro _
    exact PreservesX2.pure _

theorem preservesX2_clint_store (app_0 : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesX2 (clint_store app_0 width data) := by
  unfold clint_store
  simp only
  apply PreservesX2.ite
  · apply PreservesX2.bind
    · exact preservesX2_readReg mip
    · intro current
      apply PreservesX2.bind
      · exact PreservesX2.writeReg mip _ (by decide)
      · intro _
        exact preservesX2_after_clint_dispatch true
  · apply PreservesX2.ite
    · apply PreservesX2.bind
      · exact PreservesX2.writeReg mtimecmp _ (by decide)
      · intro _
        exact preservesX2_after_clint_dispatch false
    · apply PreservesX2.ite
      · apply PreservesX2.bind
        · exact preservesX2_readReg mtimecmp
        · intro current
          apply PreservesX2.bind
          · exact PreservesX2.writeReg mtimecmp _ (by decide)
          · intro _
            exact preservesX2_after_clint_dispatch false
      · apply PreservesX2.ite
        · apply PreservesX2.bind
          · exact preservesX2_readReg mtimecmp
          · intro current
            apply PreservesX2.bind
            · exact PreservesX2.writeReg mtimecmp _ (by decide)
            · intro _
              exact preservesX2_after_clint_dispatch false
        · apply PreservesX2.ite
          · apply PreservesX2.bind
            · exact PreservesX2.writeReg mtime _ (by decide)
            · intro _
              exact preservesX2_after_clint_dispatch false
          · apply PreservesX2.ite
            · apply PreservesX2.bind
              · exact preservesX2_readReg mtime
              · intro current
                apply PreservesX2.bind
                · exact PreservesX2.writeReg mtime _ (by decide)
                · intro _
                  exact preservesX2_after_clint_dispatch false
            · apply PreservesX2.ite
              · apply PreservesX2.bind
                · exact preservesX2_readReg mtime
                · intro current
                  apply PreservesX2.bind
                  · exact PreservesX2.writeReg mtime _ (by decide)
                  · intro _
                    exact preservesX2_after_clint_dispatch false
              · exact PreservesX2.pure _

theorem preservesX2_mip_callback_ok :
    PreservesX2 (read_mip XipReadType.IncludePlatformInterrupts >>= fun value =>
      csr_name_write_callback "mip" value >>= fun _ =>
        (pure (Sail.Ok true) : SailM (Sail.Result Bool ExceptionType))) := by
  apply PreservesX2.bind
  · exact preservesX2_read_mip XipReadType.IncludePlatformInterrupts
  · intro value
    apply PreservesX2.bind
    · exact preservesX2_csr_name_write_callback_mip value
    · intro _
      exact PreservesX2.pure _

end BinaryFv.RiscV
