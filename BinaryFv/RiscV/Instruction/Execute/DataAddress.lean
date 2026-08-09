import BinaryFv.RiscV.Instruction.Execute.Store
import BinaryFv.RiscV.Platform.PhysicalAccess

namespace BinaryFv.RiscV

open PreSail LeanRV64DExecutable.Functions Register MemoryAccessType mem_payload

/-- Under the configured Machine-mode, Bare-translation, pointer-masking-disabled setup, an
ordinary data effective address is its base register plus its signed offset. -/
theorem get_transformed_data_addr_machine_data_run (access : DataPmaAccess) (state : State)
    (rs : regidx) (width : Nat) (base offset mstatusBits mseccfgBits : BitVec 64)
    (baseRead : Runs (rX_bits rs) state state base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled) :
    Runs (get_transformed_data_addr rs offset access.memoryAccess width) state state
      (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + offset))) := by
  have address : Runs (ext_data_get_addr rs offset access.memoryAccess width) state state
      (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + offset))) := by
    unfold ext_data_get_addr
    exact Runs.bind baseRead rfl
  unfold get_transformed_data_addr
  refine Runs.bind address ?_
  have transformed : Runs (transform_effective_address (virtaddr.Virtaddr (base + offset))
      access.memoryAccess) state state (virtaddr.Virtaddr (base + offset)) := by
    have machineEq : (Privilege.Machine == Privilege.Machine) = true := rfl
    have bareEq : (SATPMode.Bare == SATPMode.Bare) = true := rfl
    have pointerMaskingBase :
        (access.memoryAccess != InstructionFetch ()) = true ∧
          (access.memoryAccess != Load PageTableEntry) = true ∧
            (access.memoryAccess != Store PageTableEntry) = true ∧
              LeanRV64DExecutable.Functions.xlen = 64 := by
      cases access <;> exact ⟨by decide, by decide, by decide, rfl⟩
    cases access <;> simp only [DataPmaAccess.memoryAccess] at pointerMaskingBase ⊢
    all_goals unfold Runs transform_effective_address get_pmlen is_pmm_applicable get_pmm translationMode
    all_goals simp [PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable,
      MonadState.get, MonadStateOf.get, getThe, mstatusRead, privilegeRead, mseccfgRead, mprvZero,
      pmmDisabled, pointerMaskingBase, machineEq, bareEq, LeanRV64DExecutable.Functions.xlen,
      effectivePrivilege, pm_transform_PA]
    all_goals
      change zero_extend (Sail.BitVec.extractLsb (base + offset) 63 0) = base + offset
      unfold zero_extend Sail.BitVec.zeroExtend
      rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq, extractLsb_full]
  exact Runs.bind transformed rfl

end BinaryFv.RiscV
