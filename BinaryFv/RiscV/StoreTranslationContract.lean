import BinaryFv.RiscV.FetchContract

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType
open page_based_mem_type

/--
Machine-mode store-data access keeps its effective privilege when `mstatus.MPRV = 0`.

`effectivePrivilege` only redirects the effective privilege for non-fetch accesses when the
generated `MPRV` modify-privilege bit is set; with `MPRV = 0` the store retains the current
Machine privilege.
-/
private theorem effectivePrivilege_store_machine_run (state : State) (mstatusBits : BitVec 64)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1) :
    Runs (effectivePrivilege (MemoryAccessType.Store mem_payload.Data) mstatusBits .Machine)
      state state .Machine := by
  unfold Runs effectivePrivilege
  rw [mprvZero]
  rfl

/-- Machine-mode translation selects the generated Bare mode. -/
private theorem translationMode_machine_run (state : State) :
    Runs (translationMode .Machine) state state .Bare := by
  rfl

/-- A store-data access is not a generated shadow-stack access. -/
private theorem store_not_shadow_stack_run (state : State) :
    Runs (is_shadow_stack_access (MemoryAccessType.Store mem_payload.Data)) state state false := by
  rfl

/-- Generated Machine-mode store-data translation is the identity Bare translation. -/
theorem translateAddr_machine_store_run (state : State) (vaddr mstatusBits : BitVec 64)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1) :
    Runs (translateAddr (virtaddr.Virtaddr vaddr) (MemoryAccessType.Store mem_payload.Data))
      state state (.Ok (physaddr.Physaddr vaddr, .PBMT_PMA, init_ext_ptw)) := by
  have hMstatus : Runs (Sail.readReg mstatus) state state mstatusBits :=
    readReg_run state mstatus mstatusBits mstatusRead
  have hPrivilege : Runs (Sail.readReg cur_privilege) state state .Machine :=
    readReg_run state cur_privilege .Machine privilegeRead
  have hEffective : Runs (effectivePrivilege (MemoryAccessType.Store mem_payload.Data)
      mstatusBits .Machine) state state .Machine :=
    effectivePrivilege_store_machine_run state mstatusBits mprvZero
  have hMode : Runs (translationMode .Machine) state state .Bare :=
    translationMode_machine_run state
  have hShadow : Runs (is_shadow_stack_access (MemoryAccessType.Store mem_payload.Data))
      state state false :=
    store_not_shadow_stack_run state
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
    (action := effectivePrivilege (MemoryAccessType.Store mem_payload.Data) mstatusBits .Machine)
    (next := ?_)
    (before := state) (middle := state) (after := state) (value := .Machine)
    (result := (.Ok (physaddr.Physaddr vaddr, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hEffective ?_
  refine runsFetchSailMELift (action := translationMode .Machine) (next := ?_)
    (before := state) (middle := state) (after := state) (value := .Bare)
    (result := (.Ok (physaddr.Physaddr vaddr, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hMode ?_
  refine runsFetchSailMELift
    (action := is_shadow_stack_access (MemoryAccessType.Store mem_payload.Data)) (next := ?_)
    (before := state) (middle := state) (after := state) (value := false)
    (result := (.Ok (physaddr.Physaddr vaddr, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hShadow ?_
  have bareEq : ((SATPMode.Bare == SATPMode.Bare) : Bool) = true := rfl
  rw [bareEq]
  rfl

end BinaryFv.RiscV
