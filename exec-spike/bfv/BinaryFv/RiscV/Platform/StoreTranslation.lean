import BinaryFv.RiscV.Platform.Fetch

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

/-- Generated Machine-mode store-data translation is the identity Bare translation.
(exec-spike repair: the specialised `translateAddr` (ZESU-SPEC R I1) reads no register; the
register premises are kept for the callers and are unused.) -/
theorem translateAddr_machine_store_run (state : State) (vaddr mstatusBits : BitVec 64)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1) :
    Runs (translateAddr (virtaddr.Virtaddr vaddr) (MemoryAccessType.Store mem_payload.Data))
      state state (.Ok (physaddr.Physaddr vaddr, .PBMT_PMA, init_ext_ptw)) := by
  rfl

end BinaryFv.RiscV
