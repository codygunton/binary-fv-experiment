import BinaryFv.RiscV.Platform.Fetch

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType
open page_based_mem_type

/-- Machine-mode instruction fetch keeps its effective privilege. -/
private theorem effectivePrivilege_instructionFetch_machine_run (state : State)
    (mstatusBits : BitVec 64) :
    Runs (effectivePrivilege (InstructionFetch ()) mstatusBits .Machine) state state .Machine := by
  rfl

/-- Machine-mode translation selects the generated Bare mode. -/
private theorem translationMode_machine_run (state : State) :
    Runs (translationMode .Machine) state state .Bare := by
  rfl

/-- Instruction fetch is not a generated shadow-stack access. -/
private theorem instructionFetch_not_shadow_stack_run (state : State) :
    Runs (is_shadow_stack_access (InstructionFetch ())) state state false := by
  rfl

/-- Generated Machine-mode instruction translation is the identity Bare translation.
(exec-spike repair: the specialised `translateAddr` (ZESU-SPEC R I1) reads no register; the
register premises are kept for the callers and are unused.) -/
theorem translateAddr_machine_instructionFetch_run (state : State) (pc mstatusBits : BitVec 64)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some .Machine) :
    Runs (translateAddr (virtaddr.Virtaddr pc) (InstructionFetch ())) state state
      (.Ok (physaddr.Physaddr pc, .PBMT_PMA, init_ext_ptw)) := by
  rfl

end BinaryFv.RiscV
