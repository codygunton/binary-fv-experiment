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

/-- Generated Machine-mode instruction translation is the identity Bare translation. -/
theorem translateAddr_machine_instructionFetch_run (state : State) (pc mstatusBits : BitVec 64)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some .Machine) :
    Runs (translateAddr (virtaddr.Virtaddr pc) (InstructionFetch ())) state state
      (.Ok (physaddr.Physaddr pc, .PBMT_PMA, init_ext_ptw)) := by
  have hMstatus : Runs (Sail.readReg mstatus) state state mstatusBits :=
    readReg_run state mstatus mstatusBits mstatusRead
  have hPrivilege : Runs (Sail.readReg cur_privilege) state state .Machine :=
    readReg_run state cur_privilege .Machine privilegeRead
  have hEffective : Runs (effectivePrivilege (InstructionFetch ()) mstatusBits .Machine)
      state state .Machine :=
    effectivePrivilege_instructionFetch_machine_run state mstatusBits
  have hMode : Runs (translationMode .Machine) state state .Bare :=
    translationMode_machine_run state
  have hShadow : Runs (is_shadow_stack_access (InstructionFetch ())) state state false :=
    instructionFetch_not_shadow_stack_run state
  unfold translateAddr
  refine runsFetchSailMELift (action := Sail.readReg mstatus) (next := ?_)
    (before := state) (middle := state) (after := state) (value := mstatusBits)
    (result := (.Ok (physaddr.Physaddr pc, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hMstatus ?_
  refine runsFetchSailMELift (action := Sail.readReg cur_privilege) (next := ?_)
    (before := state) (middle := state) (after := state) (value := .Machine)
    (result := (.Ok (physaddr.Physaddr pc, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hPrivilege ?_
  refine runsFetchSailMELift
    (action := effectivePrivilege (InstructionFetch ()) mstatusBits .Machine) (next := ?_)
    (before := state) (middle := state) (after := state) (value := .Machine)
    (result := (.Ok (physaddr.Physaddr pc, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hEffective ?_
  refine runsFetchSailMELift (action := translationMode .Machine) (next := ?_)
    (before := state) (middle := state) (after := state) (value := .Bare)
    (result := (.Ok (physaddr.Physaddr pc, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hMode ?_
  refine runsFetchSailMELift (action := is_shadow_stack_access (InstructionFetch ())) (next := ?_)
    (before := state) (middle := state) (after := state) (value := false)
    (result := (.Ok (physaddr.Physaddr pc, .PBMT_PMA, init_ext_ptw) :
      Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit))) hShadow ?_
  have bareEq : ((SATPMode.Bare == SATPMode.Bare) : Bool) = true := rfl
  rw [bareEq]
  rfl

end BinaryFv.RiscV
