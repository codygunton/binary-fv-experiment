import BinaryFv.RiscV.Platform.Pmp

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open MemoryAccessType
open page_based_mem_type

/-- Default Machine-mode PMP and executable PMA admit a generated four-byte fetch access. -/
theorem phys_access_check_machine_instructionFetch_allowed (state : State) (pc : BitVec 64)
    (pmpDisabled : FetchPmpDisabled state) (pmaAllowed : FetchPmaAllows state pc)
    (aligned : is_aligned_paddr (physaddr.Physaddr pc) 4 = true) :
    Runs (phys_access_check (InstructionFetch ()) .PBMT_PMA .Machine (physaddr.Physaddr pc) 4 false)
      state state none := by
  have hPmp : Runs (pmpCheck (physaddr.Physaddr pc) 4 (InstructionFetch ()) .Machine)
      state state none :=
    pmpCheck_machine_of_disabled state (physaddr.Physaddr pc) 4 (InstructionFetch ()) pmpDisabled
  have hPma : Runs (pmaCheck (physaddr.Physaddr pc) 4 (InstructionFetch ()) .PBMT_PMA false)
      state state none :=
    pmaCheck_fetch_allowed state pc pmaAllowed aligned
  unfold phys_access_check
  apply Runs.bind hPmp
  apply Runs.bind hPma
  rfl

end BinaryFv.RiscV
