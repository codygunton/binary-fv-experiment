import BinaryFv.RiscV.Platform.Pmp

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open MemoryAccessType
open page_based_mem_type

/-- A PMA region containing the complete load range grants ordinary data reads. -/
def LoadPmaAllows (state : State) (address : BitVec 64) (width : Nat) : Prop :=
  ∃ (regions : List PMA_Region) (region : PMA_Region),
    state.regs.get? Register.pma_regions = some regions ∧
      matching_pma_region regions (physaddr.Physaddr address) width = some region ∧
        region.attributes.readable = true

theorem loadPmaAllows_of_agree {before after : State} {address : BitVec 64} {width : Nat}
    (agree : Agree platformPreserved before after)
    (allowed : LoadPmaAllows before address width) :
    LoadPmaAllows after address width := by
  rcases allowed with ⟨regions, region, regionsRead, matching, readable⟩
  exact ⟨regions, region, (platformPreserved_pmaRegions agree).trans regionsRead,
    matching, readable⟩

theorem pmaCheck_load_allowed (state : State) (address : BitVec 64) (width : Nat)
    (allowed : LoadPmaAllows state address width)
    (aligned : is_aligned_paddr (physaddr.Physaddr address) width = true) :
    Runs (pmaCheck (physaddr.Physaddr address) width (Load mem_payload.Data) PBMT_PMA false)
      state state none := by
  rcases allowed with ⟨regions, region, regionsRead, matching, readable⟩
  unfold Runs
  simp [pmaCheck, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
    EStateM.instMonad, EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, LeanRV64DExecutable.Functions.not,
    override_PMA, Sail.assert, PreSail.assert, regionsRead, matching, readable, aligned]

theorem phys_access_check_machine_load_allowed (state : State) (address : BitVec 64)
    (width : Nat) (pmpDisabled : FetchPmpDisabled state)
    (pmaAllowed : LoadPmaAllows state address width)
    (aligned : is_aligned_paddr (physaddr.Physaddr address) width = true) :
    Runs (phys_access_check (Load mem_payload.Data) .PBMT_PMA .Machine
      (physaddr.Physaddr address) width false) state state none := by
  have hPmp := pmpCheck_machine_of_disabled state (physaddr.Physaddr address) width
    (Load mem_payload.Data) pmpDisabled
  have hPma := pmaCheck_load_allowed state address width pmaAllowed aligned
  unfold phys_access_check
  exact Runs.bind hPmp (Runs.bind hPma rfl)

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
