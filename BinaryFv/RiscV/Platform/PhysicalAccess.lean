import BinaryFv.RiscV.Platform.Pmp

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open MemoryAccessType
open page_based_mem_type

/-- The two ordinary data-access permissions selected by generated `pmaCheck`. -/
inductive DataPmaAccess where
  | load | store

def DataPmaAccess.memoryAccess : DataPmaAccess → MemoryAccessType mem_payload
  | .load => Load mem_payload.Data
  | .store => Store mem_payload.Data

def DataPmaAccess.permitted : DataPmaAccess → PMA → Bool
  | .load => PMA.readable
  | .store => PMA.writable

/-- A PMA region containing the complete range grants the selected ordinary data access. -/
def DataPmaAllows (access : DataPmaAccess) (state : State) (address : BitVec 64)
    (width : Nat) : Prop :=
  ∃ (regions : List PMA_Region) (region : PMA_Region),
    state.regs.get? Register.pma_regions = some regions ∧
      matching_pma_region regions (physaddr.Physaddr address) width = some region ∧
        access.permitted region.attributes = true

/-- Compatibility name for ordinary data reads. -/
abbrev LoadPmaAllows := DataPmaAllows .load

/-- Compatibility name for ordinary data writes. -/
abbrev StorePmaAllows := DataPmaAllows .store

theorem dataPmaAllows_of_agree {access : DataPmaAccess} {before after : State}
    {address : BitVec 64} {width : Nat} (agree : Agree platformPreserved before after)
    (allowed : DataPmaAllows access before address width) :
    DataPmaAllows access after address width := by
  rcases allowed with ⟨regions, region, regionsRead, matching, permitted⟩
  exact ⟨regions, region, (platformPreserved_pmaRegions agree).trans regionsRead,
    matching, permitted⟩

theorem loadPmaAllows_of_agree {before after : State} {address : BitVec 64} {width : Nat}
    (agree : Agree platformPreserved before after)
    (allowed : LoadPmaAllows before address width) :
    LoadPmaAllows after address width :=
  dataPmaAllows_of_agree agree allowed

theorem storePmaAllows_of_agree {before after : State} {address : BitVec 64} {width : Nat}
    (agree : Agree platformPreserved before after)
    (allowed : StorePmaAllows before address width) :
    StorePmaAllows after address width :=
  dataPmaAllows_of_agree agree allowed

theorem pmaCheck_data_allowed (access : DataPmaAccess) (state : State)
    (address : BitVec 64) (width : Nat) (allowed : DataPmaAllows access state address width)
    (aligned : is_aligned_paddr (physaddr.Physaddr address) width = true) :
    Runs (pmaCheck (physaddr.Physaddr address) width access.memoryAccess PBMT_PMA false)
      state state none := by
  cases access with
  | load =>
    rcases allowed with ⟨regions, region, regionsRead, matching, permitted⟩
    change region.attributes.readable = true at permitted
    unfold Runs
    simp [DataPmaAccess.memoryAccess, pmaCheck, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, override_PMA, Sail.assert, PreSail.assert,
      regionsRead, matching, permitted, aligned]
  | store =>
    rcases allowed with ⟨regions, region, regionsRead, matching, permitted⟩
    change region.attributes.writable = true at permitted
    unfold Runs
    simp [DataPmaAccess.memoryAccess, pmaCheck, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, override_PMA, Sail.assert, PreSail.assert,
      regionsRead, matching, permitted, aligned]

theorem pmaCheck_load_allowed (state : State) (address : BitVec 64) (width : Nat)
    (allowed : LoadPmaAllows state address width)
    (aligned : is_aligned_paddr (physaddr.Physaddr address) width = true) :
    Runs (pmaCheck (physaddr.Physaddr address) width (Load mem_payload.Data) PBMT_PMA false)
      state state none :=
  pmaCheck_data_allowed .load state address width allowed aligned

theorem pmaCheck_store_allowed (state : State) (address : BitVec 64) (width : Nat)
    (allowed : StorePmaAllows state address width)
    (aligned : is_aligned_paddr (physaddr.Physaddr address) width = true) :
    Runs (pmaCheck (physaddr.Physaddr address) width (Store mem_payload.Data) PBMT_PMA false)
      state state none :=
  pmaCheck_data_allowed .store state address width allowed aligned

theorem phys_access_check_machine_data_allowed (access : DataPmaAccess)
    (state : State) (address : BitVec 64)
    (width : Nat) (pmpDisabled : FetchPmpDisabled state)
    (pmaAllowed : DataPmaAllows access state address width)
    (aligned : is_aligned_paddr (physaddr.Physaddr address) width = true) :
    Runs (phys_access_check access.memoryAccess .PBMT_PMA .Machine
      (physaddr.Physaddr address) width false) state state none := by
  have hPmp := pmpCheck_machine_of_disabled state (physaddr.Physaddr address) width
    access.memoryAccess pmpDisabled
  have hPma := pmaCheck_data_allowed access state address width pmaAllowed aligned
  unfold phys_access_check
  exact Runs.bind hPmp (Runs.bind hPma rfl)

theorem phys_access_check_machine_load_allowed (state : State) (address : BitVec 64)
    (width : Nat) (pmpDisabled : FetchPmpDisabled state)
    (pmaAllowed : LoadPmaAllows state address width)
    (aligned : is_aligned_paddr (physaddr.Physaddr address) width = true) :
    Runs (phys_access_check (Load mem_payload.Data) .PBMT_PMA .Machine
      (physaddr.Physaddr address) width false) state state none :=
  phys_access_check_machine_data_allowed .load state address width pmpDisabled pmaAllowed aligned

theorem phys_access_check_machine_store_allowed (state : State) (address : BitVec 64)
    (width : Nat) (pmpDisabled : FetchPmpDisabled state)
    (pmaAllowed : StorePmaAllows state address width)
    (aligned : is_aligned_paddr (physaddr.Physaddr address) width = true) :
    Runs (phys_access_check (Store mem_payload.Data) .PBMT_PMA .Machine
      (physaddr.Physaddr address) width false) state state none :=
  phys_access_check_machine_data_allowed .store state address width pmpDisabled pmaAllowed aligned

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
