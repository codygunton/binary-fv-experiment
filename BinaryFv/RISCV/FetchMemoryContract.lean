import BinaryFv.RISCV.PhysicalAccessContract
import BinaryFv.RISCV.TranslationContract

namespace BinaryFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType
open page_based_mem_type

/-- The exact generated MMIO decision required to take the sparse-RAM fetch branch. -/
def FetchMemoryNoMMIO (state : State) (pc : BitVec 64) : Prop :=
  Runs (within_mmio_readable (physaddr.Physaddr pc) 4) state state false

private theorem runsExceptTLift {ε α β : Type} (action : SailM α)
    (next : α → ExceptT ε SailM β) (before middle after : State)
    (value : α) (result : Except ε β)
    (hAction : Runs action before middle value)
    (hNext : Runs (ExceptT.run (next value)) middle after result) :
    Runs (ExceptT.run (do
      let current ← liftM action
      next current)) before after result := by
  change Runs (ExceptT.run ((ExceptT.lift action) >>= next)) before after result
  have runEq : ExceptT.run ((ExceptT.lift action) >>= next) = (do
      let current ← action
      ExceptT.run (next current)) := by
    simp only [ExceptT.instMonad, Monad.toBind, ExceptT.bind, ExceptT.lift, ExceptT.mk,
      ExceptT.run, EStateM.instMonad]
    funext state
    cases hAction' : action state <;>
      simp [EStateM.bind, EStateM.map, ExceptT.bindCont, hAction']
  rw [runEq]
  exact Runs.bind hAction hNext

private theorem runsExceptTBind {ε α β : Type} (action : ExceptT ε SailM α)
    (next : α → ExceptT ε SailM β) (before middle after : State)
    (value : α) (result : Except ε β)
    (hAction : Runs (ExceptT.run action) before middle (.ok value))
    (hNext : Runs (ExceptT.run (next value)) middle after result) :
    Runs (ExceptT.run (action >>= next)) before after result := by
  have runEq : ExceptT.run (action >>= next) = (do
      let current ← ExceptT.run action
      match current with
      | .ok value => ExceptT.run (next value)
      | .error error => pure (.error error)) := by
    simp only [ExceptT.instMonad, Monad.toBind, ExceptT.bind, ExceptT.run, ExceptT.mk,
      EStateM.instMonad]
    rfl
  rw [runEq]
  exact Runs.bind hAction hNext

private theorem runsSailMERunOfOk {α : Type} (action : SailME α α)
    (before after : State) (result : α)
    (hAction : Runs (ExceptT.run action) before after (.ok result)) :
    Runs (Sail.SailME.run action) before after result := by
  unfold Runs at hAction
  unfold Runs Sail.SailME.run PreSail.PreSailME.run
  simp only [EStateM.instMonad]
  unfold EStateM.bind
  unfold EStateM.run at hAction ⊢
  dsimp
  rw [hAction]
  rfl

/-- The generated plain RAM four-byte read returns the sparse-memory fetch word. -/
theorem read_ram_plain_fetch_bytes_run (state : State) (pc : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (bytes : FetchBytesAt state pc byte0 byte1 byte2 byte3) :
    Runs (read_ram .Read_plain (physaddr.Physaddr pc) 4 false) state state
      (fetchWord byte0 byte1 byte2 byte3, ()) := by
  change (read_ram .Read_plain (physaddr.Physaddr pc) 4 false).run state =
    .ok (fetchWord byte0 byte1 byte2 byte3, ()) state
  unfold LeanRV64DExecutable.Functions.read_ram
  simp only [Sail.ConcurrencyInterfaceV1.sail_mem_read,
    PreSail.ConcurrencyInterfaceV1.sail_mem_read]
  simp only [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad,
    EStateM.instMonadExceptOfOfBacktrackable]
  rw [show (PreSail.readBytes 4 pc.toNat) state =
    .ok (fetchWord byte0 byte1 byte2 byte3, none) state from
      readBytes4_run state pc byte0 byte1 byte2 byte3 bytes]
  rfl

private theorem checked_mem_read_machine_instructionFetch_run (state : State) (pc : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (pmpDisabled : FetchPmpDisabled state) (pmaAllowed : FetchPmaAllows state pc)
    (aligned : is_aligned_paddr (physaddr.Physaddr pc) 4 = true)
    (noMMIO : FetchMemoryNoMMIO state pc)
    (bytes : FetchBytesAt state pc byte0 byte1 byte2 byte3) :
    Runs (checked_mem_read (InstructionFetch ()) .PBMT_PMA .Machine (physaddr.Physaddr pc) 4
      false false false false) state state (.Ok (fetchWord byte0 byte1 byte2 byte3, ())) := by
  have hPhysical : Runs
      (phys_access_check (InstructionFetch ()) .PBMT_PMA .Machine (physaddr.Physaddr pc) 4 false)
      state state none :=
    phys_access_check_machine_instructionFetch_allowed state pc pmpDisabled pmaAllowed aligned
  have hRam : Runs (read_ram .Read_plain (physaddr.Physaddr pc) 4 false) state state
      (fetchWord byte0 byte1 byte2 byte3, ()) :=
    read_ram_plain_fetch_bytes_run state pc byte0 byte1 byte2 byte3 bytes
  unfold FetchMemoryNoMMIO at noMMIO
  unfold checked_mem_read
  apply Runs.bind hPhysical
  apply Runs.bind noMMIO
  apply Runs.bind (by rfl)
  apply Runs.bind hRam
  rfl

private theorem mem_read_priv_meta_machine_instructionFetch_run (state : State) (pc : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (pmpDisabled : FetchPmpDisabled state) (pmaAllowed : FetchPmaAllows state pc)
    (aligned : is_aligned_paddr (physaddr.Physaddr pc) 4 = true)
    (noMMIO : FetchMemoryNoMMIO state pc)
    (bytes : FetchBytesAt state pc byte0 byte1 byte2 byte3) :
    Runs (mem_read_priv_meta (InstructionFetch ()) .PBMT_PMA .Machine (physaddr.Physaddr pc) 4
      false false false false) state state (.Ok (fetchWord byte0 byte1 byte2 byte3, ())) := by
  have hChecked : Runs
      (checked_mem_read (InstructionFetch ()) .PBMT_PMA .Machine (physaddr.Physaddr pc) 4
        false false false false)
      state state (.Ok (fetchWord byte0 byte1 byte2 byte3, ())) :=
    checked_mem_read_machine_instructionFetch_run state pc byte0 byte1 byte2 byte3 pmpDisabled
      pmaAllowed aligned noMMIO bytes
  unfold mem_read_priv_meta
  apply Runs.bind hChecked
  rfl

private theorem mem_read_priv_machine_instructionFetch_run (state : State) (pc : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (pmpDisabled : FetchPmpDisabled state) (pmaAllowed : FetchPmaAllows state pc)
    (aligned : is_aligned_paddr (physaddr.Physaddr pc) 4 = true)
    (noMMIO : FetchMemoryNoMMIO state pc)
    (bytes : FetchBytesAt state pc byte0 byte1 byte2 byte3) :
    Runs (mem_read_priv (InstructionFetch ()) .PBMT_PMA .Machine (physaddr.Physaddr pc) 4
      false false false) state state (.Ok (fetchWord byte0 byte1 byte2 byte3)) := by
  have hMeta : Runs
      (mem_read_priv_meta (InstructionFetch ()) .PBMT_PMA .Machine (physaddr.Physaddr pc) 4
        false false false false)
      state state (.Ok (fetchWord byte0 byte1 byte2 byte3, ())) :=
    mem_read_priv_meta_machine_instructionFetch_run state pc byte0 byte1 byte2 byte3 pmpDisabled
      pmaAllowed aligned noMMIO bytes
  unfold mem_read_priv
  apply Runs.bind hMeta
  rfl

private theorem effectivePrivilege_instructionFetch_machine_run (state : State)
    (mstatusBits : BitVec 64) :
    Runs (effectivePrivilege (InstructionFetch ()) mstatusBits .Machine) state state .Machine := by
  rfl

/-- Generated four-byte Machine instruction fetch reads the exact sparse-memory fetch word. -/
theorem mem_read_machine_instructionFetch_fetch_bytes_run (state : State)
    (pc mstatusBits : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some .Machine)
    (pmpDisabled : FetchPmpDisabled state) (pmaAllowed : FetchPmaAllows state pc)
    (aligned : is_aligned_paddr (physaddr.Physaddr pc) 4 = true)
    (noMMIO : FetchMemoryNoMMIO state pc)
    (bytes : FetchBytesAt state pc byte0 byte1 byte2 byte3) :
    Runs (mem_read (InstructionFetch ()) .PBMT_PMA (physaddr.Physaddr pc) 4 false false false)
      state state (.Ok (fetchWord byte0 byte1 byte2 byte3)) := by
  have hMstatus : Runs (Sail.readReg mstatus) state state mstatusBits :=
    readReg_run state mstatus mstatusBits mstatusRead
  have hPrivilege : Runs (Sail.readReg cur_privilege) state state .Machine :=
    readReg_run state cur_privilege .Machine privilegeRead
  have hEffective : Runs (effectivePrivilege (InstructionFetch ()) mstatusBits .Machine)
      state state .Machine :=
    effectivePrivilege_instructionFetch_machine_run state mstatusBits
  have hRead : Runs
      (mem_read_priv (InstructionFetch ()) .PBMT_PMA .Machine (physaddr.Physaddr pc) 4 false false
        false)
      state state (.Ok (fetchWord byte0 byte1 byte2 byte3)) :=
    mem_read_priv_machine_instructionFetch_run state pc byte0 byte1 byte2 byte3 pmpDisabled
      pmaAllowed aligned noMMIO bytes
  unfold mem_read
  apply Runs.bind hMstatus
  apply Runs.bind hPrivilege
  apply Runs.bind hEffective
  exact hRead

/-- Generated four-byte fetch composes Machine translation and sparse-memory physical fetch. -/
theorem fetch_bytes_machine_instructionFetch_fetch_word_run (state : State) (pc : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (platform : FetchBasePlatform state pc)
    (noMMIO : FetchMemoryNoMMIO state pc)
    (bytes : FetchBytesAt state pc byte0 byte1 byte2 byte3) :
    Runs (fetch_bytes pc pc 4) state state
      (.FetchBytes_Success (fetchWord byte0 byte1 byte2 byte3)) := by
  rcases platform with ⟨_, mstatusBits, _, _, mstatusRead, privilegeRead, _, _, _, aligned,
    pmpDisabled, pmaAllowed⟩
  have hTranslation : Runs (translateAddr (virtaddr.Virtaddr pc) (InstructionFetch ())) state state
      (.Ok (physaddr.Physaddr pc, .PBMT_PMA, init_ext_ptw)) :=
    translateAddr_machine_instructionFetch_run state pc mstatusBits mstatusRead privilegeRead
  have hRead : Runs
      (mem_read (InstructionFetch ()) .PBMT_PMA (physaddr.Physaddr pc) 4 false false false)
      state state (.Ok (fetchWord byte0 byte1 byte2 byte3)) :=
    mem_read_machine_instructionFetch_fetch_bytes_run state pc mstatusBits byte0 byte1 byte2 byte3
      mstatusRead privilegeRead pmpDisabled pmaAllowed aligned noMMIO bytes
  unfold fetch_bytes
  simp only [ext_fetch_check_pc]
  apply runsSailMERunOfOk
  refine runsExceptTBind (action := pure ()) (next := ?_)
    (before := state) (middle := state) (after := state)
    (value := ())
    (result := (.ok (FetchBytes_Result.FetchBytes_Success (fetchWord byte0 byte1 byte2 byte3)) :
      Except (Sail.Error exception ⊕ FetchBytes_Result 4) (FetchBytes_Result 4))) (by rfl) ?_
  refine runsExceptTBind (action := do
      let translated ← liftM (translateAddr (virtaddr.Virtaddr pc) (InstructionFetch ()))
      match translated with
      | .Err (error, _) => Sail.SailME.throw (.FetchBytes_Exception error)
      | .Ok (paddr, pbmt, _) => pure (paddr, pbmt)) (next := ?_)
    (before := state) (middle := state) (after := state)
    (value := (physaddr.Physaddr pc, .PBMT_PMA))
    (result := (.ok (FetchBytes_Result.FetchBytes_Success (fetchWord byte0 byte1 byte2 byte3)) :
      Except (Sail.Error exception ⊕ FetchBytes_Result 4) (FetchBytes_Result 4))) ?_ ?_
  · refine runsExceptTLift
      (action := translateAddr (virtaddr.Virtaddr pc) (InstructionFetch ())) (next := ?_)
      (before := state) (middle := state) (after := state)
      (value := (.Ok (physaddr.Physaddr pc, .PBMT_PMA, init_ext_ptw) :
        Sail.Result (physaddr × page_based_mem_type × Unit) (ExceptionType × Unit)))
      (result := (.ok (physaddr.Physaddr pc, .PBMT_PMA) :
        Except (Sail.Error exception ⊕ FetchBytes_Result 4) (physaddr × page_based_mem_type)))
      hTranslation ?_
    rfl
  · refine runsExceptTLift
      (action := mem_read (InstructionFetch ()) .PBMT_PMA (physaddr.Physaddr pc) 4 false false
        false)
      (next := ?_) (before := state) (middle := state) (after := state)
      (value := .Ok (fetchWord byte0 byte1 byte2 byte3))
      (result := (.ok (FetchBytes_Result.FetchBytes_Success (fetchWord byte0 byte1 byte2 byte3)) :
        Except (Sail.Error exception ⊕ FetchBytes_Result 4) (FetchBytes_Result 4))) hRead ?_
    rfl

end BinaryFv.RISCV
