import BinaryFv.RiscV.HartContract

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType
open page_based_mem_type
open extension
open FetchBytes_Result
open FetchResult

/-- The little-endian base instruction word assembled by the generated sparse-memory reader. -/
def fetchWord (byte0 byte1 byte2 byte3 : BitVec 8) : BitVec 32 :=
  byte3 ++ byte2 ++ byte1 ++ byte0

/-- The four sparse-memory bytes consumed by the generated four-byte fetch path. -/
def FetchBytesAt (state : State) (pc : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8) : Prop :=
  state.mem.get? pc.toNat = some byte0 ∧
    state.mem.get? (pc.toNat + 1) = some byte1 ∧
      state.mem.get? (pc.toNat + 2) = some byte2 ∧
        state.mem.get? (pc.toNat + 3) = some byte3

/-- The low encoding bits which make a four-byte fetched word a base instruction. -/
def BaseInstructionEncoding (byte0 : BitVec 8) : Prop :=
  Sail.BitVec.extractLsb byte0 1 0 = 0b11#2

/-- A generated PMA lookup grants an executable four-byte instruction fetch at `pc`. -/
def FetchPmaAllows (state : State) (pc : BitVec 64) : Prop :=
  ∃ (regions : List PMA_Region) (region : PMA_Region),
    state.regs.get? pma_regions = some regions ∧
      matching_pma_region regions (physaddr.Physaddr pc) 4 = some region ∧
        region.attributes.executable = true

/--
The direct-machine PMP register state: all configured entries are off.

`PmpContract` proves the generated Machine-mode `pmpCheck` loop from this state. The broader
`FetchBytesBaseContract` remains explicit for the remaining generated translation and memory path.
-/
def FetchPmpDisabled (state : State) : Prop :=
  state.regs.get? pmpcfg_n = some (default : Vector (BitVec 8) 64) ∧
    state.regs.get? pmpaddr_n = some (default : Vector (BitVec 64) 64)

/-- State facts required by the generated direct Machine-mode base-fetch path. -/
def FetchBasePlatform (state : State) (pc : BitVec 64) : Prop :=
  ∃ (misaBits mstatusBits : BitVec 64),
    state.regs.get? PC = some pc ∧
      state.regs.get? misa = some misaBits ∧
        state.regs.get? mstatus = some mstatusBits ∧
          state.regs.get? cur_privilege = some Privilege.Machine ∧
            Sail.BitVec.access pc 0 = 0#1 ∧
              Sail.BitVec.access pc 1 = 0#1 ∧
                is_aligned_vaddr (virtaddr.Virtaddr pc) 4 = true ∧
                  is_aligned_paddr (physaddr.Physaddr pc) 4 = true ∧
                  FetchPmpDisabled state ∧ FetchPmaAllows state pc

theorem readBytes4_run (state : State) (pc : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (bytes : FetchBytesAt state pc byte0 byte1 byte2 byte3) :
    (PreSail.readBytes 4 pc.toNat : SailM (BitVec 32 × Option Bool)).run state =
      .ok (fetchWord byte0 byte1 byte2 byte3, none) state := by
  rcases bytes with ⟨byte0Read, byte1Read, byte2Read, byte3Read⟩
  have byte2Read' : state.mem.get? (pc.toNat + 1 + 1) = some byte2 := by
    simpa using byte2Read
  have byte3Read' : state.mem.get? (pc.toNat + 1 + 1 + 1) = some byte3 := by
    simpa using byte3Read
  have h1 : Runs (PreSail.readBytes 1 (pc.toNat + 1 + 1 + 1) :
      SailM (BitVec 8 × Option Bool)) state state (byte3, none) := by
    apply Runs.bind (readByte_run state (pc.toNat + 1 + 1 + 1) byte3 byte3Read')
    rfl
  have h2 : Runs (PreSail.readBytes 2 (pc.toNat + 1 + 1) :
      SailM (BitVec 16 × Option Bool)) state state (byte3 ++ byte2, none) := by
    apply Runs.bind (readByte_run state (pc.toNat + 1 + 1) byte2 byte2Read')
    apply Runs.bind h1
    rfl
  have h3 : Runs (PreSail.readBytes 3 (pc.toNat + 1) :
      SailM (BitVec 24 × Option Bool)) state state (byte3 ++ byte2 ++ byte1, none) := by
    apply Runs.bind (readByte_run state (pc.toNat + 1) byte1 byte1Read)
    apply Runs.bind h2
    rfl
  apply Runs.bind (readByte_run state pc.toNat byte0 byte0Read)
  apply Runs.bind h3
  rfl

theorem baseInstructionEncoding_notRVC (byte0 byte1 byte2 byte3 : BitVec 8)
    (base : BaseInstructionEncoding byte0) :
    isRVC (Sail.BitVec.extractLsb (fetchWord byte0 byte1 byte2 byte3) 15 0) = false := by
  simp only [BaseInstructionEncoding, fetchWord, isRVC, Sail.BitVec.extractLsb,
    LeanRV64DExecutable.Functions.not] at base ⊢
  bv_decide

theorem pmaCheck_fetch_allowed (state : State) (pc : BitVec 64)
    (allowed : FetchPmaAllows state pc)
    (aligned : is_aligned_paddr (physaddr.Physaddr pc) 4 = true) :
    Runs (pmaCheck (physaddr.Physaddr pc) 4 (InstructionFetch ()) PBMT_PMA false)
      state state none := by
  rcases allowed with ⟨regions, region, regionsRead, matching, executable⟩
  unfold Runs
  simp [pmaCheck, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
    EStateM.instMonad, EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, LeanRV64DExecutable.Functions.not,
    override_PMA, regionsRead, matching, executable, aligned]

theorem fetchExceptTRunLiftBind {α β : Type} (action : SailM α) (next : α → SailME β β) :
    ExceptT.run (do
      let current ← liftM action
      next current) = (do
        let current ← action
        ExceptT.run (next current)) := by
  change ExceptT.run ((ExceptT.lift action) >>= next) = _
  simp only [ExceptT.instMonad, Monad.toBind, ExceptT.bind, ExceptT.lift, ExceptT.mk,
    ExceptT.run, EStateM.instMonad]
  funext state
  cases hAction : action state <;>
    simp [EStateM.bind, EStateM.map, ExceptT.bindCont, hAction]

theorem fetchSailMERunLiftBind {α β : Type} (action : SailM α) (next : α → SailME β β) :
    Sail.SailME.run (do
      let current ← liftM action
      next current) = (do
        let current ← action
        Sail.SailME.run (next current)) := by
  unfold Sail.SailME.run PreSail.PreSailME.run
  rw [fetchExceptTRunLiftBind]
  funext state
  simp

theorem runsFetchSailMELift {α β : Type} (action : SailM α) (next : α → SailME β β)
    (before middle after : State) (value : α) (result : β)
    (hAction : Runs action before middle value)
    (hNext : Runs (Sail.SailME.run (next value)) middle after result) :
    Runs (Sail.SailME.run (do
      let current ← liftM action
      next current)) before after result := by
  rw [fetchSailMERunLiftBind]
  exact Runs.bind hAction hNext

/-- The lower generated memory/translation contract needed by the base-fetch selector. -/
def FetchBytesBaseContract (state : State) (pc : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8) : Prop :=
  Runs (fetch_bytes pc pc 4) state state
    (.FetchBytes_Success (fetchWord byte0 byte1 byte2 byte3))

/-- Lift a successful generated four-byte fetch through the generated `fetch` selector. -/
theorem fetch_base_of_fetchBytes (state : State) (pc : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (platform : FetchBasePlatform state pc)
    (base : BaseInstructionEncoding byte0)
    (fetchBytes : FetchBytesBaseContract state pc byte0 byte1 byte2 byte3) :
    Runs (fetch ()) state state (.F_Base (fetchWord byte0 byte1 byte2 byte3)) := by
  rcases platform with ⟨misaBits, mstatusBits, pcRead, misaRead, mstatusRead, privilegeRead,
    pcLow0, pcLow1, alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩
  change (fetch_bytes pc pc 4).run state =
    .ok (.FetchBytes_Success (fetchWord byte0 byte1 byte2 byte3)) state at fetchBytes
  have hFetchBytes : Runs (fetch_bytes pc pc 4) state state
      (.FetchBytes_Success (fetchWord byte0 byte1 byte2 byte3)) := fetchBytes
  have notRvc := baseInstructionEncoding_notRVC byte0 byte1 byte2 byte3 base
  have hReadPc : Runs (Sail.readReg PC) state state pc :=
    readReg_run state PC pc pcRead
  have hZca : Runs (currentlyEnabled Ext_Zca) state state (_get_Misa_C misaBits == 1#1) := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
      LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, misaRead]
  have hZiccif : Runs (currentlyEnabled Ext_Ziccif) state state true := by
    unfold Runs currentlyEnabled hartSupports
    rfl
  unfold fetch
  simp [get_config_rvfi, ext_fetch_check_pc]
  refine runsFetchSailMELift (action := Sail.readReg PC) (next := ?_)
    (before := state) (middle := state) (after := state) (value := pc)
    (result := FetchResult.F_Base (fetchWord byte0 byte1 byte2 byte3)) hReadPc ?_
  refine runsFetchSailMELift (action := Sail.readReg PC) (next := ?_)
    (before := state) (middle := state) (after := state) (value := pc)
    (result := FetchResult.F_Base (fetchWord byte0 byte1 byte2 byte3)) hReadPc ?_
  refine runsFetchSailMELift (action := Sail.readReg PC) (next := ?_)
    (before := state) (middle := state) (after := state) (value := pc)
    (result := FetchResult.F_Base (fetchWord byte0 byte1 byte2 byte3)) hReadPc ?_
  refine runsFetchSailMELift (action := Sail.readReg PC) (next := ?_)
    (before := state) (middle := state) (after := state) (value := pc)
    (result := FetchResult.F_Base (fetchWord byte0 byte1 byte2 byte3)) hReadPc ?_
  refine runsFetchSailMELift (action := currentlyEnabled Ext_Zca) (next := ?_)
    (before := state) (middle := state) (after := state) (value := (_get_Misa_C misaBits == 1#1))
    (result := FetchResult.F_Base (fetchWord byte0 byte1 byte2 byte3)) hZca ?_
  simp [pcLow0, pcLow1]
  refine runsFetchSailMELift (action := Sail.readReg PC) (next := ?_)
    (before := state) (middle := state) (after := state) (value := pc)
    (result := FetchResult.F_Base (fetchWord byte0 byte1 byte2 byte3)) hReadPc ?_
  refine runsFetchSailMELift (action := currentlyEnabled Ext_Ziccif) (next := ?_)
    (before := state) (middle := state) (after := state) (value := true)
    (result := FetchResult.F_Base (fetchWord byte0 byte1 byte2 byte3)) hZiccif ?_
  simp [alignedVaddr]
  refine runsFetchSailMELift (action := Sail.readReg PC) (next := ?_)
    (before := state) (middle := state) (after := state) (value := pc)
    (result := FetchResult.F_Base (fetchWord byte0 byte1 byte2 byte3)) hReadPc ?_
  refine runsFetchSailMELift (action := Sail.readReg PC) (next := ?_)
    (before := state) (middle := state) (after := state) (value := pc)
    (result := FetchResult.F_Base (fetchWord byte0 byte1 byte2 byte3)) hReadPc ?_
  refine runsFetchSailMELift (action := fetch_bytes pc pc 4) (next := ?_)
    (before := state) (middle := state) (after := state)
    (value := .FetchBytes_Success (fetchWord byte0 byte1 byte2 byte3))
    (result := FetchResult.F_Base (fetchWord byte0 byte1 byte2 byte3)) hFetchBytes ?_
  simp [notRvc]
  unfold Runs Sail.SailME.run PreSail.PreSailME.run
  simp
  rfl

end BinaryFv.RiscV
