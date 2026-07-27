import BinaryFv.RiscV.Step.Hart
import BinaryFv.RiscV.Platform.NormalState

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

/--
The generated `Ext_Zca` gate, as a function of `misa` alone.

`currentlyEnabled Ext_Zca` is `hartSupports Ext_Zca && (currentlyEnabled Ext_C || not (hartSupports
Ext_C))`, and both `hartSupports` cases are configuration constants, so the whole gate collapses to
the `misa` C bit. That is why the `hzca` premise of the control-flow rules is discharged by a single
register read rather than by a platform predicate of its own: `misa` is in `platformPreserved`, so
agreement carries the read, and the read carries the run.
-/
theorem currentlyEnabledZca_run (state : State) (misaBits : BitVec 64)
    (misaRead : state.regs.get? misa = some misaBits) :
    Runs (currentlyEnabled Ext_Zca) state state (_get_Misa_C misaBits == 1#1) := by
  unfold Runs
  simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
    instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
    LeanRV64DExecutable.Functions.not, LeanRV64DExecutable.Functions.xlen, misaRead]

/-- **The `misa` read is load-bearing.** Without it the gate does not merely fail to be provable at
some value — it returns no value at all, because the generated read throws. -/
theorem not_currentlyEnabledZca_run_of_misa_absent (state : State) (enabled : Bool)
    (absent : state.regs.get? misa = none) :
    ¬ Runs (currentlyEnabled Ext_Zca) state state enabled := by
  intro run
  unfold Runs at run
  simp [currentlyEnabled, hartSupports, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
    EStateM.instMonad, EStateM.instMonadStateOf, instMonadStateOfMonadStateOf, getThe, absent,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw] at run

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
  have hZca : Runs (currentlyEnabled Ext_Zca) state state (_get_Misa_C misaBits == 1#1) :=
    currentlyEnabledZca_run state misaBits misaRead
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

/-! ## The base-fetch platform, split at the `PC` read

`FetchBasePlatform state pc` bundles ten facts, and exactly one of them — `state.regs.get? PC = some
pc` — says *where the machine is*. The other nine say what the machine is configured like, plus what
is true of the address `pc` as a number. That distinction is the whole content of this section: a
contract about a callee can carry the nine, and cannot carry the one, because a call moves `PC`.

`FetchBasePlatformOffPC` is those nine. It is not a weakening for its own sake: a transport lemma
that asks for the full bundle at the *entry* state is unusable at the exit, since its hypothesis
already asserts the entry state is at the exit pc. -/

/--
`FetchBasePlatform` with the `PC` register read removed.

Everything here is either a platform register (preserved across a call) or a fact about the address
`pc` as a number (independent of any state). Nothing here constrains where the machine currently is,
which is what makes it the right hypothesis for a state that has not arrived at `pc` yet.
-/
def FetchBasePlatformOffPC (state : State) (pc : BitVec 64) : Prop :=
  ∃ (misaBits mstatusBits : BitVec 64),
    state.regs.get? misa = some misaBits ∧
      state.regs.get? mstatus = some mstatusBits ∧
        state.regs.get? cur_privilege = some Privilege.Machine ∧
          Sail.BitVec.access pc 0 = 0#1 ∧
            Sail.BitVec.access pc 1 = 0#1 ∧
              is_aligned_vaddr (virtaddr.Virtaddr pc) 4 = true ∧
                is_aligned_paddr (physaddr.Physaddr pc) 4 = true ∧
                  FetchPmpDisabled state ∧ FetchPmaAllows state pc

/-- The split is exact: the bundle is the `PC` read and nothing else, plus the rest. -/
theorem fetchBasePlatform_iff {state : State} {pc : BitVec 64} :
    FetchBasePlatform state pc ↔
      state.regs.get? PC = some pc ∧ FetchBasePlatformOffPC state pc := by
  constructor
  · rintro ⟨misaBits, mstatusBits, pcRead, rest⟩
    exact ⟨pcRead, misaBits, mstatusBits, rest⟩
  · rintro ⟨pcRead, misaBits, mstatusBits, rest⟩
    exact ⟨misaBits, mstatusBits, pcRead, rest⟩

theorem FetchBasePlatform.offPC {state : State} {pc : BitVec 64}
    (h : FetchBasePlatform state pc) : FetchBasePlatformOffPC state pc :=
  (fetchBasePlatform_iff.mp h).2

theorem fetchBasePlatform_of_offPC {state : State} {pc : BitVec 64}
    (pcRead : state.regs.get? PC = some pc) (h : FetchBasePlatformOffPC state pc) :
    FetchBasePlatform state pc :=
  fetchBasePlatform_iff.mpr ⟨pcRead, h⟩

/-! ### Constructors

The predicates above are anonymous conjunctions, so `⟨…⟩` builds them and nothing records *what a
caller must supply*. These name it. Each is generic: the register values, the region table and the
alignment are parameters, because which values a particular machine holds is a target fact. -/

/-- The four alignment conjuncts follow from one arithmetic fact about the address.

`Sail.BitVec.access` is bit extraction and `is_aligned_*` is `tmod` against the width, so all four
are the same statement twice over; a caller should not have to discharge them separately. -/
theorem fetchAligned_of_mod_four {pc : BitVec 64} (aligned : pc.toNat % 4 = 0) :
    Sail.BitVec.access pc 0 = 0#1 ∧ Sail.BitVec.access pc 1 = 0#1 ∧
      is_aligned_vaddr (virtaddr.Virtaddr pc) 4 = true ∧
        is_aligned_paddr (physaddr.Physaddr pc) 4 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Sail.BitVec.access, BitVec.getElem_eq_testBit_toNat, Nat.testBit,
      show pc.toNat % 2 = 0 by omega]
  · simp [Sail.BitVec.access, BitVec.getElem_eq_testBit_toNat, Nat.testBit,
      show pc.toNat >>> 1 % 2 = 0 by omega]
  · simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, ← Int.ofNat_tmod,
      aligned]
    rfl
  · simp only [is_aligned_paddr, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, ← Int.ofNat_tmod,
      aligned]
    rfl

/-- `FetchPmaAllows` from the region table and the region that matches. Which table a machine holds,
and that it matches, is a target fact; that they are what the premise wants is not. -/
theorem fetchPmaAllows_of_region {state : State} {pc : BitVec 64} {regions : List PMA_Region}
    {region : PMA_Region} (regionsRead : state.regs.get? pma_regions = some regions)
    (matched : matching_pma_region regions (physaddr.Physaddr pc) 4 = some region)
    (executable : region.attributes.executable = true) : FetchPmaAllows state pc :=
  ⟨regions, region, regionsRead, matched, executable⟩

/-- `FetchPmpDisabled` is two of `NormalExecutionState`'s twelve pins. -/
theorem fetchPmpDisabled_of_normal {state : State} (normal : NormalExecutionState state) :
    FetchPmpDisabled state :=
  ⟨normal.2.2.2.2.2.2.1, normal.2.2.2.2.2.2.2.1⟩

/-- The off-`PC` platform from register reads and one alignment fact. -/
theorem fetchBasePlatformOffPC_of_reads {state : State} {pc misaBits mstatusBits : BitVec 64}
    (misaRead : state.regs.get? misa = some misaBits)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (aligned : pc.toNat % 4 = 0) (pmpDisabled : FetchPmpDisabled state)
    (pmaAllows : FetchPmaAllows state pc) : FetchBasePlatformOffPC state pc :=
  ⟨misaBits, mstatusBits, misaRead, mstatusRead, privilegeRead,
    (fetchAligned_of_mod_four aligned).1, (fetchAligned_of_mod_four aligned).2.1,
    (fetchAligned_of_mod_four aligned).2.2.1, (fetchAligned_of_mod_four aligned).2.2.2,
    pmpDisabled, pmaAllows⟩

/-- **What `NormalExecutionState` already buys.** Four of the nine off-`PC` conjuncts (`misa`
presence, `cur_privilege`, and both PMP tables) come straight out of it; a caller supplies only
`mstatus`, the alignment, and the PMA lookup. -/
theorem fetchBasePlatformOffPC_of_normal {state : State} {pc mstatusBits : BitVec 64}
    (normal : NormalExecutionState state)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits) (aligned : pc.toNat % 4 = 0)
    (pmaAllows : FetchPmaAllows state pc) : FetchBasePlatformOffPC state pc := by
  have misaClause := normal.2.2.2.2.2.2.2.2.2.2.2
  cases misaRead : state.regs.get? misa with
  | none => rw [misaRead] at misaClause; exact absurd misaClause (by simp)
  | some misaBits =>
    exact fetchBasePlatformOffPC_of_reads misaRead mstatusRead normal.2.1 aligned
      (fetchPmpDisabled_of_normal normal) pmaAllows

/-- `InterruptDisabled` from `NormalExecutionState` plus the two registers it does not pin.

`sig_meip` is asked for as presence rather than a value because the premise only needs the read to
succeed — `mie = 0` already kills the dispatch. -/
theorem interruptDisabled_of_normal {state : State} {mstatusBits : BitVec 64}
    (normal : NormalExecutionState state)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (meip : ∃ b : BitVec 1, state.regs.get? sig_meip = some b) : InterruptDisabled state := by
  obtain ⟨b, meipRead⟩ := meip
  have misaClause := normal.2.2.2.2.2.2.2.2.2.2.2
  cases misaRead : state.regs.get? misa with
  | none => rw [misaRead] at misaClause; exact absurd misaClause (by simp)
  | some misaBits =>
    exact ⟨misaBits, mstatusBits, 0, b, misaRead, normal.2.2.2.2.2.1, normal.2.2.2.2.1,
      normal.2.2.2.1, meipRead, mstatusRead⟩

/-! ## Transporting the retirement's platform premises across a call

`platformPreserved` (`Platform/NormalState.lean`) names the registers a callee owes its caller
unchanged. These lemmas are what that clause *buys*: each premise of `tryStepRetRetires` that is
a claim about platform registers, carried from a state where it is established to the exit state.

They are stated at the same `pc` where a pc appears, because the pc is not something a callee
preserves — it is supplied by the trace. `fetchBasePlatform_of_agree` therefore takes the exit pc
read as a separate hypothesis, which is exactly the split between what a contract can say and what
only the run can — **and takes `FetchBasePlatformOffPC` rather than `FetchBasePlatform` on the entry
side, so that split is real.** With the full bundle as the hypothesis the lemma was unusable at the
site it was written for: `FetchBasePlatform before pc` already asserts `before.regs.get? PC = some
pc`, so the only `before` admitting it is one already sitting on the exit, where `Agree` is
reflexivity and the conclusion is the hypothesis. `Step/AbstractPremise.lean` instantiates the
narrowed form at a `before` that is provably *not* at `pc`, which the old form could not state. -/

/-- `FetchPmpDisabled` reads the two PMP tables, both preserved. -/
theorem fetchPmpDisabled_of_agree {before after : State}
    (agree : Agree platformPreserved before after) (h : FetchPmpDisabled before) :
    FetchPmpDisabled after :=
  ⟨(agree pmpcfg_n (by simp [platformPreserved])).trans h.1,
    (agree pmpaddr_n (by simp [platformPreserved])).trans h.2⟩

/-- `FetchPmaAllows` needs `pma_regions` **at its value** — the premise evaluates
`matching_pma_region` on the list — which is why the clause is agreement rather than presence. -/
theorem fetchPmaAllows_of_agree {before after : State} {pc : BitVec 64}
    (agree : Agree platformPreserved before after) (h : FetchPmaAllows before pc) :
    FetchPmaAllows after pc := by
  obtain ⟨regions, region, regionsRead, matched, executable⟩ := h
  exact ⟨regions, region, (platformPreserved_pmaRegions agree).trans regionsRead, matched,
    executable⟩

/-- `InterruptDisabled` reads `misa`, `mip`, `mie`, `mideleg` — the four `NormalExecutionState`
already pins — plus `sig_meip` and `mstatus`, which it does not. All six are preserved. -/
theorem interruptDisabled_of_agree {before after : State}
    (agree : Agree platformPreserved before after) (h : InterruptDisabled before) :
    InterruptDisabled after := by
  obtain ⟨misaBits, mstatusBits, mipBits, meip, misaRead, mipRead, mieRead, midelegRead, meipRead,
    mstatusRead⟩ := h
  exact ⟨misaBits, mstatusBits, mipBits, meip,
    (agree misa (by simp [platformPreserved])).trans misaRead,
    (agree mip (by simp [platformPreserved])).trans mipRead,
    (agree mie (by simp [platformPreserved])).trans mieRead,
    (agree mideleg (by simp [platformPreserved])).trans midelegRead,
    (platformPreserved_sigMeip agree).trans meipRead,
    (platformPreserved_mstatus agree).trans mstatusRead⟩

/-- Every off-`PC` conjunct is preserved: three register reads, the two PMP tables, the PMA table at
its value, and four facts about `pc` that mention no state at all. -/
theorem fetchBasePlatformOffPC_of_agree {before after : State} {pc : BitVec 64}
    (agree : Agree platformPreserved before after) (h : FetchBasePlatformOffPC before pc) :
    FetchBasePlatformOffPC after pc := by
  obtain ⟨misaBits, mstatusBits, misaRead, mstatusRead, privilegeRead, pcLow0, pcLow1,
    alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩ := h
  exact ⟨misaBits, mstatusBits,
    (agree misa (by simp [platformPreserved])).trans misaRead,
    (platformPreserved_mstatus agree).trans mstatusRead,
    (agree cur_privilege (by simp [platformPreserved])).trans privilegeRead,
    pcLow0, pcLow1, alignedVaddr, alignedPaddr,
    fetchPmpDisabled_of_agree agree pmpDisabled, fetchPmaAllows_of_agree agree pmaAllows⟩

/-- The whole base-fetch platform at the exit, from the preserved configuration at the entry and the
exit pc the trace lands on. The entry side is the off-`PC` bundle, so `before` is free to be anywhere
— which is the only way this applies across a call. -/
theorem fetchBasePlatform_of_agree {before after : State} {pc : BitVec 64}
    (agree : Agree platformPreserved before after) (landed : after.regs.get? PC = some pc)
    (h : FetchBasePlatformOffPC before pc) : FetchBasePlatform after pc :=
  fetchBasePlatform_of_offPC landed (fetchBasePlatformOffPC_of_agree agree h)

end BinaryFv.RiscV
