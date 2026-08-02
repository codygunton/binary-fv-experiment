import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Accessors
import BinaryFv.Zesu.Elflings.GeneratedExtentReadability
import BinaryFv.RiscV.Step.AbstractPremise
import BinaryFv.RiscV.Step.Call

/-!
# The three sentinel attachments, assembled

`RiscV/Elfling/SentinelBridge.lean` turns an `EnteredFunctionTrace` into a `TraceToSentinel` given
three things it says outright it cannot know: the two avoidance conditions, and one `Runs (try_step
…)` for the `ret` that moves the pc from the exit address onto the sentinel. This module supplies all
three, at the three places the runner attaches them — the exported wrapper `zesu_decode_raw` and the
two exported accessors `zesu_raw_result` and `zesu_raw_error` — and it *proves* the `ret` rather than
assuming it.

## What is proved and what is still a hypothesis

Proved here, with no premise about machine execution:

* the `ret` retirement itself (`exitRetRetires`). Every premise of `tryStepRetRetires` is discharged
  from register reads at the state the exit is reached in, plus the pinned image's own bytes;
* the landing (`tryStepControlFlowAfterRetired_pc` at `Sail.BitVec.update sentinelWord 0 0#1 =
  sentinelWord`), so "the run returned to the sentinel" is a consequence of `ra`'s value, not an
  assumption about the pc;
* both avoidance conditions, from `Elfling.generated_execution_pcs_avoid_sentinel` /
  `generated_exit_pcs_avoid_sentinel`;
* which pc each attachment ends at — read off the generated exit inventory
  (`entry_function_instance_exit_is_its_return` and its two accessor analogues), never chosen.

Still hypotheses, and deliberately so:

* the `EnteredFunctionTrace` itself. That is the function instance's own contract obligation
  (`Contracts.routineObligation`), and nothing at this layer can produce one;
* `ExitPlatform` at the state the exit is reached in. This is the currency the contracts' exit
  clauses trade in — `Agree platformPreserved`, `RetiredCounterPresent`, `CodeIntact` — and
  `exitPlatform_of_agree` below is the one step from those to what the retirement wants.

## The three exit addresses are data, not choices

`FunctionTrace` halts at the *first* exit it reaches, so "the trace ends on the `ret`" is only a
definite description when the function instance has exactly one exit and it is a return. That is
false of 128 of the 141 generated function instances and is checked separately for each of these
three; nothing here is inherited from a general property of the program.

| attachment | entry | exit |
| --- | --- | --- |
| `zesu_decode_raw` | `0x102B0` (66224) | `0x10378` (66424) |
| `zesu_raw_error` | `0x13780` (79744) | `0x13788` (79752) |
| `zesu_raw_result` | `0x1378C` (79756) | `0x137A8` (79784) |

The decimal values are given because the hex ones were previously recorded wrong. `fca0341`'s commit
message put the two accessors at `0x137C0`/`0x137C8` and `0x137CC`/`0x137E8` — 64 bytes above where
they are — and nothing caught it, because `accessor_function_instances_exit_is_their_return` states
only `exitPcs.size = 1`, with no literal in it. `rawResult_function_instance_exits` and
`rawError_function_instance_exits` below carry the literals, so the addresses this module's
alignment, PMA and MMIO facts are about are now the addresses the artifact has.

## Anti-vacuity

`ExitPlatform` is nine register/memory claims about one state, and a bundle whose conjuncts are
jointly unsatisfiable would make every theorem below vacuous. So it is exhibited: the state
`buildZesuEntryState` really produces satisfies it at all three addresses
(`buildZesuEntryState_exitPlatform`), and — the stronger check — the `ret` genuinely retires from
that state moved to the wrapper's exit pc, landing on the sentinel
(`exitRet_retires_at_built_state`). That is a live machine step over the pinned image, not a witness
written to suit: had any premise of `tryStepRetRetires` been unsatisfiable at a reachable state, or
had the word at `0x10378` not been `jalr x0, 0(ra)`, it would fail rather than pass.

## Trust surface

Beyond `propext`/`Classical.choice`/`Quot.sound`, everything here reaches `Lean.ofReduceBool`, and
no door is opened that the layer below did not already open: the generated-data facts are
`native_decide` as everywhere in this target, and `retWord_low_byte`'s `bv_decide` lands in the same
place `Platform/Fetch.lean`'s `baseInstructionEncoding_notRVC` — which every fetch through
`runHartActiveControlFlow` already depends on — does. `rX_bits_ra_run` and the framing lemmas are
compiler-free.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

set_option maxRecDepth 100000

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.ControlFlow
open BinaryFv.Zesu.Elflings.Validation
open BinaryFv.Zesu.Elflings.Generated (generatedProgram)

/-! ## Two reads the retirement needs that no lemma produced

`tryStepRetRetires` wants the `ra` read as a `Runs (rX_bits …)` and the link as a
`Runs (get_next_pc ())`. The second has `Step/Call.lean`'s `get_next_pc_run`; the first had
nothing — `Logic/ReadFrame.lean` proves only that the read leaves the state alone, never what it
returns. -/

/-- **The link-register read, as a run.** Fixed at `x1`, which is the register a compiled `ret`
returns through and the one `returnExitsAreRetB` checks the encoding for. -/
theorem rX_bits_ra_run (state : State) (value : BitVec 64)
    (read : state.regs.get? x1 = some value) :
    Runs (rX_bits (.Regidx 1#5)) state state value := by
  have index : (Sail.BitVec.toNatInt (1#5 : BitVec 5)).toNat = 1 := rfl
  unfold Runs
  simp [rX_bits, rX, index, regval_from_reg, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
    instMonadStateOfMonadStateOf, getThe, read]

/-- The generated counter-increment write disturbs no preserved register, so every platform fact a
caller has at the pre-step state holds at the state the fetch happens in.

`Step/AbstractPremise.lean` has the companion for the *post*-`nextPC` state
(`agree_stepPremiseState`); `tryStepRetRetires` states its fetch premises one step earlier than
that, so it needs this one too. -/
theorem agree_afterIncrement (state : State) :
    Agree platformPreserved state (tryStepControlFlowAfterIncrement state) := by
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl) <;>
    simp [tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- The pc is not preserved — a step changes it — so it is framed separately. -/
theorem pc_afterIncrement (state : State) (pc : BitVec 64)
    (read : state.regs.get? PC = some pc) :
    (tryStepControlFlowAfterIncrement state).regs.get? PC = some pc := by
  change (state.regs.insert minstret_increment true).get? PC = some pc
  rw [Std.ExtDHashMap.get?_insert]
  simpa using read

/-! ## The exit instruction, fetched with its base-encoding bits

`Elfling.returnExit_fetch_and_decode` produces the fetch bytes and the decode, and drops the
equation `fetchWord … = retEncoding` its own proof establishes. Every retirement rule also wants
`BaseInstructionEncoding byte0` — the two low bits that say the word is not compressed — and that is
a fact about the *bytes*, unavailable once they are existentially bound. So the same two checks are
spent again here, keeping the equation. -/

/-- The low byte of `ret`'s encoding is `0x67`. The fetch assembles the word little-endian, so this
is the byte the base-encoding tag lives in. -/
theorem retWord_low_byte {byte0 byte1 byte2 byte3 : BitVec 8}
    (h : fetchWord byte0 byte1 byte2 byte3 = retEncoding) : byte0 = 0x67#8 := by
  simp only [fetchWord, retEncoding] at h
  bv_decide

/-- **`ret` is a base (uncompressed) encoding.** `0x67`'s two low bits are `0b11`, which is what the
generated four-byte fetch path checks before it commits to a 32-bit instruction. -/
theorem baseInstructionEncoding_of_retWord {byte0 byte1 byte2 byte3 : BitVec 8}
    (h : fetchWord byte0 byte1 byte2 byte3 = retEncoding) : BaseInstructionEncoding byte0 := by
  rw [retWord_low_byte h]
  rfl

/-- **The exit instruction is fetched, decodes to `ret`, and is not a compressed encoding.** -/
theorem returnExit_fetch_decode_base {nodes : Array ControlFlowNode}
    (hn : controlFlow? = some nodes) {functionInstance : FunctionInstance}
    (hFunctionInstance : functionInstance ∈ generatedProgram.functionInstances)
    {pc : Nat} (hpc : pc ∈ functionInstance.exitPcs)
    {node : ControlFlowNode} (hnode : ControlFlowNodeAt? nodes pc = some node)
    (hret : node.returnSite = true)
    (state : State) (intact : Artifacts.programImage.fileBytesMatchMemory state.mem)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (seccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    pc < 2 ^ 64 ∧ ∃ byte0 byte1 byte2 byte3 : BitVec 8,
      FetchBytesAt state (BitVec.ofNat 64 pc) byte0 byte1 byte2 byte3 ∧
        BaseInstructionEncoding byte0 ∧
          Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3)) state state
            (.JALR (0#12, .Regidx 1#5, zreg)) := by
  obtain ⟨hfits, -, howns⟩ :=
    returnExitsAreRetB_elim (returnExitsAreRet_check nodes hn) hFunctionInstance hpc hnode hret
  obtain ⟨byte0, byte1, byte2, byte3, hfetch, hword⟩ :=
    ProgramImage.fetchBytesAt_of_ownedFileEncodedWord Artifacts.programImage state
      { address := pc, bits := retEncoding } hfits intact howns
  refine ⟨hfits, _, _, _, _, hfetch, baseInstructionEncoding_of_retWord hword, ?_⟩
  rw [hword]
  exact ret_decode_run state privilege mseccfgBits seccfg

/-! ## What the exit `ret` needs to know about the machine

Nine claims about one state, and not one of them is about *where* the machine is: that comes from
the trace. Bundling them is what lets the three attachments differ only in their addresses.

`code` is `DecoderEnvironment.CodeIntact` at the canonical environment, spelled as the image
predicate it unfolds to, and it is the one conjunct that is not a register fact — the exit
instruction has to actually be in memory. -/

/-- The machine state an exit `ret` fires from, at the fetch address `pc`. -/
structure ExitPlatform (state : State) (pc : Nat) : Prop where
  /-- The twelve platform pins a retiring step depends on. -/
  normal : NormalExecutionState state
  /-- `InterruptDisabled` and `FetchBasePlatform` both read it. -/
  mstatusRead : ∃ v : BitVec 64, state.regs.get? Register.mstatus = some v
  /-- `InterruptDisabled` reads it; only the read has to succeed. -/
  meipRead : ∃ v : BitVec 1, state.regs.get? sig_meip = some v
  /-- The decode and the Zicfilp update both gate on it. -/
  seccfgRead : ∃ v : BitVec 64, state.regs.get? Register.mseccfg = some v
  /-- The PMA table grants an executable four-byte fetch at `pc`, at its *value*. -/
  pmaAllows : FetchPmaAllows state (BitVec.ofNat 64 pc)
  /-- The HTIF window is disabled, so the MMIO dispatch misses. -/
  htifRead : state.regs.get? htif_tohost_base = some none
  /-- The retired counter the retirement increments is readable. -/
  retired : RetiredCounterPresent state
  /-- `ra` holds the return sentinel: this is what makes the `ret` observable as a return. -/
  link : state.regs.get? x1 = some sentinelWord
  /-- The pinned image's file bytes are still in memory, so the exit instruction is fetchable. -/
  code : Artifacts.programImage.fileBytesMatchMemory state.mem

/-- **From the contracts' own exit clauses to the retirement's premises.**

`Agree platformPreserved before after` is the register-frame clause every contract in this target
carries, `RetiredCounterPresent after` the counter clause it carries instead (the machine writes
`minstret` on every retirement, so preserving it would be false of every function instance), and the code
clause is the postcondition's `CodeIntact`. Those three are exactly the gap between the entry state
and the exit state. -/
theorem exitPlatform_of_agree {before after : State} {pc : Nat}
    (agree : Agree platformPreserved before after)
    (retired : RetiredCounterPresent after)
    (code : Artifacts.programImage.fileBytesMatchMemory after.mem)
    (h : ExitPlatform before pc) : ExitPlatform after pc where
  normal := normalExecutionState_of_platformPreserved agree h.normal
  mstatusRead := h.mstatusRead.imp fun _ hv => (platformPreserved_mstatus agree).trans hv
  meipRead := h.meipRead.imp fun _ hv => (platformPreserved_sigMeip agree).trans hv
  seccfgRead := h.seccfgRead.imp fun _ hv => (platformPreserved_mseccfg agree).trans hv
  pmaAllows := fetchPmaAllows_of_agree agree h.pmaAllows
  htifRead := (platformPreserved_htifBase agree).trans h.htifRead
  retired := retired
  link := (platformPreserved_link agree).trans h.link
  code := code

/-! ## What the exit `ret` leaves alone

**The two halves of the capstone do not meet without this, and the gap was invisible from either
side.** Every contract postcondition speaks about the state the exit instruction is reached *in*;
every observation the runner makes — `SuccessfulRun.returnCode`, `storedPresent`, `inputPreserved`,
`storedValue`, and both accessor return codes — is made at the state the trace *ends* in, which is
one retirement later. Nothing related the two, and `exitRetRetires` hid its post-state behind an
existential, so the mismatch could not even be stated at the point of use.

The content is entirely mechanical — the retirement is four register writes (`minstret_increment`,
`nextPC`, `PC`, `minstret`) over an untouched memory — which is exactly why it went unwritten. It is
still load-bearing: without the memory equation the decode's stored value is a fact about a state the
runner never observes, and without the `a0` equation the return code the wrapper computed is not the
one the runner reads back. -/

/-- Everything the exit `ret` preserves, in the currency the layers above already trade in.

Memory verbatim rather than as an agreement, because that is what makes the transports `rfl`-cheap;
the platform frame, so `exitPlatform_of_agree` applies again at the post-state and the *next*
attachment has its bundle; the retired counter as presence, since the retirement is precisely what
writes it; and `a0`, which is the wrapper's and each accessor's whole observable result. -/
structure ExitRetFrame (before after : State) : Prop where
  /-- The retirement writes only registers, so every memory predicate survives it unchanged. -/
  mem : after.mem = before.mem
  /-- The eighteen registers a further `ret` needs, so `ExitPlatform` transports across it. -/
  agree : Agree platformPreserved before after
  /-- The counter the retirement itself just wrote — present, never preserved. -/
  retired : RetiredCounterPresent after
  /-- The return register the runner reads each call's outcome out of. -/
  returnValue : after.regs.get? x10 = before.regs.get? x10

/-- Every register a control-flow retirement does not write reads back unchanged. The four it does
write are named in the hypotheses rather than left to the reader. -/
theorem retiredJump_regs_frame (state : State) (pc target retired : BitVec 64) {r : Register}
    (hpc : r ≠ PC) (hnext : r ≠ nextPC) (hcounter : r ≠ minstret)
    (hinc : r ≠ minstret_increment) :
    (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target)
        target retired).regs.get? r = state.regs.get? r := by
  simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    Ne.symm hpc, Ne.symm hnext, Ne.symm hcounter, Ne.symm hinc]

/-- **The frame holds at the concrete post-state of a control-flow retirement.** `platformPreserved`
names eighteen registers and none of them is one of the four the retirement writes, which is what the
`decide`s below check — one per register, so a register moving into `platformPreserved` that the
retirement *does* write fails here rather than silently weakening the transport. -/
theorem exitRetFrame_retiredJump (state : State) (pc target retired : BitVec 64) :
    ExitRetFrame state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target)
        target retired) where
  mem := rfl
  agree := by
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl) <;>
      exact retiredJump_regs_frame state pc target retired (by decide) (by decide) (by decide)
        (by decide)
  retired := by
    refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
    simp [tryStepControlFlowAfterRetired]
  returnValue :=
    retiredJump_regs_frame state pc target retired (by decide) (by decide) (by decide) (by decide)

/-- **The runner's accessor prologue preserves the whole callee frame**, given that the link register
already held the sentinel.

`accessorSetup` writes `x1`, and `x1` is in `platformPreserved`, so this is not the vacuous framing
argument the other three writes get: the agreement holds because the prologue writes *the value that
is already there*. That is only true where the runner has kept the sentinel in `ra`, which is why the
hypothesis is the exit bundle's own `link` field rather than something assumed. -/
theorem agree_accessorSetup {state : State} (entryPc : Nat)
    (hlink : state.regs.get? x1 = some sentinelWord) :
    Agree platformPreserved state (accessorSetup entryPc state) := by
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl)
  · exact (accessorSetup_ra entryPc state).trans hlink.symm
  all_goals
    exact accessorSetup_regs_frame entryPc state _ (by decide) (by decide) (by decide) (by decide)

/-- **The exit bundle survives entering an accessor.** So a bundle established once, at the state the
builder produces, is still available at each of the two accessor calls — which is what lets the whole
chain of attachments run off a single `buildZesuEntryState_exitPlatform`. -/
theorem exitPlatform_accessorSetup {state : State} {pc : Nat} (entryPc : Nat)
    (h : ExitPlatform state pc) : ExitPlatform (accessorSetup entryPc state) pc :=
  exitPlatform_of_agree (agree_accessorSetup entryPc h.link)
    (h.retired.imp fun _ hv =>
      (accessorSetup_regs_frame entryPc state minstret (by decide) (by decide) (by decide)
        (by decide)).trans hv)
    h.code h

/-! ## The `ret` retirement

Every premise of `tryStepRetRetires` discharged. The three that are genuinely about the *target* —
the fetch address's alignment, its PMA grant, and its distance below the two fixed MMIO windows —
are hypotheses, because they are facts about a number and the machine's configuration, not about the
step layer. -/

/-- **A generated return exit retires, and the pc lands on the sentinel.**

The conclusion is stated as "there is a state the step reaches whose pc is the sentinel" rather than
as the exact post-state, because that is the shape `SentinelBridge` consumes and the post-state's
internal structure is not something any caller should have to match. -/
theorem exitRetRetires {nodes : Array ControlFlowNode} (hn : controlFlow? = some nodes)
    {functionInstance : FunctionInstance}
    (hFunctionInstance : functionInstance ∈ generatedProgram.functionInstances)
    {pc : Nat} (hpc : pc ∈ functionInstance.exitPcs)
    {node : ControlFlowNode} (hnode : ControlFlowNodeAt? nodes pc = some node)
    (hret : node.returnSite = true)
    (aligned : pc % 4 = 0)
    (belowClint : pc + 4 ≤ (plat_clint_base : BitVec 64).toNat)
    (belowSig : pc + 4 ≤ (plat_sig_base : BitVec 64).toNat)
    {state : State} (platform : ExitPlatform state pc)
    (atExit : state.regs.get? PC = some (BitVec.ofNat 64 pc)) (stepNo : Nat) :
    ∃ final : State, Runs (try_step stepNo false) state final false ∧
      final.regs.get? PC = some sentinelWord ∧ ExitRetFrame state final := by
  obtain ⟨hhart, hpriv, hsatp, hmideleg, hmie, hmip, hpmpcfg, hpmpaddr, hinhibit, hcfg, help,
    hmisa⟩ := platform.normal
  obtain ⟨mstatusBits, hmstatus⟩ := platform.mstatusRead
  obtain ⟨seccfgBits, hseccfg⟩ := platform.seccfgRead
  obtain ⟨retiredVal, hretired⟩ := platform.retired
  -- `misa`'s clause is a `match`, so its value has to be named by case analysis.
  obtain ⟨misaBits, hmisaRead⟩ : ∃ v, state.regs.get? Register.misa = some v := by
    cases hread : state.regs.get? Register.misa with
    | none => rw [hread] at hmisa; exact absurd hmisa (by simp)
    | some v => exact ⟨v, rfl⟩
  have hagree : Agree platformPreserved state (tryStepControlFlowAfterIncrement state) :=
    agree_afterIncrement state
  have hnormalInc : NormalExecutionState (tryStepControlFlowAfterIncrement state) :=
    normalExecutionState_of_platformPreserved hagree platform.normal
  -- The bytes and the decode, at the state the generated fetch happens in. The counter-increment
  -- write is a register write, so the memory the fetch reads is the memory the contract pinned.
  have hmemInc : (tryStepControlFlowAfterIncrement state).mem = state.mem := rfl
  obtain ⟨hfits, byte0, byte1, byte2, byte3, hbytes, hbase, hdecode⟩ :=
    returnExit_fetch_decode_base hn hFunctionInstance hpc hnode hret
      (tryStepControlFlowAfterIncrement state) (hmemInc ▸ platform.code)
      ((hagree cur_privilege (by simp [platformPreserved])).trans hpriv)
      seccfgBits ((platformPreserved_mseccfg hagree).trans hseccfg)
  have hwordNat : (BitVec.ofNat 64 pc).toNat = pc := by
    simpa using Nat.mod_eq_of_lt hfits
  -- The base-fetch platform at the exit address.
  have hplatform : FetchBasePlatform (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 pc) :=
    fetchBasePlatform_of_offPC (pc_afterIncrement state (BitVec.ofNat 64 pc) atExit)
      (fetchBasePlatformOffPC_of_normal hnormalInc
        ((platformPreserved_mstatus hagree).trans hmstatus) (by rw [hwordNat]; exact aligned)
        (fetchPmaAllows_of_agree hagree platform.pmaAllows))
  -- The MMIO dispatch misses at the exit address.
  have hnoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 pc) :=
    fetchMemoryNoMMIO_of_state_layout_excluded _ _
      ⟨fetch_mmio_address_excluded_of_before_layout (BitVec.ofNat 64 pc)
        (by rw [hwordNat]; exact belowClint) (by rw [hwordNat]; exact belowSig),
        (platformPreserved_htifBase hagree).trans platform.htifRead⟩
  -- The remaining register-level premises.
  have hinterrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state) :=
    interruptDisabled_of_normal hnormalInc ((platformPreserved_mstatus hagree).trans hmstatus)
      (platform.meipRead.imp fun _ hv => (platformPreserved_sigMeip hagree).trans hv)
  have hnotExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state) :=
    landingPadNotExpected_of_normal hnormalInc
  have helpElp := updateElpState_run_atStepPremise state (BitVec.ofNat 64 pc) (.Regidx 1#5)
    seccfgBits hpriv hseccfg
  have hzca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 pc) misaBits hmisaRead
  have hnextRead :
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 pc)).regs.get? nextPC =
        some (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp
  have hlink := get_next_pc_run _ _ hnextRead
  have hrs1 : Runs (rX_bits (.Regidx 1#5))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      sentinelWord :=
    rX_bits_ra_run _ _
      ((agree_stepPremiseState state (BitVec.ofNat 64 pc) x1
        (by simp [platformPreserved])).trans platform.link)
  -- The sentinel is four-byte aligned, so clearing bit 0 of the link leaves it alone.
  have hbit1 : Sail.BitVec.access sentinelWord 1 = 0#1 := by decide
  have hupdate : Sail.BitVec.update sentinelWord 0 0#1 = sentinelWord := by decide
  have hretires := tryStepRetRetires stepNo state (BitVec.ofNat 64 pc) retiredVal (.Regidx 1#5)
    (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) sentinelWord 0 0 byte0 byte1 byte2 byte3 _
    hplatform hnoMMIO hbytes hinterrupts hbase hdecode hnotExpected helpElp hlink hrs1 hbit1 hzca
    hhart hinhibit hcfg (by decide) (by decide) hretired
  refine ⟨_, hretires, ?_, exitRetFrame_retiredJump state (BitVec.ofNat 64 pc) _ retiredVal⟩
  rw [hupdate]
  exact Elfling.tryStepControlFlowAfterRetired_pc _ _ _

/-! ## The three exit addresses, as data

Everything below turns on three numbers, and each of the four facts about them is checked rather
than argued: they are four-byte aligned, they sit below both fixed MMIO windows, the decoded CFG
calls each of them a return site, and each is the *whole* exit inventory of the function instance the
runner enters. The last is the one that cannot be generalized — `FunctionTrace` halts at the first
exit it meets, so an instance with a second exit would let the trace stop somewhere there is no `ret`
to retire. 128 of the 141 generated instances have no return exit at all. -/

/-- The three pcs the sentinel attaches at: the wrapper's `ret` and the two accessors'. -/
def sentinelExitPcs : List Nat := [0x10378, 0x13788, 0x137A8]

/-- Four-byte aligned, so the generated fetch's four alignment conjuncts hold
(`fetchAligned_of_mod_four`). -/
theorem sentinelExitPcs_aligned : ∀ pc ∈ sentinelExitPcs, pc % 4 = 0 := by decide

/-- A four-byte fetch at any of them ends before the CLINT window. -/
theorem sentinelExitPcs_belowClint :
    ∀ pc ∈ sentinelExitPcs, pc + 4 ≤ (plat_clint_base : BitVec 64).toNat := by decide

/-- And before the signature window, so `within_mmio_readable` is false at all three. -/
theorem sentinelExitPcs_belowSig :
    ∀ pc ∈ sentinelExitPcs, pc + 4 ≤ (plat_sig_base : BitVec 64).toNat := by decide

/-- **All three are decoded return sites.** Read off the CFG the pinned image decodes to, so a moved
or re-classified exit fails here rather than silently re-describing which instruction the run ends
on. -/
theorem sentinelExitPcs_are_return_sites :
    ∀ nodes, controlFlow? = some nodes → ∀ pc ∈ sentinelExitPcs,
      ∃ node, ControlFlowNodeAt? nodes pc = some node ∧ node.returnSite = true := by
  intro nodes hn pc hpc
  have h : (controlFlow?.map fun ns => sentinelExitPcs.all fun a =>
      match ControlFlowNodeAt? ns a with
      | some node => node.returnSite
      | none => false).getD false = true := by native_decide
  rw [hn] at h
  simp only [Option.map_some, Option.getD_some] at h
  have hrow := List.all_eq_true.mp h pc hpc
  cases hnode : ControlFlowNodeAt? nodes pc with
  | none => rw [hnode] at hrow; exact absurd hrow (by simp)
  | some node => exact ⟨node, rfl, by rw [hnode] at hrow; exact hrow⟩

/-! ### Which instance each attachment enters, and its single exit

The two accessors are selected by their **pinned entry addresses**, because it is the address
`runAccessor` writes into `PC` that decides which instance runs. The wrapper is selected by the
generated program's own `entry` identity, which is how `entry_function_instance_exit_is_its_return`
states it; `entry_function_instance_entryPc` below checks the two selections name the same code, so
the runner's `PC := Artifacts.zesuDecodeRaw` really enters the instance whose exit is pinned. -/

/-- The wrapper's instance is one of the generated ones, so its obligations are the ones the
compliance statement quantifies. -/
theorem entry_function_instance_mem {fi : FunctionInstance}
    (hfind : Program.find? generatedProgram generatedProgram.entry = some fi) :
    fi ∈ generatedProgram.functionInstances :=
  Array.mem_of_find?_eq_some hfind

/-- **The identity the exit is pinned against and the address the runner jumps to agree.** Without
this the wrapper's exit inventory would be a fact about a different instance than the one
`buildZesuEntryState` enters. -/
theorem entry_function_instance_entryPc :
    ∀ fi, Program.find? generatedProgram generatedProgram.entry = some fi →
      fi.entryPc = resolvedSymbols.decodeEntry := by
  intro fi hfind
  have h : ((Program.find? generatedProgram generatedProgram.entry).map
      fun i => i.entryPc == resolvedSymbols.decodeEntry).getD false = true := by native_decide
  rw [hfind] at h
  simpa using h

/-- The two accessor instances exist and are distinct: without this the `all` below would be an `all`
over an empty selection, which is `true` for any claim whatever. -/
theorem accessor_function_instances_selected :
    (generatedProgram.functionInstances.filter
      (fun i => i.entryPc == resolvedSymbols.rawResult)).size = 1 ∧
    (generatedProgram.functionInstances.filter
      (fun i => i.entryPc == resolvedSymbols.rawError)).size = 1 ∧
    resolvedSymbols.rawResult ≠ resolvedSymbols.rawError := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- **`zesu_raw_result`'s whole exit inventory is its `ret` at `0x137A8`.** -/
theorem rawResult_function_instance_exits {fi : FunctionInstance}
    (hmem : fi ∈ generatedProgram.functionInstances)
    (hentry : fi.entryPc = resolvedSymbols.rawResult) : fi.exitPcs = #[0x137A8] := by
  have h : generatedProgram.functionInstances.all (fun i =>
      !(i.entryPc == resolvedSymbols.rawResult) || (i.exitPcs == #[0x137A8])) = true := by
    native_decide
  have hrow := forall_mem_of_all h fi hmem
  simpa [hentry] using hrow

/-- **`zesu_raw_error`'s whole exit inventory is its `ret` at `0x13788`.** -/
theorem rawError_function_instance_exits {fi : FunctionInstance}
    (hmem : fi ∈ generatedProgram.functionInstances)
    (hentry : fi.entryPc = resolvedSymbols.rawError) : fi.exitPcs = #[0x13788] := by
  have h : generatedProgram.functionInstances.all (fun i =>
      !(i.entryPc == resolvedSymbols.rawError) || (i.exitPcs == #[0x13788])) = true := by
    native_decide
  have hrow := forall_mem_of_all h fi hmem
  simpa [hentry] using hrow

theorem rawError_function_instance_execution_pcs {fi : FunctionInstance}
    (hmem : fi ∈ generatedProgram.functionInstances)
    (hentry : fi.entryPc = resolvedSymbols.rawError) :
    Program.inRanges (functionInstanceExecutionRanges generatedProgram fi) 0x13780 = true ∧
      Program.inRanges (functionInstanceExecutionRanges generatedProgram fi) 0x13784 = true ∧
        Program.inRanges (functionInstanceExecutionRanges generatedProgram fi) 0x13788 = true := by
  have h : generatedProgram.functionInstances.all (fun i =>
      !(i.entryPc == resolvedSymbols.rawError) ||
        (Program.inRanges (functionInstanceExecutionRanges generatedProgram i) 0x13780 &&
          Program.inRanges (functionInstanceExecutionRanges generatedProgram i) 0x13784 &&
            Program.inRanges (functionInstanceExecutionRanges generatedProgram i) 0x13788)) = true := by
    native_decide
  have hrow := forall_mem_of_all h fi hmem
  simp [hentry] at hrow
  exact ⟨hrow.1.1, hrow.1.2, hrow.2⟩

theorem rawError_function_instance_execution_pc_membership {fi : FunctionInstance}
    (hmem : fi ∈ generatedProgram.functionInstances)
    (hentry : fi.entryPc = resolvedSymbols.rawError) :
    functionInstanceExecutionPcs generatedProgram fi (BitVec.ofNat 64 0x13780) ∧
      functionInstanceExecutionPcs generatedProgram fi (BitVec.ofNat 64 0x13784) ∧
        functionInstanceExecutionPcs generatedProgram fi (BitVec.ofNat 64 0x13788) := by
  obtain ⟨h80, h84, h88⟩ := rawError_function_instance_execution_pcs hmem hentry
  refine ⟨functionInstanceExecutionPcs_iff_ranges.mpr ?_,
    functionInstanceExecutionPcs_iff_ranges.mpr ?_,
    functionInstanceExecutionPcs_iff_ranges.mpr ?_⟩
  · exact RegionPcs.iff_inRanges.mpr h80
  · exact RegionPcs.iff_inRanges.mpr h84
  · exact RegionPcs.iff_inRanges.mpr h88

/-! ## Which contract each of the three instances owes

The compliance obligation dispatches on `catalogEntryFor functionInstance.id.function`, so
"`zesu_decode_raw`'s instance owes `functionInstanceZesuDecodeRaw`" is a fact about the generated
identity and the address-free catalog, not something a caller may choose. Each of the three is read
through the canonical whole-program identity table and then looked up in the catalog by identity,
never by name. -/

/-- **The wrapper's instance dispatches to the exported-wrapper contract.** -/
theorem entry_function_instance_tag :
    ∀ fi, Program.find? generatedProgram generatedProgram.entry = some fi →
      (catalogEntryFor fi.id.function).map (·.tag) = some ContractTag.zesuDecodeRaw := by
  intro fi hfind
  have h : ((Program.find? generatedProgram generatedProgram.entry).map
      fun i => (catalogEntryFor i.id.function).map (·.tag) == some ContractTag.zesuDecodeRaw).getD
      false = true := by native_decide
  rw [hfind] at h
  simpa using h

/-- **`zesu_raw_result`'s instance dispatches to `contractRawResult`.** Selected by its pinned entry
address, because that is what `runAccessor` writes into `PC`. -/
theorem rawResult_function_instance_tag {fi : FunctionInstance}
    (hmem : fi ∈ generatedProgram.functionInstances)
    (hentry : fi.entryPc = resolvedSymbols.rawResult) :
    (catalogEntryFor fi.id.function).map (·.tag) = some ContractTag.rawResult := by
  have h : generatedProgram.functionInstances.all (fun i =>
      !(i.entryPc == resolvedSymbols.rawResult) ||
        ((catalogEntryFor i.id.function).map (·.tag) == some ContractTag.rawResult)) = true := by
    native_decide
  have hrow := forall_mem_of_all h fi hmem
  simpa [hentry] using hrow

/-- **`zesu_raw_error`'s instance dispatches to `contractRawError`.** -/
theorem rawError_function_instance_tag {fi : FunctionInstance}
    (hmem : fi ∈ generatedProgram.functionInstances)
    (hentry : fi.entryPc = resolvedSymbols.rawError) :
    (catalogEntryFor fi.id.function).map (·.tag) = some ContractTag.rawError := by
  have h : generatedProgram.functionInstances.all (fun i =>
      !(i.entryPc == resolvedSymbols.rawError) ||
        ((catalogEntryFor i.id.function).map (·.tag) == some ContractTag.rawError)) = true := by
    native_decide
  have hrow := forall_mem_of_all h fi hmem
  simpa [hentry] using hrow

/-- **Each accessor's instance exists.** `accessor_function_instances_selected` counts them; this
produces one, which is what an obligation quantified over `functionInstances` has to be applied to.
Without it the three lemmas above would be conditional on a membership nothing supplies. -/
theorem rawResult_function_instance_found :
    ∃ fi, fi ∈ generatedProgram.functionInstances ∧ fi.entryPc = resolvedSymbols.rawResult := by
  have h : (generatedProgram.functionInstances.find?
      (fun i => i.entryPc == resolvedSymbols.rawResult)).isSome = true := by native_decide
  obtain ⟨fi, hfi⟩ := Option.isSome_iff_exists.mp h
  exact ⟨fi, Array.mem_of_find?_eq_some hfi, by simpa using Array.find?_some hfi⟩

/-- The `zesu_raw_error` twin. -/
theorem rawError_function_instance_found :
    ∃ fi, fi ∈ generatedProgram.functionInstances ∧ fi.entryPc = resolvedSymbols.rawError := by
  have h : (generatedProgram.functionInstances.find?
      (fun i => i.entryPc == resolvedSymbols.rawError)).isSome = true := by native_decide
  obtain ⟨fi, hfi⟩ := Option.isSome_iff_exists.mp h
  exact ⟨fi, Array.mem_of_find?_eq_some hfi, by simpa using Array.find?_some hfi⟩

/-! ## One attachment, in general

The three theorems below differ only in how they identify their function instance and pin its exit;
this is everything else. Stated separately so the shared reasoning — the exit pc is a definite
description, the `ret` retires, the sentinel is avoided — is written once. -/

/-- **A function instance whose only exit is a return reaches the sentinel.**

`hexits` is what makes the exit pc a *definite description*: the trace stops at some exit, and there
is only one. `hexit ∈ sentinelExitPcs` is what supplies the three number facts. -/
theorem traceToSentinel_of_singleReturnExit {nodes : Array ControlFlowNode}
    (hn : controlFlow? = some nodes) {fi : FunctionInstance}
    (hmem : fi ∈ generatedProgram.functionInstances) {exitPc : Nat}
    (hexits : fi.exitPcs = #[exitPc]) (hlisted : exitPc ∈ sentinelExitPcs)
    {entryWord : BitVec 64} {count : Nat} {entryState atExit : State}
    (platform : ExitPlatform atExit exitPc)
    (run : Elfling.EnteredFunctionTrace (functionInstanceExecutionPcs generatedProgram fi)
      (functionInstanceExitPred fi) entryWord 0 count entryState atExit) :
    ∃ final : State, TraceToSentinel sentinelWord 0 (count + 1) entryState final ∧
      2 ≤ count + 1 ∧ final.regs.get? PC = some sentinelWord ∧ ExitRetFrame atExit final := by
  -- Where the run stopped: the only exit there is.
  obtain ⟨stopped, hstopped, hstoppedExit⟩ := run.trace.final_at_exit
  have hstoppedNat : stopped.toNat = exitPc := by
    have : stopped.toNat ∈ fi.exitPcs := hstoppedExit
    rw [hexits] at this
    simpa using this
  have hstoppedWord : stopped = BitVec.ofNat 64 exitPc := by
    apply BitVec.eq_of_toNat_eq
    rw [hstoppedNat]
    simp [Nat.mod_eq_of_lt, hstoppedNat ▸ stopped.isLt]
  have hpcRead : atExit.regs.get? PC = some (BitVec.ofNat 64 exitPc) := hstoppedWord ▸ hstopped
  -- The exit is a return site, and it is in the instance's own inventory.
  obtain ⟨node, hnode, hret⟩ := sentinelExitPcs_are_return_sites nodes hn exitPc hlisted
  have hmemExit : exitPc ∈ fi.exitPcs := by simp [hexits]
  -- The `ret` retires and lands on the sentinel.
  obtain ⟨final, hretires, hlanded, hframe⟩ :=
    exitRetRetires hn hmem hmemExit hnode hret (sentinelExitPcs_aligned exitPc hlisted)
      (sentinelExitPcs_belowClint exitPc hlisted) (sentinelExitPcs_belowSig exitPc hlisted)
      platform hpcRead (0 + count)
  -- The bridge's two avoidance conditions, at this instance.
  refine ⟨final, ?_, ?_, hlanded, hframe⟩
  · exact (Elfling.traceToSentinel_of_enteredFunctionTrace
      (generated_execution_pcs_avoid_sentinel fi hmem)
      (generated_exit_pcs_avoid_sentinel fi hmem) run hretires hlanded).1
  · exact (Elfling.traceToSentinel_of_enteredFunctionTrace
      (generated_execution_pcs_avoid_sentinel fi hmem)
      (generated_exit_pcs_avoid_sentinel fi hmem) run hretires hlanded).2

/-! ## The three attachments -/

/-- **The exported wrapper's sentinel trace.**

The `EnteredFunctionTrace` is the wrapper's own `ImplementsFunctionInstance` obligation; everything
else is discharged. The resulting trace is `count + 1` long, which is exactly what
`SuccessfulRun.withinStepBound` (`≤ entryStepBound input.size + 1`) admits given the contract's
`count ≤ entryStepBound input.size`. -/
theorem entryTraceToSentinel_of_enteredFunctionTrace {nodes : Array ControlFlowNode}
    (hn : controlFlow? = some nodes) {fi : FunctionInstance}
    (hfind : Program.find? generatedProgram generatedProgram.entry = some fi)
    {count : Nat} {entryState atExit : State}
    (platform : ExitPlatform atExit 0x10378)
    (run : Elfling.EnteredFunctionTrace (functionInstanceExecutionPcs generatedProgram fi)
      (functionInstanceExitPred fi) (functionInstanceEntryWord fi) 0 count entryState atExit) :
    ∃ final : State, TraceToSentinel sentinelWord 0 (count + 1) entryState final ∧
      2 ≤ count + 1 ∧ final.regs.get? PC = some sentinelWord ∧ ExitRetFrame atExit final :=
  traceToSentinel_of_singleReturnExit hn (entry_function_instance_mem hfind)
    (entry_function_instance_exit_is_its_return nodes hn fi hfind).1 (by decide) platform run

/-- **`zesu_raw_result`'s sentinel trace, in the runner's own packaging.**

`AccessorReachesSentinel` is what `runAccessor_returned_of_reaches` consumes, and its bound is
`stepBound + 1` for the same reason the wrapper's is: the contract bounds the accessor's own
retirements and the `ret` that reaches the sentinel is one more. -/
theorem rawResultReachesSentinel_of_enteredFunctionTrace {nodes : Array ControlFlowNode}
    (hn : controlFlow? = some nodes) {fi : FunctionInstance}
    (hmem : fi ∈ generatedProgram.functionInstances)
    (hentry : fi.entryPc = resolvedSymbols.rawResult)
    {count : Nat} (hbound : count ≤ rawResultStepBound) {before atExit : State}
    (platform : ExitPlatform atExit 0x137A8)
    (run : Elfling.EnteredFunctionTrace (functionInstanceExecutionPcs generatedProgram fi)
      (functionInstanceExitPred fi) (functionInstanceEntryWord fi) 0 count
      (accessorSetup resolvedSymbols.rawResult before) atExit) :
    ∃ after : State,
      TraceToSentinel sentinelWord 0 (count + 1)
        (accessorSetup resolvedSymbols.rawResult before) after ∧
      AccessorReachesSentinel resolvedSymbols.rawResult rawResultStepBound before after ∧
      after.regs.get? PC = some sentinelWord ∧ ExitRetFrame atExit after := by
  obtain ⟨after, htrace, -, hlanded, hframe⟩ :=
    traceToSentinel_of_singleReturnExit hn hmem (rawResult_function_instance_exits hmem hentry)
      (by decide) platform run
  exact ⟨after, htrace, ⟨count + 1, by omega, htrace⟩, hlanded, hframe⟩

/-- **`zesu_raw_error`'s sentinel trace, in the runner's own packaging.** -/
theorem rawErrorReachesSentinel_of_enteredFunctionTrace {nodes : Array ControlFlowNode}
    (hn : controlFlow? = some nodes) {fi : FunctionInstance}
    (hmem : fi ∈ generatedProgram.functionInstances)
    (hentry : fi.entryPc = resolvedSymbols.rawError)
    {count : Nat} (hbound : count ≤ rawErrorStepBound) {before atExit : State}
    (platform : ExitPlatform atExit 0x13788)
    (run : Elfling.EnteredFunctionTrace (functionInstanceExecutionPcs generatedProgram fi)
      (functionInstanceExitPred fi) (functionInstanceEntryWord fi) 0 count
      (accessorSetup resolvedSymbols.rawError before) atExit) :
    ∃ after : State,
      TraceToSentinel sentinelWord 0 (count + 1)
        (accessorSetup resolvedSymbols.rawError before) after ∧
      AccessorReachesSentinel resolvedSymbols.rawError rawErrorStepBound before after ∧
      after.regs.get? PC = some sentinelWord ∧ ExitRetFrame atExit after := by
  obtain ⟨after, htrace, -, hlanded, hframe⟩ :=
    traceToSentinel_of_singleReturnExit hn hmem (rawError_function_instance_exits hmem hentry)
      (by decide) platform run
  exact ⟨after, htrace, ⟨count + 1, by omega, htrace⟩, hlanded, hframe⟩

/-! ## Anti-vacuity

`ExitPlatform` is nine claims about one state, and `exitRetRetires` would prove anything if they
could not all hold at once. Two checks, in increasing strength.

The first exhibits the bundle at the state `buildZesuEntryState` really produces — the builder's own
state, not one written to suit, which matters because `CodeIntact` alone is twenty kilobytes of
file-backed image bytes.

The second is the one that would catch a bundle that is satisfiable but useless: it takes that same
state, moves the pc to the wrapper's exit (the one thing a builder cannot do, because arriving there
is the trace's job) and *runs the machine*. What comes back is a genuine `Runs (try_step …)` over the
pinned image whose post-state's pc is the sentinel. If any premise of `tryStepRetRetires` were
unsatisfiable at a reachable state, or if the word at `0x10378` were not a `ret` through `ra`, this
would fail rather than pass. -/

/-- The two value-pinned registers, checked at the three attachment addresses. Closed and finite, so
`native_decide` settles it — and it is the caller-side `native_decide`
`EntryBinding.configureFetchPinnedB` was parameterized for. -/
theorem configureFetchPinned_sentinelExits : configureFetchPinnedB sentinelExitPcs = true := by
  native_decide

/-- **`ExitPlatform` holds at the state the runner builds**, at all three attachment addresses. -/
theorem buildZesuEntryState_exitPlatform (input : ByteArray) :
    ∃ s, Runs (buildZesuEntryState input) initialState s () ∧
      ∀ pc ∈ sentinelExitPcs, ExitPlatform s pc := by
  obtain ⟨s, hrun, hbind, hx1, -, hnormal, hpresent, hpinned, -⟩ :=
    buildZesuEntryState_entry_binding_abi input
  obtain ⟨hpma, hhtif⟩ := hpinned sentinelExitPcs configureFetchPinned_sentinelExits
  have hcode : Artifacts.programImage.fileBytesMatchMemory s.mem := by
    have h : canonicalEnvironment.image.fileBytesMatchMemory s.mem := hbind.2.1
    have himg : canonicalEnvironment.image = Artifacts.programImage := by
      simp only [canonicalEnvironment]
    rwa [himg] at h
  refine ⟨s, hrun, fun pc hpc => ?_⟩
  obtain ⟨regions, region, hregions, hmatch, hexec⟩ := hpma pc hpc
  exact
    { normal := hnormal
      mstatusRead := hpresent.2.1
      meipRead := hpresent.2.2.1
      seccfgRead := hpresent.2.2.2.2
      pmaAllows := ⟨regions, region, hregions, hmatch, hexec⟩
      htifRead := hhtif
      retired := hpresent.1
      link := hx1
      code := hcode }

/-- The decoded control flow exists, which every data fact above is conditional on. -/
theorem controlFlow_some : ∃ nodes, controlFlow? = some nodes := by
  have h : controlFlow?.isSome = true := by native_decide
  exact Option.isSome_iff_exists.mp h

/-- **The exit `ret` retires from a state the machine reaches, and lands on the sentinel.**

Not "the hypotheses are consistent" but "they hold": a live single-step execution of the pinned
image's own instruction at `0x10378`, from the builder's state with the pc moved there. -/
theorem exitRet_retires_at_built_state :
    ∃ s final : State, Runs (buildZesuEntryState ByteArray.empty) initialState s () ∧
      Runs (try_step 0 false)
        { s with regs := s.regs.insert PC (BitVec.ofNat 64 0x10378) } final false ∧
      final.regs.get? PC = some sentinelWord := by
  obtain ⟨s, hrun, hplatform⟩ := buildZesuEntryState_exitPlatform ByteArray.empty
  obtain ⟨nodes, hn⟩ := controlFlow_some
  obtain ⟨fi, hfind⟩ : ∃ fi, Program.find? generatedProgram generatedProgram.entry = some fi :=
    Option.isSome_iff_exists.mp entry_function_instance_found
  have hexits : fi.exitPcs = #[0x10378] :=
    (entry_function_instance_exit_is_its_return nodes hn fi hfind).1
  obtain ⟨node, hnode, hret⟩ :=
    sentinelExitPcs_are_return_sites nodes hn 0x10378 (by decide)
  have hbase : ExitPlatform s 0x10378 := hplatform 0x10378 (by decide)
  -- Moving the pc disturbs no register the bundle reads; `minstret` is not preserved by the
  -- *call*, but it is certainly preserved by a write to `PC`.
  have hmoved : ExitPlatform { s with regs := s.regs.insert PC (BitVec.ofNat 64 0x10378) }
      0x10378 := by
    refine exitPlatform_of_agree (agree_insert_PC s (BitVec.ofNat 64 0x10378)) ?_ hbase.code hbase
    obtain ⟨retired, hretired⟩ := hbase.retired
    refine ⟨retired, ?_⟩
    change (s.regs.insert PC (BitVec.ofNat 64 0x10378)).get? minstret = some retired
    rw [Std.ExtDHashMap.get?_insert]
    simpa using hretired
  have hpcRead :
      ({ s with regs := s.regs.insert PC (BitVec.ofNat 64 0x10378) } : State).regs.get? PC =
        some (BitVec.ofNat 64 0x10378) := by
    change (s.regs.insert PC (BitVec.ofNat 64 0x10378)).get? PC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp
  obtain ⟨final, hretires, hlanded, -⟩ :=
    exitRetRetires hn (entry_function_instance_mem hfind) (by simp [hexits]) hnode hret
      (by decide) (by decide) (by decide) hmoved hpcRead 0
  exact ⟨s, final, hrun, hretires, hlanded⟩

/-! ## The `+ 1` composes

The bridge yields a trace of length `count + 1`, and three separate budgets have to admit it. Each of
the three was written before any `TraceToSentinel` existed, so none of them had ever been tested
against one; that is exactly the situation in which a tight bound reads as correct forever. Checked
here rather than argued. -/

/-- **The wrapper's composed trace fits both of its budgets.** `SuccessfulRun.withinStepBound` and
`RejectedRun.withinStepBound` admit `entryStepBound size + 1`, and the runner's fuel strictly exceeds
the composed length — which is what `zesuFuel = entryStepBound + 2` was sized for, one step to retire
the return onto the sentinel and one to keep the budget strictly greater. -/
theorem entryTrace_budgets {size count : Nat} (hbound : count ≤ entryStepBound size) :
    count + 1 ≤ entryStepBound size + 1 ∧ count + 1 < zesuFuel size := by
  have hfuel := zesuFuel_exceeds_bound size
  unfold zesuFuel at hfuel ⊢
  omega

/-- **Each accessor's composed trace fits its own budget**, for the same reason and with the same
`+ 2`. `AccessorReachesSentinel` allows `stepBound + 1` and `runAccessor_returned_of_bound` spends
the first of `accessorFuel`'s two slack steps here. -/
theorem accessorTrace_budgets {stepBound count : Nat} (hbound : count ≤ stepBound) :
    count + 1 ≤ stepBound + 1 ∧ count + 1 < accessorFuel stepBound := by
  have hfuel := accessorFuel_exceeds_bound stepBound
  unfold accessorFuel at hfuel ⊢
  omega

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
