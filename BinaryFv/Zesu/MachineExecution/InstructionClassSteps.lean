import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level3Contracts
import BinaryFv.Zesu.MachineExecution.RegisterRuns
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep

/-!
# One `try_step` lemma per register-writing instruction class

`decoderRegisterWriteStep` already retires an arbitrary decoded register-writing instruction through
the configured decoder's `try_step`. What every concrete instruction theorem still repeated was the
prologue in front of it: pin the four image bytes, lift them to a `FetchBytesAt`, destructure
`decoderStepPlatform` only to obtain the two register reads `decode_run` consults, run `decode_run`,
name the `execute` state, transport the source read into it, and assemble the class's
`execute_*_run` contract. That prologue is the same at every site of a given class and differs only
in (pc, four bytes, immediate, source and destination register indices, opcode).

This module collapses it: one lemma per class whose only real arguments are those literals, the
source read and the destination write. Everything else is an `autoParam`.

## Why the destination register stays abstract

Generalising over the destination looks impossible at first because `RegisterType dest` is
dependent, so a `value` written as `iTypeResult …` cannot be typed before `dest` is fixed. The fix is
to keep `value : RegisterType dest` an abstract implicit and let the *write* premise tie it to the
class's result expression: `writeDest` mentions `iTypeResult op imm source` on the action side and
`value` on the state side, so a call site's `wX_x<n>_run` instantiates both at once.

## Which premises are `autoParam`s

Every one of them, with nothing asked of the call site:

* `pcIn` — `decoder_fetch_pc` proves execution-region membership and alignment by `native_decide`.
* the four image lookups and the address bound — as in `RegisterWriteStep.fetchInstruction`.
* `decode` — `decoder_decode`; see "Making `decode` a real `autoParam`" below for why the
  obligation is stated hypothetically in the two platform reads `decode_run` consults.
* `baseEncoding` and the four destination disequalities — `decide`.

No `decoderStepPlatform` destructuring, no `decoderDecodeContext` line, and no
`fetchWord … = <literal>` rewrite is needed at a call site.

## Scope

Fourteen classes in four groups.

* Six that fall through and write a register — `ITYPE`, `SHIFTIOP`, `RTYPE`, `AUIPC`, `LUI`, and a
  `LOAD` of any width and signedness. `decoderLhuStep` survives as the `unsigned`/`2` instance of
  the generic load rather than as a sibling proof.
* Four stores — widths 1, 2, 4 and 8 — which fall through but write memory instead of a register, so
  they retire through `tryStepFallThroughRetires`. They are generated from a table because only the
  delivered `execute_STORE_*_run` differs per width; see the store section.
* One not-taken branch, which falls through and writes nothing, so it has no register-writing
  retirement to reuse.
* Four control transfers — `jal`, `jalr` call, `ret`, taken branch — whose retirements are
  `tryStepJRetires` / `tryStepJalrCallRetires` / `tryStepRetRetires` / `tryStepBranchTakenRetires`
  rather than `tryStepFallThroughWriteRegRetires`. The transfer section below states what else those
  need.

`decoderRegisterWriteStep` and the platform/counter bundles under it were moved here from the top of
`HasExactErePrefixProof` unchanged. They had to move: leaving them downstream made every class
lemma downstream of the first concrete instruction proof, so that proof could not use them.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep
open BinaryFv.RiscV.Sep

/-! ## Common configured-machine step context

`decoderRegisterWriteStep` and the platform/counter bundles it is built from used to live at the top
of `HasExactErePrefixProof`. They are moved here so the class lemmas below sit *upstream* of every
concrete instruction proof rather than downstream of the first one, which is what lets
`HasExactErePrefixProof` use them too. Nothing about them changed. -/

theorem decoderStepPlatform_of_decoderAgree {instructionPcs : BitVec 64 → Prop} {args}
    {base state : State} (machine : Entrypoints.ZesuDecodeRaw.DecoderMachinePre
      instructionPcs args base) (agree : Agree decoderPreserved base state)
    (pc : BitVec 64) (atPc : state.regs.get? PC = some pc)
    (pcIn : DecoderFetchPc instructionPcs pc)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      byte0 byte1 byte2 byte3) :
    ∃ mseccfgBits, StepPlatform state pc byte0 byte1 byte2 byte3 mseccfgBits := by
  have afterIncrementAgree : Agree decoderPreserved base
      (tryStepControlFlowAfterIncrement state) :=
    Agree.trans agree
      (Agree.weaken (fun _ preserved => preserved.2) (agree_afterIncrement state))
  have atPcAfter : (tryStepControlFlowAfterIncrement state).regs.get? PC = some pc :=
    pc_afterIncrement state pc atPc
  obtain ⟨fetch, noMMIO, interrupts, notExpected⟩ :=
    machine.platform _ pc afterIncrementAgree atPcAfter pcIn
  obtain ⟨mseccfgBits, mseccfgRead, -⟩ := machine.mseccfg
  have privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine :=
    (afterIncrementAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      machine.normal.2.1
  have mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg =
      some mseccfgBits :=
    (afterIncrementAgree Register.mseccfg
      (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead
  exact ⟨mseccfgBits, fetch, noMMIO, bytes, interrupts, notExpected, privilege, mseccfg⟩

theorem decoderStepPlatform {instructionPcs : BitVec 64 → Prop} {args}
    {base state : State} (machine : Entrypoints.ZesuDecodeRaw.DecoderMachinePre
      instructionPcs args base) (agree : Agree platformPreserved base state)
    (pc : BitVec 64) (atPc : state.regs.get? PC = some pc)
    (pcIn : DecoderFetchPc instructionPcs pc)
    (byte0 byte1 byte2 byte3 : BitVec 8)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      byte0 byte1 byte2 byte3) :
    ∃ mseccfgBits, StepPlatform state pc byte0 byte1 byte2 byte3 mseccfgBits :=
  decoderStepPlatform_of_decoderAgree machine
    (Agree.weaken (fun _ preserved => preserved.2) agree) pc atPc pcIn
    byte0 byte1 byte2 byte3 bytes

/-- The three counter-control reads a `try_step` postlude makes. All three are platform CSRs, so
`decoderPreserved` covers them; the `platformPreserved` form below is this one after
`Agree.weaken`. -/
theorem decoderStepCounters_of_decoderAgree {base state : State}
    (normal : NormalExecutionState base) (agree : Agree decoderPreserved base state)
    (retiredPresent : RetiredCounterPresent state) :
    ∃ retired inhibit config, StepCounters state retired inhibit config := by
  obtain ⟨retired, retiredRead⟩ := retiredPresent
  refine ⟨retired, 0, 0, ?_, ?_, ?_, by decide, by decide, retiredRead⟩
  · exact (agree hart_state (by simp [decoderPreserved, platformPreserved])).trans normal.1
  · exact (agree mcountinhibit (by simp [decoderPreserved, platformPreserved])).trans
      normal.2.2.2.2.2.2.2.2.1
  · exact (agree minstretcfg (by simp [decoderPreserved, platformPreserved])).trans
      normal.2.2.2.2.2.2.2.2.2.1

theorem decoderStepCounters {base state : State}
    (normal : NormalExecutionState base) (agree : Agree platformPreserved base state)
    (retiredPresent : RetiredCounterPresent state) :
    ∃ retired inhibit config, StepCounters state retired inhibit config :=
  decoderStepCounters_of_decoderAgree normal
    (Agree.weaken (fun _ preserved => preserved.2) agree) retiredPresent

theorem agree_coreControlFlowNextState (state : State) (pc : BitVec 64) :
    Agree platformPreserved state (coreControlFlowNextState state pc) := by
  intro register preserved
  have notNextPc : nextPC ≠ register := by
    intro equal
    subst register
    simpa [platformPreserved] using preserved
  simp [coreControlFlowNextState, Std.ExtDHashMap.get?_insert, notNextPc]

theorem agree_decoderExecuteState (state : State) (pc : BitVec 64) :
    Agree platformPreserved state
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) :=
  Agree.trans (agree_afterIncrement state)
    (agree_coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)

/-- Lift one decoded register-writing instruction through the configured decoder `try_step`, from
the decoder's own agreement.

`agree` reaches exactly two places here — `decoderStepPlatform` and `decoderStepCounters` — and
between them they read `cur_privilege`, `mseccfg`, `hart_state`, `mcountinhibit` and `minstretcfg`.
None of those is `x1`, which is the only register `decoderPreserved` gives up relative to
`platformPreserved`, so the weaker agreement suffices for the whole retirement. That is what lets a
block whose `x1` an earlier `jalr` already clobbered retire a register write at all; the
`platformPreserved` form below is this one after `Agree.weaken`. -/
theorem decoderRegisterWriteStepOfDecoderAgree {instructionPcs : BitVec 64 → Prop} {args}
    {baseState state : State}
    (machine : Entrypoints.ZesuDecodeRaw.DecoderMachinePre instructionPcs args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc : BitVec 64) (pcIn : DecoderFetchPc instructionPcs pc)
    (atPc : state.regs.get? PC = some pc)
    (byte0 byte1 byte2 byte3 : BitVec 8) (instruction : instruction)
    (destination : Register) (value : RegisterType destination)
    (fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      byte0 byte1 byte2 byte3)
    (baseEncoding : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) instruction)
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret)
    (execute : Runs (execute instruction)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
          destination value }
      (.Retire_Success ())) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state pc retired destination value) false := by
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform_of_decoderAgree machine agree pc atPc pcIn
    byte0 byte1 byte2 byte3 fetchBytes
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal agree retiredPresent
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  refine ⟨retired, ?_⟩
  exact tryStepFallThroughWriteRegRetires stepNo state pc retired inhibit config
    byte0 byte1 byte2 byte3 instruction destination value fetch noMMIO fetched interrupts
    baseEncoding decode notExpected execute destinationNotNextPc destinationNotHart
    destinationNotIncrement destinationNotRetired
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- Lift one decoded register-writing instruction through the configured decoder `try_step`. -/
theorem decoderRegisterWriteStep {instructionPcs : BitVec 64 → Prop} {args}
    {baseState state : State}
    (machine : Entrypoints.ZesuDecodeRaw.DecoderMachinePre instructionPcs args baseState)
    (agree : Agree platformPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc : BitVec 64) (pcIn : DecoderFetchPc instructionPcs pc)
    (atPc : state.regs.get? PC = some pc)
    (byte0 byte1 byte2 byte3 : BitVec 8) (instruction : instruction)
    (destination : Register) (value : RegisterType destination)
    (fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      byte0 byte1 byte2 byte3)
    (baseEncoding : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) instruction)
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret)
    (execute : Runs (execute instruction)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
          destination value }
      (.Retire_Success ())) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state pc retired destination value) false :=
  decoderRegisterWriteStepOfDecoderAgree machine
    (Agree.weaken (fun _ preserved => preserved.2) agree) retiredPresent stepNo pc pcIn atPc
    byte0 byte1 byte2 byte3 instruction destination value fetchBytes baseEncoding decode
    destinationNotNextPc destinationNotHart destinationNotIncrement destinationNotRetired execute

/-- The two post-increment register reads `decode_run` consults. Every call site of the class step
lemmas below opens by destructuring this, which is what makes their `decode` premise automatic.

`cur_privilege` and `mseccfg` are not the link register, so `decoderPreserved` already covers both
reads; the `platformPreserved` form below is this one after `Agree.weaken`. -/
theorem decoderDecodeContextOfDecoderAgree {instructionPcs : BitVec 64 → Prop}
    {margs : DecoderMachineArgs} {baseState state : State}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state) :
    (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine ∧
      ∃ bits, (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some bits := by
  have afterIncrement : Agree decoderPreserved baseState
      (tryStepControlFlowAfterIncrement state) :=
    Agree.trans agree
      (Agree.weaken (fun _ preserved => preserved.2) (agree_afterIncrement state))
  obtain ⟨bits, read, -⟩ := machine.mseccfg
  exact ⟨(afterIncrement cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      machine.normal.2.1,
    bits, (afterIncrement Register.mseccfg (by simp [decoderPreserved, platformPreserved])).trans
      read⟩

theorem decoderDecodeContext {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State} (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree platformPreserved baseState state) :
    (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine ∧
      ∃ bits, (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some bits :=
  decoderDecodeContextOfDecoderAgree machine
    (Agree.weaken (fun _ preserved => preserved.2) agree)

/-- A register read survives the `try_step` fetch bookkeeping into the state at which `execute`
runs. The bookkeeping writes only `minstret_increment` and `nextPC`, so the two disequalities
decide. -/
theorem decoderExecuteState_get? {state : State} {pc : BitVec 64} {register : Register}
    {value : RegisterType register} (read : state.regs.get? register = some value)
    (notIncrement : minstret_increment ≠ register := by decide)
    (notNextPc : nextPC ≠ register := by decide) :
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? register =
      some value := by
  simp [coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    notIncrement, notNextPc, read]

/-- A concrete pc is a decoder fetch pc when it lies in the instance's generated execution ranges
and is word aligned. Both are kernel-checked, so a wrong address fails here rather than later. -/
macro "decoder_fetch_pc" : tactic =>
  `(tactic|
    first
      | assumption
      | exact ⟨functionInstanceExecutionPcs_iff_ranges.mpr
          (RegionPcs.iff_inRanges.mpr (by native_decide)), by native_decide⟩)

/-! ## The class lemmas

Each takes the machine, the agreement and retirement it is invoked under, the program image, the
step and address literals, the four instruction bytes, the class's encoded operands, the `PC` read,
and the class's source read(s) and destination write. -/

/-! ### Making `decode` a real `autoParam`

`decode_run` closes with `simp only [… , *]`, and two of the hypotheses it consumes from the goal's
local context are the post-increment reads of `cur_privilege` and `mseccfg`; without them the
closing `rfl` fails on an unreduced `_get_Seccfg_MLPE`. Those reads follow from the
`DecoderMachinePre` and `Agree` a class lemma already takes, so making the *caller* put them in
scope is a leak: every site opened with a hand-written
`obtain … := decoderDecodeContext machine agree` carrying no information the lemma did not already
have.

Two repairs do not work. *Searching the caller's context* from inside the `autoParam` — an
`obtain … := decoderDecodeContext ‹_› ‹_›` alternative — only fires where the caller happens to
hold both a `DecoderMachinePre` hypothesis and an `Agree` hypothesis at exactly this `state`; sites
that pass a projection (`pre.machine`) or a constructed agreement (`Agree.refl state`) have neither,
and `assumption` there either fails or picks an `Agree` for the wrong state. *Deriving the decode in
the lemma body* does not work either: `decode_run` needs a **concrete** word, and inside the lemma
the four bytes are variables.

So the obligation is stated **under** those two reads instead. `decoder_decode` introduces them, so
they are in the local context `decode_run` runs in no matter what the caller has — the tactic reads
nothing from the call site at all; and the class lemma discharges them in its own proof body via
`decoderDecode`, where `machine` and `agree` are genuine binders. The premise is only ever weakened
(`A → B` in place of `B`), so no conclusion changes, and nothing about `decode_run` itself changes —
a wrong immediate, register, width or signedness still fails exactly as before. -/

/-- A class lemma's decode obligation, hypothetical in the two post-increment reads `decode_run`
consults. `decoderDecode` below turns one of these back into the plain `Runs` fact
`decoderRegisterWriteStep` and the retirement lemmas want. -/
abbrev DecodeAfterIncrement (state : State) (word : BitVec 32) (inst : instruction) : Prop :=
  (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine →
    ∀ mseccfgBits, (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg =
        some mseccfgBits →
      Runs (ext_decode word) (tryStepControlFlowAfterIncrement state)
        (tryStepControlFlowAfterIncrement state) inst

/-- Discharge a hypothetical decode obligation from the machine premise and the decoder's own
agreement. -/
theorem decoderDecodeOfDecoderAgree {instructionPcs : BitVec 64 → Prop}
    {margs : DecoderMachineArgs} {baseState state : State} {word : BitVec 32} {inst : instruction}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (decode : DecodeAfterIncrement state word inst) :
    Runs (ext_decode word) (tryStepControlFlowAfterIncrement state)
      (tryStepControlFlowAfterIncrement state) inst := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContextOfDecoderAgree machine agree
  exact decode privilege mseccfgBits mseccfgRead

/-- Discharge a hypothetical decode obligation from the machine premise. -/
theorem decoderDecode {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State} {word : BitVec 32} {inst : instruction}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree platformPreserved baseState state)
    (decode : DecodeAfterIncrement state word inst) :
    Runs (ext_decode word) (tryStepControlFlowAfterIncrement state)
      (tryStepControlFlowAfterIncrement state) inst :=
  decoderDecodeOfDecoderAgree machine (Agree.weaken (fun _ preserved => preserved.2) agree) decode

/-- Close a class lemma's `decode` obligation with no help from the call site: introduce the two
platform reads the obligation is stated under, then run the unchanged `decode_run`. -/
macro "decoder_decode" : tactic => `(tactic|
  (intro decodePrivilege decodeMseccfgBits decodeMseccfgRead; decode_run))

/-! ### Which agreement a fall-through class lemma needs

Each of the six register-writing classes uses its `agree` in exactly two places: the decode
(`decoderDecodeOfDecoderAgree`) and the retirement (`decoderRegisterWriteStepOfDecoderAgree`).
Neither reads `x1`, so each class is stated at the *weaker* `Agree decoderPreserved` — the
`…OfDecoderAgree` lemma is the real content — and the `Agree platformPreserved` name every existing
call site cites is a wrapper that weakens with `Agree.weaken (fun _ preserved => preserved.2)` and
delegates. Both entry points are therefore available everywhere: a block that still holds platform
agreement keeps its existing call unchanged, and a block whose `x1` an earlier `jalr` clobbered —
the wrapper epilogue, every `Agree decoderPreserved` site in the tree — can now call the class
lemma at all, which before it could not. -/

/-- One `ITYPE` (immediate ALU) instruction, retired, from the decoder's own agreement. -/
theorem decoderITypeStepOfDecoderAgree {instructionPcs : BitVec 64 → Prop}
    {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest} {source : BitVec 64}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8)
    (imm : BitVec 12) (rs rd : BitVec 5) (op : iop)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (readSource : Runs (rX_bits (.Regidx rs))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      source)
    (writeDest : Runs (wX_bits (.Regidx rd) (iTypeResult op imm source))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.ITYPE (imm, .Regidx rs, .Regidx rd, op)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderRegisterWriteStepOfDecoderAgree machine agree retiredPresent stepNo
    (BitVec.ofNat 64 pcNat) pcIn atPc
    _ _ _ _ (.ITYPE (imm, .Regidx rs, .Regidx rd, op)) dest value
    (fetchFileInstruction state pcNat b0 b1 b2 b3 code read0 read1 read2 read3 fits)
    baseEncoding (decoderDecodeOfDecoderAgree machine agree decode) notNextPc notHart notIncrement
    notRetired
    (execute_ITYPE_run _ _ imm (.Regidx rs) (.Regidx rd) op source readSource writeDest)

/-- One `ITYPE` (immediate ALU) instruction, retired. -/
theorem decoderITypeStep {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest} {source : BitVec 64}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree platformPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8)
    (imm : BitVec 12) (rs rd : BitVec 5) (op : iop)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (readSource : Runs (rX_bits (.Regidx rs))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      source)
    (writeDest : Runs (wX_bits (.Regidx rd) (iTypeResult op imm source))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.ITYPE (imm, .Regidx rs, .Regidx rd, op)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderITypeStepOfDecoderAgree machine (Agree.weaken (fun _ preserved => preserved.2) agree)
    retiredPresent code stepNo pcNat b0 b1 b2 b3 imm rs rd op atPc readSource writeDest pcIn
    read0 read1 read2 read3 fits decode baseEncoding notNextPc notHart notIncrement notRetired

/-- One `SHIFTIOP` (immediate shift) instruction, retired, from the decoder's own agreement. -/
theorem decoderShiftIopStepOfDecoderAgree {instructionPcs : BitVec 64 → Prop}
    {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest} {source : BitVec 64}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8)
    (shamt : BitVec 6) (rs rd : BitVec 5) (op : sop)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (readSource : Runs (rX_bits (.Regidx rs))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      source)
    (writeDest : Runs (wX_bits (.Regidx rd) (shiftIopResult op shamt source))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.SHIFTIOP (shamt, .Regidx rs, .Regidx rd, op)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderRegisterWriteStepOfDecoderAgree machine agree retiredPresent stepNo
    (BitVec.ofNat 64 pcNat) pcIn atPc
    _ _ _ _ (.SHIFTIOP (shamt, .Regidx rs, .Regidx rd, op)) dest value
    (fetchFileInstruction state pcNat b0 b1 b2 b3 code read0 read1 read2 read3 fits)
    baseEncoding (decoderDecodeOfDecoderAgree machine agree decode) notNextPc notHart notIncrement
    notRetired
    (execute_SHIFTIOP_run _ _ shamt (.Regidx rs) (.Regidx rd) op source readSource writeDest)

/-- One `SHIFTIOP` (immediate shift) instruction, retired. -/
theorem decoderShiftIopStep {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest} {source : BitVec 64}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree platformPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8)
    (shamt : BitVec 6) (rs rd : BitVec 5) (op : sop)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (readSource : Runs (rX_bits (.Regidx rs))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      source)
    (writeDest : Runs (wX_bits (.Regidx rd) (shiftIopResult op shamt source))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.SHIFTIOP (shamt, .Regidx rs, .Regidx rd, op)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderShiftIopStepOfDecoderAgree machine (Agree.weaken (fun _ preserved => preserved.2) agree)
    retiredPresent code stepNo pcNat b0 b1 b2 b3 shamt rs rd op atPc readSource writeDest pcIn
    read0 read1 read2 read3 fits decode baseEncoding notNextPc notHart notIncrement notRetired

/-- One `RTYPE` (register ALU) instruction, retired, from the decoder's own agreement. -/
theorem decoderRTypeStepOfDecoderAgree {instructionPcs : BitVec 64 → Prop}
    {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest}
    {source1 source2 : BitVec 64}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8)
    (rs2 rs1 rd : BitVec 5) (op : rop)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (readSource1 : Runs (rX_bits (.Regidx rs1))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      source1)
    (readSource2 : Runs (rX_bits (.Regidx rs2))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      source2)
    (writeDest : Runs (wX_bits (.Regidx rd) (rTypeResult op source1 source2))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, op)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderRegisterWriteStepOfDecoderAgree machine agree retiredPresent stepNo
    (BitVec.ofNat 64 pcNat) pcIn atPc
    _ _ _ _ (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, op)) dest value
    (fetchFileInstruction state pcNat b0 b1 b2 b3 code read0 read1 read2 read3 fits)
    baseEncoding (decoderDecodeOfDecoderAgree machine agree decode) notNextPc notHart notIncrement
    notRetired
    (execute_RTYPE_run _ _ (.Regidx rs2) (.Regidx rs1) (.Regidx rd) op source1 source2
      readSource1 readSource2 writeDest)

/-- One `RTYPE` (register ALU) instruction, retired. -/
theorem decoderRTypeStep {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest}
    {source1 source2 : BitVec 64}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree platformPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8)
    (rs2 rs1 rd : BitVec 5) (op : rop)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (readSource1 : Runs (rX_bits (.Regidx rs1))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      source1)
    (readSource2 : Runs (rX_bits (.Regidx rs2))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      source2)
    (writeDest : Runs (wX_bits (.Regidx rd) (rTypeResult op source1 source2))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, op)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderRTypeStepOfDecoderAgree machine (Agree.weaken (fun _ preserved => preserved.2) agree)
    retiredPresent code stepNo pcNat b0 b1 b2 b3 rs2 rs1 rd op atPc readSource1 readSource2
    writeDest pcIn read0 read1 read2 read3 fits decode baseEncoding notNextPc notHart notIncrement
    notRetired

/-- One `AUIPC` instruction, retired, from the decoder's own agreement. Its source is the
architectural `PC`, so the read premise is discharged from the caller's `atPc` rather than from a
general-purpose register. -/
theorem decoderAuipcStepOfDecoderAgree {instructionPcs : BitVec 64 → Prop}
    {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8) (imm : BitVec 20) (rd : BitVec 5)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (writeDest : Runs (wX_bits (.Regidx rd)
        (BitVec.ofNat 64 pcNat + sign_extend (m := 64) (imm ++ 0x000#12)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.UTYPE (imm, .Regidx rd, .AUIPC)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderRegisterWriteStepOfDecoderAgree machine agree retiredPresent stepNo
    (BitVec.ofNat 64 pcNat) pcIn atPc
    _ _ _ _ (.UTYPE (imm, .Regidx rd, .AUIPC)) dest value
    (fetchFileInstruction state pcNat b0 b1 b2 b3 code read0 read1 read2 read3 fits)
    baseEncoding (decoderDecodeOfDecoderAgree machine agree decode) notNextPc notHart notIncrement
    notRetired
    (execute_UTYPE_auipc_run _ _ imm (.Regidx rd) (BitVec.ofNat 64 pcNat)
      (readReg_run _ _ _ (decoderExecuteState_get? atPc)) writeDest)

/-- One `AUIPC` instruction, retired. Its source is the architectural `PC`, so the read premise is
discharged from the caller's `atPc` rather than from a general-purpose register. -/
theorem decoderAuipcStep {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree platformPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8) (imm : BitVec 20) (rd : BitVec 5)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (writeDest : Runs (wX_bits (.Regidx rd)
        (BitVec.ofNat 64 pcNat + sign_extend (m := 64) (imm ++ 0x000#12)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.UTYPE (imm, .Regidx rd, .AUIPC)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderAuipcStepOfDecoderAgree machine (Agree.weaken (fun _ preserved => preserved.2) agree)
    retiredPresent code stepNo pcNat b0 b1 b2 b3 imm rd atPc writeDest pcIn read0 read1 read2 read3
    fits decode baseEncoding notNextPc notHart notIncrement notRetired

/-- One `LUI` instruction, retired, from the decoder's own agreement. It reads nothing. -/
theorem decoderLuiStepOfDecoderAgree {instructionPcs : BitVec 64 → Prop}
    {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8) (imm : BitVec 20) (rd : BitVec 5)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (writeDest : Runs (wX_bits (.Regidx rd) (sign_extend (m := 64) (imm ++ 0x000#12)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.UTYPE (imm, .Regidx rd, .LUI)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderRegisterWriteStepOfDecoderAgree machine agree retiredPresent stepNo
    (BitVec.ofNat 64 pcNat) pcIn atPc
    _ _ _ _ (.UTYPE (imm, .Regidx rd, .LUI)) dest value
    (fetchFileInstruction state pcNat b0 b1 b2 b3 code read0 read1 read2 read3 fits)
    baseEncoding (decoderDecodeOfDecoderAgree machine agree decode) notNextPc notHart notIncrement
    notRetired
    (execute_UTYPE_lui_run _ _ imm (.Regidx rd) writeDest)

/-- One `LUI` instruction, retired. It reads nothing. -/
theorem decoderLuiStep {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree platformPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8) (imm : BitVec 20) (rd : BitVec 5)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (writeDest : Runs (wX_bits (.Regidx rd) (sign_extend (m := 64) (imm ++ 0x000#12)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.UTYPE (imm, .Regidx rd, .LUI)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderLuiStepOfDecoderAgree machine (Agree.weaken (fun _ preserved => preserved.2) agree)
    retiredPresent code stepNo pcNat b0 b1 b2 b3 imm rd atPc writeDest pcIn read0 read1 read2 read3
    fits decode baseEncoding notNextPc notHart notIncrement notRetired

/-- One `LOAD` of any width and signedness, retired. Only the address and data reasoning is left to
the caller; the fetch, decode and retirement are the same as for the ALU classes.

`width` and `isUnsigned` stay parameters rather than being fixed per mnemonic because
`execute_LOAD_run` is already width-polymorphic: the only width-dependent obligation is
`widthFits`, which `decide`s. So unlike the stores below this class needs no generated family, and
`decoderLhuStep` is the `true`/`2` instance rather than a sibling lemma. -/
theorem decoderLoadStepOfDecoderAgree {instructionPcs : BitVec 64 → Prop}
    {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8) (imm : BitVec 12) (rs rd : BitVec 5)
    (isUnsigned : Bool) (width : Nat) (data : BitVec (8 * width))
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (readMemory : Runs (vmem_read (.Regidx rs) (sign_extend (m := 64) imm) width
        (MemoryAccessType.Load mem_payload.Data) false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (.Ok data))
    (writeDest : Runs (wX_bits (.Regidx rd) (extend_value isUnsigned data))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.LOAD (imm, .Regidx rs, .Regidx rd, isUnsigned, width)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (widthFits : (width ≤b LeanRV64DExecutable.Functions.xlen_bytes) = true := by decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderRegisterWriteStepOfDecoderAgree machine agree retiredPresent stepNo
    (BitVec.ofNat 64 pcNat) pcIn atPc
    _ _ _ _ (.LOAD (imm, .Regidx rs, .Regidx rd, isUnsigned, width)) dest value
    (fetchFileInstruction state pcNat b0 b1 b2 b3 code read0 read1 read2 read3 fits)
    baseEncoding (decoderDecodeOfDecoderAgree machine agree decode) notNextPc notHart notIncrement
    notRetired
    (execute_LOAD_run _ _ imm (.Regidx rs) (.Regidx rd) isUnsigned width data widthFits
      readMemory writeDest)

/-- One `LOAD` of any width and signedness, retired. See `decoderLoadStepOfDecoderAgree`. -/
theorem decoderLoadStep {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree platformPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8) (imm : BitVec 12) (rs rd : BitVec 5)
    (isUnsigned : Bool) (width : Nat) (data : BitVec (8 * width))
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (readMemory : Runs (vmem_read (.Regidx rs) (sign_extend (m := 64) imm) width
        (MemoryAccessType.Load mem_payload.Data) false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (.Ok data))
    (writeDest : Runs (wX_bits (.Regidx rd) (extend_value isUnsigned data))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.LOAD (imm, .Regidx rs, .Regidx rd, isUnsigned, width)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (widthFits : (width ≤b LeanRV64DExecutable.Functions.xlen_bytes) = true := by decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderLoadStepOfDecoderAgree machine (Agree.weaken (fun _ preserved => preserved.2) agree)
    retiredPresent code stepNo pcNat b0 b1 b2 b3 imm rs rd isUnsigned width data atPc readMemory
    writeDest pcIn read0 read1 read2 read3 fits decode baseEncoding widthFits notNextPc notHart
    notIncrement notRetired

/-- One `lhu` (unsigned halfword load), retired, from the decoder's own agreement:
`decoderLoadStepOfDecoderAgree` at `isUnsigned = true`, `width = 2`. -/
theorem decoderLhuStepOfDecoderAgree {instructionPcs : BitVec 64 → Prop}
    {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest} {data : BitVec 16}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8) (imm : BitVec 12) (rs rd : BitVec 5)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (readMemory : Runs (vmem_read (.Regidx rs) (sign_extend (m := 64) imm) 2
        (MemoryAccessType.Load mem_payload.Data) false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (.Ok data))
    (writeDest : Runs (wX_bits (.Regidx rd) (extend_value true data))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.LOAD (imm, .Regidx rs, .Regidx rd, true, 2)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderLoadStepOfDecoderAgree machine agree retiredPresent code stepNo pcNat b0 b1 b2 b3 imm rs rd
    true 2 data atPc readMemory writeDest pcIn read0 read1 read2 read3 fits decode baseEncoding
    (by decide) notNextPc notHart notIncrement notRetired

/-- One `lhu` (unsigned halfword load), retired: `decoderLoadStep` at `isUnsigned = true`,
`width = 2`. Kept as its own name because sixteen sites already cite it. -/
theorem decoderLhuStep {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State} {dest : Register} {value : RegisterType dest} {data : BitVec 16}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree platformPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8) (imm : BitVec 12) (rs rd : BitVec 5)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (readMemory : Runs (vmem_read (.Regidx rs) (sign_extend (m := 64) imm) 2
        (MemoryAccessType.Load mem_payload.Data) false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (.Ok data))
    (writeDest : Runs (wX_bits (.Regidx rd) (extend_value true data))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 pcNat)).regs.insert dest value } ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.LOAD (imm, .Regidx rs, .Regidx rd, true, 2)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (notNextPc : dest ≠ nextPC := by decide) (notHart : dest ≠ hart_state := by decide)
    (notIncrement : dest ≠ minstret_increment := by decide)
    (notRetired : dest ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired dest value) false :=
  decoderLhuStepOfDecoderAgree machine (Agree.weaken (fun _ preserved => preserved.2) agree)
    retiredPresent code stepNo pcNat b0 b1 b2 b3 imm rs rd atPc readMemory writeDest pcIn read0
    read1 read2 read3 fits decode baseEncoding notNextPc notHart notIncrement notRetired

/-! ## Stores

A store writes memory rather than a register, so it retires through `tryStepFallThroughRetires`
directly and not through `decoderRegisterWriteStep`. Three things are then class data instead of the
single destination write: the base register read, the data register read, and the translated
destination address.

The class is split in three because the three delivered execute contracts are:
`execute_STORE_byte_run` (width 1), `execute_STORE_word_aligned_run` (width 4) and
`execute_STORE_dword_run` (width 8) — the generated `vmem_write` unfolding is width-specific, so
there is no width-polymorphic contract to specialise the way `execute_LOAD_run` is. Everything
*else* is width-generic, and is proved once as `decoderStoreAccess` (the machine side) and
`decoderStoreStepOfExecute` (the retirement side); the three class lemmas are generated from a table
over (width, stored payload, execute contract) so they cannot drift apart.

Like the control transfers below, and unlike the fall-through classes above, these take
`Agree decoderPreserved`: a wrapper store runs after the prologue's `jalr` has already clobbered
`x1`, so `platformPreserved` is not available at the call site. -/

/-- Exact post-state of a retired store: the memory write at the state `execute` runs in, then the
`try_step` tick and retired-counter writes. This is the shape `storeRetirement_writes` and
`storeRetirement_mem_writes` are already stated at, so every `*AfterDwordStore` /
`*AfterStatusStore` / `*AfterContextStore` successor state in the tree is this definition at a fixed
width and address, and keeps its existing frame lemmas. -/
def afterMemoryWrite (state : State) (pc retired : BitVec 64) (address : Nat) {width : Nat}
    (value : BitVec (8 * width)) : State :=
  tryStepControlFlowAfterRetired
    (afterWriteBytes (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      address value)
    (Sail.BitVec.addInt pc 4) retired

/-- `execute_STORE_byte_run` with the width-one alignment premise accepted and ignored. A byte
access is unconditionally aligned, so the delivered contract does not ask for it — but the class
lemma still has to *state* it, because `machine.dataAccess.store` demands the `physaddr` form at
every width. Accepting it here is what makes the three width contracts one signature, which is what
lets the class lemmas below be generated from a table rather than written out three times. No
width-one site pays for it: at width one the premise's autoParam closes by `simp`. -/
private theorem execute_STORE_byte_aligned_run (s s' : State) (rs2 rs1 : regidx) (imm : BitVec 12)
    (dstBits mstatusBits dataBits : BitVec 64)
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (dataReg : Runs (rX_bits rs2) s s dataBits)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm)
        (MemoryAccessType.Store mem_payload.Data) 1)
      s s (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)))
    (_aligned : is_aligned_vaddr (virtaddr.Virtaddr dstBits) 1 = true)
    (physAccess : Runs (phys_access_check (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr dstBits) 1 false)
      s s none)
    (noMMIO : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 1) s s false)
    (hwrite : Runs (PreSail.writeBytes (n := 1) dstBits.toNat
      (Sail.BitVec.extractLsb dataBits 7 0)) s s' true) :
    Runs (execute_STORE imm rs2 rs1 1) s s' (.Retire_Success ()) :=
  execute_STORE_byte_run s s' rs2 rs1 imm dstBits mstatusBits dataBits mstatusRead privRead
    mprvZero dataReg addrReg physAccess noMMIO hwrite

/-- Everything a store's `execute` contract needs from the machine premise, at the state `execute`
runs in: the two control-register reads it checks, the translated destination address, and the two
permission facts from `machine.dataAccess`. Width-generic — only `allowed` and `aligned` mention the
width — which is why the three class lemmas below share it verbatim. -/
theorem decoderStoreAccess {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (pc : BitVec 64) (rs1 : BitVec 5) (imm : BitVec 12) (width : Nat)
    (baseBits target : BitVec 64)
    (readBase : Runs (rX_bits (.Regidx rs1))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) baseBits)
    (targetEq : baseBits + sign_extend (m := 64) imm = target)
    (allowed : DecoderAccessRange DecoderWritableByte target width)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr target) width = true) :
    ∃ mstatusBits,
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? mstatus =
          some mstatusBits ∧
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get?
            cur_privilege = some Privilege.Machine ∧
        _get_Mstatus_MPRV mstatusBits = 0#1 ∧
        Runs (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm)
            (MemoryAccessType.Store mem_payload.Data) width)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
          (.Ext_DataAddr_OK (virtaddr.Virtaddr target)) ∧
        Runs (phys_access_check (MemoryAccessType.Store mem_payload.Data)
            page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr target) width false)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) none ∧
        Runs (within_mmio_writable (physaddr.Physaddr target) width)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) false := by
  subst targetEq
  obtain ⟨mstatusBits, mstatusRead, mprvDisabled⟩ := machine.mstatus
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := machine.mseccfg
  have executeAgree : Agree decoderPreserved baseState
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) :=
    agree.trans (Agree.weaken (fun _ preserved => preserved.2) (agree_stepPremiseState state pc))
  have mstatusAtExecute :=
    (executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead
  have privilege :=
    (executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      machine.normal.2.1
  obtain ⟨physical, storeNoMMIO⟩ :=
    machine.dataAccess.store _ _ width executeAgree allowed
      (by simpa [is_aligned_paddr, is_aligned_vaddr] using aligned)
  exact ⟨mstatusBits, mstatusAtExecute, privilege, mprvDisabled,
    get_transformed_data_addr_machine_store_run _ (.Regidx rs1) width baseBits
      (sign_extend (m := 64) imm) mstatusBits mseccfgBits readBase mstatusAtExecute privilege
      mprvDisabled
      ((executeAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead)
      pmmDisabled,
    physical, storeNoMMIO⟩

/-- The retirement side of a store step, with the class's `execute` contract abstracted. This is the
store analogue of `decoderRegisterWriteStep`: fetch, decode and the whole `try_step` postlude, with
the memory post-state described only by `afterWriteBytes`, whose `afterWriteBytes_regs` is what
discharges the three framing obligations without unfolding the byte list. -/
theorem decoderStoreStepOfExecute {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc : BitVec 64) (pcIn : DecoderFetchPc instructionPcs pc)
    (atPc : state.regs.get? PC = some pc)
    (byte0 byte1 byte2 byte3 : BitVec 8) (inst : instruction) (address width : Nat)
    (payload : BitVec (8 * width))
    (fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      byte0 byte1 byte2 byte3)
    (baseEncoding : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) inst)
    (execute : Runs (execute inst)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (afterWriteBytes (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
        address payload)
      (.Retire_Success ())) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterMemoryWrite state pc retired address payload) false := by
  obtain ⟨_, platform⟩ :=
    decoderStepPlatform_of_decoderAgree machine agree pc atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, fetchNoMMIO, fetched, interrupts, notExpected, -, -⟩ := platform
  obtain ⟨retired, inhibit, config, hartRead, inhibitRead, configRead, notInhibited,
    machineEnabled, retiredRead⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal agree retiredPresent
  have regs := afterWriteBytes_regs
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) address payload
  exact ⟨retired, tryStepFallThroughRetires stepNo state _ pc retired inhibit config
    byte0 byte1 byte2 byte3 inst fetch fetchNoMMIO fetched interrupts baseEncoding decode
    notExpected execute
    (by rw [regs]; simp [coreControlFlowNextState])
    (by rw [regs]; simp [coreControlFlowNextState, Std.ExtDHashMap.get?_insert])
    (by rw [regs]; simp [coreControlFlowNextState, Std.ExtDHashMap.get?_insert])
    (by rw [regs]; simp [coreControlFlowNextState, Std.ExtDHashMap.get?_insert])
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead⟩

/-- Generate one store class lemma from its width, the expression for the bytes it stores, and the
delivered execute contract at that width. Follows `gen_rx_run` / `gen_wx_run`: the table below is
the whole per-width difference, and the shared statement exists once.

`storedData` is the caller's own binder for the value in the data register, so the payload
expression in the table can mention it. -/
macro "gen_store_step" width:num " ↦ " storedData:ident ", " payload:term ", " executeRun:ident ", "
    name:ident : command =>
  `(theorem $name {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
      {baseState state : State}
      (machine : DecoderMachinePre instructionPcs margs baseState)
      (agree : Agree decoderPreserved baseState state)
      (retiredPresent : RetiredCounterPresent state)
      (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
      (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8) (imm : BitVec 12) (rs2 rs1 : BitVec 5)
      (baseBits $storedData target : BitVec 64)
      (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
      (readBase : Runs (rX_bits (.Regidx rs1))
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
        baseBits)
      (readData : Runs (rX_bits (.Regidx rs2))
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
        $storedData)
      (targetEq : baseBits + sign_extend (m := 64) imm = target)
      (allowed : DecoderAccessRange DecoderWritableByte target $width)
      (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
      (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
      (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
      (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
      (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
      (fits : pcNat < 2 ^ 64 := by decide)
      (decode : DecodeAfterIncrement state
          (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
            (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
          (.STORE (imm, .Regidx rs2, .Regidx rs1, $width)) := by decoder_decode)
      (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
        unfold BaseInstructionEncoding; decide)
      (aligned : is_aligned_vaddr (virtaddr.Virtaddr target) $width = true := by
        first | assumption | simp [is_aligned_vaddr]) :
      ∃ retired, Runs (try_step stepNo false) state
        (afterMemoryWrite state (BitVec.ofNat 64 pcNat) retired target.toNat
          (width := $width) $payload) false := by
    obtain ⟨mstatusBits, mstatusRead, privilege, mprvDisabled, addressRun, physical, noMMIO⟩ :=
      decoderStoreAccess machine agree (BitVec.ofNat 64 pcNat) rs1 imm $width baseBits target
        readBase targetEq allowed aligned
    exact decoderStoreStepOfExecute machine agree retiredPresent stepNo (BitVec.ofNat 64 pcNat)
      pcIn atPc _ _ _ _ (.STORE (imm, .Regidx rs2, .Regidx rs1, $width)) target.toNat $width
      $payload (fetchFileInstruction state pcNat b0 b1 b2 b3 code read0 read1 read2 read3 fits)
      baseEncoding (decoderDecodeOfDecoderAgree machine agree decode)
      ($executeRun _ _ (.Regidx rs2) (.Regidx rs1) imm target mstatusBits $storedData mstatusRead
        privilege mprvDisabled readData addressRun aligned physical noMMIO
        (writeBytes_run_exact _ target.toNat $payload)))

-- `sb`, `sh`, `sw` and `sd`: one retired store each, at the widths the tree emits.
gen_store_step 1 ↦ data, (Sail.BitVec.extractLsb data 7 0), execute_STORE_byte_aligned_run,
  decoderStoreByteStep

gen_store_step 2 ↦ data, (Sail.BitVec.extractLsb data 15 0), execute_STORE_half_aligned_run,
  decoderStoreHalfStep

gen_store_step 4 ↦ data, (Sail.BitVec.extractLsb data 31 0), execute_STORE_word_aligned_run,
  decoderStoreWordStep

gen_store_step 8 ↦ data, data, execute_STORE_dword_run, decoderStoreDwordStep

/-! ## Branches

A not-taken `BTYPE` has no register-writing retirement to reuse, so this is both the generic
retirement (the analogue of `decoderRegisterWriteStep`) and the class lemma. The post-state is
written out rather than named: each call site already owns a `…BranchAfter` definition pinning the
concrete successor address, and closes the gap with `simpa [thatDefinition]`. -/

/-- One conditional branch that falls through, retired. -/
theorem decoderBranchNotTakenStep {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree platformPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8)
    (imm : BitVec 13) (rs2 rs1 : BitVec 5) (op : bop)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (condition : Runs (bTypeTaken (.Regidx rs2) (.Regidx rs1) op)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      false)
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.BTYPE (imm, .Regidx rs2, .Regidx rs1, op)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
        (Sail.BitVec.addInt (BitVec.ofNat 64 pcNat) 4) retired) false := by
  have decodeRuns := decoderDecode machine agree decode
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine agree (BitVec.ofNat 64 pcNat) atPc
    pcIn _ _ _ _ (fetchFileInstruction state pcNat b0 b1 b2 b3 code read0 read1 read2 read3 fits)
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal agree retiredPresent
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  exact ⟨retired, tryStepBranchNotTakenRetires stepNo state (BitVec.ofNat 64 pcNat) retired
    imm (.Regidx rs2) (.Regidx rs1) op inhibit config _ _ _ _ fetch noMMIO fetched interrupts
    baseEncoding decodeRuns notExpected condition hartRead inhibitRead configRead notInhibited
    machineEnabled retiredRead⟩

/-! ## Control transfers

`jal`, `jalr`, `ret` and a taken branch retire through `tryStepJRetires` / `tryStepJalrCallRetires`
/ `tryStepRetRetires` / `tryStepBranchTakenRetires` rather than
`tryStepFallThroughWriteRegRetires`, so none of them can go through `decoderRegisterWriteStep`. Each
of the four lemmas below is therefore both the decoder adapter and the class lemma, like
`decoderBranchNotTakenStep`.

They differ from the fall-through classes in two further respects.

* They take `Agree decoderPreserved`, not `Agree platformPreserved`. That is the *weaker* agreement
  (`decoderPreserved r = r ≠ x1 ∧ platformPreserved r`, so it constrains fewer registers), and it is
  all a call site has once a `jalr` earlier in the block has clobbered `x1`. `Agree.refl` and the
  platform-agreement sites still apply, so this loses nothing.
* Their premise lists include the two facts a control transfer needs and a fall-through does not: the
  landing-pad update at the execute state (`decoderUpdateElp`, from `machine.landingPad`) and the
  `Ext_Zca` read (`decoderZcaEnabled`, from `machine.normal`'s `misa`). Both are derivable from the
  machine premise alone, so both are absorbed rather than exposed.

The transfer target is an explicit `BitVec 64` argument tied to the computed address by an
`autoParam` that is `decide`d at concrete sites and `assumption`-ed where the target is symbolic (a
`ret`'s return address). Substituting it is what lets a call site's post-state definition — which
names the concrete successor — match the conclusion directly. -/

/-- The `Ext_Zca` read every control-transfer retirement wants, at the state `execute` runs in.
The enabled bit is existential: no caller inspects it, they only need *some* run. -/
theorem decoderZcaEnabled {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State} (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state) (pc : BitVec 64) :
    ∃ enabled, Runs (currentlyEnabled extension.Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) enabled := by
  obtain ⟨misaBits, misaRead, -⟩ : ∃ bits,
      baseState.regs.get? misa = some bits ∧ Sail.BitVec.access bits 12 = 1#1 := by
    have normalMisa := machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match read : baseState.regs.get? misa with
    | none => simp [read] at normalMisa
    | some bits => exact ⟨bits, rfl, by simpa [read] using normalMisa⟩
  exact ⟨_, currentlyEnabledZca_run_atStepPremise state pc misaBits
    ((agree misa (by simp [decoderPreserved, platformPreserved])).trans misaRead)⟩

/-- The landing-pad premise of a `jalr`-shaped transfer, at the state `execute` runs in. -/
theorem decoderUpdateElp {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State} (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state) (pc : BitVec 64) (rs1 : regidx) :
    Runs (update_elp_state rs1)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) () :=
  machine.landingPad _ rs1 trivial
    (Agree.trans agree
      (Agree.weaken (fun _ preserved => preserved.2) (agree_stepPremiseState state pc)))

/-- The pre-execute `nextPC`, which a call writes into its link register. -/
theorem decoderReturnAddress (state : State) (pc : BitVec 64) :
    Runs (get_next_pc ())
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (Sail.BitVec.addInt pc 4) :=
  get_next_pc_run _ _ (by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt pc 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp)

/-- One direct unconditional jump (`j target` — a `JAL` whose link register is `x0`, so the link
write is discarded), retired.

Unlike `jalr` this reads no general-purpose register: the target is `PC + sext imm`, so the only
class data is the immediate, and even the `PC` read is discharged from the caller's `atPc`, exactly
as `decoderAuipcStep` and `decoderBranchTakenStep` discharge theirs.

Every `JAL` the tree emits has `rd = x0`, so only the discarded-link form is provided. A linking
`jal` would be the same lemma over `tryStepJalCallRetires` instead of `tryStepJRetires`, with
`decoderJalrCallStep`'s link write and four link disequalities added; that retirement exists in
`RiscV/Step/Call.lean`, so it is a thin sibling whenever a site first needs it. -/
theorem decoderJalStep {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8) (imm : BitVec 21) (targetPc : BitVec 64)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.JAL (imm, zreg)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (target : BitVec.ofNat 64 pcNat + sign_extend (m := 64) imm = targetPc := by
      first | assumption | decide)
    (targetAligned : Sail.BitVec.access (BitVec.ofNat 64 pcNat + sign_extend (m := 64) imm) 0 =
      0#1 := by first | assumption | decide)
    (targetBit1 : Sail.BitVec.access (BitVec.ofNat 64 pcNat + sign_extend (m := 64) imm) 1 =
      0#1 := by first | assumption | decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
          targetPc)
        targetPc retired) false := by
  subst target
  have decodeRuns := decoderDecodeOfDecoderAgree machine agree decode
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform_of_decoderAgree machine agree
    (BitVec.ofNat 64 pcNat) atPc pcIn _ _ _ _
    (fetchFileInstruction state pcNat b0 b1 b2 b3 code read0 read1 read2 read3 fits)
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, hartRead, inhibitRead, configRead, notInhibited,
    machineEnabled, retiredRead⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal agree retiredPresent
  obtain ⟨zcaEnabled, zca⟩ := decoderZcaEnabled machine agree (BitVec.ofNat 64 pcNat)
  exact ⟨retired, tryStepJRetires stepNo state (BitVec.ofNat 64 pcNat) (BitVec.ofNat 64 pcNat)
    retired imm inhibit config _ _ _ _ (Sail.BitVec.addInt (BitVec.ofNat 64 pcNat) 4) zcaEnabled
    fetch noMMIO fetched interrupts baseEncoding decodeRuns notExpected
    (decoderReturnAddress state (BitVec.ofNat 64 pcNat))
    (readReg_run _ PC _ (decoderExecuteState_get? atPc)) targetAligned targetBit1 zca hartRead
    inhibitRead configRead notInhibited machineEnabled retiredRead⟩

/-- One register-based call (`jalr rd, imm(rs1)` with `rd ≠ x0`), retired. -/
theorem decoderJalrCallStep {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State} {linkReg : Register} {linkValue : RegisterType linkReg}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (source linkPc targetPc : BitVec 64)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (readSource : Runs (rX_bits (.Regidx rs1))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      source)
    (writeLink : Runs (wX_bits (.Regidx rd) linkPc)
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        targetPc)
      (callLinkState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
        targetPc linkReg linkValue) ())
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.JALR (imm, .Regidx rs1, .Regidx rd)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (link : Sail.BitVec.addInt (BitVec.ofNat 64 pcNat) 4 = linkPc := by
      first | assumption | decide)
    (target : Sail.BitVec.update (source + sign_extend (m := 64) imm) 0 0#1 = targetPc := by
      first | assumption | decide)
    (targetBit1 : Sail.BitVec.access (source + sign_extend (m := 64) imm) 1 = 0#1 := by
      first | assumption | decide)
    (linkNotNextPc : linkReg ≠ nextPC := by decide)
    (linkNotHart : linkReg ≠ hart_state := by decide)
    (linkNotIncrement : linkReg ≠ minstret_increment := by decide)
    (linkNotRetired : linkReg ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
          targetPc linkReg linkValue)
        targetPc retired) false := by
  subst link
  subst target
  have decodeRuns := decoderDecodeOfDecoderAgree machine agree decode
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform_of_decoderAgree machine agree
    (BitVec.ofNat 64 pcNat) atPc pcIn _ _ _ _
    (fetchFileInstruction state pcNat b0 b1 b2 b3 code read0 read1 read2 read3 fits)
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, hartRead, inhibitRead, configRead, notInhibited,
    machineEnabled, retiredRead⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal agree retiredPresent
  obtain ⟨zcaEnabled, zca⟩ := decoderZcaEnabled machine agree (BitVec.ofNat 64 pcNat)
  exact ⟨retired, tryStepJalrCallRetires stepNo state (BitVec.ofNat 64 pcNat) source retired
    (Sail.BitVec.addInt (BitVec.ofNat 64 pcNat) 4) imm (.Regidx rs1) (.Regidx rd) linkReg linkValue
    inhibit config _ _ _ _ zcaEnabled writeLink linkNotNextPc linkNotHart linkNotIncrement
    linkNotRetired fetch noMMIO fetched interrupts baseEncoding decodeRuns notExpected
    (decoderUpdateElp machine agree (BitVec.ofNat 64 pcNat) (.Regidx rs1))
    (decoderReturnAddress state (BitVec.ofNat 64 pcNat)) readSource targetBit1 zca hartRead
    inhibitRead configRead notInhibited machineEnabled retiredRead⟩

/-- One `ret` (`jalr x0, 0(rs1)`), retired. The link write is discarded, so unlike a call this
writes no general-purpose register; only the source read and the return address are class data. -/
theorem decoderRetStep {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8) (rs1 : BitVec 5) (source targetPc : BitVec 64)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (readSource : Runs (rX_bits (.Regidx rs1))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      source)
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.JALR (0#12, .Regidx rs1, .Regidx 0#5)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (target : Sail.BitVec.update source 0 0#1 = targetPc := by first | assumption | decide)
    (sourceBit1 : Sail.BitVec.access source 1 = 0#1 := by first | assumption | decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
          targetPc)
        targetPc retired) false := by
  subst target
  have decodeRuns := decoderDecodeOfDecoderAgree machine agree decode
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform_of_decoderAgree machine agree
    (BitVec.ofNat 64 pcNat) atPc pcIn _ _ _ _
    (fetchFileInstruction state pcNat b0 b1 b2 b3 code read0 read1 read2 read3 fits)
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, hartRead, inhibitRead, configRead, notInhibited,
    machineEnabled, retiredRead⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal agree retiredPresent
  obtain ⟨zcaEnabled, zca⟩ := decoderZcaEnabled machine agree (BitVec.ofNat 64 pcNat)
  exact ⟨retired, tryStepRetRetires stepNo state (BitVec.ofNat 64 pcNat) retired (.Regidx rs1)
    (Sail.BitVec.addInt (BitVec.ofNat 64 pcNat) 4) source inhibit config _ _ _ _ zcaEnabled
    fetch noMMIO fetched interrupts baseEncoding decodeRuns notExpected
    (decoderUpdateElp machine agree (BitVec.ofNat 64 pcNat) (.Regidx rs1))
    (decoderReturnAddress state (BitVec.ofNat 64 pcNat)) readSource sourceBit1 zca hartRead
    inhibitRead configRead notInhibited machineEnabled retiredRead⟩

/-- One conditional branch that is taken, retired. Its `PC` read is discharged from the caller's
`atPc`, exactly as `decoderAuipcStep` discharges `AUIPC`'s. -/
theorem decoderBranchTakenStep {instructionPcs : BitVec 64 → Prop} {margs : DecoderMachineArgs}
    {baseState state : State}
    (machine : DecoderMachinePre instructionPcs margs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo pcNat : Nat) (b0 b1 b2 b3 : UInt8)
    (imm : BitVec 13) (rs2 rs1 : BitVec 5) (op : bop) (targetPc : BitVec 64)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (condition : Runs (bTypeTaken (.Regidx rs2) (.Regidx rs1) op)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      true)
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pcNat) := by decoder_fetch_pc)
    (read0 : Artifacts.programImage.readFileByte? pcNat = some b0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pcNat + 1) = some b1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pcNat + 2) = some b2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pcNat + 3) = some b3 := by native_decide)
    (fits : pcNat < 2 ^ 64 := by decide)
    (decode : DecodeAfterIncrement state
        (fetchWord (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
          (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat))
        (.BTYPE (imm, .Regidx rs2, .Regidx rs1, op)) := by decoder_decode)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 b0.toNat) := by
      unfold BaseInstructionEncoding; decide)
    (target : BitVec.ofNat 64 pcNat + sign_extend (m := 64) imm = targetPc := by
      first | assumption | decide)
    (targetAligned : Sail.BitVec.access (BitVec.ofNat 64 pcNat + sign_extend (m := 64) imm) 0 =
      0#1 := by first | assumption | decide)
    (targetBit1 : Sail.BitVec.access (BitVec.ofNat 64 pcNat + sign_extend (m := 64) imm) 1 =
      0#1 := by first | assumption | decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
          targetPc)
        targetPc retired) false := by
  subst target
  have decodeRuns := decoderDecodeOfDecoderAgree machine agree decode
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform_of_decoderAgree machine agree
    (BitVec.ofNat 64 pcNat) atPc pcIn _ _ _ _
    (fetchFileInstruction state pcNat b0 b1 b2 b3 code read0 read1 read2 read3 fits)
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, hartRead, inhibitRead, configRead, notInhibited,
    machineEnabled, retiredRead⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal agree retiredPresent
  obtain ⟨zcaEnabled, zca⟩ := decoderZcaEnabled machine agree (BitVec.ofNat 64 pcNat)
  exact ⟨retired, tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 pcNat)
    (BitVec.ofNat 64 pcNat) retired imm (.Regidx rs2) (.Regidx rs1) op inhibit config _ _ _ _
    zcaEnabled fetch noMMIO fetched interrupts baseEncoding decodeRuns notExpected condition
    (readReg_run _ PC _ (decoderExecuteState_get? atPc)) targetAligned targetBit1 zca hartRead
    inhibitRead configRead notInhibited machineEnabled retiredRead⟩

end BinaryFv.Zesu.MachineExecution
