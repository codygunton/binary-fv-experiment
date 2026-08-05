import BinaryFv.RiscV.Instruction.Execute.Arithmetic
import BinaryFv.RiscV.Instruction.Execute.Load
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.SentinelAssembly
import BinaryFv.Zesu.MachineExecution.DecodeTactic

/-!
# Shared Sail execution for register-writing fall-through instructions

This module contains the exact post-state and retirement bridge used by multiple concrete Zesu
machine proofs. It is independent of any particular compiled source function.
-/

namespace BinaryFv.Zesu.MachineExecution

namespace RegisterWriteStep

open BinaryFv BinaryFv.Binary BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open PreSail LeanRV64DExecutable.Functions Register

/-! ## The wrapper's own geometry, named once

`functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw`
is written out **189 times across 14 modules**, 173 of those occurrences occupying a line to
themselves; the exit predicate accounts for 46 more. Naming them here rather than per-module is
deliberate: the 14 consumers have **no import in common** — the intersection of their import sets is
empty, and only three of them reach any one candidate host — so an abbrev defined in any of them
would be invisible to the rest. This module is the floor they all sit above.

Both are `abbrev`, hence reducible, so a proof written against the spelled-out form still
elaborates unchanged; `decodeRawGeometry_transparent` below pins that rather than assuming it. -/
abbrev decodeRawExecutionPcs : BitVec 64 → Prop :=
  BinaryFv.RiscV.Elfling.functionInstanceExecutionPcs
    BinaryFv.Zesu.Elflings.Generated.generatedProgram
    BinaryFv.Zesu.Elflings.Generated.functionInstance_raw_decoder_root_zesu_decode_raw

abbrev decodeRawExit : BitVec 64 → Prop :=
  BinaryFv.RiscV.Elfling.functionInstanceExitPred
    BinaryFv.Zesu.Elflings.Generated.functionInstance_raw_decoder_root_zesu_decode_raw

/-- Regression: both abbrevs must stay definitionally transparent. If either stops being reducible,
every existing proof that spells the region out by hand breaks at once. -/
theorem decodeRawGeometry_transparent :
    decodeRawExecutionPcs =
      BinaryFv.RiscV.Elfling.functionInstanceExecutionPcs
        BinaryFv.Zesu.Elflings.Generated.generatedProgram
        BinaryFv.Zesu.Elflings.Generated.functionInstance_raw_decoder_root_zesu_decode_raw ∧
    decodeRawExit =
      BinaryFv.RiscV.Elfling.functionInstanceExitPred
        BinaryFv.Zesu.Elflings.Generated.functionInstance_raw_decoder_root_zesu_decode_raw :=
  ⟨rfl, rfl⟩

/-- Exact post-state of a register-writing fall-through instruction. -/
def afterRegisterWrite (state : State) (pc retired : BitVec 64) (destination : Register)
    (value : RegisterType destination) : State :=
  tryStepControlFlowAfterRetired
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
        destination value }
    (Sail.BitVec.addInt pc 4) retired

theorem afterRegisterWrite_agree_of {P : Register → Prop} {state : State}
    {pc retired : BitVec 64}
    {destination : Register} {value : RegisterType destination}
    (notDestination : ¬ P destination) (notPc : ¬ P PC) (notNextPc : ¬ P nextPC)
    (notIncrement : ¬ P minstret_increment) (notRetired : ¬ P minstret) :
    Agree P state (afterRegisterWrite state pc retired destination value) := by
  intro register preserved
  have different : destination ≠ register := by
    intro equal
    exact notDestination (equal ▸ preserved)
  have differentPc : PC ≠ register := by
    intro equal
    subst register
    exact notPc preserved
  have differentNextPc : nextPC ≠ register := by
    intro equal
    subst register
    exact notNextPc preserved
  have differentIncrement : minstret_increment ≠ register := by
    intro equal
    subst register
    exact notIncrement preserved
  have differentRetired : minstret ≠ register := by
    intro equal
    subst register
    exact notRetired preserved
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    different, differentPc, differentNextPc, differentIncrement, differentRetired]

theorem afterRegisterWrite_agree {state : State} {pc retired : BitVec 64}
    {destination : Register} {value : RegisterType destination}
    (notPreserved : ¬ platformPreserved destination) :
    Agree platformPreserved state (afterRegisterWrite state pc retired destination value) :=
  afterRegisterWrite_agree_of notPreserved (by simp [platformPreserved])
    (by simp [platformPreserved]) (by simp [platformPreserved]) (by simp [platformPreserved])

theorem afterRegisterWrite_register (state : State) (pc retired : BitVec 64)
    (destination register : Register) (value : RegisterType destination)
    (notDestination : destination ≠ register) (notPc : PC ≠ register)
    (notNextPc : nextPC ≠ register) (notIncrement : minstret_increment ≠ register)
    (notRetired : minstret ≠ register) :
    (afterRegisterWrite state pc retired destination value).regs.get? register =
      state.regs.get? register := by
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    notDestination, notPc, notNextPc, notIncrement, notRetired]

/-- The write set of a full register-writing retirement: the `try_step` bookkeeping, plus the
instruction's destination.

`destination` is a parameter, so it is kept as a separate `RegSet.only` rather than folded into a
closed set. That is what lets `RegSet.Disjoint.union` split a later disjointness obligation into a
fact about the bookkeeping — proved once per preserved predicate — and the single disequality about
the destination. Widening the destination into a closed over-approximation would look tempting and
is wrong: it strengthens the disjointness obligation into something false for `platformPreserved`,
which holds `x1`.

The proof is a repackaging of `afterRegisterWrite_register` and adds no machine reasoning; the
hypotheses that lemma already takes one at a time are exactly this set, enumerated. -/
theorem afterRegisterWrite_writes (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only destination)) state
      (afterRegisterWrite state pc retired destination value) :=
  fun r hr =>
    afterRegisterWrite_register state pc retired destination r value
      (fun h => hr (Or.inr h.symm))
      (fun h => hr (Or.inl (Or.inl h.symm)))
      (fun h => hr (Or.inl (Or.inr (Or.inl h.symm))))
      (fun h => hr (Or.inl (Or.inr (Or.inr (Or.inr h.symm)))))
      (fun h => hr (Or.inl (Or.inr (Or.inr (Or.inl h.symm)))))

theorem afterRegisterWrite_mem (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    (afterRegisterWrite state pc retired destination value).mem = state.mem := rfl

theorem afterRegisterWrite_retired_present (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    RetiredCounterPresent (afterRegisterWrite state pc retired destination value) := by
  refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]

theorem afterRegisterWrite_pc (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    (afterRegisterWrite state pc retired destination value).regs.get? PC =
      some (Sail.BitVec.addInt pc 4) := by
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    Std.ExtDHashMap.get?_insert]

theorem afterRegisterWrite_exitPlatform {state : State} {pc retired : BitVec 64}
    {destination : Register} {value : RegisterType destination} {nextPc : Nat}
    (notPreserved : ¬ platformPreserved destination) (platform : ExitPlatform state nextPc) :
    ExitPlatform (afterRegisterWrite state pc retired destination value) nextPc := by
  have code : Artifacts.programImage.fileBytesMatchMemory
      (afterRegisterWrite state pc retired destination value).mem := by
    simpa [afterRegisterWrite_mem] using platform.code
  exact exitPlatform_of_agree (afterRegisterWrite_agree notPreserved)
    (afterRegisterWrite_retired_present state pc retired destination value) code platform

theorem exitPlatform_of_executionState {before after : State} {pc : Nat}
    (agree : Agree platformPreserved before after) (retired : RetiredCounterPresent after)
    (memoryUnchanged : after.mem = before.mem) (platform : ExitPlatform before pc) :
    ExitPlatform after pc := by
  have code : Artifacts.programImage.fileBytesMatchMemory after.mem := by
    simpa [memoryUnchanged] using platform.code
  exact exitPlatform_of_agree agree retired code platform

/-- Platform facts needed by an ordinary retiring instruction. Unlike `ExitPlatform`, this does
not require `ra` to contain the runner's return sentinel: inline code neither returns nor reads it. -/
structure InstructionStepPlatform (state : State) (pc : Nat) : Prop where
  normal : NormalExecutionState state
  fetch : FetchBasePlatform state (BitVec.ofNat 64 pc)
  fetchNoMMIO : FetchMemoryNoMMIO state (BitVec.ofNat 64 pc)
  interrupts : InterruptDisabled state
  notExpected : LandingPadNotExpected state
  seccfgRead : ∃ v : BitVec 64, state.regs.get? Register.mseccfg = some v
  retired : RetiredCounterPresent state
  code : Artifacts.programImage.fileBytesMatchMemory state.mem

/-- Derive all common machine premises for one register-writing straight-line instruction. -/
theorem fallThroughRegisterWriteStepWithoutReturn (stepNo pcNat : Nat) (state : State)
    (byte0 byte1 byte2 byte3 : BitVec 8) (instruction : instruction)
    (destination : Register) (value : RegisterType destination)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (platform : InstructionStepPlatform state pcNat)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
      byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) instruction)
    (execute : Runs (execute instruction)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 pcNat)).regs.insert destination value }
      (.Retire_Success ()))
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired destination value) false := by
  obtain ⟨hartRead, privilege, satpRead, midelegRead, mieRead, mipRead, pmpcfgRead,
    pmpaddrRead, inhibitRead, configRead, elpRead, misaCase⟩ := platform.normal
  obtain ⟨retired, retiredRead⟩ := platform.retired
  have incrementAgree := agree_afterIncrement state
  have fetchPlatform := fetchBasePlatform_of_agree incrementAgree
    (pc_afterIncrement state (BitVec.ofNat 64 pcNat) atPc) platform.fetch.offPC
  have noMMIO := fetchMemoryNoMMIO_of_agree incrementAgree platform.fetchNoMMIO
  have interrupts := interruptDisabled_of_agree incrementAgree platform.interrupts
  have notExpected := landingPadNotExpected_of_agree incrementAgree platform.notExpected
  refine ⟨retired, ?_⟩
  exact tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 pcNat) retired 0 0
    byte0 byte1 byte2 byte3 instruction destination value fetchPlatform noMMIO bytes interrupts
    base decode notExpected execute destinationNotNextPc destinationNotHart
    destinationNotIncrement destinationNotRetired
    hartRead inhibitRead configRead (by decide) (by decide) retiredRead

/-- Compatibility wrapper for exported-function proofs whose runner-specific `ExitPlatform` also
pins the return sentinel. Inline code should use `fallThroughRegisterWriteStepWithoutReturn`. -/
theorem fallThroughRegisterWriteStep (stepNo pcNat : Nat) (state : State)
    (byte0 byte1 byte2 byte3 : BitVec 8) (instruction : instruction)
    (destination : Register) (value : RegisterType destination)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (platform : ExitPlatform state pcNat)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
      byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) instruction)
    (execute : Runs (execute instruction)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 pcNat)).regs.insert destination value }
      (.Retire_Success ()))
    (addressExcluded : FetchMMIOAddressExcluded (BitVec.ofNat 64 pcNat))
    (aligned : (BitVec.ofNat 64 pcNat).toNat % 4 = 0)
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired destination value) false := by
  obtain ⟨mstatusBits, mstatusRead⟩ := platform.mstatusRead
  have fetch : FetchBasePlatform state (BitVec.ofNat 64 pcNat) :=
    fetchBasePlatform_of_offPC atPc
      (fetchBasePlatformOffPC_of_normal platform.normal mstatusRead aligned platform.pmaAllows)
  have noMMIO : FetchMemoryNoMMIO state (BitVec.ofNat 64 pcNat) :=
    fetchMemoryNoMMIO_of_state_layout_excluded _ _ ⟨addressExcluded, platform.htifRead⟩
  have interrupts := interruptDisabled_of_normal platform.normal mstatusRead platform.meipRead
  exact fallThroughRegisterWriteStepWithoutReturn stepNo pcNat state byte0 byte1 byte2 byte3
    instruction destination value atPc
    { normal := platform.normal
      fetch := fetch
      fetchNoMMIO := noMMIO
      interrupts := interrupts
      notExpected := landingPadNotExpected_of_normal platform.normal
      seccfgRead := platform.seccfgRead
      retired := platform.retired
      code := platform.code }
    bytes base decode execute destinationNotNextPc destinationNotHart
    destinationNotIncrement destinationNotRetired

theorem fetchFileInstruction (state : State) (pc : Nat)
    (byte0 byte1 byte2 byte3 : UInt8)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3)
    (fits : pc < 2 ^ 64) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
      (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
      (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) := by
  have loadedAfter : Artifacts.programImage.fileBytesMatchMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc fits loadedAfter byte0 byte1 byte2 byte3
    read0 read1 read2 read3

/-- `fetchFileInstruction` with its four image lookups and its alignment check discharged
automatically, so a call site names only the address and the four instruction bytes.

The obligations are the same work either way, so this is a proof-size and vocabulary change, not a
build-time one — measured at 1.26s against 1.23s for the hand-written form, within noise. What it
removes is the five-argument tail `(by native_decide) (by native_decide) (by native_decide)
(by native_decide) (by decide)`, written out at 111 call sites across 13 files.

A wrong byte still fails, and fails informatively: `native_decide` reports the proposition false and
names the address and the byte the image actually holds. -/
theorem fetchInstruction (state : State) (pc : Nat) (byte0 byte1 byte2 byte3 : UInt8)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := by native_decide)
    (fits : pc < 2 ^ 64 := by decide) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
      (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
      (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) :=
  fetchFileInstruction state pc byte0 byte1 byte2 byte3 loaded read0 read1 read2 read3 fits

end RegisterWriteStep

end BinaryFv.Zesu.MachineExecution
