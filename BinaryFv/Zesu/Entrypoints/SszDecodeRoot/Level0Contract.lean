import BinaryFv.Zesu.MachineExecution.Level0MainSteps
import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level1Contracts
import BinaryFv.RiscV.Step.RegisterWrite

/-!
# Level 0 endpoint contract

This file composes the 24 instructions owned by `main` with the six immediate Level 1 contracts.
The first declarations establish the common execution region and the frame transports used after a
returning opaque call.
-/

namespace BinaryFv.Zesu

open BinaryFv.Specs.SSZ

open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.RiscV

/-- Every instruction selected at Level 0: parent-owned glue or one of its six opaque callees. -/
def MainExecutionPc (pc : BitVec 64) : Prop :=
  mainGluePcs pc ∨
  pcInRanges Elflings.readInputExecutionPcRanges pc ∨
  pcInRanges Elflings.allocatorGetExecutionPcRanges pc ∨
  DecodeExecutionPc pc ∨
  pcInRanges Elflings.writeSuccessExecutionPcRanges pc ∨
  pcInRanges Elflings.writeFailureExecutionPcRanges pc ∨
  pcInRanges Elflings.zkvmExitExecutionPcRanges pc

private theorem mainEntry_not_syscall : ¬ BareMetalHostTransitionPc Elflings.mainEntry := by
  unfold BareMetalHostTransitionPc
  native_decide

private theorem main14cb4_not_syscall : ¬ BareMetalHostTransitionPc 0x14cb4 := by
  unfold BareMetalHostTransitionPc
  native_decide

private theorem main14cb8_not_syscall : ¬ BareMetalHostTransitionPc 0x14cb8 := by
  unfold BareMetalHostTransitionPc
  native_decide

private theorem main14cbc_not_syscall : ¬ BareMetalHostTransitionPc 0x14cbc := by
  unfold BareMetalHostTransitionPc
  native_decide

private theorem main14cc0_not_syscall : ¬ BareMetalHostTransitionPc 0x14cc0 := by
  unfold BareMetalHostTransitionPc
  native_decide

private theorem main14cc4_not_syscall : ¬ BareMetalHostTransitionPc 0x14cc4 := by
  unfold BareMetalHostTransitionPc
  native_decide

private theorem main14cc8_not_syscall : ¬ BareMetalHostTransitionPc 0x14cc8 := by
  unfold BareMetalHostTransitionPc
  native_decide

private theorem main14cec_not_syscall : ¬ BareMetalHostTransitionPc 0x14cec := by
  unfold BareMetalHostTransitionPc
  native_decide

private theorem main14cf0_not_syscall : ¬ BareMetalHostTransitionPc 0x14cf0 := by
  unfold BareMetalHostTransitionPc
  native_decide

private theorem main14cf4_not_syscall : ¬ BareMetalHostTransitionPc 0x14cf4 := by
  unfold BareMetalHostTransitionPc
  native_decide

private theorem main14cf8_not_syscall : ¬ BareMetalHostTransitionPc 0x14cf8 := by
  unfold BareMetalHostTransitionPc
  native_decide

private theorem main14cfc_not_syscall : ¬ BareMetalHostTransitionPc 0x14cfc := by
  unfold BareMetalHostTransitionPc
  native_decide

private theorem mainGluePcs_14cfc : mainGluePcs 0x14cfc := by
  unfold mainGluePcs
  refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide

private theorem x10_not_instructionPreserved : ¬instructionPreserved x10 := by
  simp [instructionPreserved, platformPreserved]

private theorem sign_extend_zero_12_64 : sign_extend (m := 64) (0 : BitVec 12) = 0 := by
  native_decide

structure MainArgs where
  input : Array UInt8
  stackPointer : Nat
  returnAddress : Nat

inductive MainOutcome where
  | failure
  | success (decoded : ZesuDecodedResult)

/-- SSZ/RLP meaning of the complete endpoint. The exception list is fixed to `knownBugs` at the
public theorem; this parameter only makes that dependency syntactically visible. -/
def MainMeaningModulo (bugs : List KnownBug) (args : MainArgs) : MainOutcome → Prop
  | .failure => ¬∃ decoded, SailDecode args.input decoded
  | .success zesu =>
      (∃ sail, SailDecode args.input sail ∧
        decodedResultRelModuloKnownBugs args.input zesu sail) ∨
      ((¬∃ sail, SailDecode args.input sail) ∧
        ∃ bug ∈ bugs, KnownBugApplies args.input zesu bug)

/-- Exact SSZ/RLP meaning after excluding every currently reviewed implementation divergence. -/
def MainMeaning (args : MainArgs) : MainOutcome → Prop
  | .failure => ¬∃ decoded, SailDecode args.input decoded
  | .success zesu => ∃ sail, SailDecode args.input sail ∧
      decodedResultRel args.input zesu sail

/-- The particular input avoids every reviewed Zesu/EVM-Sail divergence. Unlike the former global
hypothesis, this cannot say that demonstrated bug-triggering inputs do not exist. -/
structure AvoidKnownBugs (input : Array UInt8) : Prop where
  successfulResult : ∀ zesu sail, SailDecode input sail →
    decodedResultRelModuloKnownBugs input zesu sail → decodedResultRel input zesu sail
  rejectedDomain : (¬∃ sail, SailDecode input sail) → ∀ zesu bug,
    bug ∈ knownBugs → KnownBugApplies input zesu bug → False

theorem mainMeaning_of_modulo {args : MainArgs} (hAvoidKnownBugs : AvoidKnownBugs args.input)
    {outcome : MainOutcome} (meaning : MainMeaningModulo knownBugs args outcome) :
    MainMeaning args outcome := by
  cases outcome with
  | failure => exact meaning
  | success zesu =>
      rcases meaning with ⟨sail, decoded, related⟩ | ⟨rejected, bug, listed, applies⟩
      · exact ⟨sail, decoded, hAvoidKnownBugs.successfulResult zesu sail decoded related⟩
      · exact False.elim (hAvoidKnownBugs.rejectedDomain rejected zesu bug listed applies)

set_option genInjectivity false in
/-- Data permissions supplied by the concrete endpoint environment for the complete main stack
frame and the two fixed bare-metal I/O context words. -/
structure MainDataAccess (args : MainArgs) (state : State) : Prop where
  stackLoad : ∀ offset width, offset + width ≤ 0x380 →
    LoadPmaAllows state (BitVec.ofNat 64 (args.stackPointer + offset)) width
  stackStore : ∀ offset width, offset + width ≤ 0x380 →
    StorePmaAllows state (BitVec.ofNat 64 (args.stackPointer + offset)) width
  inputContextLoad :
    LoadPmaAllows state (BitVec.ofNat 64 Elflings.ioContextAddress) 8
  exitCodeStore :
    StorePmaAllows state (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)) 8

theorem MainDataAccess.of_pma_regions_eq {args : MainArgs} {before after : State}
    (access : MainDataAccess args before)
    (regions : after.regs.get? pma_regions = before.regs.get? pma_regions) :
    MainDataAccess args after where
  stackLoad offset width bound :=
    dataPmaAllows_of_pma_regions_eq regions (access.stackLoad offset width bound)
  stackStore offset width bound :=
    dataPmaAllows_of_pma_regions_eq regions (access.stackStore offset width bound)
  inputContextLoad := dataPmaAllows_of_pma_regions_eq regions access.inputContextLoad
  exitCodeStore := dataPmaAllows_of_pma_regions_eq regions access.exitCodeStore

set_option genInjectivity false in
/-- Concrete Linux/RV64 entry state for the exported endpoint. The two PMA/MMIO clauses are the
actual stack stores at offsets `0x378` and `8`; no generated instruction run is assumed here. -/
structure MainEntry (args : MainArgs) (state : EndpointState) : Prop where
  stdin : state.stdin = args.input
  stdinCursor : state.stdinCursor = 0
  stdout : state.stdout = #[]
  exitCode : state.exitCode = none
  inputBound : args.input.size ≤ 64 * 1024 * 1024
  stackLower : 0x7d0 ≤ args.stackPointer
  stackFits : args.stackPointer + 0x380 < 2 ^ 64
  stackAligned : args.stackPointer % 16 = 0
  returnAddressFits : args.returnAddress < 2 ^ 64
  atPc : state.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.mainEntry)
  stackRegister :
    state.machine.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer + 0x380))
  returnRegister : state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress)
  configured : ConfiguredMachinePre EndpointMachinePc state.machine
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem
  dataAccess : MainDataAccess args state.machine
  savedReturnNoMMIO :
    StoreMMIOAddressExcluded (BitVec.ofNat 64 (args.stackPointer + 0x378)) 8
  inputSizeNoMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (args.stackPointer + 8)) 8
  stackNoMMIO : ∀ offset width, offset + width ≤ 0x380 →
    DataMMIOAddressExcluded (BitVec.ofNat 64 (args.stackPointer + offset)) width
  inputBytes : BytesRep state.machine.mem Elflings.inputBufferAddress args.input
  inputSizeContext : UIntRep 8 state.machine.mem Elflings.ioContextAddress args.input.size
  stackBelowInputBuffer : args.stackPointer + 0x380 ≤ Elflings.inputBufferAddress
  inputOutsideStack : ∀ index, index < args.input.size →
    Elflings.inputBufferAddress + index < args.stackPointer ∨
      args.stackPointer + 0x380 ≤ Elflings.inputBufferAddress + index
  stackNotFileBacked : ∀ address, args.stackPointer ≤ address →
    address < args.stackPointer + 0x380 → Artifacts.programImage.readFileByte? address = none

def MainExit (args : MainArgs) (outcome : MainOutcome)
    (_before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 Elflings.zkvmExitTerminalPc) ∧
  after.stdin = args.input ∧ after.stdinCursor = args.input.size ∧
  after.exitCode = some 0 ∧
  ∃ bytes, after.stdout = bytes ∧
    match outcome with
    | .failure => decodeZesuObservation bytes = some .failure
    | .success decoded => decodeZesuObservation bytes = some (.success decoded)

def mainContractModulo (bugs : List KnownBug) (stepBound : MainArgs → Nat) :
    RelationalMachineContract EndpointState MainArgs MainOutcome :=
  { allows := MainMeaningModulo bugs
    entry := MainEntry
    exit := MainExit
    stepBound }

/-- The complete shipped endpoint implements the reviewed semantics modulo exactly `bugs`. -/
def ComplianceModulo (bugs : List KnownBug) : Prop :=
  ∃ stepBound, (mainContractModulo bugs stepBound).Implements EndpointStep EndpointPc
    MainExecutionPc (pcInList [Elflings.zkvmExitTerminalPc])

def mainContractFor (input : Array UInt8) (stepBound : MainArgs → Nat) :
    RelationalMachineContract EndpointState MainArgs MainOutcome :=
  { allows := MainMeaning
    entry := fun args state => args.input = input ∧ MainEntry args state
    exit := MainExit
    stepBound }

/-- Exact endpoint compliance on one input known not to trigger a reviewed divergence. -/
def ComplianceFor (input : Array UInt8) : Prop :=
  ∃ stepBound, (mainContractFor input stepBound).Implements EndpointStep EndpointPc MainExecutionPc
    (pcInList [Elflings.zkvmExitTerminalPc])

theorem complianceFor_of_modulo (hAvoidKnownBugs : AvoidKnownBugs input)
    (compliance : ComplianceModulo knownBugs) : ComplianceFor input := by
  rcases compliance with ⟨stepBound, implements⟩
  refine ⟨stepBound, ?_⟩
  intro args fromStep before entry
  rcases entry with ⟨rfl, entry⟩
  obtain ⟨count, after, outcome, positive, bounded, trace, exitPc, meaning, exit⟩ :=
    implements args fromStep before entry
  exact ⟨count, after, outcome, positive, bounded, trace, exitPc,
    mainMeaning_of_modulo hAvoidKnownBugs meaning, exit⟩

/-- The parent contract derived by resolving Level 0 against its six selected children. -/
abbrev ExportedContractAssumptions : Prop := ComplianceModulo knownBugs

/-- The six existential contract bounds opened once, so Level 0 can add them into one endpoint
termination bound while reusing the corresponding implementation proofs. -/
structure Level1ResolvedContracts where
  readInputBound : Nat → Nat
  readInput : (readInputContract (fun args => readInputBound args.input.size)).Implements
    EndpointStep EndpointPc (pcInRanges Elflings.readInputExecutionPcRanges)
      (pcInList Elflings.readInputExitPcs)
  allocatorGetBound : Nat → Nat
  allocatorGet : (allocatorGetContract (fun args => allocatorGetBound args.input.size)).Implements
    EndpointStep EndpointPc (pcInRanges Elflings.allocatorGetExecutionPcRanges)
      (pcInList Elflings.allocatorGetExitPcs)
  decodeBound : Nat → Nat
  sszDecode : (decodeContractModuloKnownBugs (fun args => decodeBound args.input.size)).Implements
    EndpointStep EndpointPc DecodeExecutionPc DecodeExitPc
  writeSuccessBound : Nat → Nat
  writeSuccess : (writeSuccessContract (fun args => writeSuccessBound args.inputSize)).Implements
    EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessExecutionPcRanges)
      (pcInList Elflings.writeSuccessExitPcs)
  writeFailureBound : Nat
  writeFailure : (writeFailureContract (fun _ => writeFailureBound)).Implements
    EndpointStep EndpointPc (pcInRanges Elflings.writeFailureExecutionPcRanges)
      (pcInList Elflings.writeFailureExitPcs)
  zkvmExitBound : Nat
  zkvmExit : (zkvmExitContract (fun _ => zkvmExitBound)).Implements
    EndpointStep EndpointPc (pcInRanges Elflings.zkvmExitExecutionPcRanges)
      (pcInList Elflings.zkvmExitExitPcs)

noncomputable def Level1ContractAssumptions.resolve (h : Level1ContractAssumptions) :
    Level1ResolvedContracts :=
  { readInputBound := Classical.choose h.readInput
    readInput := Classical.choose_spec h.readInput
    allocatorGetBound := Classical.choose h.allocatorGet
    allocatorGet := Classical.choose_spec h.allocatorGet
    decodeBound := Classical.choose h.sszDecode
    sszDecode := Classical.choose_spec h.sszDecode
    writeSuccessBound := Classical.choose h.writeSuccess
    writeSuccess := Classical.choose_spec h.writeSuccess
    writeFailureBound := Classical.choose h.writeFailure
    writeFailure := Classical.choose_spec h.writeFailure
    zkvmExitBound := Classical.choose h.zkvmExit
    zkvmExit := Classical.choose_spec h.zkvmExit }

def level0ResolvedStepBound (contracts : Level1ResolvedContracts) (inputSize : Nat) : Nat :=
  24 + contracts.readInputBound inputSize + contracts.allocatorGetBound inputSize +
    contracts.decodeBound inputSize + contracts.writeSuccessBound inputSize +
    contracts.writeFailureBound + contracts.zkvmExitBound

private theorem instructionPreserved_abiCalleePreserved (register : Register)
    (preserved : instructionPreserved register) : abiCalleePreserved register := by
  rcases preserved.1 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  all_goals simp [abiCalleePreserved]

/-- A reviewed returning ABI contract restores the configured-machine premise needed by the next
Level 0 instruction. `minstret` is retained by presence rather than by false value equality. -/
theorem ConfiguredMachinePre.of_endpointCallFrame {before after : EndpointState}
    (configured : ConfiguredMachinePre EndpointMachinePc before.machine)
    (frame : EndpointCallFrame before after) :
    ConfiguredMachinePre EndpointMachinePc after.machine :=
  configured.mono
    (frame.1.weaken instructionPreserved_abiCalleePreserved)
    frame.2.1

private theorem instructionPreserved_disjoint_bookkeeping :
    RegSet.Disjoint instructionPreserved stepBookkeeping :=
  platformPreserved_disjoint.weaken (fun _ preserved => preserved.1)

/-- Transport through a branch or comparison that retires at its fall-through PC. -/
theorem ConfiguredMachinePre.afterFallThrough {state : MachineState}
    (pc target retired : BitVec 64) (configured : ConfiguredMachinePre EndpointMachinePc state) :
    ConfiguredMachinePre EndpointMachinePc
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) target retired) := by
  apply configured.mono
  · exact (fallThroughRetirement_writes state pc target retired).agree
      instructionPreserved_disjoint_bookkeeping
  · exact tryStepControlFlowAfterRetired_retired_present _ target retired

/-- Transport through a taken branch that retires at its jump target. -/
theorem ConfiguredMachinePre.afterJump {state : MachineState}
    (pc target retired : BitVec 64) (configured : ConfiguredMachinePre EndpointMachinePc state) :
    ConfiguredMachinePre EndpointMachinePc
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target) target retired) := by
  apply configured.mono
  · exact (jumpRetirement_writes state pc target retired).agree
      instructionPreserved_disjoint_bookkeeping
  · exact tryStepControlFlowAfterRetired_retired_present _ target retired

/-- Transport through the exact post-state of `main`'s stack allocation. -/
theorem ConfiguredMachinePre.afterStackAddi {state : MachineState} (pc : BitVec 64)
    (immediate : BitVec 12) (stackValue retired : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    ConfiguredMachinePre EndpointMachinePc
      (tryStepStackAddiAfterRetired state pc immediate stackValue retired) := by
  apply configured.mono
  · exact (stackAddiRetirement_writes state pc immediate stackValue retired).agree
      (instructionPreserved_disjoint_bookkeeping.union (RegSet.Disjoint.only (by
        simp [instructionPreserved, platformPreserved])))
  · refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
    simp [tryStepStackAddiAfterRetired]

/-- Exact register frame through either concrete Level 0 stack store. -/
theorem main_store_retirement_writes {state afterWrite : MachineState}
    (pc retired : BitVec 64)
    (writeRegs : afterWrite.regs =
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs) :
    WritesOnlyRegs stepBookkeeping state (tryStepStoreAfterRetired afterWrite pc retired) := by
  have storePrefix : WritesOnlyRegs stepBookkeeping state afterWrite :=
    (stepPremiseState_writes state pc).congr_regs writeRegs
  exact storePrefix.trans_same ((tryStepControlFlowAfterRetired_writes afterWrite
      (Sail.BitVec.addInt pc 4) retired).mono
        (fun _ written => written.elim Or.inl (fun written => Or.inr (Or.inr (Or.inl written)))))

/-- Transport through either concrete Level 0 stack store. -/
theorem ConfiguredMachinePre.afterStore {state afterWrite : MachineState}
    (pc retired : BitVec 64) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (writeRegs : afterWrite.regs =
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs) :
    ConfiguredMachinePre EndpointMachinePc (tryStepStoreAfterRetired afterWrite pc retired) := by
  apply configured.mono
  · exact (main_store_retirement_writes pc retired writeRegs).agree
      instructionPreserved_disjoint_bookkeeping
  · simpa [tryStepStoreAfterRetired] using
      tryStepControlFlowAfterRetired_retired_present afterWrite (Sail.BitVec.addInt pc 4) retired

/-- Transport through an exact link-writing call instruction. -/
theorem ConfiguredMachinePre.afterCall {state : MachineState} (pc target returnPc retired : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    ConfiguredMachinePre EndpointMachinePc
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) pc target x1 returnPc)
        target retired) := by
  apply configured.mono
  · simpa [callLinkState] using
      (callRetirement_writes state pc target retired x1 returnPc).agree
        (instructionPreserved_disjoint_bookkeeping.union
          (RegSet.Disjoint.only (by simp [instructionPreserved])))
  · simpa using tryStepControlFlowAfterRetired_retired_present
      (callLinkState (tryStepControlFlowAfterIncrement state) pc target x1 returnPc) target retired

/-- One exact non-syscall Sail instruction, lifted into and confined by the complete Level 0 region. -/
theorem main_confined_sail_step (stepNo : Nat) (before : EndpointState) (after : MachineState)
    (pc : BitVec 64) (atPc : EndpointPc before = some pc) (inside : mainGluePcs pc)
    (notSyscall : ¬ BareMetalHostTransitionPc pc) (step : MachineStep stepNo before.machine after) :
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc stepNo 1 before
      { before with machine := after } := by
  apply ConfinedTrace.step stepNo 0 pc before { before with machine := after }
    { before with machine := after }
  · exact atPc
  · exact Or.inl inside
  · exact endpointStep_sail stepNo before after (fun target targetPc => by
      rw [atPc] at targetPc
      cases Option.some.inj targetPc
      exact notSyscall) step
  · exact .refl (stepNo + 1) _

/-- Exact one-step handoff after `main` allocates its 896-byte frame. -/
def MainStackAllocatedHandoff (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ after : EndpointState,
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep 1 before after ∧
    ConfiguredMachinePre EndpointMachinePc after.machine ∧
    Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    EndpointPc after = some 0x14cb4 ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
    MainDataAccess args after.machine ∧
    BytesRep after.machine.mem Elflings.inputBufferAddress args.input ∧
    UIntRep 8 after.machine.mem Elflings.ioContextAddress args.input.size ∧
    after.stdin = args.input ∧ after.stdinCursor = 0 ∧ after.stdout = #[] ∧
    after.exitCode = none

/-- Execute the first exact Level 0 instruction and bind the resulting stack base. -/
theorem main_stack_allocate (args : MainArgs) (fromStep : Nat) (before : EndpointState)
    (entry : MainEntry args before) : MainStackAllocatedHandoff args fromStep before := by
  obtain ⟨retired, run⟩ := main_stack_allocate_step fromStep before.machine
    (BitVec.ofNat 64 (args.stackPointer + 0x380)) entry.configured entry.atPc
    entry.stackRegister entry.code
  let afterMachine := tryStepStackAddiAfterRetired before.machine
    (BitVec.ofNat 64 Elflings.mainEntry) (BitVec.ofNat 12 0xc80)
    (BitVec.ofNat 64 (args.stackPointer + 0x380)) retired
  let after : EndpointState := { before with machine := afterMachine }
  have machineStep : MachineStep fromStep before.machine afterMachine := run
  have stackValueToNat :
      (BitVec.ofNat 64 (args.stackPointer + 0x380)).toNat = args.stackPointer + 0x380 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt entry.stackFits]
  have stackResultToNat :
      (BitVec.ofNat 64 (args.stackPointer + 0x380) +
        sign_extend (m := 64) (BitVec.ofNat 12 0xc80)).toNat = args.stackPointer := by
    rw [prologue_toNat (delta := 0x380)]
    · rw [stackValueToNat]
      omega
    · native_decide
    · rw [stackValueToNat]
      omega
  have stackResult :
      BitVec.ofNat 64 (args.stackPointer + 0x380) +
        sign_extend (m := 64) (BitVec.ofNat 12 0xc80) =
          BitVec.ofNat 64 args.stackPointer := by
    apply BitVec.eq_of_toNat_eq
    rw [stackResultToNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : args.stackPointer < 2 ^ 64)]
  refine ⟨after,
      main_confined_sail_step fromStep before afterMachine
        (BitVec.ofNat 64 Elflings.mainEntry) (by simpa [EndpointPc] using entry.atPc)
        (by refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
      mainEntry_not_syscall machineStep,
      ConfiguredMachinePre.afterStackAddi _ _ _ _ entry.configured,
      (by simpa [after, afterMachine, tryStepStackAddiAfterRetired_mem] using entry.code),
      (by
        simp [after, afterMachine, EndpointPc, MachinePc, tryStepStackAddiAfterRetired,
          tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState,
          stackAddiNextState, tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert,
          Elflings.mainEntry]
        native_decide),
      (by
        simpa [after, afterMachine, stackResult] using
          tryStepStackAddiAfterRetired_stackPointer before.machine
            (BitVec.ofNat 64 Elflings.mainEntry) (BitVec.ofNat 12 0xc80)
            (BitVec.ofNat 64 (args.stackPointer + 0x380)) retired),
      (by
        calc
          after.machine.regs.get? x1 = before.machine.regs.get? x1 :=
            (stackAddiRetirement_writes before.machine
              (BitVec.ofNat 64 Elflings.mainEntry) (BitVec.ofNat 12 0xc80)
              (BitVec.ofNat 64 (args.stackPointer + 0x380)) retired).get x1 (by decide)
          _ = some (BitVec.ofNat 64 args.returnAddress) := entry.returnRegister),
      entry.dataAccess.of_pma_regions_eq
        ((stackAddiRetirement_writes before.machine
          (BitVec.ofNat 64 Elflings.mainEntry) (BitVec.ofNat 12 0xc80)
          (BitVec.ofNat 64 (args.stackPointer + 0x380)) retired).get pma_regions (by decide)),
      (by simpa [after, afterMachine, tryStepStackAddiAfterRetired_mem] using entry.inputBytes),
      (by simpa [after, afterMachine, tryStepStackAddiAfterRetired_mem] using
        entry.inputSizeContext),
      (by simpa [after] using entry.stdin), (by simpa [after] using entry.stdinCursor),
      (by simpa [after] using entry.stdout), (by simpa [after] using entry.exitCode)⟩

/-- Exact two-step handoff after `main` saves its incoming return address. -/
def MainReturnSavedHandoff (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ after : EndpointState,
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep 2 before after ∧
    ConfiguredMachinePre EndpointMachinePc after.machine ∧
    Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    EndpointPc after = some 0x14cb8 ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 0x378) args.returnAddress ∧
    MainDataAccess args after.machine ∧
    BytesRep after.machine.mem Elflings.inputBufferAddress args.input ∧
    UIntRep 8 after.machine.mem Elflings.ioContextAddress args.input.size ∧
    after.stdin = args.input ∧ after.stdinCursor = 0 ∧ after.stdout = #[] ∧
    after.exitCode = none

/-- Execute the exact `sd ra,888(sp)` and retain the remaining stack-store permission. -/
theorem main_save_return_address (args : MainArgs) (fromStep : Nat) (before : EndpointState)
    (entry : MainEntry args before) : MainReturnSavedHandoff args fromStep before := by
  obtain ⟨stackState, stackTrace, configured, code, atPc, stackRead, returnRead,
      dataAccess, inputBytes, inputContext, stdin, stdinCursor, stdout, exitCode⟩ :=
    main_stack_allocate args fromStep before entry
  let premise := coreStoreNextState (tryStepStoreAfterIncrement stackState.machine) 0x14cb4
  have returnPremise : premise.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) :=
    (stepPremiseState_writes stackState.machine 0x14cb4).get x1 (by decide) |>.trans returnRead
  have dataRead : Runs (rX_bits (.Regidx 1#5)) premise premise
      (BitVec.ofNat 64 args.returnAddress) :=
    rX_x1_run premise (BitVec.ofNat 64 args.returnAddress) returnPremise
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have frameBound : args.stackPointer + 0x380 < 18446744073709551616 := by
    simpa only [show 2 ^ 64 = 18446744073709551616 by native_decide] using entry.stackFits
  have stackDivEight : 8 ∣ args.stackPointer := by
    obtain ⟨multiple, hmultiple⟩ := Nat.dvd_of_mod_eq_zero entry.stackAligned
    exact ⟨2 * multiple, by omega⟩
  have destinationEq :
      BitVec.ofNat 64 args.stackPointer + sign_extend (m := 64) (BitVec.ofNat 12 0x378) =
        BitVec.ofNat 64 (args.stackPointer + 0x378) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have immediateNat : (sign_extend (m := 64) (BitVec.ofNat 12 0x378)).toNat = 0x378 := by
      native_decide
    rw [immediateNat]
    have stackBound : args.stackPointer < 2 ^ 64 := by
      rw [show 2 ^ 64 = 18446744073709551616 by native_decide]
      omega
    rw [Nat.mod_eq_of_lt stackBound]
  let afterWrite := afterWriteBytes (width := 8)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement stackState.machine) 0x14cb4)
    (BitVec.ofNat 64 (args.stackPointer + 0x378)).toNat
    (BitVec.ofNat 64 args.returnAddress)
  have access : MainDwordStoreAccess stackState.machine afterWrite 0x14cb4 0x378
      (.Regidx 1#5) :=
    MainDwordStoreAccess.of_stack stackState.machine 0x14cb4 0x378 (.Regidx 1#5)
      (BitVec.ofNat 64 args.stackPointer) (BitVec.ofNat 64 args.returnAddress)
      (BitVec.ofNat 64 (args.stackPointer + 0x378)) mstatusBits mseccfgBits configured
      (by simpa [EndpointPc] using atPc)
      (by refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
      stackRead dataRead mstatusRead mprvZero mseccfgRead pmmDisabled destinationEq
      (by
        unfold is_aligned_vaddr
        simp only
        change ((((BitVec.ofNat 64 (args.stackPointer + 0x378)).toNat : Int).tmod 8) == 0) = true
        have destinationBound : args.stackPointer + 0x378 < 2 ^ 64 := by
          rw [show 2 ^ 64 = 18446744073709551616 by native_decide]
          omega
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt destinationBound]
        have modEight : (args.stackPointer + 0x378) % 8 = 0 := by
          obtain ⟨multiple, hmultiple⟩ := stackDivEight
          exact Nat.mod_eq_zero_of_dvd ⟨multiple + 111, by omega⟩
        have tmodEight : ((args.stackPointer + 0x378 : Nat) : Int).tmod 8 = 0 :=
          congrArg Int.ofNat modEight
        simpa [tmodEight])
      (dataAccess.stackStore 0x378 8 (by omega)) entry.savedReturnNoMMIO
  obtain ⟨retired, run⟩ := main_save_return_address_step (fromStep + 1) stackState.machine
    afterWrite configured (by simpa [EndpointPc] using atPc) code access
  let afterMachine := tryStepStoreAfterRetired afterWrite 0x14cb4 retired
  let after : EndpointState := { stackState with machine := afterMachine }
  have writeRegs : afterWrite.regs =
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement stackState.machine) 0x14cb4).regs :=
    afterWriteBytes_regs premise _ _
  have writes := main_store_retirement_writes 0x14cb4 retired writeRegs
  have platformAgree : Agree platformPreserved stackState.machine afterMachine :=
    writes.agree platformPreserved_disjoint
  have codeWrite : Artifacts.programImage.fileBytesLoadedFaithfully afterWrite.mem := by
    apply fileBytesLoadedFaithfully_afterWriteBytes Artifacts.programImage premise
      (BitVec.ofNat 64 (args.stackPointer + 0x378)).toNat
      (BitVec.ofNat 64 args.returnAddress)
    · intro index
      have destinationBound : args.stackPointer + 0x378 < 2 ^ 64 := by
        rw [show 2 ^ 64 = 18446744073709551616 by native_decide]
        omega
      apply entry.stackNotFileBacked
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt destinationBound]
        omega
      · have hi : index.val < 8 := index.isLt
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt destinationBound]
        omega
    · simpa [premise, coreStoreNextState, tryStepStoreAfterIncrement] using code
  have inputBytesAfter : BytesRep afterMachine.mem Elflings.inputBufferAddress args.input := by
    refine ⟨inputBytes.1, ?_⟩
    intro index inBounds
    change (tryStepStoreAfterRetired afterWrite 0x14cb4 retired).mem.get?
      (Elflings.inputBufferAddress + index) = _
    rw [tryStepStoreAfterRetired, tryStepStoreAfterTick]
    rw [afterWriteBytes_mem_get?_of_outside]
    · exact inputBytes.2 index inBounds
    · intro written
      have writtenBound : written.val < 8 := written.isLt
      rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : args.stackPointer + 0x378 < 2 ^ 64)]
      rcases entry.inputOutsideStack index inBounds with below | above <;> omega
  have inputContextAfter : UIntRep 8 afterMachine.mem Elflings.ioContextAddress args.input.size := by
    refine ⟨inputContext.1, inputContext.2.1, ?_⟩
    intro index indexBound
    change (tryStepStoreAfterRetired afterWrite 0x14cb4 retired).mem.get?
      (Elflings.ioContextAddress + index) = _
    rw [tryStepStoreAfterRetired, tryStepStoreAfterTick]
    rw [afterWriteBytes_mem_get?_of_outside]
    · exact inputContext.2.2 index indexBound
    · intro written
      have writtenBound : written.val < 8 := written.isLt
      rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : args.stackPointer + 0x378 < 2 ^ 64)]
      have contextAfterInput : Elflings.inputBufferAddress ≤ Elflings.ioContextAddress := by
        native_decide
      have stackBelowInput := entry.stackBelowInputBuffer
      omega
  refine ⟨after, stackTrace.append (main_confined_sail_step (fromStep + 1) stackState afterMachine
      0x14cb4 atPc (by refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
      main14cb4_not_syscall run),
    ConfiguredMachinePre.afterStore 0x14cb4 retired configured writeRegs,
    (by simpa [after, afterMachine, tryStepStoreAfterRetired, tryStepStoreAfterTick] using codeWrite),
    (by simp [after, afterMachine, EndpointPc, MachinePc, tryStepStoreAfterRetired,
      tryStepStoreAfterTick, Std.ExtDHashMap.get?_insert]; native_decide),
    (writes.get x2 (by decide)).trans stackRead,
    (writes.get x1 (by decide)).trans returnRead,
    (by
      have destinationBound : args.stackPointer + 0x378 < 2 ^ 64 := by omega
      have written := uintRep_afterWriteBytes_eight premise (args.stackPointer + 0x378)
        args.returnAddress entry.returnAddressFits (by omega)
      change UIntRep 8 (tryStepStoreAfterRetired afterWrite 0x14cb4 retired).mem
        (args.stackPointer + 0x378) args.returnAddress
      rw [tryStepStoreAfterRetired, tryStepStoreAfterTick]
      simpa [afterWrite, BitVec.toNat_ofNat, Nat.mod_eq_of_lt destinationBound] using written),
    dataAccess.of_pma_regions_eq (writes.get pma_regions (by decide)),
    inputBytesAfter,
    inputContextAfter,
    (by simpa [after] using stdin), (by simpa [after] using stdinCursor),
    (by simpa [after] using stdout), (by simpa [after] using exitCode)⟩

/-- Exact three-step handoff after both Level 0 stack stores. -/
def MainFrameInitializedHandoff (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ after : EndpointState,
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep 3 before after ∧
    ConfiguredMachinePre EndpointMachinePc after.machine ∧
    Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    EndpointPc after = some 0x14cbc ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 0x378) args.returnAddress ∧
    MainDataAccess args after.machine ∧
    BytesRep after.machine.mem Elflings.inputBufferAddress args.input ∧
    UIntRep 8 after.machine.mem Elflings.ioContextAddress args.input.size ∧
    after.stdin = args.input ∧ after.stdinCursor = 0 ∧ after.stdout = #[] ∧
    after.exitCode = none

/-- Execute `sd zero,8(sp)` and complete the concrete Level 0 frame prefix. -/
theorem main_initialize_frame (args : MainArgs) (fromStep : Nat) (before : EndpointState)
    (entry : MainEntry args before) : MainFrameInitializedHandoff args fromStep before := by
  obtain ⟨savedState, savedTrace, configured, code, atPc, stackRead, returnRead, savedReturn,
      dataAccess, inputBytes, inputContext, stdin, stdinCursor, stdout, exitCode⟩ :=
    main_save_return_address args fromStep before entry
  let premise := coreStoreNextState (tryStepStoreAfterIncrement savedState.machine) 0x14cb8
  have dataRead : Runs (rX_bits (.Regidx 0#5)) premise premise 0 := rX_x0_run premise
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have frameBound : args.stackPointer + 0x380 < 18446744073709551616 := by
    simpa only [show 2 ^ 64 = 18446744073709551616 by native_decide] using entry.stackFits
  have stackDivEight : 8 ∣ args.stackPointer :=
    by
      obtain ⟨multiple, hmultiple⟩ := Nat.dvd_of_mod_eq_zero entry.stackAligned
      exact ⟨2 * multiple, by omega⟩
  have destinationEq :
      BitVec.ofNat 64 args.stackPointer + sign_extend (m := 64) (BitVec.ofNat 12 8) =
        BitVec.ofNat 64 (args.stackPointer + 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have immediateNat : (sign_extend (m := 64) (BitVec.ofNat 12 8)).toNat = 8 := by
      native_decide
    rw [immediateNat]
    have stackBound : args.stackPointer < 2 ^ 64 := by
      rw [show 2 ^ 64 = 18446744073709551616 by native_decide]
      omega
    rw [Nat.mod_eq_of_lt stackBound]
  let afterWrite := afterWriteBytes (width := 8)
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement savedState.machine) 0x14cb8)
    (BitVec.ofNat 64 (args.stackPointer + 8)).toNat 0
  have access : MainDwordStoreAccess savedState.machine afterWrite 0x14cb8 8 (.Regidx 0#5) :=
    MainDwordStoreAccess.of_stack savedState.machine 0x14cb8 8 (.Regidx 0#5)
      (BitVec.ofNat 64 args.stackPointer) 0 (BitVec.ofNat 64 (args.stackPointer + 8))
      mstatusBits mseccfgBits configured (by simpa [EndpointPc] using atPc)
      (by refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
      stackRead dataRead mstatusRead mprvZero mseccfgRead pmmDisabled destinationEq
      (by
        unfold is_aligned_vaddr
        simp only
        change ((((BitVec.ofNat 64 (args.stackPointer + 8)).toNat : Int).tmod 8) == 0) = true
        have destinationBound : args.stackPointer + 8 < 2 ^ 64 := by
          rw [show 2 ^ 64 = 18446744073709551616 by native_decide]
          omega
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt destinationBound]
        have modEight : (args.stackPointer + 8) % 8 = 0 :=
          by
            obtain ⟨multiple, hmultiple⟩ := stackDivEight
            exact Nat.mod_eq_zero_of_dvd ⟨multiple + 1, by omega⟩
        have tmodEight : ((args.stackPointer + 8 : Nat) : Int).tmod 8 = 0 :=
          congrArg Int.ofNat modEight
        simpa [tmodEight])
      (dataAccess.stackStore 8 8 (by omega)) entry.inputSizeNoMMIO
  obtain ⟨retired, run⟩ := main_clear_input_slot_step (fromStep + 2) savedState.machine
    afterWrite configured (by simpa [EndpointPc] using atPc) code access
  let afterMachine := tryStepStoreAfterRetired afterWrite 0x14cb8 retired
  let after : EndpointState := { savedState with machine := afterMachine }
  have writeRegs : afterWrite.regs =
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement savedState.machine) 0x14cb8).regs :=
    afterWriteBytes_regs premise _ _
  have writes := main_store_retirement_writes 0x14cb8 retired writeRegs
  have platformAgree : Agree platformPreserved savedState.machine afterMachine :=
    writes.agree platformPreserved_disjoint
  have codeWrite : Artifacts.programImage.fileBytesLoadedFaithfully afterWrite.mem := by
    apply fileBytesLoadedFaithfully_afterWriteBytes Artifacts.programImage premise
      (BitVec.ofNat 64 (args.stackPointer + 8)).toNat 0
    · intro index
      have destinationBound : args.stackPointer + 8 < 2 ^ 64 := by
        rw [show 2 ^ 64 = 18446744073709551616 by native_decide]
        omega
      apply entry.stackNotFileBacked
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt destinationBound]
        omega
      · have hi : index.val < 8 := index.isLt
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt destinationBound]
        omega
    · simpa [premise, coreStoreNextState, tryStepStoreAfterIncrement] using code
  have inputBytesAfter : BytesRep afterMachine.mem Elflings.inputBufferAddress args.input := by
    refine ⟨inputBytes.1, ?_⟩
    intro index inBounds
    change (tryStepStoreAfterRetired afterWrite 0x14cb8 retired).mem.get?
      (Elflings.inputBufferAddress + index) = _
    rw [tryStepStoreAfterRetired, tryStepStoreAfterTick]
    rw [afterWriteBytes_mem_get?_of_outside]
    · exact inputBytes.2 index inBounds
    · intro written
      have writtenBound : written.val < 8 := written.isLt
      rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : args.stackPointer + 8 < 2 ^ 64)]
      rcases entry.inputOutsideStack index inBounds with below | above <;> omega
  have inputContextAfter : UIntRep 8 afterMachine.mem Elflings.ioContextAddress args.input.size := by
    refine ⟨inputContext.1, inputContext.2.1, ?_⟩
    intro index indexBound
    change (tryStepStoreAfterRetired afterWrite 0x14cb8 retired).mem.get?
      (Elflings.ioContextAddress + index) = _
    rw [tryStepStoreAfterRetired, tryStepStoreAfterTick]
    rw [afterWriteBytes_mem_get?_of_outside]
    · exact inputContext.2.2 index indexBound
    · intro written
      have writtenBound : written.val < 8 := written.isLt
      rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : args.stackPointer + 8 < 2 ^ 64)]
      have contextAfterInput : Elflings.inputBufferAddress ≤ Elflings.ioContextAddress := by
        native_decide
      have stackBelowInput := entry.stackBelowInputBuffer
      omega
  refine ⟨after, savedTrace.append (main_confined_sail_step (fromStep + 2) savedState afterMachine
      0x14cb8 atPc (by refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
      main14cb8_not_syscall run),
    ConfiguredMachinePre.afterStore 0x14cb8 retired configured writeRegs,
    (by simpa [after, afterMachine, tryStepStoreAfterRetired, tryStepStoreAfterTick] using codeWrite),
    (by simp [after, afterMachine, EndpointPc, MachinePc, tryStepStoreAfterRetired,
      tryStepStoreAfterTick, Std.ExtDHashMap.get?_insert]; native_decide),
    (writes.get x2 (by decide)).trans stackRead,
    (writes.get x1 (by decide)).trans returnRead,
    (by
      refine ⟨savedReturn.1, savedReturn.2.1, ?_⟩
      intro index indexBound
      change (tryStepStoreAfterRetired afterWrite 0x14cb8 retired).mem.get?
        (args.stackPointer + 0x378 + index) = _
      rw [tryStepStoreAfterRetired, tryStepStoreAfterTick]
      rw [afterWriteBytes_mem_get?_of_outside]
      · exact savedReturn.2.2 index indexBound
      · intro written
        have writtenBound : written.val < 8 := written.isLt
        rw [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : args.stackPointer + 8 < 2 ^ 64)]
        omega),
    dataAccess.of_pma_regions_eq (writes.get pma_regions (by decide)),
    inputBytesAfter,
    inputContextAfter,
    (by simpa [after] using stdin), (by simpa [after] using stdinCursor),
    (by simpa [after] using stdout), (by simpa [after] using exitCode)⟩

/-- Handoff at the exact `jalr` that enters `read_input`, after its three register-only setup
instructions. -/
def MainReadInputCallReady (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ after : EndpointState,
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep 6 before after ∧
    ConfiguredMachinePre EndpointMachinePc after.machine ∧
    Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    EndpointPc after = some 0x14cc8 ∧
    after.machine.regs.get? x1 = some 0xfcc4 ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.machine.regs.get? x10 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.machine.regs.get? x11 = some (BitVec.ofNat 64 (args.stackPointer + 8)) ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 0x378) args.returnAddress ∧
    MainDataAccess args after.machine ∧
    BytesRep after.machine.mem Elflings.inputBufferAddress args.input ∧
    UIntRep 8 after.machine.mem Elflings.ioContextAddress args.input.size ∧
    after.stdin = args.input ∧ after.stdinCursor = 0 ∧ after.stdout = #[] ∧
    after.exitCode = none

/-- Compose `addi a0,sp,0; addi a1,sp,8; auipc ra,-5` from the initialized frame. -/
theorem main_prepare_read_input_call (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) (entry : MainEntry args before) :
    MainReadInputCallReady args fromStep before := by
  obtain ⟨frameState, frameTrace, configured0, code0, pc0, sp0, _ra0, _savedReturn,
      dataAccess0, inputBytes0, inputContext0, stdin0, cursor0, stdout0, exit0⟩ :=
    main_initialize_frame args fromStep before entry
  obtain ⟨retired0, run0⟩ := main_input_buffer_address_step (fromStep + 3) frameState.machine
    configured0 (by simpa [EndpointPc] using pc0) code0 (MainAddiSource.stackPointer sp0)
  let value0 := iTypeResult .ADDI 0 (BitVec.ofNat 64 args.stackPointer)
  let machine1 := afterRegisterWrite frameState.machine 0x14cbc retired0 x10 value0
  let state1 : EndpointState := { frameState with machine := machine1 }
  have value0Eq : value0 = BitVec.ofNat 64 args.stackPointer := by
    unfold value0 iTypeResult
    rw [sign_extend_zero_12_64]
    simp
  have trace1 : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep 4 before state1 :=
    frameTrace.append (main_confined_sail_step (fromStep + 3) frameState machine1 0x14cbc pc0
      mainGluePcs_14cbc
      main14cbc_not_syscall run0)
  have configured1 : ConfiguredMachinePre EndpointMachinePc machine1 :=
    ConfiguredMachinePre.afterRegisterWrite 0x14cbc retired0 x10 value0 configured0 (by
      simp [instructionPreserved, platformPreserved])
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully machine1.mem := by
    exact fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
      frameState.machine 0x14cbc retired0 x10 value0 code0
  have pc1 : EndpointPc state1 = some 0x14cc0 := by
    simpa [state1, EndpointPc, MachinePc, machine1] using
      afterRegisterWrite_pc frameState.machine 0x14cbc retired0 x10 value0
  have sp1 : machine1.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) :=
    (afterRegisterWrite_writes frameState.machine 0x14cbc retired0 x10 value0).get x2
      (by decide) |>.trans sp0
  obtain ⟨retired1, run1⟩ := main_input_size_slot_address_step (fromStep + 4) machine1
    configured1 (by simpa [state1, EndpointPc] using pc1) code1 (MainAddiSource.stackPointer sp1)
  let value1 := iTypeResult .ADDI 8 (BitVec.ofNat 64 args.stackPointer)
  let machine2 := afterRegisterWrite machine1 0x14cc0 retired1 x11 value1
  let state2 : EndpointState := { state1 with machine := machine2 }
  have value1Eq : value1 = BitVec.ofNat 64 (args.stackPointer + 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [value1, iTypeResult, BitVec.toNat_add, BitVec.toNat_ofNat]
    have immediateNat : (sign_extend (m := 64) (8 : BitVec 12)).toNat = 8 := by native_decide
    rw [immediateNat]
    have stackBound : args.stackPointer < 2 ^ 64 := by
      have frameBound := entry.stackFits
      omega
    rw [Nat.mod_eq_of_lt stackBound]
  have trace2 : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep 5 before state2 :=
    trace1.append (main_confined_sail_step (fromStep + 4) state1 machine2 0x14cc0 pc1
      mainGluePcs_14cc0
      main14cc0_not_syscall run1)
  have configured2 : ConfiguredMachinePre EndpointMachinePc machine2 :=
    ConfiguredMachinePre.afterRegisterWrite 0x14cc0 retired1 x11 value1 configured1 (by
      simp [instructionPreserved, platformPreserved])
  have code2 : Artifacts.programImage.fileBytesLoadedFaithfully machine2.mem := by
    exact fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
      machine1 0x14cc0 retired1 x11 value1 code1
  have pc2 : EndpointPc state2 = some 0x14cc4 := by
    simpa [state2, EndpointPc, MachinePc, machine2] using
      afterRegisterWrite_pc machine1 0x14cc0 retired1 x11 value1
  obtain ⟨retired2, run2⟩ := main_read_input_call_base_step (fromStep + 5) machine2 configured2
    (by simpa [state2, EndpointPc] using pc2) code2
  let callBase := (0x14cc4 : BitVec 64) + sign_extend (m := 64) (0xffffb#20 ++ 0x000#12)
  let machine3 := afterRegisterWrite machine2 0x14cc4 retired2 x1 callBase
  let state3 : EndpointState := { state2 with machine := machine3 }
  have callBaseEq : callBase = 0xfcc4 := by native_decide
  have writes0 := afterRegisterWrite_writes frameState.machine 0x14cbc retired0 x10 value0
  have writes1 := afterRegisterWrite_writes machine1 0x14cc0 retired1 x11 value1
  have writes2 := afterRegisterWrite_writes machine2 0x14cc4 retired2 x1 callBase
  refine ⟨state3, trace2.append (main_confined_sail_step (fromStep + 5) state2 machine3 0x14cc4
      pc2 mainGluePcs_14cc4
      main14cc4_not_syscall run2),
    ConfiguredMachinePre.afterRegisterWrite 0x14cc4 retired2 x1 callBase configured2 (by
      simp [instructionPreserved]),
    fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
      machine2 0x14cc4 retired2 x1 callBase code2,
    (by simpa [state3, EndpointPc, MachinePc, machine3] using
      afterRegisterWrite_pc machine2 0x14cc4 retired2 x1 callBase),
    (by simpa [state3, machine3, callBaseEq] using
      (afterRegisterWrite_destination machine2 0x14cc4 retired2 x1 callBase
        (by decide) (by decide))),
    (writes2.get x2 (by decide)).trans ((writes1.get x2 (by decide)).trans
      ((writes0.get x2 (by decide)).trans sp0)),
    (writes2.get x10 (by decide)).trans ((writes1.get x10 (by decide)).trans (by
      simpa [machine1, value0Eq] using
        (afterRegisterWrite_destination frameState.machine 0x14cbc retired0 x10 value0
          (by decide) (by decide)))),
    (writes2.get x11 (by decide)).trans (by
      simpa [machine2, value1Eq] using
        (afterRegisterWrite_destination machine1 0x14cc0 retired1 x11 value1
          (by decide) (by decide))),
    (by exact _savedReturn),
    dataAccess0.of_pma_regions_eq
      ((writes2.get pma_regions (by decide)).trans
        ((writes1.get pma_regions (by decide)).trans (writes0.get pma_regions (by decide)))),
    (by simpa [state3, state2, state1, machine3, machine2, machine1] using inputBytes0),
    (by simpa [state3, state2, state1, machine3, machine2, machine1] using inputContext0),
    (by simpa [state3, state2, state1] using stdin0),
    (by simpa [state3, state2, state1] using cursor0),
    (by simpa [state3, state2, state1] using stdout0),
    (by simpa [state3, state2, state1] using exit0)⟩

/-- Result of the exact Level 0 call instruction followed by the opaque reviewed `read_input`
contract. The dynamic child count remains explicit in the combined trace length. -/
def MainReadInputHandoff (contracts : Level1ResolvedContracts) (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ (childCount : Nat) (after : EndpointState) (outcome : ReadInputOutcome),
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep (7 + childCount) before after ∧
    0 < childCount ∧ EndpointPc after = some 0x14ccc ∧
    outcome.inputAddress = Elflings.inputBufferAddress ∧
    ConfiguredMachinePre EndpointMachinePc after.machine ∧
    Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    MainDataAccess args after.machine ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.stdin = args.input ∧ after.stdinCursor = args.input.size ∧
    after.stdout = #[] ∧ after.exitCode = none ∧
    UIntRep 8 after.machine.mem args.stackPointer outcome.inputAddress ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 8) args.input.size ∧
    BytesRep after.machine.mem outcome.inputAddress args.input ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 0x378) args.returnAddress ∧
    childCount ≤ contracts.readInputBound args.input.size

/-- Execute the `jalr` into `read_input` and consume the corresponding Level 1 assumption. -/
theorem main_call_read_input (contracts : Level1ResolvedContracts) (args : MainArgs)
    (fromStep : Nat) (before : EndpointState) (entry : MainEntry args before) :
    MainReadInputHandoff contracts args fromStep before := by
  obtain ⟨ready, prefixTrace, configured, code, atPc, callBase, sp, a0, a1, savedReturn,
      dataAccess, inputBytes, inputContext, stdin, cursor, stdout, exitCode⟩ :=
    main_prepare_read_input_call args fromStep before entry
  obtain ⟨retired, run⟩ := main_read_input_call_step (fromStep + 6) ready.machine configured
    (by simpa [EndpointPc] using atPc) callBase code
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement ready.machine) 0x14cc8 0x10140 x1 0x14ccc)
    0x10140 retired
  let callState : EndpointState := { ready with machine := callMachine }
  have callWrites := callRetirement_writes ready.machine 0x14cc8 0x10140 retired x1 0x14ccc
  have callTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep 7 before callState :=
    prefixTrace.append (main_confined_sail_step (fromStep + 6) ready callMachine 0x14cc8 atPc
      mainGluePcs_14cc8
      main14cc8_not_syscall run)
  have callCode : Artifacts.programImage.fileBytesLoadedFaithfully callMachine.mem := by
    simpa [callMachine, callLinkState, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement] using code
  have callConfigured : ConfiguredMachinePre EndpointMachinePc callMachine :=
    ConfiguredMachinePre.afterCall 0x14cc8 0x10140 0x14ccc retired configured
  have callDataAccess : MainDataAccess args callMachine :=
    dataAccess.of_pma_regions_eq (callWrites.get pma_regions (by decide))
  have readEntry : ReadInputEntry
      { returnAddress := 0x14ccc, bufferSlot := args.stackPointer,
        sizeSlot := args.stackPointer + 8, savedFrameAddress := args.stackPointer + 0x378,
        savedReturnAddress := args.returnAddress, input := args.input } callState := by
    refine ⟨readInputExitPc_14ccc, entry.inputBound, ?_, ?_, ?_, ?_, ?_, ?_, rfl,
      ?_, ?_, ?_, ?_, ?_, callDataAccess.stackStore 0 8 (by omega),
      callDataAccess.stackStore 8 8 (by omega), callDataAccess.inputContextLoad,
      entry.stackNoMMIO 0 8 (by omega), entry.stackNoMMIO 8 8 (by omega),
      ?_, ?_, ?_, ?_, callCode, callConfigured⟩
    · simpa [callState] using stdin
    · simpa [callState] using cursor
    · simp [callState, callMachine, EndpointPc, MachinePc, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, Elflings.readInputEntry]
    · simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
    · exact (callWrites.get x10 (by decide)).trans a0
    · exact (callWrites.get x11 (by decide)).trans a1
    · have divisibleByEight : args.stackPointer % 8 = 0 := by
        obtain ⟨multiple, multipleEq⟩ := Nat.dvd_of_mod_eq_zero entry.stackAligned
        exact Nat.mod_eq_zero_of_dvd ⟨2 * multiple, by omega⟩
      simpa only using divisibleByEight
    · show args.stackPointer + 16 < 2 ^ 64
      rw [show 2 ^ 64 = 18446744073709551616 by native_decide]
      have frameFits := entry.stackFits
      rw [show 2 ^ 64 = 18446744073709551616 by native_decide] at frameFits
      omega
    · simpa [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
        tryStepControlFlowAfterIncrement] using inputBytes
    · simpa [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
        tryStepControlFlowAfterIncrement] using inputContext
    · exact UIntRep.of_mem_eq savedReturn (by
        simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
          tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
          tryStepControlFlowAfterIncrement])
    · left
      change args.stackPointer + 16 ≤ Elflings.inputBufferAddress
      have stackBelowInput := entry.stackBelowInputBuffer
      omega
    · left
      change args.stackPointer + 16 ≤ Elflings.ioContextAddress
      have stackBelowInput := entry.stackBelowInputBuffer
      have inputBeforeContext : Elflings.inputBufferAddress ≤ Elflings.ioContextAddress := by
        native_decide
      omega
    · left
      change args.stackPointer + 16 ≤ args.stackPointer + 0x378
      omega
    · intro address lower upper
      change args.stackPointer ≤ address at lower
      change address < args.stackPointer + 16 at upper
      exact entry.stackNotFileBacked address lower (by omega)
  let stepBound := contracts.readInputBound
  let implements := contracts.readInput
  obtain ⟨childCount, after, outcome, positive, bounded, childTrace, _exitPc,
      _allowed, childExit⟩ := implements
        { returnAddress := 0x14ccc, bufferSlot := args.stackPointer,
          sizeSlot := args.stackPointer + 8, savedFrameAddress := args.stackPointer + 0x378,
          savedReturnAddress := args.returnAddress, input := args.input }
        (fromStep + 7) callState readEntry
  rcases childExit with ⟨afterPc, inputAddressExact, afterStdin, afterCursor, afterStdout,
    afterExitCode,
    bufferRep, sizeRep, inputRep, savedReturnRep, _memoryFrame, callFrame⟩
  have wideChild : ConfinedTrace EndpointStep EndpointPc MainExecutionPc (fromStep + 7)
      childCount callState after := childTrace.weaken (fun pc inside => Or.inr (Or.inl inside))
  refine ⟨childCount, after, outcome, callTrace.append wideChild, positive,
    (by simpa [EndpointPc] using afterPc),
    inputAddressExact,
    ConfiguredMachinePre.of_endpointCallFrame
      (ConfiguredMachinePre.afterCall 0x14cc8 0x10140 0x14ccc retired configured) callFrame,
    callFrame.2.2.1,
    callDataAccess.of_pma_regions_eq
      (callFrame.1 pma_regions (by simp [abiCalleePreserved])),
    callFrame.1 x2 (by simp [abiCalleePreserved]) |>.trans
      ((callWrites.get x2 (by decide)).trans sp),
    afterStdin.trans (by simpa [callState] using stdin), afterCursor,
    afterStdout.trans (by simpa [callState] using stdout),
    afterExitCode.trans (by simpa [callState] using exitCode),
    bufferRep, sizeRep, inputRep, savedReturnRep, bounded⟩

/-- Handoff after the adjacent opaque `allocatorGet` call returns at `0x14cec`. -/
def MainAllocatorGetHandoff (contracts : Level1ResolvedContracts) (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ (readCount allocatorCount : Nat) (after : EndpointState)
      (readOutcome : ReadInputOutcome) (allocatorOutcome : AllocatorGetOutcome),
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
      (7 + readCount + allocatorCount) before after ∧
    0 < readCount ∧ 0 < allocatorCount ∧ EndpointPc after = some 0x14cec ∧
    ConfiguredMachinePre EndpointMachinePc after.machine ∧
    Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    MainDataAccess args after.machine ∧
    allocatorOutcome.vtableAddress = Elflings.allocatorVtableAddress ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.machine.regs.get? x10 = some (BitVec.ofNat 64 allocatorOutcome.stateAddress) ∧
    after.machine.regs.get? x11 = some (BitVec.ofNat 64 allocatorOutcome.vtableAddress) ∧
    after.machine.regs.get? x12 = some (BitVec.ofNat 64 readOutcome.inputAddress) ∧
    after.machine.regs.get? x13 = some (BitVec.ofNat 64 args.input.size) ∧
    after.machine.regs.get? x18 = some (BitVec.ofNat 64 args.input.size) ∧
    after.machine.regs.get? x23 = some (BitVec.ofNat 64 readOutcome.inputAddress) ∧
    UIntRep 8 after.machine.mem args.stackPointer readOutcome.inputAddress ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 8) args.input.size ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 0x10) allocatorOutcome.stateAddress ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 0x18) allocatorOutcome.vtableAddress ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 0x378) args.returnAddress ∧
    BytesRep after.machine.mem readOutcome.inputAddress args.input ∧
    after.stdin = args.input ∧ after.stdinCursor = args.input.size ∧
    after.stdout = #[] ∧ after.exitCode = none ∧
    readCount ≤ contracts.readInputBound args.input.size ∧
    allocatorCount ≤ contracts.allocatorGetBound args.input.size

/-- Consume the second Level 1 assumption, whose entry is exactly the `read_input` return PC. -/
theorem main_call_allocator_get (contracts : Level1ResolvedContracts) (args : MainArgs)
    (fromStep : Nat) (before : EndpointState) (entry : MainEntry args before) :
    MainAllocatorGetHandoff contracts args fromStep before := by
  obtain ⟨readCount, readState, readOutcome, readTrace, readPositive, readPc,
      readInputAddressExact, configured, code, dataAccess, stackPointer, stdin, stdinCursor,
      stdout, exitCode,
      inputAddressRep, inputSizeRep,
      inputRep, savedReturnRep, readBounded⟩ :=
    main_call_read_input contracts args fromStep before entry
  let allocatorArgs : AllocatorGetArgs :=
    { returnAddress := 0x14cec, stackPointer := args.stackPointer,
      inputAddress := readOutcome.inputAddress, input := args.input,
      savedReturnAddress := args.returnAddress }
  have allocatorEntry : AllocatorGetEntry allocatorArgs readState := by
    refine ⟨allocatorGetExitPc_14cec, ?_, stackPointer, ?_, ?_,
      inputAddressRep, inputSizeRep, savedReturnRep, inputRep,
      dataAccess.stackLoad 0 8 (by omega), dataAccess.stackLoad 8 8 (by omega),
      dataAccess.stackStore 0x10 8 (by omega), dataAccess.stackStore 0x18 8 (by omega),
      entry.stackNoMMIO 0x10 8 (by omega), entry.stackNoMMIO 0x18 8 (by omega),
      ?_, ?_, code, configured⟩
    · simpa [allocatorArgs, EndpointPc, Elflings.allocatorGetEntry] using readPc
    · have divisibleByEight : args.stackPointer % 8 = 0 := by
        obtain ⟨multiple, multipleEq⟩ := Nat.dvd_of_mod_eq_zero entry.stackAligned
        exact Nat.mod_eq_zero_of_dvd ⟨2 * multiple, by omega⟩
      simpa [allocatorArgs] using divisibleByEight
    · have frameFits := entry.stackFits
      change args.stackPointer + 0x20 < 2 ^ 64
      omega
    · left
      change args.stackPointer + 0x20 ≤ readOutcome.inputAddress
      rw [readInputAddressExact]
      have stackBelowInput := entry.stackBelowInputBuffer
      omega
    · intro address lower upper
      change args.stackPointer + 0x10 ≤ address at lower
      change address < args.stackPointer + 0x20 at upper
      exact entry.stackNotFileBacked address (by omega) (by omega)
  let stepBound := contracts.allocatorGetBound
  let implements := contracts.allocatorGet
  obtain ⟨allocatorCount, after, allocatorOutcome, allocatorPositive, allocatorBounded,
      allocatorTrace, _exitPc, _allowed, allocatorExit⟩ :=
    implements allocatorArgs (fromStep + (7 + readCount)) readState allocatorEntry
  rcases allocatorExit with ⟨vtableExact, afterPc, afterStack, stateAddress, vtableAddress, inputPointer,
    inputLength, inputSize, inputAddress, inputAddressRep, inputSizeRep, stateAddressRep,
    vtableAddressRep, afterSavedReturn,
    afterInput, _memoryFrame, afterStdin, afterCursor, afterStdout, afterExitCode, callFrame⟩
  have wideAllocator : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
      (fromStep + (7 + readCount)) allocatorCount readState after :=
    allocatorTrace.weaken (fun pc inside => Or.inr (Or.inr (Or.inl inside)))
  refine ⟨readCount, allocatorCount, after, readOutcome, allocatorOutcome,
    (by simpa [Nat.add_assoc] using readTrace.append wideAllocator),
    readPositive, allocatorPositive,
    (by simpa [EndpointPc] using afterPc),
    ConfiguredMachinePre.of_endpointCallFrame configured callFrame, callFrame.2.2.1,
    dataAccess.of_pma_regions_eq (callFrame.1 pma_regions (by simp [abiCalleePreserved])),
    vtableExact,
    afterStack, stateAddress, vtableAddress, inputPointer, inputLength, inputSize, inputAddress,
    inputAddressRep, inputSizeRep, stateAddressRep, vtableAddressRep, afterSavedReturn, afterInput,
    afterStdin.trans stdin, afterCursor.trans stdinCursor,
    afterStdout.trans stdout, afterExitCode.trans exitCode, readBounded, allocatorBounded⟩

/-- Handoff immediately before the concrete `jalr` into `ssz_decode_root.decodeInput`. -/
def MainDecodeCallReady (contracts : Level1ResolvedContracts) (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ (readCount allocatorCount : Nat) (after : EndpointState)
      (readOutcome : ReadInputOutcome) (allocatorOutcome : AllocatorGetOutcome),
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
      (10 + readCount + allocatorCount) before after ∧
    0 < readCount ∧ 0 < allocatorCount ∧ EndpointPc after = some 0x14cf8 ∧
    ConfiguredMachinePre EndpointMachinePc after.machine ∧
    Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    MainDataAccess args after.machine ∧
    allocatorOutcome.vtableAddress = Elflings.allocatorVtableAddress ∧
    after.machine.regs.get? x1 = some 0x11cf4 ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.machine.regs.get? x10 = some (BitVec.ofNat 64 (args.stackPointer + 0x20)) ∧
    after.machine.regs.get? x11 = some (BitVec.ofNat 64 (args.stackPointer + 0x10)) ∧
    after.machine.regs.get? x12 = some (BitVec.ofNat 64 readOutcome.inputAddress) ∧
    after.machine.regs.get? x13 = some (BitVec.ofNat 64 args.input.size) ∧
    UIntRep 8 after.machine.mem args.stackPointer readOutcome.inputAddress ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 8) args.input.size ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 0x10) allocatorOutcome.stateAddress ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 0x18) allocatorOutcome.vtableAddress ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 0x378) args.returnAddress ∧
    BytesRep after.machine.mem readOutcome.inputAddress args.input ∧
    after.stdin = args.input ∧ after.stdinCursor = args.input.size ∧
    after.stdout = #[] ∧ after.exitCode = none ∧
    readCount ≤ contracts.readInputBound args.input.size ∧
    allocatorCount ≤ contracts.allocatorGetBound args.input.size

/-- Compose the two stack-address calculations and `auipc` before `decodeInput`. -/
theorem main_prepare_decode_call (contracts : Level1ResolvedContracts) (args : MainArgs)
    (fromStep : Nat) (before : EndpointState) (entry : MainEntry args before) :
    MainDecodeCallReady contracts args fromStep before := by
  obtain ⟨readCount, allocatorCount, allocatorState, readOutcome, allocatorOutcome,
      prefixTrace, readPositive, allocatorPositive, pc0, configured0, code0, dataAccess0,
      vtableExact, sp0,
      _a0, _a1, inputAddress0, inputLength0, _inputSize0, _inputAddress0,
      inputAddressRep0, inputSizeRep0, allocatorStateRep0, allocatorVtableRep0,
      savedReturnRep0, inputRep0, stdin0, cursor0, stdout0, exit0,
      readBounded, allocatorBounded⟩ :=
    main_call_allocator_get contracts args fromStep before entry
  let step0 := fromStep + (7 + readCount + allocatorCount)
  obtain ⟨retired0, run0⟩ := main_decode_result_address_step step0 allocatorState.machine
    configured0 (by simpa [EndpointPc] using pc0) code0 (MainAddiSource.stackPointer sp0)
  let value0 := iTypeResult .ADDI 0x20 (BitVec.ofNat 64 args.stackPointer)
  let machine1 := afterRegisterWrite allocatorState.machine 0x14cec retired0 x10 value0
  let state1 : EndpointState := { allocatorState with machine := machine1 }
  have value0Eq : value0 = BitVec.ofNat 64 (args.stackPointer + 0x20) := by
    apply BitVec.eq_of_toNat_eq
    simp only [value0, iTypeResult, BitVec.toNat_add, BitVec.toNat_ofNat]
    have immediateNat : (sign_extend (m := 64) (0x20 : BitVec 12)).toNat = 0x20 := by
      native_decide
    rw [immediateNat, Nat.mod_eq_of_lt (by
      have stackFits := entry.stackFits
      omega : args.stackPointer < 2 ^ 64)]
  have trace1 : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
      (8 + readCount + allocatorCount) before state1 := by
    simpa [step0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      prefixTrace.append (main_confined_sail_step step0 allocatorState machine1 0x14cec pc0
        mainGluePcs_14cec main14cec_not_syscall run0)
  have configured1 : ConfiguredMachinePre EndpointMachinePc machine1 :=
    ConfiguredMachinePre.afterRegisterWrite 0x14cec retired0 x10 value0 configured0 (by
      simp [instructionPreserved, platformPreserved])
  have code1 := fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
    allocatorState.machine 0x14cec retired0 x10 value0 code0
  have pc1 : EndpointPc state1 = some 0x14cf0 := by
    simpa [state1, EndpointPc, MachinePc, machine1] using
      afterRegisterWrite_pc allocatorState.machine 0x14cec retired0 x10 value0
  have sp1 := (afterRegisterWrite_writes allocatorState.machine 0x14cec retired0 x10 value0).get
    x2 (by decide) |>.trans sp0
  let step1 := fromStep + (8 + readCount + allocatorCount)
  obtain ⟨retired1, run1⟩ := main_decode_allocator_address_step step1 machine1 configured1
    (by simpa [state1, EndpointPc] using pc1) code1 (MainAddiSource.stackPointer sp1)
  let value1 := iTypeResult .ADDI 0x10 (BitVec.ofNat 64 args.stackPointer)
  let machine2 := afterRegisterWrite machine1 0x14cf0 retired1 x11 value1
  let state2 : EndpointState := { state1 with machine := machine2 }
  have value1Eq : value1 = BitVec.ofNat 64 (args.stackPointer + 0x10) := by
    apply BitVec.eq_of_toNat_eq
    simp only [value1, iTypeResult, BitVec.toNat_add, BitVec.toNat_ofNat]
    have immediateNat : (sign_extend (m := 64) (0x10 : BitVec 12)).toNat = 0x10 := by
      native_decide
    rw [immediateNat, Nat.mod_eq_of_lt (by
      have stackFits := entry.stackFits
      omega : args.stackPointer < 2 ^ 64)]
  have trace2 : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
      (9 + readCount + allocatorCount) before state2 := by
    simpa [step1, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      trace1.append (main_confined_sail_step step1 state1 machine2 0x14cf0 pc1
        mainGluePcs_14cf0 main14cf0_not_syscall run1)
  have configured2 := ConfiguredMachinePre.afterRegisterWrite 0x14cf0 retired1 x11 value1
    configured1 (by simp [instructionPreserved, platformPreserved])
  have code2 := fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
    machine1 0x14cf0 retired1 x11 value1 code1
  have pc2 : EndpointPc state2 = some 0x14cf4 := by
    simpa [state2, EndpointPc, MachinePc, machine2] using
      afterRegisterWrite_pc machine1 0x14cf0 retired1 x11 value1
  let step2 := fromStep + (9 + readCount + allocatorCount)
  obtain ⟨retired2, run2⟩ := main_decode_call_base_step step2 machine2 configured2
    (by simpa [state2, EndpointPc] using pc2) code2
  let callBase := (0x14cf4 : BitVec 64) + sign_extend (m := 64) (0xffffd#20 ++ 0x000#12)
  let machine3 := afterRegisterWrite machine2 0x14cf4 retired2 x1 callBase
  let state3 : EndpointState := { state2 with machine := machine3 }
  have callBaseEq : callBase = 0x11cf4 := main_decode_call_base_value
  have writes0 := afterRegisterWrite_writes allocatorState.machine 0x14cec retired0 x10 value0
  have writes1 := afterRegisterWrite_writes machine1 0x14cf0 retired1 x11 value1
  have writes2 := afterRegisterWrite_writes machine2 0x14cf4 retired2 x1 callBase
  have memory3 : machine3.mem = allocatorState.machine.mem := by
    simp [machine3, machine2, machine1, afterRegisterWrite_mem]
  refine ⟨readCount, allocatorCount, state3, readOutcome, allocatorOutcome,
    (by simpa [state3, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      trace2.append (main_confined_sail_step step2 state2 machine3 0x14cf4 pc2
        mainGluePcs_14cf4 main14cf4_not_syscall run2)),
    readPositive, allocatorPositive,
    (by simpa [state3, EndpointPc, MachinePc, machine3] using
      afterRegisterWrite_pc machine2 0x14cf4 retired2 x1 callBase),
    ConfiguredMachinePre.afterRegisterWrite 0x14cf4 retired2 x1 callBase configured2 (by
      simp [instructionPreserved]),
    fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
      machine2 0x14cf4 retired2 x1 callBase code2,
    dataAccess0.of_pma_regions_eq
      ((writes2.get pma_regions (by decide)).trans
        ((writes1.get pma_regions (by decide)).trans (writes0.get pma_regions (by decide)))),
    vtableExact,
    (by simpa [state3, machine3, callBaseEq] using
      (afterRegisterWrite_destination machine2 0x14cf4 retired2 x1 callBase
        (by decide) (by decide))),
    (writes2.get x2 (by decide)).trans ((writes1.get x2 (by decide)).trans
      ((writes0.get x2 (by decide)).trans sp0)),
    (by simpa [state3, machine3, value0Eq] using
      (writes2.get x10 (by decide)).trans ((writes1.get x10 (by decide)).trans
        (afterRegisterWrite_destination allocatorState.machine 0x14cec retired0 x10 value0
          (by decide) (by decide)))),
    (by
      have x11Final := (writes2.get x11 (by decide)).trans
        (afterRegisterWrite_destination machine1 0x14cf0 retired1 x11 value1
          (by decide) (by decide))
      simpa [state3, machine3, value1Eq] using x11Final),
    (writes2.get x12 (by decide)).trans ((writes1.get x12 (by decide)).trans
      ((writes0.get x12 (by decide)).trans inputAddress0)),
    (writes2.get x13 (by decide)).trans ((writes1.get x13 (by decide)).trans
      ((writes0.get x13 (by decide)).trans inputLength0)),
    UIntRep.of_mem_eq inputAddressRep0 memory3,
    UIntRep.of_mem_eq inputSizeRep0 memory3,
    UIntRep.of_mem_eq allocatorStateRep0 memory3,
    UIntRep.of_mem_eq allocatorVtableRep0 memory3,
    UIntRep.of_mem_eq savedReturnRep0 memory3,
    (by simpa [BytesRep, memory3] using inputRep0),
    (by simpa [state3, state2, state1] using stdin0),
    (by simpa [state3, state2, state1] using cursor0),
    (by simpa [state3, state2, state1] using stdout0),
    (by simpa [state3, state2, state1] using exit0), readBounded, allocatorBounded⟩

/-- Handoff after the opaque decoder returns to the parent status load at `0x14cfc`. -/
def MainDecodeHandoff (contracts : Level1ResolvedContracts) (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ (readCount allocatorCount decodeCount : Nat) (after : EndpointState)
      (readOutcome : ReadInputOutcome) (allocatorOutcome : AllocatorGetOutcome)
      (decodeOutcome : DecodeBoundaryOutcome),
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
      (11 + readCount + allocatorCount + decodeCount) before after ∧
    0 < readCount ∧ 0 < allocatorCount ∧ 0 < decodeCount ∧
    DecodeMeaningModuloKnownBugs
      { returnAddress := 0x14cfc, savedReturnAddress := args.returnAddress,
        inputAddress := readOutcome.inputAddress,
        input := args.input, stackPointer := args.stackPointer,
        allocatorStateAddress := allocatorOutcome.stateAddress,
        allocatorVtableAddress := allocatorOutcome.vtableAddress }
      decodeOutcome ∧
    EndpointPc after = some 0x14cfc ∧
    ConfiguredMachinePre EndpointMachinePc after.machine ∧
    Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    MainDataAccess args after.machine ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    UIntRep 8 after.machine.mem args.stackPointer readOutcome.inputAddress ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 8) args.input.size ∧
    UIntRep 8 after.machine.mem (args.stackPointer + 0x378) args.returnAddress ∧
    BytesRep after.machine.mem readOutcome.inputAddress args.input ∧
    after.stdin = args.input ∧ after.stdinCursor = args.input.size ∧
    after.stdout = #[] ∧ after.exitCode = none ∧
    (match decodeOutcome with
    | .failure => ∃ status : Nat, status ≠ 0 ∧ status < 2 ^ 16 ∧
        UIntRep 2 after.machine.mem (args.stackPointer + 0x370) status ∧
        DecodeStatusLoadWitness after status
    | .success decoded =>
        UIntRep 2 after.machine.mem (args.stackPointer + 0x370) 0 ∧
        DecodeStatusLoadWitness after 0 ∧
        StatelessInputRep after.machine.mem (args.stackPointer + 0x20) decoded) ∧
    readCount ≤ contracts.readInputBound args.input.size ∧
    allocatorCount ≤ contracts.allocatorGetBound args.input.size ∧
    decodeCount ≤ contracts.decodeBound args.input.size

/-- Execute the exact decoder call instruction and consume `hLevel1.sszDecode`. -/
theorem main_call_decode (contracts : Level1ResolvedContracts) (args : MainArgs)
    (fromStep : Nat) (before : EndpointState) (entry : MainEntry args before) :
    MainDecodeHandoff contracts args fromStep before := by
  obtain ⟨readCount, allocatorCount, ready, readOutcome, allocatorOutcome, prefixTrace,
      readPositive, allocatorPositive, atPc, configured, code, dataAccess, vtableExact,
      callBase, sp, resultAddress,
      allocatorAddress, inputAddress, inputLength, inputAddressRep, inputSizeRep,
      allocatorStateRep, allocatorVtableRep, savedReturnRep, inputRep,
      stdin, cursor, stdout, exitCode, readBounded, allocatorBounded⟩ :=
    main_prepare_decode_call contracts args fromStep before entry
  let callStep := fromStep + (10 + readCount + allocatorCount)
  obtain ⟨retired, run⟩ := main_decode_call_step callStep ready.machine configured
    (by simpa [EndpointPc] using atPc) callBase code
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement ready.machine) 0x14cf8 0x12168 x1 0x14cfc)
    0x12168 retired
  let callState : EndpointState := { ready with machine := callMachine }
  have callWrites := callRetirement_writes ready.machine 0x14cf8 0x12168 retired x1 0x14cfc
  have callDataAccess : MainDataAccess args callMachine :=
    dataAccess.of_pma_regions_eq (callWrites.get pma_regions (by decide))
  have callTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
      (11 + readCount + allocatorCount) before callState := by
    simpa [callState, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      prefixTrace.append (main_confined_sail_step callStep ready callMachine 0x14cf8 atPc
        mainGluePcs_14cf8 main14cf8_not_syscall run)
  have callCode : Artifacts.programImage.fileBytesLoadedFaithfully callMachine.mem := by
    simpa [callMachine, callLinkState, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement] using code
  have callMemory : callMachine.mem = ready.machine.mem := by
    simp [callMachine, callLinkState, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement]
  let decodeArgs : DecodeBoundaryArgs :=
    { returnAddress := 0x14cfc, savedReturnAddress := args.returnAddress,
      inputAddress := readOutcome.inputAddress,
      input := args.input, stackPointer := args.stackPointer,
      allocatorStateAddress := allocatorOutcome.stateAddress,
      allocatorVtableAddress := allocatorOutcome.vtableAddress }
  have decodeEntry : DecodeBoundaryEntry decodeArgs callState := by
    refine ⟨(by simpa [callState] using stdin), decodeInputExitPc_14cfc,
      (by simpa [decodeArgs] using vtableExact), ?_, callCode,
      entry.stackFits, inputRep.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [callState, callMachine, EndpointPc, MachinePc, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, Elflings.decodeInputEntry]
    · exact (callWrites.get x2 (by decide)).trans sp
    · change callMachine.regs.get? x1 = some (BitVec.ofNat 64 decodeArgs.returnAddress)
      simp [decodeArgs, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
    · exact (callWrites.get x10 (by decide)).trans resultAddress
    · exact (callWrites.get x11 (by decide)).trans allocatorAddress
    · exact (callWrites.get x12 (by decide)).trans inputAddress
    · exact (callWrites.get x13 (by decide)).trans inputLength
    · exact UIntRep.of_mem_eq inputAddressRep callMemory
    · exact UIntRep.of_mem_eq inputSizeRep callMemory
    · exact UIntRep.of_mem_eq allocatorStateRep callMemory
    · exact UIntRep.of_mem_eq allocatorVtableRep callMemory
    · simpa [callState, decodeArgs] using UIntRep.of_mem_eq savedReturnRep callMemory
    · simpa [callState, BytesRep, callMemory] using inputRep
  let stepBound := contracts.decodeBound
  let implements := contracts.sszDecode
  obtain ⟨decodeCount, after, decodeOutcome, decodePositive, decodeBounded, decodeTrace,
      _exitPc, meaning, decodeExit⟩ :=
    implements decodeArgs (fromStep + (11 + readCount + allocatorCount)) callState decodeEntry
  rcases decodeExit with ⟨afterPc, afterStdin, afterCursor, afterStdout, afterExitCode,
    afterStack, afterInputAddressRep, afterInputSizeRep, afterSavedReturn, afterInputRep,
    afterCode, _choice, _tags, _sailOutput, callFrame, outcomeRep⟩
  have wideDecode : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
      (fromStep + (11 + readCount + allocatorCount)) decodeCount callState after :=
    decodeTrace.weaken (fun pc inside => Or.inr (Or.inr (Or.inr (Or.inl inside))))
  refine ⟨readCount, allocatorCount, decodeCount, after, readOutcome, allocatorOutcome,
    decodeOutcome,
    (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      callTrace.append wideDecode),
    readPositive, allocatorPositive, decodePositive, meaning,
    (by simpa [EndpointPc] using afterPc),
    ConfiguredMachinePre.of_endpointCallFrame
      (ConfiguredMachinePre.afterCall 0x14cf8 0x12168 0x14cfc retired configured) callFrame,
    afterCode,
    callDataAccess.of_pma_regions_eq
      (callFrame.1 pma_regions (by simp [abiCalleePreserved])),
    (by simpa [decodeArgs] using afterStack),
    (by simpa [decodeArgs] using afterInputAddressRep),
    (by simpa [decodeArgs] using afterInputSizeRep),
    (by simpa [decodeArgs] using afterSavedReturn),
    (by simpa [decodeArgs] using afterInputRep),
    afterStdin.trans (by simpa [callState] using stdin),
    afterCursor.trans (by simpa [callState] using cursor),
    afterStdout.trans (by simpa [callState] using stdout),
    afterExitCode.trans (by simpa [callState] using exitCode), outcomeRep,
    readBounded, allocatorBounded, decodeBounded⟩

/-- Handoff after main loads the decoder status into `a0`, immediately before its branch. -/
def MainStatusLoadedHandoff (contracts : Level1ResolvedContracts) (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ (readCount allocatorCount decodeCount : Nat) (after : EndpointState)
      (readOutcome : ReadInputOutcome) (allocatorOutcome : AllocatorGetOutcome)
      (decodeOutcome : DecodeBoundaryOutcome),
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
      (12 + readCount + allocatorCount + decodeCount) before after ∧
    0 < readCount ∧ 0 < allocatorCount ∧ 0 < decodeCount ∧
    DecodeMeaningModuloKnownBugs
      { returnAddress := 0x14cfc, savedReturnAddress := args.returnAddress,
        inputAddress := readOutcome.inputAddress, input := args.input,
        stackPointer := args.stackPointer,
        allocatorStateAddress := allocatorOutcome.stateAddress,
        allocatorVtableAddress := allocatorOutcome.vtableAddress }
      decodeOutcome ∧
    EndpointPc after = some 0x14d00 ∧
    ConfiguredMachinePre EndpointMachinePc after.machine ∧
    Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    MainDataAccess args after.machine ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.stdin = args.input ∧ after.stdinCursor = args.input.size ∧
    after.stdout = #[] ∧ after.exitCode = none ∧
    (match decodeOutcome with
    | .failure => ∃ status : Nat, status ≠ 0 ∧ status < 2 ^ 16 ∧
        after.machine.regs.get? x10 =
          some (extend_value true (BitVec.ofNat 16 status))
    | .success decoded =>
        after.machine.regs.get? x10 = some (0#64) ∧
        StatelessInputRep after.machine.mem (args.stackPointer + 0x20) decoded) ∧
    readCount ≤ contracts.readInputBound args.input.size ∧
    allocatorCount ≤ contracts.allocatorGetBound args.input.size ∧
    decodeCount ≤ contracts.decodeBound args.input.size

/-- Execute the exact status `lhu` using the read witness exported by `sszDecode`. -/
theorem main_load_decode_status (contracts : Level1ResolvedContracts) (args : MainArgs)
    (fromStep : Nat) (before : EndpointState) (entry : MainEntry args before) :
    MainStatusLoadedHandoff contracts args fromStep before := by
  obtain ⟨readCount, allocatorCount, decodeCount, state, readOutcome, allocatorOutcome,
      decodeOutcome, prefixTrace, readPositive, allocatorPositive, decodePositive, meaning,
      atPc, configured, code, dataAccess, sp, _inputAddressRep, _inputSizeRep, _savedReturnRep,
      _inputRep, stdin, cursor, stdout, exitCode, outcomeRep,
      readBounded, allocatorBounded, decodeBounded⟩ :=
    main_call_decode contracts args fromStep before entry
  cases decodeOutcome with
  | failure =>
      rcases outcomeRep with ⟨status, statusNe, statusFits, _statusRep, access, accessData⟩
      obtain ⟨retired, run⟩ := main_decode_status_step
        (fromStep + (11 + readCount + allocatorCount + decodeCount)) state.machine configured
        (by simpa [EndpointPc] using atPc) code access
      let afterMachine := afterRegisterWrite state.machine 0x14cfc retired x10
        (extend_value true access.data)
      let after : EndpointState := { state with machine := afterMachine }
      have trace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (12 + readCount + allocatorCount + decodeCount) before after := by
        simpa [after, afterMachine, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          prefixTrace.append (main_confined_sail_step
            (fromStep + (11 + readCount + allocatorCount + decodeCount)) state afterMachine
            0x14cfc atPc mainGluePcs_14cfc main14cfc_not_syscall run)
      refine ⟨readCount, allocatorCount, decodeCount, after, readOutcome, allocatorOutcome,
        .failure, trace,
        readPositive, allocatorPositive, decodePositive, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ⟨status, statusNe, statusFits, ?_⟩, readBounded, allocatorBounded, decodeBounded⟩
      · simpa using meaning
      · simpa [after, EndpointPc, afterMachine] using
          afterRegisterWrite_pc state.machine 0x14cfc retired x10 (extend_value true access.data)
      · exact ConfiguredMachinePre.afterRegisterWrite 0x14cfc retired x10
          (extend_value true access.data) configured x10_not_instructionPreserved
      · simpa [after, afterMachine] using code
      · exact dataAccess.of_pma_regions_eq
          ((afterRegisterWrite_writes state.machine 0x14cfc retired x10
            (extend_value true access.data)).get pma_regions (by decide))
      · exact (afterRegisterWrite_writes state.machine 0x14cfc retired x10
          (extend_value true access.data)).get x2 (by decide) |>.trans sp
      · simpa [after] using stdin
      · simpa [after] using cursor
      · simpa [after] using stdout
      · simpa [after] using exitCode
      · simpa [after, afterMachine, accessData] using
          afterRegisterWrite_destination state.machine 0x14cfc retired x10
            (extend_value true access.data)
  | success decoded =>
      rcases outcomeRep with ⟨_statusRep, ⟨access, accessData⟩, decodedRep⟩
      obtain ⟨retired, run⟩ := main_decode_status_step
        (fromStep + (11 + readCount + allocatorCount + decodeCount)) state.machine configured
        (by simpa [EndpointPc] using atPc) code access
      let afterMachine := afterRegisterWrite state.machine 0x14cfc retired x10
        (extend_value true access.data)
      let after : EndpointState := { state with machine := afterMachine }
      have trace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (12 + readCount + allocatorCount + decodeCount) before after := by
        simpa [after, afterMachine, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          prefixTrace.append (main_confined_sail_step
            (fromStep + (11 + readCount + allocatorCount + decodeCount)) state afterMachine
            0x14cfc atPc mainGluePcs_14cfc main14cfc_not_syscall run)
      refine ⟨readCount, allocatorCount, decodeCount, after, readOutcome, allocatorOutcome,
        .success decoded, trace,
        readPositive, allocatorPositive, decodePositive, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ⟨?_, ?_⟩, readBounded, allocatorBounded, decodeBounded⟩
      · simpa using meaning
      · simpa [after, EndpointPc, afterMachine] using
          afterRegisterWrite_pc state.machine 0x14cfc retired x10 (extend_value true access.data)
      · exact ConfiguredMachinePre.afterRegisterWrite 0x14cfc retired x10
          (extend_value true access.data) configured x10_not_instructionPreserved
      · simpa [after, afterMachine] using code
      · exact dataAccess.of_pma_regions_eq
          ((afterRegisterWrite_writes state.machine 0x14cfc retired x10
            (extend_value true access.data)).get pma_regions (by decide))
      · exact (afterRegisterWrite_writes state.machine 0x14cfc retired x10
          (extend_value true access.data)).get x2 (by decide) |>.trans sp
      · simpa [after] using stdin
      · simpa [after] using cursor
      · simpa [after] using stdout
      · simpa [after] using exitCode
      · simpa [after, afterMachine, accessData, extend_value, zero_extend] using
          afterRegisterWrite_destination state.machine 0x14cfc retired x10
            (extend_value true access.data)
      · simpa [after, afterMachine, afterRegisterWrite_mem] using decodedRep

/-- Handoff after the exact status branch selects main's success or failure route. -/
def MainStatusBranchedHandoff (contracts : Level1ResolvedContracts) (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ (readCount allocatorCount decodeCount : Nat) (after : EndpointState)
      (readOutcome : ReadInputOutcome) (allocatorOutcome : AllocatorGetOutcome)
      (decodeOutcome : DecodeBoundaryOutcome),
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
      (13 + readCount + allocatorCount + decodeCount) before after ∧
    0 < readCount ∧ 0 < allocatorCount ∧ 0 < decodeCount ∧
    DecodeMeaningModuloKnownBugs
      { returnAddress := 0x14cfc, savedReturnAddress := args.returnAddress,
        inputAddress := readOutcome.inputAddress, input := args.input,
        stackPointer := args.stackPointer,
        allocatorStateAddress := allocatorOutcome.stateAddress,
        allocatorVtableAddress := allocatorOutcome.vtableAddress }
      decodeOutcome ∧
    ConfiguredMachinePre EndpointMachinePc after.machine ∧
    Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    MainDataAccess args after.machine ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.stdin = args.input ∧ after.stdinCursor = args.input.size ∧
    after.stdout = #[] ∧ after.exitCode = none ∧
    (match decodeOutcome with
    | .failure => EndpointPc after = some 0x14d1c
    | .success decoded => EndpointPc after = some 0x14d04 ∧
        StatelessInputRep after.machine.mem (args.stackPointer + 0x20) decoded) ∧
    readCount ≤ contracts.readInputBound args.input.size ∧
    allocatorCount ≤ contracts.allocatorGetBound args.input.size ∧
    decodeCount ≤ contracts.decodeBound args.input.size

/-- Execute the exact `bnez` and expose the selected success or failure continuation. -/
theorem main_branch_decode_status (contracts : Level1ResolvedContracts) (args : MainArgs)
    (fromStep : Nat) (before : EndpointState) (entry : MainEntry args before) :
    MainStatusBranchedHandoff contracts args fromStep before := by
  obtain ⟨readCount, allocatorCount, decodeCount, state, readOutcome, allocatorOutcome,
      decodeOutcome, prefixTrace, readPositive, allocatorPositive, decodePositive, meaning,
      atPc, configured, code, dataAccess, sp, stdin, cursor, stdout, exitCode, outcomeRep,
      readBounded, allocatorBounded, decodeBounded⟩ :=
    main_load_decode_status contracts args fromStep before entry
  cases decodeOutcome with
  | failure =>
      rcases outcomeRep with ⟨status, statusNe, statusFits, statusAtState⟩
      let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state.machine) 0x14d00
      have statusAtPremise : premise.regs.get? x10 =
          some (extend_value true (BitVec.ofNat 16 status)) :=
        (stepPremiseState_writes state.machine 0x14d00).get x10 (by decide) |>.trans statusAtState
      have statusWordNe : BitVec.ofNat 16 status ≠ 0 := by
        intro equal
        have equalNat := congrArg BitVec.toNat equal
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt statusFits] at equalNat
        exact statusNe equalNat
      have extendedNe : extend_value true (BitVec.ofNat 16 status) ≠ 0 := by
        intro equal
        apply statusWordNe
        apply BitVec.eq_of_toNat_eq
        have equalNat := congrArg BitVec.toNat equal
        simpa [extend_value, zero_extend, BitVec.zeroExtend_eq_setWidth,
          BitVec.toNat_setWidth_of_le] using equalNat
      have condition : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 10#5) .BNE)
          premise premise true := by
        unfold bTypeTaken
        refine Runs.bind (rX_x10_run premise _ statusAtPremise) ?_
        refine Runs.bind (rX_x0_run premise) ?_
        change EStateM.Result.ok
          (extend_value true (BitVec.ofNat 16 status) != (0#64)) premise = .ok true premise
        congr 1
        exact bne_iff_ne.mpr extendedNe
      obtain ⟨retired, run⟩ := main_decode_status_failure_step
        (fromStep + (12 + readCount + allocatorCount + decodeCount)) state.machine configured
        (by simpa [EndpointPc] using atPc) code condition
      let afterMachine := tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state.machine) 0x14d00 0x14d1c)
        0x14d1c retired
      let after : EndpointState := { state with machine := afterMachine }
      have trace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (13 + readCount + allocatorCount + decodeCount) before after := by
        simpa [after, afterMachine, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          prefixTrace.append (main_confined_sail_step
            (fromStep + (12 + readCount + allocatorCount + decodeCount)) state afterMachine
            0x14d00 atPc (by
              unfold mainGluePcs
              refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
            (by unfold BareMetalHostTransitionPc; native_decide) run)
      refine ⟨readCount, allocatorCount, decodeCount, after, readOutcome, allocatorOutcome,
        .failure, trace, readPositive, allocatorPositive, decodePositive, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, readBounded, allocatorBounded, decodeBounded⟩
      · simpa using meaning
      · exact ConfiguredMachinePre.afterJump 0x14d00 0x14d1c retired configured
      · simpa [after, afterMachine] using code
      · exact dataAccess.of_pma_regions_eq
          ((jumpRetirement_writes state.machine 0x14d00 0x14d1c retired).get pma_regions
            (by decide))
      · exact (jumpRetirement_writes state.machine 0x14d00 0x14d1c retired).get x2
          (by decide) |>.trans sp
      · simpa [after] using stdin
      · simpa [after] using cursor
      · simpa [after] using stdout
      · simpa [after] using exitCode
      · simp [after, EndpointPc, MachinePc, afterMachine, tryStepControlFlowAfterRetired,
          tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  | success decoded =>
      rcases outcomeRep with ⟨statusAtState, decodedRep⟩
      let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state.machine) 0x14d00
      have statusAtPremise : premise.regs.get? x10 = some (0#64) :=
        (stepPremiseState_writes state.machine 0x14d00).get x10 (by decide) |>.trans statusAtState
      have condition : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 10#5) .BNE)
          premise premise false := by
        unfold bTypeTaken
        refine Runs.bind (rX_x10_run premise _ statusAtPremise) ?_
        refine Runs.bind (rX_x0_run premise) ?_
        rfl
      obtain ⟨retired, run⟩ := main_decode_status_success_step
        (fromStep + (12 + readCount + allocatorCount + decodeCount)) state.machine configured
        (by simpa [EndpointPc] using atPc) code condition
      let afterMachine := tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state.machine) 0x14d00)
        0x14d04 retired
      let after : EndpointState := { state with machine := afterMachine }
      have trace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (13 + readCount + allocatorCount + decodeCount) before after := by
        simpa [after, afterMachine, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          prefixTrace.append (main_confined_sail_step
            (fromStep + (12 + readCount + allocatorCount + decodeCount)) state afterMachine
            0x14d00 atPc (by
              unfold mainGluePcs
              refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
            (by unfold BareMetalHostTransitionPc; native_decide) run)
      refine ⟨readCount, allocatorCount, decodeCount, after, readOutcome, allocatorOutcome,
        .success decoded, trace, readPositive, allocatorPositive, decodePositive, ?_, ?_, ?_, ?_,
        ?_,
        ?_, ?_, ?_, ?_, ?_, readBounded, allocatorBounded, decodeBounded⟩
      · simpa using meaning
      · exact ConfiguredMachinePre.afterFallThrough 0x14d00 0x14d04 retired configured
      · simpa [after, afterMachine] using code
      · exact dataAccess.of_pma_regions_eq
          ((fallThroughRetirement_writes state.machine 0x14d00 0x14d04 retired).get pma_regions
            (by decide))
      · exact (fallThroughRetirement_writes state.machine 0x14d00 0x14d04 retired).get x2
          (by decide) |>.trans sp
      · simpa [after] using stdin
      · simpa [after] using cursor
      · simpa [after] using stdout
      · simpa [after] using exitCode
      · constructor
        · simp [after, EndpointPc, MachinePc, afterMachine, tryStepControlFlowAfterRetired,
            tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
        · rw [show after.machine.mem = state.machine.mem by rfl]
          exact decodedRep

/-- The status-selected route after the successful observation has been written. A rejected input
remains at the first failure-route instruction; it performs no output work in this theorem. -/
def MainOutputSelectedHandoff (contracts : Level1ResolvedContracts) (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ (readCount allocatorCount decodeCount routeCount : Nat) (after : EndpointState)
      (readOutcome : ReadInputOutcome) (allocatorOutcome : AllocatorGetOutcome)
      (decodeOutcome : DecodeBoundaryOutcome),
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
      (13 + readCount + allocatorCount + decodeCount + routeCount) before after ∧
    0 < readCount ∧ 0 < allocatorCount ∧ 0 < decodeCount ∧
    DecodeMeaningModuloKnownBugs
      { returnAddress := 0x14cfc, savedReturnAddress := args.returnAddress,
        inputAddress := readOutcome.inputAddress, input := args.input,
        stackPointer := args.stackPointer,
        allocatorStateAddress := allocatorOutcome.stateAddress,
        allocatorVtableAddress := allocatorOutcome.vtableAddress }
      decodeOutcome ∧
    ConfiguredMachinePre EndpointMachinePc after.machine ∧
    Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    MainDataAccess args after.machine ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.stdin = args.input ∧ after.stdinCursor = args.input.size ∧
    after.exitCode = none ∧
    (match decodeOutcome with
    | .failure => routeCount = 0 ∧ EndpointPc after = some 0x14d1c ∧ after.stdout = #[]
    | .success decoded => ∃ bytes writeCount,
        routeCount = 3 + writeCount ∧ 0 < writeCount ∧
        EndpointPc after = some 0x14d10 ∧ after.stdout = bytes ∧
        decodeZesuObservation bytes = some (.success decoded)) ∧
    readCount ≤ contracts.readInputBound args.input.size ∧
    allocatorCount ≤ contracts.allocatorGetBound args.input.size ∧
    decodeCount ≤ contracts.decodeBound args.input.size ∧
    routeCount ≤ 3 + contracts.writeSuccessBound args.input.size

/-- Execute the successful result-address and call-base instructions, enter `writeSuccess`, and
consume its reviewed Level 1 contract. -/
theorem main_write_selected_output (contracts : Level1ResolvedContracts) (args : MainArgs)
    (fromStep : Nat) (before : EndpointState) (entry : MainEntry args before) :
    MainOutputSelectedHandoff contracts args fromStep before := by
  obtain ⟨readCount, allocatorCount, decodeCount, state, readOutcome, allocatorOutcome,
      decodeOutcome, prefixTrace, readPositive, allocatorPositive, decodePositive, meaning,
      configured, code, dataAccess, sp, stdin, cursor, stdout, exitCode, selected,
      readBounded, allocatorBounded, decodeBounded⟩ :=
    main_branch_decode_status contracts args fromStep before entry
  cases decodeOutcome with
  | failure =>
      refine ⟨readCount, allocatorCount, decodeCount, 0, state, readOutcome, allocatorOutcome,
        .failure, ?_, readPositive, allocatorPositive, decodePositive, meaning, configured, code,
        dataAccess, sp, stdin, cursor, exitCode, ?_, readBounded, allocatorBounded, decodeBounded,
        (by omega)⟩
      · simpa using prefixTrace
      · exact ⟨rfl, selected, stdout⟩
  | success decoded =>
      rcases selected with ⟨atPc, decodedRep⟩
      let step0 := fromStep + (13 + readCount + allocatorCount + decodeCount)
      obtain ⟨retired0, run0⟩ := main_success_result_address_step step0 state.machine configured
        (by simpa [EndpointPc] using atPc) code (MainAddiSource.stackPointer sp)
      let value0 := iTypeResult .ADDI 0x20 (BitVec.ofNat 64 args.stackPointer)
      let machine1 := afterRegisterWrite state.machine 0x14d04 retired0 x10 value0
      let state1 : EndpointState := { state with machine := machine1 }
      have value0Eq : value0 = BitVec.ofNat 64 (args.stackPointer + 0x20) := by
        apply BitVec.eq_of_toNat_eq
        simp only [value0, iTypeResult, BitVec.toNat_add, BitVec.toNat_ofNat]
        have immediateNat : (sign_extend (m := 64) (0x20 : BitVec 12)).toNat = 0x20 := by
          native_decide
        have frameBound := entry.stackFits
        rw [immediateNat, Nat.mod_eq_of_lt (by omega : args.stackPointer < 2 ^ 64)]
      have trace1 : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (14 + readCount + allocatorCount + decodeCount) before state1 := by
        simpa [step0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          prefixTrace.append (main_confined_sail_step step0 state machine1 0x14d04 atPc
            (by unfold mainGluePcs; refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
            (by unfold BareMetalHostTransitionPc; native_decide) run0)
      have configured1 := ConfiguredMachinePre.afterRegisterWrite 0x14d04 retired0 x10 value0
        configured x10_not_instructionPreserved
      have code1 := fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
        state.machine 0x14d04 retired0 x10 value0 code
      have pc1 : EndpointPc state1 = some 0x14d08 := by
        simpa [state1, EndpointPc, MachinePc, machine1] using
          afterRegisterWrite_pc state.machine 0x14d04 retired0 x10 value0
      obtain ⟨retired1, run1⟩ := main_write_success_call_base_step (step0 + 1) machine1
        configured1 (by simpa [state1, EndpointPc] using pc1) code1
      let machine2 := afterRegisterWrite machine1 0x14d08 retired1 x1 0x14d08
      let state2 : EndpointState := { state1 with machine := machine2 }
      have trace2 : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (15 + readCount + allocatorCount + decodeCount) before state2 := by
        have stepTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
            (fromStep + (14 + readCount + allocatorCount + decodeCount)) 1 state1 state2 := by
          simpa [step0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            main_confined_sail_step (step0 + 1) state1 machine2 0x14d08 pc1
              (by unfold mainGluePcs; refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
              (by unfold BareMetalHostTransitionPc; native_decide) run1
        simpa [step0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          trace1.append stepTrace
      have configured2 := ConfiguredMachinePre.afterRegisterWrite 0x14d08 retired1 x1 0x14d08
        configured1 (by simp [instructionPreserved])
      have code2 := fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
        machine1 0x14d08 retired1 x1 0x14d08 code1
      have pc2 : EndpointPc state2 = some 0x14d0c := by
        simpa [state2, EndpointPc, MachinePc, machine2] using
          afterRegisterWrite_pc machine1 0x14d08 retired1 x1 0x14d08
      have base2 : machine2.regs.get? x1 = some 0x14d08 := by
        simpa [machine2] using
          afterRegisterWrite_destination machine1 0x14d08 retired1 x1 (0x14d08 : BitVec 64)
      obtain ⟨retired2, run2⟩ := main_write_success_call_step (step0 + 2) machine2 configured2
        (by simpa [state2, EndpointPc] using pc2) base2 code2
      let callMachine := tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement machine2) 0x14d0c 0x14d30 x1 0x14d10)
        0x14d30 retired2
      let callState : EndpointState := { state2 with machine := callMachine }
      have callWrites := callRetirement_writes machine2 0x14d0c 0x14d30 retired2 x1 0x14d10
      have callTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (16 + readCount + allocatorCount + decodeCount) before callState := by
        have stepTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
            (fromStep + (15 + readCount + allocatorCount + decodeCount)) 1 state2 callState := by
          simpa [callState, step0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            main_confined_sail_step (step0 + 2) state2 callMachine 0x14d0c pc2
              (by unfold mainGluePcs; refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
              (by unfold BareMetalHostTransitionPc; native_decide) run2
        simpa [callState, step0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          trace2.append stepTrace
      have callCode : Artifacts.programImage.fileBytesLoadedFaithfully callMachine.mem := by
        simpa [callMachine, callLinkState, tryStepControlFlowAfterRetired,
          tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement] using code2
      have callMemory : callMachine.mem = state.machine.mem := by
        simp [callMachine, machine2, machine1, callLinkState, tryStepControlFlowAfterRetired,
          tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
          tryStepControlFlowAfterIncrement, afterRegisterWrite_mem]
      let writeArgs : WriteSuccessArgs :=
        { returnAddress := 0x14d10, stackPointer := args.stackPointer,
          decodedAddress := args.stackPointer + 0x20, decoded, inputSize := args.input.size }
      have writeEntry : WriteSuccessEntry writeArgs callState := by
        refine ⟨(by show 0x14d10 ∈ Elflings.writeSuccessExitPcs; native_decide),
          entry.stackLower, ?_, ?_, ?_, ?_, ?_, callCode⟩
        · simp [callState, callMachine, EndpointPc, MachinePc, tryStepControlFlowAfterRetired,
            tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, Elflings.writeSuccessEntry]
        · simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
            tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, writeArgs]
        · exact (callWrites.get x2 (by decide)).trans
            ((afterRegisterWrite_writes machine1 0x14d08 retired1 x1 0x14d08).get x2
              (by decide) |>.trans
            ((afterRegisterWrite_writes state.machine 0x14d04 retired0 x10 value0).get x2
              (by decide) |>.trans sp))
        · simpa [callState, writeArgs, value0Eq] using
            (callWrites.get x10 (by decide)).trans
              ((afterRegisterWrite_writes machine1 0x14d08 retired1 x1 0x14d08).get x10
                (by decide) |>.trans
              (afterRegisterWrite_destination state.machine 0x14d04 retired0 x10 value0
                (by decide) (by decide)))
        · simpa [callState, writeArgs, callMemory] using decodedRep
      let stepBound := contracts.writeSuccessBound
      let implements := contracts.writeSuccess
      obtain ⟨writeCount, after, bytes, writePositive, writeBounded, writeTrace, _writeExit,
          _writeAllowed, writePost⟩ := implements writeArgs
        (fromStep + (16 + readCount + allocatorCount + decodeCount)) callState writeEntry
      rcases writePost with ⟨afterPc, observed, afterStdout, afterStdin, afterCursor,
        afterExitCode, _memoryFrame, callFrame⟩
      have wideWrite : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
          (fromStep + (16 + readCount + allocatorCount + decodeCount)) writeCount callState after :=
        writeTrace.weaken (fun pc inside => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl inside)))))
      have writeBounded' : writeCount ≤ contracts.writeSuccessBound args.input.size := by
        simpa [writeSuccessContract, writeArgs] using writeBounded
      refine ⟨readCount, allocatorCount, decodeCount, 3 + writeCount, after, readOutcome,
        allocatorOutcome, .success decoded, ?_, readPositive, allocatorPositive, decodePositive,
        meaning, ?_, callFrame.2.2.1, ?_, ?_, ?_, ?_, ?_,
        ⟨bytes, writeCount, rfl, writePositive, (by simpa [EndpointPc] using afterPc), ?_, observed⟩,
        readBounded, allocatorBounded, decodeBounded, (by omega)⟩
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using callTrace.append wideWrite
      · exact ConfiguredMachinePre.of_endpointCallFrame
          (ConfiguredMachinePre.afterCall 0x14d0c 0x14d30 0x14d10 retired2 configured2) callFrame
      · exact (dataAccess.of_pma_regions_eq
          ((afterRegisterWrite_writes state.machine 0x14d04 retired0 x10 value0).get pma_regions
            (by decide))).of_pma_regions_eq
          ((afterRegisterWrite_writes machine1 0x14d08 retired1 x1 0x14d08).get pma_regions
            (by decide)) |>.of_pma_regions_eq (callWrites.get pma_regions (by decide))
          |>.of_pma_regions_eq (callFrame.1 pma_regions (by simp [abiCalleePreserved]))
      · exact callFrame.1 x2 (by simp [abiCalleePreserved]) |>.trans
          ((callWrites.get x2 (by decide)).trans
            ((afterRegisterWrite_writes machine1 0x14d08 retired1 x1 0x14d08).get x2
              (by decide) |>.trans
            ((afterRegisterWrite_writes state.machine 0x14d04 retired0 x10 value0).get x2
              (by decide) |>.trans sp)))
      · exact afterStdin.trans (by simpa [callState, state2, state1] using stdin)
      · exact afterCursor.trans (by simpa [callState, state2, state1] using cursor)
      · exact afterExitCode.trans (by simpa [callState, state2, state1] using exitCode)
      · calc
          after.stdout = callState.stdout ++ bytes := afterStdout
          _ = bytes := by simp [callState, state2, state1, stdout]

/-- The successful route has reached the terminal exit contract; a rejected input remains at its
first output instruction with every fact required to compose that route. -/
def MainSuccessExitedHandoff (contracts : Level1ResolvedContracts) (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ (used : Nat) (after : EndpointState) (outcome : MainOutcome),
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep used before after ∧
    0 < used ∧ MainMeaningModulo knownBugs args outcome ∧
    match outcome with
    | .failure => EndpointPc after = some 0x14d1c ∧
        ConfiguredMachinePre EndpointMachinePc after.machine ∧
        Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
        MainDataAccess args after.machine ∧
        after.stdin = args.input ∧ after.stdinCursor = args.input.size ∧
        after.stdout = #[] ∧ after.exitCode = none ∧
        used + 5 + contracts.writeFailureBound + contracts.zkvmExitBound ≤
          level0ResolvedStepBound contracts args.input.size
    | .success decoded => MainExit args (.success decoded) before after ∧
        used ≤ level0ResolvedStepBound contracts args.input.size

/-- Complete the successful `zkvm_exit` route while retaining the rejected-input route for the
next composition theorem. -/
theorem main_exit_success_or_select_failure (contracts : Level1ResolvedContracts) (args : MainArgs)
    (fromStep : Nat) (before : EndpointState) (entry : MainEntry args before) :
    MainSuccessExitedHandoff contracts args fromStep before := by
  obtain ⟨readCount, allocatorCount, decodeCount, routeCount, state, readOutcome,
      allocatorOutcome, decodeOutcome, prefixTrace, readPositive, allocatorPositive,
      decodePositive, meaning, configured, code, dataAccess, _sp, stdin, cursor, exitCode, selected,
      readBounded, allocatorBounded, decodeBounded, routeBounded⟩ :=
    main_write_selected_output contracts args fromStep before entry
  cases decodeOutcome with
  | failure =>
      rcases selected with ⟨routeZero, atPc, stdout⟩
      refine ⟨13 + readCount + allocatorCount + decodeCount, state, .failure, ?_, (by omega), ?_, atPc,
        configured, code, dataAccess, stdin, cursor, stdout, exitCode, ?_⟩
      · simpa [routeZero] using prefixTrace
      · change ¬∃ decoded, SailDecode args.input decoded
        exact meaning
      · unfold level0ResolvedStepBound
        omega
  | success decoded =>
      rcases selected with ⟨bytes, writeCount, routeEq, writePositive, atPc, stdout, observed⟩
      subst routeCount
      let step0 := fromStep + (16 + readCount + allocatorCount + decodeCount + writeCount)
      obtain ⟨retired0, run0⟩ := main_success_exit_code_step step0 state.machine configured
        (by simpa [EndpointPc] using atPc) code
      let machine1 := afterRegisterWrite state.machine 0x14d10 retired0 x10 0
      let state1 : EndpointState := { state with machine := machine1 }
      have trace1 : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (17 + readCount + allocatorCount + decodeCount + writeCount) before state1 := by
        have normalizedPrefix : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
            (16 + readCount + allocatorCount + decodeCount + writeCount) before state := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using prefixTrace
        have stepTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
            (fromStep + (16 + readCount + allocatorCount + decodeCount + writeCount)) 1
            state state1 :=
          main_confined_sail_step step0 state machine1 0x14d10 atPc
            (by unfold mainGluePcs; refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
            (by unfold BareMetalHostTransitionPc; native_decide) run0
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          normalizedPrefix.append stepTrace
      have configured1 := ConfiguredMachinePre.afterRegisterWrite 0x14d10 retired0 x10 0
        configured x10_not_instructionPreserved
      have code1 := fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
        state.machine 0x14d10 retired0 x10 0 code
      have pc1 : EndpointPc state1 = some 0x14d14 := by
        simpa [state1, EndpointPc, MachinePc, machine1] using
          afterRegisterWrite_pc state.machine 0x14d10 retired0 x10 0
      have zero1 : machine1.regs.get? x10 = some (0#64) := by
        simpa [machine1] using
          afterRegisterWrite_destination state.machine 0x14d10 retired0 x10 (0#64)
            (by decide) (by decide)
      obtain ⟨retired1, run1⟩ := main_success_exit_call_base_step (step0 + 1) machine1
        configured1 (by simpa [state1, EndpointPc] using pc1) code1
      let machine2 := afterRegisterWrite machine1 0x14d14 retired1 x1 0xfd14
      let state2 : EndpointState := { state1 with machine := machine2 }
      have trace2 : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (18 + readCount + allocatorCount + decodeCount + writeCount) before state2 := by
        have stepTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
            (fromStep + (17 + readCount + allocatorCount + decodeCount + writeCount)) 1
            state1 state2 := by
          simpa [step0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            main_confined_sail_step (step0 + 1) state1 machine2 0x14d14 pc1
              (by unfold mainGluePcs; refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
              (by unfold BareMetalHostTransitionPc; native_decide) run1
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using trace1.append stepTrace
      have configured2 := ConfiguredMachinePre.afterRegisterWrite 0x14d14 retired1 x1 0xfd14
        configured1 (by simp [instructionPreserved])
      have code2 := fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
        machine1 0x14d14 retired1 x1 0xfd14 code1
      have pc2 : EndpointPc state2 = some 0x14d18 := by
        simpa [state2, EndpointPc, MachinePc, machine2] using
          afterRegisterWrite_pc machine1 0x14d14 retired1 x1 0xfd14
      have base2 : machine2.regs.get? x1 = some 0xfd14 := by
        simpa [machine2] using
          afterRegisterWrite_destination machine1 0x14d14 retired1 x1 (0xfd14 : BitVec 64)
            (by decide) (by decide)
      have zero2 : machine2.regs.get? x10 = some (0#64) :=
        (afterRegisterWrite_writes machine1 0x14d14 retired1 x1 0xfd14).get x10
          (by decide) |>.trans zero1
      obtain ⟨retired2, run2⟩ := main_success_exit_call_step (step0 + 2) machine2 configured2
        (by simpa [state2, EndpointPc] using pc2) base2 code2
      let callMachine := tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement machine2) 0x14d18 0x101c4 x1 0x14d1c)
        0x101c4 retired2
      let callState : EndpointState := { state2 with machine := callMachine }
      have callWrites := callRetirement_writes machine2 0x14d18 0x101c4 retired2 x1 0x14d1c
      have callTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (19 + readCount + allocatorCount + decodeCount + writeCount) before callState := by
        have stepTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
            (fromStep + (18 + readCount + allocatorCount + decodeCount + writeCount)) 1
            state2 callState := by
          simpa [callState, step0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            main_confined_sail_step (step0 + 2) state2 callMachine 0x14d18 pc2
              (by unfold mainGluePcs; refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
              (by unfold BareMetalHostTransitionPc; native_decide) run2
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using trace2.append stepTrace
      have callCode : Artifacts.programImage.fileBytesLoadedFaithfully callMachine.mem := by
        simpa [callMachine, callLinkState, tryStepControlFlowAfterRetired,
          tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement] using code2
      have callConfigured : ConfiguredMachinePre EndpointMachinePc callMachine :=
        ConfiguredMachinePre.afterCall 0x14d18 0x101c4 0x14d1c retired2 configured2
      have callDataAccess : MainDataAccess args callMachine :=
        (dataAccess.of_pma_regions_eq
          ((afterRegisterWrite_writes state.machine 0x14d10 retired0 x10 0).get pma_regions
            (by decide))).of_pma_regions_eq
          ((afterRegisterWrite_writes machine1 0x14d14 retired1 x1 0xfd14).get pma_regions
            (by decide)) |>.of_pma_regions_eq (callWrites.get pma_regions (by decide))
      have exitEntry : ZkvmExitEntry { code := 0 } callState := by
        refine ⟨?_, ?_, callDataAccess.exitCodeStore, callCode, callConfigured⟩
        · simp [callState, callMachine, EndpointPc, MachinePc, tryStepControlFlowAfterRetired,
            tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, Elflings.zkvmExitEntry]
        · exact (callWrites.get x10 (by decide)).trans zero2
      let stepBound := contracts.zkvmExitBound
      let implements := contracts.zkvmExit
      obtain ⟨exitCount, after, unit, exitPositive, exitBounded, exitTrace, _terminal,
          _allowed, exitPost⟩ := implements { code := 0 }
        (fromStep + (19 + readCount + allocatorCount + decodeCount + writeCount)) callState exitEntry
      rcases exitPost with ⟨terminalPc, finalCode, finalStdin, finalCursor, finalStdout, _memory⟩
      have exitBounded' : exitCount ≤ contracts.zkvmExitBound := by
        simpa [zkvmExitContract] using exitBounded
      have wideExit : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
          (fromStep + (19 + readCount + allocatorCount + decodeCount + writeCount)) exitCount
          callState after :=
        exitTrace.weaken (fun pc inside =>
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr inside))))))
      refine ⟨19 + readCount + allocatorCount + decodeCount + writeCount + exitCount,
        after, .success decoded, ?_, (by omega), ?_, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using callTrace.append wideExit
      · change (∃ sail, SailDecode args.input sail ∧
          decodedResultRelModuloKnownBugs args.input decoded sail) ∨
          ((¬∃ sail, SailDecode args.input sail) ∧
            ∃ bug ∈ knownBugs, KnownBugApplies args.input decoded bug)
        exact meaning
      · refine ⟨terminalPc, ?_, ?_, finalCode, bytes, ?_, observed⟩
        · exact finalStdin.trans (by simpa [callState, state2, state1] using stdin)
        · exact finalCursor.trans (by simpa [callState, state2, state1] using cursor)
        · exact finalStdout.trans (by simpa [callState, state2, state1] using stdout)
      · unfold level0ResolvedStepBound
        omega

/-- Complete Level 0 result: an exact confined endpoint trace, its semantic outcome, and `MainExit`. -/
def MainResolvedHandoff (contracts : Level1ResolvedContracts) (args : MainArgs)
    (fromStep : Nat) (before : EndpointState) : Prop :=
  ∃ (used : Nat) (after : EndpointState) (outcome : MainOutcome),
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep used before after ∧
    0 < used ∧ MainMeaningModulo knownBugs args outcome ∧ MainExit args outcome before after ∧
    used ≤ level0ResolvedStepBound contracts args.input.size

/-- Compose the rejected-input writer and terminal exit. The successful route is already complete
and is returned unchanged. -/
theorem main_resolved_handoff (contracts : Level1ResolvedContracts) (args : MainArgs)
    (fromStep : Nat) (before : EndpointState) (entry : MainEntry args before) :
    MainResolvedHandoff contracts args fromStep before := by
  obtain ⟨used, state, outcome, prefixTrace, usedPositive, meaning, selected⟩ :=
    main_exit_success_or_select_failure contracts args fromStep before entry
  cases outcome with
  | success decoded =>
      rcases selected with ⟨exited, bounded⟩
      exact ⟨used, state, .success decoded, prefixTrace, usedPositive, meaning, exited, bounded⟩
  | failure =>
      rcases selected with ⟨atPc, configured, code, dataAccess, stdin, cursor, stdout, exitCode,
        reserved⟩
      obtain ⟨retired0, run0⟩ := main_write_failure_call_base_step (fromStep + used)
        state.machine configured (by simpa [EndpointPc] using atPc) code
      let machine1 := afterRegisterWrite state.machine 0x14d1c retired0 x1 0x15d1c
      let state1 : EndpointState := { state with machine := machine1 }
      have trace1 : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep (used + 1)
          before state1 := by
        simpa [Nat.add_assoc] using prefixTrace.append
          (main_confined_sail_step (fromStep + used) state machine1 0x14d1c atPc
            (by unfold mainGluePcs; refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
            (by unfold BareMetalHostTransitionPc; native_decide) run0)
      have configured1 := ConfiguredMachinePre.afterRegisterWrite 0x14d1c retired0 x1 0x15d1c
        configured (by simp [instructionPreserved])
      have code1 := fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
        state.machine 0x14d1c retired0 x1 0x15d1c code
      have pc1 : EndpointPc state1 = some 0x14d20 := by
        simpa [state1, EndpointPc, MachinePc, machine1] using
          afterRegisterWrite_pc state.machine 0x14d1c retired0 x1 0x15d1c
      have base1 : machine1.regs.get? x1 = some 0x15d1c := by
        simpa [machine1] using
          afterRegisterWrite_destination state.machine 0x14d1c retired0 x1 (0x15d1c : BitVec 64)
            (by decide) (by decide)
      obtain ⟨retired1, run1⟩ := main_write_failure_call_step (fromStep + used + 1) machine1
        configured1 (by simpa [state1, EndpointPc] using pc1) base1 code1
      let callMachine := tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement machine1) 0x14d20 0x161c0 x1 0x14d24)
        0x161c0 retired1
      let callState : EndpointState := { state1 with machine := callMachine }
      have callTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep (used + 2)
          before callState := by
        have stepTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
            (fromStep + (used + 1)) 1 state1 callState := by
          simpa [callState, Nat.add_assoc] using
            main_confined_sail_step (fromStep + used + 1) state1 callMachine 0x14d20 pc1
              (by unfold mainGluePcs; refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
              (by unfold BareMetalHostTransitionPc; native_decide) run1
        simpa [Nat.add_assoc] using trace1.append stepTrace
      have callCode : Artifacts.programImage.fileBytesLoadedFaithfully callMachine.mem := by
        simpa [callMachine, callLinkState, tryStepControlFlowAfterRetired,
          tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement] using code1
      have failureEntry : WriteFailureEntry { returnAddress := 0x14d24 } callState := by
        refine ⟨(by show 0x14d24 ∈ Elflings.writeFailureExitPcs; native_decide), ?_, ?_, callCode⟩
        · simp [callState, callMachine, EndpointPc, MachinePc, tryStepControlFlowAfterRetired,
            tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, Elflings.writeFailureEntry]
        · simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
            tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
      let failureBound := contracts.writeFailureBound
      let failureImplements := contracts.writeFailure
      obtain ⟨failureCount, written, bytes, failurePositive, failureBounded, failureTrace,
          _failureExit, _failureAllowed, failurePost⟩ := failureImplements
        { returnAddress := 0x14d24 } (fromStep + (used + 2)) callState failureEntry
      rcases failurePost with ⟨writtenPc, observed, writtenStdout, writtenStdin, writtenCursor,
        writtenExitCode, writtenMemory, callFrame⟩
      have wideFailure : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
          (fromStep + (used + 2)) failureCount callState written :=
        failureTrace.weaken (fun pc inside =>
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl inside))))))
      have writtenTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (used + 2 + failureCount) before written := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using callTrace.append wideFailure
      have writtenConfigured := ConfiguredMachinePre.of_endpointCallFrame
        (ConfiguredMachinePre.afterCall 0x14d20 0x161c0 0x14d24 retired1 configured1) callFrame
      have writtenCode := callFrame.2.2.1
      have writtenDataAccess : MainDataAccess args written.machine :=
        (dataAccess.of_pma_regions_eq
          ((afterRegisterWrite_writes state.machine 0x14d1c retired0 x1 0x15d1c).get pma_regions
            (by decide))).of_pma_regions_eq
          ((callRetirement_writes machine1 0x14d20 0x161c0 retired1 x1 0x14d24).get pma_regions
            (by decide)) |>.of_pma_regions_eq
          (callFrame.1 pma_regions (by simp [abiCalleePreserved]))
      have writtenStdoutEq : written.stdout = bytes := by
        calc
          written.stdout = callState.stdout ++ bytes := writtenStdout
          _ = bytes := by simp [callState, state1, stdout]
      have writtenStdinEq : written.stdin = args.input :=
        writtenStdin.trans (by simpa [callState, state1] using stdin)
      have writtenCursorEq : written.stdinCursor = args.input.size :=
        writtenCursor.trans (by simpa [callState, state1] using cursor)
      have writtenExitEq : written.exitCode = none :=
        writtenExitCode.trans (by simpa [callState, state1] using exitCode)
      let step2 := fromStep + (used + 2 + failureCount)
      obtain ⟨retired2, run2⟩ := main_failure_exit_code_step step2 written.machine
        writtenConfigured (by simpa [EndpointPc] using writtenPc) writtenCode
      let machine3 := afterRegisterWrite written.machine 0x14d24 retired2 x10 0
      let state3 : EndpointState := { written with machine := machine3 }
      have trace3 : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (used + 3 + failureCount) before state3 := by
        have stepTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
            (fromStep + (used + 2 + failureCount)) 1 written state3 :=
          main_confined_sail_step step2 written machine3 0x14d24 writtenPc
            (by unfold mainGluePcs; refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
            (by unfold BareMetalHostTransitionPc; native_decide) run2
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using writtenTrace.append stepTrace
      have configured3 := ConfiguredMachinePre.afterRegisterWrite 0x14d24 retired2 x10 0
        writtenConfigured x10_not_instructionPreserved
      have code3 := fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
        written.machine 0x14d24 retired2 x10 0 writtenCode
      have pc3 : EndpointPc state3 = some 0x14d28 := by
        simpa [state3, EndpointPc, MachinePc, machine3] using
          afterRegisterWrite_pc written.machine 0x14d24 retired2 x10 0
      have zero3 : machine3.regs.get? x10 = some (0#64) := by
        simpa [machine3] using
          afterRegisterWrite_destination written.machine 0x14d24 retired2 x10 (0#64)
            (by decide) (by decide)
      obtain ⟨retired3, run3⟩ := main_failure_exit_call_base_step (step2 + 1) machine3
        configured3 (by simpa [state3, EndpointPc] using pc3) code3
      let machine4 := afterRegisterWrite machine3 0x14d28 retired3 x1 0xfd28
      let state4 : EndpointState := { state3 with machine := machine4 }
      have trace4 : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (used + 4 + failureCount) before state4 := by
        have stepTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
            (fromStep + (used + 3 + failureCount)) 1 state3 state4 := by
          simpa [step2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            main_confined_sail_step (step2 + 1) state3 machine4 0x14d28 pc3
              (by unfold mainGluePcs; refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
              (by unfold BareMetalHostTransitionPc; native_decide) run3
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using trace3.append stepTrace
      have configured4 := ConfiguredMachinePre.afterRegisterWrite 0x14d28 retired3 x1 0xfd28
        configured3 (by simp [instructionPreserved])
      have code4 := fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
        machine3 0x14d28 retired3 x1 0xfd28 code3
      have pc4 : EndpointPc state4 = some 0x14d2c := by
        simpa [state4, EndpointPc, MachinePc, machine4] using
          afterRegisterWrite_pc machine3 0x14d28 retired3 x1 0xfd28
      have base4 : machine4.regs.get? x1 = some 0xfd28 := by
        simpa [machine4] using
          afterRegisterWrite_destination machine3 0x14d28 retired3 x1 (0xfd28 : BitVec 64)
            (by decide) (by decide)
      have zero4 : machine4.regs.get? x10 = some (0#64) :=
        (afterRegisterWrite_writes machine3 0x14d28 retired3 x1 0xfd28).get x10
          (by decide) |>.trans zero3
      obtain ⟨retired4, run4⟩ := main_failure_exit_call_step (step2 + 2) machine4 configured4
        (by simpa [state4, EndpointPc] using pc4) base4 code4
      let exitMachine := tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement machine4) 0x14d2c 0x101c4 x1 0x14d30)
        0x101c4 retired4
      let exitState : EndpointState := { state4 with machine := exitMachine }
      have exitWrites := callRetirement_writes machine4 0x14d2c 0x101c4 retired4 x1 0x14d30
      have exitCallTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep
          (used + 5 + failureCount) before exitState := by
        have stepTrace : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
            (fromStep + (used + 4 + failureCount)) 1 state4 exitState := by
          simpa [exitState, step2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            main_confined_sail_step (step2 + 2) state4 exitMachine 0x14d2c pc4
              (by unfold mainGluePcs; refine ⟨(0x14cec, 0x14d30), ?_, ?_, ?_⟩ <;> native_decide)
              (by unfold BareMetalHostTransitionPc; native_decide) run4
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using trace4.append stepTrace
      have exitCodeLoaded : Artifacts.programImage.fileBytesLoadedFaithfully exitMachine.mem := by
        simpa [exitMachine, callLinkState, tryStepControlFlowAfterRetired,
          tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement] using code4
      have exitConfigured : ConfiguredMachinePre EndpointMachinePc exitMachine :=
        ConfiguredMachinePre.afterCall 0x14d2c 0x101c4 0x14d30 retired4 configured4
      have terminalEntry : ZkvmExitEntry { code := 0 } exitState := by
        have exitDataAccess :=
          (writtenDataAccess.of_pma_regions_eq
            ((afterRegisterWrite_writes written.machine 0x14d24 retired2 x10 0).get pma_regions
              (by decide))).of_pma_regions_eq
            ((afterRegisterWrite_writes machine3 0x14d28 retired3 x1 0xfd28).get pma_regions
              (by decide)) |>.of_pma_regions_eq (exitWrites.get pma_regions (by decide))
        refine ⟨?_, (exitWrites.get x10 (by decide)).trans zero4,
          exitDataAccess.exitCodeStore, exitCodeLoaded, exitConfigured⟩
        simp [exitState, exitMachine, EndpointPc, MachinePc, tryStepControlFlowAfterRetired,
          tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, Elflings.zkvmExitEntry]
      let exitBound := contracts.zkvmExitBound
      let exitImplements := contracts.zkvmExit
      obtain ⟨exitCount, after, unit, exitPositive, exitBounded, exitTrace, _terminal,
          _exitAllowed, exitPost⟩ := exitImplements { code := 0 }
        (fromStep + (used + 5 + failureCount)) exitState terminalEntry
      rcases exitPost with ⟨terminalPc, finalCode, finalStdin, finalCursor, finalStdout, _finalMem⟩
      have failureBounded' : failureCount ≤ contracts.writeFailureBound := by
        simpa [writeFailureContract] using failureBounded
      have exitBounded' : exitCount ≤ contracts.zkvmExitBound := by
        simpa [zkvmExitContract] using exitBounded
      have wideExit : ConfinedTrace EndpointStep EndpointPc MainExecutionPc
          (fromStep + (used + 5 + failureCount)) exitCount exitState after :=
        exitTrace.weaken (fun pc inside =>
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr inside))))))
      refine ⟨used + 5 + failureCount + exitCount, after, .failure, ?_, (by omega), meaning, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using exitCallTrace.append wideExit
      · refine ⟨terminalPc, ?_, ?_, finalCode, bytes, ?_, observed⟩
        · exact finalStdin.trans (by simpa [exitState, state4, state3] using writtenStdinEq)
        · exact finalCursor.trans (by simpa [exitState, state4, state3] using writtenCursorEq)
        · exact finalStdout.trans (by simpa [exitState, state4, state3] using writtenStdoutEq)
      · omega

end BinaryFv.Zesu
