import BinaryFv.Zesu.MachineExecution.HLevel3SszDecodeSteps
import BinaryFv.Zesu.MachineExecution.MemcpyProof
import BinaryFv.Zesu.Staging.ForkName
import BinaryFv.Zesu.Staging.MemReadInt

/-!
# Level 3 `ssz.decode` parent composition

This module connects parent-owned `ssz.decode` segments to their proved child contracts.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register

def sszDecodeCleanupMemcpyArgs (args : DecodeInlineArgs) : MemcpyArgs :=
  { returnAddress := 0x122b8
    destination := args.boundary.stackPointer - 0xbb0 + 0x330
    source := 0x1755c
    bytes := sszDecodeCleanupTemplateBytes }

/-- The first represented four-byte schema word at the `mem.readInt` child boundary. -/
def sszDecodeSchemaWordArgs (args : DecodeInlineArgs) (bound : 4 ≤ args.boundary.input.size)
    (fits : args.boundary.inputAddress + args.boundary.input.size ≤ 2 ^ 64) :
    MemReadIntArgs where
  address := args.boundary.inputAddress
  byte0 := args.boundary.input[0].toNat
  byte1 := args.boundary.input[1].toNat
  byte2 := args.boundary.input[2].toNat
  byte3 := args.boundary.input[3].toNat
  sourceFits := by omega

/-- The typed parent handoff satisfies the proved `mem.readInt` entry contract. -/
theorem memReadIntEntry_of_sszDecodeSchemaWord (args : DecodeInlineArgs) (template : EndpointState)
    (state : State) (entry : SszDecodeSchemaWordEntry args state) :
    memReadIntEntry
      (sszDecodeSchemaWordArgs args entry.inputAtLeastFour entry.input.1)
      { template with machine := state } := by
  have bound := entry.inputAtLeastFour
  refine ⟨entry.atPc, entry.sourceAt, ?_, ?_, ?_, ?_, ?_, ?_, entry.access.configured,
    entry.code⟩
  · simpa [sszDecodeSchemaWordArgs] using entry.input.uintRepAt 0 (by omega)
  · simpa [sszDecodeSchemaWordArgs] using entry.input.uintRepAt 1 (by omega)
  · simpa [sszDecodeSchemaWordArgs] using entry.input.uintRepAt 2 (by omega)
  · simpa [sszDecodeSchemaWordArgs] using entry.input.uintRepAt 3 (by omega)
  · intro offset offsetBound
    exact entry.access.inputLoad offset 1 (by omega)
  · intro offset offsetBound
    exact entry.access.inputNoMMIO offset 1 (by omega)

private theorem sszDecodeAllocatorOwnPc_in_initial {pc : BitVec 64}
    (inside : sszDecodeAllocatorPrefixOwnPc pc) : DecodeInlineInitialExecutionPc pc := by
  simp [sszDecodeAllocatorPrefixOwnPc, pcInList] at inside
  rcases inside with inside | inside | inside | inside | inside | inside
  all_goals
    unfold DecodeInlineInitialExecutionPc pcInRanges
    exact ⟨(0x121ac, 0x14ca8), by simp [Elflings.sszDecodeExecutionPcRanges], by omega,
      by omega⟩

private theorem sszDecodeAllocatorOwnPc_not_observed {pc : BitVec 64}
    (inside : sszDecodeAllocatorPrefixOwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  simp [sszDecodeAllocatorPrefixOwnPc, pcInList] at inside
  unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc
    at observed
  rcases observed with observed | observed | observed
  all_goals omega

private theorem memReadIntOwnPc_in_initial {pc : BitVec 64}
    (inside : memReadIntOwnPc pc) : DecodeInlineInitialExecutionPc pc := by
  simp [memReadIntOwnPc, pcInList] at inside
  rcases inside with inside | inside | inside | inside | inside | inside | inside | inside | inside |
    inside
  all_goals
    unfold DecodeInlineInitialExecutionPc pcInRanges
    exact ⟨(0x121ac, 0x14ca8), by simp [Elflings.sszDecodeExecutionPcRanges], by omega,
      by omega⟩

private theorem liftSszDecodeParentTrace (own exit : BitVec 64 → Prop)
    (ownInInitial : ∀ {pc}, own pc → DecodeInlineInitialExecutionPc pc)
    (ownNotObserved : ∀ {pc}, own pc → ¬BareMetalHostTransitionPc pc)
    (template : EndpointState) {fromStep count : Nat} {before after : State}
    (trace : ScopedTrace own exit (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc fromStep count
      { template with machine := before } { template with machine := after } := by
  induction trace with
  | exitAt fromStep state pc atPc exitPc => exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step (stepRelation := EndpointStep) (statePc := EndpointPc)
        fromStep count pc
        { template with machine := before } { template with machine := middle }
        { template with machine := after } atPc (ownInInitial inside) ?_ ?_
      · exact endpointStep_sail fromStep { template with machine := before } middle
          (fun observed observedPc => by
            change before.regs.get? PC = some observed at observedPc
            rw [atPc] at observedPc
            cases Option.some.inj observedPc
            exact ownNotObserved inside)
          machineStep
      · exact ih
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count callSite program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

private theorem liftSszDecodeAllocatorTrace (template : EndpointState)
    {fromStep count : Nat} {before after : State}
    (trace : ScopedTrace sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
      (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc fromStep count
      { template with machine := before } { template with machine := after } :=
  liftSszDecodeParentTrace sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
    sszDecodeAllocatorOwnPc_in_initial sszDecodeAllocatorOwnPc_not_observed template trace

private theorem instructionPreserved_disjoint_memReadIntWrites_for_sszDecode :
    RegSet.Disjoint instructionPreserved memReadIntWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem generalRegistersOfSeg {own exit : BitVec 64 → Prop}
    {W : RegSet} {M : Region} {kv : List RegVal} {a n : Nat} {base cur : State}
    {pc : BitVec 64}
    (present : GeneralRegistersPresent base)
    (seg : Seg own exit (fun _ _ _ _ _ => False) W M kv a n base cur pc)
    (covered : ∀ register, register ∈ architecturalIntegerRegisters → W register →
      ∃ value : RegisterType register, (⟨register, value⟩ : RegVal) ∈ kv) :
    GeneralRegistersPresent cur := by
  apply present.of_writesOnlyRegs seg.writes
  intro register member written
  obtain ⟨value, held⟩ := covered register member written
  exact ⟨value, seg.reg register value held⟩

/-- Typed facts retained when the first schema-word child returns to `ssz.decode`. -/
structure SszDecodeSchemaWordExit (args : DecodeInlineArgs) (readArgs : MemReadIntArgs)
    (state : EndpointState) : Prop where
  atPc : state.machine.regs.get? PC = some 0x121ec
  atStack : state.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0))
  inputSizeAt : state.machine.regs.get? x13 =
    some (BitVec.ofNat 64 args.boundary.input.size)
  sourceAt : state.machine.regs.get? x18 =
    some (BitVec.ofNat 64 args.boundary.inputAddress)
  resultAt : state.machine.regs.get? x8 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20))
  schemaAt : state.machine.regs.get? x14 = some (memReadIntResult readArgs)
  input : BytesRep state.machine.mem args.boundary.inputAddress args.boundary.input
  access : DecodeBoundaryMachineAccess args.boundary state.machine
  configured : ConfiguredMachinePre EndpointMachinePc state.machine
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem
  generalRegisters : GeneralRegistersPresent state.machine

set_option genInjectivity false in
/-- Facts retained at the accepted marker check after the validated length route. -/
structure SszDecodeMarkerReady (args : DecodeInlineArgs) (machine : State) : Prop where
  atPc : machine.regs.get? PC = some 0x1220c
  atStack : machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0))
  stackFits : 0xbb0 ≤ args.boundary.stackPointer
  stackAligned : args.boundary.stackPointer % 16 = 0
  stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64
  sourceAt : machine.regs.get? x18 =
    some (BitVec.ofNat 64 (args.boundary.inputAddress + 4))
  resultAt : machine.regs.get? x8 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20))
  inputAtLeastFour : 4 ≤ args.boundary.input.size
  input : BytesRep machine.mem args.boundary.inputAddress args.boundary.input
  access : DecodeBoundaryMachineAccess args.boundary machine
  configured : ConfiguredMachinePre EndpointMachinePc machine
  code : Artifacts.programImage.fileBytesLoadedFaithfully machine.mem
  generalRegisters : GeneralRegistersPresent machine

/-- The rejection routes retain the exact stack and machine facts needed by decoder cleanup. -/
structure SszDecodeCleanupReady (args : DecodeInlineArgs) (machine : State) : Prop where
  atPc : machine.regs.get? PC = some 0x1225c
  atStack : machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0))
  resultAt : machine.regs.get? x8 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20))
  stackFits : 0xbb0 ≤ args.boundary.stackPointer
  stackAligned : args.boundary.stackPointer % 16 = 0
  stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64
  access : DecodeBoundaryMachineAccess args.boundary machine
  configured : ConfiguredMachinePre EndpointMachinePc machine
  code : Artifacts.programImage.fileBytesLoadedFaithfully machine.mem
  generalRegisters : GeneralRegistersPresent machine

private theorem sszDecodeCleanupMemcpyWindowsDisjoint {args : DecodeInlineArgs} {state : State}
    (ready : SszDecodeCleanupReady args state) :
    let memcpyArgs := sszDecodeCleanupMemcpyArgs args
    memcpyArgs.destination + memcpyArgs.bytes.size ≤ memcpyArgs.source ∨
      memcpyArgs.source + memcpyArgs.bytes.size ≤ memcpyArgs.destination := by
  dsimp [sszDecodeCleanupMemcpyArgs]
  simp only [sszDecodeCleanupTemplateBytes, Array.size_ofFn]
  let destination := args.boundary.stackPointer - 0xbb0 + 0x330
  by_cases order : destination ≤ 0x1755c
  · left
    by_cases separated : destination + 256 ≤ 0x1755c
    · exact separated
    · exfalso
      have sourceInside : destination ≤ 0x1755c ∧ 0x1755c < destination + 256 := by omega
      have sourceInFrame : args.boundary.stackPointer - 0xbb0 ≤ 0x1755c ∧
          0x1755c < args.boundary.stackPointer := by
        dsimp [destination] at sourceInside
        omega
      have noCode := ready.access.frameNotCode 0x1755c sourceInFrame.1 sourceInFrame.2
      have backed := sszDecodeCleanupTemplateBacked ⟨0, by omega⟩
      simp [noCode] at backed
  · right
    have sourceBefore : 0x1755c ≤ destination := by omega
    by_cases separated : 0x1755c + 256 ≤ destination
    · exact separated
    · exfalso
      have destinationInside : destination < 0x1755c + 256 := by omega
      let index : Fin 256 := ⟨destination - 0x1755c, by omega⟩
      have atDestination : 0x1755c + index.val = destination := by
        dsimp [index]
        omega
      have destinationInFrame : args.boundary.stackPointer - 0xbb0 ≤ destination ∧
          destination < args.boundary.stackPointer := by
        dsimp [destination]
        omega
      have noCode := ready.access.frameNotCode destination destinationInFrame.1
        destinationInFrame.2
      have backed := sszDecodeCleanupTemplateBacked index
      rw [atDestination, noCode] at backed
      simp at backed

/-- The first two cleanup stores retain one opaque `Seg` and reach the address-setup instruction. -/
theorem sszDecodeCleanupFirstStoresFromReady (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (ready : SszDecodeCleanupReady args before) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [] fromStep 2 before after 0x12264 :=
  sszDecodeCleanupFirstStores fromStep args before ready.atPc ready.atStack ready.stackFits
    ready.stackAligned ready.stackUpper ready.access ready.configured ready.code

/-- The cleanup handoff reaches `0x12268` and retains the computed template page in `x10`. -/
theorem sszDecodeCleanupBaseHighFromReady (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (ready : SszDecodeCleanupReady args before) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x10, 0x17264⟩] fromStep 3 before after 0x12268 :=
  sszDecodeCleanupBaseHighAfterFirstStores fromStep args before ready.atPc ready.atStack
    ready.stackFits ready.stackAligned ready.stackUpper ready.access ready.configured ready.code

/-- The cleanup handoff reaches the exact `memcpy` call with all four argument registers bound. -/
theorem sszDecodeCleanupMemcpyCallReadyFromReady (fromStep : Nat) (args : DecodeInlineArgs)
    (before : State) (ready : SszDecodeCleanupReady args before) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x1, 0x102b0⟩, ⟨x12, 256⟩,
          ⟨x10, BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330)⟩,
          ⟨x11, 0x1755c⟩]
        fromStep 22 before after 0x122b4 :=
  sszDecodeCleanupMemcpyCallReady fromStep args before ready.atPc ready.atStack
    ready.stackFits ready.stackAligned ready.stackUpper ready.access ready.configured ready.code

/-- The cleanup handoff reaches `memcpy` and retains the nine later load sources. -/
theorem sszDecodeCleanupMemcpyCallReadyFromReadyWithZeroSlots (fromStep : Nat)
    (args : DecodeInlineArgs) (before : State) (ready : SszDecodeCleanupReady args before) :
    ∃ after,
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x1, 0x102b0⟩, ⟨x12, 256⟩,
          ⟨x10, BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330)⟩,
          ⟨x11, 0x1755c⟩]
        fromStep 22 before after 0x122b4 ∧
      SszDecodeCleanupZeroSlots args after :=
  sszDecodeCleanupMemcpyCallReadyWithZeroSlots fromStep args before ready.atPc ready.atStack
    ready.stackFits ready.stackAligned ready.stackUpper ready.access ready.configured ready.code

/-- The exact call step constructs the existing proved `memcpy` entry without a new contract. -/
theorem sszDecodeCleanupMemcpyEntry (fromStep : Nat) (args : DecodeInlineArgs)
    (template : EndpointState) (before : State) (ready : SszDecodeCleanupReady args before) :
    ∃ (callReady : State) (callState : EndpointState),
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x1, 0x102b0⟩, ⟨x12, 256⟩,
          ⟨x10, BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330)⟩,
          ⟨x11, 0x1755c⟩]
        fromStep 22 before callReady 0x122b4 ∧
      Runs (try_step (fromStep + 22) false) callReady callState.machine false ∧
      callState.machine.regs.get? x2 =
        some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)) ∧
      callState.machine.regs.get? x8 =
        some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)) ∧
      Agree instructionPreserved before callState.machine ∧
      callState.machine.regs.get? pma_regions = before.regs.get? pma_regions ∧
      callState = { template with machine := callState.machine } ∧
      GeneralRegistersPresent callState.machine ∧
      SszDecodeCleanupZeroSlots args callState.machine ∧
      MemcpyEntry (sszDecodeCleanupMemcpyArgs args) callState := by
  obtain ⟨callReady, seg, readySlots⟩ :=
    sszDecodeCleanupMemcpyCallReadyFromReadyWithZeroSlots fromStep args before ready
  obtain ⟨retired, callRun⟩ := sszDecodeCleanupMemcpyCallRun seg ready.stackFits
    ready.access ready.code
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement callReady) 0x122b4 0x101d4 x1 0x122b8)
    0x101d4 retired
  let callState : EndpointState := { template with machine := callMachine }
  have callWrites : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x1))
      callReady callMachine := by
    simpa [callMachine, callLinkState] using
      callRetirement_writes callReady 0x122b4 0x101d4 retired x1 0x122b8
  have parentPmaEq := seg.writes.get pma_regions (by
    simp [sszDecodeCleanupWrites, stepBookkeeping])
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have pmaEq : callMachine.regs.get? pma_regions = before.regs.get? pma_regions :=
    callPmaEq.trans parentPmaEq
  have sourceBefore := sszDecodeCleanupTemplateRep before ready.code
  have sourceAtReady : BytesRep callReady.mem 0x1755c sszDecodeCleanupTemplateBytes :=
    sourceBefore.of_writesOnlyWithin seg.mem (by
      intro index indexBound inside
      unfold sszDecodeCleanupMemory byteRange at inside
      have inFrame : args.boundary.stackPointer - 0xbb0 ≤ 0x1755c + index ∧
          0x1755c + index < args.boundary.stackPointer := by omega
      have noCode := ready.access.frameNotCode (0x1755c + index) inFrame.1 inFrame.2
      let fin : Fin 256 := ⟨index, by simpa [sszDecodeCleanupTemplateBytes] using indexBound⟩
      have backed := sszDecodeCleanupTemplateBacked fin
      dsimp [fin] at backed
      rw [noCode] at backed
      simp at backed)
  have sourceAtCall : BytesRep callMachine.mem 0x1755c sszDecodeCleanupTemplateBytes := by
    simpa [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      sourceAtReady
  have callCode : Artifacts.programImage.fileBytesLoadedFaithfully callMachine.mem := by
    simpa [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      sszDecodeCleanupCodeOfSeg ready.stackFits ready.access ready.code seg
  have callSlots : SszDecodeCleanupZeroSlots args callMachine :=
    readySlots.of_mem_eq (by
      simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        callLinkState, controlFlowJumpState_mem, tryStepControlFlowAfterIncrement_mem])
  have stackFits := ready.stackFits
  have stackUpper := ready.stackUpper
  have windowsDisjoint := sszDecodeCleanupMemcpyWindowsDisjoint ready
  have entry : MemcpyEntry (sszDecodeCleanupMemcpyArgs args) callState := by
    unfold MemcpyEntry
    constructor
    · change 0x122b8 ∈ Elflings.memcpyExitPcs
      native_decide
    constructor
    · simp [sszDecodeCleanupMemcpyArgs, sszDecodeCleanupTemplateBytes]
    constructor
    · simpa only [sszDecodeCleanupMemcpyArgs, sszDecodeCleanupTemplateBytes, Array.size_ofFn]
        using (show args.boundary.stackPointer - 0xbb0 + 0x330 + 256 ≤ 2 ^ 64 by omega)
    constructor
    · simpa only [sszDecodeCleanupMemcpyArgs, sszDecodeCleanupTemplateBytes, Array.size_ofFn]
        using (show 0x1755c + 256 ≤ 2 ^ 64 by omega)
    constructor
    · exact windowsDisjoint
    constructor
    · simp [callState, callMachine, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, callLinkState, Std.ExtDHashMap.get?_insert]
      native_decide
    constructor
    · simp [sszDecodeCleanupMemcpyArgs, callState, callMachine,
        tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, callLinkState,
        Std.ExtDHashMap.get?_insert]
    constructor
    · exact (callWrites.get x10 (by decide)).trans
        (seg.reg x10 (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330)) (by simp))
    constructor
    · exact (callWrites.get x11 (by decide)).trans (seg.reg x11 0x1755c (by simp))
    constructor
    · simp only [sszDecodeCleanupMemcpyArgs, sszDecodeCleanupTemplateBytes, Array.size_ofFn]
      exact (callWrites.get x12 (by decide)).trans (seg.reg x12 256 (by simp))
    constructor
    · simpa only [sszDecodeCleanupMemcpyArgs, callState] using sourceAtCall
    constructor
    · simpa only [callState] using callCode
    · refine
        { configured := configuredAfterSszDecodeCleanupCall callReady retired
            (sszDecodeCleanupAccessOfSeg ready.access seg).configured
          sourcePma := ?_
          destinationPma := ?_
          sourceNotMMIO := ?_
          destinationNotMMIO := ?_
          destinationNotCode := ?_ }
      · intro index indexBound
        simp only [sszDecodeCleanupMemcpyArgs, sszDecodeCleanupTemplateBytes, Array.size_ofFn]
          at indexBound ⊢
        exact dataPmaAllows_of_pma_regions_eq pmaEq
          (ready.access.cleanupTemplateLoad index 1 (by omega))
      · intro index indexBound
        simp only [sszDecodeCleanupMemcpyArgs, sszDecodeCleanupTemplateBytes, Array.size_ofFn]
          at indexBound ⊢
        simpa [sszDecodeCleanupMemcpyArgs, Nat.add_assoc] using
          dataPmaAllows_of_pma_regions_eq pmaEq
            (ready.access.frameStore (0x330 + index) 1 (by omega))
      · intro index indexBound
        simp only [sszDecodeCleanupMemcpyArgs, sszDecodeCleanupTemplateBytes, Array.size_ofFn]
          at indexBound ⊢
        simpa [sszDecodeCleanupMemcpyArgs, Nat.add_assoc] using
          ready.access.cleanupTemplateNoMMIO index 1 (by omega)
      · intro index indexBound
        simp only [sszDecodeCleanupMemcpyArgs, sszDecodeCleanupTemplateBytes, Array.size_ofFn]
          at indexBound ⊢
        simpa [sszDecodeCleanupMemcpyArgs, Nat.add_assoc] using
          ready.access.frameNoMMIO (0x330 + index) 1 (by omega)
      · intro index indexBound
        simp only [sszDecodeCleanupMemcpyArgs, sszDecodeCleanupTemplateBytes, Array.size_ofFn]
          at indexBound ⊢
        exact ready.access.frameNotCode _ (by omega) (by omega)
  have callStack : callState.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)) := by
    exact (callWrites.get x2 (by decide)).trans
      ((seg.get x2 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans ready.atStack)
  have callResult : callState.machine.regs.get? x8 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)) := by
    exact (callWrites.get x8 (by decide)).trans
      ((seg.get x8 (by simp [sszDecodeCleanupWrites, stepBookkeeping])).trans ready.resultAt)
  have callAgree : Agree instructionPreserved before callState.machine := by
    have parentAgree := seg.agree instructionPreserved_disjoint_sszDecodeCleanupWrites
    have stepAgree := callWrites.agree (by
      intro register (preserved : instructionPreserved register) written
      rcases written with bookkeeping | rfl
      · exact platformPreserved_disjoint register preserved.1 bookkeeping
      · exact preserved.2 rfl)
    simpa only [callState] using parentAgree.trans stepAgree
  have callReadyGeneral := generalRegistersOfSeg ready.generalRegisters seg (by
    intro register member written
    rcases written with bookkeeping | rfl | rfl | rfl | rfl
    · simp only [stepBookkeeping] at bookkeeping
      rcases bookkeeping with rfl | rfl | rfl | rfl <;>
        simp [architecturalIntegerRegisters] at member
    all_goals simp)
  have callGeneral : GeneralRegistersPresent callState.machine := by
    refine callReadyGeneral.of_one_general_write (destination := x1)
      (value := (0x122b8 : BitVec 64)) callWrites ?_ ?_
    · intro register member written
      rcases written with bookkeeping | rfl
      · simp only [stepBookkeeping] at bookkeeping
        rcases bookkeeping with rfl | rfl | rfl | rfl <;>
          simp [architecturalIntegerRegisters] at member
      · rfl
    · simp [callState, callMachine, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, callLinkState, Std.ExtDHashMap.get?_insert]
  exact ⟨callReady, callState, seg, by simpa [callState, callMachine] using callRun,
    callStack, callResult, callAgree, by simpa [callState] using pmaEq, by simp [callState],
    callGeneral, callSlots, entry⟩

/-- Apply the unconditional `memcpy` contract at the cleanup call boundary. -/
theorem sszDecodeCleanupMemcpyChild (fromStep : Nat) (args : DecodeInlineArgs)
    (template : EndpointState) (before : State) (ready : SszDecodeCleanupReady args before) :
    ∃ (callReady : State) (callState : EndpointState) (used : Nat) (after : EndpointState),
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x1, 0x102b0⟩, ⟨x12, 256⟩,
          ⟨x10, BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330)⟩,
          ⟨x11, 0x1755c⟩]
        fromStep 22 before callReady 0x122b4 ∧
      Runs (try_step (fromStep + 22) false) callReady callState.machine false ∧
      callState.machine.regs.get? x2 =
        some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)) ∧
      callState.machine.regs.get? x8 =
        some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)) ∧
      Agree instructionPreserved before callState.machine ∧
      callState.machine.regs.get? pma_regions = before.regs.get? pma_regions ∧
      callState = { template with machine := callState.machine } ∧
      GeneralRegistersPresent callState.machine ∧
      SszDecodeCleanupZeroSlots args callState.machine ∧
      MemcpyEntry (sszDecodeCleanupMemcpyArgs args) callState ∧
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.memcpyExecutionPcRanges)
        (fromStep + 23) used callState after ∧
      MemcpyExit (sszDecodeCleanupMemcpyArgs args) () callState after := by
  obtain ⟨callReady, callState, seg, callRun, callStack, callResult, callAgree, callPma,
    callStateEq, callGeneral, callSlots, entry⟩ :=
    sszDecodeCleanupMemcpyEntry fromStep args template before ready
  obtain ⟨used, after, _outcome, _positive, _bounded, childTrace, _childExitPc, _allowed,
    childExit⟩ := MemcpyInstanceContract.implements memcpyInstanceContract
      (sszDecodeCleanupMemcpyArgs args) (fromStep + 23) callState entry
  exact ⟨callReady, callState, used, after, seg, callRun, callStack, callResult, callAgree, callPma,
    callStateEq, callGeneral, callSlots, entry, childTrace, childExit⟩

private theorem instructionPreserved_abiCalleePreserved_cleanup (register : Register)
    (preserved : instructionPreserved register) : abiCalleePreserved register := by
  rcases preserved.1 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact (preserved.2 rfl).elim
  all_goals simp [abiCalleePreserved]

/-- Machine facts restored by the proved `memcpy` return to `0x122b8`. -/
structure SszDecodeCleanupResume (args : DecodeInlineArgs) (machine : State) : Prop where
  atPc : machine.regs.get? PC = some 0x122b8
  atStack : machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0))
  resultAt : machine.regs.get? x8 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20))
  stackFits : 0xbb0 ≤ args.boundary.stackPointer
  stackAligned : args.boundary.stackPointer % 16 = 0
  stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64
  access : DecodeBoundaryMachineAccess args.boundary machine
  code : Artifacts.programImage.fileBytesLoadedFaithfully machine.mem
  generalRegisters : GeneralRegistersPresent machine
  zeroSlots : SszDecodeCleanupZeroSlots args machine

/-- Facts required by the result stores after the complete rejection cleanup. -/
structure SszDecodeResultStoresReady (args : DecodeInlineArgs) (machine : State) : Prop where
  atPc : machine.regs.get? PC = some 0x1230c
  atStack : machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0))
  resultAt : machine.regs.get? x8 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20))
  statusAt : machine.regs.get? x22 = some 1
  stackFits : 0xbb0 ≤ args.boundary.stackPointer
  stackAligned : args.boundary.stackPointer % 16 = 0
  stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64
  access : DecodeBoundaryMachineAccess args.boundary machine
  configured : ConfiguredMachinePre EndpointMachinePc machine
  code : Artifacts.programImage.fileBytesLoadedFaithfully machine.mem
  generalRegisters : GeneralRegistersPresent machine
  zeroSlots : SszDecodeCleanupZeroSlots args machine

/-- The eleven live registers consumed by the twelve result stores at `0x1230c..0x12338`. -/
structure SszDecodeResultStoreSources (machine : State) : Prop where
  ra : ∃ value, machine.regs.get? x1 = some value
  t0 : ∃ value, machine.regs.get? x5 = some value
  s1 : ∃ value, machine.regs.get? x9 = some value
  a5 : ∃ value, machine.regs.get? x15 = some value
  a6 : ∃ value, machine.regs.get? x16 = some value
  a7 : ∃ value, machine.regs.get? x17 = some value
  s3 : ∃ value, machine.regs.get? x19 = some value
  s4 : ∃ value, machine.regs.get? x20 = some value
  s7 : ∃ value, machine.regs.get? x23 = some value
  s10 : ∃ value, machine.regs.get? x26 = some value
  t6 : ∃ value, machine.regs.get? x31 = some value

/-- Project only the register values required by the result-store family. -/
theorem SszDecodeResultStoresReady.sources {args : DecodeInlineArgs} {machine : State}
    (ready : SszDecodeResultStoresReady args machine) :
    SszDecodeResultStoreSources machine := by
  constructor <;>
    apply ready.generalRegisters.read <;>
    simp [architecturalIntegerRegisters]

/-- The twelve result stores reach the first post-store instruction without exposing successors. -/
structure SszDecodeResultStoresHandoff (fromStep : Nat) (args : DecodeInlineArgs)
    (before after : State) : Prop where
  seg : Seg sszDecodeResultStoresOwnPc sszDecodeResultStoresExitPc
    (fun _ _ _ _ _ => False) stepBookkeeping (sszDecodeResultStoresMemory args)
    [] fromStep 12 before after 0x1233c
  access : DecodeBoundaryMachineAccess args.boundary after
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  zeroSlots : SszDecodeCleanupZeroSlots args after
  generalRegisters : GeneralRegistersPresent after

/-- Compose all twelve result stores through one shared store family and `Seg`. -/
theorem sszDecodeResultStores (fromStep : Nat) (args : DecodeInlineArgs) (before : State)
    (ready : SszDecodeResultStoresReady args before) :
    ∃ after, SszDecodeResultStoresHandoff fromStep args before after := by
  rcases ready.sources with ⟨⟨ra, raAt⟩, ⟨t0, t0At⟩, ⟨s1, s1At⟩, ⟨a5, a5At⟩,
    ⟨a6, a6At⟩, ⟨a7, a7At⟩, ⟨s3, s3At⟩, ⟨s4, s4At⟩, ⟨s7, s7At⟩,
    ⟨s10, s10At⟩, ⟨t6, t6At⟩⟩
  have seg0 := Seg.nil sszDecodeResultStoresOwnPc sszDecodeResultStoresExitPc
    (fun _ _ _ _ _ => False) stepBookkeeping (sszDecodeResultStoresMemory args)
    fromStep ready.configured.retiredCounter ready.atPc
  obtain ⟨machine1, seg1⟩ := sszDecodeResultStoresAppend seg0 0 s1 0x12310 (by omega)
    (by simp [sszDecodeResultStoresOwnPc])
    (sszDecodeResultStoreS1 fromStep args before s1 ready.access seg0.atPc
      ((seg0.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
      ((seg0.get x9 (by simp [stepBookkeeping])).trans s1At)
      ready.stackAligned ready.stackUpper ready.code) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := sszDecodeResultStoresAccessOfSeg ready.access seg1
  have code1 := sszDecodeResultStoresCodeOfSeg ready.access ready.code seg1
  obtain ⟨machine2, seg2⟩ := sszDecodeResultStoresAppend seg1 8 s10 0x12314 (by omega)
    (by simp [sszDecodeResultStoresOwnPc])
    (sszDecodeResultStoreS10 (fromStep + 1) args machine1 s10 access1 seg1.atPc
      ((seg1.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
      ((seg1.get x26 (by simp [stepBookkeeping])).trans s10At)
      ready.stackAligned ready.stackUpper code1) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := sszDecodeResultStoresAccessOfSeg ready.access seg2
  have code2 := sszDecodeResultStoresCodeOfSeg ready.access ready.code seg2
  obtain ⟨machine3, seg3⟩ := sszDecodeResultStoresAppend seg2 0x10 s4 0x12318 (by omega)
    (by simp [sszDecodeResultStoresOwnPc])
    (sszDecodeResultStoreS4 (fromStep + 2) args machine2 s4 access2 seg2.atPc
      ((seg2.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
      ((seg2.get x20 (by simp [stepBookkeeping])).trans s4At)
      ready.stackAligned ready.stackUpper code2) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access3 := sszDecodeResultStoresAccessOfSeg ready.access seg3
  have code3 := sszDecodeResultStoresCodeOfSeg ready.access ready.code seg3
  obtain ⟨machine4, seg4⟩ := sszDecodeResultStoresAppend seg3 0x18 s3 0x1231c (by omega)
    (by simp [sszDecodeResultStoresOwnPc])
    (sszDecodeResultStoreS3 (fromStep + 3) args machine3 s3 access3 seg3.atPc
      ((seg3.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
      ((seg3.get x19 (by simp [stepBookkeeping])).trans s3At)
      ready.stackAligned ready.stackUpper code3) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access4 := sszDecodeResultStoresAccessOfSeg ready.access seg4
  have code4 := sszDecodeResultStoresCodeOfSeg ready.access ready.code seg4
  obtain ⟨machine5, seg5⟩ := sszDecodeResultStoresAppend seg4 0x20 a7 0x12320 (by omega)
    (by simp [sszDecodeResultStoresOwnPc])
    (sszDecodeResultStoreA7 (fromStep + 4) args machine4 a7 access4 seg4.atPc
      ((seg4.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
      ((seg4.get x17 (by simp [stepBookkeeping])).trans a7At)
      ready.stackAligned ready.stackUpper code4) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access5 := sszDecodeResultStoresAccessOfSeg ready.access seg5
  have code5 := sszDecodeResultStoresCodeOfSeg ready.access ready.code seg5
  obtain ⟨machine6, seg6⟩ := sszDecodeResultStoresAppend seg5 0x28 a6 0x12324 (by omega)
    (by simp [sszDecodeResultStoresOwnPc])
    (sszDecodeResultStoreA6 (fromStep + 5) args machine5 a6 access5 seg5.atPc
      ((seg5.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
      ((seg5.get x16 (by simp [stepBookkeeping])).trans a6At)
      ready.stackAligned ready.stackUpper code5) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access6 := sszDecodeResultStoresAccessOfSeg ready.access seg6
  have code6 := sszDecodeResultStoresCodeOfSeg ready.access ready.code seg6
  obtain ⟨machine7, seg7⟩ := sszDecodeResultStoresAppend seg6 0x30 t6 0x12328 (by omega)
    (by simp [sszDecodeResultStoresOwnPc])
    (sszDecodeResultStoreT6 (fromStep + 6) args machine6 t6 access6 seg6.atPc
      ((seg6.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
      ((seg6.get x31 (by simp [stepBookkeeping])).trans t6At)
      ready.stackAligned ready.stackUpper code6) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access7 := sszDecodeResultStoresAccessOfSeg ready.access seg7
  have code7 := sszDecodeResultStoresCodeOfSeg ready.access ready.code seg7
  obtain ⟨machine8, seg8⟩ := sszDecodeResultStoresAppend seg7 0x38 t0 0x1232c (by omega)
    (by simp [sszDecodeResultStoresOwnPc])
    (sszDecodeResultStoreT0 (fromStep + 7) args machine7 t0 access7 seg7.atPc
      ((seg7.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
      ((seg7.get x5 (by simp [stepBookkeeping])).trans t0At)
      ready.stackAligned ready.stackUpper code7) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access8 := sszDecodeResultStoresAccessOfSeg ready.access seg8
  have code8 := sszDecodeResultStoresCodeOfSeg ready.access ready.code seg8
  obtain ⟨machine9, seg9⟩ := sszDecodeResultStoresAppend seg8 0x40 s7 0x12330 (by omega)
    (by simp [sszDecodeResultStoresOwnPc])
    (sszDecodeResultStoreS7First (fromStep + 8) args machine8 s7 access8 seg8.atPc
      ((seg8.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
      ((seg8.get x23 (by simp [stepBookkeeping])).trans s7At)
      ready.stackAligned ready.stackUpper code8) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access9 := sszDecodeResultStoresAccessOfSeg ready.access seg9
  have code9 := sszDecodeResultStoresCodeOfSeg ready.access ready.code seg9
  obtain ⟨machine10, seg10⟩ := sszDecodeResultStoresAppend seg9 0x48 a5 0x12334 (by omega)
    (by simp [sszDecodeResultStoresOwnPc])
    (sszDecodeResultStoreA5 (fromStep + 9) args machine9 a5 access9 seg9.atPc
      ((seg9.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
      ((seg9.get x15 (by simp [stepBookkeeping])).trans a5At)
      ready.stackAligned ready.stackUpper code9) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access10 := sszDecodeResultStoresAccessOfSeg ready.access seg10
  have code10 := sszDecodeResultStoresCodeOfSeg ready.access ready.code seg10
  obtain ⟨machine11, seg11⟩ := sszDecodeResultStoresAppend seg10 0x50 s7 0x12338 (by omega)
    (by simp [sszDecodeResultStoresOwnPc])
    (sszDecodeResultStoreS7Second (fromStep + 10) args machine10 s7 access10 seg10.atPc
      ((seg10.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
      ((seg10.get x23 (by simp [stepBookkeeping])).trans s7At)
      ready.stackAligned ready.stackUpper code10) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access11 := sszDecodeResultStoresAccessOfSeg ready.access seg11
  have code11 := sszDecodeResultStoresCodeOfSeg ready.access ready.code seg11
  obtain ⟨machine12, seg12⟩ := sszDecodeResultStoresAppend seg11 0x58 ra 0x1233c (by omega)
    (by simp [sszDecodeResultStoresOwnPc])
    (sszDecodeResultStoreRa (fromStep + 11) args machine11 ra access11 seg11.atPc
      ((seg11.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
      ((seg11.get x1 (by simp [stepBookkeeping])).trans raAt)
      ready.stackAligned ready.stackUpper code11) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have stackFits := ready.stackFits
  have zeroSlots := ready.zeroSlots.of_writesOnlyWithin seg12.mem (by
    intro address width member
    unfold sszDecodeResultStoresMemory byteRange
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h <;> cases h <;>
      intro index indexBound inside <;> omega)
  exact ⟨machine12, seg12, sszDecodeResultStoresAccessOfSeg ready.access seg12,
    sszDecodeResultStoresCodeOfSeg ready.access ready.code seg12, zeroSlots,
    generalRegistersOfSeg ready.generalRegisters seg12 (by
      intro register member bookkeeping
      simp only [stepBookkeeping] at bookkeeping
      rcases bookkeeping with rfl | rfl | rfl | rfl <;>
        simp [architecturalIntegerRegisters] at member)⟩

def sszDecodeCleanupLoadsOwnPc (pc : BitVec 64) : Prop :=
  0x1233c ≤ pc.toNat ∧ pc.toNat < 0x12360

def sszDecodeCleanupLoadsExitPc (pc : BitVec 64) : Prop := pc = 0x12360

def sszDecodeCleanupLoadsWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x5 ∨ register = x10 ∨ register = x11 ∨
    register = x12 ∨ register = x13 ∨ register = x14 ∨ register = x15 ∨
    register = x16 ∨ register = x17

private theorem instructionPreserved_disjoint_sszDecodeCleanupLoadsWrites :
    RegSet.Disjoint instructionPreserved sszDecodeCleanupLoadsWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem sszDecodeCleanupLoadsAppend {before cur : State} {kv a n pc}
    (seg : Seg sszDecodeCleanupLoadsOwnPc sszDecodeCleanupLoadsExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupLoadsWrites noMemory
      kv a n before cur pc)
    (destination : Register) (value : RegisterType destination) (nextPc : BitVec 64)
    (inside : sszDecodeCleanupLoadsOwnPc pc)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (afterRegisterWrite cur pc retired destination value) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (written : sszDecodeCleanupLoadsWrites destination)
    (destinationNotPc : destination ≠ PC) (destinationNotRetired : destination ≠ minstret)
    (keep : RegsOutside (RegSet.union stepBookkeeping (RegSet.only destination)) kv) :
    ∃ next, Seg sszDecodeCleanupLoadsOwnPc sszDecodeCleanupLoadsExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupLoadsWrites noMemory
      (⟨destination, value⟩ :: kv) a (n + 1) before next nextPc := by
  obtain ⟨retired, run⟩ := run
  exact ⟨_, seg.stepKnown inside (by
      intro atExit
      unfold sszDecodeCleanupLoadsExitPc at atExit
      subst pc
      simp [sszDecodeCleanupLoadsOwnPc] at inside)
    destination value nextPc retired run advance
    (by intro register bookkeeping; exact Or.inl bookkeeping) written
    destinationNotPc destinationNotRetired keep⟩

private theorem sszDecodeCleanupLoadsAccessOfSeg {args : DecodeInlineArgs} {before cur : State}
    {kv a n pc} (access : DecodeBoundaryMachineAccess args.boundary before)
    (seg : Seg sszDecodeCleanupLoadsOwnPc sszDecodeCleanupLoadsExitPc
      (fun _ _ _ _ _ => False) sszDecodeCleanupLoadsWrites noMemory
      kv a n before cur pc) :
    DecodeBoundaryMachineAccess args.boundary cur :=
  access.of_pma_regions_eq
    (seg.agree instructionPreserved_disjoint_sszDecodeCleanupLoadsWrites) seg.retired
    (seg.get pma_regions (by simp [sszDecodeCleanupLoadsWrites, stepBookkeeping]))

/-- The nine cleanup loads reach the next result-construction store with all loaded values zero. -/
structure SszDecodeCleanupLoadsHandoff (fromStep : Nat) (args : DecodeInlineArgs)
    (before after : State) : Prop where
  seg : Seg sszDecodeCleanupLoadsOwnPc sszDecodeCleanupLoadsExitPc
    (fun _ _ _ _ _ => False) sszDecodeCleanupLoadsWrites noMemory
    [⟨x5, 0⟩, ⟨x17, 0⟩, ⟨x16, 0⟩, ⟨x15, 0⟩, ⟨x14, 0⟩,
      ⟨x13, 0⟩, ⟨x12, 0⟩, ⟨x11, 0⟩, ⟨x10, 0⟩]
    fromStep 9 before after 0x12360
  access : DecodeBoundaryMachineAccess args.boundary after
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  generalRegisters : GeneralRegistersPresent after

/-- Compose all nine cleanup-slot loads through one `Seg`. -/
theorem sszDecodeCleanupLoads (fromStep : Nat) (args : DecodeInlineArgs)
    (source storeAfter : State) (ready : SszDecodeResultStoresReady args source)
    (stores : SszDecodeResultStoresHandoff fromStep args source storeAfter) :
    ∃ after, SszDecodeCleanupLoadsHandoff (fromStep + 12) args storeAfter after := by
  have stackAt : storeAfter.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)) :=
    (stores.seg.get x2 (by simp [stepBookkeeping])).trans ready.atStack
  have seg0 := Seg.nil sszDecodeCleanupLoadsOwnPc sszDecodeCleanupLoadsExitPc
    (fun _ _ _ _ _ => False) sszDecodeCleanupLoadsWrites noMemory
    (fromStep + 12) stores.access.configured.retiredCounter stores.seg.atPc
  have run0 := sszDecodeCleanupLoadA0 (fromStep + 12) args storeAfter seg0.atPc stackAt
    stores.zeroSlots.slot4a8 ready.stackFits ready.stackAligned ready.stackUpper stores.access
    stores.code
  obtain ⟨state1, seg1⟩ := sszDecodeCleanupLoadsAppend seg0 x10 0 0x12340
    (by simp [sszDecodeCleanupLoadsOwnPc]) run0 (by native_decide)
    (by simp [sszDecodeCleanupLoadsWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := sszDecodeCleanupLoadsAccessOfSeg stores.access seg1
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully state1.mem := by
    rw [seg1.memEq noMemory_empty]
    exact stores.code
  have slots1 := stores.zeroSlots.of_mem_eq (seg1.memEq noMemory_empty)
  have run1 := sszDecodeCleanupLoadA1 (fromStep + 13) args state1 seg1.atPc
    ((seg1.get x2 (by simp [sszDecodeCleanupLoadsWrites, stepBookkeeping])).trans stackAt)
    slots1.slot4b0 ready.stackFits ready.stackAligned ready.stackUpper access1 code1
  obtain ⟨state2, seg2⟩ := sszDecodeCleanupLoadsAppend seg1 x11 0 0x12344
    (by simp [sszDecodeCleanupLoadsOwnPc]) run1 (by native_decide)
    (by simp [sszDecodeCleanupLoadsWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := sszDecodeCleanupLoadsAccessOfSeg stores.access seg2
  have code2 : Artifacts.programImage.fileBytesLoadedFaithfully state2.mem := by
    rw [seg2.memEq noMemory_empty]
    exact stores.code
  have slots2 := stores.zeroSlots.of_mem_eq (seg2.memEq noMemory_empty)
  have run2 := sszDecodeCleanupLoadA2 (fromStep + 14) args state2 seg2.atPc
    ((seg2.get x2 (by simp [sszDecodeCleanupLoadsWrites, stepBookkeeping])).trans stackAt)
    slots2.slot488 ready.stackFits ready.stackAligned ready.stackUpper access2 code2
  obtain ⟨state3, seg3⟩ := sszDecodeCleanupLoadsAppend seg2 x12 0 0x12348
    (by simp [sszDecodeCleanupLoadsOwnPc]) run2 (by native_decide)
    (by simp [sszDecodeCleanupLoadsWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access3 := sszDecodeCleanupLoadsAccessOfSeg stores.access seg3
  have code3 : Artifacts.programImage.fileBytesLoadedFaithfully state3.mem := by
    rw [seg3.memEq noMemory_empty]
    exact stores.code
  have slots3 := stores.zeroSlots.of_mem_eq (seg3.memEq noMemory_empty)
  have run3 := sszDecodeCleanupLoadA3 (fromStep + 15) args state3 seg3.atPc
    ((seg3.get x2 (by simp [sszDecodeCleanupLoadsWrites, stepBookkeeping])).trans stackAt)
    slots3.slot490 ready.stackFits ready.stackAligned ready.stackUpper access3 code3
  obtain ⟨state4, seg4⟩ := sszDecodeCleanupLoadsAppend seg3 x13 0 0x1234c
    (by simp [sszDecodeCleanupLoadsOwnPc]) run3 (by native_decide)
    (by simp [sszDecodeCleanupLoadsWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access4 := sszDecodeCleanupLoadsAccessOfSeg stores.access seg4
  have code4 : Artifacts.programImage.fileBytesLoadedFaithfully state4.mem := by
    rw [seg4.memEq noMemory_empty]
    exact stores.code
  have slots4 := stores.zeroSlots.of_mem_eq (seg4.memEq noMemory_empty)
  have run4 := sszDecodeCleanupLoadA4 (fromStep + 16) args state4 seg4.atPc
    ((seg4.get x2 (by simp [sszDecodeCleanupLoadsWrites, stepBookkeeping])).trans stackAt)
    slots4.slot498 ready.stackFits ready.stackAligned ready.stackUpper access4 code4
  obtain ⟨state5, seg5⟩ := sszDecodeCleanupLoadsAppend seg4 x14 0 0x12350
    (by simp [sszDecodeCleanupLoadsOwnPc]) run4 (by native_decide)
    (by simp [sszDecodeCleanupLoadsWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access5 := sszDecodeCleanupLoadsAccessOfSeg stores.access seg5
  have code5 : Artifacts.programImage.fileBytesLoadedFaithfully state5.mem := by
    rw [seg5.memEq noMemory_empty]
    exact stores.code
  have slots5 := stores.zeroSlots.of_mem_eq (seg5.memEq noMemory_empty)
  have run5 := sszDecodeCleanupLoadA5 (fromStep + 17) args state5 seg5.atPc
    ((seg5.get x2 (by simp [sszDecodeCleanupLoadsWrites, stepBookkeeping])).trans stackAt)
    slots5.slot4a0 ready.stackFits ready.stackAligned ready.stackUpper access5 code5
  obtain ⟨state6, seg6⟩ := sszDecodeCleanupLoadsAppend seg5 x15 0 0x12354
    (by simp [sszDecodeCleanupLoadsOwnPc]) run5 (by native_decide)
    (by simp [sszDecodeCleanupLoadsWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access6 := sszDecodeCleanupLoadsAccessOfSeg stores.access seg6
  have code6 : Artifacts.programImage.fileBytesLoadedFaithfully state6.mem := by
    rw [seg6.memEq noMemory_empty]
    exact stores.code
  have slots6 := stores.zeroSlots.of_mem_eq (seg6.memEq noMemory_empty)
  have run6 := sszDecodeCleanupLoadA6 (fromStep + 18) args state6 seg6.atPc
    ((seg6.get x2 (by simp [sszDecodeCleanupLoadsWrites, stepBookkeeping])).trans stackAt)
    slots6.slot470 ready.stackFits ready.stackAligned ready.stackUpper access6 code6
  obtain ⟨state7, seg7⟩ := sszDecodeCleanupLoadsAppend seg6 x16 0 0x12358
    (by simp [sszDecodeCleanupLoadsOwnPc]) run6 (by native_decide)
    (by simp [sszDecodeCleanupLoadsWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access7 := sszDecodeCleanupLoadsAccessOfSeg stores.access seg7
  have code7 : Artifacts.programImage.fileBytesLoadedFaithfully state7.mem := by
    rw [seg7.memEq noMemory_empty]
    exact stores.code
  have slots7 := stores.zeroSlots.of_mem_eq (seg7.memEq noMemory_empty)
  have run7 := sszDecodeCleanupLoadA7 (fromStep + 19) args state7 seg7.atPc
    ((seg7.get x2 (by simp [sszDecodeCleanupLoadsWrites, stepBookkeeping])).trans stackAt)
    slots7.slot478 ready.stackFits ready.stackAligned ready.stackUpper access7 code7
  obtain ⟨state8, seg8⟩ := sszDecodeCleanupLoadsAppend seg7 x17 0 0x1235c
    (by simp [sszDecodeCleanupLoadsOwnPc]) run7 (by native_decide)
    (by simp [sszDecodeCleanupLoadsWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access8 := sszDecodeCleanupLoadsAccessOfSeg stores.access seg8
  have code8 : Artifacts.programImage.fileBytesLoadedFaithfully state8.mem := by
    rw [seg8.memEq noMemory_empty]
    exact stores.code
  have slots8 := stores.zeroSlots.of_mem_eq (seg8.memEq noMemory_empty)
  have run8 := sszDecodeCleanupLoadT0 (fromStep + 20) args state8 seg8.atPc
    ((seg8.get x2 (by simp [sszDecodeCleanupLoadsWrites, stepBookkeeping])).trans stackAt)
    slots8.slot480 ready.stackFits ready.stackAligned ready.stackUpper access8 code8
  obtain ⟨state9, seg9⟩ := sszDecodeCleanupLoadsAppend seg8 x5 0 0x12360
    (by simp [sszDecodeCleanupLoadsOwnPc]) run8 (by native_decide)
    (by simp [sszDecodeCleanupLoadsWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  exact ⟨state9, seg9, sszDecodeCleanupLoadsAccessOfSeg stores.access seg9, by
    rw [seg9.memEq noMemory_empty]
    exact stores.code, generalRegistersOfSeg stores.generalRegisters seg9 (by
      intro register member written
      rcases written with bookkeeping | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [stepBookkeeping] at bookkeeping
        rcases bookkeeping with rfl | rfl | rfl | rfl <;>
          simp [architecturalIntegerRegisters] at member
      all_goals simp) ⟩

def sszDecodeSecondStoresOwnPc (pc : BitVec 64) : Prop :=
  0x12360 ≤ pc.toNat ∧ pc.toNat < 0x12398

def sszDecodeSecondStoresExitPc (pc : BitVec 64) : Prop := pc = 0x12398

def sszDecodeSecondStoresMemory (args : DecodeInlineArgs) : Region :=
  byteRange (args.boundary.stackPointer + 0x20) 0xcc

private theorem sszDecodeSecondStoresAppend {width : Nat} {args : DecodeInlineArgs}
    {before cur : State} {a n pc} (seg : Seg sszDecodeSecondStoresOwnPc
      sszDecodeSecondStoresExitPc (fun _ _ _ _ _ => False) stepBookkeeping
      (sszDecodeSecondStoresMemory args) [] a n before cur pc)
    (offset : Nat) (value : BitVec 64) (nextPc : BitVec 64)
    (offsetBound : offset + width ≤ 0xcc)
    (inside : sszDecodeSecondStoresOwnPc pc)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := width)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur) pc)
          (args.boundary.stackPointer + 0x20 + offset) value)
        (Sail.BitVec.addInt pc 4) retired) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc) :
    ∃ next, Seg sszDecodeSecondStoresOwnPc sszDecodeSecondStoresExitPc
      (fun _ _ _ _ _ => False) stepBookkeeping (sszDecodeSecondStoresMemory args)
      [] a (n + 1) before next nextPc := by
  apply seg.stepStore (width := width) (args.boundary.stackPointer + 0x20 + offset) value
    nextPc inside
    (by intro atExit; unfold sszDecodeSecondStoresExitPc at atExit; subst pc
        simp [sszDecodeSecondStoresOwnPc] at inside)
    run advance
  · intro other lower upper
    unfold sszDecodeSecondStoresMemory byteRange
    omega
  · intro register bookkeeping
    exact bookkeeping
  · simp [RegsOutside]

private theorem sszDecodeSecondStoresAccessOfSeg {args : DecodeInlineArgs} {before cur : State}
    {a n pc} (access : DecodeBoundaryMachineAccess args.boundary before)
    (seg : Seg sszDecodeSecondStoresOwnPc sszDecodeSecondStoresExitPc
      (fun _ _ _ _ _ => False) stepBookkeeping (sszDecodeSecondStoresMemory args)
      [] a n before cur pc) :
    DecodeBoundaryMachineAccess args.boundary cur :=
  access.of_pma_regions_eq
    (seg.agree instructionPreserved_disjoint_stepBookkeeping) seg.retired
    (seg.get pma_regions (by simp [stepBookkeeping]))

private theorem sszDecodeSecondStoresCodeOfSeg {args : DecodeInlineArgs} {before cur : State}
    {a n pc} (access : DecodeBoundaryMachineAccess args.boundary before)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg sszDecodeSecondStoresOwnPc sszDecodeSecondStoresExitPc
      (fun _ _ _ _ _ => False) stepBookkeeping (sszDecodeSecondStoresMemory args)
      [] a n before cur pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  intro address byte fileByte
  rw [seg.mem address (by
    intro inside
    unfold sszDecodeSecondStoresMemory byteRange at inside
    have outside := access.callerNotCode address (by omega) (by omega)
    rw [fileByte] at outside
    cases outside)]
  exact code address byte fileByte

/-- The second result-store packet ends before the first fixed-size `memcpy` setup. -/
structure SszDecodeSecondStoresHandoff (fromStep : Nat) (args : DecodeInlineArgs)
    (before after : State) : Prop where
  seg : Seg sszDecodeSecondStoresOwnPc sszDecodeSecondStoresExitPc
    (fun _ _ _ _ _ => False) stepBookkeeping (sszDecodeSecondStoresMemory args)
    [] fromStep 14 before after 0x12398
  access : DecodeBoundaryMachineAccess args.boundary after
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  generalRegisters : GeneralRegistersPresent after

/-- Compose the 13 dword stores and one word store after the cleanup-slot loads. -/
theorem sszDecodeSecondStores (fromStep : Nat) (args : DecodeInlineArgs)
    (source storeAfter loadAfter : State) (ready : SszDecodeResultStoresReady args source)
    (stores : SszDecodeResultStoresHandoff fromStep args source storeAfter)
    (loads : SszDecodeCleanupLoadsHandoff (fromStep + 12) args storeAfter loadAfter) :
    ∃ after, SszDecodeSecondStoresHandoff (fromStep + 21) args loadAfter after := by
  have resultAt : loadAfter.regs.get? x8 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)) :=
    (loads.seg.get x8 (by simp [sszDecodeCleanupLoadsWrites, stepBookkeeping])).trans
      ((stores.seg.get x8 (by simp [stepBookkeeping])).trans ready.resultAt)
  obtain ⟨t5, t5At⟩ := loads.generalRegisters.read (register := x30)
    (by simp [architecturalIntegerRegisters])
  obtain ⟨t2, t2At⟩ := loads.generalRegisters.read (register := x7)
    (by simp [architecturalIntegerRegisters])
  obtain ⟨t1, t1At⟩ := loads.generalRegisters.read (register := x6)
    (by simp [architecturalIntegerRegisters])
  obtain ⟨t4, t4At⟩ := loads.generalRegisters.read (register := x29)
    (by simp [architecturalIntegerRegisters])
  obtain ⟨t3, t3At⟩ := loads.generalRegisters.read (register := x28)
    (by simp [architecturalIntegerRegisters])
  have a0At := loads.seg.reg x10 0 (by simp)
  have a1At := loads.seg.reg x11 0 (by simp)
  have a2At := loads.seg.reg x12 0 (by simp)
  have a3At := loads.seg.reg x13 0 (by simp)
  have a4At := loads.seg.reg x14 0 (by simp)
  have a5At := loads.seg.reg x15 0 (by simp)
  have a6At := loads.seg.reg x16 0 (by simp)
  have a7At := loads.seg.reg x17 0 (by simp)
  have t0At := loads.seg.reg x5 0 (by simp)
  have seg0 := Seg.nil sszDecodeSecondStoresOwnPc sszDecodeSecondStoresExitPc
    (fun _ _ _ _ _ => False) stepBookkeeping (sszDecodeSecondStoresMemory args)
    (fromStep + 21) loads.access.configured.retiredCounter loads.seg.atPc
  have run0 := sszDecodeResultStoreT5 (fromStep + 21) args loadAfter t5 loads.access seg0.atPc
    resultAt t5At ready.stackAligned ready.stackUpper loads.code
  obtain ⟨state1, seg1⟩ := sszDecodeSecondStoresAppend seg0 0x60 t5 0x12364
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run0 (by native_decide)
  have access1 := sszDecodeSecondStoresAccessOfSeg loads.access seg1
  have code1 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg1
  have run1 := sszDecodeResultStoreT2 (fromStep + 22) args state1 t2 access1 seg1.atPc
    ((seg1.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg1.get x7 (by simp [stepBookkeeping])).trans t2At)
    ready.stackAligned ready.stackUpper code1
  obtain ⟨state2, seg2⟩ := sszDecodeSecondStoresAppend seg1 0x68 t2 0x12368
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run1 (by native_decide)
  have access2 := sszDecodeSecondStoresAccessOfSeg loads.access seg2
  have code2 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg2
  have run2 := sszDecodeResultStoreT1 (fromStep + 23) args state2 t1 access2 seg2.atPc
    ((seg2.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg2.get x6 (by simp [stepBookkeeping])).trans t1At)
    ready.stackAligned ready.stackUpper code2
  obtain ⟨state3, seg3⟩ := sszDecodeSecondStoresAppend seg2 0x70 t1 0x1236c
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run2 (by native_decide)
  have access3 := sszDecodeSecondStoresAccessOfSeg loads.access seg3
  have code3 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg3
  have run3 := sszDecodeResultStoreA0Second (fromStep + 24) args state3 0 access3 seg3.atPc
    ((seg3.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg3.get x10 (by simp [stepBookkeeping])).trans a0At)
    ready.stackAligned ready.stackUpper code3
  obtain ⟨state4, seg4⟩ := sszDecodeSecondStoresAppend seg3 0x78 0 0x12370
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run3 (by native_decide)
  have access4 := sszDecodeSecondStoresAccessOfSeg loads.access seg4
  have code4 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg4
  have run4 := sszDecodeResultStoreA1Second (fromStep + 25) args state4 0 access4 seg4.atPc
    ((seg4.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg4.get x11 (by simp [stepBookkeeping])).trans a1At)
    ready.stackAligned ready.stackUpper code4
  obtain ⟨state5, seg5⟩ := sszDecodeSecondStoresAppend seg4 0x80 0 0x12374
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run4 (by native_decide)
  have access5 := sszDecodeSecondStoresAccessOfSeg loads.access seg5
  have code5 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg5
  have run5 := sszDecodeResultStoreT4 (fromStep + 26) args state5 t4 access5 seg5.atPc
    ((seg5.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg5.get x29 (by simp [stepBookkeeping])).trans t4At)
    ready.stackAligned ready.stackUpper code5
  obtain ⟨state6, seg6⟩ := sszDecodeSecondStoresAppend seg5 0x88 t4 0x12378
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run5 (by native_decide)
  have access6 := sszDecodeSecondStoresAccessOfSeg loads.access seg6
  have code6 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg6
  have run6 := sszDecodeResultStoreT3 (fromStep + 27) args state6 t3 access6 seg6.atPc
    ((seg6.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg6.get x28 (by simp [stepBookkeeping])).trans t3At)
    ready.stackAligned ready.stackUpper code6
  obtain ⟨state7, seg7⟩ := sszDecodeSecondStoresAppend seg6 0x90 t3 0x1237c
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run6 (by native_decide)
  have access7 := sszDecodeSecondStoresAccessOfSeg loads.access seg7
  have code7 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg7
  have run7 := sszDecodeResultStoreA2Second (fromStep + 28) args state7 0 access7 seg7.atPc
    ((seg7.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg7.get x12 (by simp [stepBookkeeping])).trans a2At)
    ready.stackAligned ready.stackUpper code7
  obtain ⟨state8, seg8⟩ := sszDecodeSecondStoresAppend seg7 0x98 0 0x12380
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run7 (by native_decide)
  have access8 := sszDecodeSecondStoresAccessOfSeg loads.access seg8
  have code8 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg8
  have run8 := sszDecodeResultStoreA7Second (fromStep + 29) args state8 0 access8 seg8.atPc
    ((seg8.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg8.get x17 (by simp [stepBookkeeping])).trans a7At)
    ready.stackAligned ready.stackUpper code8
  obtain ⟨state9, seg9⟩ := sszDecodeSecondStoresAppend seg8 0xc0 0 0x12384
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run8 (by native_decide)
  have access9 := sszDecodeSecondStoresAccessOfSeg loads.access seg9
  have code9 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg9
  have run9 := sszDecodeResultStoreT0Word (fromStep + 30) args state9 0 access9 seg9.atPc
    ((seg9.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg9.get x5 (by simp [stepBookkeeping])).trans t0At)
    ready.stackAligned ready.stackUpper code9
  obtain ⟨state10, seg10⟩ := sszDecodeSecondStoresAppend seg9 0xc8 0 0x12388
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run9 (by native_decide)
  have access10 := sszDecodeSecondStoresAccessOfSeg loads.access seg10
  have code10 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg10
  have run10 := sszDecodeResultStoreA3Second (fromStep + 31) args state10 0 access10 seg10.atPc
    ((seg10.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg10.get x13 (by simp [stepBookkeeping])).trans a3At)
    ready.stackAligned ready.stackUpper code10
  obtain ⟨state11, seg11⟩ := sszDecodeSecondStoresAppend seg10 0xa0 0 0x1238c
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run10 (by native_decide)
  have access11 := sszDecodeSecondStoresAccessOfSeg loads.access seg11
  have code11 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg11
  have run11 := sszDecodeResultStoreA4Second (fromStep + 32) args state11 0 access11 seg11.atPc
    ((seg11.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg11.get x14 (by simp [stepBookkeeping])).trans a4At)
    ready.stackAligned ready.stackUpper code11
  obtain ⟨state12, seg12⟩ := sszDecodeSecondStoresAppend seg11 0xa8 0 0x12390
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run11 (by native_decide)
  have access12 := sszDecodeSecondStoresAccessOfSeg loads.access seg12
  have code12 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg12
  have run12 := sszDecodeResultStoreA5Second (fromStep + 33) args state12 0 access12 seg12.atPc
    ((seg12.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg12.get x15 (by simp [stepBookkeeping])).trans a5At)
    ready.stackAligned ready.stackUpper code12
  obtain ⟨state13, seg13⟩ := sszDecodeSecondStoresAppend seg12 0xb0 0 0x12394
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run12 (by native_decide)
  have access13 := sszDecodeSecondStoresAccessOfSeg loads.access seg13
  have code13 := sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg13
  have run13 := sszDecodeResultStoreA6Second (fromStep + 34) args state13 0 access13 seg13.atPc
    ((seg13.get x8 (by simp [stepBookkeeping])).trans resultAt)
    ((seg13.get x16 (by simp [stepBookkeeping])).trans a6At)
    ready.stackAligned ready.stackUpper code13
  obtain ⟨state14, seg14⟩ := sszDecodeSecondStoresAppend seg13 0xb8 0 0x12398
    (by omega) (by simp [sszDecodeSecondStoresOwnPc]) run13 (by native_decide)
  exact ⟨state14, seg14, sszDecodeSecondStoresAccessOfSeg loads.access seg14,
    sszDecodeSecondStoresCodeOfSeg loads.access loads.code seg14,
    generalRegistersOfSeg loads.generalRegisters seg14 (by
      intro register member bookkeeping
      simp only [stepBookkeeping] at bookkeeping
      rcases bookkeeping with rfl | rfl | rfl | rfl <;>
        simp [architecturalIntegerRegisters] at member)⟩

/-- The cleanup child return carries the exact facts required by the remaining parent stores. -/
theorem sszDecodeCleanupAfterMemcpy (fromStep : Nat) (args : DecodeInlineArgs)
    (template : EndpointState) (before : State) (ready : SszDecodeCleanupReady args before) :
    ∃ (callReady : State) (callState : EndpointState) (used : Nat) (after : EndpointState),
      Seg sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
        (fun _ _ _ _ _ => False) sszDecodeCleanupWrites (sszDecodeCleanupMemory args)
        [⟨x1, 0x102b0⟩, ⟨x12, 256⟩,
          ⟨x10, BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0 + 0x330)⟩,
          ⟨x11, 0x1755c⟩]
        fromStep 22 before callReady 0x122b4 ∧
      Runs (try_step (fromStep + 22) false) callReady callState.machine false ∧
      callState.machine.regs.get? PC = some 0x101d4 ∧
      callState = { template with machine := callState.machine } ∧
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.memcpyExecutionPcRanges)
        (fromStep + 23) used callState after ∧
      SszDecodeCleanupResume args after.machine := by
  obtain ⟨callReady, callState, used, after, seg, callRun, callStack, callResult, callAgree,
    callPma, callStateEq, callGeneral, callSlots, entry, childTrace, childExit⟩ :=
    sszDecodeCleanupMemcpyChild fromStep args template before ready
  rcases childExit with ⟨childPc, _stdin, _cursor, _stdout, _exitCode, _destination,
    _source, codeAfter, childMem, childFrame, childGeneralPreserved⟩
  rcases childFrame with ⟨childRegisters, childRetired, childCode, childChoice, childTags,
    childOutput⟩
  unfold MemcpyEntry at entry
  rcases entry with ⟨_return, _size, _destinationFits, _sourceFits, _disjoint, _atPc,
    _atLink, _atDestination, _atSource, _atSize, _sourceRep, _callCode, memcpyAccess⟩
  have childAgree : Agree instructionPreserved callState.machine after.machine :=
    childRegisters.weaken instructionPreserved_abiCalleePreserved_cleanup
  have wholeAgree := callAgree.trans childAgree
  have childPma : after.machine.regs.get? pma_regions = before.regs.get? pma_regions :=
    (childRegisters pma_regions (by simp [abiCalleePreserved])).trans callPma
  have resume : SszDecodeCleanupResume args after.machine :=
    { atPc := by simpa [sszDecodeCleanupMemcpyArgs] using childPc
      atStack := (childRegisters x2 (by simp [abiCalleePreserved])).trans callStack
      resultAt := (childRegisters x8 (by simp [abiCalleePreserved])).trans callResult
      stackFits := ready.stackFits
      stackAligned := ready.stackAligned
      stackUpper := ready.stackUpper
      access := ready.access.of_pma_regions_eq wholeAgree childRetired childPma
      code := codeAfter
      generalRegisters := childGeneralPreserved callGeneral
      zeroSlots := callSlots.of_lowerFrameWrites childMem (by
        intro address inside
        unfold byteRange sszDecodeCleanupMemcpyArgs at inside
        simp only [sszDecodeCleanupTemplateBytes, Array.size_ofFn] at inside
        omega) }
  exact ⟨callReady, callState, used, after, seg, callRun, by simpa using _atPc, callStateEq, by
    simpa only using childTrace, resume⟩

private theorem iTypeResult_addi_four_ofNat (value : Nat) :
    iTypeResult .ADDI 4 (BitVec.ofNat 64 value) = BitVec.ofNat 64 (value + 4) := by
  unfold iTypeResult
  have immediate : sign_extend (m := 64) (4#12) = (4#64) := by native_decide
  change BitVec.ofNat 64 value + sign_extend (m := 64) (4#12) = _
  rw [immediate, ← BitVec.ofNat_add]

private theorem inputAtLeastSix_of_minimumComparison (size : Nat) (atLeastFour : 4 ≤ size)
    (sizeFits : size < 2 ^ 64)
    (minimum : zopz0zI_u (iTypeResult .ADDI 0xffc (BitVec.ofNat 64 size)) 2 = false) :
    6 ≤ size := by
  have subtractFour :
      iTypeResult .ADDI 0xffc (BitVec.ofNat 64 size) = BitVec.ofNat 64 (size - 4) := by
    simp only [iTypeResult]
    have immediate : sign_extend (m := 64) (0xffc#12) =
        BitVec.ofNat 64 (2 ^ 64 - 4) := by native_decide
    change BitVec.ofNat 64 size + sign_extend (m := 64) (0xffc#12) = _
    rw [immediate, ← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp
    omega
  rw [subtractFour] at minimum
  simp [zopz0zI_u, Sail.BitVec.toNatInt] at minimum
  omega

private theorem sszDecodeLengthValidatedOwnPc_in_initial {pc : BitVec 64}
    (inside : sszDecodeLengthValidatedOwnPc pc) : DecodeInlineInitialExecutionPc pc := by
  simp [sszDecodeLengthValidatedOwnPc, pcInList] at inside
  rcases inside with inside | inside | inside | inside | inside
  all_goals
    unfold DecodeInlineInitialExecutionPc pcInRanges
    exact ⟨(0x121ac, 0x14ca8), by simp [Elflings.sszDecodeExecutionPcRanges], by omega,
      by omega⟩

private theorem sszDecodeLengthMinimumOwnPc_in_initial {pc : BitVec 64}
    (inside : sszDecodeLengthMinimumOwnPc pc) : DecodeInlineInitialExecutionPc pc := by
  simp [sszDecodeLengthMinimumOwnPc, pcInList] at inside
  rcases inside with inside | inside
  all_goals
    unfold DecodeInlineInitialExecutionPc pcInRanges
    exact ⟨(0x121ac, 0x14ca8), by simp [Elflings.sszDecodeExecutionPcRanges], by omega,
      by omega⟩

private theorem sszDecodeLengthValidatedOwnPc_not_observed {pc : BitVec 64}
    (inside : sszDecodeLengthValidatedOwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  simp [sszDecodeLengthValidatedOwnPc, pcInList] at inside
  unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc
    at observed
  rcases inside with inside | inside | inside | inside | inside
  all_goals rcases observed with observed | observed | observed <;> omega

private theorem sszDecodeLengthMinimumOwnPc_not_observed {pc : BitVec 64}
    (inside : sszDecodeLengthMinimumOwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  simp [sszDecodeLengthMinimumOwnPc, pcInList] at inside
  unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc
    at observed
  rcases inside with inside | inside
  all_goals rcases observed with observed | observed | observed <;> omega

private theorem sszDecodeCleanupOwnPc_in_initial {pc : BitVec 64}
    (inside : sszDecodeCleanupOwnPc pc) : DecodeInlineInitialExecutionPc pc := by
  unfold sszDecodeCleanupOwnPc at inside
  unfold DecodeInlineInitialExecutionPc pcInRanges
  exact ⟨(0x121ac, 0x14ca8), by simp [Elflings.sszDecodeExecutionPcRanges], by omega,
    by omega⟩

private theorem sszDecodeCleanupOwnPc_not_observed {pc : BitVec 64}
    (inside : sszDecodeCleanupOwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  unfold sszDecodeCleanupOwnPc at inside
  unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc
    at observed
  rcases observed with observed | observed | observed <;> omega

private theorem memcpyPc_in_sszDecodeInitial {pc : BitVec 64}
    (inside : pcInRanges Elflings.memcpyExecutionPcRanges pc) :
    DecodeInlineInitialExecutionPc pc := by
  unfold pcInRanges at inside
  unfold DecodeInlineInitialExecutionPc pcInRanges
  rcases inside with ⟨range, member, lower, upper⟩
  simp [Elflings.memcpyExecutionPcRanges] at member
  rcases member with rfl
  exact ⟨(0x101d4, 0x12168), by simp [Elflings.sszDecodeExecutionPcRanges], lower,
    Nat.lt_trans upper (by native_decide)⟩

private theorem scopedTraceOfSegAtExit {own exit : BitVec 64 → Prop} {W : RegSet} {M : Region}
    {kv : List RegVal} {a n : Nat} {base cur : State} {pc : BitVec 64}
    (seg : Seg own exit (fun _ _ _ _ _ => False) W M kv a n base cur pc)
    (atExit : exit pc) : ScopedTrace own exit (fun _ _ _ _ _ => False) a n base cur := by
  have endTrace : ScopedTrace own exit (fun _ _ _ _ _ => False) (a + n) 0 cur cur :=
    .exitAt (a + n) cur pc seg.atPc atExit
  simpa using seg.confined 0 cur endTrace

/-- The restored child frame supports all twenty stores and the final success-tag write. -/
theorem sszDecodeCleanupResumeTrace (fromStep : Nat) (args : DecodeInlineArgs)
    (template : EndpointState) (before : State) (resume : SszDecodeCleanupResume args before) :
    ∃ after,
      ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc fromStep 21
        { template with machine := before } { template with machine := after } ∧
      SszDecodeResultStoresReady args after := by
  obtain ⟨after, seg⟩ := sszDecodeCleanupAfterMemcpyComplete fromStep args before resume.atPc
    resume.atStack resume.stackFits resume.stackAligned resume.stackUpper resume.access
    resume.access.configured resume.code
  have localTrace := scopedTraceOfSegAtExit seg (by simp [sszDecodeCleanupExitPc])
  have lifted := liftSszDecodeParentTrace sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
    sszDecodeCleanupOwnPc_in_initial sszDecodeCleanupOwnPc_not_observed template localTrace
  have access := sszDecodeCleanupTailAccessOfSeg resume.access seg
  exact ⟨after, by simpa using lifted,
    { atPc := seg.atPc
      atStack := (seg.get x2 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans
        resume.atStack
      resultAt := (seg.get x8 (by simp [sszDecodeCleanupTailWrites, stepBookkeeping])).trans
        resume.resultAt
      statusAt := seg.reg x22 1 (by simp)
      stackFits := resume.stackFits
      stackAligned := resume.stackAligned
      stackUpper := resume.stackUpper
      access := access
      configured := access.configured
      code := sszDecodeCleanupTailCodeOfSeg resume.stackFits resume.access resume.code seg
      generalRegisters := generalRegistersOfSeg resume.generalRegisters seg (by
        intro register member written
        rcases written with bookkeeping | rfl
        · simp only [stepBookkeeping] at bookkeeping
          rcases bookkeeping with rfl | rfl | rfl | rfl <;>
            simp [architecturalIntegerRegisters] at member
        · simp)
      zeroSlots := resume.zeroSlots.of_lowerFrameWrites seg.mem (by
        intro address inside
        unfold sszDecodeCleanupTailMemory byteRange at inside
        omega) }⟩

/-- The proved `memcpy` body and the 21-step cleanup tail execute in dependency order. -/
theorem sszDecodeCleanupChildAndTail (fromStep : Nat) (args : DecodeInlineArgs)
    (template : EndpointState) (before : State) (ready : SszDecodeCleanupReady args before) :
    ∃ (callState : EndpointState) (childUsed : Nat) (childAfter : EndpointState)
        (after : State),
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.memcpyExecutionPcRanges)
        (fromStep + 23) childUsed callState childAfter ∧
      ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
        (fromStep + 23 + childUsed) 21 childAfter
        { childAfter with machine := after } ∧
      SszDecodeResultStoresReady args after := by
  obtain ⟨_callReady, callState, childUsed, childAfter, _seg, _callRun, _callAtPc,
    _callStateEq, childTrace, resume⟩ :=
    sszDecodeCleanupAfterMemcpy fromStep args template before ready
  obtain ⟨after, tailTrace, storeReady⟩ :=
    sszDecodeCleanupResumeTrace (fromStep + 23 + childUsed) args childAfter
      childAfter.machine resume
  exact ⟨callState, childUsed, childAfter, after, childTrace, by simpa using tailTrace,
    storeReady⟩

/-- The cleanup parent prefix, proved `memcpy` child, and return tail form one decoder trace. -/
theorem sszDecodeCleanupTrace (fromStep : Nat) (args : DecodeInlineArgs)
    (template : EndpointState) (before : State) (ready : SszDecodeCleanupReady args before) :
    ∃ (childUsed : Nat) (after : EndpointState),
      ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc fromStep
        (23 + childUsed + 21) { template with machine := before } after ∧
      SszDecodeResultStoresReady args after.machine := by
  obtain ⟨callReady, callState, childUsed, childAfter, seg, callRun, callAtPc,
    callStateEq, childTrace, resume⟩ :=
    sszDecodeCleanupAfterMemcpy fromStep args template before ready
  have endAtCall : ScopedTrace sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) (fromStep + 23) 0 callState.machine callState.machine :=
    .exitAt (fromStep + 23) callState.machine 0x101d4 callAtPc (by
      unfold sszDecodeCleanupExitPc
      exact Or.inl rfl)
  have callPrefix : ConfinedPrefix sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
      (fun _ _ _ _ _ => False) (fromStep + 22) 1 callReady callState.machine :=
    ConfinedPrefix.ownStep seg.atPc (by simp [sszDecodeCleanupOwnPc])
      (by simp [sszDecodeCleanupExitPc]) callRun
  have parentMachineTrace := seg.confined.trans callPrefix 0 callState.machine endAtCall
  have parentTrace := liftSszDecodeParentTrace sszDecodeCleanupOwnPc sszDecodeCleanupExitPc
    sszDecodeCleanupOwnPc_in_initial sszDecodeCleanupOwnPc_not_observed template (by
      simpa [Nat.add_assoc] using parentMachineTrace)
  have childTrace' := childTrace.weaken (fun _ inside => memcpyPc_in_sszDecodeInitial inside)
  rw [callStateEq] at childTrace'
  obtain ⟨tailMachine, tailTrace, storeReady⟩ :=
    sszDecodeCleanupResumeTrace (fromStep + 23 + childUsed) args childAfter childAfter.machine
      resume
  rcases childAfter with ⟨childMachine, childStdin, childCursor, childStdout, childExitCode⟩
  have throughChild := parentTrace.append childTrace'
  have tailTrace' : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      (fromStep + (23 + childUsed)) 21
      { machine := childMachine, stdin := childStdin, stdinCursor := childCursor,
        stdout := childStdout, exitCode := childExitCode }
      { machine := tailMachine, stdin := childStdin, stdinCursor := childCursor,
        stdout := childStdout, exitCode := childExitCode } := by
    simpa [Nat.add_assoc] using tailTrace
  have fullTrace := throughChild.append tailTrace'
  exact ⟨childUsed,
    { machine := tailMachine, stdin := childStdin, stdinCursor := childCursor,
      stdout := childStdout, exitCode := childExitCode },
    by simpa [Nat.add_assoc] using fullTrace,
    storeReady⟩

private theorem instructionPreserved_disjoint_sszDecodeLengthValidatedWrites_for_staging :
    RegSet.Disjoint instructionPreserved sszDecodeLengthValidatedWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem instructionPreserved_disjoint_sszDecodeLengthMinimumWrites_for_staging :
    RegSet.Disjoint instructionPreserved sszDecodeLengthMinimumWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  · simp [instructionPreserved, platformPreserved] at preserved

private theorem instructionPreserved_disjoint_sszDecodeLengthShortWrites_for_staging :
    RegSet.Disjoint instructionPreserved sszDecodeLengthShortWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  · simp [instructionPreserved, platformPreserved] at preserved

private theorem sszDecodeLengthShortOwnPc_in_initial {pc : BitVec 64}
    (inside : sszDecodeLengthShortOwnPc pc) : DecodeInlineInitialExecutionPc pc := by
  unfold sszDecodeLengthShortOwnPc at inside
  subst pc
  unfold DecodeInlineInitialExecutionPc pcInRanges
  exact ⟨(0x121ac, 0x14ca8), by simp [Elflings.sszDecodeExecutionPcRanges],
    by native_decide, by native_decide⟩

private theorem sszDecodeLengthShortOwnPc_not_observed {pc : BitVec 64}
    (inside : sszDecodeLengthShortOwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  unfold sszDecodeLengthShortOwnPc at inside
  subst pc
  unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc
  native_decide

private theorem instructionPreserved_disjoint_sszDecodeForkNameByteWrites_for_staging :
    RegSet.Disjoint instructionPreserved sszDecodeForkNameByteWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  · simp [instructionPreserved, platformPreserved] at preserved

private theorem platformPreserved_disjoint_sszDecodeForkNameByteWrites_for_staging :
    RegSet.Disjoint platformPreserved sszDecodeForkNameByteWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl
  · exact platformPreserved_disjoint register preserved bookkeeping
  · simp [platformPreserved] at preserved

private theorem platformPreserved_disjoint_sszDecodeSchemaMarkerWrites_for_staging :
    RegSet.Disjoint platformPreserved sszDecodeSchemaMarkerWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint register preserved bookkeeping
  all_goals simp [platformPreserved] at preserved

private theorem instructionPreserved_disjoint_sszDecodeSchemaMarkerWrites_for_staging :
    RegSet.Disjoint instructionPreserved sszDecodeSchemaMarkerWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem sszDecodeSchemaMarkerOwnPc_in_initial {pc : BitVec 64}
    (inside : sszDecodeSchemaMarkerOwnPc pc) : DecodeInlineInitialExecutionPc pc := by
  simp [sszDecodeSchemaMarkerOwnPc, pcInList] at inside
  rcases inside with inside | inside | inside
  all_goals
    unfold DecodeInlineInitialExecutionPc pcInRanges
    exact ⟨(0x121ac, 0x14ca8), by simp [Elflings.sszDecodeExecutionPcRanges], by omega,
      by omega⟩

private theorem sszDecodeForkNameByteOwnPc_in_initial {pc : BitVec 64}
    (inside : sszDecodeForkNameByteOwnPc pc) : DecodeInlineInitialExecutionPc pc := by
  unfold sszDecodeForkNameByteOwnPc at inside
  subst pc
  unfold DecodeInlineInitialExecutionPc pcInRanges
  exact ⟨(0x121ac, 0x14ca8), by simp [Elflings.sszDecodeExecutionPcRanges], by native_decide,
    by native_decide⟩

private theorem forkNameOwnPc_in_initial {pc : BitVec 64}
    (inside : forkNameOwnPc pc) : DecodeInlineInitialExecutionPc pc := by
  simp [forkNameOwnPc, pcInList] at inside
  rcases inside with inside | inside | inside | inside | inside | inside | inside | inside |
    inside | inside | inside | inside
  all_goals
    unfold DecodeInlineInitialExecutionPc pcInRanges
    exact ⟨(0x121ac, 0x14ca8), by simp [Elflings.sszDecodeExecutionPcRanges], by omega,
      by omega⟩

private theorem sszDecodeSchemaMarkerOwnPc_not_observed {pc : BitVec 64}
    (inside : sszDecodeSchemaMarkerOwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  simp [sszDecodeSchemaMarkerOwnPc, pcInList] at inside
  unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc
    at observed
  rcases observed with observed | observed | observed
  all_goals omega

private theorem sszDecodeForkNameByteOwnPc_not_observed {pc : BitVec 64}
    (inside : sszDecodeForkNameByteOwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  unfold sszDecodeForkNameByteOwnPc at inside
  subst pc
  unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc exitContextStorePc
  native_decide

/-- The parent byte load constructs the exact entry of the proved fork-name child. -/
theorem sszDecodeForkNameChildHandoff (fromStep baseAddress schema : Nat)
    (args : ForkNameArgs) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x12218)
    (base : before.machine.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 before.machine.mem baseAddress schema)
    (pma : LoadPmaAllows before.machine (BitVec.ofNat 64 baseAddress) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 baseAddress) 1)
    (configured : ConfiguredMachinePre EndpointMachinePc before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (schemaEq : args.schema = schema)
    (selection : ForkNameSelectionFacts args before) :
    ∃ after,
      Seg sszDecodeForkNameByteOwnPc sszDecodeForkNameByteExitPc
        (fun _ _ _ _ _ => False) sszDecodeForkNameByteWrites noMemory
        [⟨x10, zero_extend (m := 64) (BitVec.ofNat 8 schema)⟩]
        fromStep 1 before.machine after.machine 0x1221c ∧
      forkNameSelectionEntry args after := by
  have baseFits : baseAddress < 2 ^ 64 := by
    have := rep.2.1
    omega
  obtain ⟨afterMachine, seg⟩ := sszDecodeForkNameByteSeg fromStep baseAddress schema
    before.machine configured atPc base rep pma notMMIO baseFits loaded
  let after : EndpointState := { before with machine := afterMachine }
  have schemaFits : schema < 2 ^ 8 := rep.1
  have schemaWord : zero_extend (m := 64) (BitVec.ofNat 8 schema) = BitVec.ofNat 64 schema := by
    apply BitVec.eq_of_toNat_eq
    simp [zero_extend, Sail.BitVec.zeroExtend, Nat.mod_eq_of_lt schemaFits,
      Nat.mod_eq_of_lt (by omega : schema < 2 ^ 64)]
  have agree := seg.agree instructionPreserved_disjoint_sszDecodeForkNameByteWrites_for_staging
  have platformAgree :=
    seg.agree platformPreserved_disjoint_sszDecodeForkNameByteWrites_for_staging
  have memory := seg.memEq noMemory_empty
  refine ⟨after, by simpa [after] using seg, seg.atPc, ?_, ?_, ?_, ?_⟩
  · rw [schemaEq, ← schemaWord]
    exact seg.reg x10 (zero_extend (m := 64) (BitVec.ofNat 8 schema)) (by simp)
  · exact configured.mono agree seg.retired
  · rw [memory]
    exact loaded
  · unfold ForkNameSelectionFacts at selection ⊢
    rw [schemaEq] at selection ⊢
    cases selectedEq : args.selected with
    | none => simpa only [selectedEq] using selection
    | some fork =>
        simp only [selectedEq] at selection ⊢
        rcases selection with ⟨meaning, accepted, tableEq, targetRep, targetPma, targetNotMMIO,
          tableFits, tableAligned, targetAligned, targetUpdate⟩
        exact ⟨meaning, accepted, tableEq, targetRep.of_mem_eq memory,
          loadPmaAllows_of_agree platformAgree targetPma, targetNotMMIO, tableFits, tableAligned,
          targetAligned, targetUpdate⟩

/-- The accepted schema marker, schema-byte load, and fork-name child entry share one typed
handoff. All accepted and rejected schema values use the same proof. -/
theorem sszDecodeForkNameEntryFromMarker (fromStep baseAddress schema : Nat)
    (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x1220c)
    (base : before.machine.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (markerRep : UIntRep 1 before.machine.mem (baseAddress + 1) 1)
    (schemaRep : UIntRep 1 before.machine.mem baseAddress schema)
    (markerPma : LoadPmaAllows before.machine (BitVec.ofNat 64 (baseAddress + 1)) 1)
    (schemaPma : LoadPmaAllows before.machine (BitVec.ofNat 64 baseAddress) 1)
    (markerNoMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 1)) 1)
    (schemaNoMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 baseAddress) 1)
    (sumFits : baseAddress + 1 < 2 ^ 64)
    (configured : ConfiguredMachinePre EndpointMachinePc before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (tablePma : ∀ offset width, offset + width ≤ 21 * 8 →
      LoadPmaAllows before.machine (BitVec.ofNat 64 (0x17228 + offset)) width)
    (tableNoMMIO : ∀ offset width, offset + width ≤ 21 * 8 →
      LoadMMIOAddressExcluded (BitVec.ofNat 64 (0x17228 + offset)) width) :
    ∃ (markerMachine childMachine : State),
      Seg sszDecodeSchemaMarkerOwnPc sszDecodeSchemaMarkerExitPc
        (fun _ _ _ _ _ => False) sszDecodeSchemaMarkerWrites noMemory
        [⟨x12, 1⟩, ⟨x10, zero_extend (m := 64) (BitVec.ofNat 8 1)⟩]
        fromStep 3 before.machine markerMachine 0x12218 ∧
      Seg sszDecodeForkNameByteOwnPc sszDecodeForkNameByteExitPc
        (fun _ _ _ _ _ => False) sszDecodeForkNameByteWrites noMemory
        [⟨x10, zero_extend (m := 64) (BitVec.ofNat 8 schema)⟩]
        (fromStep + 3) 1 markerMachine childMachine 0x1221c ∧
      forkNameSelectionEntry (forkNameArgsForSchema schema)
        { before with machine := childMachine } := by
  obtain ⟨markerMachine, markerSeg⟩ := sszDecodeSchemaMarkerSeg fromStep baseAddress 1
    before.machine configured atPc base markerRep markerPma markerNoMMIO sumFits
    (rejected := false) (by native_decide) loaded
  let markerAfter : EndpointState := { before with machine := markerMachine }
  have memory := markerSeg.memEq noMemory_empty
  have platformAgree :=
    markerSeg.agree platformPreserved_disjoint_sszDecodeSchemaMarkerWrites_for_staging
  have markerConfigured := configured.mono
    (markerSeg.agree instructionPreserved_disjoint_sszDecodeSchemaMarkerWrites_for_staging)
    markerSeg.retired
  have markerLoaded : Artifacts.programImage.fileBytesLoadedFaithfully markerMachine.mem := by
    rw [memory]
    exact loaded
  have selection := forkNameSelectionFacts_forSchema schema schemaRep.1 markerAfter markerLoaded
    (fun offset width bound =>
      loadPmaAllows_of_agree platformAgree (tablePma offset width bound))
    tableNoMMIO
  obtain ⟨childAfter, childSeg, childEntry⟩ := sszDecodeForkNameChildHandoff
    (fromStep + 3) baseAddress schema (forkNameArgsForSchema schema) markerAfter markerSeg.atPc
    ((markerSeg.get x18 (by simp [sszDecodeSchemaMarkerWrites, stepBookkeeping])).trans base)
    (schemaRep.of_mem_eq memory)
    (loadPmaAllows_of_agree platformAgree schemaPma) schemaNoMMIO markerConfigured markerLoaded rfl
    selection
  exact ⟨markerMachine, childAfter.machine, markerSeg, childSeg, by simpa [markerAfter] using childEntry⟩

/-- The accepted marker route and the proved fork-name child form one parent-owned trace. -/
theorem sszDecodeForkNameTraceFromMarker (fromStep baseAddress schema : Nat)
    (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x1220c)
    (base : before.machine.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (markerRep : UIntRep 1 before.machine.mem (baseAddress + 1) 1)
    (schemaRep : UIntRep 1 before.machine.mem baseAddress schema)
    (markerPma : LoadPmaAllows before.machine (BitVec.ofNat 64 (baseAddress + 1)) 1)
    (schemaPma : LoadPmaAllows before.machine (BitVec.ofNat 64 baseAddress) 1)
    (markerNoMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 1)) 1)
    (schemaNoMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 baseAddress) 1)
    (sumFits : baseAddress + 1 < 2 ^ 64)
    (configured : ConfiguredMachinePre EndpointMachinePc before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (tablePma : ∀ offset width, offset + width ≤ 21 * 8 →
      LoadPmaAllows before.machine (BitVec.ofNat 64 (0x17228 + offset)) width)
    (tableNoMMIO : ∀ offset width, offset + width ≤ 21 * 8 →
      LoadMMIOAddressExcluded (BitVec.ofNat 64 (0x17228 + offset)) width) :
    ∃ used childBefore after outcome,
      used ≤ 12 ∧
      ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc fromStep (4 + used)
        before after ∧
      forkNameSelectionExit (forkNameArgsForSchema schema) outcome childBefore after := by
  obtain ⟨markerMachine, childMachine, markerSeg, byteSeg, childEntry⟩ :=
    sszDecodeForkNameEntryFromMarker fromStep baseAddress schema before atPc base markerRep
      schemaRep markerPma schemaPma markerNoMMIO schemaNoMMIO sumFits configured loaded tablePma
      tableNoMMIO
  let markerAfter : EndpointState := { before with machine := markerMachine }
  let childBefore : EndpointState := { before with machine := childMachine }
  obtain ⟨used, after, outcome, positive, bounded, childTrace, childExitPc, allowed, childExit⟩ :=
    forkNameSelectionContract_implements (forkNameArgsForSchema schema) (fromStep + 4)
      childBefore (by simpa [childBefore] using childEntry)
  have markerMachineTrace := scopedTraceOfSegAtExit markerSeg (by
    simp [sszDecodeSchemaMarkerExitPc, pcInList])
  have markerTrace : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      fromStep 3 before markerAfter := by
    simpa using liftSszDecodeParentTrace sszDecodeSchemaMarkerOwnPc
      sszDecodeSchemaMarkerExitPc sszDecodeSchemaMarkerOwnPc_in_initial
      sszDecodeSchemaMarkerOwnPc_not_observed before markerMachineTrace
  have byteMachineTrace := scopedTraceOfSegAtExit byteSeg (by
    simp [sszDecodeForkNameByteExitPc])
  have byteTrace : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      (fromStep + 3) 1 markerAfter childBefore := by
    simpa using liftSszDecodeParentTrace sszDecodeForkNameByteOwnPc
      sszDecodeForkNameByteExitPc sszDecodeForkNameByteOwnPc_in_initial
      sszDecodeForkNameByteOwnPc_not_observed markerAfter byteMachineTrace
  have childTrace' : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      (fromStep + 4) used childBefore after :=
    childTrace.weaken (fun _ inside => forkNameOwnPc_in_initial inside)
  have markerAndByte := markerTrace.append byteTrace
  have combined := markerAndByte.append childTrace'
  have combined' : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      fromStep (4 + used) before after := by
    simpa only [Nat.reduceAdd] using combined
  have bounded' : used ≤ 12 := by simpa [forkNameSelectionContract] using bounded
  exact ⟨used, childBefore, after, outcome, bounded', combined', childExit⟩

/-- The marker-ready frame supplies every machine fact for the accepted marker and fork-name child. -/
theorem sszDecodeAcceptedForkNameTrace (fromStep : Nat) (args : DecodeInlineArgs)
    (before : EndpointState) (ready : SszDecodeMarkerReady args before.machine)
    (inputAtLeastSix : 6 ≤ args.boundary.input.size)
    (acceptedMarker : args.boundary.input[5].toNat = 1) :
    ∃ used childBefore after outcome,
      used ≤ 12 ∧
      ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc fromStep (4 + used)
        before after ∧
      forkNameSelectionExit
        (forkNameArgsForSchema args.boundary.input[4].toNat) outcome childBefore after := by
  have schemaRep := ready.input.uintRepAt 4 (by omega)
  have markerRep := ready.input.uintRepAt 5 (by omega)
  have markerRep' : UIntRep 1 before.machine.mem (args.boundary.inputAddress + 4 + 1) 1 := by
    have repValue : UIntRep 1 before.machine.mem (args.boundary.inputAddress + 5) 1 :=
      acceptedMarker ▸ markerRep
    simpa only [Nat.reduceAdd, Nat.add_assoc] using repValue
  have markerPma := ready.access.inputLoad 5 1 (by omega)
  have schemaPma := ready.access.inputLoad 4 1 (by omega)
  have markerNoMMIO := ready.access.inputNoMMIO 5 1 (by omega)
  have schemaNoMMIO := ready.access.inputNoMMIO 4 1 (by omega)
  have sumFits : args.boundary.inputAddress + 4 + 1 < 2 ^ 64 := by
    have inputFits := ready.input.1
    omega
  apply sszDecodeForkNameTraceFromMarker fromStep (args.boundary.inputAddress + 4)
    args.boundary.input[4].toNat before ready.atPc ready.sourceAt markerRep' schemaRep
  · simpa only [Nat.add_assoc] using markerPma
  · exact schemaPma
  · simpa only [Nat.add_assoc] using markerNoMMIO
  · exact schemaNoMMIO
  · exact sumFits
  · exact ready.configured
  · exact ready.code
  · exact ready.access.forkNameTableLoad
  · exact ready.access.forkNameTableNoMMIO

/-- A non-one schema marker follows the three-step rejection route to `0x1225c`. -/
theorem sszDecodeRejectedMarkerTrace (fromStep : Nat) (args : DecodeInlineArgs)
    (before : EndpointState) (ready : SszDecodeMarkerReady args before.machine)
    (inputAtLeastSix : 6 ≤ args.boundary.input.size)
    (rejectedMarker : args.boundary.input[5].toNat ≠ 1) :
    ∃ after,
      ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc fromStep 3 before after ∧
      SszDecodeCleanupReady args after.machine := by
  let marker := args.boundary.input[5].toNat
  have markerRep := ready.input.uintRepAt 5 (by omega)
  have markerRep' : UIntRep 1 before.machine.mem (args.boundary.inputAddress + 4 + 1) marker := by
    simpa only [marker, Nat.reduceAdd, Nat.add_assoc] using markerRep
  have markerPma := ready.access.inputLoad 5 1 (by omega)
  have markerNoMMIO := ready.access.inputNoMMIO 5 1 (by omega)
  have sumFits : args.boundary.inputAddress + 4 + 1 < 2 ^ 64 := by
    have inputFits := ready.input.1
    omega
  have comparison :
      (zero_extend (m := 64) (BitVec.ofNat 8 marker) != 1) = true := by
    simp [zero_extend, Sail.BitVec.zeroExtend, markerRep'.1]
    intro equal
    apply rejectedMarker
    have valueEqual := congrArg BitVec.toNat equal
    simpa [marker, markerRep'.1] using valueEqual
  obtain ⟨afterMachine, seg⟩ := sszDecodeSchemaMarkerSeg fromStep
    (args.boundary.inputAddress + 4) marker before.machine ready.configured ready.atPc
    ready.sourceAt markerRep' (by simpa only [Nat.add_assoc] using markerPma)
    (by simpa only [Nat.add_assoc] using markerNoMMIO) sumFits comparison ready.code
  let after : EndpointState := { before with machine := afterMachine }
  have machineTrace := scopedTraceOfSegAtExit seg (by
    simp [sszDecodeSchemaMarkerExitPc, pcInList])
  have trace : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      fromStep 3 before after := by
    simpa [after] using liftSszDecodeParentTrace sszDecodeSchemaMarkerOwnPc
      sszDecodeSchemaMarkerExitPc sszDecodeSchemaMarkerOwnPc_in_initial
      sszDecodeSchemaMarkerOwnPc_not_observed before machineTrace
  have memory := seg.memEq noMemory_empty
  have access := ready.access.of_pma_regions_eq
    (seg.agree instructionPreserved_disjoint_sszDecodeSchemaMarkerWrites_for_staging)
    seg.retired
    (seg.get pma_regions (by simp [sszDecodeSchemaMarkerWrites, stepBookkeeping]))
  refine ⟨after, trace, ?_⟩
  exact
    { atPc := by simpa [after] using seg.atPc
      atStack := by
        simpa [after] using
          (seg.get x2 (by simp [sszDecodeSchemaMarkerWrites, stepBookkeeping])).trans ready.atStack
      resultAt := by
        simpa [after] using
          (seg.get x8 (by simp [sszDecodeSchemaMarkerWrites, stepBookkeeping])).trans ready.resultAt
      stackFits := ready.stackFits
      stackAligned := ready.stackAligned
      stackUpper := ready.stackUpper
      access := by simpa [after] using access
      configured := by simpa [after] using access.configured
      code := by
        simp only [after]
        rw [memory]
        exact ready.code
      generalRegisters := by
        simpa only [after] using generalRegistersOfSeg ready.generalRegisters seg (by
          intro register member written
          rcases written with bookkeeping | rfl | rfl
          · simp only [stepBookkeeping] at bookkeeping
            rcases bookkeeping with rfl | rfl | rfl | rfl <;>
              simp [architecturalIntegerRegisters] at member
          all_goals simp) }

/-- The parent prefix and the proved four-byte child form one initial decoder trace. -/
theorem sszDecodeSchemaWordPrefixAndChild (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (frame : DecodeInlineFrame args values before)
    (atPc : before.machine.regs.get? PC = some 0x121ac)
    (allocatorAt : before.machine.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)))
    (inputSizeAt : before.machine.regs.get? x13 =
      some (BitVec.ofNat 64 args.boundary.input.size))
    (sourceAt : before.machine.regs.get? x18 =
      some (BitVec.ofNat 64 args.boundary.inputAddress))
    (resultAt : before.machine.regs.get? x8 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)))
    (comparison : zopz0zKzJ_u 3 (BitVec.ofNat 64 args.boundary.input.size) = false) :
    ∃ used middle after readArgs,
      readArgs.address = args.boundary.inputAddress ∧
      (∃ bound : 4 ≤ args.boundary.input.size,
        ∃ fits : args.boundary.inputAddress + args.boundary.input.size ≤ 2 ^ 64,
          readArgs = sszDecodeSchemaWordArgs args bound fits) ∧
      used ≤ 10 ∧
      ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc fromStep (6 + used)
        before after ∧
      SszDecodeSchemaWordExit args readArgs after ∧
      memReadIntExit readArgs () middle after := by
  obtain ⟨middleMachine, prefixSeg, childMachineEntry⟩ :=
    sszDecodeAllocatorFallThroughHandoff fromStep args values before frame atPc allocatorAt
      inputSizeAt sourceAt comparison
  let middle : EndpointState := { before with machine := middleMachine }
  let readArgs := sszDecodeSchemaWordArgs args childMachineEntry.inputAtLeastFour
    childMachineEntry.input.1
  have childEntry : memReadIntEntry readArgs middle := by
    exact memReadIntEntry_of_sszDecodeSchemaWord args before middleMachine childMachineEntry
  obtain ⟨used, after, childOutcome, positive, bounded, childTrace, childExitPc, allowed,
    childExit⟩ :=
    memReadIntContract_implements readArgs (fromStep + 6) middle childEntry
  have prefixEnd : ScopedTrace sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
      (fun _ _ _ _ _ => False) (fromStep + 6) 0 middleMachine middleMachine :=
    .exitAt (fromStep + 6) middleMachine 0x121c4 prefixSeg.atPc (by
      unfold sszDecodeAllocatorPrefixExitPc pcInList
      native_decide)
  have prefixMachineTrace : ScopedTrace sszDecodeAllocatorPrefixOwnPc
      sszDecodeAllocatorPrefixExitPc (fun _ _ _ _ _ => False) fromStep 6
      before.machine middleMachine := by
    simpa using prefixSeg.confined 0 middleMachine prefixEnd
  have prefixTrace := liftSszDecodeAllocatorTrace before prefixMachineTrace
  have childTrace' : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      (fromStep + 6) used middle after :=
    childTrace.weaken (fun pc inside => memReadIntOwnPc_in_initial inside)
  have combined := prefixTrace.append childTrace'
  cases childOutcome
  rcases childExit with ⟨childAtPc, schemaAfter, childWrites, childMem, stdinAfter,
    stdinCursorAfter, stdoutAfter, exitCodeAfter, retiredAfter, loadedAfter, auxAfter,
    childGeneralPreserved⟩
  have middleInputSize : middle.machine.regs.get? x13 =
      some (BitVec.ofNat 64 args.boundary.input.size) :=
    (prefixSeg.get x13 (by simp [sszDecodeAllocatorPrefixWrites])).trans inputSizeAt
  have middleSource : middle.machine.regs.get? x18 =
      some (BitVec.ofNat 64 args.boundary.inputAddress) :=
    (prefixSeg.get x18 (by simp [sszDecodeAllocatorPrefixWrites])).trans sourceAt
  have middleStack : middle.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)) :=
    (prefixSeg.get x2 (by simp [sszDecodeAllocatorPrefixWrites])).trans frame.atStack
  have middleResult : middle.machine.regs.get? x8 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)) :=
    (prefixSeg.get x8 (by simp [sszDecodeAllocatorPrefixWrites])).trans resultAt
  have middleGeneral : GeneralRegistersPresent middle.machine :=
    generalRegistersOfSeg frame.generalRegisters prefixSeg (by
      intro register member written
      rcases written with bookkeeping | rfl | rfl | rfl
      · simp only [stepBookkeeping] at bookkeeping
        rcases bookkeeping with rfl | rfl | rfl | rfl <;>
          simp [architecturalIntegerRegisters] at member
      all_goals simp)
  have typedExit : SszDecodeSchemaWordExit args readArgs after :=
    ⟨childAtPc,
      (childWrites.get x2 (by simp [memReadIntWrites])).trans middleStack,
      (childWrites.get x13 (by simp [memReadIntWrites])).trans middleInputSize,
      (childWrites.get x18 (by simp [memReadIntWrites])).trans middleSource,
      (childWrites.get x8 (by simp [memReadIntWrites])).trans middleResult,
      schemaAfter,
      childMachineEntry.input.of_mem_eq childMem,
      childMachineEntry.access.of_pma_regions_eq
        (childWrites.agree instructionPreserved_disjoint_memReadIntWrites_for_sszDecode)
        retiredAfter (childWrites.get pma_regions (by simp [memReadIntWrites, stepBookkeeping])),
      childMachineEntry.access.configured.mono
        (childWrites.agree instructionPreserved_disjoint_memReadIntWrites_for_sszDecode)
        retiredAfter,
      loadedAfter,
      childGeneralPreserved middleGeneral⟩
  have childExit' : memReadIntExit readArgs () middle after :=
    ⟨childAtPc, schemaAfter, childWrites, childMem, stdinAfter, stdinCursorAfter,
      stdoutAfter, exitCodeAfter, retiredAfter, loadedAfter, auxAfter,
      childGeneralPreserved⟩
  refine ⟨used, middle, after, readArgs, rfl,
    ⟨childMachineEntry.inputAtLeastFour, childMachineEntry.input.1, rfl⟩,
    by simpa [memReadIntContract] using bounded, ?_, typedExit, childExit'⟩
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined

/-- The first child, validated-length route, and shared minimum check form one decoder trace. -/
theorem sszDecodeValidatedLengthTrace (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (frame : DecodeInlineFrame args values before)
    (atPc : before.machine.regs.get? PC = some 0x121ac)
    (allocatorAt : before.machine.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)))
    (inputSizeAt : before.machine.regs.get? x13 =
      some (BitVec.ofNat 64 args.boundary.input.size))
    (sourceAt : before.machine.regs.get? x18 =
      some (BitVec.ofNat 64 args.boundary.inputAddress))
    (resultAt : before.machine.regs.get? x8 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)))
    (fieldComparison : zopz0zKzJ_u 3 (BitVec.ofNat 64 args.boundary.input.size) = false)
    (lengthEqual : ∀ (bound : 4 ≤ args.boundary.input.size)
      (fits : args.boundary.inputAddress + args.boundary.input.size ≤ 2 ^ 64),
      iTypeResult .ADDI 0xffc (BitVec.ofNat 64 args.boundary.input.size) =
        memReadIntResult (sszDecodeSchemaWordArgs args bound fits))
    (minimumComparison : zopz0zI_u
      (iTypeResult .ADDI 0xffc (BitVec.ofNat 64 args.boundary.input.size)) 2 = short) :
    ∃ used after,
      used ≤ 10 ∧
      ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc fromStep
        (6 + used + 5 + 2) before after ∧
      after.machine.regs.get? PC = some (if short then 0x1225c else 0x1220c) ∧
      (short = false → SszDecodeMarkerReady args after.machine) := by
  obtain ⟨used, middle, childAfter, readArgs, readAddress, readShape, bounded,
    prefixAndChild, childReady, childExit⟩ :=
    sszDecodeSchemaWordPrefixAndChild fromStep args values before frame atPc allocatorAt
      inputSizeAt sourceAt resultAt fieldComparison
  rcases readShape with ⟨bound, fits, readArgsEq⟩
  subst readArgs
  let candidate := iTypeResult .ADDI 0xffc (BitVec.ofNat 64 args.boundary.input.size)
  let advanced := iTypeResult .ADDI 4 (BitVec.ofNat 64 args.boundary.inputAddress)
  obtain ⟨validatedMachine, validatedSeg⟩ :=
    sszDecodeLengthValidatedRouteSeg (fromStep + 6 + used) childAfter.machine
      childReady.configured childReady.atPc childReady.inputSizeAt childReady.schemaAt
      childReady.sourceAt rfl (lengthEqual bound fits) rfl childReady.code
  let validatedAfter : EndpointState := { childAfter with machine := validatedMachine }
  have validatedMachineTrace := scopedTraceOfSegAtExit validatedSeg (by
    simp [sszDecodeLengthValidatedExitPc])
  have validatedTrace : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      (fromStep + 6 + used) 5 childAfter validatedAfter := by
    simpa [validatedAfter] using
      liftSszDecodeParentTrace sszDecodeLengthValidatedOwnPc
        sszDecodeLengthValidatedExitPc sszDecodeLengthValidatedOwnPc_in_initial
        sszDecodeLengthValidatedOwnPc_not_observed childAfter validatedMachineTrace
  have validatedConfigured := childReady.configured.mono
    (validatedSeg.agree
      instructionPreserved_disjoint_sszDecodeLengthValidatedWrites_for_staging)
    validatedSeg.retired
  have validatedCode : Artifacts.programImage.fileBytesLoadedFaithfully validatedMachine.mem := by
    rw [validatedSeg.memEq noMemory_empty]
    exact childReady.code
  obtain ⟨finalMachine, minimumSeg⟩ :=
    sszDecodeLengthMinimumBranchSeg (fromStep + 6 + used + 5) validatedMachine
      validatedConfigured validatedSeg.atPc
      (validatedSeg.reg x10 candidate (by simp [candidate])) minimumComparison validatedCode
  let after : EndpointState := { validatedAfter with machine := finalMachine }
  have minimumMachineTrace := scopedTraceOfSegAtExit minimumSeg (by
    cases short <;> simp [sszDecodeLengthMinimumExitPc, pcInList])
  have minimumTrace : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      (fromStep + 6 + used + 5) 2 validatedAfter after := by
    simpa [after, validatedAfter] using
      liftSszDecodeParentTrace sszDecodeLengthMinimumOwnPc sszDecodeLengthMinimumExitPc
        sszDecodeLengthMinimumOwnPc_in_initial sszDecodeLengthMinimumOwnPc_not_observed
        validatedAfter minimumMachineTrace
  have validatedTrace' : ConfinedTrace EndpointStep EndpointPc
      DecodeInlineInitialExecutionPc (fromStep + (6 + used)) 5 childAfter validatedAfter := by
    simpa only [Nat.add_assoc] using validatedTrace
  have prefixValidated := prefixAndChild.append validatedTrace'
  have minimumTrace' : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      (fromStep + (6 + used + 5)) 2 validatedAfter after := by
    simpa only [Nat.add_assoc] using minimumTrace
  have combined := prefixValidated.append minimumTrace'
  have validatedAccess := childReady.access.of_pma_regions_eq
    (validatedSeg.agree instructionPreserved_disjoint_sszDecodeLengthValidatedWrites_for_staging)
    validatedSeg.retired
    (validatedSeg.get pma_regions (by simp [sszDecodeLengthValidatedWrites, stepBookkeeping]))
  have minimumAccess := validatedAccess.of_pma_regions_eq
    (minimumSeg.agree instructionPreserved_disjoint_sszDecodeLengthMinimumWrites_for_staging)
    minimumSeg.retired
    (minimumSeg.get pma_regions (by simp [sszDecodeLengthMinimumWrites, stepBookkeeping]))
  have validatedMemory := validatedSeg.memEq noMemory_empty
  have minimumMemory := minimumSeg.memEq noMemory_empty
  have finalMemory := minimumMemory.trans validatedMemory
  refine ⟨used, after, bounded, ?_, minimumSeg.atPc, ?_⟩
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined
  · intro shortEq
    subst short
    have finalSource :=
      (minimumSeg.get x18 (by simp [sszDecodeLengthMinimumWrites, stepBookkeeping])).trans
        (validatedSeg.reg x18 advanced (by simp [advanced]))
    have finalStack :=
      (minimumSeg.get x2 (by simp [sszDecodeLengthMinimumWrites, stepBookkeeping])).trans
        ((validatedSeg.get x2
          (by simp [sszDecodeLengthValidatedWrites, stepBookkeeping])).trans childReady.atStack)
    have finalResult :=
      (minimumSeg.get x8 (by simp [sszDecodeLengthMinimumWrites, stepBookkeeping])).trans
        ((validatedSeg.get x8
          (by simp [sszDecodeLengthValidatedWrites, stepBookkeeping])).trans childReady.resultAt)
    have finalInput := childReady.input.of_mem_eq finalMemory
    have finalCode : Artifacts.programImage.fileBytesLoadedFaithfully finalMachine.mem := by
      rw [minimumMemory]
      exact validatedCode
    have finalAtPc : finalMachine.regs.get? PC = some 0x1220c := by
      have notTrue :
          zopz0zI_u (iTypeResult .ADDI 0xffc
            (BitVec.ofNat 64 args.boundary.input.size)) 2 ≠ true := by
        intro isTrue
        rw [isTrue] at shortEq
        contradiction
      have finalAtPcRaw := minimumSeg.atPc
      rw [if_neg notTrue] at finalAtPcRaw
      exact finalAtPcRaw
    have finalSource' : finalMachine.regs.get? x18 =
        some (BitVec.ofNat 64 (args.boundary.inputAddress + 4)) := by
      unfold advanced at finalSource
      rw [iTypeResult_addi_four_ofNat] at finalSource
      exact finalSource
    have validatedGeneral := generalRegistersOfSeg childReady.generalRegisters validatedSeg (by
      intro register member written
      rcases written with bookkeeping | rfl | rfl | rfl
      · simp only [stepBookkeeping] at bookkeeping
        rcases bookkeeping with rfl | rfl | rfl | rfl <;>
          simp [architecturalIntegerRegisters] at member
      all_goals simp)
    have finalGeneral := generalRegistersOfSeg validatedGeneral minimumSeg (by
      intro register member written
      rcases written with bookkeeping | rfl
      · simp only [stepBookkeeping] at bookkeeping
        rcases bookkeeping with rfl | rfl | rfl | rfl <;>
          simp [architecturalIntegerRegisters] at member
      · simp)
    have markerReady : SszDecodeMarkerReady args finalMachine := by
      apply SszDecodeMarkerReady.mk
      · exact finalAtPc
      · exact finalStack
      · exact frame.stackFits
      · exact frame.stackAligned
      · exact frame.stackUpper
      · exact finalSource'
      · exact finalResult
      · exact bound
      · exact finalInput
      · exact minimumAccess
      · exact minimumAccess.configured
      · exact finalCode
      · exact finalGeneral
    exact markerReady

/-- The validated route derives its byte bound internally and selects either marker rejection or
the proved fork-name child. No byte-index bound is exposed to the parent. -/
theorem sszDecodeValidatedMarkerRoutes (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (frame : DecodeInlineFrame args values before)
    (atPc : before.machine.regs.get? PC = some 0x121ac)
    (allocatorAt : before.machine.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)))
    (inputSizeAt : before.machine.regs.get? x13 =
      some (BitVec.ofNat 64 args.boundary.input.size))
    (sourceAt : before.machine.regs.get? x18 =
      some (BitVec.ofNat 64 args.boundary.inputAddress))
    (resultAt : before.machine.regs.get? x8 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)))
    (fieldComparison : zopz0zKzJ_u 3 (BitVec.ofNat 64 args.boundary.input.size) = false)
    (lengthEqual : ∀ (bound : 4 ≤ args.boundary.input.size)
      (fits : args.boundary.inputAddress + args.boundary.input.size ≤ 2 ^ 64),
      iTypeResult .ADDI 0xffc (BitVec.ofNat 64 args.boundary.input.size) =
        memReadIntResult (sszDecodeSchemaWordArgs args bound fits))
    (minimumComparison : zopz0zI_u
      (iTypeResult .ADDI 0xffc (BitVec.ofNat 64 args.boundary.input.size)) 2 = false) :
    ∃ count after,
      count ≤ 39 ∧
      ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc fromStep count
        before after ∧
      (SszDecodeCleanupReady args after.machine ∨
        ∃ schema childBefore outcome,
          forkNameSelectionExit (forkNameArgsForSchema schema) outcome childBefore after) := by
  obtain ⟨parentUsed, markerState, parentBound, parentTrace, markerPc, markerReady⟩ :=
    sszDecodeValidatedLengthTrace fromStep args values before frame atPc allocatorAt inputSizeAt
      sourceAt resultAt fieldComparison lengthEqual minimumComparison
  have ready := markerReady rfl
  have inputAtLeastSix := inputAtLeastSix_of_minimumComparison args.boundary.input.size
    ready.inputAtLeastFour frame.inputSize.1 minimumComparison
  by_cases acceptedMarker : args.boundary.input[5].toNat = 1
  · obtain ⟨childUsed, childBefore, after, outcome, childBound, childTrace, childExit⟩ :=
      sszDecodeAcceptedForkNameTrace (fromStep + (13 + parentUsed)) args markerState ready
        inputAtLeastSix acceptedMarker
    have parentTrace' : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
        fromStep (13 + parentUsed) before markerState := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using parentTrace
    have childTrace' : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
        (fromStep + (13 + parentUsed)) (4 + childUsed) markerState after := childTrace
    have combined := parentTrace'.append childTrace'
    refine ⟨17 + parentUsed + childUsed, after, by omega, ?_, Or.inr ?_⟩
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined
    · exact ⟨args.boundary.input[4].toNat, childBefore, outcome, childExit⟩
  · obtain ⟨after, rejectedTrace, rejectedPc⟩ := sszDecodeRejectedMarkerTrace
      (fromStep + (13 + parentUsed)) args markerState ready inputAtLeastSix acceptedMarker
    have parentTrace' : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
        fromStep (13 + parentUsed) before markerState := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using parentTrace
    have rejectedTrace' : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
        (fromStep + (13 + parentUsed)) 3 markerState after := rejectedTrace
    have combined := parentTrace'.append rejectedTrace'
    refine ⟨16 + parentUsed, after, by omega, ?_, Or.inl rejectedPc⟩
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined

/-- The first taken branch and shared minimum check form the complete short-input trace. -/
theorem sszDecodeShortLengthTrace (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (frame : DecodeInlineFrame args values before)
    (atPc : before.machine.regs.get? PC = some 0x121ac)
    (allocatorAt : before.machine.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)))
    (inputSizeAt : before.machine.regs.get? x13 =
      some (BitVec.ofNat 64 args.boundary.input.size))
    (resultAt : before.machine.regs.get? x8 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)))
    (fieldComparison : zopz0zKzJ_u 3 (BitVec.ofNat 64 args.boundary.input.size) = true)
    (minimumComparison : zopz0zI_u (BitVec.ofNat 64 args.boundary.input.size) 2 = short) :
    ∃ after,
      ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc fromStep
        (6 + 1 + 2) before after ∧
      after.machine.regs.get? PC = some (if short then 0x1225c else 0x1220c) ∧
      (short = true → SszDecodeCleanupReady args after.machine) := by
  obtain ⟨prefixMachine, prefixSeg, shortEntry⟩ :=
    sszDecodeAllocatorShortHandoff fromStep args values before frame atPc allocatorAt
      inputSizeAt fieldComparison
  let prefixAfter : EndpointState := { before with machine := prefixMachine }
  have prefixMachineTrace := scopedTraceOfSegAtExit prefixSeg (by
    simp [sszDecodeAllocatorPrefixExitPc, pcInList])
  have prefixTrace : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      fromStep 6 before prefixAfter := by
    simpa [prefixAfter] using liftSszDecodeAllocatorTrace before prefixMachineTrace
  obtain ⟨shortMachine, shortSeg⟩ :=
    sszDecodeLengthShortRouteSeg (fromStep + 6) prefixMachine shortEntry.configured
      shortEntry.atPc shortEntry.inputSizeAt shortEntry.code
  let shortAfter : EndpointState := { prefixAfter with machine := shortMachine }
  have shortMachineTrace := scopedTraceOfSegAtExit shortSeg (by
    simp [sszDecodeLengthShortExitPc])
  have shortTrace : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      (fromStep + 6) 1 prefixAfter shortAfter := by
    simpa [shortAfter, prefixAfter] using
      liftSszDecodeParentTrace sszDecodeLengthShortOwnPc sszDecodeLengthShortExitPc
        sszDecodeLengthShortOwnPc_in_initial sszDecodeLengthShortOwnPc_not_observed
        prefixAfter shortMachineTrace
  have shortConfigured := shortEntry.configured.mono
    (shortSeg.agree instructionPreserved_disjoint_sszDecodeLengthShortWrites_for_staging)
    shortSeg.retired
  have shortCode : Artifacts.programImage.fileBytesLoadedFaithfully shortMachine.mem := by
    rw [shortSeg.memEq noMemory_empty]
    exact shortEntry.code
  obtain ⟨finalMachine, minimumSeg⟩ :=
    sszDecodeLengthMinimumBranchSeg (fromStep + 6 + 1) shortMachine shortConfigured
      shortSeg.atPc (shortSeg.reg x10 (BitVec.ofNat 64 args.boundary.input.size) (by simp))
      minimumComparison shortCode
  let after : EndpointState := { shortAfter with machine := finalMachine }
  have minimumMachineTrace := scopedTraceOfSegAtExit minimumSeg (by
    cases short <;> simp [sszDecodeLengthMinimumExitPc, pcInList])
  have minimumTrace : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      (fromStep + 6 + 1) 2 shortAfter after := by
    simpa [after, shortAfter] using
      liftSszDecodeParentTrace sszDecodeLengthMinimumOwnPc sszDecodeLengthMinimumExitPc
        sszDecodeLengthMinimumOwnPc_in_initial sszDecodeLengthMinimumOwnPc_not_observed
        shortAfter minimumMachineTrace
  have shortTrace' : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      (fromStep + 6) 1 prefixAfter shortAfter := shortTrace
  have prefixShort := prefixTrace.append shortTrace'
  have minimumTrace' : ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc
      (fromStep + (6 + 1)) 2 shortAfter after := by
    simpa only [Nat.add_assoc] using minimumTrace
  have combined := prefixShort.append minimumTrace'
  refine ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined,
    minimumSeg.atPc, ?_⟩
  intro shortEq
  subst short
  have shortAccess := shortEntry.access.of_pma_regions_eq
    (shortSeg.agree instructionPreserved_disjoint_sszDecodeLengthShortWrites_for_staging)
    shortSeg.retired
    (shortSeg.get pma_regions (by simp [sszDecodeLengthShortWrites, stepBookkeeping]))
  have finalAccess := shortAccess.of_pma_regions_eq
    (minimumSeg.agree instructionPreserved_disjoint_sszDecodeLengthMinimumWrites_for_staging)
    minimumSeg.retired
    (minimumSeg.get pma_regions (by simp [sszDecodeLengthMinimumWrites, stepBookkeeping]))
  have shortMemory := shortSeg.memEq noMemory_empty
  have minimumMemory := minimumSeg.memEq noMemory_empty
  have cleanupPc := minimumSeg.atPc
  rw [shortEq] at cleanupPc
  have prefixGeneral := generalRegistersOfSeg frame.generalRegisters prefixSeg (by
    intro register member written
    rcases written with bookkeeping | rfl | rfl | rfl
    · simp only [stepBookkeeping] at bookkeeping
      rcases bookkeeping with rfl | rfl | rfl | rfl <;>
        simp [architecturalIntegerRegisters] at member
    all_goals simp)
  have shortGeneral := generalRegistersOfSeg prefixGeneral shortSeg (by
    intro register member written
    rcases written with bookkeeping | rfl
    · simp only [stepBookkeeping] at bookkeeping
      rcases bookkeeping with rfl | rfl | rfl | rfl <;>
        simp [architecturalIntegerRegisters] at member
    · simp)
  have finalGeneral := generalRegistersOfSeg shortGeneral minimumSeg (by
    intro register member written
    rcases written with bookkeeping | rfl
    · simp only [stepBookkeeping] at bookkeeping
      rcases bookkeeping with rfl | rfl | rfl | rfl <;>
        simp [architecturalIntegerRegisters] at member
    · simp)
  exact
    { atPc := by simpa [after] using cleanupPc
      atStack := by
        simpa [after] using
          (minimumSeg.get x2 (by simp [sszDecodeLengthMinimumWrites, stepBookkeeping])).trans
            ((shortSeg.get x2 (by simp [sszDecodeLengthShortWrites, stepBookkeeping])).trans
              shortEntry.atStack)
      resultAt := by
        simpa [after] using
          (minimumSeg.get x8 (by simp [sszDecodeLengthMinimumWrites, stepBookkeeping])).trans
            ((shortSeg.get x8
              (by simp [sszDecodeLengthShortWrites, stepBookkeeping])).trans
              ((prefixSeg.get x8
                (by simp [sszDecodeAllocatorPrefixWrites, stepBookkeeping])).trans resultAt))
      stackFits := shortEntry.stackFits
      stackAligned := shortEntry.stackAligned
      stackUpper := shortEntry.stackUpper
      access := by simpa [after] using finalAccess
      configured := by simpa [after] using finalAccess.configured
      code := by
        simp only [after]
        rw [minimumMemory, shortMemory]
        exact shortEntry.code
      generalRegisters := by simpa [after] using finalGeneral }

end BinaryFv.Zesu.Staging
