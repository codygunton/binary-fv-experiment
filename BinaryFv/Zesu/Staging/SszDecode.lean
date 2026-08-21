import BinaryFv.Zesu.MachineExecution.HLevel3SszDecodeSteps
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
  schemaAt : state.machine.regs.get? x14 = some (memReadIntResult readArgs)
  input : BytesRep state.machine.mem args.boundary.inputAddress args.boundary.input
  access : DecodeBoundaryMachineAccess args.boundary state.machine
  configured : ConfiguredMachinePre EndpointMachinePc state.machine
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

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
  inputAtLeastFour : 4 ≤ args.boundary.input.size
  input : BytesRep machine.mem args.boundary.inputAddress args.boundary.input
  access : DecodeBoundaryMachineAccess args.boundary machine
  configured : ConfiguredMachinePre EndpointMachinePc machine
  code : Artifacts.programImage.fileBytesLoadedFaithfully machine.mem

/-- The rejection routes retain the exact stack and machine facts needed by decoder cleanup. -/
structure SszDecodeCleanupReady (args : DecodeInlineArgs) (machine : State) : Prop where
  atPc : machine.regs.get? PC = some 0x1225c
  atStack : machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0))
  stackFits : 0xbb0 ≤ args.boundary.stackPointer
  stackAligned : args.boundary.stackPointer % 16 = 0
  stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64
  access : DecodeBoundaryMachineAccess args.boundary machine
  configured : ConfiguredMachinePre EndpointMachinePc machine
  code : Artifacts.programImage.fileBytesLoadedFaithfully machine.mem

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

private theorem scopedTraceOfSegAtExit {own exit : BitVec 64 → Prop} {W : RegSet} {M : Region}
    {kv : List RegVal} {a n : Nat} {base cur : State} {pc : BitVec 64}
    (seg : Seg own exit (fun _ _ _ _ _ => False) W M kv a n base cur pc)
    (atExit : exit pc) : ScopedTrace own exit (fun _ _ _ _ _ => False) a n base cur := by
  have endTrace : ScopedTrace own exit (fun _ _ _ _ _ => False) (a + n) 0 cur cur :=
    .exitAt (a + n) cur pc seg.atPc atExit
  simpa using seg.confined 0 cur endTrace

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
      stackFits := ready.stackFits
      stackAligned := ready.stackAligned
      stackUpper := ready.stackUpper
      access := by simpa [after] using access
      configured := by simpa [after] using access.configured
      code := by
        simp only [after]
        rw [memory]
        exact ready.code }

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
    stdinCursorAfter, stdoutAfter, exitCodeAfter, retiredAfter, loadedAfter, auxAfter⟩
  have middleInputSize : middle.machine.regs.get? x13 =
      some (BitVec.ofNat 64 args.boundary.input.size) :=
    (prefixSeg.get x13 (by simp [sszDecodeAllocatorPrefixWrites])).trans inputSizeAt
  have middleSource : middle.machine.regs.get? x18 =
      some (BitVec.ofNat 64 args.boundary.inputAddress) :=
    (prefixSeg.get x18 (by simp [sszDecodeAllocatorPrefixWrites])).trans sourceAt
  have middleStack : middle.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)) :=
    (prefixSeg.get x2 (by simp [sszDecodeAllocatorPrefixWrites])).trans frame.atStack
  have typedExit : SszDecodeSchemaWordExit args readArgs after :=
    ⟨childAtPc,
      (childWrites.get x2 (by simp [memReadIntWrites])).trans middleStack,
      (childWrites.get x13 (by simp [memReadIntWrites])).trans middleInputSize,
      (childWrites.get x18 (by simp [memReadIntWrites])).trans middleSource,
      schemaAfter,
      childMachineEntry.input.of_mem_eq childMem,
      childMachineEntry.access.of_pma_regions_eq
        (childWrites.agree instructionPreserved_disjoint_memReadIntWrites_for_sszDecode)
        retiredAfter (childWrites.get pma_regions (by simp [memReadIntWrites, stepBookkeeping])),
      childMachineEntry.access.configured.mono
        (childWrites.agree instructionPreserved_disjoint_memReadIntWrites_for_sszDecode)
        retiredAfter,
      loadedAfter⟩
  have childExit' : memReadIntExit readArgs () middle after :=
    ⟨childAtPc, schemaAfter, childWrites, childMem, stdinAfter, stdinCursorAfter,
      stdoutAfter, exitCodeAfter, retiredAfter, loadedAfter, auxAfter⟩
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
      inputSizeAt sourceAt fieldComparison
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
    have markerReady : SszDecodeMarkerReady args finalMachine := by
      apply SszDecodeMarkerReady.mk
      · exact finalAtPc
      · exact finalStack
      · exact frame.stackFits
      · exact frame.stackAligned
      · exact frame.stackUpper
      · exact finalSource'
      · exact bound
      · exact finalInput
      · exact minimumAccess
      · exact minimumAccess.configured
      · exact finalCode
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
      sourceAt fieldComparison lengthEqual minimumComparison
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
  exact
    { atPc := by simpa [after] using cleanupPc
      atStack := by
        simpa [after] using
          (minimumSeg.get x2 (by simp [sszDecodeLengthMinimumWrites, stepBookkeeping])).trans
            ((shortSeg.get x2 (by simp [sszDecodeLengthShortWrites, stepBookkeeping])).trans
              shortEntry.atStack)
      stackFits := shortEntry.stackFits
      stackAligned := shortEntry.stackAligned
      stackUpper := shortEntry.stackUpper
      access := by simpa [after] using finalAccess
      configured := by simpa [after] using finalAccess.configured
      code := by
        simp only [after]
        rw [minimumMemory, shortMemory]
        exact shortEntry.code }

end BinaryFv.Zesu.Staging
