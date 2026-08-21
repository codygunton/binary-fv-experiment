import BinaryFv.Zesu.MachineExecution.HLevel3SszDecodeSteps
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
  inputSizeAt : state.machine.regs.get? x13 =
    some (BitVec.ofNat 64 args.boundary.input.size)
  sourceAt : state.machine.regs.get? x18 =
    some (BitVec.ofNat 64 args.boundary.inputAddress)
  schemaAt : state.machine.regs.get? x14 = some (memReadIntResult readArgs)
  configured : ConfiguredMachinePre EndpointMachinePc state.machine
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

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

private theorem instructionPreserved_disjoint_sszDecodeLengthShortWrites_for_staging :
    RegSet.Disjoint instructionPreserved sszDecodeLengthShortWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  · simp [instructionPreserved, platformPreserved] at preserved

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
  have typedExit : SszDecodeSchemaWordExit args readArgs after :=
    ⟨childAtPc,
      (childWrites.get x13 (by simp [memReadIntWrites])).trans middleInputSize,
      (childWrites.get x18 (by simp [memReadIntWrites])).trans middleSource,
      schemaAfter,
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
      after.machine.regs.get? PC = some (if short then 0x1225c else 0x1220c) := by
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
  refine ⟨used, after, bounded, ?_, ?_⟩
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined
  · exact minimumSeg.atPc

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
      after.machine.regs.get? PC = some (if short then 0x1225c else 0x1220c) := by
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
  exact ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined,
    minimumSeg.atPc⟩

end BinaryFv.Zesu.Staging
