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

private theorem liftSszDecodeAllocatorTrace (template : EndpointState)
    {fromStep count : Nat} {before after : State}
    (trace : ScopedTrace sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
      (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc DecodeInlineInitialExecutionPc fromStep count
      { template with machine := before } { template with machine := after } := by
  induction trace with
  | exitAt fromStep state pc atPc exitPc => exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step (stepRelation := EndpointStep) (statePc := EndpointPc)
        fromStep count pc
        { template with machine := before } { template with machine := middle }
        { template with machine := after } atPc (sszDecodeAllocatorOwnPc_in_initial inside) ?_ ?_
      · exact endpointStep_sail fromStep { template with machine := before } middle
          (fun observed observedPc => by
            change before.regs.get? PC = some observed at observedPc
            rw [atPc] at observedPc
            cases Option.some.inj observedPc
            exact sszDecodeAllocatorOwnPc_not_observed inside)
          machineStep
      · exact ih
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count callSite program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

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
  refine ⟨used, middle, after, readArgs, rfl,
    ⟨childMachineEntry.inputAtLeastFour, childMachineEntry.input.1, rfl⟩,
    by simpa [memReadIntContract] using bounded, ?_, ?_⟩
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined
  · cases childOutcome
    simpa [memReadIntContract] using childExit

end BinaryFv.Zesu.Staging
