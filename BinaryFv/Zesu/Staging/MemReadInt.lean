import BinaryFv.Zesu.MachineExecution.HLevel3MemReadIntSteps

/-!
# The `mem.readInt` hLevel3 boundary

This contract binds the four represented input bytes to the production registers and memory.
The unconditional proof executes the exact ten-instruction inlined instance at `0x121c4`.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register

structure MemReadIntArgs where
  address : Nat
  byte0 : Nat
  byte1 : Nat
  byte2 : Nat
  byte3 : Nat
  sourceFits : address + 4 ≤ 2 ^ 64

def memReadIntResult (args : MemReadIntArgs) : BitVec 64 :=
  let b0 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 args.byte0)
  let b1 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 args.byte1)
  let b2 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 args.byte2)
  let b3 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 args.byte3)
  let s1 := Sail.shift_bits_left b1
    (Sail.BitVec.extractLsb (8#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let s2 := Sail.shift_bits_left b2
    (Sail.BitVec.extractLsb (16#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let s3 := Sail.shift_bits_left b3
    (Sail.BitVec.extractLsb (24#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  (s3 ||| s2) ||| (s1 ||| b0)

def memReadIntEntry (args : MemReadIntArgs) (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 0x121c4) ∧
  state.machine.regs.get? x18 = some (BitVec.ofNat 64 args.address) ∧
  UIntRep 1 state.machine.mem args.address args.byte0 ∧
  UIntRep 1 state.machine.mem (args.address + 1) args.byte1 ∧
  UIntRep 1 state.machine.mem (args.address + 2) args.byte2 ∧
  UIntRep 1 state.machine.mem (args.address + 3) args.byte3 ∧
  (∀ offset, offset < 4 →
    LoadPmaAllows state.machine (BitVec.ofNat 64 (args.address + offset)) 1) ∧
  (∀ offset, offset < 4 →
    LoadMMIOAddressExcluded (BitVec.ofNat 64 (args.address + offset)) 1) ∧
  ConfiguredMachinePre EndpointMachinePc state.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def memReadIntExit (args : MemReadIntArgs) (_outcome : Unit)
    (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 0x121ec) ∧
  after.machine.regs.get? x14 = some (memReadIntResult args) ∧
  WritesOnlyRegs memReadIntWrites before.machine after.machine ∧
  after.machine.mem = before.machine.mem ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  EndpointMachineAuxAgree before.machine after.machine ∧
  GeneralRegistersPreserved before.machine after.machine

def memReadIntContract : RelationalMachineContract EndpointState MemReadIntArgs Unit :=
  { allows := fun _ _ => True
    entry := memReadIntEntry
    exit := memReadIntExit
    stepBound := fun _ => 10 }

private theorem memReadIntOwnPc_not_observed {pc : BitVec 64}
    (inside : memReadIntOwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  unfold memReadIntOwnPc pcInList at inside
  unfold BareMetalHostTransitionPc at observed
  unfold readContextReturnPc writeContextReturnPc exitContextStorePc at observed
  simp at inside
  rcases observed with observed | observed | observed
  all_goals omega

private theorem liftMemReadIntTrace (template : EndpointState)
    {fromStep count : Nat} {before after : State}
    (trace : ScopedTrace memReadIntOwnPc memReadIntExitPc
      (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc memReadIntOwnPc fromStep count
      { template with machine := before } { template with machine := after } := by
  induction trace with
  | exitAt fromStep state pc atPc exitPc =>
      exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step (stepRelation := EndpointStep) (statePc := EndpointPc)
        fromStep count pc
        { template with machine := before } { template with machine := middle }
        { template with machine := after } atPc inside ?_ ?_
      · exact endpointStep_sail fromStep { template with machine := before } middle
          (fun observed observedPc => by
            change before.regs.get? PC = some observed at observedPc
            rw [atPc] at observedPc
            cases Option.some.inj observedPc
            exact memReadIntOwnPc_not_observed inside)
          machineStep
      · simpa using ih
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count callSite program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

/-- The production `mem.readInt` instance satisfies its exact relational contract. -/
theorem memReadIntContract_implements :
    memReadIntContract.Implements EndpointStep EndpointPc memReadIntOwnPc memReadIntExitPc := by
  intro args fromStep before entry
  rcases entry with ⟨atPc, base, rep0, rep1, rep2, rep3, pma, notMMIO, configured, loaded⟩
  obtain ⟨finalMachine, seg, generalPreserved⟩ := memReadIntRun fromStep args.address args.byte0 args.byte1
    args.byte2 args.byte3 before.machine configured atPc base rep0 rep1 rep2 rep3 pma notMMIO
    args.sourceFits loaded
  let after : EndpointState := { before with machine := finalMachine }
  have endTrace : ScopedTrace memReadIntOwnPc memReadIntExitPc
      (fun _ _ _ _ _ => False) (fromStep + 10) 0 finalMachine finalMachine :=
    .exitAt (fromStep + 10) finalMachine 0x121ec seg.atPc (by
      unfold memReadIntExitPc pcInList
      native_decide)
  have machineTrace : ScopedTrace memReadIntOwnPc memReadIntExitPc
      (fun _ _ _ _ _ => False) fromStep 10 before.machine finalMachine := by
    simpa using seg.confined 0 finalMachine endTrace
  refine ⟨10, after, (), by omega, by simp [memReadIntContract], ?_, ?_, trivial, ?_⟩
  · simpa [after] using liftMemReadIntTrace before machineTrace
  · refine ⟨0x121ec, seg.atPc, ?_⟩
    unfold memReadIntExitPc pcInList
    native_decide
  · refine ⟨seg.atPc, ?_, seg.writes, seg.memEq noMemory_empty, rfl, rfl, rfl, rfl,
      seg.retired, ?_, seg.aux, ?_⟩
    · rw [memReadIntResult]
      exact seg.reg x14 _ (by simp)
    · rw [seg.memEq noMemory_empty]
      exact loaded
    · exact generalPreserved

def Proposed_mem_readInt_fi_1_2fa7_Contract : Prop :=
  memReadIntContract.Implements EndpointStep EndpointPc memReadIntOwnPc memReadIntExitPc

theorem proposed_memReadInt_proved : Proposed_mem_readInt_fi_1_2fa7_Contract :=
  memReadIntContract_implements

end BinaryFv.Zesu.Staging
