import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HLevel3ReadU32Steps

/-!
# Level 3 `ssz.readU32` contracts

This module defines the shared four-byte contract. It proves the first reviewed instance directly.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register

structure SszReadU32Args where
  sourceAddress : Nat
  sourceBytes : Array UInt8

def sszReadU32Byte (bytes : Array UInt8) (index : Nat) : UInt8 :=
  (bytes[index]?).getD 0

def sszReadU32Value (bytes : Array UInt8) : Nat :=
  (sszReadU32Byte bytes 0).toNat + 256 * (sszReadU32Byte bytes 1).toNat +
    65536 * (sszReadU32Byte bytes 2).toNat +
    16777216 * (sszReadU32Byte bytes 3).toNat

def sszReadU32Preserved3335 (register : Register) : Prop :=
  instructionPreserved register ∧ register ≠ x10 ∧ register ≠ x15 ∧
    register ≠ x13 ∧ register ≠ x14

def sszReadU32SourceX18 (args : SszReadU32Args) (state : EndpointState) : Prop :=
  state.machine.regs.get? x18 = some (BitVec.ofNat 64 args.sourceAddress)

def sszReadU32Entry (entry sourceOffset : Nat)
    (bindSource : SszReadU32Args → EndpointState → Prop) (args : SszReadU32Args)
    (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  bindSource args state ∧
  args.sourceBytes.size = 4 ∧
  args.sourceAddress + sourceOffset + 4 ≤ 2 ^ 64 ∧
  BytesRep state.machine.mem (args.sourceAddress + sourceOffset) args.sourceBytes ∧
  (∀ index, index < 4 →
    LoadPmaAllows state.machine
      (BitVec.ofNat 64 (args.sourceAddress + sourceOffset + index)) 1) ∧
  (∀ index, index < 4 →
    LoadMMIOAddressExcluded
      (BitVec.ofNat 64 (args.sourceAddress + sourceOffset + index)) 1) ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem ∧
  ConfiguredMachinePre EndpointMachinePc state.machine

def sszReadU32Exit (bindBytes : Array UInt8 → EndpointState → Prop)
    (preserved : Register → Prop) (args : SszReadU32Args) (result : Nat)
    (before after : EndpointState) : Prop :=
  result = sszReadU32Value args.sourceBytes ∧
  bindBytes args.sourceBytes after ∧
  Agree preserved before.machine after.machine ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  after.machine.mem = before.machine.mem ∧
  EndpointMachineAuxAgree before.machine after.machine ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode

def sszReadU32Contract (entry sourceOffset : Nat)
    (bindSource : SszReadU32Args → EndpointState → Prop)
    (bindBytes : Array UInt8 → EndpointState → Prop) (preserved : Register → Prop)
    (stepBound : SszReadU32Args → Nat) :
    RelationalMachineContract EndpointState SszReadU32Args Nat :=
  { allows := fun args result => args.sourceBytes.size = 4 ∧
      result = sszReadU32Value args.sourceBytes
    entry := sszReadU32Entry entry sourceOffset bindSource
    exit := sszReadU32Exit bindBytes preserved
    stepBound := stepBound }

def sszReadU32Bindings3335 (bytes : Array UInt8) (state : EndpointState) : Prop :=
  state.machine.regs.get? x10 =
    some (zero_extend (m := 64) (BitVec.ofNat 8 (sszReadU32Byte bytes 0).toNat)) ∧
  state.machine.regs.get? x15 =
    some (zero_extend (m := 64) (BitVec.ofNat 8 (sszReadU32Byte bytes 1).toNat)) ∧
  state.machine.regs.get? x13 =
    some (zero_extend (m := 64) (BitVec.ofNat 8 (sszReadU32Byte bytes 2).toNat)) ∧
  state.machine.regs.get? x14 =
    some (zero_extend (m := 64) (BitVec.ofNat 8 (sszReadU32Byte bytes 3).toNat))

def Proposed_ssz_readU32_fi_1_3335_Contract : Prop :=
  ∃ stepBound : SszReadU32Args → Nat,
    (∀ args, stepBound args < level2ContractFuel) ∧
    (sszReadU32Contract 0x12c18 22 sszReadU32SourceX18 sszReadU32Bindings3335
      sszReadU32Preserved3335 stepBound).Implements EndpointStep EndpointPc
      readU32_3335OwnPc readU32_3335ExitPc

private theorem readU32OwnPc_not_observed {pc : BitVec 64}
    (inside : readU32_3335OwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  unfold readU32_3335OwnPc pcInList at inside
  unfold BareMetalHostTransitionPc at observed
  unfold readContextReturnPc writeContextReturnPc exitContextStorePc at observed
  simp at inside
  rcases observed with observed | observed | observed
  all_goals omega

private theorem liftReadU32Trace (template : EndpointState)
    {own exit : BitVec 64 → Prop} {fromStep count : Nat} {before after : State}
    (ownNotObserved : ∀ {pc}, own pc → ¬BareMetalHostTransitionPc pc)
    (trace : ScopedTrace own exit (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc own fromStep count
      { template with machine := before } { template with machine := after } := by
  induction trace with
  | exitAt fromStep state pc atPc exitPc => exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step (stepRelation := EndpointStep) (statePc := EndpointPc)
        fromStep count pc { template with machine := before } { template with machine := middle }
        { template with machine := after } atPc inside ?_ ?_
      · exact endpointStep_sail fromStep { template with machine := before } middle
          (fun observed observedPc => by
            change before.regs.get? PC = some observed at observedPc
            rw [atPc] at observedPc
            cases Option.some.inj observedPc
            exact ownNotObserved inside)
          machineStep
      · simpa using ih
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count callSite program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

private theorem preservedDisjoint :
    RegSet.Disjoint sszReadU32Preserved3335 readU32_3335Writes := by
  intro register preserved written
  rcases preserved with ⟨instruction, ne10, ne15, ne13, ne14⟩
  rcases written with bookkeeping | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register instruction.1 bookkeeping
  all_goals contradiction

/-- The production `fi:1:3335` instance satisfies its exact relational contract. -/
theorem readU32_3335Contract_implements : Proposed_ssz_readU32_fi_1_3335_Contract := by
  refine ⟨fun _ => 4, by intro; simp [level2ContractFuel], ?_⟩
  intro args fromStep before entry
  rcases entry with ⟨atPc, base, size, sourceFits, bytesRep, pma, notMMIO, loaded, configured⟩
  have rep0 := bytesRep.uintRepAt 0 (by omega)
  have rep1 := bytesRep.uintRepAt 1 (by omega)
  have rep2 := bytesRep.uintRepAt 2 (by omega)
  have rep3 := bytesRep.uintRepAt 3 (by omega)
  obtain ⟨finalMachine, seg⟩ := readU32_3335Run fromStep args.sourceAddress
    args.sourceBytes[0].toNat args.sourceBytes[1].toNat args.sourceBytes[2].toNat
    args.sourceBytes[3].toNat before.machine configured atPc base
    (by simpa [Nat.add_assoc] using rep0) (by simpa [Nat.add_assoc] using rep1)
    (by simpa [Nat.add_assoc] using rep2) (by simpa [Nat.add_assoc] using rep3)
    pma notMMIO sourceFits loaded
  let after : EndpointState := { before with machine := finalMachine }
  have endTrace : ScopedTrace readU32_3335OwnPc readU32_3335ExitPc
      (fun _ _ _ _ _ => False) (fromStep + 4) 0 finalMachine finalMachine :=
    .exitAt (fromStep + 4) finalMachine 0x12c28 seg.atPc (by
      unfold readU32_3335ExitPc pcInList
      native_decide)
  have machineTrace : ScopedTrace readU32_3335OwnPc readU32_3335ExitPc
      (fun _ _ _ _ _ => False) fromStep 4 before.machine finalMachine := by
    simpa using seg.confined 0 finalMachine endTrace
  have b0 : sszReadU32Byte args.sourceBytes 0 = args.sourceBytes[0] := by
    simp [sszReadU32Byte, size]
  have b1 : sszReadU32Byte args.sourceBytes 1 = args.sourceBytes[1] := by
    simp [sszReadU32Byte, size]
  have b2 : sszReadU32Byte args.sourceBytes 2 = args.sourceBytes[2] := by
    simp [sszReadU32Byte, size]
  have b3 : sszReadU32Byte args.sourceBytes 3 = args.sourceBytes[3] := by
    simp [sszReadU32Byte, size]
  refine ⟨4, after, sszReadU32Value args.sourceBytes, by omega,
    by simp [sszReadU32Contract], ?_, ?_, ?_, ?_⟩
  · simpa [after] using liftReadU32Trace before readU32OwnPc_not_observed machineTrace
  · exact ⟨0x12c28, seg.atPc, by unfold readU32_3335ExitPc pcInList; native_decide⟩
  · exact ⟨size, rfl⟩
  · refine ⟨rfl, ?_, seg.writes.agree preservedDisjoint, seg.retired, ?_,
      seg.memEq noMemory_empty, seg.aux, rfl, rfl, rfl, rfl⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · have reg := seg.reg x10
          (zero_extend (m := 64) (BitVec.ofNat 8 args.sourceBytes[0].toNat)) (by simp)
        simpa [after, b0] using reg
      · have reg := seg.reg x15
          (zero_extend (m := 64) (BitVec.ofNat 8 args.sourceBytes[1].toNat)) (by simp)
        simpa [after, b1] using reg
      · have reg := seg.reg x13
          (zero_extend (m := 64) (BitVec.ofNat 8 args.sourceBytes[2].toNat)) (by simp)
        simpa [after, b2] using reg
      · have reg := seg.reg x14
          (zero_extend (m := 64) (BitVec.ofNat 8 args.sourceBytes[3].toNat)) (by simp)
        simpa [after, b3] using reg
    · rw [seg.memEq noMemory_empty]
      exact loaded

theorem proposed_readU32_3335_proved : Proposed_ssz_readU32_fi_1_3335_Contract :=
  readU32_3335Contract_implements

/-! ## Complete `fi:1:2ff8` wrapper -/

def sszReadU32Preserved2ff8 (register : Register) : Prop :=
  instructionPreserved register ∧ register ≠ x10 ∧ register ≠ x12 ∧
    register ≠ x13 ∧ register ≠ x14

def sszReadU32Bindings2ff8 (bytes : Array UInt8) (state : EndpointState) : Prop :=
  state.machine.regs.get? x10 = some (readU32MachineValue
    (sszReadU32Byte bytes 0).toNat (sszReadU32Byte bytes 1).toNat
    (sszReadU32Byte bytes 2).toNat (sszReadU32Byte bytes 3).toNat) ∧
  state.machine.regs.get? x12 = some 16

def Proposed_ssz_readU32_fi_1_2ff8_Contract : Prop :=
  ∃ stepBound : SszReadU32Args → Nat,
    (∀ args, stepBound args < level2ContractFuel) ∧
    (sszReadU32Contract 0x12734 2 sszReadU32SourceX18 sszReadU32Bindings2ff8
      sszReadU32Preserved2ff8 stepBound).Implements EndpointStep EndpointPc
      readU32_2ff8OwnPc readU32_2ff8ExitPc

private theorem readU32_2ff8OwnPc_not_observed {pc : BitVec 64}
    (inside : readU32_2ff8OwnPc pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  unfold readU32_2ff8OwnPc pcInList at inside
  unfold BareMetalHostTransitionPc at observed
  unfold readContextReturnPc writeContextReturnPc exitContextStorePc at observed
  simp at inside
  rcases observed with observed | observed | observed
  all_goals omega

private theorem preserved2ff8Disjoint :
    RegSet.Disjoint sszReadU32Preserved2ff8 readU32_2ff8Writes := by
  intro register preserved written
  rcases preserved with ⟨instruction, ne10, ne12, ne13, ne14⟩
  rcases written with bookkeeping | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register instruction.1 bookkeeping
  all_goals contradiction

/-- The complete production `fi:1:2ff8` wrapper satisfies the shared `readU32` contract. -/
theorem readU32_2ff8Contract_implements : Proposed_ssz_readU32_fi_1_2ff8_Contract := by
  refine ⟨fun _ => 11, by intro; simp [level2ContractFuel], ?_⟩
  intro args fromStep before entry
  rcases entry with ⟨atPc, base, size, sourceFits, bytesRep, pma, notMMIO, loaded, configured⟩
  have rep0 := bytesRep.uintRepAt 0 (by omega)
  have rep1 := bytesRep.uintRepAt 1 (by omega)
  have rep2 := bytesRep.uintRepAt 2 (by omega)
  have rep3 := bytesRep.uintRepAt 3 (by omega)
  obtain ⟨finalMachine, seg⟩ := readU32_2ff8Run fromStep args.sourceAddress
    args.sourceBytes[0].toNat args.sourceBytes[1].toNat args.sourceBytes[2].toNat
    args.sourceBytes[3].toNat before.machine configured atPc base
    (by simpa [Nat.add_assoc] using rep0) (by simpa [Nat.add_assoc] using rep1)
    (by simpa [Nat.add_assoc] using rep2) (by simpa [Nat.add_assoc] using rep3)
    pma notMMIO sourceFits loaded
  let after : EndpointState := { before with machine := finalMachine }
  have endTrace : ScopedTrace readU32_2ff8OwnPc readU32_2ff8ExitPc
      (fun _ _ _ _ _ => False) (fromStep + 11) 0 finalMachine finalMachine :=
    .exitAt (fromStep + 11) finalMachine 0x12760 seg.atPc (by
      unfold readU32_2ff8ExitPc pcInList
      native_decide)
  have machineTrace : ScopedTrace readU32_2ff8OwnPc readU32_2ff8ExitPc
      (fun _ _ _ _ _ => False) fromStep 11 before.machine finalMachine := by
    simpa using seg.confined 0 finalMachine endTrace
  have b0 : sszReadU32Byte args.sourceBytes 0 = args.sourceBytes[0] := by
    simp [sszReadU32Byte, size]
  have b1 : sszReadU32Byte args.sourceBytes 1 = args.sourceBytes[1] := by
    simp [sszReadU32Byte, size]
  have b2 : sszReadU32Byte args.sourceBytes 2 = args.sourceBytes[2] := by
    simp [sszReadU32Byte, size]
  have b3 : sszReadU32Byte args.sourceBytes 3 = args.sourceBytes[3] := by
    simp [sszReadU32Byte, size]
  refine ⟨11, after, sszReadU32Value args.sourceBytes, by omega,
    by simp [sszReadU32Contract], ?_, ?_, ?_, ?_⟩
  · simpa [after] using liftReadU32Trace before readU32_2ff8OwnPc_not_observed machineTrace
  · exact ⟨0x12760, seg.atPc, by unfold readU32_2ff8ExitPc pcInList; native_decide⟩
  · exact ⟨size, rfl⟩
  · refine ⟨rfl, ?_, seg.writes.agree preserved2ff8Disjoint, seg.retired, ?_,
      seg.memEq noMemory_empty, seg.aux, rfl, rfl, rfl, rfl⟩
    · constructor
      · have reg := seg.reg x10 (readU32MachineValue args.sourceBytes[0].toNat
          args.sourceBytes[1].toNat args.sourceBytes[2].toNat args.sourceBytes[3].toNat) (by simp)
        simpa [after, sszReadU32Bindings2ff8, b0, b1, b2, b3] using reg
      · have reg := seg.reg x12 16 (by simp)
        simpa [after] using reg
    · rw [seg.memEq noMemory_empty]
      exact loaded

theorem proposed_readU32_2ff8_proved : Proposed_ssz_readU32_fi_1_2ff8_Contract :=
  readU32_2ff8Contract_implements

end BinaryFv.Zesu.Staging
