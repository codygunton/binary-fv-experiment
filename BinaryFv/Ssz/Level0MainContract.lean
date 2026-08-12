import BinaryFv.Ssz.Level0MainSteps
import BinaryFv.Ssz.Level1Contracts
import BinaryFv.RiscV.Step.RegisterWrite

/-!
# Level 0 endpoint contract

This file composes the 24 instructions owned by `main` with the six immediate Level 1 contracts.
The first declarations establish the common execution region and the frame transports used after a
returning opaque call.
-/

namespace BinaryFv.Ssz

open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.RiscV

/-- Every instruction selected at Level 0: parent-owned glue or one of its six opaque callees. -/
def MainExecutionPc (pc : BitVec 64) : Prop :=
  mainGluePcs pc ∨
  pcInRanges Generated.readInputExecutionPcRanges pc ∨
  pcInRanges Generated.allocatorGetExecutionPcRanges pc ∨
  DecodeExecutionPc pc ∨
  pcInRanges Generated.writeSuccessExecutionPcRanges pc ∨
  pcInRanges Generated.writeFailureExecutionPcRanges pc ∨
  pcInRanges Generated.zkvmExitExecutionPcRanges pc

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

set_option genInjectivity false in
/-- Concrete Linux/RV64 entry state for the exported endpoint. The two PMA/MMIO clauses are the
actual stack stores at offsets `0x378` and `8`; no generated instruction run is assumed here. -/
structure MainEntry (args : MainArgs) (state : EndpointState) : Prop where
  stdin : state.stdin = args.input
  stdinCursor : state.stdinCursor = 0
  stdout : state.stdout = #[]
  exitCode : state.exitCode = none
  inputBound : args.input.size ≤ 64 * 1024 * 1024
  stackFits : args.stackPointer + 0x380 < 2 ^ 64
  stackAligned : args.stackPointer % 16 = 0
  returnAddressFits : args.returnAddress < 2 ^ 64
  atPc : state.machine.regs.get? PC = some (BitVec.ofNat 64 Generated.mainEntry)
  stackRegister :
    state.machine.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer + 0x380))
  returnRegister : state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress)
  configured : ConfiguredMachinePre mainGluePcs state.machine
  code : Generated.programImage.fileBytesLoadedFaithfully state.machine.mem
  savedReturnPma :
    StorePmaAllows state.machine (BitVec.ofNat 64 (args.stackPointer + 0x378)) 8
  inputSizePma : StorePmaAllows state.machine (BitVec.ofNat 64 (args.stackPointer + 8)) 8
  savedReturnNoMMIO :
    StoreMMIOAddressExcluded (BitVec.ofNat 64 (args.stackPointer + 0x378)) 8
  inputSizeNoMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (args.stackPointer + 8)) 8
  stackNotFileBacked : ∀ address, args.stackPointer ≤ address →
    address < args.stackPointer + 0x380 → Generated.programImage.readFileByte? address = none

def MainExit (args : MainArgs) (outcome : MainOutcome)
    (_before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 Generated.zkvmExitTerminalPc) ∧
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
    MainExecutionPc (pcInList [Generated.zkvmExitTerminalPc])

/-- The parent contract derived by resolving Level 0 against its six selected children. -/
abbrev ExportedContractAssumptions : Prop := ComplianceModulo knownBugs

private theorem instructionPreserved_abiCalleePreserved (register : Register)
    (preserved : instructionPreserved register) : abiCalleePreserved register := by
  rcases preserved.1 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  all_goals simp [abiCalleePreserved]

/-- A reviewed returning ABI contract restores the configured-machine premise needed by the next
Level 0 instruction. `minstret` is retained by presence rather than by false value equality. -/
theorem ConfiguredMachinePre.of_endpointCallFrame {before after : EndpointState}
    (configured : ConfiguredMachinePre mainGluePcs before.machine)
    (frame : EndpointCallFrame before after) :
    ConfiguredMachinePre mainGluePcs after.machine :=
  configured.mono
    (frame.1.weaken instructionPreserved_abiCalleePreserved)
    frame.2.1

private theorem instructionPreserved_disjoint_bookkeeping :
    RegSet.Disjoint instructionPreserved stepBookkeeping :=
  platformPreserved_disjoint.weaken (fun _ preserved => preserved.1)

/-- Transport through the exact post-state of a Level 0 register-writing instruction. -/
theorem ConfiguredMachinePre.afterRegisterWrite {state : MachineState} (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination)
    (configured : ConfiguredMachinePre mainGluePcs state)
    (destinationNotPreserved : ¬instructionPreserved destination) :
    ConfiguredMachinePre mainGluePcs
      (BinaryFv.RiscV.afterRegisterWrite state pc retired destination value) :=
  configured.mono
    ((afterRegisterWrite_writes state pc retired destination value).agree
      (instructionPreserved_disjoint_bookkeeping.union
        (RegSet.Disjoint.only destinationNotPreserved)))
    (afterRegisterWrite_retired_present state pc retired destination value)

/-- Transport through the exact post-state of `main`'s stack allocation. -/
theorem ConfiguredMachinePre.afterStackAddi {state : MachineState} (pc : BitVec 64)
    (immediate : BitVec 12) (stackValue retired : BitVec 64)
    (configured : ConfiguredMachinePre mainGluePcs state) :
    ConfiguredMachinePre mainGluePcs
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
    (pc retired : BitVec 64) (configured : ConfiguredMachinePre mainGluePcs state)
    (writeRegs : afterWrite.regs =
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs) :
    ConfiguredMachinePre mainGluePcs (tryStepStoreAfterRetired afterWrite pc retired) := by
  apply configured.mono
  · exact (main_store_retirement_writes pc retired writeRegs).agree
      instructionPreserved_disjoint_bookkeeping
  · simpa [tryStepStoreAfterRetired] using
      tryStepControlFlowAfterRetired_retired_present afterWrite (Sail.BitVec.addInt pc 4) retired

/-- One exact non-syscall Sail instruction, lifted into and confined by the complete Level 0 region. -/
theorem main_confined_sail_step (stepNo : Nat) (before : EndpointState) (after : MachineState)
    (pc : BitVec 64) (atPc : EndpointPc before = some pc) (inside : mainGluePcs pc)
    (notSyscall : ¬ LinuxSyscallPc pc) (step : MachineStep stepNo before.machine after) :
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
    ConfiguredMachinePre mainGluePcs after.machine ∧
    Generated.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    EndpointPc after = some 0x14cb4 ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
    StorePmaAllows after.machine (BitVec.ofNat 64 (args.stackPointer + 0x378)) 8 ∧
    StorePmaAllows after.machine (BitVec.ofNat 64 (args.stackPointer + 8)) 8 ∧
    after.stdin = args.input ∧ after.stdinCursor = 0 ∧ after.stdout = #[] ∧
    after.exitCode = none

/-- Execute the first exact Level 0 instruction and bind the resulting stack base. -/
theorem main_stack_allocate (args : MainArgs) (fromStep : Nat) (before : EndpointState)
    (entry : MainEntry args before) : MainStackAllocatedHandoff args fromStep before := by
  obtain ⟨retired, run⟩ := main_stack_allocate_step fromStep before.machine
    (BitVec.ofNat 64 (args.stackPointer + 0x380)) entry.configured entry.atPc
    entry.stackRegister entry.code
  let afterMachine := tryStepStackAddiAfterRetired before.machine
    (BitVec.ofNat 64 Generated.mainEntry) (BitVec.ofNat 12 0xc80)
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
        (BitVec.ofNat 64 Generated.mainEntry) (by simpa [EndpointPc] using entry.atPc)
        (by refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
        (by unfold LinuxSyscallPc; native_decide) machineStep,
      ConfiguredMachinePre.afterStackAddi _ _ _ _ entry.configured,
      (by simpa [after, afterMachine, tryStepStackAddiAfterRetired_mem] using entry.code),
      (by
        simp [after, afterMachine, EndpointPc, MachinePc, tryStepStackAddiAfterRetired,
          tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState,
          stackAddiNextState, tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert,
          Generated.mainEntry]
        native_decide),
      (by
        simpa [after, afterMachine, stackResult] using
          tryStepStackAddiAfterRetired_stackPointer before.machine
            (BitVec.ofNat 64 Generated.mainEntry) (BitVec.ofNat 12 0xc80)
            (BitVec.ofNat 64 (args.stackPointer + 0x380)) retired),
      (by
        calc
          after.machine.regs.get? x1 = before.machine.regs.get? x1 :=
            (stackAddiRetirement_writes before.machine
              (BitVec.ofNat 64 Generated.mainEntry) (BitVec.ofNat 12 0xc80)
              (BitVec.ofNat 64 (args.stackPointer + 0x380)) retired).get x1 (by decide)
          _ = some (BitVec.ofNat 64 args.returnAddress) := entry.returnRegister),
      (by
        apply storePmaAllows_of_agree
          ((stackAddiRetirement_writes before.machine
            (BitVec.ofNat 64 Generated.mainEntry) (BitVec.ofNat 12 0xc80)
            (BitVec.ofNat 64 (args.stackPointer + 0x380)) retired).agree
              (platformPreserved_disjoint.union
                (RegSet.Disjoint.only (by simp [platformPreserved]))))
        exact entry.savedReturnPma),
      (by
        apply storePmaAllows_of_agree
          ((stackAddiRetirement_writes before.machine
            (BitVec.ofNat 64 Generated.mainEntry) (BitVec.ofNat 12 0xc80)
            (BitVec.ofNat 64 (args.stackPointer + 0x380)) retired).agree
              (platformPreserved_disjoint.union
                (RegSet.Disjoint.only (by simp [platformPreserved]))))
        exact entry.inputSizePma),
      (by simpa [after] using entry.stdin), (by simpa [after] using entry.stdinCursor),
      (by simpa [after] using entry.stdout), (by simpa [after] using entry.exitCode)⟩

/-- Exact two-step handoff after `main` saves its incoming return address. -/
def MainReturnSavedHandoff (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ after : EndpointState,
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep 2 before after ∧
    ConfiguredMachinePre mainGluePcs after.machine ∧
    Generated.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    EndpointPc after = some 0x14cb8 ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
    StorePmaAllows after.machine (BitVec.ofNat 64 (args.stackPointer + 8)) 8 ∧
    after.stdin = args.input ∧ after.stdinCursor = 0 ∧ after.stdout = #[] ∧
    after.exitCode = none

/-- Execute the exact `sd ra,888(sp)` and retain the remaining stack-store permission. -/
theorem main_save_return_address (args : MainArgs) (fromStep : Nat) (before : EndpointState)
    (entry : MainEntry args before) : MainReturnSavedHandoff args fromStep before := by
  obtain ⟨stackState, stackTrace, configured, code, atPc, stackRead, returnRead,
      savedReturnPma, inputSizePma, stdin, stdinCursor, stdout, exitCode⟩ :=
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
  let afterWrite := afterWriteBytes (width := 8) premise
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
      savedReturnPma entry.savedReturnNoMMIO
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
  have codeWrite : Generated.programImage.fileBytesLoadedFaithfully afterWrite.mem := by
    apply fileBytesLoadedFaithfully_afterWriteBytes Generated.programImage premise
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
  refine ⟨after, stackTrace.append (main_confined_sail_step (fromStep + 1) stackState afterMachine
      0x14cb4 atPc (by refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
      (by unfold LinuxSyscallPc; native_decide) run),
    ConfiguredMachinePre.afterStore 0x14cb4 retired configured writeRegs,
    (by simpa [after, afterMachine, tryStepStoreAfterRetired, tryStepStoreAfterTick] using codeWrite),
    (by simp [after, afterMachine, EndpointPc, MachinePc, tryStepStoreAfterRetired,
      tryStepStoreAfterTick, Std.ExtDHashMap.get?_insert]; native_decide),
    (writes.get x2 (by decide)).trans stackRead,
    (writes.get x1 (by decide)).trans returnRead,
    storePmaAllows_of_agree platformAgree inputSizePma,
    (by simpa [after] using stdin), (by simpa [after] using stdinCursor),
    (by simpa [after] using stdout), (by simpa [after] using exitCode)⟩

/-- Exact three-step handoff after both Level 0 stack stores. -/
def MainFrameInitializedHandoff (args : MainArgs) (fromStep : Nat)
    (before : EndpointState) : Prop :=
  ∃ after : EndpointState,
    ConfinedTrace EndpointStep EndpointPc MainExecutionPc fromStep 3 before after ∧
    ConfiguredMachinePre mainGluePcs after.machine ∧
    Generated.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
    EndpointPc after = some 0x14cbc ∧
    after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    after.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) ∧
    after.stdin = args.input ∧ after.stdinCursor = 0 ∧ after.stdout = #[] ∧
    after.exitCode = none

/-- Execute `sd zero,8(sp)` and complete the concrete Level 0 frame prefix. -/
theorem main_initialize_frame (args : MainArgs) (fromStep : Nat) (before : EndpointState)
    (entry : MainEntry args before) : MainFrameInitializedHandoff args fromStep before := by
  obtain ⟨savedState, savedTrace, configured, code, atPc, stackRead, returnRead,
      inputSizePma, stdin, stdinCursor, stdout, exitCode⟩ :=
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
  let afterWrite := afterWriteBytes (width := 8) premise
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
      inputSizePma entry.inputSizeNoMMIO
  obtain ⟨retired, run⟩ := main_clear_input_slot_step (fromStep + 2) savedState.machine
    afterWrite configured (by simpa [EndpointPc] using atPc) code access
  let afterMachine := tryStepStoreAfterRetired afterWrite 0x14cb8 retired
  let after : EndpointState := { savedState with machine := afterMachine }
  have writeRegs : afterWrite.regs =
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement savedState.machine) 0x14cb8).regs :=
    afterWriteBytes_regs premise _ _
  have writes := main_store_retirement_writes 0x14cb8 retired writeRegs
  have codeWrite : Generated.programImage.fileBytesLoadedFaithfully afterWrite.mem := by
    apply fileBytesLoadedFaithfully_afterWriteBytes Generated.programImage premise
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
  refine ⟨after, savedTrace.append (main_confined_sail_step (fromStep + 2) savedState afterMachine
      0x14cb8 atPc (by refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
      (by unfold LinuxSyscallPc; native_decide) run),
    ConfiguredMachinePre.afterStore 0x14cb8 retired configured writeRegs,
    (by simpa [after, afterMachine, tryStepStoreAfterRetired, tryStepStoreAfterTick] using codeWrite),
    (by simp [after, afterMachine, EndpointPc, MachinePc, tryStepStoreAfterRetired,
      tryStepStoreAfterTick, Std.ExtDHashMap.get?_insert]; native_decide),
    (writes.get x2 (by decide)).trans stackRead,
    (writes.get x1 (by decide)).trans returnRead,
    (by simpa [after] using stdin), (by simpa [after] using stdinCursor),
    (by simpa [after] using stdout), (by simpa [after] using exitCode)⟩

end BinaryFv.Ssz
