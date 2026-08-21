import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.ProofProgress.OwnedPc
import BinaryFv.RiscV.Instruction.DecodeTactic
import BinaryFv.RiscV.Elfling.Seg

/-!
# Parent-owned `ssz.decode` steps

This module composes the instructions that belong to the selected `ssz.decode` instance, outside
its selected children. The first segment loads the allocator descriptor and stores both words in
the decoder frame.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.Binary BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

def sszDecodeAllocatorPrefixOwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x121ac, 0x121b0, 0x121b4, 0x121b8, 0x121bc, 0x121c0] pc

def sszDecodeAllocatorPrefixExitPc (pc : BitVec 64) : Prop :=
  pcInList [0x121c4, 0x12200] pc

def sszDecodeAllocatorPrefixWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x10 ∨ register = x12 ∨ register = x14

def sszDecodeAllocatorPrefixMemory (stackPointer : Nat) : Region := fun address =>
  byteRange (stackPointer + 0x4b8) 8 address ∨ byteRange (stackPointer + 0x4c0) 8 address

private theorem instructionPreserved_disjoint_sszDecodeAllocatorPrefixWrites :
    RegSet.Disjoint instructionPreserved sszDecodeAllocatorPrefixWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem sszDecodeAllocatorPrefixMemory_in_frame {args : DecodeInlineArgs} {address : Nat}
    (stackFits : 0xbb0 ≤ args.boundary.stackPointer)
    (inside : sszDecodeAllocatorPrefixMemory
      (args.boundary.stackPointer - 0xbb0) address) :
    args.boundary.stackPointer - 0xbb0 ≤ address ∧ address < args.boundary.stackPointer := by
  unfold sszDecodeAllocatorPrefixMemory byteRange at inside
  rcases inside with first | second <;> omega

private theorem sszDecodeAllocatorAccessOfSeg {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {before : EndpointState} {kv a n cur pc}
    (frame : DecodeInlineFrame args values before)
    (seg : Seg sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
      (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
      (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0)) kv a n
      before.machine cur pc) :
    DecodeBoundaryMachineAccess args.boundary cur :=
  frame.access.of_pma_regions_eq
    (seg.agree instructionPreserved_disjoint_sszDecodeAllocatorPrefixWrites) seg.retired
    (seg.get pma_regions (by simp [sszDecodeAllocatorPrefixWrites, stepBookkeeping]))

private theorem sszDecodeAllocatorCodeOfSeg {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {before : EndpointState} {kv a n cur pc}
    (frame : DecodeInlineFrame args values before)
    (seg : Seg sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
      (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
      (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0)) kv a n
      before.machine cur pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  intro address byte fileByte
  rw [seg.mem address (by
    intro inside
    have outside := frame.access.frameNotCode address
      (sszDecodeAllocatorPrefixMemory_in_frame frame.stackFits inside).1
      (sszDecodeAllocatorPrefixMemory_in_frame frame.stackFits inside).2
    rw [fileByte] at outside
    cases outside)]
  exact frame.code address byte fileByte

/-- Exact `0x121ac: ld a0,0(a1)`. -/
theorem sszDecodeLoadAllocatorStateStep (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (access : DecodeBoundaryMachineAccess args.boundary state)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (atPc : state.regs.get? PC = some 0x121ac)
    (allocatorAt : state.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)))
    (rep : UIntRep 8 state.mem (args.boundary.stackPointer + 0x10)
      args.boundary.allocatorStateAddress)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x121ac retired x10
        (BitVec.ofNat 64 args.boundary.allocatorStateAddress)) false := by
  apply configuredDwordLoadStep stepNo 0x121ac state 0 (.Regidx 11#5) (.Regidx 10#5)
    x10 (args.boundary.stackPointer + 0x10) 0 args.boundary.allocatorStateAddress
    (BitVec.ofNat 64 args.boundary.allocatorStateAddress) 0x03 0xb5 0x05 0x00
    access.configured atPc rep (access.callerLoad 0x10 8 (by omega))
    (access.callerNoMMIO 0x10 8 (by omega)) (by omega) (by omega) loaded
    (addressEq := by
      change BitVec.ofNat 64 (args.boundary.stackPointer + 0x10) +
        sign_extend (m := 64) (0 : BitVec 12) = _
      rw [show sign_extend (m := 64) (0 : BitVec 12) = 0 by native_decide]
      simp)
    (baseRun := by
      intro premise writes
      exact rX_x11_run premise _ ((writes.get x11 (by decide)).trans allocatorAt))
    (writeRun := by intro premise; exact wX_x10_run premise _)
    (decode := by configured_decode access.configured) (base := by rfl)

/-- Exact `0x121b0: ld a2,8(a1)`. -/
theorem sszDecodeLoadAllocatorVtableStep (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (access : DecodeBoundaryMachineAccess args.boundary state)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (atPc : state.regs.get? PC = some 0x121b0)
    (allocatorAt : state.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)))
    (rep : UIntRep 8 state.mem (args.boundary.stackPointer + 0x18)
      args.boundary.allocatorVtableAddress)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x121b0 retired x12
        (BitVec.ofNat 64 args.boundary.allocatorVtableAddress)) false := by
  apply configuredDwordLoadStep stepNo 0x121b0 state 8 (.Regidx 11#5) (.Regidx 12#5)
    x12 (args.boundary.stackPointer + 0x10) 8 args.boundary.allocatorVtableAddress
    (BitVec.ofNat 64 args.boundary.allocatorVtableAddress) 0x03 0xb6 0x85 0x00
    access.configured atPc rep (access.callerLoad 0x18 8 (by omega))
    (access.callerNoMMIO 0x18 8 (by omega)) (by omega) (by omega) loaded
    (addressEq := by
      change BitVec.ofNat 64 (args.boundary.stackPointer + 0x10) + 8#64 = _
      rw [← BitVec.ofNat_add])
    (baseRun := by
      intro premise writes
      exact rX_x11_run premise _ ((writes.get x11 (by decide)).trans allocatorAt))
    (writeRun := by intro premise; exact wX_x12_run premise _)
    (decode := by configured_decode access.configured) (base := by rfl)

/-- Exact `0x121b4: li a4,3`. -/
theorem sszDecodeLoadFieldCountStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x121b4)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x121b4 retired x14 3) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x121b4
  have execute : Runs (execute (.ITYPE (3, .Regidx 0#5, .Regidx 14#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x14 3 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 3 (.Regidx 0#5) (.Regidx 14#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 3 0 = 3#64 := by native_decide
    simpa only [resultEq] using execute_ITYPE_run premise _ 3 (.Regidx 0#5)
      (.Regidx 14#5) .ADDI 0 (rX_x0_run premise) (wX_x14_run premise _)
  exact configuredRegisterWriteStep stepNo 0x121b4 state x14 3
    (.ITYPE (3, .Regidx 0#5, .Regidx 14#5, .ADDI)) 0x13 0x07 0x30 0x00
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x121b8: sd a0,0x4b8(sp)`. -/
theorem sszDecodeStoreAllocatorStateStep (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (access : DecodeBoundaryMachineAccess args.boundary state)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (atPc : state.regs.get? PC = some 0x121b8)
    (stackAt : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (valueAt : state.regs.get? x10 =
      some (BitVec.ofNat 64 args.boundary.allocatorStateAddress))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x121b8)
          (args.boundary.stackPointer - 0xbb0 + 0x4b8)
          (BitVec.ofNat 64 args.boundary.allocatorStateAddress))
        0x121b8 retired) false := by
  apply configuredStackDwordStoreStep stepNo 0x121b8
    (args.boundary.stackPointer - 0xbb0) 0x4b8 state
    (BitVec.ofNat 64 args.boundary.allocatorStateAddress) 0x4b8 (.Regidx 10#5)
    0x23 0x3c 0xa1 0x4a access.configured atPc stackAt
    (access.frameStore 0x4b8 8 (by omega)) (access.frameNoMMIO 0x4b8 8 (by omega))
    (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) + 0x4b8#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨_, _, _, _, _⟩ := access.configured.storeDecodeContext
    decode_run
  · intro premise writes
    exact rX_x10_run premise _ ((writes.get x10 (by decide)).trans valueAt)

/-- Exact `0x121bc: sd a2,0x4c0(sp)`. -/
theorem sszDecodeStoreAllocatorVtableStep (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (access : DecodeBoundaryMachineAccess args.boundary state)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (atPc : state.regs.get? PC = some 0x121bc)
    (stackAt : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)))
    (valueAt : state.regs.get? x12 =
      some (BitVec.ofNat 64 args.boundary.allocatorVtableAddress))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x121bc)
          (args.boundary.stackPointer - 0xbb0 + 0x4c0)
          (BitVec.ofNat 64 args.boundary.allocatorVtableAddress))
        0x121bc retired) false := by
  apply configuredStackDwordStoreStep stepNo 0x121bc
    (args.boundary.stackPointer - 0xbb0) 0x4c0 state
    (BitVec.ofNat 64 args.boundary.allocatorVtableAddress) 0x4c0 (.Regidx 12#5)
    0x23 0x30 0xc1 0x4c access.configured atPc stackAt
    (access.frameStore 0x4c0 8 (by omega)) (access.frameNoMMIO 0x4c0 8 (by omega))
    (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0) + 0x4c0#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨_, _, _, _, _⟩ := access.configured.storeDecodeContext
    decode_run
  · intro premise writes
    exact rX_x12_run premise _ ((writes.get x12 (by decide)).trans valueAt)

/-- The unique five-instruction allocator prefix of `ssz.decode`. -/
theorem sszDecodeAllocatorPrefixSeg (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (frame : DecodeInlineFrame args values before)
    (atPc : before.machine.regs.get? PC = some 0x121ac)
    (allocatorAt : before.machine.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10))) :
    ∃ after,
      Seg sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
        (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
        (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0))
        [⟨x14, 3⟩, ⟨x12, BitVec.ofNat 64 args.boundary.allocatorVtableAddress⟩,
          ⟨x10, BitVec.ofNat 64 args.boundary.allocatorStateAddress⟩]
        fromStep 5 before.machine after 0x121c0 ∧
      UIntRep 8 after.mem (args.boundary.stackPointer - 0xbb0 + 0x4b8)
        args.boundary.allocatorStateAddress ∧
      UIntRep 8 after.mem (args.boundary.stackPointer - 0xbb0 + 0x4c0)
        args.boundary.allocatorVtableAddress := by
  have stackFits := frame.stackFits
  have stackUpper := frame.stackUpper
  obtain ⟨retired, retiredRead⟩ := frame.configured.retiredCounter
  have seg0 := Seg.nil sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
    (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
    (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0))
    fromStep ⟨retired, retiredRead⟩ atPc
  obtain ⟨s1, seg1⟩ := seg0.step
    (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
    (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList]) x10
    (BitVec.ofNat 64 args.boundary.allocatorStateAddress) 0x121b0
    (sszDecodeLoadAllocatorStateStep fromStep args before.machine frame.access
      frame.stackAligned frame.stackUpper atPc allocatorAt frame.allocatorState frame.code)
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inl rfl)) (by decide) (by decide) (by simp [RegsOutside])
  have vtable1 := frame.allocatorVtable.of_writesOnlyWithin seg1.mem (by
    intro index bound inside
    have inFrame := sszDecodeAllocatorPrefixMemory_in_frame frame.stackFits inside
    omega)
  obtain ⟨s2, seg2⟩ := seg1.step
    (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
    (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList]) x12
    (BitVec.ofNat 64 args.boundary.allocatorVtableAddress) 0x121b4
    (sszDecodeLoadAllocatorVtableStep (fromStep + 1) args s1
      (sszDecodeAllocatorAccessOfSeg frame seg1) frame.stackAligned frame.stackUpper seg1.atPc
      ((seg1.get x11 (by simp [sszDecodeAllocatorPrefixWrites])).trans allocatorAt) vtable1
      (sszDecodeAllocatorCodeOfSeg frame seg1))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨s3, seg3⟩ := seg2.step
    (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
    (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList]) x14 3 0x121b8
    (sszDecodeLoadFieldCountStep (fromStep + 2) s2
      (sszDecodeAllocatorAccessOfSeg frame seg2).configured seg2.atPc
      (sszDecodeAllocatorCodeOfSeg frame seg2))
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inr (Or.inr rfl))) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨retired3, s4, s4Eq, seg4⟩ := seg3.stepStoreWitness
    (width := 8) (args.boundary.stackPointer - 0xbb0 + 0x4b8)
    (BitVec.ofNat 64 args.boundary.allocatorStateAddress) 0x121bc
    (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
    (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList])
    (sszDecodeStoreAllocatorStateStep (fromStep + 3) args s3
      (sszDecodeAllocatorAccessOfSeg frame seg3) frame.stackAligned frame.stackUpper seg3.atPc
      ((seg3.get x2 (by simp [sszDecodeAllocatorPrefixWrites])).trans frame.atStack)
      (seg3.reg x10 (BitVec.ofNat 64 args.boundary.allocatorStateAddress) (by simp))
      (sszDecodeAllocatorCodeOfSeg frame seg3))
    (by native_decide)
    (by intro address lower upper; unfold sszDecodeAllocatorPrefixMemory byteRange; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have storedState : UIntRep 8 s4.mem
      (args.boundary.stackPointer - 0xbb0 + 0x4b8)
      args.boundary.allocatorStateAddress := by
    rw [s4Eq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement s3) 0x121b8)
        (args.boundary.stackPointer - 0xbb0 + 0x4b8)
        args.boundary.allocatorStateAddress frame.allocatorState.1 (by omega)
  obtain ⟨retired4, s5, s5Eq, seg5⟩ := seg4.stepStoreWitness
    (width := 8) (args.boundary.stackPointer - 0xbb0 + 0x4c0)
    (BitVec.ofNat 64 args.boundary.allocatorVtableAddress) 0x121c0
    (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
    (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList])
    (sszDecodeStoreAllocatorVtableStep (fromStep + 4) args s4
      (sszDecodeAllocatorAccessOfSeg frame seg4) frame.stackAligned frame.stackUpper seg4.atPc
      ((seg4.get x2 (by simp [sszDecodeAllocatorPrefixWrites])).trans frame.atStack)
      (seg4.reg x12 (BitVec.ofNat 64 args.boundary.allocatorVtableAddress) (by simp))
      (sszDecodeAllocatorCodeOfSeg frame seg4))
    (by native_decide)
    (by intro address lower upper; unfold sszDecodeAllocatorPrefixMemory byteRange; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have storedState5 : UIntRep 8 s5.mem
      (args.boundary.stackPointer - 0xbb0 + 0x4b8)
      args.boundary.allocatorStateAddress := by
    refine ⟨storedState.1, storedState.2.1, ?_⟩
    intro index bound
    rw [s5Eq]
    simp only [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]
    rw [afterWriteBytes_mem_get?_of_outside]
    · simpa [coreStoreNextState, tryStepStoreAfterIncrement,
        tryStepControlFlowAfterIncrement] using storedState.2.2 index bound
    · intro writtenIndex
      omega
  have storedVtable : UIntRep 8 s5.mem
      (args.boundary.stackPointer - 0xbb0 + 0x4c0)
      args.boundary.allocatorVtableAddress := by
    rw [s5Eq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement s4) 0x121bc)
        (args.boundary.stackPointer - 0xbb0 + 0x4c0)
        args.boundary.allocatorVtableAddress frame.allocatorVtable.1 (by omega)
  exact ⟨s5, by simpa only [Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using seg5,
    storedState5, storedVtable⟩

private theorem sszDecodeFieldCountBgeuRun (state : State) (inputSize : Nat)
    (fieldCountAt : state.regs.get? x14 = some 3)
    (inputSizeAt : state.regs.get? x13 = some (BitVec.ofNat 64 inputSize)) :
    Runs (bTypeTaken (.Regidx 13#5) (.Regidx 14#5) .BGEU) state state
      (zopz0zKzJ_u 3 (BitVec.ofNat 64 inputSize)) := by
  unfold bTypeTaken
  exact Runs.bind (rX_x14_run state 3 fieldCountAt)
    (Runs.bind (rX_x13_run state (BitVec.ofNat 64 inputSize) inputSizeAt) rfl)

/-- The fall-through branch implies that the four-byte schema word exists. -/
theorem sszDecodeInputLengthAtLeastFour (inputSize : Nat)
    (fits : inputSize < 2 ^ 64)
    (comparison : zopz0zKzJ_u 3 (BitVec.ofNat 64 inputSize) = false) :
    4 ≤ inputSize := by
  simp only [zopz0zKzJ_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat] at comparison
  rw [Nat.mod_eq_of_lt fits] at comparison
  simp at comparison
  omega

/-- Exact taken or not-taken `0x121c0: bgeu a4,a3,0x12200`. -/
theorem sszDecodeFieldCountBranchStep (stepNo inputSize : Nat) (args : DecodeInlineArgs)
    (state : State)
    (access : DecodeBoundaryMachineAccess args.boundary state)
    (atPc : state.regs.get? PC = some 0x121c0)
    (fieldCountAt : state.regs.get? x14 = some 3)
    (inputSizeAt : state.regs.get? x13 = some (BitVec.ofNat 64 inputSize))
    (comparison : zopz0zKzJ_u 3 (BitVec.ofNat 64 inputSize) = short)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if short then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x121c0 0x12200)
          0x12200 retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x121c0)
          0x121c4 retired) false := by
  cases short
  · apply configuredBranchNotTakenStep stepNo 0x121c0 state 0x40 (.Regidx 13#5)
      (.Regidx 14#5) .BGEU 0x63 0x70 0xd7 0x04 access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using sszDecodeFieldCountBgeuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x121c0)
        inputSize
        ((stepPremiseState_writes state 0x121c0).get x14 (by decide) |>.trans fieldCountAt)
        ((stepPremiseState_writes state 0x121c0).get x13 (by decide) |>.trans inputSizeAt)
  · apply configuredBranchTakenStep stepNo 0x121c0 0x12200 state 0x40 (.Regidx 13#5)
      (.Regidx 14#5) .BGEU 0x63 0x70 0xd7 0x04 access.configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode access.configured
    · simpa only [comparison] using sszDecodeFieldCountBgeuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x121c0)
        inputSize
        ((stepPremiseState_writes state 0x121c0).get x14 (by decide) |>.trans fieldCountAt)
        ((stepPremiseState_writes state 0x121c0).get x13 (by decide) |>.trans inputSizeAt)
    all_goals native_decide

/-- The allocator prefix and its first exact branch route. -/
theorem sszDecodeAllocatorBranchSeg (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (frame : DecodeInlineFrame args values before)
    (atPc : before.machine.regs.get? PC = some 0x121ac)
    (allocatorAt : before.machine.regs.get? x11 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x10)))
    (inputSizeAt : before.machine.regs.get? x13 =
      some (BitVec.ofNat 64 args.boundary.input.size))
    (comparison : zopz0zKzJ_u 3 (BitVec.ofNat 64 args.boundary.input.size) = short) :
    ∃ after,
      Seg sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
        (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
        (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0))
        [⟨x14, 3⟩, ⟨x12, BitVec.ofNat 64 args.boundary.allocatorVtableAddress⟩,
          ⟨x10, BitVec.ofNat 64 args.boundary.allocatorStateAddress⟩]
        fromStep 6 before.machine after (if short then 0x12200 else 0x121c4) ∧
      UIntRep 8 after.mem (args.boundary.stackPointer - 0xbb0 + 0x4b8)
        args.boundary.allocatorStateAddress ∧
      UIntRep 8 after.mem (args.boundary.stackPointer - 0xbb0 + 0x4c0)
        args.boundary.allocatorVtableAddress := by
  obtain ⟨branched, prefixSeg, storedState, storedVtable⟩ :=
    sszDecodeAllocatorPrefixSeg fromStep args values before frame atPc allocatorAt
  have currentInputSize : branched.regs.get? x13 =
      some (BitVec.ofNat 64 args.boundary.input.size) :=
    (prefixSeg.get x13 (by simp [sszDecodeAllocatorPrefixWrites])).trans inputSizeAt
  cases short
  · obtain ⟨retired, after, afterEq, full⟩ := prefixSeg.stepFallThroughWitness 0x121c4
      (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
      (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList])
      (sszDecodeFieldCountBranchStep (fromStep + 5) args.boundary.input.size args branched
        (sszDecodeAllocatorAccessOfSeg frame prefixSeg) prefixSeg.atPc
        (prefixSeg.reg x14 3 (by simp)) currentInputSize comparison
        (sszDecodeAllocatorCodeOfSeg frame prefixSeg))
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    refine ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full,
      ?_, ?_⟩
    · rw [afterEq]
      exact storedState.of_mem_eq (fallThroughRetirement_mem branched 0x121c0 0x121c4 retired)
    · rw [afterEq]
      exact storedVtable.of_mem_eq
        (fallThroughRetirement_mem branched 0x121c0 0x121c4 retired)
  · obtain ⟨retired, after, afterEq, full⟩ := prefixSeg.stepJumpWitness 0x12200
      (by owned_pc [sszDecodeAllocatorPrefixOwnPc, pcInList])
      (by owned_pc [sszDecodeAllocatorPrefixExitPc, pcInList])
      (sszDecodeFieldCountBranchStep (fromStep + 5) args.boundary.input.size args branched
        (sszDecodeAllocatorAccessOfSeg frame prefixSeg) prefixSeg.atPc
        (prefixSeg.reg x14 3 (by simp)) currentInputSize comparison
        (sszDecodeAllocatorCodeOfSeg frame prefixSeg))
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    refine ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full,
      ?_, ?_⟩
    · rw [afterEq]
      exact storedState.of_mem_eq (jumpRetirement_mem branched 0x121c0 0x12200 retired)
    · rw [afterEq]
      exact storedVtable.of_mem_eq (jumpRetirement_mem branched 0x121c0 0x12200 retired)

/-- Typed entry facts for the first four-byte read after the allocator prefix. -/
structure SszDecodeSchemaWordEntry (args : DecodeInlineArgs) (state : State) : Prop where
  atPc : state.regs.get? PC = some 0x121c4
  sourceAt : state.regs.get? x18 = some (BitVec.ofNat 64 args.boundary.inputAddress)
  sizeAt : state.regs.get? x13 = some (BitVec.ofNat 64 args.boundary.input.size)
  input : BytesRep state.mem args.boundary.inputAddress args.boundary.input
  inputAtLeastFour : 4 ≤ args.boundary.input.size
  access : DecodeBoundaryMachineAccess args.boundary state
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem

/-- The fall-through route produces the exact typed entry for `mem.readInt`. -/
theorem sszDecodeAllocatorFallThroughHandoff (fromStep : Nat) (args : DecodeInlineArgs)
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
    ∃ after,
      Seg sszDecodeAllocatorPrefixOwnPc sszDecodeAllocatorPrefixExitPc
        (fun _ _ _ _ _ => False) sszDecodeAllocatorPrefixWrites
        (sszDecodeAllocatorPrefixMemory (args.boundary.stackPointer - 0xbb0))
        [⟨x14, 3⟩, ⟨x12, BitVec.ofNat 64 args.boundary.allocatorVtableAddress⟩,
          ⟨x10, BitVec.ofNat 64 args.boundary.allocatorStateAddress⟩]
        fromStep 6 before.machine after 0x121c4 ∧
      SszDecodeSchemaWordEntry args after := by
  obtain ⟨after, seg, _storedState, _storedVtable⟩ :=
    sszDecodeAllocatorBranchSeg fromStep args values before frame atPc allocatorAt inputSizeAt
      comparison
  have inputAfter := frame.input.of_writesOnlyWithin seg.mem (by
    intro index bound inside
    have inFrame := sszDecodeAllocatorPrefixMemory_in_frame frame.stackFits inside
    rcases frame.inputSeparated with above | below <;> omega)
  refine ⟨after, seg, seg.atPc, ?_, ?_, inputAfter,
    sszDecodeInputLengthAtLeastFour args.boundary.input.size frame.inputSize.1 comparison,
    sszDecodeAllocatorAccessOfSeg frame seg, sszDecodeAllocatorCodeOfSeg frame seg⟩
  · exact (seg.get x18 (by simp [sszDecodeAllocatorPrefixWrites])).trans sourceAt
  · exact (seg.get x13 (by simp [sszDecodeAllocatorPrefixWrites])).trans inputSizeAt

def sszDecodeLengthMinimumOwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x12204, 0x12208] pc

def sszDecodeLengthMinimumExitPc (pc : BitVec 64) : Prop :=
  pcInList [0x1220c, 0x1225c] pc

def sszDecodeLengthMinimumWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x12

private theorem instructionPreserved_disjoint_sszDecodeLengthMinimumWrites :
    RegSet.Disjoint instructionPreserved sszDecodeLengthMinimumWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  · simp [instructionPreserved, platformPreserved] at preserved

/-- Exact `0x12204: li a2,2`. -/
theorem sszDecodeLengthMinimumStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x12204)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12204 retired x12 2) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12204
  have execute : Runs (execute (.ITYPE (2, .Regidx 0#5, .Regidx 12#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x12 2 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 2 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 2 0 = 2#64 := by native_decide
    simpa only [resultEq] using execute_ITYPE_run premise _ 2 (.Regidx 0#5)
      (.Regidx 12#5) .ADDI 0 (rX_x0_run premise) (wX_x12_run premise _)
  exact configuredRegisterWriteStep stepNo 0x12204 state x12 2
    (.ITYPE (2, .Regidx 0#5, .Regidx 12#5, .ADDI)) 0x13 0x06 0x20 0x00
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

private theorem sszDecodeLengthMinimumBltuRun (state : State) (length : BitVec 64)
    (lengthAt : state.regs.get? x10 = some length)
    (minimumAt : state.regs.get? x12 = some 2) :
    Runs (bTypeTaken (.Regidx 12#5) (.Regidx 10#5) .BLTU) state state
      (zopz0zI_u length 2) := by
  unfold bTypeTaken
  exact Runs.bind (rX_x10_run state length lengthAt)
    (Runs.bind (rX_x12_run state 2 minimumAt) rfl)

/-- Exact taken or not-taken `0x12208: bltu a0,a2,0x1225c`. -/
theorem sszDecodeLengthMinimumBranchStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x12208)
    (lengthAt : state.regs.get? x10 = some length)
    (minimumAt : state.regs.get? x12 = some 2)
    (comparison : zopz0zI_u length 2 = short)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (if short then
        tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x12208 0x1225c)
          0x1225c retired
      else
        tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12208)
          0x1220c retired) false := by
  cases short
  · apply configuredBranchNotTakenStep stepNo 0x12208 state 0x54 (.Regidx 12#5)
      (.Regidx 10#5) .BLTU 0x63 0x6a 0xc5 0x04 configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode configured
    · simpa only [comparison] using sszDecodeLengthMinimumBltuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12208)
        length
        ((stepPremiseState_writes state 0x12208).get x10 (by decide) |>.trans lengthAt)
        ((stepPremiseState_writes state 0x12208).get x12 (by decide) |>.trans minimumAt)
  · apply configuredBranchTakenStep stepNo 0x12208 0x1225c state 0x54 (.Regidx 12#5)
      (.Regidx 10#5) .BLTU 0x63 0x6a 0xc5 0x04 configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode configured
    · simpa only [comparison] using sszDecodeLengthMinimumBltuRun
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12208)
        length
        ((stepPremiseState_writes state 0x12208).get x10 (by decide) |>.trans lengthAt)
        ((stepPremiseState_writes state 0x12208).get x12 (by decide) |>.trans minimumAt)
    all_goals native_decide

/-- Both length routes use this one `li; bltu` composition. -/
theorem sszDecodeLengthMinimumBranchSeg (fromStep : Nat) (before : State)
    (configured : ConfiguredMachinePre EndpointMachinePc before)
    (atPc : before.regs.get? PC = some 0x12204)
    (lengthAt : before.regs.get? x10 = some length)
    (comparison : zopz0zI_u length 2 = short)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem) :
    ∃ after,
      Seg sszDecodeLengthMinimumOwnPc sszDecodeLengthMinimumExitPc
        (fun _ _ _ _ _ => False) sszDecodeLengthMinimumWrites noMemory
        [⟨x12, 2⟩] fromStep 2 before after (if short then 0x1225c else 0x1220c) := by
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  have seg0 := Seg.nil sszDecodeLengthMinimumOwnPc sszDecodeLengthMinimumExitPc
    (fun _ _ _ _ _ => False) sszDecodeLengthMinimumWrites noMemory
    fromStep ⟨retired, retiredRead⟩ atPc
  obtain ⟨middle, seg1⟩ := seg0.step
    (by owned_pc [sszDecodeLengthMinimumOwnPc, pcInList])
    (by owned_pc [sszDecodeLengthMinimumExitPc, pcInList]) x12 2 0x12208
    (sszDecodeLengthMinimumStep fromStep before configured atPc loaded)
    (by native_decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr rfl) (by decide) (by decide) (by simp [RegsOutside])
  have configured1 := configured.mono
    (seg1.agree instructionPreserved_disjoint_sszDecodeLengthMinimumWrites) seg1.retired
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully middle.mem := by
    rw [seg1.memEq noMemory_empty]
    exact loaded
  cases short
  · obtain ⟨_, after, _, full⟩ := seg1.stepFallThroughWitness 0x1220c
      (by owned_pc [sszDecodeLengthMinimumOwnPc, pcInList])
      (by owned_pc [sszDecodeLengthMinimumExitPc, pcInList])
      (sszDecodeLengthMinimumBranchStep (fromStep + 1) middle configured1 seg1.atPc
        ((seg1.get x10 (by simp [sszDecodeLengthMinimumWrites])).trans lengthAt)
        (seg1.reg x12 2 (by simp)) comparison loaded1)
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full⟩
  · obtain ⟨_, after, _, full⟩ := seg1.stepJumpWitness 0x1225c
      (by owned_pc [sszDecodeLengthMinimumOwnPc, pcInList])
      (by owned_pc [sszDecodeLengthMinimumExitPc, pcInList])
      (sszDecodeLengthMinimumBranchStep (fromStep + 1) middle configured1 seg1.atPc
        ((seg1.get x10 (by simp [sszDecodeLengthMinimumWrites])).trans lengthAt)
        (seg1.reg x12 2 (by simp)) comparison loaded1)
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [RegsOutside, stepBookkeeping])
    exact ⟨after, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full⟩

end BinaryFv.Zesu.MachineExecution
