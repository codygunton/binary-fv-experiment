import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.DecodedValue.Representation

/-!
# Optional-address copy steps

These wrappers bind the six production instructions that copy one 20-byte address from the caller
stack window to the encoder scratch window. The shared staging proof composes these wrappers with
`Seg`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open BinaryFv.Zesu
open PreSail LeanRV64DExecutable.Functions Register

private theorem optionalAddressPresenceCondition (state : State) (value : BitVec 64)
    (valueAt : state.regs.get? x10 = some value) :
    Runs (bTypeTaken (.Regidx 0#5) (.Regidx 10#5) .BEQ) state state (value == 0) := by
  unfold bTypeTaken
  refine Runs.bind (rX_x10_run state value valueAt) ?_
  refine Runs.bind (rX_x0_run state) ?_
  rfl

/-- Execute the optional-address presence branch on either reviewed semantic route. -/
theorem optionalAddressPresenceBranchStep (stepNo : Nat) (state : State)
    (present : Bool) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15158)
    (presenceAt : state.regs.get? x10 = some (if present then 1 else 0))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    if present then
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepControlFlowAfterRetired
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15158)
          0x1515c retired) false
    else
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepControlFlowAfterRetired
          (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x15158 0x15194)
          0x15194 retired) false := by
  cases present
  · simp only [Bool.false_eq_true, ↓reduceIte] at presenceAt ⊢
    apply configuredBranchTakenStep stepNo 0x15158 0x15194 state 0x03c (.Regidx 0#5)
      (.Regidx 10#5) .BEQ 0x63 0x0e 0x05 0x02 configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode configured
    · simpa using optionalAddressPresenceCondition
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15158) 0
        ((stepPremiseState_writes state 0x15158).get x10 (by decide) |>.trans presenceAt)
    all_goals native_decide
  · simp only [↓reduceIte] at presenceAt ⊢
    apply configuredBranchNotTakenStep stepNo 0x15158 state 0x03c (.Regidx 0#5)
      (.Regidx 10#5) .BEQ 0x63 0x0e 0x05 0x02 configured atPc loaded
      (site := by native_decide) (base := by rfl)
    · configured_decode configured
    · simpa using optionalAddressPresenceCondition
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15158) 1
        ((stepPremiseState_writes state 0x15158).get x10 (by decide) |>.trans presenceAt)

/-- Execute `li a0, 1` after the exact 20-byte copy. -/
theorem optionalAddressPresentTagStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15174)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15174 retired x10 1) false := by
  exact configuredITypeX10Step stepNo 0x15174 state 1 (.Regidx 0#5) .ADDI 0 1
    0x13 0x05 0x10 0x00 configured atPc loaded (by native_decide)
    (by intro premise _; exact rX_x0_run premise)
    (by intro premise; exact wX_x10_run premise 1)
    (by configured_decode configured) (base := by rfl) (site := by native_decide)

/-- Execute the exact present-route jump to the shared optional-address exit. -/
theorem optionalAddressJoinJumpStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15190)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x15190 0x1519c)
        0x1519c retired) false := by
  exact configuredJStep stepNo 0x15190 0x1519c state 0x00c
    0x6f 0x00 0xc0 0x00 configured atPc loaded
    (by configured_decode configured) (by native_decide) (by native_decide) (by native_decide)
    (base := by rfl)

/-- Production `0x1515c: ld a0,0x668(sp)`. -/
theorem optionalAddressLoadFirstStep (stepNo stackPointer value : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x1515c)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (rep : UIntRep 8 state.mem (stackPointer + 0x668) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (stackPointer + 0x668)) 8)
    (noMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + 0x668)) 8)
    (aligned : stackPointer % 16 = 0) (sourceFits : stackPointer + 0x67c ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1515c retired x10 (BitVec.ofNat 64 value)) false := by
  apply configuredStackDwordLoadStep stepNo 0x1515c stackPointer 0x668 value state
    0x668 (.Regidx 10#5) x10 (BitVec.ofNat 64 value) 0x03 0x35 0x81 0x66
    configured atPc stack rep pma noMMIO (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x668#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise _
  · configured_decode configured

/-- Production `0x15160: ld a1,0x670(sp)`. -/
theorem optionalAddressLoadSecondStep (stepNo stackPointer value : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15160)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (rep : UIntRep 8 state.mem (stackPointer + 0x670) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (stackPointer + 0x670)) 8)
    (noMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + 0x670)) 8)
    (aligned : stackPointer % 16 = 0) (sourceFits : stackPointer + 0x67c ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15160 retired x11 (BitVec.ofNat 64 value)) false := by
  apply configuredStackDwordLoadStep stepNo 0x15160 stackPointer 0x670 value state
    0x670 (.Regidx 11#5) x11 (BitVec.ofNat 64 value) 0x83 0x35 0x01 0x67
    configured atPc stack rep pma noMMIO (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x670#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x11_run premise _
  · configured_decode configured

/-- Production `0x15164: lw a2,0x678(sp)`. -/
theorem optionalAddressLoadFinalStep (stepNo stackPointer value : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15164)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (rep : UIntRep 4 state.mem (stackPointer + 0x678) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (stackPointer + 0x678)) 4)
    (noMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + 0x678)) 4)
    (aligned : stackPointer % 16 = 0) (sourceFits : stackPointer + 0x67c ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15164 retired x12
        (extend_value false (BitVec.ofNat 32 value))) false := by
  apply configuredStackWordLoadStep stepNo 0x15164 stackPointer 0x678 value state
    0x678 (.Regidx 12#5) x12 (extend_value false (BitVec.ofNat 32 value))
    0x03 0x26 0x81 0x67 configured atPc stack rep pma noMMIO (by omega) (by omega) loaded
    (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x678#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x12_run premise _
  · configured_decode configured

/-- Production `0x15168: sd a0,0x6d0(sp)`. -/
theorem optionalAddressStoreFirstStep (stepNo stackPointer : Nat) (state : State)
    (value : BitVec 64) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15168)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (data : state.regs.get? x10 = some value)
    (pma : StorePmaAllows state (BitVec.ofNat 64 (stackPointer + 0x6d0)) 8)
    (noMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + 0x6d0)) 8)
    (aligned : stackPointer % 16 = 0) (fits : stackPointer + 0x6d8 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8) (coreStoreNextState (tryStepStoreAfterIncrement state) 0x15168)
          (stackPointer + 0x6d0) value) 0x15168 retired) false := by
  apply configuredStackDwordStoreStep stepNo 0x15168 stackPointer 0x6d0 state value
    0x6d0 (.Regidx 10#5) 0x23 0x38 0xa1 0x6c configured atPc stack pma noMMIO
    (by omega) fits loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x6d0#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨_, _, _, _, _⟩ := configured.storeDecodeContext
    configured_decode configured
  · intro premise writes
    exact rX_x10_run premise value ((writes.get x10 (by decide)).trans data)

/-- Production `0x1516c: sd a1,0x6d8(sp)`. -/
theorem optionalAddressStoreSecondStep (stepNo stackPointer : Nat) (state : State)
    (value : BitVec 64) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x1516c)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (data : state.regs.get? x11 = some value)
    (pma : StorePmaAllows state (BitVec.ofNat 64 (stackPointer + 0x6d8)) 8)
    (noMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + 0x6d8)) 8)
    (aligned : stackPointer % 16 = 0) (fits : stackPointer + 0x6e0 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8) (coreStoreNextState (tryStepStoreAfterIncrement state) 0x1516c)
          (stackPointer + 0x6d8) value) 0x1516c retired) false := by
  apply configuredStackDwordStoreStep stepNo 0x1516c stackPointer 0x6d8 state value
    0x6d8 (.Regidx 11#5) 0x23 0x3c 0xb1 0x6c configured atPc stack pma noMMIO
    (by omega) fits loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x6d8#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨_, _, _, _, _⟩ := configured.storeDecodeContext
    configured_decode configured
  · intro premise writes
    exact rX_x11_run premise value ((writes.get x11 (by decide)).trans data)

/-- Production `0x15170: sw a2,0x6e0(sp)`. -/
theorem optionalAddressStoreFinalStep (stepNo stackPointer : Nat) (state : State)
    (value : BitVec 64) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15170)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (data : state.regs.get? x12 = some value)
    (pma : StorePmaAllows state (BitVec.ofNat 64 (stackPointer + 0x6e0)) 4)
    (noMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + 0x6e0)) 4)
    (aligned : stackPointer % 16 = 0) (fits : stackPointer + 0x6e4 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := 4)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15170)
          (stackPointer + 0x6e0) value) 0x15174 retired) false := by
  apply configuredStackWordStoreStep stepNo 0x15170 stackPointer 0x6e0 state value
    0x6e0 (.Regidx 12#5) 0x23 0x20 0xc1 0x6e configured atPc stack pma noMMIO
    (by omega) fits loaded (base := by rfl)
  · change BitVec.ofNat 64 stackPointer + 0x6e0#64 = _
    rw [← BitVec.ofNat_add]
  · configured_decode configured
  · intro premise writes
    exact rX_x12_run premise value ((writes.get x12 (by decide)).trans data)

end BinaryFv.Zesu.MachineExecution
