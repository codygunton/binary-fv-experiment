import BinaryFv.Zesu.MachineExecution.InstructionClassSteps

/-!
# Exact steps for the Level 3 `mem.readInt` instance

The inlined instance at `0x121c4` reads four bytes through `x18`. It combines them into the
little-endian result in `x14`. This module starts with the four exact unsigned-byte loads.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

private theorem memReadIntOfNatAdd (base offset : Nat) (_fits : base + offset < 2 ^ 64) :
    BitVec.ofNat 64 base + BitVec.ofNat 64 offset = BitVec.ofNat 64 (base + offset) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem memReadIntByteLoadStep (stepNo pc offset : Nat) (state : State)
    (rd : regidx) (destination : Register) (result : RegisterType destination)
    (byte0 byte1 byte2 byte3 : UInt8) (baseAddress value : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 state.mem (baseAddress + offset) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (sumFits : baseAddress + offset < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (BitVec.ofNat 12 offset, .Regidx 18#5, rd, true, 1)))
    (writeRun : ∀ premise,
      Runs (wX_bits rd (zero_extend (m := 64) (BitVec.ofNat 8 value))) premise
        { premise with regs := premise.regs.insert destination result } ())
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (addressEq : BitVec.ofNat 64 baseAddress +
      sign_extend (m := 64) (BitVec.ofNat 12 offset) =
        BitVec.ofNat 64 (baseAddress + offset)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false := by
  have baseRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits (.Regidx 18#5)) premise premise (BitVec.ofNat 64 baseAddress) := by
    intro premise writes
    exact rX_x18_run premise _ ((writes x18 (by simp [stepBookkeeping])).trans base)
  exact configuredByteLoadStep stepNo pc state (BitVec.ofNat 12 offset) (.Regidx 18#5) rd
    destination baseAddress offset value result
    byte0 byte1 byte2 byte3 configured atPc rep pma notMMIO sumFits loaded
    addressEq baseRun writeRun decode (pcFits := site.pcFits) (pcAligned := site.pcAligned)
    (destinationNotNextPc := destinationNotNextPc) (destinationNotHart := destinationNotHart)
    (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired) (base := baseEncoding)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)

theorem memReadIntLoadOffsetOne (stepNo : Nat) (state : State) (baseAddress value : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x121c4))
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 state.mem (baseAddress + 1) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + 1)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 1)) 1)
    (sumFits : baseAddress + 1 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x121c4) retired x10
        (zero_extend (m := 64) (BitVec.ofNat 8 value))) false := by
  apply memReadIntByteLoadStep stepNo 0x121c4 1 state (.Regidx 10#5) x10
    (zero_extend (m := 64) (BitVec.ofNat 8 value))
    0x03 0x45 0x19 0x00 baseAddress value configured atPc base rep pma notMMIO sumFits loaded
  · configured_decode configured
  · intro premise
    exact wX_x10_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · rw [show sign_extend (m := 64) (1#12) = 1#64 by native_decide]
    exact memReadIntOfNatAdd baseAddress 1 sumFits

theorem memReadIntLoadOffsetZero (stepNo : Nat) (state : State) (baseAddress value : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x121c8))
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 state.mem baseAddress value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 baseAddress) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 baseAddress) 1)
    (sumFits : baseAddress < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x121c8) retired x12
        (zero_extend (m := 64) (BitVec.ofNat 8 value))) false := by
  apply memReadIntByteLoadStep stepNo 0x121c8 0 state (.Regidx 12#5) x12
    (zero_extend (m := 64) (BitVec.ofNat 8 value))
    0x03 0x46 0x09 0x00 baseAddress value configured atPc base (by simpa using rep)
    (by simpa using pma) (by simpa using notMMIO) (by simpa using sumFits) loaded
  · configured_decode configured
  · intro premise
    exact wX_x12_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · rw [show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
    exact memReadIntOfNatAdd baseAddress 0 (by simpa using sumFits)

theorem memReadIntLoadOffsetTwo (stepNo : Nat) (state : State) (baseAddress value : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x121cc))
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 state.mem (baseAddress + 2) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + 2)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 2)) 1)
    (sumFits : baseAddress + 2 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x121cc) retired x14
        (zero_extend (m := 64) (BitVec.ofNat 8 value))) false := by
  apply memReadIntByteLoadStep stepNo 0x121cc 2 state (.Regidx 14#5) x14
    (zero_extend (m := 64) (BitVec.ofNat 8 value))
    0x03 0x47 0x29 0x00 baseAddress value configured atPc base rep pma notMMIO sumFits loaded
  · configured_decode configured
  · intro premise
    exact wX_x14_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · rw [show sign_extend (m := 64) (2#12) = 2#64 by native_decide]
    exact memReadIntOfNatAdd baseAddress 2 sumFits

theorem memReadIntLoadOffsetThree (stepNo : Nat) (state : State) (baseAddress value : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x121d0))
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 state.mem (baseAddress + 3) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + 3)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 3)) 1)
    (sumFits : baseAddress + 3 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x121d0) retired x15
        (zero_extend (m := 64) (BitVec.ofNat 8 value))) false := by
  apply memReadIntByteLoadStep stepNo 0x121d0 3 state (.Regidx 15#5) x15
    (zero_extend (m := 64) (BitVec.ofNat 8 value))
    0x83 0x47 0x39 0x00 baseAddress value configured atPc base rep pma notMMIO sumFits loaded
  · configured_decode configured
  · intro premise
    exact wX_x15_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · rw [show sign_extend (m := 64) (3#12) = 3#64 by native_decide]
    exact memReadIntOfNatAdd baseAddress 3 sumFits

end BinaryFv.Zesu.MachineExecution
