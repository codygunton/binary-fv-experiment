import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.RiscV.Instruction.Execute.ShiftOr

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

private theorem memReadIntSlliStep (stepNo pc : Nat) (state : State) (shamt : BitVec 6)
    (rs1 rd : regidx) (destination : Register) (result : RegisterType destination)
    (source : BitVec 64)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (shamt, rs1, rd, .SLLI)))
    (sourceRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs1) premise premise source)
    (writeRun : ∀ premise,
      Runs (wX_bits rd (Sail.shift_bits_left source
        (Sail.BitVec.extractLsb shamt (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) premise
        { premise with regs := premise.regs.insert destination result } ())
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have execute : Runs
      (execute (.SHIFTIOP (shamt, rs1, rd, .SLLI))) premise
      { premise with regs := premise.regs.insert destination result }
      (.Retire_Success ()) := by
    change Runs (execute_SHIFTIOP shamt _ _ .SLLI) _ _ _
    exact execute_SHIFTIOP_slli_run premise _ shamt rs1 rd source
      (sourceRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)))
      (writeRun premise)
  exact configuredRegisterWriteStep stepNo pc state destination result
    (.SHIFTIOP (shamt, rs1, rd, .SLLI)) byte0 byte1 byte2 byte3 configured atPc loaded
    decode execute (pcFits := site.pcFits) (pcAligned := site.pcAligned)
    (destinationNotNextPc := destinationNotNextPc) (destinationNotHart := destinationNotHart)
    (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired) (base := baseEncoding)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)

theorem memReadIntShiftA0ByEight (stepNo : Nat) (state : State) (source : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x121d4))
    (sourceRead : state.regs.get? x10 = some source)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x121d4) retired x10
        (Sail.shift_bits_left source
          (Sail.BitVec.extractLsb (8#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
        false := by
  apply memReadIntSlliStep stepNo 0x121d4 state 8#6 (.Regidx 10#5) (.Regidx 10#5)
    x10 _ source 0x13 0x15 0x85 0x00 configured atPc loaded
  · configured_decode configured
  · intro premise writes
    exact rX_x10_run premise source ((writes x10 (by simp [stepBookkeeping])).trans sourceRead)
  · intro premise
    exact wX_x10_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl

theorem memReadIntShiftA4BySixteen (stepNo : Nat) (state : State) (source : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x121dc))
    (sourceRead : state.regs.get? x14 = some source)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x121dc) retired x14
        (Sail.shift_bits_left source
          (Sail.BitVec.extractLsb (16#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
        false := by
  apply memReadIntSlliStep stepNo 0x121dc state 16#6 (.Regidx 14#5) (.Regidx 14#5)
    x14 _ source 0x13 0x17 0x07 0x01 configured atPc loaded
  · configured_decode configured
  · intro premise writes
    exact rX_x14_run premise source ((writes x14 (by simp [stepBookkeeping])).trans sourceRead)
  · intro premise
    exact wX_x14_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl

theorem memReadIntShiftA5ByTwentyFour (stepNo : Nat) (state : State) (source : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x121e0))
    (sourceRead : state.regs.get? x15 = some source)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x121e0) retired x15
        (Sail.shift_bits_left source
          (Sail.BitVec.extractLsb (24#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
        false := by
  apply memReadIntSlliStep stepNo 0x121e0 state 24#6 (.Regidx 15#5) (.Regidx 15#5)
    x15 _ source 0x93 0x97 0x87 0x01 configured atPc loaded
  · configured_decode configured
  · intro premise writes
    exact rX_x15_run premise source ((writes x15 (by simp [stepBookkeeping])).trans sourceRead)
  · intro premise
    exact wX_x15_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl

private theorem memReadIntOrStep (stepNo pc : Nat) (state : State) (rs2 rs1 rd : regidx)
    (destination : Register) (result : RegisterType destination) (left right : BitVec 64)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (rs2, rs1, rd, .OR)))
    (leftRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs1) premise premise left)
    (rightRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs2) premise premise right)
    (writeRun : ∀ premise, Runs (wX_bits rd (left ||| right)) premise
      { premise with regs := premise.regs.insert destination result } ())
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have execute : Runs (execute (.RTYPE (rs2, rs1, rd, .OR))) premise
      { premise with regs := premise.regs.insert destination result } (.Retire_Success ()) := by
    change Runs (execute_RTYPE rs2 rs1 rd .OR) _ _ _
    exact execute_RTYPE_or_run premise _ rs2 rs1 rd left right
      (leftRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)))
      (rightRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)))
      (writeRun premise)
  exact configuredRegisterWriteStep stepNo pc state destination result
    (.RTYPE (rs2, rs1, rd, .OR)) byte0 byte1 byte2 byte3 configured atPc loaded decode execute
    (pcFits := site.pcFits) (pcAligned := site.pcAligned)
    (destinationNotNextPc := destinationNotNextPc) (destinationNotHart := destinationNotHart)
    (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired) (base := baseEncoding)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)

theorem memReadIntOrA0A2 (stepNo : Nat) (state : State) (left right : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x121d8))
    (leftRead : state.regs.get? x10 = some left)
    (rightRead : state.regs.get? x12 = some right)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x121d8) retired x10 (left ||| right)) false := by
  apply memReadIntOrStep stepNo 0x121d8 state (.Regidx 12#5) (.Regidx 10#5)
    (.Regidx 10#5) x10 (left ||| right) left right 0x33 0x65 0xc5 0x00
    configured atPc loaded
  · configured_decode configured
  · intro premise writes
    exact rX_x10_run premise left ((writes x10 (by simp [stepBookkeeping])).trans leftRead)
  · intro premise writes
    exact rX_x12_run premise right ((writes x12 (by simp [stepBookkeeping])).trans rightRead)
  · intro premise
    exact wX_x10_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl

theorem memReadIntOrA5A4 (stepNo : Nat) (state : State) (left right : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x121e4))
    (leftRead : state.regs.get? x15 = some left)
    (rightRead : state.regs.get? x14 = some right)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x121e4) retired x14 (left ||| right)) false := by
  apply memReadIntOrStep stepNo 0x121e4 state (.Regidx 14#5) (.Regidx 15#5)
    (.Regidx 14#5) x14 (left ||| right) left right 0x33 0xe7 0xe7 0x00
    configured atPc loaded
  · configured_decode configured
  · intro premise writes
    exact rX_x15_run premise left ((writes x15 (by simp [stepBookkeeping])).trans leftRead)
  · intro premise writes
    exact rX_x14_run premise right ((writes x14 (by simp [stepBookkeeping])).trans rightRead)
  · intro premise
    exact wX_x14_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl

theorem memReadIntOrA4A0 (stepNo : Nat) (state : State) (left right : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x121e8))
    (leftRead : state.regs.get? x14 = some left)
    (rightRead : state.regs.get? x10 = some right)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x121e8) retired x14 (left ||| right)) false := by
  apply memReadIntOrStep stepNo 0x121e8 state (.Regidx 10#5) (.Regidx 14#5)
    (.Regidx 14#5) x14 (left ||| right) left right 0x33 0x67 0xa7 0x00
    configured atPc loaded
  · configured_decode configured
  · intro premise writes
    exact rX_x14_run premise left ((writes x14 (by simp [stepBookkeeping])).trans leftRead)
  · intro premise writes
    exact rX_x10_run premise right ((writes x10 (by simp [stepBookkeeping])).trans rightRead)
  · intro premise
    exact wX_x14_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl

end BinaryFv.Zesu.MachineExecution
