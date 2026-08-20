import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.RiscV.Instruction.Execute.ShiftOr
import BinaryFv.RiscV.Elfling.Seg
import BinaryFv.ProofProgress.OwnedPc

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

/-- One exact unsigned-byte load through `x18`, shared by inlined integer readers. -/
theorem configuredByteLoadFromX18Step (stepNo pc offset : Nat) (state : State)
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
  apply configuredByteLoadFromX18Step stepNo 0x121c4 1 state (.Regidx 10#5) x10
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
  apply configuredByteLoadFromX18Step stepNo 0x121c8 0 state (.Regidx 12#5) x12
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
  apply configuredByteLoadFromX18Step stepNo 0x121cc 2 state (.Regidx 14#5) x14
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
  apply configuredByteLoadFromX18Step stepNo 0x121d0 3 state (.Regidx 15#5) x15
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

def memReadIntOwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x121c4, 0x121c8, 0x121cc, 0x121d0, 0x121d4,
    0x121d8, 0x121dc, 0x121e0, 0x121e4, 0x121e8] pc

def memReadIntExitPc (pc : BitVec 64) : Prop := pcInList [0x121ec] pc

def memReadIntWrites (register : Register) : Prop :=
  stepBookkeeping register ∨ register = x10 ∨ register = x12 ∨ register = x14 ∨ register = x15

private theorem instructionPreserved_disjoint_memReadIntWrites :
    RegSet.Disjoint instructionPreserved memReadIntWrites := by
  intro register preserved writes
  rcases writes with writes | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 writes
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem platformPreserved_disjoint_memReadIntWrites :
    RegSet.Disjoint platformPreserved memReadIntWrites := by
  intro register preserved writes
  rcases writes with writes | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved writes
  all_goals simp [platformPreserved] at preserved

private theorem memReadIntLoadedOfSeg
    {kv : List RegVal} {a n : Nat} {base cur : State} {pc : BitVec 64}
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (seg : Seg memReadIntOwnPc memReadIntExitPc (fun _ _ _ _ _ => False)
      memReadIntWrites noMemory kv a n base cur pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  rw [seg.memEq noMemory_empty]
  exact loaded

/-- Exact ten-step machine trace for the inlined four-byte little-endian read. -/
theorem memReadIntRun (fromStep baseAddress byte0 byte1 byte2 byte3 : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x121c4))
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep0 : UIntRep 1 state.mem baseAddress byte0)
    (rep1 : UIntRep 1 state.mem (baseAddress + 1) byte1)
    (rep2 : UIntRep 1 state.mem (baseAddress + 2) byte2)
    (rep3 : UIntRep 1 state.mem (baseAddress + 3) byte3)
    (pma : ∀ offset, offset < 4 →
      LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (notMMIO : ∀ offset, offset < 4 →
      LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (sourceFits : baseAddress + 4 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after,
      Seg memReadIntOwnPc memReadIntExitPc (fun _ _ _ _ _ => False)
        memReadIntWrites noMemory
        [⟨x14,
          ((Sail.shift_bits_left (zero_extend (m := 64) (BitVec.ofNat 8 byte3))
              (Sail.BitVec.extractLsb (24#6)
                (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) |||
            (Sail.shift_bits_left (zero_extend (m := 64) (BitVec.ofNat 8 byte2))
              (Sail.BitVec.extractLsb (16#6)
                (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) |||
          ((Sail.shift_bits_left (zero_extend (m := 64) (BitVec.ofNat 8 byte1))
              (Sail.BitVec.extractLsb (8#6)
                (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) |||
            zero_extend (m := 64) (BitVec.ofNat 8 byte0))⟩]
        fromStep 10 state after (BitVec.ofNat 64 0x121ec) := by
  let b0 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 byte0)
  let b1 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 byte1)
  let b2 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 byte2)
  let b3 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 byte3)
  let s1 := Sail.shift_bits_left b1
    (Sail.BitVec.extractLsb (8#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let low := s1 ||| b0
  let s2 := Sail.shift_bits_left b2
    (Sail.BitVec.extractLsb (16#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let s3 := Sail.shift_bits_left b3
    (Sail.BitVec.extractLsb (24#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let high := s3 ||| s2
  let result := high ||| low
  obtain ⟨retired0, retiredRead0⟩ := configured.retiredCounter
  have seg0 := Seg.nil memReadIntOwnPc memReadIntExitPc (fun _ _ _ _ _ => False)
    memReadIntWrites noMemory fromStep ⟨retired0, retiredRead0⟩ atPc
  have baseOfSeg {kv n cur pc}
      (seg : Seg memReadIntOwnPc memReadIntExitPc (fun _ _ _ _ _ => False)
        memReadIntWrites noMemory kv fromStep n state cur pc) :
      cur.regs.get? x18 = some (BitVec.ofNat 64 baseAddress) :=
    (seg.get x18 (by simp [memReadIntWrites, stepBookkeeping])).trans base
  have repOfSeg {kv n cur pc offset value}
      (seg : Seg memReadIntOwnPc memReadIntExitPc (fun _ _ _ _ _ => False)
        memReadIntWrites noMemory kv fromStep n state cur pc)
      (rep : UIntRep 1 state.mem (baseAddress + offset) value) :
      UIntRep 1 cur.mem (baseAddress + offset) value := by
    rw [seg.memEq noMemory_empty]
    exact rep
  have configuredOfSeg {kv n cur pc}
      (seg : Seg memReadIntOwnPc memReadIntExitPc (fun _ _ _ _ _ => False)
        memReadIntWrites noMemory kv fromStep n state cur pc) :
      ConfiguredMachinePre EndpointMachinePc cur :=
    configured.mono (seg.agree instructionPreserved_disjoint_memReadIntWrites) seg.retired
  have pmaOfSeg {kv n cur pc offset}
      (seg : Seg memReadIntOwnPc memReadIntExitPc (fun _ _ _ _ _ => False)
        memReadIntWrites noMemory kv fromStep n state cur pc)
      (bound : offset < 4) :
      LoadPmaAllows cur (BitVec.ofNat 64 (baseAddress + offset)) 1 :=
    loadPmaAllows_of_agree (seg.agree platformPreserved_disjoint_memReadIntWrites)
      (pma offset bound)
  obtain ⟨m1, seg1⟩ := seg0.step (by owned_pc [memReadIntOwnPc, pcInList])
    (by owned_pc [memReadIntExitPc, pcInList]) x10 b1 0x121c8
    (memReadIntLoadOffsetOne fromStep state baseAddress byte1 configured atPc base rep1
      (pma 1 (by omega)) (notMMIO 1 (by omega)) (by omega) loaded)
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨m2, seg2⟩ := seg1.step (by owned_pc [memReadIntOwnPc, pcInList])
    (by owned_pc [memReadIntExitPc, pcInList]) x12 b0 0x121cc
    (memReadIntLoadOffsetZero (fromStep + 1) m1 baseAddress byte0 (configuredOfSeg seg1)
      seg1.atPc (baseOfSeg seg1) (by simpa using repOfSeg seg1 (offset := 0) rep0)
      (by simpa using pmaOfSeg seg1 (offset := 0) (by omega)) (notMMIO 0 (by omega))
      (by omega) (memReadIntLoadedOfSeg loaded seg1))
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inl rfl)))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨m3, seg3⟩ := seg2.step (by owned_pc [memReadIntOwnPc, pcInList])
    (by owned_pc [memReadIntExitPc, pcInList]) x14 b2 0x121d0
    (memReadIntLoadOffsetTwo (fromStep + 2) m2 baseAddress byte2 (configuredOfSeg seg2)
      seg2.atPc (baseOfSeg seg2) (repOfSeg seg2 rep2) (pmaOfSeg seg2 (by omega))
      (notMMIO 2 (by omega)) (by omega) (memReadIntLoadedOfSeg loaded seg2))
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨m4, seg4⟩ := seg3.step (by owned_pc [memReadIntOwnPc, pcInList])
    (by owned_pc [memReadIntExitPc, pcInList]) x15 b3 0x121d4
    (memReadIntLoadOffsetThree (fromStep + 3) m3 baseAddress byte3 (configuredOfSeg seg3)
      seg3.atPc (baseOfSeg seg3) (repOfSeg seg3 rep3) (pmaOfSeg seg3 (by omega))
      (notMMIO 3 (by omega)) (by omega) (memReadIntLoadedOfSeg loaded seg3))
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨r5, run5⟩ := memReadIntShiftA0ByEight (fromStep + 4) m4 b1
    (configuredOfSeg seg4) seg4.atPc (seg4.reg x10 b1 (by simp))
    (memReadIntLoadedOfSeg loaded seg4)
  have seg4' := seg4.forget (kv' := [⟨x15, b3⟩, ⟨x14, b2⟩, ⟨x12, b0⟩]) (by simp)
  obtain ⟨m5, seg5⟩ := seg4'.step (by owned_pc [memReadIntOwnPc, pcInList])
    (by owned_pc [memReadIntExitPc, pcInList]) x10 s1 0x121d8 ⟨r5, run5⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨r6, run6⟩ := memReadIntOrA0A2 (fromStep + 5) m5 s1 b0
    (configuredOfSeg seg5) seg5.atPc (seg5.reg x10 s1 (by simp))
    (seg5.reg x12 b0 (by simp)) (memReadIntLoadedOfSeg loaded seg5)
  have seg5' := seg5.forget (kv' := [⟨x10, s1⟩, ⟨x15, b3⟩, ⟨x14, b2⟩,
    ⟨x12, b0⟩]) (by simp)
  have seg5' := seg5'.forget (kv' := [⟨x15, b3⟩, ⟨x14, b2⟩, ⟨x12, b0⟩]) (by simp)
  obtain ⟨m6, seg6⟩ := seg5'.step (by owned_pc [memReadIntOwnPc, pcInList])
    (by owned_pc [memReadIntExitPc, pcInList]) x10 low 0x121dc ⟨r6, run6⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨r7, run7⟩ := memReadIntShiftA4BySixteen (fromStep + 6) m6 b2
    (configuredOfSeg seg6) seg6.atPc (seg6.reg x14 b2 (by simp))
    (memReadIntLoadedOfSeg loaded seg6)
  have seg6' := seg6.forget (kv' := [⟨x10, low⟩, ⟨x15, b3⟩, ⟨x12, b0⟩]) (by simp)
  obtain ⟨m7, seg7⟩ := seg6'.step (by owned_pc [memReadIntOwnPc, pcInList])
    (by owned_pc [memReadIntExitPc, pcInList]) x14 s2 0x121e0 ⟨r7, run7⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨r8, run8⟩ := memReadIntShiftA5ByTwentyFour (fromStep + 7) m7 b3
    (configuredOfSeg seg7) seg7.atPc (seg7.reg x15 b3 (by simp))
    (memReadIntLoadedOfSeg loaded seg7)
  have seg7' := seg7.forget (kv' := [⟨x14, s2⟩, ⟨x10, low⟩, ⟨x12, b0⟩]) (by simp)
  obtain ⟨m8, seg8⟩ := seg7'.step (by owned_pc [memReadIntOwnPc, pcInList])
    (by owned_pc [memReadIntExitPc, pcInList]) x15 s3 0x121e4 ⟨r8, run8⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨r9, run9⟩ := memReadIntOrA5A4 (fromStep + 8) m8 s3 s2
    (configuredOfSeg seg8) seg8.atPc (seg8.reg x15 s3 (by simp))
    (seg8.reg x14 s2 (by simp)) (memReadIntLoadedOfSeg loaded seg8)
  have seg8' := seg8.forget (kv' := [⟨x15, s3⟩, ⟨x10, low⟩, ⟨x12, b0⟩]) (by simp)
  obtain ⟨m9, seg9⟩ := seg8'.step (by owned_pc [memReadIntOwnPc, pcInList])
    (by owned_pc [memReadIntExitPc, pcInList]) x14 high 0x121e8 ⟨r9, run9⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨r10, run10⟩ := memReadIntOrA4A0 (fromStep + 9) m9 high low
    (configuredOfSeg seg9) seg9.atPc (seg9.reg x14 high (by simp))
    (seg9.reg x10 low (by simp)) (memReadIntLoadedOfSeg loaded seg9)
  have seg9' := seg9.forget (kv' := [⟨x15, s3⟩, ⟨x10, low⟩, ⟨x12, b0⟩]) (by simp)
  obtain ⟨after, seg10⟩ := seg9'.step (by owned_pc [memReadIntOwnPc, pcInList])
    (by owned_pc [memReadIntExitPc, pcInList]) x14 result 0x121ec ⟨r10, run10⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have final := seg10.forget (kv' := [⟨x14, result⟩]) (by simp)
  refine ⟨after, ?_⟩
  simpa [b0, b1, b2, b3, s1, s2, s3, low, high, result, Nat.add_assoc] using final

end BinaryFv.Zesu.MachineExecution
