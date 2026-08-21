import BinaryFv.Zesu.MachineExecution.HLevel3MemReadIntSteps
import BinaryFv.RiscV.Instruction.Execute.RegisterOp

/-!
# Exact steps for one Level 3 `ssz.readU32` instance

The inlined instance at `0x12c18` performs four unsigned-byte loads through `x18`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

/-! ## Shared integer-reader segment transport -/

/-- Transport the configured machine facts through a register-only integer-reader segment. -/
theorem configuredMachinePre_of_readSeg {own exit : BitVec 64 → Prop}
    {W : RegSet} {kv : List RegVal} {fromStep count : Nat} {base cur : State}
    {pc : BitVec 64}
    (configured : ConfiguredMachinePre EndpointMachinePc base)
    (disjoint : RegSet.Disjoint instructionPreserved W)
    (seg : Seg own exit (fun _ _ _ _ _ => False) W noMemory kv
      fromStep count base cur pc) :
    ConfiguredMachinePre EndpointMachinePc cur :=
  configured.mono (seg.agree disjoint) seg.retired

/-- Transport an unchanged source-register value through an integer-reader segment. -/
theorem registerValue_of_readSeg {own exit : BitVec 64 → Prop}
    {W : RegSet} {kv : List RegVal} {fromStep count : Nat} {base cur : State}
    {pc : BitVec 64} {register : Register} {value : RegisterType register}
    (seg : Seg own exit (fun _ _ _ _ _ => False) W noMemory kv
      fromStep count base cur pc)
    (notWritten : ¬W register) (holds : base.regs.get? register = some value) :
    cur.regs.get? register = some value :=
  (seg.get register notWritten).trans holds

/-- Transport one byte representation through an integer-reader segment. -/
theorem uintRep_of_readSeg {own exit : BitVec 64 → Prop}
    {W : RegSet} {kv : List RegVal} {fromStep count address value : Nat}
    {base cur : State} {pc : BitVec 64}
    (seg : Seg own exit (fun _ _ _ _ _ => False) W noMemory kv
      fromStep count base cur pc)
    (rep : UIntRep 1 base.mem address value) : UIntRep 1 cur.mem address value := by
  rw [seg.memEq noMemory_empty]
  exact rep

/-- Transport one load-PMA fact through an integer-reader segment. -/
theorem loadPmaAllows_of_readSeg {own exit : BitVec 64 → Prop}
    {W : RegSet} {kv : List RegVal} {fromStep count width : Nat}
    {base cur : State} {pc address : BitVec 64}
    (seg : Seg own exit (fun _ _ _ _ _ => False) W noMemory kv
      fromStep count base cur pc)
    (disjoint : RegSet.Disjoint platformPreserved W)
    (allows : LoadPmaAllows base address width) : LoadPmaAllows cur address width :=
  loadPmaAllows_of_agree (seg.agree disjoint) allows

/-- Transport the pinned program bytes through an integer-reader segment. -/
theorem loadedFaithfully_of_readSeg {own exit : BitVec 64 → Prop}
    {W : RegSet} {kv : List RegVal} {fromStep count : Nat} {base cur : State}
    {pc : BitVec 64}
    (seg : Seg own exit (fun _ _ _ _ _ => False) W noMemory kv
      fromStep count base cur pc)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  rw [seg.memEq noMemory_empty]
  exact loaded

def readU32_3335OwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x12c18, 0x12c1c, 0x12c20, 0x12c24] pc

def readU32_3335ExitPc (pc : BitVec 64) : Prop := pcInList [0x12c28] pc

def readU32_3335Writes (register : Register) : Prop :=
  stepBookkeeping register ∨ register = x10 ∨ register = x15 ∨
    register = x13 ∨ register = x14

private theorem ofNatAdd (base offset : Nat) (_fits : base + offset < 2 ^ 64) :
    BitVec.ofNat 64 base + BitVec.ofNat 64 offset = BitVec.ofNat 64 (base + offset) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem step0 (stepNo : Nat) (state : State) (baseAddress value : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12c18))
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 state.mem (baseAddress + 22) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + 22)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 22)) 1)
    (fits : baseAddress + 22 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12c18 retired x10
        (zero_extend (m := 64) (BitVec.ofNat 8 value))) false := by
  apply configuredByteLoadFromX18Step stepNo 0x12c18 22 state (.Regidx 10#5) x10
    (zero_extend (m := 64) (BitVec.ofNat 8 value)) 0x03 0x45 0x69 0x01
    baseAddress value configured atPc base rep pma
    notMMIO fits loaded
  · configured_decode configured
  · intro premise; exact wX_x10_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · rw [show sign_extend (m := 64) (22#12) = 22#64 by native_decide]
    exact ofNatAdd baseAddress 22 fits

private theorem step1 (stepNo : Nat) (state : State) (baseAddress value : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12c1c))
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 state.mem (baseAddress + 23) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + 23)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 23)) 1)
    (fits : baseAddress + 23 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12c1c retired x15
        (zero_extend (m := 64) (BitVec.ofNat 8 value))) false := by
  apply configuredByteLoadFromX18Step stepNo 0x12c1c 23 state (.Regidx 15#5) x15
    (zero_extend (m := 64) (BitVec.ofNat 8 value)) 0x83 0x47 0x79 0x01
    baseAddress value configured atPc base rep pma
    notMMIO fits loaded
  · configured_decode configured
  · intro premise; exact wX_x15_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · rw [show sign_extend (m := 64) (23#12) = 23#64 by native_decide]
    exact ofNatAdd baseAddress 23 fits

private theorem step2 (stepNo : Nat) (state : State) (baseAddress value : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12c20))
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 state.mem (baseAddress + 24) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + 24)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 24)) 1)
    (fits : baseAddress + 24 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12c20 retired x13
        (zero_extend (m := 64) (BitVec.ofNat 8 value))) false := by
  apply configuredByteLoadFromX18Step stepNo 0x12c20 24 state (.Regidx 13#5) x13
    (zero_extend (m := 64) (BitVec.ofNat 8 value)) 0x83 0x46 0x89 0x01
    baseAddress value configured atPc base rep pma
    notMMIO fits loaded
  · configured_decode configured
  · intro premise; exact wX_x13_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · rw [show sign_extend (m := 64) (24#12) = 24#64 by native_decide]
    exact ofNatAdd baseAddress 24 fits

private theorem step3 (stepNo : Nat) (state : State) (baseAddress value : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12c24))
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep : UIntRep 1 state.mem (baseAddress + 25) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + 25)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 25)) 1)
    (fits : baseAddress + 25 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12c24 retired x14
        (zero_extend (m := 64) (BitVec.ofNat 8 value))) false := by
  apply configuredByteLoadFromX18Step stepNo 0x12c24 25 state (.Regidx 14#5) x14
    (zero_extend (m := 64) (BitVec.ofNat 8 value)) 0x03 0x47 0x99 0x01
    baseAddress value configured atPc base rep pma
    notMMIO fits loaded
  · configured_decode configured
  · intro premise; exact wX_x14_run premise _
  · native_decide
  · decide
  · decide
  · decide
  · decide
  · rfl
  · rw [show sign_extend (m := 64) (25#12) = 25#64 by native_decide]
    exact ofNatAdd baseAddress 25 fits

private theorem instructionPreserved_disjoint (register : Register)
    (preserved : instructionPreserved register) : ¬readU32_3335Writes register := by
  intro writes
  rcases writes with writes | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 writes
  all_goals simp_all [instructionPreserved, platformPreserved]

private theorem platformDisjointWrites (register : Register)
    (preserved : platformPreserved register) : ¬readU32_3335Writes register := by
  intro writes
  rcases writes with writes | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved writes
  all_goals simp_all [platformPreserved]

/-- Exact four-load trace for `fi:1:3335`. -/
theorem readU32_3335Run (fromStep baseAddress v0 v1 v2 v3 : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12c18))
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep0 : UIntRep 1 state.mem (baseAddress + 22) v0)
    (rep1 : UIntRep 1 state.mem (baseAddress + 23) v1)
    (rep2 : UIntRep 1 state.mem (baseAddress + 24) v2)
    (rep3 : UIntRep 1 state.mem (baseAddress + 25) v3)
    (pma : ∀ offset, offset < 4 →
      LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + 22 + offset)) 1)
    (notMMIO : ∀ offset, offset < 4 →
      LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 22 + offset)) 1)
    (sourceFits : baseAddress + 22 + 4 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after, Seg readU32_3335OwnPc readU32_3335ExitPc (fun _ _ _ _ _ => False)
      readU32_3335Writes noMemory
      [⟨x14, zero_extend (m := 64) (BitVec.ofNat 8 v3)⟩,
       ⟨x13, zero_extend (m := 64) (BitVec.ofNat 8 v2)⟩,
       ⟨x15, zero_extend (m := 64) (BitVec.ofNat 8 v1)⟩,
       ⟨x10, zero_extend (m := 64) (BitVec.ofNat 8 v0)⟩]
      fromStep 4 state after (BitVec.ofNat 64 0x12c28) := by
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  have seg0 := Seg.nil readU32_3335OwnPc readU32_3335ExitPc (fun _ _ _ _ _ => False)
    readU32_3335Writes noMemory fromStep ⟨retired, retiredRead⟩ atPc
  have configuredOfSeg {kv n cur pc}
      (seg : Seg readU32_3335OwnPc readU32_3335ExitPc (fun _ _ _ _ _ => False)
        readU32_3335Writes noMemory kv fromStep n state cur pc) :
      ConfiguredMachinePre EndpointMachinePc cur :=
    configuredMachinePre_of_readSeg configured instructionPreserved_disjoint seg
  have baseOfSeg {kv n cur pc}
      (seg : Seg readU32_3335OwnPc readU32_3335ExitPc (fun _ _ _ _ _ => False)
        readU32_3335Writes noMemory kv fromStep n state cur pc) :
      cur.regs.get? x18 = some (BitVec.ofNat 64 baseAddress) :=
    registerValue_of_readSeg seg (by simp [readU32_3335Writes, stepBookkeeping]) base
  have repOfSeg {kv n cur pc offset value}
      (seg : Seg readU32_3335OwnPc readU32_3335ExitPc (fun _ _ _ _ _ => False)
        readU32_3335Writes noMemory kv fromStep n state cur pc)
      (rep : UIntRep 1 state.mem (baseAddress + offset) value) :
      UIntRep 1 cur.mem (baseAddress + offset) value :=
    uintRep_of_readSeg seg rep
  have pmaOfSeg {kv n cur pc offset}
      (seg : Seg readU32_3335OwnPc readU32_3335ExitPc (fun _ _ _ _ _ => False)
        readU32_3335Writes noMemory kv fromStep n state cur pc)
      (bound : offset < 4) :
      LoadPmaAllows cur (BitVec.ofNat 64 (baseAddress + 22 + offset)) 1 :=
    loadPmaAllows_of_readSeg seg platformDisjointWrites (pma offset bound)
  have loadedOfSeg {kv n cur pc}
      (seg : Seg readU32_3335OwnPc readU32_3335ExitPc (fun _ _ _ _ _ => False)
        readU32_3335Writes noMemory kv fromStep n state cur pc) :
      Artifacts.programImage.fileBytesLoadedFaithfully cur.mem :=
    loadedFaithfully_of_readSeg seg loaded
  obtain ⟨m1, seg1⟩ := seg0.step (by owned_pc [readU32_3335OwnPc, pcInList])
    (by owned_pc [readU32_3335ExitPc, pcInList]) x10
    (zero_extend (m := 64) (BitVec.ofNat 8 v0)) 0x12c1c
    (step0 fromStep state baseAddress v0 configured atPc base rep0 (pma 0 (by omega))
      (notMMIO 0 (by omega)) (by omega) loaded)
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨m2, seg2⟩ := seg1.step (by owned_pc [readU32_3335OwnPc, pcInList])
    (by owned_pc [readU32_3335ExitPc, pcInList]) x15
    (zero_extend (m := 64) (BitVec.ofNat 8 v1)) 0x12c20
    (step1 (fromStep + 1) m1 baseAddress v1 (configuredOfSeg seg1) seg1.atPc
      (baseOfSeg seg1) (repOfSeg seg1 rep1) (by simpa [Nat.add_assoc] using pmaOfSeg seg1 (offset := 1) (by omega))
      (by simpa [Nat.add_assoc] using notMMIO 1 (by omega)) (by omega) (loadedOfSeg seg1))
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inl rfl)))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨m3, seg3⟩ := seg2.step (by owned_pc [readU32_3335OwnPc, pcInList])
    (by owned_pc [readU32_3335ExitPc, pcInList]) x13
    (zero_extend (m := 64) (BitVec.ofNat 8 v2)) 0x12c24
    (step2 (fromStep + 2) m2 baseAddress v2 (configuredOfSeg seg2) seg2.atPc
      (baseOfSeg seg2) (repOfSeg seg2 rep2) (by simpa [Nat.add_assoc] using pmaOfSeg seg2 (offset := 2) (by omega))
      (by simpa [Nat.add_assoc] using notMMIO 2 (by omega)) (by omega) (loadedOfSeg seg2))
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨after, seg4⟩ := seg3.step (by owned_pc [readU32_3335OwnPc, pcInList])
    (by owned_pc [readU32_3335ExitPc, pcInList]) x14
    (zero_extend (m := 64) (BitVec.ofNat 8 v3)) 0x12c28
    (step3 (fromStep + 3) m3 baseAddress v3 (configuredOfSeg seg3) seg3.atPc
      (baseOfSeg seg3) (repOfSeg seg3 rep3) (by simpa [Nat.add_assoc] using pmaOfSeg seg3 (offset := 3) (by omega))
      (by simpa [Nat.add_assoc] using notMMIO 3 (by omega)) (by omega) (loadedOfSeg seg3))
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  exact ⟨after, seg4⟩

/-! ## `fi:1:2ff8`: complete inline `readU32` wrapper -/

def readU32_2ff8OwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x12734, 0x12738, 0x1273c, 0x12740, 0x12744, 0x12748,
    0x1274c, 0x12750, 0x12754, 0x12758, 0x1275c] pc

def readU32_2ff8ExitPc (pc : BitVec 64) : Prop := pcInList [0x12760] pc

def readU32_2ff8Writes (register : Register) : Prop :=
  stepBookkeeping register ∨ register = x10 ∨ register = x12 ∨
    register = x13 ∨ register = x14

def readU32MachineValue (v0 v1 v2 v3 : Nat) : BitVec 64 :=
  let z0 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v0)
  let z1 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v1)
  let z2 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v2)
  let s3 : BitVec 64 := sign_extend (m := 64) (BitVec.ofNat 8 v3)
  let sh1 := Sail.shift_bits_left z1
    (Sail.BitVec.extractLsb (8#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let sh2 := Sail.shift_bits_left z2
    (Sail.BitVec.extractLsb (16#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let sh3 := Sail.shift_bits_left s3
    (Sail.BitVec.extractLsb (24#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  (sh3 ||| sh2) ||| (sh1 ||| z0)

private theorem readU32LoadUnsignedStep (stepNo pc offset : Nat) (state : State)
    (rs1 rd : regidx) (destination : Register) (result : RegisterType destination)
    (value baseAddress : Nat)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (rep : UIntRep 1 state.mem (baseAddress + offset) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (fits : baseAddress + offset < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (BitVec.ofNat 12 offset, rs1, rd, true, 1)))
    (baseRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs1) premise premise (BitVec.ofNat 64 baseAddress))
    (write : ∀ premise : State, Runs (wX_bits rd (zero_extend (m := 64) (BitVec.ofNat 8 value)))
      premise ({ premise with regs := premise.regs.insert destination result } : State) ())
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
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination
        result) false := by
  exact configuredByteLoadStep stepNo pc state (BitVec.ofNat 12 offset) rs1 rd destination
    baseAddress offset value result byte0 byte1 byte2 byte3 configured atPc rep pma notMMIO fits
    loaded addressEq baseRun write (by simpa using decode) (pcFits := site.pcFits)
    (pcAligned := site.pcAligned) (destinationNotNextPc := destinationNotNextPc)
    (destinationNotHart := destinationNotHart)
    (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired) (base := baseEncoding)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)

private theorem readU32LoadSignedStep (stepNo pc offset : Nat) (state : State)
    (rs1 rd : regidx) (destination : Register) (result : RegisterType destination)
    (value baseAddress : Nat)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (rep : UIntRep 1 state.mem (baseAddress + offset) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (fits : baseAddress + offset < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (BitVec.ofNat 12 offset, rs1, rd, false, 1)))
    (baseRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs1) premise premise (BitVec.ofNat 64 baseAddress))
    (write : ∀ premise : State, Runs (wX_bits rd (sign_extend (m := 64) (BitVec.ofNat 8 value)))
      premise ({ premise with regs := premise.regs.insert destination result } : State) ())
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
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination
        result) false := by
  exact configuredSignedByteLoadStep stepNo pc state (BitVec.ofNat 12 offset) rs1 rd destination
    baseAddress offset value result byte0 byte1 byte2 byte3 configured atPc rep pma notMMIO fits
    loaded addressEq baseRun write (by simpa using decode) (pcFits := site.pcFits)
    (pcAligned := site.pcAligned) (destinationNotNextPc := destinationNotNextPc)
    (destinationNotHart := destinationNotHart)
    (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired) (base := baseEncoding)
    (read0 := site.read0) (read1 := site.read1) (read2 := site.read2) (read3 := site.read3)

private theorem readU32SlliStep (stepNo pc : Nat) (state : State) (shamt : BitVec 6)
    (sourceRegister : regidx) (destination : Register) (result : RegisterType destination)
    (source : BitVec 64)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.SHIFTIOP (shamt, sourceRegister, sourceRegister, .SLLI)))
    (readRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits sourceRegister) premise premise source)
    (writeRun : ∀ premise : State, Runs (wX_bits sourceRegister
      (Sail.shift_bits_left source
        (Sail.BitVec.extractLsb shamt (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))
      premise ({ premise with regs := premise.regs.insert destination result } : State) ())
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination
        result) false := by
  apply configuredSlliStep stepNo pc state shamt sourceRegister sourceRegister destination result source
    byte0 byte1 byte2 byte3 configured atPc loaded (by simpa using decode) readRun writeRun
    site destinationNotNextPc destinationNotHart destinationNotIncrement destinationNotRetired
    baseEncoding

private theorem readU32OrStep (stepNo pc : Nat) (state : State)
    (rs2 rs1 rd : regidx) (destination : Register) (result : RegisterType destination)
    (left right : BitVec 64)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (leftRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs1) premise premise left)
    (rightRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs2) premise premise right)
    (writeRun : ∀ premise : State, Runs (wX_bits rd (left ||| right)) premise
      { premise with regs := premise.regs.insert destination result } ())
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.RTYPE (rs2, rs1, rd, .OR)))
    (site : ExactInstructionSite pc byte0 byte1 byte2 byte3)
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false := by
  apply configuredOrStep stepNo pc state rs2 rs1 rd destination result left right
    byte0 byte1 byte2 byte3 configured atPc loaded (by simpa using decode)
    leftRun rightRun writeRun site destinationNotNextPc destinationNotHart destinationNotIncrement
    destinationNotRetired baseEncoding

/-- Declare one exact unsigned-byte load used by a standard `readU32` schedule. -/
macro "readU32UnsignedLoadSite(" name:ident ";" pc:term "," offset:term ";"
    baseIndex:term "," baseRegister:term "," baseRead:term ";"
    destinationIndex:term "," destination:term "," destinationWrite:term ";"
    byte0:term "," byte1:term "," byte2:term "," byte3:term ")" : command =>
  `(private theorem $name (stepNo : Nat) (state : State) (baseAddress value : Nat)
      (configured : ConfiguredMachinePre EndpointMachinePc state)
      (atPc : state.regs.get? PC = some (BitVec.ofNat 64 $pc))
      (base : state.regs.get? $baseRegister = some (BitVec.ofNat 64 baseAddress))
      (rep : UIntRep 1 state.mem (baseAddress + $offset) value)
      (pma : LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + $offset)) 1)
      (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + $offset)) 1)
      (fits : baseAddress + $offset < 2 ^ 64)
      (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 $pc) retired $destination
          (zero_extend (m := 64) (BitVec.ofNat 8 value))) false := by
      exact readU32LoadUnsignedStep stepNo $pc $offset state $baseIndex $destinationIndex
        $destination (zero_extend (m := 64) (BitVec.ofNat 8 value)) value baseAddress
        $byte0 $byte1 $byte2 $byte3 configured atPc rep pma notMMIO fits loaded
        (by configured_decode configured)
        (fun premise writes => $baseRead premise _
          ((writes $baseRegister (by simp [stepBookkeeping])).trans base))
        (fun premise => $destinationWrite premise _)
        (by constructor <;> native_decide) (by decide) (by decide) (by decide) (by decide)
        (by rfl)
        (by rw [show sign_extend (m := 64) (BitVec.ofNat 12 $offset) =
              BitVec.ofNat 64 $offset by native_decide]
            exact ofNatAdd baseAddress $offset fits))

/-- Declare one exact left-shift used by a standard `readU32` schedule. -/
macro "readU32SlliSite(" name:ident ";" pc:term "," shift:term ";"
    registerIndex:term "," register:term "," registerRead:term "," registerWrite:term ";"
    byte0:term "," byte1:term "," byte2:term "," byte3:term ")" : command =>
  `(private theorem $name (stepNo : Nat) (state : State) (source : BitVec 64)
      (configured : ConfiguredMachinePre EndpointMachinePc state)
      (atPc : state.regs.get? PC = some (BitVec.ofNat 64 $pc))
      (holds : state.regs.get? $register = some source)
      (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 $pc) retired $register
          (Sail.shift_bits_left source
            (Sail.BitVec.extractLsb (BitVec.ofNat 6 $shift)
              (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) false := by
      exact readU32SlliStep stepNo $pc state (BitVec.ofNat 6 $shift) $registerIndex
        $register _ source $byte0 $byte1 $byte2 $byte3 configured atPc loaded
        (by configured_decode configured)
        (fun premise writes => $registerRead premise source
          ((writes $register (by simp [stepBookkeeping])).trans holds))
        (fun premise => $registerWrite premise _) (by constructor <;> native_decide)
        (by decide) (by decide) (by decide) (by decide) (by rfl))

/-- Declare one exact register OR used by a standard `readU32` schedule. -/
macro "readU32OrSite(" name:ident ";" pc:term ";"
    leftIndex:term "," leftRegister:term "," leftRead:term ";"
    rightIndex:term "," rightRegister:term "," rightRead:term ";"
    destinationIndex:term "," destination:term "," destinationWrite:term ";"
    byte0:term "," byte1:term "," byte2:term "," byte3:term ")" : command =>
  `(private theorem $name (stepNo : Nat) (state : State) (left right : BitVec 64)
      (configured : ConfiguredMachinePre EndpointMachinePc state)
      (atPc : state.regs.get? PC = some (BitVec.ofNat 64 $pc))
      (leftHolds : state.regs.get? $leftRegister = some left)
      (rightHolds : state.regs.get? $rightRegister = some right)
      (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 $pc) retired $destination
          (left ||| right)) false := by
      exact readU32OrStep stepNo $pc state $rightIndex $leftIndex $destinationIndex
        $destination _ left right $byte0 $byte1 $byte2 $byte3 configured atPc
        (fun premise writes => $leftRead premise left
          ((writes $leftRegister (by simp [stepBookkeeping])).trans leftHolds))
        (fun premise writes => $rightRead premise right
          ((writes $rightRegister (by simp [stepBookkeeping])).trans rightHolds))
        (fun premise => $destinationWrite premise _) loaded
        (by configured_decode configured) (by constructor <;> native_decide)
        (by decide) (by decide) (by decide) (by decide) (by rfl))

private theorem readU32_2ff8InstructionDisjoint :
    RegSet.Disjoint instructionPreserved readU32_2ff8Writes := by
  intro register preserved writes
  rcases writes with writes | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 writes
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem readU32_2ff8PlatformDisjoint :
    RegSet.Disjoint platformPreserved readU32_2ff8Writes := by
  intro register preserved writes
  rcases writes with writes | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved writes
  all_goals simp [platformPreserved] at preserved

/-- Exact 11-step trace for `fi:1:2ff8`, including its signed high-byte load. -/
theorem readU32_2ff8Run (fromStep baseAddress v0 v1 v2 v3 : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12734))
    (base : state.regs.get? x18 = some (BitVec.ofNat 64 baseAddress))
    (rep0 : UIntRep 1 state.mem (baseAddress + 2) v0)
    (rep1 : UIntRep 1 state.mem (baseAddress + 3) v1)
    (rep2 : UIntRep 1 state.mem (baseAddress + 4) v2)
    (rep3 : UIntRep 1 state.mem (baseAddress + 5) v3)
    (pma : ∀ offset, offset < 4 →
      LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + 2 + offset)) 1)
    (notMMIO : ∀ offset, offset < 4 →
      LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 2 + offset)) 1)
    (sourceFits : baseAddress + 2 + 4 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after, Seg readU32_2ff8OwnPc readU32_2ff8ExitPc (fun _ _ _ _ _ => False)
      readU32_2ff8Writes noMemory
      [⟨x12, 16⟩, ⟨x10, readU32MachineValue v0 v1 v2 v3⟩]
      fromStep 11 state after (BitVec.ofNat 64 0x12760) := by
  let z0 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v0)
  let z1 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v1)
  let z2 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v2)
  let s3 : BitVec 64 := sign_extend (m := 64) (BitVec.ofNat 8 v3)
  let sh1 := Sail.shift_bits_left z1
    (Sail.BitVec.extractLsb (8#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let lo := sh1 ||| z0
  let sh2 := Sail.shift_bits_left z2
    (Sail.BitVec.extractLsb (16#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let sh3 := Sail.shift_bits_left s3
    (Sail.BitVec.extractLsb (24#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let hi := sh3 ||| sh2
  let result := hi ||| lo
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  have seg0 := Seg.nil readU32_2ff8OwnPc readU32_2ff8ExitPc (fun _ _ _ _ _ => False)
    readU32_2ff8Writes noMemory fromStep ⟨retired, retiredRead⟩ atPc
  have configuredOfSeg {kv n cur pc}
      (seg : Seg readU32_2ff8OwnPc readU32_2ff8ExitPc (fun _ _ _ _ _ => False)
        readU32_2ff8Writes noMemory kv fromStep n state cur pc) :
      ConfiguredMachinePre EndpointMachinePc cur :=
    configuredMachinePre_of_readSeg configured readU32_2ff8InstructionDisjoint seg
  have baseOfSeg {kv n cur pc}
      (seg : Seg readU32_2ff8OwnPc readU32_2ff8ExitPc (fun _ _ _ _ _ => False)
        readU32_2ff8Writes noMemory kv fromStep n state cur pc) :
      cur.regs.get? x18 = some (BitVec.ofNat 64 baseAddress) :=
    registerValue_of_readSeg seg (by simp [readU32_2ff8Writes, stepBookkeeping]) base
  have repOfSeg {kv n cur pc offset value}
      (seg : Seg readU32_2ff8OwnPc readU32_2ff8ExitPc (fun _ _ _ _ _ => False)
        readU32_2ff8Writes noMemory kv fromStep n state cur pc)
      (rep : UIntRep 1 state.mem (baseAddress + offset) value) :
      UIntRep 1 cur.mem (baseAddress + offset) value :=
    uintRep_of_readSeg seg rep
  have pmaOfSeg {kv n cur pc offset}
      (seg : Seg readU32_2ff8OwnPc readU32_2ff8ExitPc (fun _ _ _ _ _ => False)
        readU32_2ff8Writes noMemory kv fromStep n state cur pc)
      (bound : offset < 4) :
      LoadPmaAllows cur (BitVec.ofNat 64 (baseAddress + 2 + offset)) 1 :=
    loadPmaAllows_of_readSeg seg readU32_2ff8PlatformDisjoint (pma offset bound)
  have loadedOfSeg {kv n cur pc}
      (seg : Seg readU32_2ff8OwnPc readU32_2ff8ExitPc (fun _ _ _ _ _ => False)
        readU32_2ff8Writes noMemory kv fromStep n state cur pc) :
      Artifacts.programImage.fileBytesLoadedFaithfully cur.mem :=
    loadedFaithfully_of_readSeg seg loaded
  obtain ⟨m1, seg1⟩ := seg0.step (by owned_pc [readU32_2ff8OwnPc, pcInList])
    (by owned_pc [readU32_2ff8ExitPc, pcInList]) x10 z1 0x12738
    (readU32LoadUnsignedStep fromStep 0x12734 3 state (.Regidx 18#5) (.Regidx 10#5) x10 z1 v1
      baseAddress 0x03 0x45 0x39 0x00 configured atPc rep1 (pma 1 (by omega))
      (notMMIO 1 (by omega)) (by omega) loaded (by configured_decode configured)
      (fun premise writes => rX_x18_run premise _
        ((writes x18 (by simp [stepBookkeeping])).trans base))
      (fun premise => wX_x10_run premise z1) (by constructor <;> native_decide)
      (by decide) (by decide) (by decide) (by decide) (by rfl)
      (by rw [show sign_extend (m := 64) (3#12) = 3#64 by native_decide];
          exact ofNatAdd baseAddress 3 (by omega)))
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨m2, seg2⟩ := seg1.step (by owned_pc [readU32_2ff8OwnPc, pcInList])
    (by owned_pc [readU32_2ff8ExitPc, pcInList]) x12 z0 0x1273c
    (readU32LoadUnsignedStep (fromStep + 1) 0x12738 2 m1 (.Regidx 18#5)
      (.Regidx 12#5) x12 z0 v0 baseAddress 0x03 0x46 0x29 0x00
      (configuredOfSeg seg1) seg1.atPc
      (repOfSeg seg1 rep0) (by simpa [Nat.add_assoc] using pmaOfSeg seg1 (offset := 0) (by omega))
      (by simpa [Nat.add_assoc] using notMMIO 0 (by omega)) (by omega) (loadedOfSeg seg1)
      (by configured_decode (configuredOfSeg seg1))
      (fun premise writes => rX_x18_run premise _
        ((writes x18 (by simp [stepBookkeeping])).trans (baseOfSeg seg1)))
      (fun premise => wX_x12_run premise z0)
      (by constructor <;> native_decide) (by decide) (by decide) (by decide) (by decide) (by rfl)
      (by rw [show sign_extend (m := 64) (2#12) = 2#64 by native_decide];
          exact ofNatAdd baseAddress 2 (by omega)))
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inl rfl)))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨m3, seg3⟩ := seg2.step (by owned_pc [readU32_2ff8OwnPc, pcInList])
    (by owned_pc [readU32_2ff8ExitPc, pcInList]) x13 z2 0x12740
    (readU32LoadUnsignedStep (fromStep + 2) 0x1273c 4 m2 (.Regidx 18#5)
      (.Regidx 13#5) x13 z2 v2 baseAddress 0x83 0x46 0x49 0x00
      (configuredOfSeg seg2) seg2.atPc
      (repOfSeg seg2 rep2) (by simpa [Nat.add_assoc] using pmaOfSeg seg2 (offset := 2) (by omega))
      (by simpa [Nat.add_assoc] using notMMIO 2 (by omega)) (by omega) (loadedOfSeg seg2)
      (by configured_decode (configuredOfSeg seg2))
      (fun premise writes => rX_x18_run premise _
        ((writes x18 (by simp [stepBookkeeping])).trans (baseOfSeg seg2)))
      (fun premise => wX_x13_run premise z2)
      (by constructor <;> native_decide) (by decide) (by decide) (by decide) (by decide) (by rfl)
      (by rw [show sign_extend (m := 64) (4#12) = 4#64 by native_decide];
          exact ofNatAdd baseAddress 4 (by omega)))
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨m4, seg4⟩ := seg3.step (by owned_pc [readU32_2ff8OwnPc, pcInList])
    (by owned_pc [readU32_2ff8ExitPc, pcInList]) x14 s3 0x12744
    (readU32LoadSignedStep (fromStep + 3) 0x12740 5 m3 (.Regidx 18#5)
      (.Regidx 14#5) x14 s3 v3 baseAddress 0x03 0x07 0x59 0x00
      (configuredOfSeg seg3) seg3.atPc
      (repOfSeg seg3 rep3) (by simpa [Nat.add_assoc] using pmaOfSeg seg3 (offset := 3) (by omega))
      (by simpa [Nat.add_assoc] using notMMIO 3 (by omega)) (by omega) (loadedOfSeg seg3)
      (by configured_decode (configuredOfSeg seg3))
      (fun premise writes => rX_x18_run premise _
        ((writes x18 (by simp [stepBookkeeping])).trans (baseOfSeg seg3)))
      (fun premise => wX_x14_run premise s3)
      (by constructor <;> native_decide) (by decide) (by decide) (by decide) (by decide) (by rfl)
      (by rw [show sign_extend (m := 64) (5#12) = 5#64 by native_decide];
          exact ofNatAdd baseAddress 5 (by omega)))
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have seg4' := seg4.forget
    (kv' := [⟨x14, s3⟩, ⟨x13, z2⟩, ⟨x12, z0⟩]) (by simp)
  obtain ⟨m5, seg5⟩ := seg4'.step (by owned_pc [readU32_2ff8OwnPc, pcInList])
    (by owned_pc [readU32_2ff8ExitPc, pcInList]) x10 sh1 0x12748
    (readU32SlliStep (fromStep + 4) 0x12744 m4 8 (.Regidx 10#5) x10 sh1 z1
      0x13 0x15 0x85 0x00 (configuredOfSeg seg4') seg4'.atPc (loadedOfSeg seg4')
      (by configured_decode (configuredOfSeg seg4'))
      (fun premise writes => rX_x10_run premise z1
        ((writes x10 (by simp [stepBookkeeping])).trans (seg4.reg x10 z1 (by simp))))
      (fun premise => wX_x10_run premise sh1) (by constructor <;> native_decide)
      (by decide) (by decide) (by decide) (by decide) (by rfl))
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨r6, run6⟩ := readU32OrStep (fromStep + 5) 0x12748 m5
    (.Regidx 12#5) (.Regidx 10#5) (.Regidx 10#5) x10 lo sh1 z0
    0x33 0x65 0xc5 0x00 (configuredOfSeg seg5) seg5.atPc
    (fun premise writes => rX_x10_run premise sh1
      ((writes x10 (by simp [stepBookkeeping])).trans (seg5.reg x10 sh1 (by simp))))
    (fun premise writes => rX_x12_run premise z0
      ((writes x12 (by simp [stepBookkeeping])).trans (seg5.reg x12 z0 (by simp))))
    (fun premise => wX_x10_run premise lo) (loadedOfSeg seg5)
    (by configured_decode (configuredOfSeg seg5)) (by constructor <;> native_decide)
    (by decide) (by decide) (by decide) (by decide) (by rfl)
  have seg5' := seg5.forget
    (kv' := [⟨x14, s3⟩, ⟨x13, z2⟩, ⟨x12, z0⟩]) (by simp)
  obtain ⟨m6, seg6⟩ := seg5'.step (by owned_pc [readU32_2ff8OwnPc, pcInList])
    (by owned_pc [readU32_2ff8ExitPc, pcInList]) x10 lo 0x1274c ⟨r6, run6⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨r7, run7⟩ := readU32SlliStep (fromStep + 6) 0x1274c m6 16
    (.Regidx 13#5) x13 sh2 z2 0x93 0x96 0x06 0x01 (configuredOfSeg seg6)
    seg6.atPc (loadedOfSeg seg6) (by configured_decode (configuredOfSeg seg6))
    (fun premise writes => rX_x13_run premise z2
      ((writes x13 (by simp [stepBookkeeping])).trans (seg6.reg x13 z2 (by simp))))
    (fun premise => wX_x13_run premise sh2) (by constructor <;> native_decide)
    (by decide) (by decide) (by decide) (by decide) (by rfl)
  have seg6' := seg6.forget
    (kv' := [⟨x10, lo⟩, ⟨x14, s3⟩, ⟨x12, z0⟩]) (by simp)
  obtain ⟨m7, seg7⟩ := seg6'.step (by owned_pc [readU32_2ff8OwnPc, pcInList])
    (by owned_pc [readU32_2ff8ExitPc, pcInList]) x13 sh2 0x12750 ⟨r7, run7⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨r8, run8⟩ := readU32SlliStep (fromStep + 7) 0x12750 m7 24
    (.Regidx 14#5) x14 sh3 s3 0x13 0x17 0x87 0x01 (configuredOfSeg seg7)
    seg7.atPc (loadedOfSeg seg7) (by configured_decode (configuredOfSeg seg7))
    (fun premise writes => rX_x14_run premise s3
      ((writes x14 (by simp [stepBookkeeping])).trans (seg7.reg x14 s3 (by simp))))
    (fun premise => wX_x14_run premise sh3) (by constructor <;> native_decide)
    (by decide) (by decide) (by decide) (by decide) (by rfl)
  have seg7' := seg7.forget
    (kv' := [⟨x13, sh2⟩, ⟨x10, lo⟩, ⟨x12, z0⟩]) (by simp)
  obtain ⟨m8, seg8⟩ := seg7'.step (by owned_pc [readU32_2ff8OwnPc, pcInList])
    (by owned_pc [readU32_2ff8ExitPc, pcInList]) x14 sh3 0x12754 ⟨r8, run8⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨r9, run9⟩ := readU32OrStep (fromStep + 8) 0x12754 m8
    (.Regidx 13#5) (.Regidx 14#5) (.Regidx 13#5) x13 hi sh3 sh2
    0xb3 0x66 0xd7 0x00 (configuredOfSeg seg8) seg8.atPc
    (fun premise writes => rX_x14_run premise sh3
      ((writes x14 (by simp [stepBookkeeping])).trans (seg8.reg x14 sh3 (by simp))))
    (fun premise writes => rX_x13_run premise sh2
      ((writes x13 (by simp [stepBookkeeping])).trans (seg8.reg x13 sh2 (by simp))))
    (fun premise => wX_x13_run premise hi) (loadedOfSeg seg8)
    (by configured_decode (configuredOfSeg seg8)) (by constructor <;> native_decide)
    (by decide) (by decide) (by decide) (by decide) (by rfl)
  have seg8' := seg8.forget
    (kv' := [⟨x14, sh3⟩, ⟨x10, lo⟩, ⟨x12, z0⟩]) (by simp)
  obtain ⟨m9, seg9⟩ := seg8'.step (by owned_pc [readU32_2ff8OwnPc, pcInList])
    (by owned_pc [readU32_2ff8ExitPc, pcInList]) x13 hi 0x12758 ⟨r9, run9⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨r10, run10⟩ := readU32OrStep (fromStep + 9) 0x12758 m9
    (.Regidx 10#5) (.Regidx 13#5) (.Regidx 10#5) x10 result hi lo
    0x33 0xe5 0xa6 0x00 (configuredOfSeg seg9) seg9.atPc
    (fun premise writes => rX_x13_run premise hi
      ((writes x13 (by simp [stepBookkeeping])).trans (seg9.reg x13 hi (by simp))))
    (fun premise writes => rX_x10_run premise lo
      ((writes x10 (by simp [stepBookkeeping])).trans (seg9.reg x10 lo (by simp))))
    (fun premise => wX_x10_run premise result) (loadedOfSeg seg9)
    (by configured_decode (configuredOfSeg seg9)) (by constructor <;> native_decide)
    (by decide) (by decide) (by decide) (by decide) (by rfl)
  have seg9' := seg9.forget
    (kv' := [⟨x13, hi⟩, ⟨x14, sh3⟩, ⟨x12, z0⟩]) (by simp)
  obtain ⟨m10, seg10⟩ := seg9'.step (by owned_pc [readU32_2ff8OwnPc, pcInList])
    (by owned_pc [readU32_2ff8ExitPc, pcInList]) x10 result 0x1275c ⟨r10, run10⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement m10) 0x1275c
  have execute : Runs (execute (.ITYPE (16, .Regidx 0#5, .Regidx 12#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x12 16 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 16 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    simpa using execute_ITYPE_addi_run premise _ 16 (.Regidx 0#5) (.Regidx 12#5) 0
      (rX_x0_run premise) (wX_x12_run premise 16)
  obtain ⟨r11, run11⟩ := configuredRegisterWriteStep (fromStep + 10) 0x1275c m10 x12 16
    (.ITYPE (16, .Regidx 0#5, .Regidx 12#5, .ADDI)) 0x13 0x06 0x00 0x01
    (configuredOfSeg seg10) seg10.atPc (loadedOfSeg seg10)
    (by configured_decode (configuredOfSeg seg10)) execute (base := by rfl)
  have seg10' := seg10.forget (kv' := [⟨x10, result⟩]) (by simp)
  obtain ⟨after, seg11⟩ := seg10'.step (by owned_pc [readU32_2ff8OwnPc, pcInList])
    (by owned_pc [readU32_2ff8ExitPc, pcInList]) x12 16 0x12760 ⟨r11, run11⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inl rfl)))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  exact ⟨after, by simpa [readU32MachineValue, z0, z1, z2, s3, sh1, sh2, sh3,
    lo, hi, result] using seg11⟩

/-! ## Shared standard unsigned `readU32` schedule -/

/-- Ten consecutive instructions in the standard unsigned `readU32` schedule. -/
def standardReadU32OwnPc (start : Nat) (pc : BitVec 64) : Prop :=
  pcInList [start, start + 4, start + 8, start + 12, start + 16,
    start + 20, start + 24, start + 28, start + 32, start + 36] pc

/-- The fall-through PC after the standard unsigned `readU32` schedule. -/
def standardReadU32ExitPc (start : Nat) (pc : BitVec 64) : Prop :=
  pcInList [start + 40] pc

/-- The four data registers and the common step bookkeeping registers. -/
def standardReadU32Writes (first second third fourth : Register) (register : Register) : Prop :=
  stepBookkeeping register ∨ register = first ∨ register = second ∨
    register = third ∨ register = fourth

/-- The standard schedule preserves every instruction register outside its four data registers. -/
theorem standardReadU32InstructionDisjoint (first second third fourth : Register)
    (firstNotPreserved : ¬instructionPreserved first)
    (secondNotPreserved : ¬instructionPreserved second)
    (thirdNotPreserved : ¬instructionPreserved third)
    (fourthNotPreserved : ¬instructionPreserved fourth) :
    RegSet.Disjoint instructionPreserved
      (standardReadU32Writes first second third fourth) := by
  intro register preserved writes
  rcases writes with writes | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 writes
  · exact firstNotPreserved preserved
  · exact secondNotPreserved preserved
  · exact thirdNotPreserved preserved
  · exact fourthNotPreserved preserved

/-- The standard schedule preserves every platform register outside its four data registers. -/
theorem standardReadU32PlatformDisjoint (first second third fourth : Register)
    (firstNotPreserved : ¬platformPreserved first)
    (secondNotPreserved : ¬platformPreserved second)
    (thirdNotPreserved : ¬platformPreserved third)
    (fourthNotPreserved : ¬platformPreserved fourth) :
    RegSet.Disjoint platformPreserved
      (standardReadU32Writes first second third fourth) := by
  intro register preserved writes
  rcases writes with writes | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved writes
  · exact firstNotPreserved preserved
  · exact secondNotPreserved preserved
  · exact thirdNotPreserved preserved
  · exact fourthNotPreserved preserved

/-- Declare the PC predicates, write frame, and frame-disjointness facts for one standard site. -/
macro "standardReadU32Frame(" own:ident "," exit:ident "," writes:ident ","
    instructionDisjoint:ident "," platformDisjoint:ident ";"
    start:term ";" first:term "," second:term "," third:term "," fourth:term ")" : command =>
  `(section
    def $own (pc : BitVec 64) : Prop := standardReadU32OwnPc $start pc

    def $exit (pc : BitVec 64) : Prop := standardReadU32ExitPc $start pc

    def $writes (register : Register) : Prop :=
      standardReadU32Writes $first $second $third $fourth register

    private theorem $instructionDisjoint :
        RegSet.Disjoint instructionPreserved $writes :=
      standardReadU32InstructionDisjoint $first $second $third $fourth
        (by simp [instructionPreserved, platformPreserved])
        (by simp [instructionPreserved, platformPreserved])
        (by simp [instructionPreserved, platformPreserved])
        (by simp [instructionPreserved, platformPreserved])

    private theorem $platformDisjoint :
        RegSet.Disjoint platformPreserved $writes :=
      standardReadU32PlatformDisjoint $first $second $third $fourth
        (by simp [platformPreserved]) (by simp [platformPreserved])
        (by simp [platformPreserved]) (by simp [platformPreserved])
    end)

/-! ## `fi:1:3064`: standard unsigned `readU32` schedule -/

standardReadU32Frame(readU32_3064OwnPc, readU32_3064ExitPc, readU32_3064Writes,
  readU32_3064InstructionDisjoint, readU32_3064PlatformDisjoint;
  0x128cc; x13, x14, x15, x16)

def readU32UnsignedMachineValue (v0 v1 v2 v3 : Nat) : BitVec 64 :=
  let z0 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v0)
  let z1 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v1)
  let z2 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v2)
  let z3 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 v3)
  let sh1 := Sail.shift_bits_left z1
    (Sail.BitVec.extractLsb (8#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let sh2 := Sail.shift_bits_left z2
    (Sail.BitVec.extractLsb (16#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  let sh3 := Sail.shift_bits_left z3
    (Sail.BitVec.extractLsb (24#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  (sh3 ||| sh2) ||| (sh1 ||| z0)

readU32UnsignedLoadSite(readU32_3064Load1; 0x128cc, 9;
  .Regidx 10#5, x10, rX_x10_run; .Regidx 13#5, x13, wX_x13_run;
  0x83, 0x46, 0x95, 0x00)
readU32UnsignedLoadSite(readU32_3064Load0; 0x128d0, 8;
  .Regidx 10#5, x10, rX_x10_run; .Regidx 14#5, x14, wX_x14_run;
  0x03, 0x47, 0x85, 0x00)
readU32UnsignedLoadSite(readU32_3064Load2; 0x128d4, 10;
  .Regidx 10#5, x10, rX_x10_run; .Regidx 15#5, x15, wX_x15_run;
  0x83, 0x47, 0xa5, 0x00)
readU32UnsignedLoadSite(readU32_3064Load3; 0x128d8, 11;
  .Regidx 10#5, x10, rX_x10_run; .Regidx 16#5, x16, wX_x16_run;
  0x03, 0x48, 0xb5, 0x00)
readU32SlliSite(readU32_3064Shift1; 0x128dc, 8;
  .Regidx 13#5, x13, rX_x13_run, wX_x13_run; 0x93, 0x96, 0x86, 0x00)
readU32OrSite(readU32_3064OrLow; 0x128e0;
  .Regidx 13#5, x13, rX_x13_run; .Regidx 14#5, x14, rX_x14_run;
  .Regidx 13#5, x13, wX_x13_run; 0xb3, 0xe6, 0xe6, 0x00)
readU32SlliSite(readU32_3064Shift2; 0x128e4, 16;
  .Regidx 15#5, x15, rX_x15_run, wX_x15_run; 0x93, 0x97, 0x07, 0x01)
readU32SlliSite(readU32_3064Shift3; 0x128e8, 24;
  .Regidx 16#5, x16, rX_x16_run, wX_x16_run; 0x13, 0x18, 0x88, 0x01)
readU32OrSite(readU32_3064OrHigh; 0x128ec;
  .Regidx 16#5, x16, rX_x16_run; .Regidx 15#5, x15, rX_x15_run;
  .Regidx 14#5, x14, wX_x14_run; 0x33, 0x67, 0xf8, 0x00)
readU32OrSite(readU32_3064OrResult; 0x128f0;
  .Regidx 14#5, x14, rX_x14_run; .Regidx 13#5, x13, rX_x13_run;
  .Regidx 13#5, x13, wX_x13_run; 0xb3, 0x66, 0xd7, 0x00)

/-- Compose one standard unsigned `readU32` schedule from its ten exact site theorems. -/
macro "standard_read_u32_compose " own:ident "," exit:ident "," writes:ident ","
    instructionDisjoint:ident "," platformDisjoint:ident ";"
    start:term "," finish:term "," baseOffset:term ";"
    first:term "," second:term "," third:term "," fourth:term ","
    highRegister:term "," resultRegister:term ";"
    load1:ident "," load0:ident "," load2:ident "," load3:ident ","
    shift1:ident "," orLow:ident "," shift2:ident "," shift3:ident ","
    orHigh:ident "," orResult:ident ";"
    fromStep:term "," baseAddress:term "," v0:term "," v1:term "," v2:term "," v3:term ","
    state:term "," configured:term "," atPc:term "," base:term ","
    rep0:term "," rep1:term "," rep2:term "," rep3:term ","
    pma:term "," notMMIO:term "," sourceFits:term "," loaded:term : term =>
  `(by
    let z0 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v0)
    let z1 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v1)
    let z2 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v2)
    let z3 : BitVec 64 := zero_extend (m := 64) (BitVec.ofNat 8 $v3)
    let sh1 := Sail.shift_bits_left z1
      (Sail.BitVec.extractLsb (8#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
    let lo := sh1 ||| z0
    let sh2 := Sail.shift_bits_left z2
      (Sail.BitVec.extractLsb (16#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
    let sh3 := Sail.shift_bits_left z3
      (Sail.BitVec.extractLsb (24#6) (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
    let hi := sh3 ||| sh2
    let result := hi ||| lo
    obtain ⟨retired, retiredRead⟩ := ($configured).retiredCounter
    have seg0 := Seg.nil $own $exit (fun _ _ _ _ _ => False) $writes noMemory
      $fromStep ⟨retired, retiredRead⟩ $atPc
    have configuredOfSeg {kv n cur pc}
        (seg : Seg $own $exit (fun _ _ _ _ _ => False) $writes noMemory kv
          $fromStep n $state cur pc) :=
      configuredMachinePre_of_readSeg $configured $instructionDisjoint seg
    have baseOfSeg {kv n cur pc}
        (seg : Seg $own $exit (fun _ _ _ _ _ => False) $writes noMemory kv
          $fromStep n $state cur pc) :=
      registerValue_of_readSeg seg
        (by unfold $writes; simp [standardReadU32Writes, stepBookkeeping]) $base
    have pmaOfSeg {kv n cur pc} (relative : Nat)
        (seg : Seg $own $exit (fun _ _ _ _ _ => False) $writes noMemory kv
          $fromStep n $state cur pc)
        (bound : relative < 4) :
        LoadPmaAllows cur
          (BitVec.ofNat 64 ($baseAddress + $baseOffset + relative)) 1 := by
      simpa [Nat.add_assoc] using
        loadPmaAllows_of_readSeg seg $platformDisjoint ($pma relative bound)
    have loadedOfSeg {kv n cur pc}
        (seg : Seg $own $exit (fun _ _ _ _ _ => False) $writes noMemory kv
          $fromStep n $state cur pc) :=
      loadedFaithfully_of_readSeg seg $loaded
    obtain ⟨m1, seg1⟩ := seg0.step
      (by unfold $own standardReadU32OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU32ExitPc pcInList; native_decide)
      $first z1 ($start + 4)
      ($load1 $fromStep $state $baseAddress $v1 $configured $atPc $base $rep1
        ($pma 1 (by omega)) ($notMMIO 1 (by omega))
        (by have := $sourceFits; omega) $loaded)
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU32Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨m2, seg2⟩ := seg1.step
      (by unfold $own standardReadU32OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU32ExitPc pcInList; native_decide)
      $second z0 ($start + 8)
      ($load0 ($fromStep + 1) m1 $baseAddress $v0 (configuredOfSeg seg1)
        seg1.atPc (baseOfSeg seg1)
        (by simpa using uintRep_of_readSeg seg1 $rep0)
        (pmaOfSeg 0 seg1 (by omega)) ($notMMIO 0 (by omega))
        (by have := $sourceFits; omega) (loadedOfSeg seg1))
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU32Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨m3, seg3⟩ := seg2.step
      (by unfold $own standardReadU32OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU32ExitPc pcInList; native_decide)
      $third z2 ($start + 12)
      ($load2 ($fromStep + 2) m2 $baseAddress $v2 (configuredOfSeg seg2)
        seg2.atPc (baseOfSeg seg2) (by simpa using uintRep_of_readSeg seg2 $rep2)
        (pmaOfSeg 2 seg2 (by omega)) ($notMMIO 2 (by omega))
        (by have := $sourceFits; omega) (loadedOfSeg seg2))
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU32Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨m4, seg4⟩ := seg3.step
      (by unfold $own standardReadU32OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU32ExitPc pcInList; native_decide)
      $fourth z3 ($start + 16)
      ($load3 ($fromStep + 3) m3 $baseAddress $v3 (configuredOfSeg seg3)
        seg3.atPc (baseOfSeg seg3) (by simpa using uintRep_of_readSeg seg3 $rep3)
        (pmaOfSeg 3 seg3 (by omega)) ($notMMIO 3 (by omega))
        (by have := $sourceFits; omega) (loadedOfSeg seg3))
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU32Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    have seg4' := seg4.forget
      (kv' := [⟨$fourth, z3⟩, ⟨$third, z2⟩, ⟨$second, z0⟩]) (by simp)
    obtain ⟨m5, seg5⟩ := seg4'.step
      (by unfold $own standardReadU32OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU32ExitPc pcInList; native_decide)
      $first sh1 ($start + 20)
      ($shift1 ($fromStep + 4) m4 z1 (configuredOfSeg seg4') seg4'.atPc
        (seg4.reg $first z1 (by simp)) (loadedOfSeg seg4'))
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU32Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r6, run6⟩ := $orLow ($fromStep + 5) m5 sh1 z0
      (configuredOfSeg seg5) seg5.atPc (seg5.reg $first sh1 (by simp))
      (seg5.reg $second z0 (by simp)) (loadedOfSeg seg5)
    have seg5' := seg5.forget
      (kv' := [⟨$fourth, z3⟩, ⟨$third, z2⟩, ⟨$second, z0⟩]) (by simp)
    obtain ⟨m6, seg6⟩ := seg5'.step
      (by unfold $own standardReadU32OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU32ExitPc pcInList; native_decide)
      $first lo ($start + 24) ⟨r6, run6⟩
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU32Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r7, run7⟩ := $shift2 ($fromStep + 6) m6 z2
      (configuredOfSeg seg6) seg6.atPc (seg6.reg $third z2 (by simp)) (loadedOfSeg seg6)
    have seg6' := seg6.forget
      (kv' := [⟨$first, lo⟩, ⟨$fourth, z3⟩, ⟨$second, z0⟩]) (by simp)
    obtain ⟨m7, seg7⟩ := seg6'.step
      (by unfold $own standardReadU32OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU32ExitPc pcInList; native_decide)
      $third sh2 ($start + 28) ⟨r7, run7⟩
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU32Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r8, run8⟩ := $shift3 ($fromStep + 7) m7 z3
      (configuredOfSeg seg7) seg7.atPc (seg7.reg $fourth z3 (by simp)) (loadedOfSeg seg7)
    have seg7' := seg7.forget
      (kv' := [⟨$third, sh2⟩, ⟨$first, lo⟩, ⟨$second, z0⟩]) (by simp)
    obtain ⟨m8, seg8⟩ := seg7'.step
      (by unfold $own standardReadU32OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU32ExitPc pcInList; native_decide)
      $fourth sh3 ($start + 32) ⟨r8, run8⟩
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU32Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r9, run9⟩ := $orHigh ($fromStep + 8) m8 sh3 sh2
      (configuredOfSeg seg8) seg8.atPc (seg8.reg $fourth sh3 (by simp))
      (seg8.reg $third sh2 (by simp)) (loadedOfSeg seg8)
    have seg8' := seg8.forget (kv' := [⟨$first, lo⟩]) (by simp)
    obtain ⟨m9, seg9⟩ := seg8'.step
      (by unfold $own standardReadU32OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU32ExitPc pcInList; native_decide)
      $highRegister hi ($start + 36) ⟨r9, run9⟩
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU32Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    obtain ⟨r10, run10⟩ := $orResult ($fromStep + 9) m9 hi lo
      (configuredOfSeg seg9) seg9.atPc (seg9.reg $highRegister hi (by simp))
      (seg9.reg $first lo (by simp)) (loadedOfSeg seg9)
    have seg9' := seg9.forget (kv' := []) (by simp)
    obtain ⟨after, seg10⟩ := seg9'.step
      (by unfold $own standardReadU32OwnPc pcInList; native_decide)
      (by unfold $exit standardReadU32ExitPc pcInList; native_decide)
      $resultRegister result $finish ⟨r10, run10⟩
      (by decide) (by intro r h; exact Or.inl h)
      (by unfold $writes; simp [standardReadU32Writes]) (by decide) (by decide)
      (by simp [RegsOutside, stepBookkeeping])
    have finalSeg := seg10.forget (kv' := [⟨$resultRegister, result⟩]) (by simp)
    exact ⟨after, by simpa [readU32UnsignedMachineValue, z0, z1, z2, z3,
      sh1, sh2, sh3, lo, hi, result] using finalSeg⟩)

/-- Exact ten-step standard unsigned `readU32` trace for `fi:1:3064`. -/
theorem readU32_3064Run (fromStep baseAddress v0 v1 v2 v3 : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x128cc))
    (base : state.regs.get? x10 = some (BitVec.ofNat 64 baseAddress))
    (rep0 : UIntRep 1 state.mem (baseAddress + 8) v0)
    (rep1 : UIntRep 1 state.mem (baseAddress + 9) v1)
    (rep2 : UIntRep 1 state.mem (baseAddress + 10) v2)
    (rep3 : UIntRep 1 state.mem (baseAddress + 11) v3)
    (pma : ∀ offset, offset < 4 →
      LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + 8 + offset)) 1)
    (notMMIO : ∀ offset, offset < 4 →
      LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + 8 + offset)) 1)
    (sourceFits : baseAddress + 8 + 4 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after, Seg readU32_3064OwnPc readU32_3064ExitPc (fun _ _ _ _ _ => False)
      readU32_3064Writes noMemory
      [⟨x13, readU32UnsignedMachineValue v0 v1 v2 v3⟩]
      fromStep 10 state after (BitVec.ofNat 64 0x128f4) :=
  standard_read_u32_compose readU32_3064OwnPc, readU32_3064ExitPc, readU32_3064Writes,
    readU32_3064InstructionDisjoint, readU32_3064PlatformDisjoint;
    0x128cc, 0x128f4, 8; x13, x14, x15, x16, x14, x13;
    readU32_3064Load1, readU32_3064Load0, readU32_3064Load2, readU32_3064Load3,
    readU32_3064Shift1, readU32_3064OrLow, readU32_3064Shift2, readU32_3064Shift3,
    readU32_3064OrHigh, readU32_3064OrResult;
    fromStep, baseAddress, v0, v1, v2, v3, state, configured, atPc, base,
    rep0, rep1, rep2, rep3, pma, notMMIO, sourceFits, loaded
/-! ## `fi:1:30e2`: second standard unsigned `readU32` schedule -/

standardReadU32Frame(readU32_30e2OwnPc, readU32_30e2ExitPc, readU32_30e2Writes,
  readU32_30e2InstructionDisjoint, readU32_30e2PlatformDisjoint;
  0x12944; x12, x14, x16, x17)

readU32UnsignedLoadSite(readU32_30e2Load1; 0x12944, 1;
  .Regidx 15#5, x15, rX_x15_run; .Regidx 12#5, x12, wX_x12_run;
  0x03, 0xc6, 0x17, 0x00)
readU32UnsignedLoadSite(readU32_30e2Load0; 0x12948, 0;
  .Regidx 15#5, x15, rX_x15_run; .Regidx 14#5, x14, wX_x14_run;
  0x03, 0xc7, 0x07, 0x00)
readU32UnsignedLoadSite(readU32_30e2Load2; 0x1294c, 2;
  .Regidx 15#5, x15, rX_x15_run; .Regidx 16#5, x16, wX_x16_run;
  0x03, 0xc8, 0x27, 0x00)
readU32UnsignedLoadSite(readU32_30e2Load3; 0x12950, 3;
  .Regidx 15#5, x15, rX_x15_run; .Regidx 17#5, x17, wX_x17_run;
  0x83, 0xc8, 0x37, 0x00)
readU32SlliSite(readU32_30e2Shift1; 0x12954, 8;
  .Regidx 12#5, x12, rX_x12_run, wX_x12_run; 0x13, 0x16, 0x86, 0x00)
readU32OrSite(readU32_30e2OrLow; 0x12958;
  .Regidx 12#5, x12, rX_x12_run; .Regidx 14#5, x14, rX_x14_run;
  .Regidx 12#5, x12, wX_x12_run; 0x33, 0x66, 0xe6, 0x00)
readU32SlliSite(readU32_30e2Shift2; 0x1295c, 16;
  .Regidx 16#5, x16, rX_x16_run, wX_x16_run; 0x13, 0x18, 0x08, 0x01)
readU32SlliSite(readU32_30e2Shift3; 0x12960, 24;
  .Regidx 17#5, x17, rX_x17_run, wX_x17_run; 0x93, 0x98, 0x88, 0x01)
readU32OrSite(readU32_30e2OrHigh; 0x12964;
  .Regidx 17#5, x17, rX_x17_run; .Regidx 16#5, x16, rX_x16_run;
  .Regidx 14#5, x14, wX_x14_run; 0x33, 0xe7, 0x08, 0x01)
readU32OrSite(readU32_30e2OrResult; 0x12968;
  .Regidx 14#5, x14, rX_x14_run; .Regidx 12#5, x12, rX_x12_run;
  .Regidx 14#5, x14, wX_x14_run; 0x33, 0x67, 0xc7, 0x00)

/-- Exact ten-step standard unsigned `readU32` trace for `fi:1:30e2`. -/
theorem readU32_30e2Run (fromStep baseAddress v0 v1 v2 v3 : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12944))
    (base : state.regs.get? x15 = some (BitVec.ofNat 64 baseAddress))
    (rep0 : UIntRep 1 state.mem baseAddress v0)
    (rep1 : UIntRep 1 state.mem (baseAddress + 1) v1)
    (rep2 : UIntRep 1 state.mem (baseAddress + 2) v2)
    (rep3 : UIntRep 1 state.mem (baseAddress + 3) v3)
    (pma : ∀ offset, offset < 4 →
      LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (notMMIO : ∀ offset, offset < 4 →
      LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (sourceFits : baseAddress + 4 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after, Seg readU32_30e2OwnPc readU32_30e2ExitPc (fun _ _ _ _ _ => False)
      readU32_30e2Writes noMemory
      [⟨x14, readU32UnsignedMachineValue v0 v1 v2 v3⟩]
      fromStep 10 state after (BitVec.ofNat 64 0x1296c) :=
  standard_read_u32_compose readU32_30e2OwnPc, readU32_30e2ExitPc, readU32_30e2Writes,
    readU32_30e2InstructionDisjoint, readU32_30e2PlatformDisjoint;
    0x12944, 0x1296c, 0; x12, x14, x16, x17, x14, x14;
    readU32_30e2Load1, readU32_30e2Load0, readU32_30e2Load2, readU32_30e2Load3,
    readU32_30e2Shift1, readU32_30e2OrLow, readU32_30e2Shift2, readU32_30e2Shift3,
    readU32_30e2OrHigh, readU32_30e2OrResult;
    fromStep, baseAddress, v0, v1, v2, v3, state, configured, atPc, base,
    rep0, rep1, rep2, rep3, pma, notMMIO, sourceFits, loaded

/-! ## `fi:1:3457`: third standard unsigned `readU32` schedule -/

standardReadU32Frame(readU32_3457OwnPc, readU32_3457ExitPc, readU32_3457Writes,
  readU32_3457InstructionDisjoint, readU32_3457PlatformDisjoint;
  0x12ff0; x11, x12, x13, x14)

readU32UnsignedLoadSite(readU32_3457Load1; 0x12ff0, 1;
  .Regidx 9#5, x9, rX_x9_run; .Regidx 11#5, x11, wX_x11_run;
  0x83, 0xc5, 0x14, 0x00)
readU32UnsignedLoadSite(readU32_3457Load0; 0x12ff4, 0;
  .Regidx 9#5, x9, rX_x9_run; .Regidx 12#5, x12, wX_x12_run;
  0x03, 0xc6, 0x04, 0x00)
readU32UnsignedLoadSite(readU32_3457Load2; 0x12ff8, 2;
  .Regidx 9#5, x9, rX_x9_run; .Regidx 13#5, x13, wX_x13_run;
  0x83, 0xc6, 0x24, 0x00)
readU32UnsignedLoadSite(readU32_3457Load3; 0x12ffc, 3;
  .Regidx 9#5, x9, rX_x9_run; .Regidx 14#5, x14, wX_x14_run;
  0x03, 0xc7, 0x34, 0x00)
readU32SlliSite(readU32_3457Shift1; 0x13000, 8;
  .Regidx 11#5, x11, rX_x11_run, wX_x11_run; 0x93, 0x95, 0x85, 0x00)
readU32OrSite(readU32_3457OrLow; 0x13004;
  .Regidx 11#5, x11, rX_x11_run; .Regidx 12#5, x12, rX_x12_run;
  .Regidx 11#5, x11, wX_x11_run; 0xb3, 0xe5, 0xc5, 0x00)
readU32SlliSite(readU32_3457Shift2; 0x13008, 16;
  .Regidx 13#5, x13, rX_x13_run, wX_x13_run; 0x93, 0x96, 0x06, 0x01)
readU32SlliSite(readU32_3457Shift3; 0x1300c, 24;
  .Regidx 14#5, x14, rX_x14_run, wX_x14_run; 0x13, 0x17, 0x87, 0x01)
readU32OrSite(readU32_3457OrHigh; 0x13010;
  .Regidx 14#5, x14, rX_x14_run; .Regidx 13#5, x13, rX_x13_run;
  .Regidx 13#5, x13, wX_x13_run; 0xb3, 0x66, 0xd7, 0x00)
readU32OrSite(readU32_3457OrResult; 0x13014;
  .Regidx 13#5, x13, rX_x13_run; .Regidx 11#5, x11, rX_x11_run;
  .Regidx 11#5, x11, wX_x11_run; 0xb3, 0xe5, 0xb6, 0x00)

/-- Exact ten-step standard unsigned `readU32` trace for `fi:1:3457`. -/
theorem readU32_3457Run (fromStep baseAddress v0 v1 v2 v3 : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12ff0))
    (base : state.regs.get? x9 = some (BitVec.ofNat 64 baseAddress))
    (rep0 : UIntRep 1 state.mem baseAddress v0)
    (rep1 : UIntRep 1 state.mem (baseAddress + 1) v1)
    (rep2 : UIntRep 1 state.mem (baseAddress + 2) v2)
    (rep3 : UIntRep 1 state.mem (baseAddress + 3) v3)
    (pma : ∀ offset, offset < 4 →
      LoadPmaAllows state (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (notMMIO : ∀ offset, offset < 4 →
      LoadMMIOAddressExcluded (BitVec.ofNat 64 (baseAddress + offset)) 1)
    (sourceFits : baseAddress + 4 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after, Seg readU32_3457OwnPc readU32_3457ExitPc (fun _ _ _ _ _ => False)
      readU32_3457Writes noMemory
      [⟨x11, readU32UnsignedMachineValue v0 v1 v2 v3⟩]
      fromStep 10 state after (BitVec.ofNat 64 0x13018) :=
  standard_read_u32_compose readU32_3457OwnPc, readU32_3457ExitPc, readU32_3457Writes,
    readU32_3457InstructionDisjoint, readU32_3457PlatformDisjoint;
    0x12ff0, 0x13018, 0; x11, x12, x13, x14, x13, x11;
    readU32_3457Load1, readU32_3457Load0, readU32_3457Load2, readU32_3457Load3,
    readU32_3457Shift1, readU32_3457OrLow, readU32_3457Shift2, readU32_3457Shift3,
    readU32_3457OrHigh, readU32_3457OrResult;
    fromStep, baseAddress, v0, v1, v2, v3, state, configured, atPc, base,
    rep0, rep1, rep2, rep3, pma, notMMIO, sourceFits, loaded

end BinaryFv.Zesu.MachineExecution
