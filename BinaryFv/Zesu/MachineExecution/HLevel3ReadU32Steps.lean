import BinaryFv.Zesu.MachineExecution.HLevel3MemReadIntSteps

/-!
# Exact steps for one Level 3 `ssz.readU32` instance

The inlined instance at `0x12c18` performs four unsigned-byte loads through `x18`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

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
    configured.mono (seg.agree instructionPreserved_disjoint) seg.retired
  have baseOfSeg {kv n cur pc}
      (seg : Seg readU32_3335OwnPc readU32_3335ExitPc (fun _ _ _ _ _ => False)
        readU32_3335Writes noMemory kv fromStep n state cur pc) :
      cur.regs.get? x18 = some (BitVec.ofNat 64 baseAddress) :=
    (seg.get x18 (by simp [readU32_3335Writes, stepBookkeeping])).trans base
  have repOfSeg {kv n cur pc offset value}
      (seg : Seg readU32_3335OwnPc readU32_3335ExitPc (fun _ _ _ _ _ => False)
        readU32_3335Writes noMemory kv fromStep n state cur pc)
      (rep : UIntRep 1 state.mem (baseAddress + offset) value) :
      UIntRep 1 cur.mem (baseAddress + offset) value := by
    rw [seg.memEq noMemory_empty]
    exact rep
  have pmaOfSeg {kv n cur pc offset}
      (seg : Seg readU32_3335OwnPc readU32_3335ExitPc (fun _ _ _ _ _ => False)
        readU32_3335Writes noMemory kv fromStep n state cur pc)
      (bound : offset < 4) :
      LoadPmaAllows cur (BitVec.ofNat 64 (baseAddress + 22 + offset)) 1 :=
    loadPmaAllows_of_agree (seg.agree platformDisjointWrites) (pma offset bound)
  have loadedOfSeg {kv n cur pc}
      (seg : Seg readU32_3335OwnPc readU32_3335ExitPc (fun _ _ _ _ _ => False)
        readU32_3335Writes noMemory kv fromStep n state cur pc) :
      Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
    rw [seg.memEq noMemory_empty]
    exact loaded
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

end BinaryFv.Zesu.MachineExecution
