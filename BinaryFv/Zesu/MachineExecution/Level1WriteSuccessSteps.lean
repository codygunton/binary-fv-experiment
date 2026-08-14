import BinaryFv.Zesu.MachineExecution.Level1DecodeInputSteps
import BinaryFv.Zesu.MachineExecution.Level2RuntimeLeaves
import BinaryFv.Zesu.MachineExecution.MemcpyProof

/-!
# Parent-owned `writeSuccess` steps

This module composes the optimized observation writer around the selected Level-2 encoder regions.
The ABI prologue reuses the shared configured `addi`/dword-store instruction adapters and `Seg`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.Binary BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

def writeSuccessParentPc (pc : BitVec 64) : Prop :=
  pcInRanges Elflings.writeSuccessOwnedPcRanges pc

def writeSuccessInitialExitPc (pc : BitVec 64) : Prop := pc = 0x101d4 ∨ pc = 0x14e00

private def writeSuccessSecondMemcpyExitPc (pc : BitVec 64) : Prop :=
  pc = 0x101d4 ∨ pc = 0x14e2c

private def writeSuccessFirstIntExitPc (pc : BitVec 64) : Prop :=
  pc = 0x15d10 ∨ pc = 0x14e94

private def writeSuccessIntCallExitPc (pc : BitVec 64) : Prop :=
  pc = 0x15d10

private def writeSuccessBytesCallExitPc (pc : BitVec 64) : Prop :=
  pc = 0x15c6c

private def writeSuccessByteListsCallExitPc (pc : BitVec 64) : Prop :=
  pc = 0x15c10

private def writeSuccessOptionalCallExitPc (pc : BitVec 64) : Prop :=
  pc = 0x15bc8

private def writeSuccessOutputSetupPc (pc : BitVec 64) : Prop :=
  writeSuccessParentPc pc ∨
    pcInRanges [(0x15730, 0x1573c)] pc

def writeSuccessParentWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x1 ∨ register = x2 ∨ register = x8 ∨
    register = x9 ∨ register = x10 ∨ register = x11 ∨ register = x12 ∨
    register = x13 ∨ register = x14 ∨ register = x15 ∨ register = x16 ∨
    register = x17 ∨ register = x18 ∨ register = x19 ∨ register = x20 ∨
    register = x21 ∨ register = x22 ∨ register = x23 ∨ register = x24 ∨
    register = x25 ∨ register = x26 ∨ register = x27 ∨ register = x28 ∨
    register = x29 ∨ register = x30 ∨ register = x31

def writeSuccessPrologueWrites : RegSet := writeSuccessParentWrites

def writeSuccessFrameMemory (args : WriteSuccessArgs) : Region :=
  byteRange (args.stackPointer - 0x880) 0x880

private def writeSuccessTransactionSetupMemory (args : WriteSuccessArgs) : Region := fun address =>
  byteRange (args.stackPointer - 0x7d0 + 104) 8 address ∨
  byteRange (args.stackPointer - 0x7d0 + 112) 8 address

private def writeSuccessSlotSetupMemory (args : WriteSuccessArgs) : Region := fun address =>
  byteRange (args.stackPointer - 0x7d0 + 0x658) 8 address ∨
  byteRange (args.stackPointer - 0x7d0 + 0x660) 8 address

def WriteSuccessIoFrame (before after : EndpointState) : Prop :=
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode

def WriteSuccessMemoryFrame (args : WriteSuccessArgs) (before after : State) : Prop :=
  WritesOnlyWithin (writeSuccessFrameMemory args) before after

private theorem writeSuccessChildFrame_mem_frame {stackPointer address : Nat}
    (lower : 0x880 ≤ stackPointer)
    (inside : byteRange (stackPointer - 0x7d0 - 16) 16 address) :
    byteRange (stackPointer - 0x880) 0x880 address := by
  rcases inside with ⟨insideLower, insideUpper⟩
  constructor
  · have frameLower : stackPointer - 0x880 ≤ stackPointer - 0x7e0 :=
      Nat.sub_le_sub_left (by decide : 0x7e0 ≤ 0x880) stackPointer
    have childLower : stackPointer - 0x7e0 = stackPointer - 0x7d0 - 16 := by omega
    rw [childLower] at frameLower
    exact Nat.le_trans frameLower insideLower
  · rw [Nat.sub_add_cancel lower]
    omega

private theorem writeSuccessChildFrame48_mem_frame {stackPointer address : Nat}
    (lower : 0x880 ≤ stackPointer)
    (inside : byteRange (stackPointer - 0x7d0 - 48) 48 address) :
    byteRange (stackPointer - 0x880) 0x880 address := by
  unfold byteRange at inside ⊢
  constructor
  · omega
  · rw [Nat.sub_add_cancel lower]
    omega

private theorem writeSuccessChildFrame64_mem_frame {stackPointer address : Nat}
    (lower : 0x880 ≤ stackPointer)
    (inside : byteRange (stackPointer - 0x7d0 - 64) 64 address) :
    byteRange (stackPointer - 0x880) 0x880 address := by
  unfold byteRange at inside ⊢
  constructor
  · omega
  · rw [Nat.sub_add_cancel lower]
    omega

private theorem writeSuccessChildFrame_writes_writerFrame {args : WriteSuccessArgs}
    {before after : State} (lower : 0x880 ≤ args.stackPointer)
    (writes : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 - 16) 16) before after) :
    WriteSuccessMemoryFrame args before after := by
  intro address outside
  exact writes address (fun inside => outside (writeSuccessChildFrame_mem_frame lower inside))

private theorem writeSuccessChildFrame48_writes_writerFrame {args : WriteSuccessArgs}
    {before after : State} (lower : 0x880 ≤ args.stackPointer)
    (writes : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 - 48) 48) before after) :
    WriteSuccessMemoryFrame args before after := by
  intro address outside
  exact writes address (fun inside => outside (writeSuccessChildFrame48_mem_frame lower inside))

private theorem writeSuccessChildFrame64_writes_writerFrame {args : WriteSuccessArgs}
    {before after : State} (lower : 0x880 ≤ args.stackPointer)
    (writes : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 - 64) 64) before after) :
    WriteSuccessMemoryFrame args before after := by
  intro address outside
  exact writes address (fun inside => outside (writeSuccessChildFrame64_mem_frame lower inside))

private theorem writeSuccessChildStackFits {stackPointer : Nat} (lower : 0x880 ≤ stackPointer) :
    16 ≤ stackPointer - 0x7d0 := by
  apply Nat.le_sub_of_add_le
  exact Nat.le_trans (by decide : 16 + 0x7d0 ≤ 0x880) lower

private theorem writeSuccessChild16_in_child48 {stackPointer address : Nat}
    (lower : 0x880 ≤ stackPointer)
    (inside : byteRange (stackPointer - 0x7d0 - 16) 16 address) :
    byteRange (stackPointer - 0x7d0 - 48) 48 address := by
  unfold byteRange at inside ⊢
  have fit : 48 ≤ stackPointer - 0x7d0 := by
    apply Nat.le_sub_of_add_le
    exact Nat.le_trans (by decide : 48 + 0x7d0 ≤ 0x880) lower
  constructor
  · exact Nat.le_trans (Nat.sub_le_sub_left (by decide : 16 ≤ 48) _) inside.1
  · rw [Nat.sub_add_cancel fit]
    rw [Nat.sub_add_cancel (Nat.le_trans (by decide : 16 ≤ 48) fit)] at inside
    exact inside.2

private theorem writeSuccessChildStackBound {stackPointer : Nat} (upper : stackPointer < 2 ^ 64) :
    stackPointer - 0x7d0 < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.sub_le stackPointer 0x7d0) upper

def writeSuccessIncomingRegs (args : WriteSuccessArgs) (values : DecodeCalleeSavedValues) :
    List RegVal :=
  [⟨x1, BitVec.ofNat 64 args.returnAddress⟩,
   ⟨x8, values.s0⟩, ⟨x9, values.s1⟩, ⟨x18, values.s2⟩, ⟨x19, values.s3⟩,
   ⟨x20, values.s4⟩, ⟨x21, values.s5⟩, ⟨x22, values.s6⟩, ⟨x23, values.s7⟩,
   ⟨x24, values.s8⟩, ⟨x25, values.s9⟩, ⟨x26, values.s10⟩, ⟨x27, values.s11⟩,
   ⟨x10, BitVec.ofNat 64 args.decodedAddress⟩]

private theorem writeSuccessIncomingRegs_hold (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state)
    (values : DecodeCalleeSavedValues) (saved : DecodeCalleeSavedAtRegisters values state) :
    RegsHold state.machine (writeSuccessIncomingRegs args values) := by
  rcases entry with ⟨_, _, _, _, _, _, link, _, decoded, _, _, _, _, _, _, _⟩
  rcases saved with ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
  intro pair member
  simp only [writeSuccessIncomingRegs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> assumption

private theorem writeSuccessStackResult (stackPointer : Nat) (lower : 0x880 ≤ stackPointer)
    (fits : stackPointer < 2 ^ 64) :
    BitVec.ofNat 64 (stackPointer - 0x7d0) =
      iTypeResult .ADDI 0x830 (BitVec.ofNat 64 stackPointer) := by
  have sign : sign_extend (m := 64) (0x830#12) =
      BitVec.ofNat 64 (2 ^ 64 - 0x7d0) := by native_decide
  unfold iTypeResult
  change BitVec.ofNat 64 (stackPointer - 0x7d0) =
    BitVec.ofNat 64 stackPointer + sign_extend (m := 64) (0x830#12)
  rw [sign, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have sum : stackPointer + (2 ^ 64 - 0x7d0) =
      (stackPointer - 0x7d0) + 2 ^ 64 := by omega
  rw [sum, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

private theorem writeSuccessFinalStackResult (stackPointer : Nat) (lower : 0x880 ≤ stackPointer)
    (fits : stackPointer < 2 ^ 64) :
    BitVec.ofNat 64 stackPointer =
      iTypeResult .ADDI 0x7d0 (BitVec.ofNat 64 (stackPointer - 0x7d0)) := by
  have sign : sign_extend (m := 64) (0x7d0#12) = BitVec.ofNat 64 0x7d0 := by native_decide
  unfold iTypeResult
  change BitVec.ofNat 64 stackPointer =
    BitVec.ofNat 64 (stackPointer - 0x7d0) + sign_extend (m := 64) (0x7d0#12)
  rw [sign, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have lower' : 0x7d0 ≤ stackPointer := Nat.le_trans (by decide) lower
  rw [Nat.sub_add_cancel lower', Nat.mod_eq_of_lt fits]

/-- Exact first writer instruction, `0x14d30: addi sp,sp,-2000`, as a one-step `Seg`. -/
theorem writeSuccessAllocateFrame (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state)
    (values : DecodeCalleeSavedValues) (saved : DecodeCalleeSavedAtRegisters values state) :
    ∃ next,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 1 state.machine next 0x14d34 ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  rcases entry with ⟨_return, lower, _aligned, fits, _decodedEq, atPc, _link, stack, _decoded, _rep,
    _initialized, _initializedFull, loaded, _saved, access, stable⟩
  let kv := writeSuccessIncomingRegs args values
  have seg0 : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      kv fromStep 0 state.machine state.machine 0x14d30 := {
    trace := Trace.refl fromStep state.machine
    confined := .nil
    writes := WritesOnlyRegs.refl writeSuccessPrologueWrites state.machine
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := writeSuccessIncomingRegs_hold args state
      ⟨_return, lower, _aligned, fits, _decodedEq, atPc, _link, stack, _decoded, _rep,
        _initialized, _initializedFull, loaded, _saved, access, stable⟩
      values saved }
  have decode : Runs
      (ext_decode (fetchWord (0x13 : BitVec 8) (0x01 : BitVec 8) (0x01 : BitVec 8)
        (0x83 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state.machine)
      (tryStepControlFlowAfterIncrement state.machine)
      (.ITYPE (0x830, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := access.configured.seccfgPresent
    have privilegeAfter :
        (tryStepControlFlowAfterIncrement state.machine).regs.get? cur_privilege =
          some Privilege.Machine := by
      calc
        _ = state.machine.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using writeReg_read_unchanged
            state.machine minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := access.configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state.machine).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.machine.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using writeReg_read_unchanged
            state.machine minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    decode_run
  obtain ⟨retired, run⟩ := decodeInputAddiX2Step fromStep 0x14d30 state.machine 0x830
    (BitVec.ofNat 64 args.stackPointer) (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
    0x13 0x01 0x01 0x83 access.configured atPc stack loaded
    (writeSuccessStackResult args.stackPointer lower fits) decode (base := by rfl)
  obtain ⟨retired', next, nextEq, seg1⟩ := seg0.stepWitness
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessInitialExitPc; native_decide) x2
    (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) 0x14d34 ⟨retired, run⟩
    (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping)
    (by simp [writeSuccessPrologueWrites, writeSuccessParentWrites]) (by decide) (by decide) (by
      simpa [kv, writeSuccessIncomingRegs, RegsOutside, RegSet.union, RegSet.only,
        stepBookkeeping] using
        (show RegsOutside (RegSet.union stepBookkeeping (RegSet.only x2)) kv by decide))
  have disjoint : RegSet.Disjoint instructionPreserved writeSuccessPrologueWrites := by
    intro register preserved written
    simp only [writeSuccessPrologueWrites, writeSuccessParentWrites] at written
    rcases written with bookkeeping | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact platformPreserved_disjoint register preserved.1 bookkeeping
    all_goals simp [instructionPreserved, platformPreserved] at preserved
  exact ⟨next, seg1, access.configured.mono (seg1.agree disjoint) seg1.retired⟩

private theorem instructionPreserved_disjoint_bookkeeping :
    RegSet.Disjoint instructionPreserved stepBookkeeping :=
  platformPreserved_disjoint.weaken (fun _ preserved => preserved.1)

private theorem instructionPreserved_abiCalleePreserved_local (register : Register)
    (preserved : instructionPreserved register) : abiCalleePreserved register := by
  rcases preserved with ⟨platform, notLink⟩
  rcases platform with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact (notLink rfl).elim
  all_goals simp [abiCalleePreserved]

private theorem instructionPreserved_inlineEncoderPreserved (register : Register)
    (preserved : instructionPreserved register) : inlineEncoderPreserved register := by
  rcases preserved.1 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact (preserved.2 rfl).elim
  all_goals simp [inlineEncoderPreserved]

private theorem configuredAfterWriteSuccessCall {state : State} (callPc target returnPc : BitVec 64)
    (retired : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    ConfiguredMachinePre EndpointMachinePc
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) callPc target x1 returnPc)
        target retired) := by
  apply configured.mono
  · simpa [callLinkState] using
      (callRetirement_writes state callPc target retired x1 returnPc).agree
        (instructionPreserved_disjoint_bookkeeping.union
          (RegSet.Disjoint.only (by simp [instructionPreserved])))
  · simpa using tryStepControlFlowAfterRetired_retired_present
      (callLinkState (tryStepControlFlowAfterIncrement state) callPc target x1 returnPc)
      target retired

private theorem configuredAfterEndpointCall {before after : EndpointState}
    (configured : ConfiguredMachinePre EndpointMachinePc before.machine)
    (frame : EndpointCallFrame before after) :
    ConfiguredMachinePre EndpointMachinePc after.machine :=
  configured.mono
    (frame.1.weaken instructionPreserved_abiCalleePreserved_local)
    frame.2.1

private theorem writeSuccessStoreDecodeReads {state : State}
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    ∃ seccfgBits,
      (tryStepStoreAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine ∧
      (tryStepStoreAfterIncrement state).regs.get? mseccfg = some seccfgBits := by
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  refine ⟨seccfgBits, ?_, ?_⟩
  · calc
      _ = state.regs.get? cur_privilege := by
        simpa [tryStepStoreAfterIncrement] using writeReg_read_unchanged state
          minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := configured.normal.2.1
  · calc
      _ = state.regs.get? mseccfg := by
        simpa [tryStepStoreAfterIncrement] using writeReg_read_unchanged state
          minstret_increment mseccfg true (by decide)
      _ = some seccfgBits := seccfgRead

private theorem writeSuccessLoadDecodeReads {state : State}
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    ∃ seccfgBits,
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine ∧
      (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some seccfgBits := by
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  refine ⟨seccfgBits, ?_, ?_⟩
  · calc
      _ = state.regs.get? cur_privilege := by
        simpa [tryStepControlFlowAfterIncrement] using writeReg_read_unchanged state
          minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := configured.normal.2.1
  · calc
      _ = state.regs.get? mseccfg := by
        simpa [tryStepControlFlowAfterIncrement] using writeReg_read_unchanged state
          minstret_increment mseccfg true (by decide)
      _ = some seccfgBits := seccfgRead

/-- Execute one exact parent-owned dword load from the optimized decoded-value window. -/
private theorem writeSuccessDecodedDwordLoadStep (stepNo pc offset value : Nat)
    (args : WriteSuccessArgs) (state : State) (rd : regidx) (destination : Register)
    (result : RegisterType destination) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8)
    (access : WriteSuccessMachineAccess args state)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (baseRead : state.regs.get? x8 = some (BitVec.ofNat 64 args.decodedAddress))
    (rep : UIntRep 8 state.mem (args.decodedAddress + offset) value)
    (offsetBound : 0x20 + offset + 8 ≤ 0x380)
    (aligned : (args.decodedAddress + offset) % 8 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 args.decodedAddress + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (args.decodedAddress + offset))
    (writeRun : ∀ premise, Runs (wX_bits rd (BitVec.ofNat 64 value)) premise
      { premise with regs := premise.regs.insert destination result } ())
    (decode : ConfiguredMachinePre EndpointMachinePc state →
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
        (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
        (BitVec.ofNat 8 byte3.toNat)))
        (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
        (.LOAD (imm, .Regidx 8#5, rd, false, 8)))
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret)
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false := by
  have pma : LoadPmaAllows state (BitVec.ofNat 64 (args.decodedAddress + offset)) 8 := by
    simpa [decodedEq, Nat.add_assoc] using access.decodedLoad (0x20 + offset) 8 offsetBound
  have noMMIO : LoadMMIOAddressExcluded
      (BitVec.ofNat 64 (args.decodedAddress + offset)) 8 := by
    simpa [decodedEq, Nat.add_assoc] using access.decodedNoMMIO (0x20 + offset) 8 offsetBound
  exact configuredDwordLoadStep stepNo pc state imm (.Regidx 8#5) rd destination
    args.decodedAddress offset value result byte0 byte1 byte2 byte3 access.configured atPc rep
    pma noMMIO (by have := rep.2.1; omega) aligned loaded addressEq
    (fun premise writes => rX_x8_run premise (BitVec.ofNat 64 args.decodedAddress)
      ((writes.get x8 (by decide)).trans baseRead))
    writeRun (decode access.configured) (pcFits := pcFits) (base := base)
    (destinationNotNextPc := destinationNotNextPc) (destinationNotHart := destinationNotHart)
    (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired)
    (read0 := read0) (read1 := read1) (read2 := read2) (read3 := read3)

/-- Exact first decoded-tail load, `0x14d80: ld a0,720(s0)`. -/
private theorem writeSuccessLoadDecoded720 (stepNo value : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20)
    (stackAligned : args.stackPointer % 16 = 0)
    (atPc : state.regs.get? PC = some 0x14d80)
    (baseRead : state.regs.get? x8 = some (BitVec.ofNat 64 args.decodedAddress))
    (rep : UIntRep 8 state.mem (args.decodedAddress + 720) value)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14d80 retired x10 (BitVec.ofNat 64 value)) false := by
  apply writeSuccessDecodedDwordLoadStep stepNo 0x14d80 720 value args state
    (.Regidx 10#5) x10 (BitVec.ofNat 64 value) 0x2d0 0x03 0x35 0x04 0x2d access decodedEq
    atPc baseRead rep (by omega) (by omega) loaded (base := by rfl)
  · change BitVec.ofNat 64 args.decodedAddress + 0x2d0#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise (BitVec.ofNat 64 value)
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  all_goals decide

private theorem writeSuccessCodeOfSeg {args : WriteSuccessArgs} {W kv a n base cur pc}
    (access : WriteSuccessMachineAccess args base)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (stackLower : 0x880 ≤ args.stackPointer)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) W (writeSuccessFrameMemory args) kv a n base cur pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  intro address byte fileByte
  have unchanged := seg.mem address (by
    intro inside
    unfold writeSuccessFrameMemory byteRange at inside
    have none := access.frameNotCode address inside.1 (by omega)
    rw [fileByte] at none
    cases none)
  exact unchanged.trans (loaded address byte fileByte)

private theorem writeSuccessAccessOfSeg {args : WriteSuccessArgs} {owned exit M kv a n base cur pc}
    (access : WriteSuccessMachineAccess args base)
    (seg : Seg owned exit
      (fun _ _ _ _ _ => False) writeSuccessParentWrites M
      kv a n base cur pc) : WriteSuccessMachineAccess args cur := by
  have disjoint : RegSet.Disjoint instructionPreserved writeSuccessParentWrites := by
    intro register preserved written
    rcases written with bookkeeping | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact platformPreserved_disjoint register preserved.1 bookkeeping
    all_goals simp [instructionPreserved, platformPreserved] at preserved
  have pmaEq := seg.writes.get pma_regions (by simp [writeSuccessParentWrites, stepBookkeeping])
  exact
    { configured := access.configured.mono (seg.agree disjoint) seg.retired
      frameLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameLoad offset width inBounds)
      frameStore := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameStore offset width inBounds)
      frameNoMMIO := access.frameNoMMIO
      decodedLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.decodedLoad offset width inBounds)
      decodedNoMMIO := access.decodedNoMMIO
      outputBufferStore :=
        dataPmaAllows_of_pma_regions_eq pmaEq access.outputBufferStore
      outputLengthStore :=
        dataPmaAllows_of_pma_regions_eq pmaEq access.outputLengthStore
      writerRegionBeforeOutputContext := access.writerRegionBeforeOutputContext
      frameNotCode := access.frameNotCode }

private theorem writeSuccessConfiguredOfSeg {args : WriteSuccessArgs} {exit M kv a n base cur pc}
    (access : WriteSuccessMachineAccess args base)
    (seg : Seg writeSuccessParentPc exit
      (fun _ _ _ _ _ => False) writeSuccessParentWrites M kv a n base cur pc) :
    ConfiguredMachinePre EndpointMachinePc cur :=
  (writeSuccessAccessOfSeg access seg).configured

private theorem writeSuccessParentPc_in_execution {pc : BitVec 64}
    (inside : writeSuccessParentPc pc) :
    pcInRanges Elflings.writeSuccessExecutionPcRanges pc := by
  unfold writeSuccessParentPc at inside
  unfold pcInRanges at inside ⊢
  rcases inside with ⟨range, member, lower, upper⟩
  simp [Elflings.writeSuccessOwnedPcRanges] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
    exact ⟨(0x14d30, 0x15a14), by simp [Elflings.writeSuccessExecutionPcRanges], by omega,
      by omega⟩

private theorem writeSuccessParentPc_not_observed {pc : BitVec 64}
    (inside : writeSuccessParentPc pc) : ¬ BareMetalHostTransitionPc pc := by
  unfold writeSuccessParentPc pcInRanges at inside
  rcases inside with ⟨range, member, lower, upper⟩
  simp [Elflings.writeSuccessOwnedPcRanges] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
    simp [BareMetalHostTransitionPc, readContextReturnPc, writeContextReturnPc,
      exitContextStorePc] <;> omega

private theorem liftWriteSuccessParentTrace {exit : BitVec 64 → Prop} (template : EndpointState)
    {fromStep count : Nat} {before after : State}
    (trace : ScopedTrace writeSuccessParentPc exit
      (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessExecutionPcRanges)
      fromStep count { template with machine := before } { template with machine := after } := by
  induction trace with
  | exitAt fromStep state pc atPc exitPc => exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step fromStep count pc
        { template with machine := before } { template with machine := middle }
        { template with machine := after } ?_ ?_ ?_ ?_
      · exact atPc
      · exact writeSuccessParentPc_in_execution inside
      · exact endpointStep_sail fromStep { template with machine := before } middle
          (fun observed observedPc => by
            change before.regs.get? PC = some observed at observedPc
            rw [atPc] at observedPc
            cases Option.some.inj observedPc
            exact writeSuccessParentPc_not_observed inside)
          machineStep
      · simpa using ih
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count call program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

private theorem liftWriteSuccessOutputTrace {exit : BitVec 64 → Prop} (template : EndpointState)
    {fromStep count : Nat} {before after : State}
    (trace : ScopedTrace writeSuccessOutputSetupPc exit
      (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessExecutionPcRanges)
      fromStep count { template with machine := before } { template with machine := after } := by
  induction trace with
  | exitAt fromStep state pc atPc exitPc => exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step fromStep count pc
        { template with machine := before } { template with machine := middle }
        { template with machine := after } atPc ?_ ?_ ih
      · rcases inside with parent | child
        · exact writeSuccessParentPc_in_execution parent
        · unfold pcInRanges at child ⊢
          rcases child with ⟨range, member, lower, upper⟩
          simp at member
          subst range
          exact ⟨(0x14d30, 0x15a14), by simp [Elflings.writeSuccessExecutionPcRanges],
            by omega, by omega⟩
      · exact endpointStep_sail fromStep { template with machine := before } middle
          (fun observed observedPc => by
            change before.regs.get? PC = some observed at observedPc
            rw [atPc] at observedPc
            cases Option.some.inj observedPc
            rcases inside with parent | child
            · exact writeSuccessParentPc_not_observed parent
            · unfold pcInRanges at child
              rcases child with ⟨range, member, lower, upper⟩
              simp at member
              subst range
              simp [BareMetalHostTransitionPc, readContextReturnPc, writeContextReturnPc,
                exitContextStorePc]
              omega)
          machineStep
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count call program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

private theorem memcpyPc_in_writeSuccess {pc : BitVec 64}
    (inside : pcInRanges Elflings.memcpyExecutionPcRanges pc) :
    pcInRanges Elflings.writeSuccessExecutionPcRanges pc := by
  unfold pcInRanges at inside ⊢
  rcases inside with ⟨range, member, lower, upper⟩
  simp [Elflings.memcpyExecutionPcRanges] at member
  rcases member with rfl
  exact ⟨(0x101d4, 0x101f8), by simp [Elflings.writeSuccessExecutionPcRanges], lower, upper⟩

/-- Extend the writer prologue by one exact dword save, preserving all previously saved words. -/
theorem writeSuccessSaveStepExact {args : WriteSuccessArgs} {base : State}
    {kv : List RegVal} {a n : Nat} {cur : State} {pc : BitVec 64}
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      kv a n base cur pc)
    (access : WriteSuccessMachineAccess args base)
    (configured : ConfiguredMachinePre EndpointMachinePc cur)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (stackLower : 0x880 ≤ args.stackPointer) (stackFits : args.stackPointer < 2 ^ 64)
    (words : List (Nat × Nat)) (wordsRep : SavedWordReps cur words)
    (storePc offset : Nat) (source : BitVec 64) (imm : BitVec 12) (rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (stackRead : cur.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping cur premise →
      Runs (rX_bits rs2) premise premise source)
    (belowWords : ∀ word ∈ words,
      args.stackPointer - 0x7d0 + offset + 8 ≤ word.1)
    (frameBound : offset + 8 ≤ 0x7d0)
    (aligned : (args.stackPointer - 0x7d0 + offset) % 8 = 0)
    (pcEq : pc = BitVec.ofNat 64 storePc)
    (inRegion : writeSuccessParentPc (BitVec.ofNat 64 storePc))
    (notExit : ¬writeSuccessInitialExitPc (BitVec.ofNat 64 storePc))
    (decodeOfConfigured : ConfiguredMachinePre EndpointMachinePc cur →
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
        (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
        (BitVec.ofNat 8 byte3.toNat)))
        (tryStepStoreAfterIncrement cur) (tryStepStoreAfterIncrement cur)
        (.STORE (imm, rs2, .Regidx 2#5, 8)))
    (addressEq : BitVec.ofNat 64 (args.stackPointer - 0x7d0) + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (args.stackPointer - 0x7d0 + offset))
    (keep : RegsOutside stepBookkeeping kv)
    (pcFits : storePc < 2 ^ 64) (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? storePc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (storePc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (storePc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (storePc + 3) = some byte3)
    (advance : Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4 = BitVec.ofNat 64 (storePc + 4)) :
    ∃ next,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        kv a (n + 1) base next (BitVec.ofNat 64 (storePc + 4)) ∧
      SavedWordReps next
        ((args.stackPointer - 0x7d0 + offset, source.toNat) :: words) ∧
      ConfiguredMachinePre EndpointMachinePc next ∧
      ∃ retired,
        next = tryStepControlFlowAfterRetired
          (afterWriteBytes (width := 8)
            (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur)
              (BitVec.ofNat 64 storePc))
            (args.stackPointer - 0x7d0 + offset) source)
          (Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4) retired := by
  subst pc
  have code := writeSuccessCodeOfSeg access loaded stackLower seg
  have pma := dataPmaAllows_of_pma_regions_eq
    (seg.writes.get pma_regions (by
      simp [writeSuccessPrologueWrites, writeSuccessParentWrites, stepBookkeeping]))
    (access.frameStore offset 8 frameBound)
  have noMMIO := access.frameNoMMIO offset 8 frameBound
  have fits : args.stackPointer - 0x7d0 + offset + 8 ≤ 2 ^ 64 := by omega
  obtain ⟨retired, run⟩ := decodeInputStoreStep (a + n) storePc offset cur
    (args.stackPointer - 0x7d0) source imm rs2 byte0 byte1 byte2 byte3 configured seg.atPc
    stackRead pma noMMIO aligned fits code addressEq (decodeOfConfigured configured) dataRun
    (pcFits := pcFits) (base := baseEncoding) (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3)
  obtain ⟨retired', next, nextEq, nextSeg⟩ := seg.stepStoreWitness
    (width := 8) (args.stackPointer - 0x7d0 + offset) source
    (BitVec.ofNat 64 (storePc + 4))
    inRegion notExit ⟨retired, run⟩ advance
    (by intro address lower upper; unfold writeSuccessFrameMemory byteRange; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping) keep
  have stepWrites : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 + offset) 8) cur next := by
    intro address outside
    rw [nextEq]
    exact storeRetirement_mem_writes cur (BitVec.ofNat 64 storePc)
      (Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4) retired'
      (args.stackPointer - 0x7d0 + offset) source address outside
  have oldReps : SavedWordReps next words := by
    intro word member
    exact (wordsRep word member).of_writesOnlyWithin stepWrites (by
      intro index indexBound inside
      unfold byteRange at inside
      have := belowWords word member
      omega)
  have currentRep : UIntRep 8 next.mem
      (args.stackPointer - 0x7d0 + offset) source.toNat := by
    have sourceFits : source.toNat < 2 ^ 64 := source.isLt
    rw [nextEq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement cur) (BitVec.ofNat 64 storePc))
        (args.stackPointer - 0x7d0 + offset) source.toNat sourceFits fits
  refine ⟨next, nextSeg, ?_, ?_, retired', nextEq⟩
  · intro word member
    simp only [List.mem_cons] at member
    rcases member with rfl | tail
    · simpa using currentRep
    · exact oldReps word tail
  · have stepAgree : Agree instructionPreserved cur next := by
      rw [nextEq]
      exact (storeRetirement_writes cur (BitVec.ofNat 64 storePc)
        (Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4) retired'
        (args.stackPointer - 0x7d0 + offset) source).agree
        instructionPreserved_disjoint_bookkeeping
    exact configured.mono stepAgree nextSeg.retired

/-- Compatibility wrapper for callers that need only the saved-word and configured-machine facts. -/
theorem writeSuccessSaveStep {args : WriteSuccessArgs} {base : State}
    {kv : List RegVal} {a n : Nat} {cur : State} {pc : BitVec 64}
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      kv a n base cur pc)
    (access : WriteSuccessMachineAccess args base)
    (configured : ConfiguredMachinePre EndpointMachinePc cur)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (stackLower : 0x880 ≤ args.stackPointer) (stackFits : args.stackPointer < 2 ^ 64)
    (words : List (Nat × Nat)) (wordsRep : SavedWordReps cur words)
    (storePc offset : Nat) (source : BitVec 64) (imm : BitVec 12) (rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (stackRead : cur.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping cur premise →
      Runs (rX_bits rs2) premise premise source)
    (belowWords : ∀ word ∈ words,
      args.stackPointer - 0x7d0 + offset + 8 ≤ word.1)
    (frameBound : offset + 8 ≤ 0x7d0)
    (aligned : (args.stackPointer - 0x7d0 + offset) % 8 = 0)
    (pcEq : pc = BitVec.ofNat 64 storePc)
    (inRegion : writeSuccessParentPc (BitVec.ofNat 64 storePc))
    (notExit : ¬writeSuccessInitialExitPc (BitVec.ofNat 64 storePc))
    (decodeOfConfigured : ConfiguredMachinePre EndpointMachinePc cur →
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
        (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
        (BitVec.ofNat 8 byte3.toNat)))
        (tryStepStoreAfterIncrement cur) (tryStepStoreAfterIncrement cur)
        (.STORE (imm, rs2, .Regidx 2#5, 8)))
    (addressEq : BitVec.ofNat 64 (args.stackPointer - 0x7d0) + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (args.stackPointer - 0x7d0 + offset))
    (keep : RegsOutside stepBookkeeping kv)
    (pcFits : storePc < 2 ^ 64) (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? storePc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (storePc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (storePc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (storePc + 3) = some byte3)
    (advance : Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4 = BitVec.ofNat 64 (storePc + 4)) :
    ∃ next,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        kv a (n + 1) base next (BitVec.ofNat 64 (storePc + 4)) ∧
      SavedWordReps next
        ((args.stackPointer - 0x7d0 + offset, source.toNat) :: words) ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  obtain ⟨next, nextSeg, nextWords, nextConfigured, _retired, _nextEq⟩ :=
    writeSuccessSaveStepExact seg access configured loaded stackLower stackFits words wordsRep
      storePc offset source imm rs2 byte0 byte1 byte2 byte3 stackRead dataRun belowWords
      frameBound aligned pcEq inRegion notExit decodeOfConfigured addressEq keep pcFits baseEncoding
      read0 read1 read2 read3 advance
  exact ⟨next, nextSeg, nextWords, nextConfigured⟩

private theorem initializedByteWindow_of_writeSuccessStore
    {cur next : State} {memAddress width storePc storeAddress : Nat}
    {source : BitVec 64} {retired : BitVec 64}
    (window : InitializedByteWindow cur.mem memAddress width)
    (nextEq : next = tryStepControlFlowAfterRetired
      (afterWriteBytes (width := 8)
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur)
          (BitVec.ofNat 64 storePc)) storeAddress source)
      (Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4) retired) :
    InitializedByteWindow next.mem memAddress width := by
  rw [nextEq]
  have coreWindow : InitializedByteWindow
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur)
        (BitVec.ofNat 64 storePc)).mem memAddress width := by
    simpa only [coreControlFlowNextState_mem, tryStepControlFlowAfterIncrement_mem] using window
  simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
    InitializedByteWindow.afterWriteBytes coreWindow (storeAddress := storeAddress)
      (storeWidth := 8) (value := source)

private theorem bytesRep_of_writeSuccessStore
    {cur next : State} {memAddress storePc storeAddress : Nat} {bytes : Array UInt8}
    {source : BitVec 64} {retired : BitVec 64}
    (rep : BytesRep cur.mem memAddress bytes) (storeBefore : storeAddress + 8 ≤ memAddress)
    (nextEq : next = tryStepControlFlowAfterRetired
      (afterWriteBytes (width := 8)
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur)
          (BitVec.ofNat 64 storePc)) storeAddress source)
      (Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4) retired) :
    BytesRep next.mem memAddress bytes := by
  refine ⟨rep.1, ?_⟩
  intro index indexBound
  rw [nextEq, storeRetirement_mem_writes]
  · exact rep.2 index indexBound
  · omega

/-- Exact first save, `0x14d34: sd ra,1992(sp)`. -/
theorem writeSuccessSaveRa {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 1 state.machine cur 0x14d34)
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ next,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 2 state.machine next 0x14d38 ∧
      SavedWordReps next
        [(args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits [] (by
    intro word member; simp at member) 0x14d34 0x7c8
    (BitVec.ofNat 64 args.returnAddress) 0x7c8 (.Regidx 1#5) 0x23 0x34 0x11 0x7c
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x1_run premise (BitVec.ofNat 64 args.returnAddress)
      ((writes.get x1 (by decide)).trans
        (seg.reg x1 (BitVec.ofNat 64 args.returnAddress) (by
          simp [writeSuccessIncomingRegs])))
  · intro word member; simp at member
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x7c8#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide


  · native_decide
  · native_decide

/-- Exact second save, `0x14d38: sd s0,1984(sp)`. -/
theorem writeSuccessSaveS0 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 2 state.machine cur 0x14d38)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x7c8,
        (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ next,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 3 state.machine next 0x14d3c ∧
      SavedWordReps next
        [(args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d38 0x7c0 values.s0 0x7c0 (.Regidx 8#5) 0x23 0x30 0x81 0x7c
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x8_run premise values.s0
      ((writes.get x8 (by decide)).trans
        (seg.reg x8 values.s0 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x7c0#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d3c: sd s1,1976(sp)`. -/
theorem writeSuccessSaveS1 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 3 state.machine cur 0x14d3c)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 4 state.machine nextState 0x14d40 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d3c 0x7b8 values.s1 0x7b8 (.Regidx 9#5) 0x23 0x3c 0x91 0x7a
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x9_run premise values.s1
      ((writes.get x9 (by decide)).trans
        (seg.reg x9 values.s1 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x7b8#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d40: sd s2,1968(sp)`. -/
theorem writeSuccessSaveS2 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 4 state.machine cur 0x14d40)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 5 state.machine nextState 0x14d44 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d40 0x7b0 values.s2 0x7b0 (.Regidx 18#5) 0x23 0x38 0x21 0x7b
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x18_run premise values.s2
      ((writes.get x18 (by decide)).trans
        (seg.reg x18 values.s2 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x7b0#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d44: sd s3,1960(sp)`. -/
theorem writeSuccessSaveS3 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 5 state.machine cur 0x14d44)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 6 state.machine nextState 0x14d48 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d44 0x7a8 values.s3 0x7a8 (.Regidx 19#5) 0x23 0x34 0x31 0x7b
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x19_run premise values.s3
      ((writes.get x19 (by decide)).trans
        (seg.reg x19 values.s3 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x7a8#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d48: sd s4,1952(sp)`. -/
theorem writeSuccessSaveS4 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 6 state.machine cur 0x14d48)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 7 state.machine nextState 0x14d4c ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d48 0x7a0 values.s4 0x7a0 (.Regidx 20#5) 0x23 0x30 0x41 0x7b
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x20_run premise values.s4
      ((writes.get x20 (by decide)).trans
        (seg.reg x20 values.s4 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x7a0#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d4c: sd s5,1944(sp)`. -/
theorem writeSuccessSaveS5 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 7 state.machine cur 0x14d4c)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 8 state.machine nextState 0x14d50 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d4c 0x798 values.s5 0x798 (.Regidx 21#5) 0x23 0x3c 0x51 0x79
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x21_run premise values.s5
      ((writes.get x21 (by decide)).trans
        (seg.reg x21 values.s5 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x798#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d50: sd s6,1936(sp)`. -/
theorem writeSuccessSaveS6 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 8 state.machine cur 0x14d50)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 9 state.machine nextState 0x14d54 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d50 0x790 values.s6 0x790 (.Regidx 22#5) 0x23 0x38 0x61 0x79
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x22_run premise values.s6
      ((writes.get x22 (by decide)).trans
        (seg.reg x22 values.s6 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x790#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d54: sd s7,1928(sp)`. -/
theorem writeSuccessSaveS7 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 9 state.machine cur 0x14d54)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 10 state.machine nextState 0x14d58 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d54 0x788 values.s7 0x788 (.Regidx 23#5) 0x23 0x34 0x71 0x79
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x23_run premise values.s7
      ((writes.get x23 (by decide)).trans
        (seg.reg x23 values.s7 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x788#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d58: sd s8,1920(sp)`. -/
theorem writeSuccessSaveS8 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 10 state.machine cur 0x14d58)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 11 state.machine nextState 0x14d5c ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d58 0x780 values.s8 0x780 (.Regidx 24#5) 0x23 0x30 0x81 0x79
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x24_run premise values.s8
      ((writes.get x24 (by decide)).trans
        (seg.reg x24 values.s8 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x780#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d5c: sd s9,1912(sp)`. -/
theorem writeSuccessSaveS9 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 11 state.machine cur 0x14d5c)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 12 state.machine nextState 0x14d60 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x778, values.s9.toNat),
         (args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d5c 0x778 values.s9 0x778 (.Regidx 25#5) 0x23 0x3c 0x91 0x77
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x25_run premise values.s9
      ((writes.get x25 (by decide)).trans
        (seg.reg x25 values.s9 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x778#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d60: sd s10,1904(sp)`. -/
theorem writeSuccessSaveS10 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 12 state.machine cur 0x14d60)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x778, values.s9.toNat),
         (args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 13 state.machine nextState 0x14d64 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x770, values.s10.toNat),
         (args.stackPointer - 0x7d0 + 0x778, values.s9.toNat),
         (args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d60 0x770 values.s10 0x770 (.Regidx 26#5) 0x23 0x38 0xa1 0x77
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x26_run premise values.s10
      ((writes.get x26 (by decide)).trans
        (seg.reg x26 values.s10 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x770#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Exact save at `0x14d64: sd s11,1896(sp)`. -/
theorem writeSuccessSaveS11 {fromStep : Nat} {args : WriteSuccessArgs}
    {state : EndpointState} {values : DecodeCalleeSavedValues} {cur : State}
    (entry : WriteSuccessEntry args state)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
        writeSuccessIncomingRegs args values)
      fromStep 13 state.machine cur 0x14d64)
    (words : SavedWordReps cur
      [(args.stackPointer - 0x7d0 + 0x770, values.s10.toNat),
         (args.stackPointer - 0x7d0 + 0x778, values.s9.toNat),
         (args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)])
    (configured : ConfiguredMachinePre EndpointMachinePc cur) :
    ∃ nextState,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 14 state.machine nextState 0x14d68 ∧
      SavedWordReps nextState
        [(args.stackPointer - 0x7d0 + 0x768, values.s11.toNat),
         (args.stackPointer - 0x7d0 + 0x770, values.s10.toNat),
         (args.stackPointer - 0x7d0 + 0x778, values.s9.toNat),
         (args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
         (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
         (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
         (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
         (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
         (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
         (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
         (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
         (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
         (args.stackPointer - 0x7d0 + 0x7c8,
          (BitVec.ofNat 64 args.returnAddress).toNat)] ∧
      ConfiguredMachinePre EndpointMachinePc nextState := by
  rcases entry with ⟨_, lower, aligned, fits, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  apply writeSuccessSaveStep seg access configured loaded lower fits _ words
    0x14d64 0x768 values.s11 0x768 (.Regidx 27#5) 0x23 0x34 0xb1 0x77
  · exact seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · intro premise writes
    exact rX_x27_run premise values.s11
      ((writes.get x27 (by decide)).trans
        (seg.reg x27 values.s11 (by simp [writeSuccessIncomingRegs])))
  · intro word member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · native_decide
  · omega
  · rfl
  · unfold writeSuccessParentPc
    exact ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩
  · unfold writeSuccessInitialExitPc; native_decide
  · intro configured'
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessStoreDecodeReads configured'
    decode_run
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x768#64 = _
    rw [← BitVec.ofNat_add]
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


def writeSuccessSavedWords (args : WriteSuccessArgs) (values : DecodeCalleeSavedValues) :
    List (Nat × Nat) :=
  [(args.stackPointer - 0x7d0 + 0x768, values.s11.toNat),
   (args.stackPointer - 0x7d0 + 0x770, values.s10.toNat),
   (args.stackPointer - 0x7d0 + 0x778, values.s9.toNat),
   (args.stackPointer - 0x7d0 + 0x780, values.s8.toNat),
   (args.stackPointer - 0x7d0 + 0x788, values.s7.toNat),
   (args.stackPointer - 0x7d0 + 0x790, values.s6.toNat),
   (args.stackPointer - 0x7d0 + 0x798, values.s5.toNat),
   (args.stackPointer - 0x7d0 + 0x7a0, values.s4.toNat),
   (args.stackPointer - 0x7d0 + 0x7a8, values.s3.toNat),
   (args.stackPointer - 0x7d0 + 0x7b0, values.s2.toNat),
   (args.stackPointer - 0x7d0 + 0x7b8, values.s1.toNat),
   (args.stackPointer - 0x7d0 + 0x7c0, values.s0.toNat),
   (args.stackPointer - 0x7d0 + 0x7c8,
    (BitVec.ofNat 64 args.returnAddress).toNat)]

/-- The exact stack allocation and thirteen ABI saves, ending before `mv s0,a0`. -/
theorem writeSuccessSavePrologue (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state) :
    ∃ values next,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ::
          writeSuccessIncomingRegs args values)
        fromStep 14 state.machine next 0x14d68 ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  rcases entry with ⟨ret, lower, aligned, fits, decodedEq, atPc, link, stack, decoded, rep,
    initialized, initializedFull, loaded, ⟨values, saved⟩, access, stable⟩
  have entry' : WriteSuccessEntry args state :=
    ⟨ret, lower, aligned, fits, decodedEq, atPc, link, stack, decoded, rep, initialized,
      initializedFull, loaded, ⟨values, saved⟩, access, stable⟩
  obtain ⟨s1, seg1, cfg1⟩ := writeSuccessAllocateFrame fromStep args state entry' values saved
  obtain ⟨s2, seg2, words2, cfg2⟩ := writeSuccessSaveRa entry' seg1 cfg1
  obtain ⟨s3, seg3, words3, cfg3⟩ := writeSuccessSaveS0 entry' seg2 words2 cfg2
  obtain ⟨s4, seg4, words4, cfg4⟩ := writeSuccessSaveS1 entry' seg3 words3 cfg3
  obtain ⟨s5, seg5, words5, cfg5⟩ := writeSuccessSaveS2 entry' seg4 words4 cfg4
  obtain ⟨s6, seg6, words6, cfg6⟩ := writeSuccessSaveS3 entry' seg5 words5 cfg5
  obtain ⟨s7, seg7, words7, cfg7⟩ := writeSuccessSaveS4 entry' seg6 words6 cfg6
  obtain ⟨s8, seg8, words8, cfg8⟩ := writeSuccessSaveS5 entry' seg7 words7 cfg7
  obtain ⟨s9, seg9, words9, cfg9⟩ := writeSuccessSaveS6 entry' seg8 words8 cfg8
  obtain ⟨s10, seg10, words10, cfg10⟩ := writeSuccessSaveS7 entry' seg9 words9 cfg9
  obtain ⟨s11, seg11, words11, cfg11⟩ := writeSuccessSaveS8 entry' seg10 words10 cfg10
  obtain ⟨s12, seg12, words12, cfg12⟩ := writeSuccessSaveS9 entry' seg11 words11 cfg11
  obtain ⟨s13, seg13, words13, cfg13⟩ := writeSuccessSaveS10 entry' seg12 words12 cfg12
  obtain ⟨s14, seg14, words14, cfg14⟩ := writeSuccessSaveS11 entry' seg13 words13 cfg13
  exact ⟨values, s14, seg14, by simpa [writeSuccessSavedWords] using words14, cfg14⟩

/-- Production `0x14d68: mv s0,a0`. -/
theorem writeSuccessBindDecodedStep (stepNo : Nat) (state : State) (value : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d68)
    (source : state.regs.get? x10 = some value)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14d68 retired x8 value) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d68
  have source' := (stepPremiseState_writes state 0x14d68).get x10 (by decide) |>.trans source
  have execute : Runs (execute (.ITYPE (0, .Regidx 10#5, .Regidx 8#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x8 value } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 10#5) (.Regidx 8#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 0 value = value := by
      simp [iTypeResult, show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
    simpa only [resultEq] using
      execute_ITYPE_run premise _ 0 (.Regidx 10#5) (.Regidx 8#5) .ADDI value
        (rX_x10_run premise value source') (wX_x8_run premise (iTypeResult .ADDI 0 value))
  exact configuredRegisterWriteStep stepNo 0x14d68 state x8 value
    (.ITYPE (0, .Regidx 10#5, .Regidx 8#5, .ADDI)) 0x13 0x04 0x05 0x00
    configured atPc loaded (by
      obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
      have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
          some Privilege.Machine := by
        calc
          _ = state.regs.get? cur_privilege := by
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
          _ = some Privilege.Machine := configured.normal.2.1
      have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
          some seccfgBits := by
        calc
          _ = state.regs.get? mseccfg := by
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
          _ = some seccfgBits := seccfgRead
      decode_run) execute (base := by rfl)

/-- Production `0x14d6c: addi a0,sp,0x138`. -/
theorem writeSuccessMemcpyDestinationStep (stepNo : Nat) (state : State) (stackPointer : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d6c)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (fits : stackPointer + 0x138 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14d6c retired x10
        (BitVec.ofNat 64 (stackPointer + 0x138))) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d6c
  let destination := BitVec.ofNat 64 (stackPointer + 0x138)
  have source := (stepPremiseState_writes state 0x14d6c).get x2 (by decide) |>.trans stack
  have resultEq : iTypeResult .ADDI 0x138 (BitVec.ofNat 64 stackPointer) =
      BitVec.ofNat 64 (stackPointer + 0x138) := by
    have sign : sign_extend (m := 64) (BitVec.ofNat 12 0x138) = 0x138#64 := by
      native_decide
    simp only [iTypeResult]
    change BitVec.ofNat 64 stackPointer + sign_extend (BitVec.ofNat 12 0x138) = _
    rw [sign]
    rw [← BitVec.ofNat_add]
  have execute : Runs (execute (.ITYPE (0x138, .Regidx 2#5, .Regidx 10#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x10 destination } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x138 (.Regidx 2#5) (.Regidx 10#5) .ADDI) _ _ _
    simpa only [resultEq] using execute_ITYPE_run premise _ 0x138 (.Regidx 2#5)
      (.Regidx 10#5) .ADDI (BitVec.ofNat 64 stackPointer)
      (rX_x2_run premise (BitVec.ofNat 64 stackPointer) source)
      (wX_x10_run premise (iTypeResult .ADDI 0x138 (BitVec.ofNat 64 stackPointer)))
  exact configuredRegisterWriteStep stepNo 0x14d6c state x10
    (BitVec.ofNat 64 (stackPointer + 0x138))
    (.ITYPE (0x138, .Regidx 2#5, .Regidx 10#5, .ADDI)) 0x13 0x05 0x81 0x13
    configured atPc loaded (by
      obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
      have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
          some Privilege.Machine := by
        calc
          _ = state.regs.get? cur_privilege := by
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
          _ = some Privilege.Machine := configured.normal.2.1
      have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
          some seccfgBits := by
        calc
          _ = state.regs.get? mseccfg := by
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
          _ = some seccfgBits := seccfgRead
      decode_run) execute (base := by rfl)

/-- Production `0x14d70: li a2,0x2d0`. -/
theorem writeSuccessMemcpyLengthStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d70)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14d70 retired x12 0x2d0) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d70
  have resultEq : iTypeResult .ADDI 0x2d0 0 = 0x2d0#64 := by
    native_decide
  have execute : Runs (execute (.ITYPE (0x2d0, .Regidx 0#5, .Regidx 12#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x12 0x2d0 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x2d0 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    simpa only [resultEq] using execute_ITYPE_run premise _ 0x2d0 (.Regidx 0#5)
      (.Regidx 12#5) .ADDI 0 (rX_x0_run premise)
      (wX_x12_run premise (iTypeResult .ADDI 0x2d0 0))
  exact configuredRegisterWriteStep stepNo 0x14d70 state x12 0x2d0
    (.ITYPE (0x2d0, .Regidx 0#5, .Regidx 12#5, .ADDI)) 0x13 0x06 0x00 0x2d
    configured atPc loaded (by
      obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
      have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
          some Privilege.Machine := by
        calc
          _ = state.regs.get? cur_privilege := by
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
          _ = some Privilege.Machine := configured.normal.2.1
      have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
          some seccfgBits := by
        calc
          _ = state.regs.get? mseccfg := by
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
          _ = some seccfgBits := seccfgRead
      decode_run) execute (base := by rfl)

/-- Production `0x14d74: mv a1,s0`. -/
theorem writeSuccessMemcpySourceStep (stepNo : Nat) (state : State) (sourceValue : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14d74)
    (source : state.regs.get? x8 = some sourceValue)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14d74 retired x11 sourceValue) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14d74
  have source' := (stepPremiseState_writes state 0x14d74).get x8 (by decide) |>.trans source
  have resultEq : iTypeResult .ADDI 0 sourceValue = sourceValue := by
    simp [iTypeResult, show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
  have execute : Runs (execute (.ITYPE (0, .Regidx 8#5, .Regidx 11#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x11 sourceValue } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 8#5) (.Regidx 11#5) .ADDI) _ _ _
    simpa only [resultEq] using execute_ITYPE_run premise _ 0 (.Regidx 8#5)
      (.Regidx 11#5) .ADDI sourceValue (rX_x8_run premise sourceValue source')
      (wX_x11_run premise (iTypeResult .ADDI 0 sourceValue))
  exact configuredRegisterWriteStep stepNo 0x14d74 state x11 sourceValue
    (.ITYPE (0, .Regidx 8#5, .Regidx 11#5, .ADDI)) 0x93 0x05 0x04 0x00
    configured atPc loaded (by
      obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
      have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
          some Privilege.Machine := by
        calc
          _ = state.regs.get? cur_privilege := by
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
          _ = some Privilege.Machine := configured.normal.2.1
      have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
          some seccfgBits := by
        calc
          _ = state.regs.get? mseccfg := by
            simpa [tryStepControlFlowAfterIncrement] using
              writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
          _ = some seccfgBits := seccfgRead
      decode_run) execute (base := by rfl)

private theorem writeSuccessAddiX10FromSpStep (stepNo pc offset : Nat) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8) (state : State) (stackPointer : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (resultEq : iTypeResult .ADDI imm (BitVec.ofNat 64 stackPointer) =
      BitVec.ofNat 64 (stackPointer + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (imm, .Regidx 2#5, .Regidx 10#5, .ADDI)))
    (pcFits : pc < 2 ^ 64) (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x10
        (BitVec.ofNat 64 (stackPointer + offset))) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have source := (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x2
    (by decide) |>.trans stack
  have execute : Runs (execute (.ITYPE (imm, .Regidx 2#5, .Regidx 10#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x10 (BitVec.ofNat 64 (stackPointer + offset)) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE imm (.Regidx 2#5) (.Regidx 10#5) .ADDI) _ _ _
    simpa only [resultEq] using execute_ITYPE_run premise _ imm (.Regidx 2#5)
      (.Regidx 10#5) .ADDI (BitVec.ofNat 64 stackPointer)
      (rX_x2_run premise (BitVec.ofNat 64 stackPointer) source)
      (wX_x10_run premise (iTypeResult .ADDI imm (BitVec.ofNat 64 stackPointer)))
  exact configuredRegisterWriteStep stepNo pc state x10
    (BitVec.ofNat 64 (stackPointer + offset))
    (.ITYPE (imm, .Regidx 2#5, .Regidx 10#5, .ADDI)) byte0 byte1 byte2 byte3
    configured atPc loaded decode execute (pcFits := pcFits) (base := base)
    (read0 := read0) (read1 := read1) (read2 := read2) (read3 := read3)

private theorem writeSuccessAddiX11FromSpStep (stepNo pc offset : Nat) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8) (state : State) (stackPointer : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (resultEq : iTypeResult .ADDI imm (BitVec.ofNat 64 stackPointer) =
      BitVec.ofNat 64 (stackPointer + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (imm, .Regidx 2#5, .Regidx 11#5, .ADDI)))
    (pcFits : pc < 2 ^ 64) (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x11
        (BitVec.ofNat 64 (stackPointer + offset))) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have source := (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x2
    (by decide) |>.trans stack
  have execute : Runs (execute (.ITYPE (imm, .Regidx 2#5, .Regidx 11#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x11 (BitVec.ofNat 64 (stackPointer + offset)) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE imm (.Regidx 2#5) (.Regidx 11#5) .ADDI) _ _ _
    simpa only [resultEq] using execute_ITYPE_run premise _ imm (.Regidx 2#5)
      (.Regidx 11#5) .ADDI (BitVec.ofNat 64 stackPointer)
      (rX_x2_run premise (BitVec.ofNat 64 stackPointer) source)
      (wX_x11_run premise (iTypeResult .ADDI imm (BitVec.ofNat 64 stackPointer)))
  exact configuredRegisterWriteStep stepNo pc state x11
    (BitVec.ofNat 64 (stackPointer + offset))
    (.ITYPE (imm, .Regidx 2#5, .Regidx 11#5, .ADDI)) byte0 byte1 byte2 byte3
    configured atPc loaded decode execute (pcFits := pcFits) (base := base)
    (read0 := read0) (read1 := read1) (read2 := read2) (read3 := read3)

private theorem writeSuccessAddiX12FromZeroStep (stepNo pc value : Nat) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (resultEq : iTypeResult .ADDI imm 0 = BitVec.ofNat 64 value)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (imm, .Regidx 0#5, .Regidx 12#5, .ADDI)))
    (pcFits : pc < 2 ^ 64) (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x12
        (BitVec.ofNat 64 value)) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have execute : Runs (execute (.ITYPE (imm, .Regidx 0#5, .Regidx 12#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x12 (BitVec.ofNat 64 value) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE imm (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    simpa only [resultEq] using execute_ITYPE_run premise _ imm (.Regidx 0#5)
      (.Regidx 12#5) .ADDI 0 (rX_x0_run premise)
      (wX_x12_run premise (iTypeResult .ADDI imm 0))
  exact configuredRegisterWriteStep stepNo pc state x12 (BitVec.ofNat 64 value)
    (.ITYPE (imm, .Regidx 0#5, .Regidx 12#5, .ADDI)) byte0 byte1 byte2 byte3
    configured atPc loaded decode execute (pcFits := pcFits) (base := base)
    (read0 := read0) (read1 := read1) (read2 := read2) (read3 := read3)

private theorem writeSuccessAddiX11FromZeroStep (stepNo pc value : Nat) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (resultEq : iTypeResult .ADDI imm 0 = BitVec.ofNat 64 value)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (imm, .Regidx 0#5, .Regidx 11#5, .ADDI)))
    (pcFits : pc < 2 ^ 64) (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x11
        (BitVec.ofNat 64 value)) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have execute : Runs (execute (.ITYPE (imm, .Regidx 0#5, .Regidx 11#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x11 (BitVec.ofNat 64 value) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE imm (.Regidx 0#5) (.Regidx 11#5) .ADDI) _ _ _
    simpa only [resultEq] using execute_ITYPE_run premise _ imm (.Regidx 0#5)
      (.Regidx 11#5) .ADDI 0 (rX_x0_run premise)
      (wX_x11_run premise (iTypeResult .ADDI imm 0))
  exact configuredRegisterWriteStep stepNo pc state x11 (BitVec.ofNat 64 value)
    (.ITYPE (imm, .Regidx 0#5, .Regidx 11#5, .ADDI)) byte0 byte1 byte2 byte3
    configured atPc loaded decode execute (pcFits := pcFits) (base := base)
    (read0 := read0) (read1 := read1) (read2 := read2) (read3 := read3)

/-- Complete the writer ABI prologue at the first parent-owned payload setup instruction. -/
theorem writeSuccessPrologueHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state) :
    ∃ values next,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessPrologueWrites (writeSuccessFrameMemory args)
        [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
         ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
        fromStep 15 state.machine next 0x14d6c ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  obtain ⟨values, savedState, seg, words, configured⟩ :=
    writeSuccessSavePrologue fromStep args state entry
  rcases entry with ⟨_, lower, _, _, _, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  have stack := seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  have seg0 := seg.forget (kv' := []) (by simp)
  have code := writeSuccessCodeOfSeg access loaded lower seg0
  have source := seg.reg x10 (BitVec.ofNat 64 args.decodedAddress)
    (by simp [writeSuccessIncomingRegs])
  obtain ⟨retired, run⟩ := writeSuccessBindDecodedStep (fromStep + 14) savedState
    (BitVec.ofNat 64 args.decodedAddress) configured seg.atPc source code
  obtain ⟨retired', next, nextEq, seg1⟩ := seg0.stepWitness
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessInitialExitPc; native_decide) x8 (BitVec.ofNat 64 args.decodedAddress) 0x14d6c
    ⟨retired, run⟩ (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping)
    (by simp [writeSuccessPrologueWrites, writeSuccessParentWrites])
    (by decide) (by decide) (by simp [RegsOutside])
  have wordsNext : SavedWordReps next (writeSuccessSavedWords args values) := by
    rw [nextEq]
    simpa only [afterRegisterWrite_mem] using words
  have configuredNext : ConfiguredMachinePre EndpointMachinePc next := by
    rw [nextEq]
    exact ConfiguredMachinePre.afterRegisterWrite 0x14d68 retired' x8
      (BitVec.ofNat 64 args.decodedAddress) configured (by
        intro preserved
        rcases preserved.1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
          h | h | h
        all_goals cases h)
  have stackNext : next.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) := by
    rw [nextEq]
    exact (afterRegisterWrite_writes savedState 0x14d68 retired' x8
      (BitVec.ofNat 64 args.decodedAddress)).get x2 (by decide) |>.trans stack
  exact ⟨values, next, seg1.know x2
    (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) stackNext, wordsNext, configuredNext⟩

/-- Set the three `memcpy` arguments and its call base, ending at the exact call instruction. -/
theorem writeSuccessMemcpyCallSetup (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state) :
    ∃ values next,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
        [⟨x1, 0xfd78⟩, ⟨x11, BitVec.ofNat 64 args.decodedAddress⟩, ⟨x12, 0x2d0⟩,
         ⟨x10, BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x138)⟩,
         ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
         ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
        fromStep 19 state.machine next 0x14d7c ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      ConfiguredMachinePre EndpointMachinePc next := by
  obtain ⟨values, prologueState, prologue, words, configured⟩ :=
    writeSuccessPrologueHandoff fromStep args state entry
  rcases entry with ⟨_, lower, _, fits, decodedEq, _, _, _, _, _, _, _, loaded, _, access, _stable⟩
  have disjoint : RegSet.Disjoint instructionPreserved writeSuccessParentWrites := by
    intro register preserved written
    rcases written with bookkeeping | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact platformPreserved_disjoint register preserved.1 bookkeeping
    all_goals simp [instructionPreserved, platformPreserved] at preserved
  have seg0 := prologue
  have code0 := writeSuccessCodeOfSeg access loaded lower seg0
  obtain ⟨retired0, run0⟩ := writeSuccessMemcpyDestinationStep (fromStep + 15)
    prologueState (args.stackPointer - 0x7d0) configured seg0.atPc
    (seg0.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)) (by omega) code0
  obtain ⟨retired0', state0, state0Eq, seg1⟩ := seg0.stepWitness
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessInitialExitPc; native_decide) x10
    (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x138)) 0x14d70 ⟨retired0, run0⟩
    (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping)
    (by simp [writeSuccessPrologueWrites, writeSuccessParentWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have configured1 := access.configured.mono (seg1.agree disjoint) seg1.retired
  have code1 := writeSuccessCodeOfSeg access loaded lower seg1
  obtain ⟨retired1, run1⟩ := writeSuccessMemcpyLengthStep (fromStep + 16) state0
    configured1 seg1.atPc code1
  obtain ⟨retired1', state1, state1Eq, seg2⟩ := seg1.stepWitness
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessInitialExitPc; native_decide) x12 0x2d0 0x14d74 ⟨retired1, run1⟩
    (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping)
    (by simp [writeSuccessPrologueWrites, writeSuccessParentWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have configured2 := access.configured.mono (seg2.agree disjoint) seg2.retired
  have code2 := writeSuccessCodeOfSeg access loaded lower seg2
  obtain ⟨retired2, run2⟩ := writeSuccessMemcpySourceStep (fromStep + 17) state1
    (BitVec.ofNat 64 args.decodedAddress) configured2 seg2.atPc
    (seg2.reg x8 (BitVec.ofNat 64 args.decodedAddress) (by simp)) code2
  obtain ⟨retired2', state2, state2Eq, seg3⟩ := seg2.stepWitness
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessInitialExitPc; native_decide) x11 (BitVec.ofNat 64 args.decodedAddress) 0x14d78
    ⟨retired2, run2⟩ (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping)
    (by simp [writeSuccessPrologueWrites, writeSuccessParentWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have configured3 := access.configured.mono (seg3.agree disjoint) seg3.retired
  have code3 := writeSuccessCodeOfSeg access loaded lower seg3
  obtain ⟨retired3, run3⟩ := writeSuccessMemcpyCallBaseStep (fromStep + 18) state2
    configured3 seg3.atPc code3
  obtain ⟨retired3', state3, state3Eq, seg4⟩ := seg3.stepWitness
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessInitialExitPc; native_decide) x1 0xfd78 0x14d7c ⟨retired3, run3⟩
    (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping)
    (by simp [writeSuccessPrologueWrites, writeSuccessParentWrites]) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping])
  have words3 : SavedWordReps state3 (writeSuccessSavedWords args values) := by
    rw [state3Eq, state2Eq, state1Eq, state0Eq]
    simpa only [afterRegisterWrite_mem] using words
  exact ⟨values, state3, seg4, words3,
    access.configured.mono (seg4.agree disjoint) seg4.retired⟩

/-- Execute the exact call and discharge the selected `memcpy` instance unconditionally. -/
theorem writeSuccessMemcpyHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state) :
    ∃ values bytes, ∃ tailValues : Fin 16 → Nat, ∃ used after,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        fromStep (20 + used) state after ∧
      EndpointPc after = some 0x14d80 ∧
      BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      BytesRep after.machine.mem args.decodedAddress bytes ∧
      bytes.size = 720 ∧
      RawPayloadFieldBytes bytes args.decoded.payload ∧
      DwordWindowRep after.machine.mem (args.decodedAddress + 720) 16 ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      SavedWordReps after.machine (writeSuccessSavedWords args values) ∧
      after.machine.regs.get? x2 =
        some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) ∧
      after.machine.regs.get? x8 = some (BitVec.ofNat 64 args.decodedAddress) ∧
      Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
      WriteSuccessMachineAccess args after.machine ∧
      WriteSuccessMemoryFrame args state.machine after.machine ∧
      WriteSuccessIoFrame state after := by
  obtain ⟨values, setupState, setup, savedWords, configured⟩ :=
    writeSuccessMemcpyCallSetup fromStep args state entry
  rcases entry with ⟨_, lower, _, fits, decodedEq, _, _, _, _, decodedRep,
    ⟨bytes, bytesSize, sourceRep⟩, ⟨tailValues, tailReps⟩, loaded, _, access, stable⟩
  have code := writeSuccessCodeOfSeg access loaded lower setup
  obtain ⟨retired, callRun⟩ := writeSuccessMemcpyCallStep (fromStep + 19) setupState
    configured setup.atPc (setup.reg x1 0xfd78 (by simp)) code
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement setupState) 0x14d7c 0x101d4 x1 0x14d80)
    0x101d4 retired
  let callState : EndpointState := { state with machine := callMachine }
  have callAtPc : callMachine.regs.get? PC = some 0x101d4 := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callWrites := callRetirement_writes setupState 0x14d7c 0x101d4 retired x1 0x14d80
  have callConfigured : ConfiguredMachinePre EndpointMachinePc callMachine :=
    configuredAfterWriteSuccessCall 0x14d7c 0x101d4 0x14d80 retired configured
  have sourceAtSetup : BytesRep setupState.mem args.decodedAddress bytes := by
    refine ⟨sourceRep.1, ?_⟩
    intro index indexBound
    rw [setup.mem (args.decodedAddress + index) (by
      intro inside
      unfold writeSuccessFrameMemory byteRange at inside
      rw [decodedEq] at inside
      omega)]
    exact sourceRep.2 index indexBound
  have sourceAtCall : BytesRep callMachine.mem args.decodedAddress bytes := by
    simpa [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      sourceAtSetup
  have wholeWrites : WritesOnlyRegs writeSuccessParentWrites state.machine callMachine :=
    setup.writes.trans_same (callWrites.mono (by
      intro register written
      rcases written with bookkeeping | rfl
      · exact Or.inl bookkeeping
      · exact Or.inr (Or.inl rfl)))
  have pmaEq := wholeWrites.get pma_regions (by
    simp [writeSuccessParentWrites, stepBookkeeping])
  let memcpyArgs : MemcpyArgs :=
    { returnAddress := 0x14d80
      destination := args.stackPointer - 0x7d0 + 0x138
      source := args.decodedAddress
      bytes }
  have memcpyEntry : MemcpyEntry memcpyArgs callState := by
    refine ⟨(show 0x14d80 ∈ Elflings.memcpyExitPcs by native_decide),
      (by simp [memcpyArgs, bytesSize]), ?_, sourceAtCall.1, ?_,
      ?_, ?_, ?_, ?_, ?_, sourceAtCall, ?_, ?_⟩
    · dsimp [memcpyArgs]
      rw [bytesSize]
      omega
    · left
      dsimp [memcpyArgs]
      rw [bytesSize, decodedEq]
      omega
    · simpa [callState, EndpointPc, MachinePc] using callAtPc
    · simp [memcpyArgs, callState, callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        callLinkState, Std.ExtDHashMap.get?_insert]
    · exact (callWrites.get x10 (by decide)).trans
        (setup.reg x10 (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x138)) (by simp))
    · exact (callWrites.get x11 (by decide)).trans
        (setup.reg x11 (BitVec.ofNat 64 args.decodedAddress) (by simp))
    · rw [bytesSize]
      exact (callWrites.get x12 (by decide)).trans (setup.reg x12 0x2d0 (by simp))
    · simpa [callState, callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]
        using code
    · refine
        { configured := callConfigured
          sourcePma := ?_
          destinationPma := ?_
          sourceNotMMIO := ?_
          destinationNotMMIO := ?_
          destinationNotCode := ?_ }
      · intro index indexBound
        rw [bytesSize] at indexBound
        dsimp [memcpyArgs]
        rw [decodedEq]
        exact dataPmaAllows_of_pma_regions_eq pmaEq (by
          simpa [Nat.add_assoc] using access.decodedLoad (0x20 + index) 1 (by omega))
      · intro index indexBound
        rw [bytesSize] at indexBound
        change StorePmaAllows callMachine
          (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x138 + index)) 1
        have original := access.frameStore (0x138 + index) 1 (by omega)
        have moved := dataPmaAllows_of_pma_regions_eq pmaEq original
        simpa [Nat.add_assoc] using moved
      · intro index indexBound
        rw [bytesSize] at indexBound
        dsimp [memcpyArgs]
        rw [decodedEq]
        simpa [Nat.add_assoc] using access.decodedNoMMIO (0x20 + index) 1 (by omega)
      · intro index indexBound
        rw [bytesSize] at indexBound
        change StoreMMIOAddressExcluded
          (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x138 + index)) 1
        simpa [Nat.add_assoc] using access.frameNoMMIO (0x138 + index) 1 (by omega)
      · intro index indexBound
        rw [bytesSize] at indexBound
        change Artifacts.programImage.readFileByte?
          (args.stackPointer - 0x7d0 + 0x138 + index) = none
        exact access.frameNotCode _ (by omega) (by omega)
  obtain ⟨memcpyBound, memcpyImpl⟩ := memcpyInstanceContract
  obtain ⟨used, after, unit, positive, bounded, childTrace, childExitPc, _allowed,
    childExit⟩ := memcpyImpl memcpyArgs (fromStep + 20) callState memcpyEntry
  have endTrace : ScopedTrace writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) (fromStep + 20) 0 callMachine callMachine :=
    .exitAt (fromStep + 20) callMachine 0x101d4 callAtPc (Or.inl rfl)
  have callPrefix : ConfinedPrefix writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) (fromStep + 19) 1 setupState callMachine :=
    ConfinedPrefix.ownStep setup.atPc
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide) callRun
  have parentMachineTrace := setup.confined.trans callPrefix 0 callMachine endTrace
  have parentTrace := liftWriteSuccessParentTrace state (by
    simpa [Nat.add_assoc] using parentMachineTrace)
  have childTrace' := childTrace.weaken (fun _ inside => memcpyPc_in_writeSuccess inside)
  have fullTrace := parentTrace.append childTrace'
  rcases childExit with ⟨childPc, stdin, cursor, stdout, exitCode, destinationRep,
    sourceRepAfter, codeAfter, childMem, childFrame⟩
  have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact (savedWords word member).of_writesOnlyWithin childMem (by
      intro index indexBound inside
      unfold byteRange at inside
      simp [memcpyArgs, bytesSize] at inside
      have addressLower : args.stackPointer - 0x7d0 + 0x768 ≤ word.1 := by
        simp [writeSuccessSavedWords] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> omega
      omega)
  have configuredAfter := configuredAfterEndpointCall callConfigured childFrame
  have childPmaEq : after.machine.regs.get? pma_regions = state.machine.regs.get? pma_regions :=
    (childFrame.1 pma_regions (by simp [abiCalleePreserved])).trans pmaEq
  have accessAfter : WriteSuccessMachineAccess args after.machine :=
    { configured := configuredAfter
      frameLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq childPmaEq (access.frameLoad offset width inBounds)
      frameStore := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq childPmaEq (access.frameStore offset width inBounds)
      frameNoMMIO := access.frameNoMMIO
      decodedLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq childPmaEq (access.decodedLoad offset width inBounds)
      decodedNoMMIO := access.decodedNoMMIO
      outputBufferStore := dataPmaAllows_of_pma_regions_eq childPmaEq access.outputBufferStore
      outputLengthStore := dataPmaAllows_of_pma_regions_eq childPmaEq access.outputLengthStore
      writerRegionBeforeOutputContext := access.writerRegionBeforeOutputContext
      frameNotCode := access.frameNotCode }
  have parentMemory : WriteSuccessMemoryFrame args state.machine callMachine := by
    intro address outside
    simpa [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      setup.mem address outside
  have childMemory : WriteSuccessMemoryFrame args callMachine after.machine :=
    childMem.mono (by
      intro address inside
      unfold byteRange at inside
      unfold writeSuccessFrameMemory byteRange
      simp [memcpyArgs, bytesSize] at inside
      omega)
  have wholeMemory : WriteSuccessMemoryFrame args state.machine after.machine :=
    WritesOnlyWithin.trans_same parentMemory childMemory
  have payloadFields := decodedRep.rawPayloadFields.of_writesOnlyWithin wholeMemory (by
    intro offset width bound index indexBound inside
    unfold writeSuccessFrameMemory byteRange at inside
    rw [decodedEq] at inside
    omega)
  have payloadFieldBytes : RawPayloadFieldBytes bytes args.decoded.payload :=
    payloadFields.fieldBytes sourceRepAfter (by omega)
  have tailAfterReps : ∀ index (inBounds : index < 16),
      UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
        (tailValues ⟨index, inBounds⟩) := by
    intro index inBounds
    have atSetup := (tailReps index inBounds).of_writesOnlyWithin setup.mem (by
      intro byte byteBound inside
      unfold writeSuccessFrameMemory byteRange at inside
      rw [decodedEq] at inside
      omega)
    exact atSetup.of_writesOnlyWithin childMem (by
      intro byte byteBound inside
      unfold byteRange at inside
      simp [memcpyArgs, bytesSize] at inside
      rw [decodedEq] at inside
      omega)
  have tailAfter : DwordWindowRep after.machine.mem (args.decodedAddress + 720) 16 :=
    ⟨tailValues, tailAfterReps⟩
  refine ⟨values, bytes, tailValues, used, after, ?_, ?_, destinationRep, sourceRepAfter,
    bytesSize, payloadFieldBytes, tailAfter, tailAfterReps, savedAfter, ?_, ?_, codeAfter, accessAfter,
    wholeMemory, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using fullTrace
  · simpa [EndpointPc, MachinePc, memcpyArgs] using childPc
  · exact (childFrame.1 x2 (by simp [abiCalleePreserved])).trans
      ((callWrites.get x2 (by decide)).trans
        (setup.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)))
  · exact (childFrame.1 x8 (by simp [abiCalleePreserved])).trans
      ((callWrites.get x8 (by decide)).trans
        (setup.reg x8 (BitVec.ofNat 64 args.decodedAddress) (by simp)))
  · exact ⟨by simpa [callState] using stdin, by simpa [callState] using cursor,
      by simpa [callState] using stdout, by simpa [callState] using exitCode⟩

/-- Append the first parent-owned decoded-tail load after the unconditional `memcpy`. -/
theorem writeSuccessFirstTailLoadHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state) :
    ∃ values bytes, ∃ tailValues : Fin 16 → Nat, ∃ used after next,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        fromStep (20 + used) state after ∧
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
        [⟨x10, BitVec.ofNat 64 (tailValues ⟨0, by omega⟩)⟩,
         ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
         ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
        (fromStep + 20 + used) 1 after.machine next 0x14d84 ∧
      BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      BytesRep after.machine.mem args.decodedAddress bytes ∧
      bytes.size = 720 ∧
      RawPayloadFieldBytes bytes args.decoded.payload ∧
      DwordWindowRep after.machine.mem (args.decodedAddress + 720) 16 ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      SavedWordReps after.machine (writeSuccessSavedWords args values) ∧
      Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
      WriteSuccessMachineAccess args after.machine ∧
      DwordWindowRep next.mem (args.decodedAddress + 720) 16 ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 next.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      Artifacts.programImage.fileBytesLoadedFaithfully next.mem ∧
      WriteSuccessMachineAccess args next ∧
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMemoryFrame args state.machine after.machine ∧
      WriteSuccessIoFrame state after := by
  obtain ⟨values, bytes, tailValues, used, after, trace, atPc, _destinationRep, sourceRep,
    bytesSize, fieldBytes, _tailWindow, tailReps, saved, stackRead, baseRead, loaded, access, memoryFrame,
    ioFrame⟩ :=
    writeSuccessMemcpyHandoff fromStep args state entry
  rcases entry with ⟨_, lower, aligned, _, decodedEq, _, _, _, _, _, _, _, _, _, _, _⟩
  let kv : List RegVal :=
    [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
     ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
  have seg0 : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
      kv (fromStep + 20 + used) 0 after.machine after.machine 0x14d80 :=
    { trace := .refl _ _
      confined := .nil
      writes := .refl _ _
      mem := fun _ _ => rfl
      retired := access.configured.retiredCounter
      atPc := atPc
      regs := by
        intro pair member
        simp only [kv, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact stackRead
        · exact baseRead }
  obtain ⟨retired, run⟩ := writeSuccessLoadDecoded720 (fromStep + 20 + used)
    (tailValues ⟨0, by omega⟩) args after.machine access decodedEq aligned atPc baseRead
    (tailReps 0 (by omega)) loaded
  obtain ⟨retired', next, nextEq, seg1⟩ := seg0.stepWitness
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessInitialExitPc; native_decide) x10
    (BitVec.ofNat 64 (tailValues ⟨0, by omega⟩)) 0x14d84 ⟨retired, run⟩
    (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping)
    (by simp [writeSuccessParentWrites]) (by decide) (by decide)
    (by simp [kv, RegsOutside, stepBookkeeping])
  have tailNextReps : ∀ index (inBounds : index < 16),
      UIntRep 8 next.mem (args.decodedAddress + 720 + index * 8)
        (tailValues ⟨index, inBounds⟩) := by
    intro index inBounds
    rw [nextEq]
    simpa only [afterRegisterWrite_mem] using tailReps index inBounds
  have tailNext : DwordWindowRep next.mem (args.decodedAddress + 720) 16 :=
    ⟨tailValues, tailNextReps⟩
  have savedNext : SavedWordReps next (writeSuccessSavedWords args values) := by
    intro word member
    rw [nextEq]
    simpa only [afterRegisterWrite_mem] using saved word member
  have codeNext := writeSuccessCodeOfSeg access loaded lower seg1
  have initializedAfter :
      InitializedByteWindow after.machine.mem (args.stackPointer - 0x7d0 + 0x138) 720 :=
    ⟨bytes, bytesSize, _destinationRep⟩
  have initializedNext :
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 := by
    rw [nextEq]
    simpa only [afterRegisterWrite_mem] using initializedAfter
  have destinationNext : BytesRep next.mem
      (args.stackPointer - 0x7d0 + 0x138) bytes := by
    rw [nextEq]
    simpa only [afterRegisterWrite_mem] using _destinationRep
  exact ⟨values, bytes, tailValues, used, after, next, trace, seg1, _destinationRep, sourceRep,
    bytesSize, fieldBytes, ⟨tailValues, tailReps⟩, tailReps, saved, loaded, access, tailNext,
    tailNextReps, savedNext, codeNext, writeSuccessAccessOfSeg access seg1, destinationNext,
    initializedNext,
    memoryFrame, ioFrame⟩

def writeSuccessLocalTailWords (args : WriteSuccessArgs) (values : Fin 16 → Nat) :
    List (Nat × Nat) :=
  let sp := args.stackPointer - 0x7d0
  [(sp + 0x18, values ⟨0, by omega⟩), (sp + 0x10, values ⟨1, by omega⟩),
   (sp + 0x28, values ⟨2, by omega⟩), (sp + 0x20, values ⟨3, by omega⟩),
   (sp + 0x38, values ⟨4, by omega⟩), (sp + 0x30, values ⟨5, by omega⟩),
   (sp + 0x40, values ⟨6, by omega⟩), (sp + 0x48, values ⟨7, by omega⟩),
   (sp + 0x08, values ⟨8, by omega⟩), (sp + 0x50, values ⟨9, by omega⟩),
   (sp + 0x128, values ⟨10, by omega⟩), (sp + 0x130, values ⟨11, by omega⟩),
   (sp + 0x118, values ⟨12, by omega⟩), (sp + 0x120, values ⟨13, by omega⟩),
   (sp + 0x60, values ⟨14, by omega⟩), (sp + 0x58, values ⟨15, by omega⟩)]

def WriteSuccessLocalTailReps (args : WriteSuccessArgs) (state : EndpointState) : Prop :=
  ∃ values : Fin 16 → Nat,
    InlineEncoderSavedWords state.machine.mem (writeSuccessLocalTailWords args values)

/-- The copied local words paired with the exact decoded-tail words from which they were loaded.
This is the semantic link needed by the later witness and chain-configuration encoders. -/
def WriteSuccessLinkedTailReps (args : WriteSuccessArgs) (state : EndpointState) : Prop :=
  ∃ values : Fin 16 → Nat,
    InlineEncoderSavedWords state.machine.mem (writeSuccessLocalTailWords args values) ∧
    ∀ index (bound : index < 16),
      UIntRep 8 state.machine.mem (args.decodedAddress + 720 + index * 8)
        (values ⟨index, bound⟩)

private theorem WriteSuccessLinkedTailReps.value_eq
    {args : WriteSuccessArgs} {state : EndpointState} {values : Fin 16 → Nat}
    {index value : Nat}
    (linked : InlineEncoderSavedWords state.machine.mem
      (writeSuccessLocalTailWords args values) ∧
      ∀ index (bound : index < 16),
        UIntRep 8 state.machine.mem (args.decodedAddress + 720 + index * 8)
          (values ⟨index, bound⟩))
    (bound : index < 16)
    (semantic : UIntRep 8 state.machine.mem
      (args.decodedAddress + 720 + index * 8) value) :
    values ⟨index, bound⟩ = value :=
  UIntRep.eight_unique (linked.2 index bound) semantic

def writeSuccessLocalTailOffset : Nat → Nat
  | 0 => 0x18 | 1 => 0x10 | 2 => 0x28 | 3 => 0x20
  | 4 => 0x38 | 5 => 0x30 | 6 => 0x40 | 7 => 0x48
  | 8 => 0x08 | 9 => 0x50 | 10 => 0x128 | 11 => 0x130
  | 12 => 0x118 | 13 => 0x120 | 14 => 0x60 | 15 => 0x58
  | _ => 0

/-- Select one of the sixteen concrete local tail words without repeatedly simplifying the list. -/
private theorem writeSuccessLocalTailRep {args : WriteSuccessArgs} {state : EndpointState}
    {values : Fin 16 → Nat}
    (reps : InlineEncoderSavedWords state.machine.mem (writeSuccessLocalTailWords args values))
    (index : Nat) (bound : index < 16) :
    UIntRep 8 state.machine.mem
      (args.stackPointer - 0x7d0 + writeSuccessLocalTailOffset index)
      (values ⟨index, bound⟩) := by
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨
      index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [writeSuccessLocalTailOffset] <;>
    apply reps (_, _) <;> simp [writeSuccessLocalTailWords]

/-- A one-byte semantic tag is retained by an eight-byte linked-tail copy. -/
private theorem writeSuccessLocalTailTagRep {args : WriteSuccessArgs} {state : EndpointState}
    {values : Fin 16 → Nat}
    (localReps : InlineEncoderSavedWords state.machine.mem
      (writeSuccessLocalTailWords args values))
    (source : ∀ index (bound : index < 16),
      UIntRep 8 state.machine.mem (args.decodedAddress + 720 + index * 8)
        (values ⟨index, bound⟩))
    (index : Nat) (bound : index < 16) {value : Nat}
    (semantic : UIntRep 1 state.machine.mem
      (args.decodedAddress + 720 + index * 8) value) :
    UIntRep 1 state.machine.mem
      (args.stackPointer - 0x7d0 + writeSuccessLocalTailOffset index) value := by
  have localWord := writeSuccessLocalTailRep localReps index bound
  have sourceWord := source index bound
  have localFits := localWord.2.1
  refine ⟨semantic.1, by omega, ?_⟩
  intro byte byteBound
  calc
    state.machine.mem.get?
        (args.stackPointer - 0x7d0 + writeSuccessLocalTailOffset index + byte) =
        some _ := localWord.2.2 byte (by omega)
    _ = state.machine.mem.get? (args.decodedAddress + 720 + index * 8 + byte) :=
      (sourceWord.2.2 byte (by omega)).symm
    _ = some _ := semantic.2.2 byte byteBound

def WriteSuccessLocalTailPrefix (args : WriteSuccessArgs) (values : Fin 16 → Nat)
    (count : Nat) (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ index (bound : index < 16), index < count →
    UIntRep 8 mem (args.stackPointer - 0x7d0 + writeSuccessLocalTailOffset index)
      (values ⟨index, bound⟩)

private theorem writeSuccessLocalTailOffset_disjoint {index count : Nat}
    (old : index < count) (bound : count < 16) :
    writeSuccessLocalTailOffset index + 8 ≤ writeSuccessLocalTailOffset count ∨
      writeSuccessLocalTailOffset count + 8 ≤ writeSuccessLocalTailOffset index := by
  have indexCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨
      index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 := by omega
  have countCases : count = 1 ∨ count = 2 ∨ count = 3 ∨ count = 4 ∨ count = 5 ∨
      count = 6 ∨ count = 7 ∨ count = 8 ∨ count = 9 ∨ count = 10 ∨ count = 11 ∨
      count = 12 ∨ count = 13 ∨ count = 14 ∨ count = 15 := by omega
  rcases indexCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    rcases countCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
    simp_all [writeSuccessLocalTailOffset]

private theorem writeSuccessLocalTailPrefix_succ {args values count before after}
    (prior : WriteSuccessLocalTailPrefix args values count before.mem)
    (writes : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 + writeSuccessLocalTailOffset count) 8)
      before after)
    (countBound : count < 16)
    (current : UIntRep 8 after.mem
      (args.stackPointer - 0x7d0 + writeSuccessLocalTailOffset count)
      (values ⟨count, countBound⟩)) :
    WriteSuccessLocalTailPrefix args values (count + 1) after.mem := by
  intro index bound below
  by_cases old : index < count
  · exact (prior index bound old).of_writesOnlyWithin writes (by
      intro byte byteBound inside
      unfold byteRange at inside
      rcases writeSuccessLocalTailOffset_disjoint old countBound with before | after
      · omega
      · omega)
  · have : index = count := by omega
    subst index
    exact current

private theorem writeSuccessLocalTailPrefix_after_store {args values count storeIndex before after}
    (prior : WriteSuccessLocalTailPrefix args values count before.mem)
    (writes : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 + writeSuccessLocalTailOffset storeIndex) 8)
      before after)
    (ordered : count ≤ storeIndex) (storeBound : storeIndex < 16) :
    WriteSuccessLocalTailPrefix args values count after.mem := by
  intro index bound below
  exact (prior index bound below).of_writesOnlyWithin writes (by
    intro byte byteBound inside
    unfold byteRange at inside
    rcases writeSuccessLocalTailOffset_disjoint (index := index) (count := storeIndex)
      (by omega) storeBound with before | after
    · omega
    · omega)

private theorem inlineEncoderSavedWords_cons {mem} {word : Nat × Nat} {words}
    (head : UIntRep 8 mem word.1 word.2) (tail : InlineEncoderSavedWords mem words) :
    InlineEncoderSavedWords mem (word :: words) := by
  intro current member
  simp only [List.mem_cons] at member
  exact member.elim (fun eq => eq ▸ head) (tail current)

/-- Append `0x14d84: sd a0,24(sp)` after the first decoded-tail load. -/
theorem writeSuccessFirstTailPairHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state) :
    ∃ values bytes, ∃ tailValues : Fin 16 → Nat, ∃ used after next,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        fromStep (20 + used) state after ∧
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
        [⟨x10, BitVec.ofNat 64 (tailValues ⟨0, by omega⟩)⟩,
         ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
         ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
        (fromStep + 20 + used) 2 after.machine next 0x14d88 ∧
      BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      BytesRep after.machine.mem args.decodedAddress bytes ∧
      bytes.size = 720 ∧
      RawPayloadFieldBytes bytes args.decoded.payload ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
      WriteSuccessMachineAccess args after.machine ∧
      DwordWindowRep next.mem (args.decodedAddress + 720) 16 ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 next.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      UIntRep 8 next.mem (args.stackPointer - 0x7d0 + 0x18)
        (tailValues ⟨0, by omega⟩) ∧
      Artifacts.programImage.fileBytesLoadedFaithfully next.mem ∧
      WriteSuccessMachineAccess args next ∧
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMemoryFrame args state.machine after.machine ∧
      WriteSuccessIoFrame state after := by
  obtain ⟨values, bytes, tailValues, used, after, loadedState, trace, loadedSeg,
    destinationRep, sourceRep, bytesSize, fieldBytes, _tailWindowAtBase, tailAtBase, _savedAtBase, loadedAtBase,
    accessAtBase, _tailWindowAtLoad, _tailAtLoad, savedAtLoad, _loadedAtLoad, accessAtLoad,
    destinationAtLoad, initializedAtLoad, memoryFrame, ioFrame⟩ :=
    writeSuccessFirstTailLoadHandoff fromStep args state entry
  rcases entry with ⟨_, lower, aligned, fits, decodedEq, _, _, _, _, _, _, _, _, _, _, _⟩
  refine ⟨values, bytes, tailValues, used, after, ?_⟩
  obtain ⟨next, seg2, words2, _configured2, retired2, nextEq⟩ :=
    writeSuccessSaveStepExact loadedSeg accessAtBase
    accessAtLoad.configured loadedAtBase lower fits (writeSuccessSavedWords args values)
    savedAtLoad 0x14d84 0x18 (BitVec.ofNat 64 (tailValues ⟨0, by omega⟩)) 0x18
    (.Regidx 10#5) 0x23 0x3c 0xa1 0x00
    (loadedSeg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    (fun premise writes => rX_x10_run premise (BitVec.ofNat 64 (tailValues ⟨0, by omega⟩))
      ((writes.get x10 (by decide)).trans
        (loadedSeg.reg x10 (BitVec.ofNat 64 (tailValues ⟨0, by omega⟩)) (by simp))))
    (by
      intro word member
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
    (by omega) (by omega) rfl
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessInitialExitPc; native_decide)
    (by
      intro configured
      obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
        writeSuccessStoreDecodeReads configured
      decode_run)
    (by
      change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x18#64 = _
      rw [← BitVec.ofNat_add])
    (by simp [RegsOutside, stepBookkeeping])
    (by native_decide) (by rfl) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have tailNextReps : ∀ index (inBounds : index < 16),
      UIntRep 8 next.mem (args.decodedAddress + 720 + index * 8)
        (tailValues ⟨index, inBounds⟩) := by
    intro index inBounds
    exact (tailAtBase index inBounds).of_writesOnlyWithin seg2.mem (by
      intro byte byteBound inside
      unfold writeSuccessFrameMemory byteRange at inside
      rw [decodedEq] at inside
      omega)
  have tailNext : DwordWindowRep next.mem (args.decodedAddress + 720) 16 :=
    ⟨tailValues, tailNextReps⟩
  have savedNext : SavedWordReps next (writeSuccessSavedWords args values) := by
    intro word member
    exact words2 word (by simp [member])
  have stored0 : UIntRep 8 next.mem (args.stackPointer - 0x7d0 + 0x18)
      (tailValues ⟨0, by omega⟩) := by
    have valueEq : (BitVec.ofNat 64 (tailValues ⟨0, by omega⟩)).toNat =
        tailValues ⟨0, by omega⟩ := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (tailAtBase 0 (by omega)).1]
    rw [valueEq] at words2
    exact words2 _ (List.mem_cons_self)
  have initializedNext := initializedByteWindow_of_writeSuccessStore initializedAtLoad nextEq
  have destinationNext := bytesRep_of_writeSuccessStore destinationAtLoad (by omega) nextEq
  exact ⟨next, trace, seg2, destinationRep, sourceRep, bytesSize, fieldBytes, tailAtBase, loadedAtBase, accessAtBase,
    tailNext, tailNextReps, savedNext, stored0,
    writeSuccessCodeOfSeg accessAtBase loadedAtBase lower seg2,
    writeSuccessAccessOfSeg accessAtBase seg2, destinationNext, initializedNext, memoryFrame, ioFrame⟩

/-- Reusable exact `ld a0,offset(s0); sd a0,slot(sp)` pair for the decoded writer tail. -/
private theorem writeSuccessTailPairStep {a n : Nat} {base cur : State} {bytes : Array UInt8}
    (args : WriteSuccessArgs) (values : DecodeCalleeSavedValues)
    (tailValues : Fin 16 → Nat) (index : Nat) (inBounds : index < 16)
    (loadPc storePc loadOffset storeOffset : Nat) (loadImm storeImm : BitVec 12)
    (load0 load1 load2 load3 store0 store1 store2 store3 : UInt8)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
      [⟨x10, BitVec.ofNat 64 (tailValues ⟨index - 1, by omega⟩)⟩,
       ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
       ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
      a n base cur (BitVec.ofNat 64 loadPc))
    (access : WriteSuccessMachineAccess args base)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (lower : 0x880 ≤ args.stackPointer) (fits : args.stackPointer < 2 ^ 64)
    (aligned : args.stackPointer % 16 = 0)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20)
    (tailBase : ∀ i (bound : i < 16),
      UIntRep 8 base.mem (args.decodedAddress + 720 + i * 8) (tailValues ⟨i, bound⟩))
    (saved : SavedWordReps cur (writeSuccessSavedWords args values))
    (initialized : InitializedByteWindow cur.mem
      (args.stackPointer - 0x7d0 + 0x138) 720)
    (copied : BytesRep cur.mem (args.stackPointer - 0x7d0 + 0x138) bytes)
    (loadOffsetEq : loadOffset = 720 + index * 8)
    (loadOffsetBound : 0x20 + loadOffset + 8 ≤ 0x380)
    (storeBound : storeOffset + 8 ≤ 0x7d0)
    (storeBeforeCopied : storeOffset + 8 ≤ 0x138)
    (loadAddressEq : BitVec.ofNat 64 args.decodedAddress + sign_extend (m := 64) loadImm =
      BitVec.ofNat 64 (args.decodedAddress + loadOffset))
    (storeAddressEq : BitVec.ofNat 64 (args.stackPointer - 0x7d0) +
      sign_extend (m := 64) storeImm =
      BitVec.ofNat 64 (args.stackPointer - 0x7d0 + storeOffset))
    (loadDecode : ∀ configured : ConfiguredMachinePre EndpointMachinePc cur,
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 load0.toNat) (BitVec.ofNat 8 load1.toNat)
        (BitVec.ofNat 8 load2.toNat) (BitVec.ofNat 8 load3.toNat)))
        (tryStepControlFlowAfterIncrement cur) (tryStepControlFlowAfterIncrement cur)
        (.LOAD (loadImm, .Regidx 8#5, .Regidx 10#5, false, 8)))
    (storeDecode : ∀ state : State, ConfiguredMachinePre EndpointMachinePc state →
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 store0.toNat) (BitVec.ofNat 8 store1.toNat)
        (BitVec.ofNat 8 store2.toNat) (BitVec.ofNat 8 store3.toNat)))
        (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
        (.STORE (storeImm, .Regidx 10#5, .Regidx 2#5, 8)))
    (loadRead0 : Artifacts.programImage.readFileByte? loadPc = some load0)
    (loadRead1 : Artifacts.programImage.readFileByte? (loadPc + 1) = some load1)
    (loadRead2 : Artifacts.programImage.readFileByte? (loadPc + 2) = some load2)
    (loadRead3 : Artifacts.programImage.readFileByte? (loadPc + 3) = some load3)
    (storeRead0 : Artifacts.programImage.readFileByte? storePc = some store0)
    (storeRead1 : Artifacts.programImage.readFileByte? (storePc + 1) = some store1)
    (storeRead2 : Artifacts.programImage.readFileByte? (storePc + 2) = some store2)
    (storeRead3 : Artifacts.programImage.readFileByte? (storePc + 3) = some store3)
    (loadPcFits : loadPc < 2 ^ 64) (storePcFits : storePc < 2 ^ 64)
    (loadInRegion : writeSuccessParentPc (BitVec.ofNat 64 loadPc))
    (storeInRegion : writeSuccessParentPc (BitVec.ofNat 64 storePc))
    (loadNotExit : ¬writeSuccessInitialExitPc (BitVec.ofNat 64 loadPc))
    (storeNotExit : ¬writeSuccessInitialExitPc (BitVec.ofNat 64 storePc))
    (loadBase : BaseInstructionEncoding (BitVec.ofNat 8 load0.toNat))
    (storeBase : BaseInstructionEncoding (BitVec.ofNat 8 store0.toNat))
    (storeAligned : (args.stackPointer - 0x7d0 + storeOffset) % 8 = 0)
    (storeBelowSaved : storeOffset + 8 ≤ 0x748)
    (loadAdvance : Sail.BitVec.addInt (BitVec.ofNat 64 loadPc) 4 = BitVec.ofNat 64 storePc)
    (storeAdvance : Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4 =
      BitVec.ofNat 64 (storePc + 4)) :
    ∃ next,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
        [⟨x10, BitVec.ofNat 64 (tailValues ⟨index, inBounds⟩)⟩,
         ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
         ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
        a (n + 2) base next (BitVec.ofNat 64 (storePc + 4)) ∧
      (∀ i (bound : i < 16),
        UIntRep 8 next.mem (args.decodedAddress + 720 + i * 8) (tailValues ⟨i, bound⟩)) ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      UIntRep 8 next.mem (args.stackPointer - 0x7d0 + storeOffset)
        (tailValues ⟨index, inBounds⟩) ∧
      WritesOnlyWithin (byteRange (args.stackPointer - 0x7d0 + storeOffset) 8)
        cur next ∧
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMachineAccess args next := by
  let kv : List RegVal :=
    [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
     ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
  have seg0 := seg.forget (kv' := kv) (by simp [kv])
  have access0 := writeSuccessAccessOfSeg access seg0
  have code0 := writeSuccessCodeOfSeg access loaded lower seg0
  have tailCur : UIntRep 8 cur.mem (args.decodedAddress + loadOffset)
      (tailValues ⟨index, inBounds⟩) := by
    rw [loadOffsetEq]
    simpa [Nat.add_assoc] using (tailBase index inBounds).of_writesOnlyWithin seg0.mem (by
      intro byte byteBound inside
      unfold writeSuccessFrameMemory byteRange at inside
      rw [decodedEq] at inside
      omega)
  obtain ⟨retired0, run0⟩ := writeSuccessDecodedDwordLoadStep (a + n) loadPc loadOffset
    (tailValues ⟨index, inBounds⟩) args cur (.Regidx 10#5) x10
    (BitVec.ofNat 64 (tailValues ⟨index, inBounds⟩)) loadImm load0 load1 load2 load3
    access0 decodedEq seg0.atPc
    (seg0.reg x8 (BitVec.ofNat 64 args.decodedAddress) (by simp [kv])) tailCur
    loadOffsetBound (by rw [decodedEq, loadOffsetEq]; omega) code0 loadAddressEq
    (fun premise => wX_x10_run premise (BitVec.ofNat 64 (tailValues ⟨index, inBounds⟩)))
    loadDecode (by decide) (by decide) (by decide) (by decide)
    (pcFits := loadPcFits) (base := loadBase) (read0 := loadRead0) (read1 := loadRead1)
    (read2 := loadRead2) (read3 := loadRead3)
  obtain ⟨retired0', loadedState, loadedEq, seg1⟩ := seg0.stepWitness
    loadInRegion loadNotExit x10
    (BitVec.ofNat 64 (tailValues ⟨index, inBounds⟩)) (BitVec.ofNat 64 storePc)
    ⟨retired0, run0⟩ loadAdvance (fun _ bookkeeping => Or.inl bookkeeping)
    (by simp [writeSuccessParentWrites]) (by decide) (by decide)
    (by simp [kv, RegsOutside, stepBookkeeping])
  have savedLoaded : SavedWordReps loadedState (writeSuccessSavedWords args values) := by
    intro word member
    rw [loadedEq]
    simpa only [afterRegisterWrite_mem] using saved word member
  have access1 := writeSuccessAccessOfSeg access seg1
  have initializedLoaded : InitializedByteWindow loadedState.mem
      (args.stackPointer - 0x7d0 + 0x138) 720 := by
    rw [loadedEq]
    simpa only [afterRegisterWrite_mem] using initialized
  have copiedLoaded : BytesRep loadedState.mem
      (args.stackPointer - 0x7d0 + 0x138) bytes := by
    rw [loadedEq]
    simpa only [afterRegisterWrite_mem] using copied
  obtain ⟨next, seg2, words2, _configured2, _retired2, nextEq⟩ :=
    writeSuccessSaveStepExact seg1 access
    access1.configured loaded lower fits (writeSuccessSavedWords args values) savedLoaded
    storePc storeOffset (BitVec.ofNat 64 (tailValues ⟨index, inBounds⟩)) storeImm
    (.Regidx 10#5) store0 store1 store2 store3
    (seg1.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp [kv]))
    (fun premise writes => rX_x10_run premise (BitVec.ofNat 64 (tailValues ⟨index, inBounds⟩))
      ((writes.get x10 (by decide)).trans
        (seg1.reg x10 (BitVec.ofNat 64 (tailValues ⟨index, inBounds⟩)) (by simp))))
    (by
      intro word member
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
    storeBound storeAligned rfl storeInRegion storeNotExit (storeDecode loadedState)
    storeAddressEq (by simp [kv, RegsOutside, stepBookkeeping])
    storePcFits storeBase storeRead0 storeRead1 storeRead2 storeRead3 storeAdvance
  have tailNext : ∀ i (bound : i < 16),
      UIntRep 8 next.mem (args.decodedAddress + 720 + i * 8) (tailValues ⟨i, bound⟩) := by
    intro i bound
    exact (tailBase i bound).of_writesOnlyWithin seg2.mem (by
      intro byte byteBound inside
      unfold writeSuccessFrameMemory byteRange at inside
      rw [decodedEq] at inside
      omega)
  have savedNext : SavedWordReps next (writeSuccessSavedWords args values) := by
    intro word member
    exact words2 word (by simp [member])
  have storedNext : UIntRep 8 next.mem (args.stackPointer - 0x7d0 + storeOffset)
      (tailValues ⟨index, inBounds⟩) := by
    have valueEq : (BitVec.ofNat 64 (tailValues ⟨index, inBounds⟩)).toNat =
        tailValues ⟨index, inBounds⟩ := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (tailBase index inBounds).1]
    rw [valueEq] at words2
    exact words2 (args.stackPointer - 0x7d0 + storeOffset,
      tailValues ⟨index, inBounds⟩) (List.mem_cons_self)
  have storeWrites : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 + storeOffset) 8) loadedState next := by
    intro address outside
    rw [nextEq]
    exact storeRetirement_mem_writes loadedState (BitVec.ofNat 64 storePc)
      (Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4) _
      (args.stackPointer - 0x7d0 + storeOffset)
      (BitVec.ofNat 64 (tailValues ⟨index, inBounds⟩)) address outside
  have loadMem : loadedState.mem = cur.mem := by rw [loadedEq]; rfl
  have pairWrites : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 + storeOffset) 8) cur next :=
    WritesOnlyWithin.trans_same (writesOnlyWithin_of_mem_eq loadMem) storeWrites
  have initializedNext := initializedByteWindow_of_writeSuccessStore initializedLoaded nextEq
  have copiedNext := bytesRep_of_writeSuccessStore copiedLoaded (by omega) nextEq
  exact ⟨next, by simpa [Nat.add_assoc] using seg2, tailNext, savedNext, storedNext, pairWrites,
    copiedNext, initializedNext,
    writeSuccessAccessOfSeg access seg2⟩

/-- Extend the writer tail through the second exact load/store pair, ending at `0x14d90`. -/
theorem writeSuccessSecondTailPairHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state) :
    ∃ values bytes, ∃ tailValues : Fin 16 → Nat, ∃ used after next,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        fromStep (20 + used) state after ∧
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
        [⟨x10, BitVec.ofNat 64 (tailValues ⟨1, by omega⟩)⟩,
         ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
         ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
        (fromStep + 20 + used) 4 after.machine next 0x14d90 ∧
      BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      BytesRep after.machine.mem args.decodedAddress bytes ∧
      bytes.size = 720 ∧
      RawPayloadFieldBytes bytes args.decoded.payload ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
      WriteSuccessMachineAccess args after.machine ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 next.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      WriteSuccessLocalTailPrefix args tailValues 2 next.mem ∧
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMachineAccess args next ∧
      WriteSuccessMemoryFrame args state.machine after.machine ∧
      WriteSuccessIoFrame state after := by
  obtain ⟨values, bytes, tailValues, used, after, first, trace, seg, destinationRep,
    sourceRep, bytesSize, fieldBytes, tailBase, loaded, access, _tailWindow, tailFirst, saved,
    stored0, _code, _accessFirst,
    copiedFirst, initializedFirst, memoryFrame, ioFrame⟩ :=
    writeSuccessFirstTailPairHandoff fromStep args state entry
  rcases entry with ⟨_, lower, aligned, fits, decodedEq, _, _, _, _, _, _, _, _, _, _, _⟩
  obtain ⟨next, seg2, tailNext, savedNext, stored1, pairWrites, copiedNext, initializedNext,
    accessNext⟩ :=
    writeSuccessTailPairStep args values tailValues 1 (by omega)
      0x14d88 0x14d8c 728 0x10 0x2d8 0x10
      0x03 0x35 0x84 0x2d 0x23 0x38 0xa1 0x00 seg access loaded lower fits aligned
      decodedEq tailBase saved initializedFirst copiedFirst (by omega) (by omega) (by omega)
      (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x2d8#64 = _;
          rw [← BitVec.ofNat_add])
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x10#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by rfl) (by omega) (by omega) (by native_decide) (by native_decide)
  have local1 : WriteSuccessLocalTailPrefix args tailValues 1 first.mem := by
    intro index bound below
    have : index = 0 := by omega
    subst index
    simpa [writeSuccessLocalTailOffset] using stored0
  have local2 : WriteSuccessLocalTailPrefix args tailValues 2 next.mem := by
    apply writeSuccessLocalTailPrefix_succ (count := 1) (countBound := by decide)
      local1 pairWrites
    simpa [writeSuccessLocalTailOffset] using stored1
  exact ⟨values, bytes, tailValues, used, after, next, trace, seg2, destinationRep, sourceRep, bytesSize,
    fieldBytes, tailBase, loaded, access, tailNext, savedNext, local2, copiedNext, initializedNext, accessNext,
    memoryFrame, ioFrame⟩

/-- Compose the first ten decoded-tail load/store pairs, ending at `0x14dd0`. -/
theorem writeSuccessFirstTenTailPairsHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state) :
    ∃ values bytes, ∃ tailValues : Fin 16 → Nat, ∃ used after next,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        fromStep (20 + used) state after ∧
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
        [⟨x10, BitVec.ofNat 64 (tailValues ⟨9, by omega⟩)⟩,
         ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
         ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
        (fromStep + 20 + used) 20 after.machine next 0x14dd0 ∧
      BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      BytesRep after.machine.mem args.decodedAddress bytes ∧
      bytes.size = 720 ∧
      RawPayloadFieldBytes bytes args.decoded.payload ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
      WriteSuccessMachineAccess args after.machine ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 next.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      WriteSuccessLocalTailPrefix args tailValues 10 next.mem ∧
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMachineAccess args next ∧
      WriteSuccessMemoryFrame args state.machine after.machine ∧
      WriteSuccessIoFrame state after := by
  obtain ⟨values, bytes, tailValues, used, after, cur1, trace, seg1, destinationRep,
    sourceRep, bytesSize, fieldBytes, tailBase, loaded, access, tail1, saved1, local2,
    copied1, initialized1, access1, memoryFrame,
    ioFrame⟩ :=
    writeSuccessSecondTailPairHandoff fromStep args state entry
  rcases entry with ⟨_, lower, aligned, fits, decodedEq, _, _, _, _, _, _, _, _, _, _, _⟩
  obtain ⟨cur2, seg2, tail2, saved2, stored2, pairWrites2, copied2, initialized2, access2⟩ :=
    writeSuccessTailPairStep args values tailValues 2 (by omega)
      0x14d90 0x14d94 736 0x28 0x2e0 0x28
      0x03 0x35 0x04 0x2e 0x23 0x34 0xa1 0x02 seg1 access loaded lower fits aligned
      decodedEq tailBase saved1 initialized1 copied1 (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x2e0#64 = _;
          rw [← BitVec.ofNat_add])
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x28#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by rfl) (by omega) (by omega) (by native_decide) (by native_decide)
  have local3 := writeSuccessLocalTailPrefix_succ (count := 2) (countBound := by decide)
    local2 pairWrites2 (by simpa [writeSuccessLocalTailOffset] using stored2)
  obtain ⟨cur3, seg3, tail3, saved3, stored3, pairWrites3, copied3, initialized3, access3⟩ :=
    writeSuccessTailPairStep args values tailValues 3 (by omega)
      0x14d98 0x14d9c 744 0x20 0x2e8 0x20
      0x03 0x35 0x84 0x2e 0x23 0x30 0xa1 0x02 seg2 access loaded lower fits aligned
      decodedEq tailBase saved2 initialized2 copied2 (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x2e8#64 = _;
          rw [← BitVec.ofNat_add])
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x20#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by rfl) (by omega) (by omega) (by native_decide) (by native_decide)
  have local4 := writeSuccessLocalTailPrefix_succ (count := 3) (countBound := by decide)
    local3 pairWrites3 (by simpa [writeSuccessLocalTailOffset] using stored3)
  obtain ⟨cur4, seg4, tail4, saved4, stored4, pairWrites4, copied4, initialized4, access4⟩ :=
    writeSuccessTailPairStep args values tailValues 4 (by omega)
      0x14da0 0x14da4 752 0x38 0x2f0 0x38
      0x03 0x35 0x04 0x2f 0x23 0x3c 0xa1 0x02 seg3 access loaded lower fits aligned
      decodedEq tailBase saved3 initialized3 copied3 (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x2f0#64 = _;
          rw [← BitVec.ofNat_add])
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x38#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by rfl) (by omega) (by omega) (by native_decide) (by native_decide)
  have local5 := writeSuccessLocalTailPrefix_succ (count := 4) (countBound := by decide)
    local4 pairWrites4 (by simpa [writeSuccessLocalTailOffset] using stored4)
  obtain ⟨cur5, seg5, tail5, saved5, stored5, pairWrites5, copied5, initialized5, access5⟩ :=
    writeSuccessTailPairStep args values tailValues 5 (by omega)
      0x14da8 0x14dac 760 0x30 0x2f8 0x30
      0x03 0x35 0x84 0x2f 0x23 0x38 0xa1 0x02 seg4 access loaded lower fits aligned
      decodedEq tailBase saved4 initialized4 copied4 (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x2f8#64 = _;
          rw [← BitVec.ofNat_add])
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x30#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by rfl) (by omega) (by omega) (by native_decide) (by native_decide)
  have local6 := writeSuccessLocalTailPrefix_succ (count := 5) (countBound := by decide)
    local5 pairWrites5 (by simpa [writeSuccessLocalTailOffset] using stored5)
  obtain ⟨cur6, seg6, tail6, saved6, stored6, pairWrites6, copied6, initialized6, access6⟩ :=
    writeSuccessTailPairStep args values tailValues 6 (by omega)
      0x14db0 0x14db4 768 0x40 0x300 0x40
      0x03 0x35 0x04 0x30 0x23 0x30 0xa1 0x04 seg5 access loaded lower fits aligned
      decodedEq tailBase saved5 initialized5 copied5 (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x300#64 = _;
          rw [← BitVec.ofNat_add])
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x40#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by rfl) (by omega) (by omega) (by native_decide) (by native_decide)
  have local7 := writeSuccessLocalTailPrefix_succ (count := 6) (countBound := by decide)
    local6 pairWrites6 (by simpa [writeSuccessLocalTailOffset] using stored6)
  obtain ⟨cur7, seg7, tail7, saved7, stored7, pairWrites7, copied7, initialized7, access7⟩ :=
    writeSuccessTailPairStep args values tailValues 7 (by omega)
      0x14db8 0x14dbc 776 0x48 0x308 0x48
      0x03 0x35 0x84 0x30 0x23 0x34 0xa1 0x04 seg6 access loaded lower fits aligned
      decodedEq tailBase saved6 initialized6 copied6 (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x308#64 = _;
          rw [← BitVec.ofNat_add])
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x48#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by rfl) (by omega) (by omega) (by native_decide) (by native_decide)
  have local8 := writeSuccessLocalTailPrefix_succ (count := 7) (countBound := by decide)
    local7 pairWrites7 (by simpa [writeSuccessLocalTailOffset] using stored7)
  obtain ⟨cur8, seg8, tail8, saved8, stored8, pairWrites8, copied8, initialized8, access8⟩ :=
    writeSuccessTailPairStep args values tailValues 8 (by omega)
      0x14dc0 0x14dc4 784 0x08 0x310 0x08
      0x03 0x35 0x04 0x31 0x23 0x34 0xa1 0x00 seg7 access loaded lower fits aligned
      decodedEq tailBase saved7 initialized7 copied7 (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x310#64 = _;
          rw [← BitVec.ofNat_add])
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x08#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by rfl) (by omega) (by omega) (by native_decide) (by native_decide)
  have local9 := writeSuccessLocalTailPrefix_succ (count := 8) (countBound := by decide)
    local8 pairWrites8 (by simpa [writeSuccessLocalTailOffset] using stored8)
  obtain ⟨cur9, seg9, tail9, saved9, stored9, pairWrites9, copied9, initialized9, access9⟩ :=
    writeSuccessTailPairStep args values tailValues 9 (by omega)
      0x14dc8 0x14dcc 792 0x50 0x318 0x50
      0x03 0x35 0x84 0x31 0x23 0x38 0xa1 0x04 seg8 access loaded lower fits aligned
      decodedEq tailBase saved8 initialized8 copied8 (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x318#64 = _;
          rw [← BitVec.ofNat_add])
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x50#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by rfl) (by omega) (by omega) (by native_decide) (by native_decide)
  have local10 := writeSuccessLocalTailPrefix_succ (count := 9) (countBound := by decide)
    local9 pairWrites9 (by simpa [writeSuccessLocalTailOffset] using stored9)
  exact ⟨values, bytes, tailValues, used, after, cur9, trace, seg9, destinationRep,
    sourceRep, bytesSize, fieldBytes, tailBase, loaded, access, tail9, saved9, local10,
    copied9, initialized9, access9,
    memoryFrame, ioFrame⟩

/-- Append one exact decoded-tail load while retaining the earlier live tail values. -/
private theorem writeSuccessTailLoadStep {a n : Nat} {base cur : State} {kv : List RegVal}
    {bytes : Array UInt8}
    (args : WriteSuccessArgs) (values : DecodeCalleeSavedValues)
    (tailValues : Fin 16 → Nat) (index : Nat) (inBounds : index < 16)
    (loadPc loadOffset : Nat) (loadImm : BitVec 12)
    (load0 load1 load2 load3 : UInt8) (rd : regidx) (destination : Register)
    (result : RegisterType destination)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
      kv a n base cur (BitVec.ofNat 64 loadPc))
    (access : WriteSuccessMachineAccess args base)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (stackLower : 0x880 ≤ args.stackPointer)
    (stackAligned : args.stackPointer % 16 = 0)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20)
    (tailBase : ∀ i (bound : i < 16),
      UIntRep 8 base.mem (args.decodedAddress + 720 + i * 8) (tailValues ⟨i, bound⟩))
    (saved : SavedWordReps cur (writeSuccessSavedWords args values))
    (initialized : InitializedByteWindow cur.mem
      (args.stackPointer - 0x7d0 + 0x138) 720)
    (copied : BytesRep cur.mem (args.stackPointer - 0x7d0 + 0x138) bytes)
    (baseHeld : ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩ ∈ kv)
    (loadOffsetEq : loadOffset = 720 + index * 8)
    (loadOffsetBound : 0x20 + loadOffset + 8 ≤ 0x380)
    (loadAddressEq : BitVec.ofNat 64 args.decodedAddress + sign_extend (m := 64) loadImm =
      BitVec.ofNat 64 (args.decodedAddress + loadOffset))
    (loadDecode : ∀ configured : ConfiguredMachinePre EndpointMachinePc cur,
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 load0.toNat) (BitVec.ofNat 8 load1.toNat)
        (BitVec.ofNat 8 load2.toNat) (BitVec.ofNat 8 load3.toNat)))
        (tryStepControlFlowAfterIncrement cur) (tryStepControlFlowAfterIncrement cur)
        (.LOAD (loadImm, .Regidx 8#5, rd, false, 8)))
    (writeRun : ∀ premise,
      Runs (wX_bits rd (BitVec.ofNat 64 (tailValues ⟨index, inBounds⟩))) premise
        { premise with regs := premise.regs.insert destination result } ())
    (loadRead0 : Artifacts.programImage.readFileByte? loadPc = some load0)
    (loadRead1 : Artifacts.programImage.readFileByte? (loadPc + 1) = some load1)
    (loadRead2 : Artifacts.programImage.readFileByte? (loadPc + 2) = some load2)
    (loadRead3 : Artifacts.programImage.readFileByte? (loadPc + 3) = some load3)
    (loadPcFits : loadPc < 2 ^ 64)
    (loadInRegion : writeSuccessParentPc (BitVec.ofNat 64 loadPc))
    (loadNotExit : ¬writeSuccessInitialExitPc (BitVec.ofNat 64 loadPc))
    (loadBase : BaseInstructionEncoding (BitVec.ofNat 8 load0.toNat))
    (destinationInWrites : writeSuccessParentWrites destination)
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotPc : destination ≠ PC) (destinationNotRetired : destination ≠ minstret)
    (keep : RegsOutside (RegSet.union stepBookkeeping (RegSet.only destination)) kv)
    (loadAdvance : Sail.BitVec.addInt (BitVec.ofNat 64 loadPc) 4 =
      BitVec.ofNat 64 (loadPc + 4)) :
    ∃ next,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
        (⟨destination, result⟩ :: kv)
        a (n + 1) base next (BitVec.ofNat 64 (loadPc + 4)) ∧
      (∀ i (bound : i < 16),
        UIntRep 8 next.mem (args.decodedAddress + 720 + i * 8) (tailValues ⟨i, bound⟩)) ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      next.mem = cur.mem ∧
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMachineAccess args next := by
  have accessCur := writeSuccessAccessOfSeg access seg
  have codeCur := writeSuccessCodeOfSeg access loaded stackLower seg
  have tailCur : UIntRep 8 cur.mem (args.decodedAddress + loadOffset)
      (tailValues ⟨index, inBounds⟩) := by
    rw [loadOffsetEq]
    simpa [Nat.add_assoc] using (tailBase index inBounds).of_writesOnlyWithin seg.mem (by
      intro byte byteBound inside
      unfold writeSuccessFrameMemory byteRange at inside
      rw [decodedEq] at inside
      omega)
  obtain ⟨retired, run⟩ := writeSuccessDecodedDwordLoadStep (a + n) loadPc loadOffset
    (tailValues ⟨index, inBounds⟩) args cur rd destination
    result loadImm load0 load1 load2 load3
    accessCur decodedEq seg.atPc
    (seg.reg x8 (BitVec.ofNat 64 args.decodedAddress) baseHeld) tailCur loadOffsetBound
    (by rw [decodedEq, loadOffsetEq]; omega) codeCur loadAddressEq writeRun loadDecode
    destinationNotNextPc destinationNotHart destinationNotIncrement destinationNotRetired
    (pcFits := loadPcFits) (base := loadBase) (read0 := loadRead0) (read1 := loadRead1)
    (read2 := loadRead2) (read3 := loadRead3)
  obtain ⟨retired', next, nextEq, nextSeg⟩ := seg.stepWitness loadInRegion loadNotExit
    destination result
    (BitVec.ofNat 64 (loadPc + 4)) ⟨retired, run⟩ loadAdvance
    (fun _ bookkeeping => Or.inl bookkeeping) destinationInWrites destinationNotPc
    destinationNotRetired keep
  have tailNext : ∀ i (bound : i < 16),
      UIntRep 8 next.mem (args.decodedAddress + 720 + i * 8) (tailValues ⟨i, bound⟩) := by
    intro i bound
    exact (tailBase i bound).of_writesOnlyWithin nextSeg.mem (by
      intro byte byteBound inside
      unfold writeSuccessFrameMemory byteRange at inside
      rw [decodedEq] at inside
      omega)
  have savedNext : SavedWordReps next (writeSuccessSavedWords args values) := by
    intro word member
    rw [nextEq]
    simpa only [afterRegisterWrite_mem] using saved word member
  have initializedNext : InitializedByteWindow next.mem
      (args.stackPointer - 0x7d0 + 0x138) 720 := by
    rw [nextEq]
    simpa only [afterRegisterWrite_mem] using initialized
  have copiedNext : BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes := by
    rw [nextEq]
    simpa only [afterRegisterWrite_mem] using copied
  exact ⟨next, nextSeg, tailNext, savedNext, by rw [nextEq]; rfl, copiedNext, initializedNext,
    writeSuccessAccessOfSeg access nextSeg⟩

/-- Load the next four writer-tail words into `a0..a3`, ending at `0x14de0`. -/
theorem writeSuccessFirstFourFinalLoadsHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state) :
    ∃ values bytes, ∃ tailValues : Fin 16 → Nat, ∃ used after next,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        fromStep (20 + used) state after ∧
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
        [⟨x13, BitVec.ofNat 64 (tailValues ⟨13, by omega⟩)⟩,
         ⟨x12, BitVec.ofNat 64 (tailValues ⟨12, by omega⟩)⟩,
         ⟨x11, BitVec.ofNat 64 (tailValues ⟨11, by omega⟩)⟩,
         ⟨x10, BitVec.ofNat 64 (tailValues ⟨10, by omega⟩)⟩,
         ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
         ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
        (fromStep + 20 + used) 24 after.machine next 0x14de0 ∧
      BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      BytesRep after.machine.mem args.decodedAddress bytes ∧
      bytes.size = 720 ∧
      RawPayloadFieldBytes bytes args.decoded.payload ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
      WriteSuccessMachineAccess args after.machine ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 next.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      WriteSuccessLocalTailPrefix args tailValues 10 next.mem ∧
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMachineAccess args next ∧
      WriteSuccessMemoryFrame args state.machine after.machine ∧
      WriteSuccessIoFrame state after := by
  obtain ⟨values, bytes, tailValues, used, after, cur9, trace, seg9, destinationRep,
    sourceRep, bytesSize, fieldBytes, tailBase, loaded, access, _tail9, saved9, local10,
    copied9, initialized9, _access9, memoryFrame,
    ioFrame⟩ :=
    writeSuccessFirstTenTailPairsHandoff fromStep args state entry
  rcases entry with ⟨_, lower, aligned, _, decodedEq, _, _, _, _, _, _, _, _, _, _, _⟩
  let kv0 : List RegVal :=
    [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
     ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
  have seg0 := seg9.forget (kv' := kv0) (by simp [kv0])
  obtain ⟨cur10, seg10, tail10, saved10, mem10, copied10, initialized10, access10⟩ :=
    writeSuccessTailLoadStep args values tailValues 10 (by omega) 0x14dd0 800
      0x320 0x03 0x35 0x04 0x32 (.Regidx 10#5) x10
      (BitVec.ofNat 64 (tailValues ⟨10, by omega⟩)) seg0 access loaded lower aligned
      decodedEq tailBase saved9 initialized9 copied9
      (by simp [kv0]) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x320#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (fun premise => wX_x10_run premise
        (BitVec.ofNat 64 (tailValues ⟨10, by omega⟩)))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by simp [writeSuccessParentWrites]) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by simp [kv0, RegsOutside, stepBookkeeping])
      (by native_decide)
  obtain ⟨cur11, seg11, tail11, saved11, mem11, copied11, initialized11, access11⟩ :=
    writeSuccessTailLoadStep args values tailValues 11 (by omega) 0x14dd4 808
      0x328 0x83 0x35 0x84 0x32 (.Regidx 11#5) x11
      (BitVec.ofNat 64 (tailValues ⟨11, by omega⟩)) seg10 access loaded lower aligned
      decodedEq tailBase saved10 initialized10 copied10
      (by simp [kv0]) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x328#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (fun premise => wX_x11_run premise
        (BitVec.ofNat 64 (tailValues ⟨11, by omega⟩)))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by simp [writeSuccessParentWrites]) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by simp [kv0, RegsOutside, stepBookkeeping])
      (by native_decide)
  obtain ⟨cur12, seg12, tail12, saved12, mem12, copied12, initialized12, access12⟩ :=
    writeSuccessTailLoadStep args values tailValues 12 (by omega) 0x14dd8 816
      0x330 0x03 0x36 0x04 0x33 (.Regidx 12#5) x12
      (BitVec.ofNat 64 (tailValues ⟨12, by omega⟩)) seg11 access loaded lower aligned
      decodedEq tailBase saved11 initialized11 copied11
      (by simp [kv0]) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x330#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (fun premise => wX_x12_run premise
        (BitVec.ofNat 64 (tailValues ⟨12, by omega⟩)))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by simp [writeSuccessParentWrites]) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by simp [kv0, RegsOutside, stepBookkeeping])
      (by native_decide)
  obtain ⟨cur13, seg13, tail13, saved13, mem13, copied13, initialized13, access13⟩ :=
    writeSuccessTailLoadStep args values tailValues 13 (by omega) 0x14ddc 824
      0x338 0x83 0x36 0x84 0x33 (.Regidx 13#5) x13
      (BitVec.ofNat 64 (tailValues ⟨13, by omega⟩)) seg12 access loaded lower aligned
      decodedEq tailBase saved12 initialized12 copied12
      (by simp [kv0]) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x338#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (fun premise => wX_x13_run premise
        (BitVec.ofNat 64 (tailValues ⟨13, by omega⟩)))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by simp [writeSuccessParentWrites]) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by simp [kv0, RegsOutside, stepBookkeeping])
      (by native_decide)
  have local10At13 : WriteSuccessLocalTailPrefix args tailValues 10 cur13.mem := by
    rw [mem13, mem12, mem11, mem10]
    exact local10
  exact ⟨values, bytes, tailValues, used, after, cur13, trace,
    by simpa [Nat.add_assoc] using seg13, destinationRep, sourceRep, bytesSize, fieldBytes, tailBase, loaded, access,
    tail13, saved13, local10At13, copied13, initialized13, access13, memoryFrame, ioFrame⟩

/-- Append one exact child-frame store while retaining tail values and ABI saves. -/
private theorem writeSuccessTailStoreStep {a n : Nat} {base cur : State} {kv : List RegVal}
    {bytes : Array UInt8}
    (args : WriteSuccessArgs) (values : DecodeCalleeSavedValues)
    (tailValues : Fin 16 → Nat) (sourceValue : Nat)
    (storePc storeOffset : Nat) (storeImm : BitVec 12) (rs2 : regidx)
    (store0 store1 store2 store3 : UInt8)
    (seg : Seg writeSuccessParentPc writeSuccessInitialExitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
      kv a n base cur (BitVec.ofNat 64 storePc))
    (access : WriteSuccessMachineAccess args base)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (stackLower : 0x880 ≤ args.stackPointer) (stackFits : args.stackPointer < 2 ^ 64)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20)
    (tailBase : ∀ i (bound : i < 16),
      UIntRep 8 base.mem (args.decodedAddress + 720 + i * 8) (tailValues ⟨i, bound⟩))
    (saved : SavedWordReps cur (writeSuccessSavedWords args values))
    (initialized : InitializedByteWindow cur.mem
      (args.stackPointer - 0x7d0 + 0x138) 720)
    (copied : BytesRep cur.mem (args.stackPointer - 0x7d0 + 0x138) bytes)
    (stackHeld : ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ∈ kv)
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping cur premise →
      Runs (rX_bits rs2) premise premise (BitVec.ofNat 64 sourceValue))
    (sourceFits : sourceValue < 2 ^ 64)
    (storeBound : storeOffset + 8 ≤ 0x7d0)
    (storeBeforeCopied : storeOffset + 8 ≤ 0x138)
    (storeBelowSaved : storeOffset + 8 ≤ 0x748)
    (storeAligned : (args.stackPointer - 0x7d0 + storeOffset) % 8 = 0)
    (storeAddressEq : BitVec.ofNat 64 (args.stackPointer - 0x7d0) +
      sign_extend (m := 64) storeImm =
      BitVec.ofNat 64 (args.stackPointer - 0x7d0 + storeOffset))
    (storeDecode : ∀ state : State, ConfiguredMachinePre EndpointMachinePc state →
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 store0.toNat) (BitVec.ofNat 8 store1.toNat)
        (BitVec.ofNat 8 store2.toNat) (BitVec.ofNat 8 store3.toNat)))
        (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
        (.STORE (storeImm, rs2, .Regidx 2#5, 8)))
    (storeRead0 : Artifacts.programImage.readFileByte? storePc = some store0)
    (storeRead1 : Artifacts.programImage.readFileByte? (storePc + 1) = some store1)
    (storeRead2 : Artifacts.programImage.readFileByte? (storePc + 2) = some store2)
    (storeRead3 : Artifacts.programImage.readFileByte? (storePc + 3) = some store3)
    (storePcFits : storePc < 2 ^ 64)
    (storeInRegion : writeSuccessParentPc (BitVec.ofNat 64 storePc))
    (storeNotExit : ¬writeSuccessInitialExitPc (BitVec.ofNat 64 storePc))
    (storeBase : BaseInstructionEncoding (BitVec.ofNat 8 store0.toNat))
    (keep : RegsOutside stepBookkeeping kv)
    (storeAdvance : Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4 =
      BitVec.ofNat 64 (storePc + 4)) :
    ∃ next,
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
        kv a (n + 1) base next (BitVec.ofNat 64 (storePc + 4)) ∧
      (∀ i (bound : i < 16),
        UIntRep 8 next.mem (args.decodedAddress + 720 + i * 8) (tailValues ⟨i, bound⟩)) ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      UIntRep 8 next.mem (args.stackPointer - 0x7d0 + storeOffset) sourceValue ∧
      WritesOnlyWithin (byteRange (args.stackPointer - 0x7d0 + storeOffset) 8) cur next ∧
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMachineAccess args next := by
  have accessCur := writeSuccessAccessOfSeg access seg
  obtain ⟨next, nextSeg, wordsNext, _configuredNext, _retiredNext, nextEq⟩ :=
    writeSuccessSaveStepExact seg access
    accessCur.configured loaded stackLower stackFits (writeSuccessSavedWords args values) saved
    storePc storeOffset (BitVec.ofNat 64 sourceValue) storeImm rs2
    store0 store1 store2 store3
    (seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) stackHeld) dataRun
    (by
      intro word member
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
    storeBound storeAligned rfl storeInRegion storeNotExit (storeDecode cur)
    storeAddressEq keep storePcFits storeBase storeRead0 storeRead1 storeRead2 storeRead3
    storeAdvance
  have tailNext : ∀ i (bound : i < 16),
      UIntRep 8 next.mem (args.decodedAddress + 720 + i * 8) (tailValues ⟨i, bound⟩) := by
    intro i bound
    exact (tailBase i bound).of_writesOnlyWithin nextSeg.mem (by
      intro byte byteBound inside
      unfold writeSuccessFrameMemory byteRange at inside
      rw [decodedEq] at inside
      omega)
  have savedNext : SavedWordReps next (writeSuccessSavedWords args values) := by
    intro word member
    exact wordsNext word (by simp [member])
  have storedNext : UIntRep 8 next.mem
      (args.stackPointer - 0x7d0 + storeOffset) sourceValue := by
    have valueEq : (BitVec.ofNat 64 sourceValue).toNat = sourceValue := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sourceFits]
    rw [valueEq] at wordsNext
    exact wordsNext (args.stackPointer - 0x7d0 + storeOffset, sourceValue)
      (List.mem_cons_self)
  have storeWrites : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 + storeOffset) 8) cur next := by
    intro address outside
    rw [nextEq]
    exact storeRetirement_mem_writes cur (BitVec.ofNat 64 storePc)
      (Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4) _
      (args.stackPointer - 0x7d0 + storeOffset) (BitVec.ofNat 64 sourceValue)
      address outside
  have initializedNext := initializedByteWindow_of_writeSuccessStore initialized nextEq
  have copiedNext := bytesRep_of_writeSuccessStore copied (by omega) nextEq
  exact ⟨next, nextSeg, tailNext, savedNext, storedNext, storeWrites, copiedNext, initializedNext,
    writeSuccessAccessOfSeg access nextSeg⟩

/-- Complete the 32-instruction decoded-tail transfer, ending at encoder prefix `0x14e00`. -/
theorem writeSuccessTailSegmentHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (state : EndpointState) (entry : WriteSuccessEntry args state) :
    ∃ values bytes, ∃ tailValues : Fin 16 → Nat, ∃ used after next,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        fromStep (20 + used) state after ∧
      Seg writeSuccessParentPc writeSuccessInitialExitPc
        (fun _ _ _ _ _ => False) writeSuccessParentWrites (writeSuccessFrameMemory args)
        [⟨x14, BitVec.ofNat 64 (tailValues ⟨15, by omega⟩)⟩,
         ⟨x13, BitVec.ofNat 64 (tailValues ⟨13, by omega⟩)⟩,
         ⟨x12, BitVec.ofNat 64 (tailValues ⟨12, by omega⟩)⟩,
         ⟨x11, BitVec.ofNat 64 (tailValues ⟨11, by omega⟩)⟩,
         ⟨x10, BitVec.ofNat 64 (tailValues ⟨10, by omega⟩)⟩,
         ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
         ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
        (fromStep + 20 + used) 32 after.machine next 0x14e00 ∧
      BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      BytesRep after.machine.mem args.decodedAddress bytes ∧
      bytes.size = 720 ∧
      RawPayloadFieldBytes bytes args.decoded.payload ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 next.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      SavedWordReps next (writeSuccessSavedWords args values) ∧
      WriteSuccessLocalTailReps args { state with machine := next } ∧
      WriteSuccessLinkedTailReps args { state with machine := next } ∧
      Artifacts.programImage.fileBytesLoadedFaithfully next.mem ∧
      WriteSuccessMachineAccess args next ∧
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMemoryFrame args state.machine next ∧
      WriteSuccessIoFrame state after := by
  obtain ⟨values, bytes, tailValues, used, after, cur13, trace, seg13, destinationRep,
    sourceRep, bytesSize, fieldBytes, tailBase, loaded, access, _tail13, saved13, local10,
    copied13, initialized13, _access13, memoryFrame,
    ioFrame⟩ :=
    writeSuccessFirstFourFinalLoadsHandoff fromStep args state entry
  rcases entry with ⟨_, lower, aligned, fits, decodedEq, _, _, _, _, _, _, _, _, _, _, _⟩
  let kvBase : List RegVal := [⟨x13, BitVec.ofNat 64 (tailValues ⟨13, by omega⟩)⟩,
     ⟨x12, BitVec.ofNat 64 (tailValues ⟨12, by omega⟩)⟩,
     ⟨x11, BitVec.ofNat 64 (tailValues ⟨11, by omega⟩)⟩,
     ⟨x10, BitVec.ofNat 64 (tailValues ⟨10, by omega⟩)⟩,
     ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
     ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
  obtain ⟨curL14, segL14, tailL14, savedL14, memL14, copiedL14, initializedL14, accessL14⟩ :=
    writeSuccessTailLoadStep args values tailValues 14 (by omega) 0x14de0 832
      0x340 0x03 0x37 0x04 0x34 (.Regidx 14#5) x14
      (BitVec.ofNat 64 (tailValues ⟨14, by omega⟩)) seg13 access loaded lower aligned
      decodedEq tailBase saved13 initialized13 copied13
      (by simp) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x340#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (fun premise => wX_x14_run premise
        (BitVec.ofNat 64 (tailValues ⟨14, by omega⟩)))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by simp [writeSuccessParentWrites]) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
      (by native_decide)
  let kvWith14 : List RegVal :=
    ⟨x14, BitVec.ofNat 64 (tailValues ⟨14, by omega⟩)⟩ :: kvBase
  obtain ⟨curS14, segS14, tailS14, savedS14, stored14, writes14, copiedS14, initializedS14,
    accessS14⟩ :=
    writeSuccessTailStoreStep args values tailValues (tailValues ⟨14, by omega⟩)
      0x14de4 0x60 0x60 (.Regidx 14#5) 0x23 0x30 0xe1 0x06 segL14 access loaded
      lower fits decodedEq tailBase savedL14 initializedL14 copiedL14 (by simp)
      (fun premise writes => rX_x14_run premise
        (BitVec.ofNat 64 (tailValues ⟨14, by omega⟩))
        ((writes.get x14 (by decide)).trans
          (segL14.reg x14 (BitVec.ofNat 64 (tailValues ⟨14, by omega⟩))
            (by simp))))
      (tailBase 14 (by omega)).1
      (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x60#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by simp [RegsOutside, stepBookkeeping]) (by native_decide)
  have segF14 := segS14.forget (kv' := kvBase) (by simp [kvBase])
  obtain ⟨curL15, segL15, tailL15, savedL15, memL15, copiedL15, initializedL15, accessL15⟩ :=
    writeSuccessTailLoadStep args values tailValues 15 (by omega) 0x14de8 840
      0x348 0x03 0x37 0x84 0x34 (.Regidx 14#5) x14
      (BitVec.ofNat 64 (tailValues ⟨15, by omega⟩)) segF14 access loaded lower aligned
      decodedEq tailBase savedS14 initializedS14 copiedS14
      (by simp [kvBase]) (by omega) (by omega)
      (by change BitVec.ofNat 64 args.decodedAddress + 0x348#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured
        decode_run)
      (fun premise => wX_x14_run premise
        (BitVec.ofNat 64 (tailValues ⟨15, by omega⟩)))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by simp [writeSuccessParentWrites]) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by simp [kvBase, RegsOutside, stepBookkeeping])
      (by native_decide)
  let kvFinal : List RegVal :=
    ⟨x14, BitVec.ofNat 64 (tailValues ⟨15, by omega⟩)⟩ :: kvBase
  obtain ⟨curS15, segS15, tailS15, savedS15, stored15, writes15, copiedS15, initializedS15,
    accessS15⟩ :=
    writeSuccessTailStoreStep args values tailValues (tailValues ⟨15, by omega⟩)
      0x14dec 0x58 0x58 (.Regidx 14#5) 0x23 0x3c 0xe1 0x04 segL15 access loaded
      lower fits decodedEq tailBase savedL15 initializedL15 copiedL15 (by simp [kvBase])
      (fun premise writes => rX_x14_run premise
        (BitVec.ofNat 64 (tailValues ⟨15, by omega⟩))
        ((writes.get x14 (by decide)).trans
          (segL15.reg x14 (BitVec.ofNat 64 (tailValues ⟨15, by omega⟩))
            (by simp [kvBase]))))
      (tailBase 15 (by omega)).1
      (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x58#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by simp [kvBase, RegsOutside, stepBookkeeping]) (by native_decide)
  obtain ⟨curS10, segS10, tailS10, savedS10, stored10, writes10, copiedS10, initializedS10,
    accessS10⟩ :=
    writeSuccessTailStoreStep args values tailValues (tailValues ⟨10, by omega⟩)
      0x14df0 0x128 0x128 (.Regidx 10#5) 0x23 0x34 0xa1 0x12 segS15 access loaded
      lower fits decodedEq tailBase savedS15 initializedS15 copiedS15 (by simp [kvBase])
      (fun premise writes => rX_x10_run premise
        (BitVec.ofNat 64 (tailValues ⟨10, by omega⟩))
        ((writes.get x10 (by decide)).trans
          (segS15.reg x10 (BitVec.ofNat 64 (tailValues ⟨10, by omega⟩))
            (by simp [kvBase]))))
      (tailBase 10 (by omega)).1
      (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x128#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by simp [kvBase, RegsOutside, stepBookkeeping]) (by native_decide)
  obtain ⟨curS11, segS11, tailS11, savedS11, stored11, writes11, copiedS11, initializedS11,
    accessS11⟩ :=
    writeSuccessTailStoreStep args values tailValues (tailValues ⟨11, by omega⟩)
      0x14df4 0x130 0x130 (.Regidx 11#5) 0x23 0x38 0xb1 0x12 segS10 access loaded
      lower fits decodedEq tailBase savedS10 initializedS10 copiedS10 (by simp [kvBase])
      (fun premise writes => rX_x11_run premise
        (BitVec.ofNat 64 (tailValues ⟨11, by omega⟩))
        ((writes.get x11 (by decide)).trans
          (segS10.reg x11 (BitVec.ofNat 64 (tailValues ⟨11, by omega⟩))
            (by simp [kvBase]))))
      (tailBase 11 (by omega)).1
      (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x130#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by simp [kvBase, RegsOutside, stepBookkeeping]) (by native_decide)
  obtain ⟨curS12, segS12, tailS12, savedS12, stored12, writes12, copiedS12, initializedS12,
    accessS12⟩ :=
    writeSuccessTailStoreStep args values tailValues (tailValues ⟨12, by omega⟩)
      0x14df8 0x118 0x118 (.Regidx 12#5) 0x23 0x3c 0xc1 0x10 segS11 access loaded
      lower fits decodedEq tailBase savedS11 initializedS11 copiedS11 (by simp [kvBase])
      (fun premise writes => rX_x12_run premise
        (BitVec.ofNat 64 (tailValues ⟨12, by omega⟩))
        ((writes.get x12 (by decide)).trans
          (segS11.reg x12 (BitVec.ofNat 64 (tailValues ⟨12, by omega⟩))
            (by simp [kvBase]))))
      (tailBase 12 (by omega)).1
      (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x118#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by simp [kvBase, RegsOutside, stepBookkeeping]) (by native_decide)
  obtain ⟨curS13, segS13, tailS13, savedS13, stored13, writes13, copiedS13, initializedS13,
    accessS13⟩ :=
    writeSuccessTailStoreStep args values tailValues (tailValues ⟨13, by omega⟩)
      0x14dfc 0x120 0x120 (.Regidx 13#5) 0x23 0x30 0xd1 0x12 segS12 access loaded
      lower fits decodedEq tailBase savedS12 initializedS12 copiedS12 (by simp [kvBase])
      (fun premise writes => rX_x13_run premise
        (BitVec.ofNat 64 (tailValues ⟨13, by omega⟩))
        ((writes.get x13 (by decide)).trans
          (segS12.reg x13 (BitVec.ofNat 64 (tailValues ⟨13, by omega⟩))
            (by simp [kvBase]))))
      (tailBase 13 (by omega)).1
      (by omega) (by omega) (by omega) (by omega)
      (by change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x120#64 = _;
          rw [← BitVec.ofNat_add])
      (by
        intro storeState configured
        obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessStoreDecodeReads configured
        decode_run)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14d30, 0x14e00), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessInitialExitPc; native_decide)
      (by rfl) (by simp [kvBase, RegsOutside, stepBookkeeping]) (by native_decide)
  have local10L14 : WriteSuccessLocalTailPrefix args tailValues 10 curL14.mem := by
    rw [memL14]
    exact local10
  have local10S14 := writeSuccessLocalTailPrefix_after_store
    (storeIndex := 14) local10L14 writes14 (by omega) (by omega)
  have local10L15 : WriteSuccessLocalTailPrefix args tailValues 10 curL15.mem := by
    rw [memL15]
    exact local10S14
  have local10S15 := writeSuccessLocalTailPrefix_after_store
    (storeIndex := 15) local10L15 writes15 (by omega) (by omega)
  have local11 := writeSuccessLocalTailPrefix_succ (count := 10) (countBound := by decide)
    local10S15 writes10 (by simpa [writeSuccessLocalTailOffset] using stored10)
  have local12 := writeSuccessLocalTailPrefix_succ (count := 11) (countBound := by decide)
    local11 writes11 (by simpa [writeSuccessLocalTailOffset] using stored11)
  have local13 := writeSuccessLocalTailPrefix_succ (count := 12) (countBound := by decide)
    local12 writes12 (by simpa [writeSuccessLocalTailOffset] using stored12)
  have local14 := writeSuccessLocalTailPrefix_succ (count := 13) (countBound := by decide)
    local13 writes13 (by simpa [writeSuccessLocalTailOffset] using stored13)
  have stored14L15 : UIntRep 8 curL15.mem
      (args.stackPointer - 0x7d0 + 0x60) (tailValues ⟨14, by omega⟩) := by
    rw [memL15]
    exact stored14
  have stored14S15 := stored14L15.of_writesOnlyWithin writes15 (by
    intro index inBounds inside
    unfold byteRange at inside
    omega)
  have stored14S10 := stored14S15.of_writesOnlyWithin writes10 (by
    intro index inBounds inside; unfold byteRange at inside; omega)
  have stored14S11 := stored14S10.of_writesOnlyWithin writes11 (by
    intro index inBounds inside; unfold byteRange at inside; omega)
  have stored14S12 := stored14S11.of_writesOnlyWithin writes12 (by
    intro index inBounds inside; unfold byteRange at inside; omega)
  have stored14Final := stored14S12.of_writesOnlyWithin writes13 (by
    intro index inBounds inside; unfold byteRange at inside; omega)
  have stored15S10 := stored15.of_writesOnlyWithin writes10 (by
    intro index inBounds inside; unfold byteRange at inside; omega)
  have stored15S11 := stored15S10.of_writesOnlyWithin writes11 (by
    intro index inBounds inside; unfold byteRange at inside; omega)
  have stored15S12 := stored15S11.of_writesOnlyWithin writes12 (by
    intro index inBounds inside; unfold byteRange at inside; omega)
  have stored15Final := stored15S12.of_writesOnlyWithin writes13 (by
    intro index inBounds inside; unfold byteRange at inside; omega)
  have allLocal : InlineEncoderSavedWords curS13.mem
      (writeSuccessLocalTailWords args tailValues) := by
    intro word member
    simp [writeSuccessLocalTailWords] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact local14 0 (by decide) (by decide)
    · exact local14 1 (by decide) (by decide)
    · exact local14 2 (by decide) (by decide)
    · exact local14 3 (by decide) (by decide)
    · exact local14 4 (by decide) (by decide)
    · exact local14 5 (by decide) (by decide)
    · exact local14 6 (by decide) (by decide)
    · exact local14 7 (by decide) (by decide)
    · exact local14 8 (by decide) (by decide)
    · exact local14 9 (by decide) (by decide)
    · exact local14 10 (by decide) (by decide)
    · exact local14 11 (by decide) (by decide)
    · exact local14 12 (by decide) (by decide)
    · exact local14 13 (by decide) (by decide)
    · exact stored14Final
    · exact stored15Final
  exact ⟨values, bytes, tailValues, used, after, curS13, trace,
    by simpa [kvBase, kvFinal, Nat.add_assoc] using segS13, destinationRep, sourceRep, bytesSize,
    fieldBytes, tailS13, savedS13, ⟨tailValues, by simpa using allLocal⟩,
    ⟨tailValues, by simpa using allLocal, tailS13⟩,
    writeSuccessCodeOfSeg access loaded lower segS13, accessS13, copiedS13,
    initializedS13,
    WritesOnlyWithin.trans_same memoryFrame segS13.mem, ioFrame⟩

private theorem writeSuccessPrefixPc_in_execution {pc : BitVec 64}
    (inside : pcInRanges Elflings.writeSuccessRawLine131ExecutionPcRanges pc) :
    pcInRanges Elflings.writeSuccessExecutionPcRanges pc := by
  unfold pcInRanges at inside ⊢
  rcases inside with ⟨range, member, lower, upper⟩
  simp [Elflings.writeSuccessRawLine131ExecutionPcRanges] at member
  rcases member with rfl | rfl
  · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lower, upper⟩
  · exact ⟨(0x14d30, 0x15a14), by simp [Elflings.writeSuccessExecutionPcRanges], by omega,
      by omega⟩

/-- Consume the selected constant-prefix encoder after the exact initial writer transfer. -/
theorem writeSuccessPrefixHandoff (child : WriteSuccessPrefixInstanceContract)
    (fromStep : Nat) (args : WriteSuccessArgs) (state : EndpointState)
    (entry : WriteSuccessEntry args state) :
    ∃ values bytes, ∃ tailValues : Fin 16 → Nat, ∃ parentUsed childUsed after,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        fromStep (20 + parentUsed + 32 + childUsed) state after ∧
      EndpointPc after = some 0x14e14 ∧
      after.machine.regs.get? x2 =
        some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) ∧
      after.stdout = state.stdout ++ successPrefixBytes ∧
      after.stdin = state.stdin ∧ after.stdinCursor = state.stdinCursor ∧
      after.exitCode = state.exitCode ∧
      BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      BytesRep after.machine.mem args.decodedAddress bytes ∧
      bytes.size = 720 ∧
      RawPayloadFieldBytes bytes args.decoded.payload ∧
      (∀ index (inBounds : index < 16),
        UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
          (tailValues ⟨index, inBounds⟩)) ∧
      SavedWordReps after.machine (writeSuccessSavedWords args values) ∧
      WriteSuccessLocalTailReps args after ∧
      WriteSuccessLinkedTailReps args after ∧
      Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
      WriteSuccessMachineAccess args after.machine ∧
      InitializedByteWindow after.machine.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMemoryFrame args state.machine after.machine := by
  obtain ⟨values, bytes, tailValues, parentUsed, parentAfter, tailMachine, parentTrace,
    tailSeg, destinationRep, sourceRep, bytesSize, fieldBytes, tailReps, saved, localTail,
    linkedTail, loaded, access, copied, initialized,
    memoryFrame, ioFrame⟩ := writeSuccessTailSegmentHandoff fromStep args state entry
  let tailState : EndpointState := { parentAfter with machine := tailMachine }
  have tailTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges)
      (fromStep + (20 + parentUsed)) 32 parentAfter tailState := by
    have machineTrace := tailSeg.confined 0 tailMachine
      (.exitAt (fromStep + 20 + parentUsed + 32) tailMachine 0x14e00 tailSeg.atPc
        (Or.inr rfl))
    simpa [tailState, Nat.add_assoc] using liftWriteSuccessParentTrace parentAfter machineTrace
  obtain ⟨childBound, childImpl⟩ := child
  have childEntry : ConstantEncoderEntry Elflings.writeSuccessRawLine131Entry () tailState := by
    exact ⟨by simpa [tailState] using tailSeg.atPc, by simpa [tailState] using loaded⟩
  obtain ⟨childUsed, final, unit, positive, bounded, childTrace, childExitPc, _allowed,
    childExit⟩ := childImpl () (fromStep + 20 + parentUsed + 32) tailState childEntry
  have childTrace' := childTrace.weaken (fun _ inside => writeSuccessPrefixPc_in_execution inside)
  have fullTrace := (parentTrace.append tailTrace).append (by
    simpa [Nat.add_assoc] using childTrace')
  rcases childExit with ⟨finalPc, stdout, stdin, cursor, exitCode, childMem, childFrame⟩
  have tailMemory : WriteSuccessMemoryFrame args state.machine tailMachine := memoryFrame
  have stackLower : 0x880 ≤ args.stackPointer := entry.2.1
  have decodedEq : args.decodedAddress = args.stackPointer + 0x20 := entry.2.2.2.2.1
  have sourceTail : BytesRep tailMachine.mem args.decodedAddress bytes :=
    sourceRep.of_writesOnlyWithin tailSeg.mem (by
      intro index inBounds inside
      unfold writeSuccessFrameMemory byteRange at inside
      rw [decodedEq] at inside
      omega)
  have finalMemory : WriteSuccessMemoryFrame args state.machine final.machine := by
    apply WritesOnlyWithin.trans_same tailMemory
    simpa [tailState] using writesOnlyWithin_of_mem_eq childMem
  have pmaEq : final.machine.regs.get? pma_regions = tailMachine.regs.get? pma_regions := by
    simpa [tailState] using childFrame.1 pma_regions (by simp [abiCalleePreserved])
  have accessFinal : WriteSuccessMachineAccess args final.machine :=
    { configured := configuredAfterEndpointCall access.configured childFrame
      frameLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameLoad offset width inBounds)
      frameStore := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameStore offset width inBounds)
      frameNoMMIO := access.frameNoMMIO
      decodedLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.decodedLoad offset width inBounds)
      decodedNoMMIO := access.decodedNoMMIO
      outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq access.outputBufferStore
      outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq access.outputLengthStore
      writerRegionBeforeOutputContext := access.writerRegionBeforeOutputContext
      frameNotCode := access.frameNotCode }
  refine ⟨values, bytes, tailValues, parentUsed, childUsed, final, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, bytesSize, fieldBytes, ?_, ?_, ?_, ?_, childFrame.2.2.1, accessFinal, ?_, finalMemory⟩
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using fullTrace
  · simpa [EndpointPc, MachinePc] using finalPc
  · exact (childFrame.1 x2 (by simp [abiCalleePreserved])).trans
      (tailSeg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
  · calc
      final.stdout = tailState.stdout ++ successPrefixBytes := stdout
      _ = state.stdout ++ successPrefixBytes := by rw [ioFrame.2.2.1]
  · exact stdin.trans (by simpa [tailState] using ioFrame.1)
  · exact cursor.trans (by simpa [tailState] using ioFrame.2.1)
  · exact exitCode.trans (by simpa [tailState] using ioFrame.2.2.2)
  · simpa [tailState, childMem] using copied
  · simpa [tailState, childMem] using sourceTail
  · intro index inBounds
    simpa [tailState, childMem] using tailReps index inBounds
  · intro word member
    simpa [tailState, childMem] using saved word member
  · simpa [WriteSuccessLocalTailReps, tailState, childMem] using localTail
  · simpa [WriteSuccessLinkedTailReps, tailState, childMem] using linkedTail
  · simpa [tailState, childMem] using initialized

/-- Production `0x14e14: addi a0,sp,0x408`. -/
theorem writeSuccessSecondMemcpyDestinationStep (stepNo : Nat) (state : State)
    (stackPointer : Nat) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e14)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e14 retired x10
        (BitVec.ofNat 64 (stackPointer + 0x408))) false := by
  apply writeSuccessAddiX10FromSpStep stepNo 0x14e14 0x408 0x408
    0x13 0x05 0x81 0x40 state stackPointer configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 stackPointer + sign_extend (BitVec.ofNat 12 0x408) = _
    rw [show sign_extend (m := 64) (0x408#12) = 0x408#64 by native_decide]
    rw [← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x14e18: addi a1,sp,0x138`. -/
theorem writeSuccessSecondMemcpySourceStep (stepNo : Nat) (state : State)
    (stackPointer : Nat) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e18)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e18 retired x11
        (BitVec.ofNat 64 (stackPointer + 0x138))) false := by
  apply writeSuccessAddiX11FromSpStep stepNo 0x14e18 0x138 0x138
    0x93 0x05 0x81 0x13 state stackPointer configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 stackPointer + sign_extend (BitVec.ofNat 12 0x138) = _
    rw [show sign_extend (m := 64) (0x138#12) = 0x138#64 by native_decide]
    rw [← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x14e1c: li a2,0x250`. -/
theorem writeSuccessSecondMemcpyLengthStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e1c)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e1c retired x12 0x250) false := by
  apply writeSuccessAddiX12FromZeroStep stepNo 0x14e1c 0x250 0x250
    0x13 0x06 0x00 0x25 state configured atPc loaded
  · native_decide
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x14e20: auipc ra,-5`. -/
theorem writeSuccessSecondMemcpyCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e20)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e20 retired x1 0xfe20) false := by
  apply configuredAuipcStep stepNo state 0x14e20 0xffffb 0x97 0xb0 0xff 0xff
    configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x14e24: jalr ra,0x3b4(ra)`, entering `memcpy`. -/
theorem writeSuccessSecondMemcpyCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e24)
    (baseRead : state.regs.get? x1 = some 0xfe20)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14e24 0x101d4 x1 0x14e28)
        0x101d4 retired) false := by
  apply configuredJalrCallStep stepNo state 0x14e24 0xfe20 0x3b4 0x101d4 0x14e28
    0xe7 0x80 0x40 0x3b configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x14e28: addi a0,sp,0x4a0`. -/
theorem writeSuccessParentHashSourceStep (stepNo : Nat) (state : State)
    (stackPointer : Nat) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e28)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e28 retired x10
        (BitVec.ofNat 64 (stackPointer + 0x4a0))) false := by
  apply writeSuccessAddiX10FromSpStep stepNo 0x14e28 0x4a0 0x4a0
    0x13 0x05 0x01 0x4a state stackPointer configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 stackPointer + sign_extend (BitVec.ofNat 12 0x4a0) = _
    rw [show sign_extend (m := 64) (0x4a0#12) = 0x4a0#64 by native_decide]
    rw [← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x14ed4: addi a0,sp,0x634`, selecting the copied block hash. -/
private theorem writeSuccessBlockHashSourceStep (stepNo : Nat) (state : State)
    (stackPointer : Nat) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14ed4)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14ed4 retired x10
        (BitVec.ofNat 64 (stackPointer + 0x634))) false := by
  apply writeSuccessAddiX10FromSpStep stepNo 0x14ed4 0x634 0x634
    0x13 0x05 0x41 0x63 state stackPointer configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 stackPointer + sign_extend (BitVec.ofNat 12 0x634) = _
    rw [show sign_extend (m := 64) (0x634#12) = 0x634#64 by native_decide]
    rw [← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

private theorem writeSuccessPayloadFieldSourceStep (stepNo pc offset : Nat)
    (imm : BitVec 12) (byte0 byte1 byte2 byte3 : UInt8) (state : State)
    (stackPointer : Nat) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (resultEq : iTypeResult .ADDI imm (BitVec.ofNat 64 stackPointer) =
      BitVec.ofNat 64 (stackPointer + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (imm, .Regidx 2#5, .Regidx 10#5, .ADDI)))
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by rfl)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x10
        (BitVec.ofNat 64 (stackPointer + offset))) false := by
  apply writeSuccessAddiX10FromSpStep stepNo pc offset imm byte0 byte1 byte2 byte3
    state stackPointer configured atPc stack loaded resultEq decode pcFits base read0 read1 read2 read3

private theorem writeSuccessFeeRecipientSourceStep (stepNo : Nat) (state : State)
    (stackPointer : Nat) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e38)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e38 retired x10
        (BitVec.ofNat 64 (stackPointer + 0x4c0))) false := by
  apply writeSuccessPayloadFieldSourceStep stepNo 0x14e38 0x4c0 0x4c0
    0x13 0x05 0x01 0x4c state stackPointer configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 stackPointer + sign_extend (0x4c0#12) = _
    rw [show sign_extend (m := 64) (0x4c0#12) = 0x4c0#64 by native_decide,
      ← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

private theorem writeSuccessStateRootSourceStep (stepNo : Nat) (state : State)
    (stackPointer : Nat) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e48)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e48 retired x10
        (BitVec.ofNat 64 (stackPointer + 0x4d4))) false := by
  apply writeSuccessPayloadFieldSourceStep stepNo 0x14e48 0x4d4 0x4d4
    0x13 0x05 0x41 0x4d state stackPointer configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 stackPointer + sign_extend (0x4d4#12) = _
    rw [show sign_extend (m := 64) (0x4d4#12) = 0x4d4#64 by native_decide,
      ← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

private theorem writeSuccessReceiptsRootSourceStep (stepNo : Nat) (state : State)
    (stackPointer : Nat) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e58)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e58 retired x10
        (BitVec.ofNat 64 (stackPointer + 0x4f4))) false := by
  apply writeSuccessPayloadFieldSourceStep stepNo 0x14e58 0x4f4 0x4f4
    0x13 0x05 0x41 0x4f state stackPointer configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 stackPointer + sign_extend (0x4f4#12) = _
    rw [show sign_extend (m := 64) (0x4f4#12) = 0x4f4#64 by native_decide,
      ← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

private theorem writeSuccessLogsBloomSourceStep (stepNo : Nat) (state : State)
    (stackPointer : Nat) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e68)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e68 retired x10
        (BitVec.ofNat 64 (stackPointer + 0x514))) false := by
  apply writeSuccessPayloadFieldSourceStep stepNo 0x14e68 0x514 0x514
    0x13 0x05 0x41 0x51 state stackPointer configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 stackPointer + sign_extend (0x514#12) = _
    rw [show sign_extend (m := 64) (0x514#12) = 0x514#64 by native_decide,
      ← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

private theorem writeSuccessPrevRandaoSourceStep (stepNo : Nat) (state : State)
    (stackPointer : Nat) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e78)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e78 retired x10
        (BitVec.ofNat 64 (stackPointer + 0x614))) false := by
  apply writeSuccessPayloadFieldSourceStep stepNo 0x14e78 0x614 0x614
    0x13 0x05 0x41 0x61 state stackPointer configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 stackPointer + sign_extend (0x614#12) = _
    rw [show sign_extend (m := 64) (0x614#12) = 0x614#64 by native_decide,
      ← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

set_option genInjectivity false in
/-- State carried from the second writer `memcpy` to the parent-hash encoder. -/
structure WriteSuccessSecondMemcpyHandoff (fromStep parentUsed prefixUsed memcpyUsed : Nat)
    (args : WriteSuccessArgs) (state after : EndpointState) (values : DecodeCalleeSavedValues)
    (bytes : Array UInt8) (tailValues : Fin 16 → Nat) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep
    (20 + parentUsed + 32 + prefixUsed + 5 + memcpyUsed + 1) state after
  atPc : EndpointPc after = some 0x14e2c
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  source : after.machine.regs.get? x10 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x4a0))
  stdout : after.stdout = state.stdout ++ successPrefixBytes
  stdin : after.stdin = state.stdin
  cursor : after.stdinCursor = state.stdinCursor
  exitCode : after.exitCode = state.exitCode
  bytesSize : bytes.size = 0x250
  destinationRep : BytesRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) bytes
  parentRootRep : BytesRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x3e8) args.decoded.parentBeaconBlockRoot
  versionedHashesRelocation : ByteWindowRelocation after.machine.mem after.machine.mem
    (args.decodedAddress + 592) (args.stackPointer - 0x7d0 + 0x388) 16
  sourceRep : BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes
  fullCopy : ∃ fullBytes : Array UInt8, fullBytes.size = 720 ∧
    BytesRep after.machine.mem args.decodedAddress fullBytes ∧
    BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) fullBytes
  tailReps : ∀ index (inBounds : index < 16),
    UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
      (tailValues ⟨index, inBounds⟩)
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  slotWord : ∃ value, UIntRep 8 after.machine.mem
    (args.stackPointer - 0x7d0 + 0x480) value
  slotTagWord : ∃ value, UIntRep 8 after.machine.mem
    (args.stackPointer - 0x7d0 + 0x488) value
  localTailReps : WriteSuccessLocalTailReps args after
  linkedTailReps : WriteSuccessLinkedTailReps args after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memoryFrame : WriteSuccessMemoryFrame args state.machine after.machine
  fieldBytes : RawPayloadFieldBytes bytes args.decoded.payload
  fieldReps : RawPayloadFieldReps after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  payloadRep : ExecutionPayloadRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  decodedBytesRep : BytesRep after.machine.mem args.decodedAddress bytes
  stable : StatelessInputRepStableOutside (writeSuccessMemoryRegion args)
    after.machine.mem args.decodedAddress args.decoded

/-- Compose the second writer `memcpy` and enter the parent-hash encoder. -/
theorem writeSuccessSecondMemcpyHandoff (child : WriteSuccessPrefixInstanceContract)
    (fromStep : Nat) (args : WriteSuccessArgs) (state : EndpointState)
    (entry : WriteSuccessEntry args state) :
    ∃ values bytes, ∃ tailValues : Fin 16 → Nat, ∃ parentUsed prefixUsed memcpyUsed after,
      WriteSuccessSecondMemcpyHandoff fromStep parentUsed prefixUsed memcpyUsed args state after
        values bytes tailValues := by
  obtain ⟨values, fullBytes, tailValues, parentUsed, prefixUsed, prefixState, prefixTrace,
    prefixPc, prefixStack, prefixStdout, prefixStdin, prefixCursor, prefixExitCode, fullRep,
    decodedFullRep, fullSize, fullFieldBytes, tailReps, saved, localTail, linkedTail, loaded, access,
    initialized, memoryFrame⟩ :=
    writeSuccessPrefixHandoff child fromStep args state entry
  have stackLower : 0x880 ≤ args.stackPointer := entry.2.1
  have stackFits : args.stackPointer < 2 ^ 64 := entry.2.2.2.1
  have decodedEq : args.decodedAddress = args.stackPointer + 0x20 := entry.2.2.2.2.1
  let bytes := fullBytes.extract 0 0x250
  have bytesSize : bytes.size = 0x250 := by
    dsimp [bytes]
    rw [Array.size_extract, fullSize]
    native_decide
  have sourceRep : BytesRep prefixState.machine.mem
      (args.stackPointer - 0x7d0 + 0x138) bytes := by
    dsimp [bytes]
    exact fullRep.extractPrefix (by rw [fullSize]; omega)
  have fieldBytes : RawPayloadFieldBytes bytes args.decoded.payload := by
    dsimp [bytes]
    exact fullFieldBytes.extractPrefix 0x250 (by omega) (by rw [fullSize]; omega)
  let startStep := fromStep + (20 + parentUsed + 32 + prefixUsed)
  have prefixMachinePc : prefixState.machine.regs.get? PC = some 0x14e14 := by
    simpa [EndpointPc, MachinePc] using prefixPc
  have seg0 : Seg writeSuccessParentPc writeSuccessSecondMemcpyExitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [] startStep 0 prefixState.machine prefixState.machine 0x14e14 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := prefixMachinePc
    regs := RegsHold.nil _ }
  have seg0 := seg0.know x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) prefixStack
  obtain ⟨retired0, run0⟩ := writeSuccessSecondMemcpyDestinationStep _ prefixState.machine
    (args.stackPointer - 0x7d0) access.configured prefixMachinePc prefixStack loaded
  have seg1 := seg0.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e14, 0x14e2c), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessSecondMemcpyExitPc; native_decide) x10
    (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x408)) 0x14e18 retired0 run0
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have configured1 := writeSuccessConfiguredOfSeg access seg1
  obtain ⟨retired1, run1⟩ := writeSuccessSecondMemcpySourceStep _ _
    (args.stackPointer - 0x7d0) configured1 seg1.atPc
    (seg1.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    (by simpa [seg1.memEq (by simp)] using loaded)
  have seg2 := seg1.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e14, 0x14e2c), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessSecondMemcpyExitPc; native_decide) x11
    (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x138)) 0x14e1c retired1 run1
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have configured2 := writeSuccessConfiguredOfSeg access seg2
  obtain ⟨retired2, run2⟩ := writeSuccessSecondMemcpyLengthStep _ _ configured2 seg2.atPc
    (by simpa [seg2.memEq (by simp)] using loaded)
  have seg3 := seg2.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e14, 0x14e2c), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessSecondMemcpyExitPc; native_decide) x12 0x250 0x14e20 retired2 run2
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have seg3 := seg3.forget (kv' := [
      ⟨x12, (0x250 : BitVec 64)⟩,
      ⟨x11, BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x138)⟩,
      ⟨x10, BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x408)⟩,
      ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]) (by simp)
  have configured3 := writeSuccessConfiguredOfSeg access seg3
  obtain ⟨setupMachine, seg4⟩ := seg3.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e14, 0x14e2c), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessSecondMemcpyExitPc; native_decide) x1 0xfe20 0x14e24
    (writeSuccessSecondMemcpyCallBaseStep _ _ configured3 seg3.atPc
      (by simpa [seg3.memEq (by simp)] using loaded))
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have setupLoaded : Artifacts.programImage.fileBytesLoadedFaithfully setupMachine.mem := by
    simpa [seg4.memEq (by simp)] using loaded
  have configured4 := writeSuccessConfiguredOfSeg access seg4
  obtain ⟨retired4, callRun⟩ := writeSuccessSecondMemcpyCallStep _ setupMachine configured4 seg4.atPc
    (seg4.reg x1 0xfe20 (by simp)) setupLoaded
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement setupMachine) 0x14e24 0x101d4 x1 0x14e28)
    0x101d4 retired4
  let callState : EndpointState := { prefixState with machine := callMachine }
  have callAtPc : callMachine.regs.get? PC = some 0x101d4 := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callWrites := callRetirement_writes setupMachine 0x14e24 0x101d4 retired4 x1 0x14e28
  have callConfigured : ConfiguredMachinePre EndpointMachinePc callMachine :=
    configuredAfterWriteSuccessCall 0x14e24 0x101d4 0x14e28 retired4 configured4
  have setupMemEq : setupMachine.mem = prefixState.machine.mem := seg4.memEq (by simp)
  have callMemEq : callMachine.mem = setupMachine.mem := by
    change
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement setupMachine) 0x14e24 0x101d4 x1 0x14e28)
        0x101d4 retired4).mem = setupMachine.mem
    rw [tryStepControlFlowAfterRetired_mem]
    change
      (controlFlowJumpState (tryStepControlFlowAfterIncrement setupMachine) 0x14e24 0x101d4).mem =
        setupMachine.mem
    rw [controlFlowJumpState_mem]
    rfl
  have callPrefixMemEq : callMachine.mem = prefixState.machine.mem :=
    callMemEq.trans setupMemEq
  have sourceAtCall : BytesRep callMachine.mem
      (args.stackPointer - 0x7d0 + 0x138) bytes := by
    rw [callMemEq, setupMemEq]
    exact sourceRep
  let memcpyArgs : MemcpyArgs :=
    { returnAddress := 0x14e28
      destination := args.stackPointer - 0x7d0 + 0x408
      source := args.stackPointer - 0x7d0 + 0x138
      bytes }
  have wholeWrites : WritesOnlyRegs writeSuccessParentWrites prefixState.machine callMachine :=
    seg4.writes.trans_same (callWrites.mono (by
      intro register written
      rcases written with bookkeeping | rfl
      · exact Or.inl bookkeeping
      · exact Or.inr (Or.inl rfl)))
  have pmaEq := wholeWrites.get pma_regions (by
    simp [writeSuccessParentWrites, stepBookkeeping])
  have memcpyEntry : MemcpyEntry memcpyArgs callState := by
    refine ⟨(show 0x14e28 ∈ Elflings.memcpyExitPcs by native_decide), (by
      rw [bytesSize]
      native_decide), ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, sourceAtCall, ?_, ?_⟩
    · dsimp [memcpyArgs]
      rw [bytesSize]
      omega
    · dsimp [memcpyArgs]
      rw [bytesSize]
      omega
    · right
      dsimp [memcpyArgs]
      rw [bytesSize]
      omega
    · simpa [callState, EndpointPc, MachinePc] using callAtPc
    · simp [memcpyArgs, callState, callMachine, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, callLinkState, Std.ExtDHashMap.get?_insert]
    · exact (callWrites.get x10 (by decide)).trans
        (seg4.reg x10 (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x408)) (by simp))
    · exact (callWrites.get x11 (by decide)).trans
        (seg4.reg x11 (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x138)) (by simp))
    · rw [bytesSize]
      exact (callWrites.get x12 (by decide)).trans (seg4.reg x12 0x250 (by simp))
    · simpa [callState, callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]
        using setupLoaded
    · refine
        { configured := callConfigured
          sourcePma := ?_
          destinationPma := ?_
          sourceNotMMIO := ?_
          destinationNotMMIO := ?_
          destinationNotCode := ?_ }
      · intro index indexBound
        rw [bytesSize] at indexBound
        have original := access.frameLoad (0x138 + index) 1 (by omega)
        have moved := dataPmaAllows_of_pma_regions_eq pmaEq original
        simpa [memcpyArgs, Nat.add_assoc] using moved
      · intro index indexBound
        rw [bytesSize] at indexBound
        have original := access.frameStore (0x408 + index) 1 (by omega)
        have moved := dataPmaAllows_of_pma_regions_eq pmaEq original
        simpa [memcpyArgs, Nat.add_assoc] using moved
      · intro index indexBound
        rw [bytesSize] at indexBound
        simpa [memcpyArgs, LoadMMIOAddressExcluded, StoreMMIOAddressExcluded, Nat.add_assoc]
          using access.frameNoMMIO (0x138 + index) 1 (by omega)
      · intro index indexBound
        rw [bytesSize] at indexBound
        simpa [memcpyArgs, Nat.add_assoc] using access.frameNoMMIO (0x408 + index) 1 (by omega)
      · intro index indexBound
        rw [bytesSize] at indexBound
        dsimp [memcpyArgs]
        exact access.frameNotCode _ (by omega) (by omega)
  obtain ⟨memcpyBound, memcpyImpl⟩ := memcpyInstanceContract
  obtain ⟨memcpyUsed, childAfter, unit, positive, bounded, childTrace, childExitPc, _allowed,
    childExit⟩ := memcpyImpl memcpyArgs (startStep + 5) callState memcpyEntry
  have callPrefix : ConfinedPrefix writeSuccessParentPc writeSuccessSecondMemcpyExitPc
      (fun _ _ _ _ _ => False) (startStep + 4) 1 setupMachine callMachine :=
    ConfinedPrefix.ownStep seg4.atPc
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14e14, 0x14e2c), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessSecondMemcpyExitPc; native_decide) callRun
  have callEnd : ScopedTrace writeSuccessParentPc writeSuccessSecondMemcpyExitPc
      (fun _ _ _ _ _ => False) (startStep + 5) 0 callMachine callMachine :=
    .exitAt _ _ 0x101d4 callAtPc (Or.inl rfl)
  have setupMachineTrace := seg4.confined.trans callPrefix 0 callMachine callEnd
  have setupTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) startStep 5 prefixState callState := by
    simpa [callState] using liftWriteSuccessParentTrace prefixState setupMachineTrace
  have childTrace' := childTrace.weaken (fun _ inside => memcpyPc_in_writeSuccess inside)
  rcases childExit with ⟨childPc, stdin, cursor, stdout, exitCode, destinationRep,
    sourceRepAfter, codeAfter, childMem, childFrame⟩
  have childStack : childAfter.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) := by
    exact (childFrame.1 x2 (by simp [abiCalleePreserved])).trans
      ((callWrites.get x2 (by decide)).trans
        (seg4.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)))
  have childConfigured := configuredAfterEndpointCall callConfigured childFrame
  have finalSeg0 : Seg writeSuccessParentPc writeSuccessSecondMemcpyExitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [] (startStep + 5 + memcpyUsed) 0 childAfter.machine childAfter.machine 0x14e28 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := childConfigured.retiredCounter
    atPc := by simpa [EndpointPc, MachinePc, memcpyArgs] using childPc
    regs := RegsHold.nil _ }
  have finalSeg0 := finalSeg0.know x2
    (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) childStack
  obtain ⟨finalMachine, finalSeg⟩ := finalSeg0.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e14, 0x14e2c), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessSecondMemcpyExitPc; native_decide) x10
    (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x4a0)) 0x14e2c
    (writeSuccessParentHashSourceStep _ childAfter.machine
      (args.stackPointer - 0x7d0) childConfigured finalSeg0.atPc childStack codeAfter)
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  let finalState : EndpointState := { childAfter with machine := finalMachine }
  have finalTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) (startStep + 5 + memcpyUsed) 1
      childAfter finalState := by
    have machineTrace := finalSeg.confined 0 finalMachine
      (.exitAt _ _ 0x14e2c finalSeg.atPc (Or.inr rfl))
    simpa [finalState] using liftWriteSuccessParentTrace childAfter machineTrace
  have prefixSetup := prefixTrace.append (by
    simpa [startStep, Nat.add_assoc] using setupTrace)
  have throughChild := prefixSetup.append (by
    simpa [startStep, Nat.add_assoc] using childTrace')
  have fullTrace := throughChild.append (by
    simpa [startStep, Nat.add_assoc] using finalTrace)
  have childPmaEq : childAfter.machine.regs.get? pma_regions =
      prefixState.machine.regs.get? pma_regions :=
    (childFrame.1 pma_regions (by simp [abiCalleePreserved])).trans pmaEq
  have accessAfter : WriteSuccessMachineAccess args childAfter.machine :=
    { configured := childConfigured
      frameLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq childPmaEq (access.frameLoad offset width inBounds)
      frameStore := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq childPmaEq (access.frameStore offset width inBounds)
      frameNoMMIO := access.frameNoMMIO
      decodedLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq childPmaEq (access.decodedLoad offset width inBounds)
      decodedNoMMIO := access.decodedNoMMIO
      outputBufferStore := dataPmaAllows_of_pma_regions_eq childPmaEq access.outputBufferStore
      outputLengthStore := dataPmaAllows_of_pma_regions_eq childPmaEq access.outputLengthStore
      writerRegionBeforeOutputContext := access.writerRegionBeforeOutputContext
      frameNotCode := access.frameNotCode }
  have accessFinal := writeSuccessAccessOfSeg accessAfter finalSeg
  have tailAfter : ∀ index (inBounds : index < 16),
      UIntRep 8 finalMachine.mem (args.decodedAddress + 720 + index * 8)
        (tailValues ⟨index, inBounds⟩) := by
    intro index inBounds
    have atCall := (tailReps index inBounds).of_mem_eq callPrefixMemEq
    have atChild := atCall.of_writesOnlyWithin
      (owned := byteRange memcpyArgs.destination memcpyArgs.bytes.size) childMem (by
      intro byte byteBound inside
      unfold byteRange at inside
      simp [memcpyArgs, bytesSize] at inside
      rw [decodedEq] at inside
      omega)
    simpa [finalSeg.memEq (by simp)] using atChild
  have savedAfter : SavedWordReps finalMachine (writeSuccessSavedWords args values) := by
    intro word member
    have atCall := (saved word member).of_mem_eq callPrefixMemEq
    have atChild := atCall.of_writesOnlyWithin
      (owned := byteRange memcpyArgs.destination memcpyArgs.bytes.size) childMem (by
      intro index indexBound inside
      unfold byteRange at inside
      simp [memcpyArgs, bytesSize] at inside
      have wordLower : args.stackPointer - 0x7d0 + 0x768 ≤ word.1 := by
        simp [writeSuccessSavedWords] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> omega
      omega)
    simpa [finalSeg.memEq (by simp)] using atChild
  obtain ⟨localValues, localWords⟩ := localTail
  have localTailAfter : WriteSuccessLocalTailReps args { childAfter with machine := finalMachine } := by
    refine ⟨localValues, ?_⟩
    intro word member
    have atCall := (localWords word member).of_mem_eq callPrefixMemEq
    have atChild := atCall.of_writesOnlyWithin
      (owned := byteRange memcpyArgs.destination memcpyArgs.bytes.size) childMem (by
      intro index indexBound inside
      unfold byteRange at inside
      simp [memcpyArgs, bytesSize] at inside
      have wordUpper : word.1 + 8 ≤ args.stackPointer - 0x7d0 + 0x138 := by
        simp [writeSuccessLocalTailWords] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      omega)
    simpa [finalSeg.memEq (by simp)] using atChild
  obtain ⟨linkedValues, linkedLocal, linkedSource⟩ := linkedTail
  have linkedTailAfter :
      WriteSuccessLinkedTailReps args { childAfter with machine := finalMachine } := by
    refine ⟨linkedValues, ?_, ?_⟩
    · intro word member
      have atCall := (linkedLocal word member).of_mem_eq callPrefixMemEq
      have atChild := atCall.of_writesOnlyWithin
        (owned := byteRange memcpyArgs.destination memcpyArgs.bytes.size) childMem (by
        intro index indexBound inside
        unfold byteRange at inside
        simp [memcpyArgs, bytesSize] at inside
        have wordUpper : word.1 + 8 ≤ args.stackPointer - 0x7d0 + 0x138 := by
          simp [writeSuccessLocalTailWords] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        omega)
      simpa [finalSeg.memEq (by simp)] using atChild
    · intro index bound
      have atCall := (linkedSource index bound).of_mem_eq callPrefixMemEq
      have atChild := atCall.of_writesOnlyWithin
        (owned := byteRange memcpyArgs.destination memcpyArgs.bytes.size) childMem (by
        intro byte byteBound inside
        unfold byteRange at inside
        simp [memcpyArgs, bytesSize] at inside
        rw [decodedEq] at inside
        omega)
      simpa [finalSeg.memEq (by simp)] using atChild
  have setupMemory : WriteSuccessMemoryFrame args prefixState.machine callMachine := by
    intro address outside
    rw [callMemEq, setupMemEq]
  have childMemory : WriteSuccessMemoryFrame args callMachine childAfter.machine :=
    childMem.mono (by
      intro address inside
      unfold byteRange at inside
      unfold writeSuccessFrameMemory byteRange
      simp [memcpyArgs, bytesSize] at inside
      omega)
  have finalRegisterMemory : WriteSuccessMemoryFrame args childAfter.machine finalMachine :=
    finalSeg.mem.mono (by intro address impossible; exact impossible.elim)
  have finalMemory : WriteSuccessMemoryFrame args state.machine finalMachine := by
    exact WritesOnlyWithin.trans_same memoryFrame
      (WritesOnlyWithin.trans_same setupMemory
        (WritesOnlyWithin.trans_same childMemory finalRegisterMemory))
  rcases entry with ⟨_, _, _, _, _, _, _, _, _, decodedRep, _, _, _, _, _, stable⟩
  have decodedFinal : StatelessInputRep finalMachine.mem args.decodedAddress args.decoded :=
    stable.of_writesOnlyWithin (finalMemory.mono (fun _ inside => Or.inl inside))
  have decodedBytesAtCall : BytesRep callMachine.mem args.decodedAddress fullBytes :=
    decodedFullRep.of_mem_eq callPrefixMemEq
  have decodedBytesAtChild : BytesRep childAfter.machine.mem args.decodedAddress fullBytes :=
    decodedBytesAtCall.of_writesOnlyWithin childMem (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [memcpyArgs, bytesSize] at inside
      rw [decodedEq] at inside
      omega)
  have fullDecodedFinal : BytesRep finalMachine.mem args.decodedAddress fullBytes := by
    simpa [finalSeg.memEq (by simp)] using decodedBytesAtChild
  have fullCopiedAtCall : BytesRep callMachine.mem
      (args.stackPointer - 0x7d0 + 0x138) fullBytes := fullRep.of_mem_eq callPrefixMemEq
  have fullCopiedAtChild : BytesRep childAfter.machine.mem
      (args.stackPointer - 0x7d0 + 0x138) fullBytes :=
    fullCopiedAtCall.of_writesOnlyWithin childMem (by
      intro index inBounds inside
      unfold byteRange at inside
      dsimp [memcpyArgs] at inside
      rw [fullSize] at inBounds
      omega)
  have fullCopiedFinal : BytesRep finalMachine.mem
      (args.stackPointer - 0x7d0 + 0x138) fullBytes := by
    simpa [finalSeg.memEq (by simp)] using fullCopiedAtChild
  have decodedBytesFinal : BytesRep finalMachine.mem args.decodedAddress bytes := by
    dsimp [bytes]
    exact fullDecodedFinal.extractPrefix (by rw [fullSize]; omega)
  have rootBytesEq : fullBytes.extract 688 720 = args.decoded.parentBeaconBlockRoot := by
    have sourceRoot := fullDecodedFinal.extractRange 688 32 (by rw [fullSize]; omega)
    have semanticRoot := decodedFinal.2.2.2.2.2.1
    exact BytesRep.unique sourceRoot semanticRoot (by
      rw [Array.size_extract]
      have sizeEq := decodedFinal.2.2.2.2.1
      omega)
  have rootAtPrefix : BytesRep prefixState.machine.mem
      (args.stackPointer - 0x7d0 + 0x3e8) args.decoded.parentBeaconBlockRoot := by
    have extracted := fullRep.extractRange 688 32 (by rw [fullSize]; omega)
    simpa [rootBytesEq, Nat.add_assoc] using extracted
  have rootAtCall := rootAtPrefix.of_mem_eq callPrefixMemEq
  have rootAtChild := rootAtCall.of_writesOnlyWithin childMem (by
    intro index inBounds inside
    unfold byteRange at inside
    dsimp [memcpyArgs] at inside
    rw [← rootBytesEq, Array.size_extract] at inBounds
    omega)
  have rootFinal : BytesRep finalMachine.mem
      (args.stackPointer - 0x7d0 + 0x3e8) args.decoded.parentBeaconBlockRoot := by
    simpa [finalSeg.memEq (by simp)] using rootAtChild
  have versionedRelocation : ByteWindowRelocation finalMachine.mem finalMachine.mem
      (args.decodedAddress + 592) (args.stackPointer - 0x7d0 + 0x388) 16 := by
    have relocation := ByteWindowRelocation.of_same_bytes fullDecodedFinal fullCopiedFinal
    simpa [Nat.add_assoc] using relocation.atOffset 592 16 (by rw [fullSize]; omega)
  have destinationFinal : BytesRep finalMachine.mem
      (args.stackPointer - 0x7d0 + 0x408) bytes := by
    simpa [finalSeg.memEq (by simp)] using destinationRep
  have payloadFinal : ExecutionPayloadRep finalMachine.mem
      (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload := by
    apply decodedFinal.2.1.rebase (by omega)
    have sameBytes := ByteWindowRelocation.of_same_bytes decodedBytesFinal destinationFinal
    simpa [bytesSize] using sameBytes
  refine ⟨values, bytes, tailValues, parentUsed, prefixUsed, memcpyUsed, finalState, {
    trace := ?_
    atPc := ?_
    stack := ?_
    source := ?_
    stdout := ?_
    stdin := stdin.trans (by simpa [callState, finalState] using prefixStdin)
    cursor := cursor.trans (by simpa [callState, finalState] using prefixCursor)
    exitCode := exitCode.trans (by simpa [callState, finalState] using prefixExitCode)
    bytesSize := bytesSize
    destinationRep := by
      simpa [finalState, finalSeg.memEq (by simp)] using destinationRep
    sourceRep := by simpa [finalState, finalSeg.memEq (by simp)] using sourceRepAfter
    fullCopy := ⟨fullBytes, fullSize, by simpa [finalState] using fullDecodedFinal,
      by simpa [finalState] using fullCopiedFinal⟩
    parentRootRep := by simpa [finalState] using rootFinal
    versionedHashesRelocation := by simpa [finalState] using versionedRelocation
    tailReps := tailAfter
    saved := savedAfter
    slotWord := by
      have rep := destinationFinal.extractRange 120 8 (by simp [bytesSize])
      have size : (bytes.extract 120 128).size = 8 := by simp [bytesSize]
      simpa [finalState, Nat.add_assoc] using BytesRep.existsUIntRepEight rep size
    slotTagWord := by
      have rep := destinationFinal.extractRange 128 8 (by simp [bytesSize])
      have size : (bytes.extract 128 136).size = 8 := by simp [bytesSize]
      simpa [finalState, Nat.add_assoc] using BytesRep.existsUIntRepEight rep size
    localTailReps := by simpa [finalState] using localTailAfter
    linkedTailReps := by simpa [finalState] using linkedTailAfter
    loaded := by simpa [finalState, finalSeg.memEq (by simp)] using codeAfter
    access := accessFinal
    memoryFrame := finalMemory
    fieldBytes := fieldBytes
    fieldReps := (by
      apply fieldBytes.fieldReps
      · simpa [finalState, finalSeg.memEq (by simp)] using destinationRep
      · omega)
    payloadRep := by simpa [finalState] using payloadFinal
    decodedBytesRep := by simpa [finalState] using decodedBytesFinal
    stable := by simpa [finalState] using
      stable.afterWrites (finalMemory.mono (fun _ inside => Or.inl inside)) }⟩
  · simpa [startStep, finalState, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using fullTrace
  · simpa [finalState, EndpointPc, MachinePc] using finalSeg.atPc
  · simpa [finalState] using
      finalSeg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
  · simpa [finalState] using
      finalSeg.reg x10 (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x4a0)) (by simp)
  · calc
      finalState.stdout = childAfter.stdout := rfl
      _ = callState.stdout := stdout
      _ = prefixState.stdout := rfl
      _ = state.stdout ++ successPrefixBytes := prefixStdout

private theorem writeSuccessRawEncoderHandoff
    {entry success : Nat} {executionPcs : List Elflings.PcRange} {exitPcs : List Nat}
    (child : RawEncoderInstanceContract entry executionPcs exitPcs success)
    (insideWriter : ∀ {pc}, pcInRanges executionPcs pc →
      pcInRanges Elflings.writeSuccessExecutionPcRanges pc)
    (fromStep : Nat) (args : RawEncoderArgs) (before : EndpointState)
    (childEntry : RawEncoderEntry entry args before) :
    ∃ used after,
      used ≤ RawEncoderInstanceContract.stepBound child args.bytes.size ∧
      ConfinedTrace EndpointStep EndpointPc
        (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep used before after ∧
      RawEncoderExit success args () before after := by
  obtain ⟨used, after, unit, positive, bounded, trace, exitPc, allowed, exit⟩ :=
    RawEncoderInstanceContract.implements child args fromStep before childEntry
  exact ⟨used, after, bounded, trace.weaken (fun _ pc => insideWriter pc), exit⟩

private theorem writeSuccessInlineEncoderHandoff
    {Value : Type} {entry success : Nat} {executionPcs : List Elflings.PcRange}
    {exitPcs : List Nat} {encode : Value → Array UInt8}
    {bindValue : EndpointState → Value → Prop}
    (child : InlineEncoderInstanceContract entry executionPcs exitPcs success encode bindValue)
    (insideWriter : ∀ {pc}, pcInRanges executionPcs pc →
      pcInRanges Elflings.writeSuccessExecutionPcRanges pc)
    (fromStep : Nat) (args : InlineEncoderArgs Value) (before : EndpointState)
    (childEntry : InlineEncoderEntry entry bindValue args before) :
    ∃ used after,
      used ≤ InlineEncoderInstanceContract.stepBound child args.inputSize ∧
      ConfinedTrace EndpointStep EndpointPc
        (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep used before after ∧
      InlineEncoderExit success encode bindValue args () before after := by
  obtain ⟨used, after, unit, positive, bounded, trace, exitPc, allowed, exit⟩ :=
    InlineEncoderInstanceContract.implements child args fromStep before childEntry
  exact ⟨used, after, bounded, trace.weaken (fun _ pc => insideWriter pc), exit⟩

set_option genInjectivity false in
/-- Common result of entering one selected called encoder after parent-owned register setup. -/
structure WriteSuccessEncoderChildHandoff (Value : Type)
    (fromStep parentUsed childUsed frameSize returnPc : Nat) (childBound : Nat → Nat)
    (encode : Value → Array UInt8) (value : Value) (writerArgs : WriteSuccessArgs)
    (before callState after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges)
    fromStep (parentUsed + childUsed) before after
  childBounded : childUsed ≤ childBound writerArgs.inputSize
  atPc : EndpointPc after = some (BitVec.ofNat 64 returnPc)
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (writerArgs.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encode value
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : WritesOnlyWithin
    (byteRange (writerArgs.stackPointer - 0x7d0 - frameSize) frameSize)
    before.machine after.machine
  calleeX8 : after.machine.regs.get? x8 = callState.machine.regs.get? x8
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess writerArgs after.machine

/-- Consume any selected called encoder once its exact parent-owned setup reaches the child entry. -/
private theorem writeSuccessEncoderChildHandoff
    {Value : Type} {entry frameSize returnPc : Nat}
    {executionPcs : List Elflings.PcRange} {exitPcs : List Nat}
    {encode : Value → Array UInt8} {bindValue : EndpointState → Value → Prop}
    (child : EncoderCallInstanceContract entry executionPcs exitPcs frameSize encode bindValue)
    (insideWriter : ∀ {pc}, pcInRanges executionPcs pc →
      pcInRanges Elflings.writeSuccessExecutionPcRanges pc)
    (fromStep parentUsed : Nat) (writerArgs : WriteSuccessArgs)
    (value : Value) (before callState : EndpointState)
    (childArgs : EncoderCallArgs Value)
    (argsEq : childArgs = {
      returnAddress := returnPc
      callerStack := writerArgs.stackPointer - 0x7d0
      inputSize := writerArgs.inputSize
      value })
    (childEntry : EncoderCallEntry entry exitPcs bindValue childArgs callState)
    (parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges)
      fromStep parentUsed before callState)
    (io : callState.stdin = before.stdin ∧ callState.stdinCursor = before.stdinCursor ∧
      callState.stdout = before.stdout ∧ callState.exitCode = before.exitCode)
    (memoryEq : callState.machine.mem = before.machine.mem)
    (access : WriteSuccessMachineAccess writerArgs callState.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully callState.machine.mem)
    (lower : 0x880 ≤ writerArgs.stackPointer)
    (frameInWriter : ∀ address,
      byteRange (writerArgs.stackPointer - 0x7d0 - frameSize) frameSize address →
      writeSuccessFrameMemory writerArgs address) :
    ∃ childUsed after,
      WriteSuccessEncoderChildHandoff Value fromStep parentUsed childUsed frameSize returnPc
        (EncoderCallInstanceContract.stepBound child)
        encode value writerArgs before callState after := by
  obtain ⟨childUsed, after, unit, positive, bounded, childTrace, exitPc, allowed, childExit⟩ :=
    EncoderCallInstanceContract.implements child childArgs (fromStep + parentUsed) callState childEntry
  rcases childExit with ⟨afterPc, stdout, stdin, cursor, exitCode, frameFits, childMemory,
    childFrame⟩
  have childTrace' := childTrace.weaken (fun _ pc => insideWriter pc)
  have memory : WritesOnlyWithin
      (byteRange (writerArgs.stackPointer - 0x7d0 - frameSize) frameSize)
      before.machine after.machine := by
    intro address outside
    rw [childMemory address (by simpa [argsEq] using outside), memoryEq]
  have pmaEq := childFrame.1 pma_regions (by simp [abiCalleePreserved])
  have accessAfter : WriteSuccessMachineAccess writerArgs after.machine := {
    configured := configuredAfterEndpointCall access.configured childFrame
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (access.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (access.frameStore offset width bound)
    frameNoMMIO := access.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (access.decodedLoad offset width bound)
    decodedNoMMIO := access.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq access.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq access.outputLengthStore
    writerRegionBeforeOutputContext := access.writerRegionBeforeOutputContext
    frameNotCode := access.frameNotCode }
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem := by
    intro address byte fileByte
    have outside : ¬byteRange (writerArgs.stackPointer - 0x7d0 - frameSize) frameSize address := by
      intro inside
      have inWriter := frameInWriter address inside
      unfold writeSuccessFrameMemory byteRange at inWriter
      have notCode := access.frameNotCode address inWriter.1 (by omega)
      exact Option.some_ne_none byte (fileByte.symm.trans notCode)
    rw [memory address outside]
    rw [← memoryEq]
    exact loaded address byte fileByte
  refine ⟨childUsed, after, {
    trace := by
      have all := parentTrace.append (by simpa [Nat.add_assoc] using childTrace')
      simpa [Nat.add_assoc] using all
    childBounded := by simpa [encoderCallContract, argsEq] using bounded
    atPc := by simpa [argsEq] using afterPc
    stack := by
      have := childFrame.1 x2 (by simp [abiCalleePreserved])
      simpa [argsEq] using this.trans childEntry.2.2.2.2.1
    stdout := by simpa [argsEq, io.2.2.1] using stdout
    stdin := by simpa [io.1] using stdin
    cursor := by simpa [io.2.1] using cursor
    exitCode := by simpa [io.2.2.2] using exitCode
    memory := memory
    calleeX8 := childFrame.1 x8 (by simp [abiCalleePreserved])
    loaded := loadedAfter
    access := accessAfter }⟩

set_option genInjectivity false in
structure RawEncoderPointerHandoff (fromStep childUsed nextEntry nextSourceAddress : Nat)
    (writerArgs : WriteSuccessArgs) (rawArgs : RawEncoderArgs)
    (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (childUsed + 1) before after
  atPc : EndpointPc after = some (BitVec.ofNat 64 nextEntry)
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (writerArgs.stackPointer - 0x7d0))
  source : after.machine.regs.get? x10 = some (BitVec.ofNat 64 nextSourceAddress)
  stdout : after.stdout = before.stdout ++ rawArgs.bytes
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : after.machine.mem = before.machine.mem
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess writerArgs after.machine

private theorem writeSuccessRawEncoderThenPointerHandoff
    {entry success nextEntry : Nat} {executionPcs : List Elflings.PcRange}
    {exitPcs : List Nat} (child : RawEncoderInstanceContract entry executionPcs exitPcs success)
    (insideWriter : ∀ {pc}, pcInRanges executionPcs pc →
      pcInRanges Elflings.writeSuccessExecutionPcRanges pc)
    (successOwned : writeSuccessParentPc (BitVec.ofNat 64 success))
    (successNotNext : BitVec.ofNat 64 success ≠ BitVec.ofNat 64 nextEntry)
    (nextAddress stackBase : Nat)
    (pointerStep : ∀ stepNo state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 success) →
      state.regs.get? x2 = some (BitVec.ofNat 64 stackBase) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state success retired x10 (BitVec.ofNat 64 nextAddress)) false)
    (advance : Sail.BitVec.addInt (BitVec.ofNat 64 success) 4 = BitVec.ofNat 64 nextEntry)
    (fromStep : Nat) (writerArgs : WriteSuccessArgs) (rawArgs : RawEncoderArgs)
    (before : EndpointState) (childEntry : RawEncoderEntry entry rawArgs before)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (writerArgs.stackPointer - 0x7d0)))
    (stackBaseEq : stackBase = writerArgs.stackPointer - 0x7d0)
    (access : WriteSuccessMachineAccess writerArgs before.machine) :
    ∃ childUsed after,
      RawEncoderPointerHandoff fromStep childUsed nextEntry nextAddress writerArgs rawArgs
        before after := by
  obtain ⟨childUsed, childAfter, _childBounded, childTrace, childExit⟩ :=
    writeSuccessRawEncoderHandoff child insideWriter fromStep rawArgs before childEntry
  rcases childExit with ⟨childPc, stdout, stdin, cursor, exitCode, childMem, childFrame⟩
  have childAtPc : childAfter.machine.regs.get? PC = some (BitVec.ofNat 64 success) := childPc
  have childStack := (childFrame.1 x2 (by simp [abiCalleePreserved])).trans stack
  have pmaEq := childFrame.1 pma_regions (by simp [abiCalleePreserved])
  have childAccess : WriteSuccessMachineAccess writerArgs childAfter.machine :=
    { configured := configuredAfterEndpointCall access.configured childFrame
      frameLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameLoad offset width inBounds)
      frameStore := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.frameStore offset width inBounds)
      frameNoMMIO := access.frameNoMMIO
      decodedLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.decodedLoad offset width inBounds)
      decodedNoMMIO := access.decodedNoMMIO
      outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq access.outputBufferStore
      outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq access.outputLengthStore
      writerRegionBeforeOutputContext := access.writerRegionBeforeOutputContext
      frameNotCode := access.frameNotCode }
  have childLoaded : Artifacts.programImage.fileBytesLoadedFaithfully childAfter.machine.mem := by
    simpa [childMem] using childEntry.2.2.2
  have seg0 : Seg writeSuccessParentPc
      (fun pc => pc = BitVec.ofNat 64 nextEntry)
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (writerArgs.stackPointer - 0x7d0)⟩]
      (fromStep + childUsed) 0 childAfter.machine childAfter.machine (BitVec.ofNat 64 success) := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := childAccess.configured.retiredCounter
    atPc := childAtPc
    regs := by
      intro pair member
      simp only [List.mem_singleton] at member
      subst pair
      exact childStack }
  obtain ⟨retired, run⟩ := pointerStep (fromStep + childUsed) childAfter.machine
    childAccess.configured childAtPc (by simpa [stackBaseEq] using childStack) childLoaded
  obtain ⟨retired', nextMachine, nextEq, seg1⟩ := seg0.stepWitness
    successOwned successNotNext x10 (BitVec.ofNat 64 nextAddress) (BitVec.ofNat 64 nextEntry)
    ⟨retired, run⟩ advance (fun _ h => Or.inl h) (by simp [writeSuccessParentWrites])
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  let after : EndpointState := { childAfter with machine := nextMachine }
  have parentMachineTrace := seg1.confined 0 nextMachine
    (.exitAt (fromStep + childUsed + 1) nextMachine (BitVec.ofNat 64 nextEntry) seg1.atPc
      rfl)
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) (fromStep + childUsed) 1
      childAfter after := by
    simpa [after] using liftWriteSuccessParentTrace childAfter parentMachineTrace
  refine ⟨childUsed, after, {
    trace := by simpa [Nat.add_assoc] using childTrace.append parentTrace
    atPc := by simpa [after, EndpointPc, MachinePc] using seg1.atPc
    stack := by
      simpa [after] using
        (seg1.reg x2 (BitVec.ofNat 64 (writerArgs.stackPointer - 0x7d0)) (by simp))
    source := by
      simpa [after] using (seg1.reg x10 (BitVec.ofNat 64 nextAddress) (by simp))
    stdout := stdout
    stdin := stdin
    cursor := cursor
    exitCode := exitCode
    memory := by simpa [after, seg1.memEq (by simp)] using childMem
    loaded := by simpa [after, seg1.memEq (by simp)] using childLoaded
    access := writeSuccessAccessOfSeg childAccess seg1 }⟩

private theorem writeSuccessRawPc_in_writeSuccess {pc : BitVec 64} {start stop : Nat}
    (inside : pcInRanges [(0x10190, 0x101c4), (start, stop)] pc)
    (startLower : 0x14d30 ≤ start) (stopUpper : stop ≤ 0x15a14) :
    pcInRanges Elflings.writeSuccessExecutionPcRanges pc := by
  unfold pcInRanges at inside ⊢
  rcases inside with ⟨range, member, lower, upper⟩
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lower, upper⟩
  · simp at member
    subst range
    exact ⟨(0x14d30, 0x15a14), by simp [Elflings.writeSuccessExecutionPcRanges],
      by omega, by omega⟩

private theorem writeSuccessParentHashThenFee
    (child : WriteSuccessParentHashInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (before : EndpointState)
    (atPc : EndpointPc before = some 0x14e2c)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (source : before.machine.regs.get? x10 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x4a0)))
    (rep : BytesRep before.machine.mem (args.stackPointer - 0x7d0 + 0x4a0)
      args.decoded.payload.parentHash)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (access : WriteSuccessMachineAccess args before.machine) :
    ∃ used after,
      RawEncoderPointerHandoff fromStep used 0x14e3c
        (args.stackPointer - 0x7d0 + 0x4c0) args
        { sourceAddress := args.stackPointer - 0x7d0 + 0x4a0
          bytes := args.decoded.payload.parentHash }
        before after := by
  let rawArgs : RawEncoderArgs :=
    { sourceAddress := args.stackPointer - 0x7d0 + 0x4a0
      bytes := args.decoded.payload.parentHash }
  apply writeSuccessRawEncoderThenPointerHandoff child (fun inside => by
    simpa [Elflings.writeSuccessRawLine135ExecutionPcRanges] using
      writeSuccessRawPc_in_writeSuccess inside (by omega) (by omega))
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e38, 0x14e3c), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide)
    (args.stackPointer - 0x7d0 + 0x4c0) (args.stackPointer - 0x7d0)
    (writeSuccessFeeRecipientSourceStep (stackPointer := args.stackPointer - 0x7d0))
    (by native_decide) fromStep args rawArgs before
  · exact ⟨by simpa [EndpointPc, MachinePc] using atPc, by simpa [rawArgs] using source,
      by simpa [rawArgs] using rep, loaded⟩
  · exact stack
  · rfl
  · exact access

private theorem writeSuccessFeeThenStateRoot
    (child : WriteSuccessFeeRecipientInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (before : EndpointState)
    (atPc : EndpointPc before = some 0x14e3c)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (source : before.machine.regs.get? x10 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x4c0)))
    (rep : BytesRep before.machine.mem (args.stackPointer - 0x7d0 + 0x4c0)
      args.decoded.payload.feeRecipient)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (access : WriteSuccessMachineAccess args before.machine) :
    ∃ used after,
      RawEncoderPointerHandoff fromStep used 0x14e4c
        (args.stackPointer - 0x7d0 + 0x4d4) args
        { sourceAddress := args.stackPointer - 0x7d0 + 0x4c0
          bytes := args.decoded.payload.feeRecipient }
        before after := by
  let rawArgs : RawEncoderArgs :=
    { sourceAddress := args.stackPointer - 0x7d0 + 0x4c0
      bytes := args.decoded.payload.feeRecipient }
  apply writeSuccessRawEncoderThenPointerHandoff child (fun inside => by
    simpa [Elflings.writeSuccessRawLine136ExecutionPcRanges] using
      writeSuccessRawPc_in_writeSuccess inside (by omega) (by omega))
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e48, 0x14e4c), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) (args.stackPointer - 0x7d0 + 0x4d4)
    (args.stackPointer - 0x7d0)
    (writeSuccessStateRootSourceStep (stackPointer := args.stackPointer - 0x7d0))
    (by native_decide) fromStep args rawArgs before
  · exact ⟨by simpa [EndpointPc, MachinePc] using atPc, by simpa [rawArgs] using source,
      by simpa [rawArgs] using rep, loaded⟩
  · exact stack
  · rfl
  · exact access

private theorem writeSuccessStateThenReceiptsRoot
    (child : WriteSuccessStateRootInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (before : EndpointState)
    (atPc : EndpointPc before = some 0x14e4c)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (source : before.machine.regs.get? x10 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x4d4)))
    (rep : BytesRep before.machine.mem (args.stackPointer - 0x7d0 + 0x4d4)
      args.decoded.payload.stateRoot)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (access : WriteSuccessMachineAccess args before.machine) :
    ∃ used after,
      RawEncoderPointerHandoff fromStep used 0x14e5c
        (args.stackPointer - 0x7d0 + 0x4f4) args
        { sourceAddress := args.stackPointer - 0x7d0 + 0x4d4
          bytes := args.decoded.payload.stateRoot }
        before after := by
  let rawArgs : RawEncoderArgs :=
    { sourceAddress := args.stackPointer - 0x7d0 + 0x4d4
      bytes := args.decoded.payload.stateRoot }
  apply writeSuccessRawEncoderThenPointerHandoff child (fun inside => by
    simpa [Elflings.writeSuccessRawLine137ExecutionPcRanges] using
      writeSuccessRawPc_in_writeSuccess inside (by omega) (by omega))
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e58, 0x14e5c), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) (args.stackPointer - 0x7d0 + 0x4f4)
    (args.stackPointer - 0x7d0)
    (writeSuccessReceiptsRootSourceStep (stackPointer := args.stackPointer - 0x7d0))
    (by native_decide) fromStep args rawArgs before
  · exact ⟨by simpa [EndpointPc, MachinePc] using atPc, by simpa [rawArgs] using source,
      by simpa [rawArgs] using rep, loaded⟩
  · exact stack
  · rfl
  · exact access

private theorem writeSuccessReceiptsThenLogsBloom
    (child : WriteSuccessReceiptsRootInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (before : EndpointState)
    (atPc : EndpointPc before = some 0x14e5c)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (source : before.machine.regs.get? x10 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x4f4)))
    (rep : BytesRep before.machine.mem (args.stackPointer - 0x7d0 + 0x4f4)
      args.decoded.payload.receiptsRoot)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (access : WriteSuccessMachineAccess args before.machine) :
    ∃ used after,
      RawEncoderPointerHandoff fromStep used 0x14e6c
        (args.stackPointer - 0x7d0 + 0x514) args
        { sourceAddress := args.stackPointer - 0x7d0 + 0x4f4
          bytes := args.decoded.payload.receiptsRoot }
        before after := by
  let rawArgs : RawEncoderArgs :=
    { sourceAddress := args.stackPointer - 0x7d0 + 0x4f4
      bytes := args.decoded.payload.receiptsRoot }
  apply writeSuccessRawEncoderThenPointerHandoff child (fun inside => by
    simpa [Elflings.writeSuccessRawLine138ExecutionPcRanges] using
      writeSuccessRawPc_in_writeSuccess inside (by omega) (by omega))
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e68, 0x14e6c), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) (args.stackPointer - 0x7d0 + 0x514)
    (args.stackPointer - 0x7d0)
    (writeSuccessLogsBloomSourceStep (stackPointer := args.stackPointer - 0x7d0))
    (by native_decide) fromStep args rawArgs before
  · exact ⟨by simpa [EndpointPc, MachinePc] using atPc, by simpa [rawArgs] using source,
      by simpa [rawArgs] using rep, loaded⟩
  · exact stack
  · rfl
  · exact access

private theorem writeSuccessLogsThenPrevRandao
    (child : WriteSuccessLogsBloomInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (before : EndpointState)
    (atPc : EndpointPc before = some 0x14e6c)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (source : before.machine.regs.get? x10 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x514)))
    (rep : BytesRep before.machine.mem (args.stackPointer - 0x7d0 + 0x514)
      args.decoded.payload.logsBloom)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (access : WriteSuccessMachineAccess args before.machine) :
    ∃ used after,
      RawEncoderPointerHandoff fromStep used 0x14e7c
        (args.stackPointer - 0x7d0 + 0x614) args
        { sourceAddress := args.stackPointer - 0x7d0 + 0x514
          bytes := args.decoded.payload.logsBloom }
        before after := by
  let rawArgs : RawEncoderArgs :=
    { sourceAddress := args.stackPointer - 0x7d0 + 0x514
      bytes := args.decoded.payload.logsBloom }
  apply writeSuccessRawEncoderThenPointerHandoff child (fun inside => by
    simpa [Elflings.writeSuccessRawLine139ExecutionPcRanges] using
      writeSuccessRawPc_in_writeSuccess inside (by omega) (by omega))
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e78, 0x14e7c), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) (args.stackPointer - 0x7d0 + 0x614)
    (args.stackPointer - 0x7d0)
    (writeSuccessPrevRandaoSourceStep (stackPointer := args.stackPointer - 0x7d0))
    (by native_decide) fromStep args rawArgs before
  · exact ⟨by simpa [EndpointPc, MachinePc] using atPc, by simpa [rawArgs] using source,
      by simpa [rawArgs] using rep, loaded⟩
  · exact stack
  · rfl
  · exact access

set_option genInjectivity false in
structure WriteSuccessFirstThreeRawHandoff (fromStep parentHashUsed feeUsed stateUsed : Nat)
    (args : WriteSuccessArgs) (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep
    (parentHashUsed + 1 + feeUsed + 1 + stateUsed + 1) before after
  atPc : EndpointPc after = some 0x14e5c
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  source : after.machine.regs.get? x10 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x4f4))
  stdout : after.stdout = before.stdout ++ args.decoded.payload.parentHash ++
    args.decoded.payload.feeRecipient ++ args.decoded.payload.stateRoot
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : after.machine.mem = before.machine.mem
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  fieldReps : RawPayloadFieldReps after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  payloadRep : ExecutionPayloadRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload

private theorem writeSuccessFirstThreeRawHandoff
    (parentHash : WriteSuccessParentHashInstanceContract)
    (feeRecipient : WriteSuccessFeeRecipientInstanceContract)
    (stateRoot : WriteSuccessStateRootInstanceContract)
    {fromStep parentUsed prefixUsed memcpyUsed : Nat} {args : WriteSuccessArgs}
    {origin before : EndpointState} {values : DecodeCalleeSavedValues}
    {bytes : Array UInt8} {tailValues : Fin 16 → Nat}
    (beforeHandoff : WriteSuccessSecondMemcpyHandoff fromStep parentUsed prefixUsed memcpyUsed
      args origin before values bytes tailValues) :
    ∃ parentHashUsed feeUsed stateUsed after,
      WriteSuccessFirstThreeRawHandoff
        (fromStep + (20 + parentUsed + 32 + prefixUsed + 5 + memcpyUsed + 1))
        parentHashUsed feeUsed stateUsed args before after := by
  let start0 := fromStep + (20 + parentUsed + 32 + prefixUsed + 5 + memcpyUsed + 1)
  obtain ⟨parentHashUsed, after1, h1⟩ := writeSuccessParentHashThenFee parentHash start0
    args before beforeHandoff.atPc beforeHandoff.stack beforeHandoff.source
    beforeHandoff.fieldReps.parentHash beforeHandoff.loaded beforeHandoff.access
  have fields1 : RawPayloadFieldReps after1.machine.mem
      (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload := by
    simpa [h1.memory] using beforeHandoff.fieldReps
  let start1 := start0 + parentHashUsed + 1
  obtain ⟨feeUsed, after2, h2⟩ := writeSuccessFeeThenStateRoot feeRecipient start1 args
    after1 h1.atPc h1.stack h1.source fields1.feeRecipient h1.loaded h1.access
  have fields2 : RawPayloadFieldReps after2.machine.mem
      (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload := by
    simpa [h2.memory] using fields1
  let start2 := start1 + feeUsed + 1
  obtain ⟨stateUsed, after3, h3⟩ := writeSuccessStateThenReceiptsRoot stateRoot start2 args
    after2 h2.atPc h2.stack h2.source fields2.stateRoot h2.loaded h2.access
  have fields3 : RawPayloadFieldReps after3.machine.mem
      (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload := by
    simpa [h3.memory] using fields2
  refine ⟨parentHashUsed, feeUsed, stateUsed, after3, {
    trace := ?_
    atPc := h3.atPc
    stack := h3.stack
    source := h3.source
    stdout := ?_
    stdin := h3.stdin.trans (h2.stdin.trans h1.stdin)
    cursor := h3.cursor.trans (h2.cursor.trans h1.cursor)
    exitCode := h3.exitCode.trans (h2.exitCode.trans h1.exitCode)
    memory := h3.memory.trans (h2.memory.trans h1.memory)
    loaded := h3.loaded
    access := h3.access
    fieldReps := fields3
    payloadRep := by simpa [h3.memory, h2.memory, h1.memory] using beforeHandoff.payloadRep }⟩
  · have t12 := h1.trace.append (by simpa [start1, Nat.add_assoc] using h2.trace)
    have h3Trace : ConfinedTrace EndpointStep EndpointPc
        (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        (start0 + (parentHashUsed + 1 + feeUsed + 1)) (stateUsed + 1) after2 after3 := by
      simpa [start1, start2, Nat.add_assoc] using h3.trace
    simpa [start0, start1, start2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      t12.append h3Trace
  · rw [h3.stdout, h2.stdout, h1.stdout]

private theorem writeSuccessPrevRandaoHandoff
    (child : WriteSuccessPrevRandaoInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (before : EndpointState)
    (atPc : EndpointPc before = some 0x14e7c)
    (source : before.machine.regs.get? x10 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x614)))
    (rep : BytesRep before.machine.mem (args.stackPointer - 0x7d0 + 0x614)
      args.decoded.payload.prevRandao)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem) :
    ∃ used after,
      ConfinedTrace EndpointStep EndpointPc
        (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep used before after ∧
      RawEncoderExit 0x14e88
        { sourceAddress := args.stackPointer - 0x7d0 + 0x614
          bytes := args.decoded.payload.prevRandao }
        () before after := by
  let rawArgs : RawEncoderArgs :=
    { sourceAddress := args.stackPointer - 0x7d0 + 0x614
      bytes := args.decoded.payload.prevRandao }
  obtain ⟨used, after, _bounded, trace, exit⟩ :=
    writeSuccessRawEncoderHandoff child (fun inside => by
    simpa [Elflings.writeSuccessRawLine140ExecutionPcRanges] using
      writeSuccessRawPc_in_writeSuccess inside (by omega) (by omega))
    fromStep rawArgs before
    ⟨by simpa [EndpointPc, MachinePc] using atPc, by simpa [rawArgs] using source,
      by simpa [rawArgs] using rep, loaded⟩
  exact ⟨used, after, trace, exit⟩

set_option genInjectivity false in
structure WriteSuccessLastThreeRawHandoff
    (fromStep receiptsUsed logsUsed prevRandaoUsed : Nat)
    (args : WriteSuccessArgs) (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep
    (receiptsUsed + 1 + logsUsed + 1 + prevRandaoUsed) before after
  atPc : EndpointPc after = some 0x14e88
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ args.decoded.payload.receiptsRoot ++
    args.decoded.payload.logsBloom ++ args.decoded.payload.prevRandao
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : after.machine.mem = before.machine.mem
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  fieldReps : RawPayloadFieldReps after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload

private theorem writeSuccessLastThreeRawHandoff
    (receiptsRoot : WriteSuccessReceiptsRootInstanceContract)
    (logsBloom : WriteSuccessLogsBloomInstanceContract)
    (prevRandao : WriteSuccessPrevRandaoInstanceContract)
    {fromStep parentHashUsed feeUsed stateUsed : Nat} {args : WriteSuccessArgs}
    {initial before : EndpointState}
    (beforeHandoff : WriteSuccessFirstThreeRawHandoff fromStep parentHashUsed feeUsed stateUsed
      args initial before) :
    ∃ receiptsUsed logsUsed prevRandaoUsed after,
      WriteSuccessLastThreeRawHandoff
        (fromStep + (parentHashUsed + 1 + feeUsed + 1 + stateUsed + 1))
        receiptsUsed logsUsed prevRandaoUsed args before after := by
  let start0 := fromStep + (parentHashUsed + 1 + feeUsed + 1 + stateUsed + 1)
  obtain ⟨receiptsUsed, after1, h1⟩ := writeSuccessReceiptsThenLogsBloom receiptsRoot start0
    args before beforeHandoff.atPc beforeHandoff.stack beforeHandoff.source
    beforeHandoff.fieldReps.receiptsRoot beforeHandoff.loaded beforeHandoff.access
  have fields1 : RawPayloadFieldReps after1.machine.mem
      (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload := by
    simpa [h1.memory] using beforeHandoff.fieldReps
  let start1 := start0 + receiptsUsed + 1
  obtain ⟨logsUsed, after2, h2⟩ := writeSuccessLogsThenPrevRandao logsBloom start1 args
    after1 h1.atPc h1.stack h1.source fields1.logsBloom h1.loaded h1.access
  have fields2 : RawPayloadFieldReps after2.machine.mem
      (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload := by
    simpa [h2.memory] using fields1
  let start2 := start1 + logsUsed + 1
  obtain ⟨prevRandaoUsed, after3, trace3, exit3⟩ :=
    writeSuccessPrevRandaoHandoff prevRandao start2 args after2 h2.atPc h2.source
      fields2.prevRandao h2.loaded
  rcases exit3 with ⟨pc3, stdout3, stdin3, cursor3, exitCode3, memory3, frame3⟩
  have pmaEq3 := frame3.1 pma_regions (by simp [abiCalleePreserved])
  have access3 : WriteSuccessMachineAccess args after3.machine :=
    { configured := configuredAfterEndpointCall h2.access.configured frame3
      frameLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq pmaEq3 (h2.access.frameLoad offset width inBounds)
      frameStore := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq pmaEq3 (h2.access.frameStore offset width inBounds)
      frameNoMMIO := h2.access.frameNoMMIO
      decodedLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq pmaEq3 (h2.access.decodedLoad offset width inBounds)
      decodedNoMMIO := h2.access.decodedNoMMIO
      outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq3 h2.access.outputBufferStore
      outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq3 h2.access.outputLengthStore
      writerRegionBeforeOutputContext := h2.access.writerRegionBeforeOutputContext
      frameNotCode := h2.access.frameNotCode }
  have fields3 : RawPayloadFieldReps after3.machine.mem
      (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload := by
    simpa [memory3] using fields2
  refine ⟨receiptsUsed, logsUsed, prevRandaoUsed, after3, {
    trace := ?_
    atPc := by simpa [EndpointPc, MachinePc] using pc3
    stack := (frame3.1 x2 (by simp [abiCalleePreserved])).trans h2.stack
    stdout := ?_
    stdin := stdin3.trans (h2.stdin.trans h1.stdin)
    cursor := cursor3.trans (h2.cursor.trans h1.cursor)
    exitCode := exitCode3.trans (h2.exitCode.trans h1.exitCode)
    memory := memory3.trans (h2.memory.trans h1.memory)
    loaded := by simpa [memory3] using h2.loaded
    access := access3
    fieldReps := fields3 }⟩
  · have t12 := h1.trace.append (by simpa [start1, Nat.add_assoc] using h2.trace)
    have t3 : ConfinedTrace EndpointStep EndpointPc
        (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        (start0 + (receiptsUsed + 1 + logsUsed + 1)) prevRandaoUsed after2 after3 := by
      simpa [start1, start2, Nat.add_assoc] using trace3
    simpa [start0, start1, start2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      t12.append t3
  · rw [stdout3, h2.stdout, h1.stdout]

set_option genInjectivity false in
structure WriteSuccessSixRawFieldsHandoff
    (fromStep parentUsed prefixUsed memcpyUsed parentHashUsed feeUsed stateUsed
      receiptsUsed logsUsed prevRandaoUsed : Nat)
    (args : WriteSuccessArgs) (before after : EndpointState)
    (values : DecodeCalleeSavedValues) (bytes : Array UInt8) (tailValues : Fin 16 → Nat) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep
    (20 + parentUsed + 32 + prefixUsed + 5 + memcpyUsed + 1 +
      (parentHashUsed + 1 + feeUsed + 1 + stateUsed + 1) +
      (receiptsUsed + 1 + logsUsed + 1 + prevRandaoUsed)) before after
  atPc : EndpointPc after = some 0x14e88
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ successPrefixBytes ++
    args.decoded.payload.parentHash ++ args.decoded.payload.feeRecipient ++
    args.decoded.payload.stateRoot ++ args.decoded.payload.receiptsRoot ++
    args.decoded.payload.logsBloom ++ args.decoded.payload.prevRandao
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  destinationRep : BytesRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) bytes
  parentRootRep : BytesRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x3e8) args.decoded.parentBeaconBlockRoot
  versionedHashesRelocation : ByteWindowRelocation after.machine.mem after.machine.mem
    (args.decodedAddress + 592) (args.stackPointer - 0x7d0 + 0x388) 16
  bytesSize : bytes.size = 0x250
  sourceRep : BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes
  fullCopy : ∃ fullBytes : Array UInt8, fullBytes.size = 720 ∧
    BytesRep after.machine.mem args.decodedAddress fullBytes ∧
    BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) fullBytes
  tailReps : ∀ index (inBounds : index < 16),
    UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
      (tailValues ⟨index, inBounds⟩)
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  slotWord : ∃ value, UIntRep 8 after.machine.mem
    (args.stackPointer - 0x7d0 + 0x480) value
  slotTagWord : ∃ value, UIntRep 8 after.machine.mem
    (args.stackPointer - 0x7d0 + 0x488) value
  localTailReps : WriteSuccessLocalTailReps args after
  linkedTailReps : WriteSuccessLinkedTailReps args after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memoryFrame : WriteSuccessMemoryFrame args before.machine after.machine
  fieldReps : RawPayloadFieldReps after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  payloadRep : ExecutionPayloadRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  decodedBytesRep : BytesRep after.machine.mem args.decodedAddress bytes
  stable : StatelessInputRepStableOutside (writeSuccessMemoryRegion args)
    after.machine.mem args.decodedAddress args.decoded

/-- Compose the copied payload prefix with its first six raw-field encoder children. -/
theorem writeSuccessSixRawFieldsHandoff
    (prefixChild : WriteSuccessPrefixInstanceContract)
    (parentHash : WriteSuccessParentHashInstanceContract)
    (feeRecipient : WriteSuccessFeeRecipientInstanceContract)
    (stateRoot : WriteSuccessStateRootInstanceContract)
    (receiptsRoot : WriteSuccessReceiptsRootInstanceContract)
    (logsBloom : WriteSuccessLogsBloomInstanceContract)
    (prevRandao : WriteSuccessPrevRandaoInstanceContract)
    (fromStep : Nat) (args : WriteSuccessArgs) (state : EndpointState)
    (entry : WriteSuccessEntry args state) :
    ∃ values bytes, ∃ tailValues : Fin 16 → Nat,
      ∃ parentUsed prefixUsed memcpyUsed parentHashUsed feeUsed stateUsed receiptsUsed logsUsed
        prevRandaoUsed after,
        WriteSuccessSixRawFieldsHandoff fromStep parentUsed prefixUsed memcpyUsed parentHashUsed
          feeUsed stateUsed receiptsUsed logsUsed prevRandaoUsed args state after values bytes
          tailValues := by
  obtain ⟨values, bytes, tailValues, parentUsed, prefixUsed, memcpyUsed, initial, initialHandoff⟩ :=
    writeSuccessSecondMemcpyHandoff prefixChild fromStep args state entry
  obtain ⟨parentHashUsed, feeUsed, stateUsed, middle, firstHandoff⟩ :=
    writeSuccessFirstThreeRawHandoff parentHash feeRecipient stateRoot initialHandoff
  obtain ⟨receiptsUsed, logsUsed, prevRandaoUsed, after, lastHandoff⟩ :=
    writeSuccessLastThreeRawHandoff receiptsRoot logsBloom prevRandao firstHandoff
  have rawMemory : after.machine.mem = initial.machine.mem :=
    lastHandoff.memory.trans firstHandoff.memory
  refine ⟨values, bytes, tailValues, parentUsed, prefixUsed, memcpyUsed, parentHashUsed,
    feeUsed, stateUsed, receiptsUsed, logsUsed, prevRandaoUsed, after, {
      trace := ?_
      atPc := lastHandoff.atPc
      stack := lastHandoff.stack
      stdout := ?_
      stdin := lastHandoff.stdin.trans (firstHandoff.stdin.trans initialHandoff.stdin)
      cursor := lastHandoff.cursor.trans (firstHandoff.cursor.trans initialHandoff.cursor)
      exitCode := lastHandoff.exitCode.trans
        (firstHandoff.exitCode.trans initialHandoff.exitCode)
      destinationRep := by simpa [rawMemory] using initialHandoff.destinationRep
      parentRootRep := by simpa [rawMemory] using initialHandoff.parentRootRep
      versionedHashesRelocation := by
        simpa [rawMemory] using initialHandoff.versionedHashesRelocation
      bytesSize := initialHandoff.bytesSize
      sourceRep := by simpa [rawMemory] using initialHandoff.sourceRep
      fullCopy := by simpa [rawMemory] using initialHandoff.fullCopy
      tailReps := by
        intro index inBounds
        simpa [rawMemory] using initialHandoff.tailReps index inBounds
      saved := by
        intro word member
        simpa [rawMemory] using initialHandoff.saved word member
      slotWord := by simpa [rawMemory] using initialHandoff.slotWord
      slotTagWord := by simpa [rawMemory] using initialHandoff.slotTagWord
      localTailReps := by
        simpa only [WriteSuccessLocalTailReps, rawMemory] using initialHandoff.localTailReps
      linkedTailReps := by
        simpa only [WriteSuccessLinkedTailReps, rawMemory] using initialHandoff.linkedTailReps
      loaded := lastHandoff.loaded
      access := lastHandoff.access
      memoryFrame := by
        intro address outside
        rw [rawMemory]
        exact initialHandoff.memoryFrame address outside
      fieldReps := lastHandoff.fieldReps
      payloadRep := by simpa [rawMemory] using initialHandoff.payloadRep
      decodedBytesRep := by simpa [rawMemory] using initialHandoff.decodedBytesRep
      stable := by simpa [rawMemory] using initialHandoff.stable }⟩
  · have firstTrace : ConfinedTrace EndpointStep EndpointPc
        (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        (fromStep + (20 + parentUsed + 32 + prefixUsed + 5 + memcpyUsed + 1))
        (parentHashUsed + 1 + feeUsed + 1 + stateUsed + 1) initial middle :=
      firstHandoff.trace
    have prefixAndFirst := initialHandoff.trace.append firstTrace
    have lastTrace : ConfinedTrace EndpointStep EndpointPc
        (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        (fromStep + (20 + parentUsed + 32 + prefixUsed + 5 + memcpyUsed + 1 +
          (parentHashUsed + 1 + feeUsed + 1 + stateUsed + 1)))
        (receiptsUsed + 1 + logsUsed + 1 + prevRandaoUsed) middle after := by
      simpa [Nat.add_assoc] using lastHandoff.trace
    simpa [Nat.add_assoc] using prefixAndFirst.append lastTrace
  · rw [lastHandoff.stdout, firstHandoff.stdout, initialHandoff.stdout]

/-- Execute one parent-owned dword load from the writer's copied payload value. -/
private theorem writeSuccessFrameDwordLoadStep (stepNo pc offset value : Nat)
    (args : WriteSuccessArgs) (state : State) (rd : regidx) (destination : Register)
    (result : RegisterType destination) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + offset) value)
    (offsetBound : offset + 8 ≤ 0x7d0)
    (aligned : (args.stackPointer - 0x7d0 + offset) % 8 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 (args.stackPointer - 0x7d0) + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (args.stackPointer - 0x7d0 + offset))
    (writeRun : ∀ premise, Runs (wX_bits rd (BitVec.ofNat 64 value)) premise
      { premise with regs := premise.regs.insert destination result } ())
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (imm, .Regidx 2#5, rd, false, 8)))
    (pcFits : pc < 2 ^ 64)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3)
    (destinationNotNextPc : destination ≠ nextPC := by decide)
    (destinationNotHart : destination ≠ hart_state := by decide)
    (destinationNotIncrement : destination ≠ minstret_increment := by decide)
    (destinationNotRetired : destination ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false := by
  exact configuredDwordLoadStep stepNo pc state imm (.Regidx 2#5) rd destination
    (args.stackPointer - 0x7d0) offset value result byte0 byte1 byte2 byte3 access.configured
    atPc rep (access.frameLoad offset 8 offsetBound) (access.frameNoMMIO offset 8 offsetBound)
    (by have := rep.2.1; omega) aligned loaded addressEq
    (fun premise writes => rX_x2_run premise (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
    ((writes.get x2 (by decide)).trans stack)) writeRun decode (pcFits := pcFits)
    (destinationNotNextPc := destinationNotNextPc) (destinationNotHart := destinationNotHart)
    (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired) (base := base)
    (read0 := read0) (read1 := read1) (read2 := read2) (read3 := read3)

/-- Execute one parent-owned dword store into the writer frame. -/
private theorem writeSuccessFrameDwordStoreRegStep (stepNo pc offset value : Nat)
    (args : WriteSuccessArgs) (state : State) (rs2 : regidx) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (offsetBound : offset + 8 ≤ 0x7d0)
    (aligned : (args.stackPointer - 0x7d0 + offset) % 8 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (upper : args.stackPointer < 2 ^ 64)
    (addressEq : BitVec.ofNat 64 (args.stackPointer - 0x7d0) + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (args.stackPointer - 0x7d0 + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (imm, rs2, .Regidx 2#5, 8)))
    (pcFits : pc < 2 ^ 64)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3)
    (sourceRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs2) premise premise (BitVec.ofNat 64 value)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc))
          (args.stackPointer - 0x7d0 + offset) (BitVec.ofNat 64 value))
        (BitVec.ofNat 64 pc) retired) false := by
  exact decodeInputStoreStep stepNo pc offset state (args.stackPointer - 0x7d0)
    (BitVec.ofNat 64 value) imm rs2 byte0 byte1 byte2 byte3 access.configured
    atPc stack (access.frameStore offset 8 offsetBound) (access.frameNoMMIO offset 8 offsetBound)
    aligned (by omega) loaded addressEq decode
    sourceRun
    (pcFits := pcFits) (base := base) (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3)

/-- Compatibility wrapper for the writer's common x10 stores. -/
private theorem writeSuccessFrameDwordStoreStep (stepNo pc offset value : Nat)
    (args : WriteSuccessArgs) (state : State) (imm : BitVec 12)
    (byte0 byte1 byte2 byte3 : UInt8)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (data : state.regs.get? x10 = some (BitVec.ofNat 64 value))
    (offsetBound : offset + 8 ≤ 0x7d0)
    (aligned : (args.stackPointer - 0x7d0 + offset) % 8 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (upper : args.stackPointer < 2 ^ 64)
    (addressEq : BitVec.ofNat 64 (args.stackPointer - 0x7d0) + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (args.stackPointer - 0x7d0 + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (imm, .Regidx 10#5, .Regidx 2#5, 8)))
    (pcFits : pc < 2 ^ 64)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc))
          (args.stackPointer - 0x7d0 + offset) (BitVec.ofNat 64 value))
        (BitVec.ofNat 64 pc) retired) false := by
  apply writeSuccessFrameDwordStoreRegStep stepNo pc offset value args state (.Regidx 10#5)
    imm byte0 byte1 byte2 byte3 access atPc stack offsetBound aligned loaded upper
    addressEq decode pcFits base read0 read1 read2 read3
  intro premise writes
  exact rX_x10_run premise _ ((writes.get x10 (by decide)).trans data)

/-- Production `0x14e88: ld a0,0x408(sp)`. -/
private theorem writeSuccessBlockNumberLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x14e88)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x408)
      args.decoded.payload.blockNumber)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e88 retired x10
        (BitVec.ofNat 64 args.decoded.payload.blockNumber)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x14e88 0x408
    args.decoded.payload.blockNumber args state (.Regidx 10#5) x10
    (BitVec.ofNat 64 args.decoded.payload.blockNumber) 0x408 0x03 0x35 0x81 0x40
    access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x408#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise (BitVec.ofNat 64 args.decoded.payload.blockNumber)
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x14e8c: auipc ra,1`. -/
private theorem writeSuccessFirstIntCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e8c)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e8c retired x1 0x15e8c) false := by
  apply configuredAuipcStep stepNo state 0x14e8c 1 0x97 0x10 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x14e90: jalr ra,-380(ra)`, entering the shared integer encoder. -/
private theorem writeSuccessFirstIntCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e90)
    (baseRead : state.regs.get? x1 = some 0x15e8c)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14e90 0x15d10 x1 0x14e94)
        0x15d10 retired) false := by
  apply configuredJalrCallStep stepNo state 0x14e90 0x15e8c 0xe84 0x15d10 0x14e94
    0xe7 0x80 0x40 0xe8 configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x14e94: ld a0,0x410(sp)`. -/
private theorem writeSuccessGasLimitLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x14e94)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x410)
      args.decoded.payload.gasLimit)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e94 retired x10
        (BitVec.ofNat 64 args.decoded.payload.gasLimit)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x14e94 0x410 args.decoded.payload.gasLimit
    args state (.Regidx 10#5) x10 (BitVec.ofNat 64 args.decoded.payload.gasLimit)
    0x410 0x03 0x35 0x01 0x41 access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x410#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise (BitVec.ofNat 64 args.decoded.payload.gasLimit)
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x14e98: auipc ra,1`. -/
private theorem writeSuccessGasLimitCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e98)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14e98 retired x1 0x15e98) false := by
  apply configuredAuipcStep stepNo state 0x14e98 1 0x97 0x10 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x14e9c: jalr ra,-392(ra)`. -/
private theorem writeSuccessGasLimitCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14e9c)
    (baseRead : state.regs.get? x1 = some 0x15e98)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14e9c 0x15d10 x1 0x14ea0)
        0x15d10 retired) false := by
  apply configuredJalrCallStep stepNo state 0x14e9c 0x15e98 0xe78 0x15d10 0x14ea0
    0xe7 0x80 0x80 0xe7 configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x14ea0: ld a0,0x418(sp)`. -/
private theorem writeSuccessGasUsedLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x14ea0)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x418)
      args.decoded.payload.gasUsed)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14ea0 retired x10
        (BitVec.ofNat 64 args.decoded.payload.gasUsed)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x14ea0 0x418 args.decoded.payload.gasUsed
    args state (.Regidx 10#5) x10 (BitVec.ofNat 64 args.decoded.payload.gasUsed)
    0x418 0x03 0x35 0x81 0x41 access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x418#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise (BitVec.ofNat 64 args.decoded.payload.gasUsed)
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x14ea4: auipc ra,1`. -/
private theorem writeSuccessGasUsedCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14ea4)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14ea4 retired x1 0x15ea4) false := by
  apply configuredAuipcStep stepNo state 0x14ea4 1 0x97 0x10 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x14ea8: jalr ra,-404(ra)`. -/
private theorem writeSuccessGasUsedCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14ea8)
    (baseRead : state.regs.get? x1 = some 0x15ea4)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14ea8 0x15d10 x1 0x14eac)
        0x15d10 retired) false := by
  apply configuredJalrCallStep stepNo state 0x14ea8 0x15ea4 0xe6c 0x15d10 0x14eac
    0xe7 0x80 0xc0 0xe6 configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x14eac: ld a0,0x420(sp)`. -/
private theorem writeSuccessTimestampLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x14eac)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x420)
      args.decoded.payload.timestamp)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14eac retired x10
        (BitVec.ofNat 64 args.decoded.payload.timestamp)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x14eac 0x420 args.decoded.payload.timestamp
    args state (.Regidx 10#5) x10 (BitVec.ofNat 64 args.decoded.payload.timestamp)
    0x420 0x03 0x35 0x01 0x42 access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x420#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise (BitVec.ofNat 64 args.decoded.payload.timestamp)
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x14eb0: auipc ra,1`. -/
private theorem writeSuccessTimestampCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14eb0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14eb0 retired x1 0x15eb0) false := by
  apply configuredAuipcStep stepNo state 0x14eb0 1 0x97 0x10 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x14eb4: jalr ra,-416(ra)`. -/
private theorem writeSuccessTimestampCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14eb4)
    (baseRead : state.regs.get? x1 = some 0x15eb0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14eb4 0x15d10 x1 0x14eb8)
        0x15d10 retired) false := by
  apply configuredJalrCallStep stepNo state 0x14eb4 0x15eb0 0xe60 0x15d10 0x14eb8
    0xe7 0x80 0x00 0xe6 configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x14eb8: ld a0,0x428(sp)`, loading the extra-data pointer. -/
private theorem writeSuccessExtraDataPointerLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (address : Nat) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x14eb8)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x428) address)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14eb8 retired x10 (BitVec.ofNat 64 address)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x14eb8 0x428 address args state (.Regidx 10#5)
    x10 (BitVec.ofNat 64 address) 0x428 0x03 0x35 0x81 0x42 access atPc stack rep
    (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x428#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise (BitVec.ofNat 64 address)
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x14ebc: ld a1,0x430(sp)`, loading the extra-data length. -/
private theorem writeSuccessExtraDataLengthLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (length : Nat) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x14ebc)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x430) length)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14ebc retired x11 (BitVec.ofNat 64 length)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x14ebc 0x430 length args state (.Regidx 11#5)
    x11 (BitVec.ofNat 64 length) 0x430 0x83 0x35 0x01 0x43 access atPc stack rep
    (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x430#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x11_run premise (BitVec.ofNat 64 length)
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x14ec0: auipc ra,1`. -/
private theorem writeSuccessExtraDataCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14ec0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14ec0 retired x1 0x15ec0) false := by
  apply configuredAuipcStep stepNo state 0x14ec0 1 0x97 0x10 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x14ec4: jalr ra,-596(ra)`, entering the shared byte encoder. -/
private theorem writeSuccessExtraDataCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14ec4)
    (baseRead : state.regs.get? x1 = some 0x15ec0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14ec4 0x15c6c x1 0x14ec8)
        0x15c6c retired) false := by
  apply configuredJalrCallStep stepNo state 0x14ec4 0x15ec0 0xdac 0x15c6c 0x14ec8
    0xe7 0x80 0xc0 0xda configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x14ec8: ld a0,0x438(sp)`. -/
private theorem writeSuccessBaseFeeLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x14ec8)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x438)
      args.decoded.payload.baseFeePerGas)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14ec8 retired x10
        (BitVec.ofNat 64 args.decoded.payload.baseFeePerGas)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x14ec8 0x438 args.decoded.payload.baseFeePerGas
    args state (.Regidx 10#5) x10 (BitVec.ofNat 64 args.decoded.payload.baseFeePerGas)
    0x438 0x03 0x35 0x81 0x43 access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x438#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise (BitVec.ofNat 64 args.decoded.payload.baseFeePerGas)
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x14ecc: auipc ra,1`. -/
private theorem writeSuccessBaseFeeCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14ecc)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14ecc retired x1 0x15ecc) false := by
  apply configuredAuipcStep stepNo state 0x14ecc 1 0x97 0x10 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x14ed0: jalr ra,-444(ra)`. -/
private theorem writeSuccessBaseFeeCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14ed0)
    (baseRead : state.regs.get? x1 = some 0x15ecc)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x14ed0 0x15d10 x1 0x14ed4)
        0x15d10 retired) false := by
  apply configuredJalrCallStep stepNo state 0x14ed0 0x15ecc 0xe44 0x15d10 0x14ed4
    0xe7 0x80 0x40 0xe4 configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x1572c: addi a0,sp,0x3e8`. -/
private theorem writeSuccessOutputBufferStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x1572c)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1572c retired x10
        (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x3e8))) false := by
  apply writeSuccessAddiX10FromSpStep stepNo 0x1572c 0x3e8 0x3e8
    0x13 0x05 0x81 0x3e state (args.stackPointer - 0x7d0) access.configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + sign_extend (0x3e8#12) = _
    rw [show sign_extend (m := 64) (0x3e8#12) = 0x3e8#64 by native_decide]
    rw [← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x15730: li a1,32`. -/
private theorem writeSuccessOutputLengthStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15730)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15730 retired x11 32) false := by
  apply writeSuccessAddiX11FromZeroStep stepNo 0x15730 32 32
    0x93 0x05 0x00 0x02 state configured atPc loaded
  · native_decide
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x15734: auipc ra,-5`. -/
private theorem writeSuccessOutputCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15734)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15734 retired x1 0x10734) false := by
  apply configuredAuipcStep stepNo state 0x15734 0xffffb 0x97 0xb0 0xff 0xff
    configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x15738: jalr ra,-0x5a4(ra)`, entering bare-metal `write_output`. -/
private theorem writeSuccessOutputCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15738)
    (baseRead : state.regs.get? x1 = some 0x10734)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x15738 0x10190 x1 0x1573c)
        0x10190 retired) false := by
  apply configuredJalrCallStep stepNo state 0x15738 0x10734 0xa5c 0x10190 0x1573c
    0xe7 0x80 0xc0 0xa5 configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x1573c: ld s1,0x388(sp)`. -/
private theorem writeSuccessHashesAddressLoadStep (stepNo address : Nat)
    (args : WriteSuccessArgs) (state : State)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x1573c)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x388) address)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1573c retired x9 (BitVec.ofNat 64 address)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x1573c 0x388 address args state
    (.Regidx 9#5) x9 (BitVec.ofNat 64 address) 0x388 0x83 0x34 0x81 0x38
    access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x388#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x9_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x15740: ld s0,0x390(sp)`. -/
private theorem writeSuccessHashesCountLoadStep (stepNo count : Nat)
    (args : WriteSuccessArgs) (state : State)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x15740)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x390) count)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15740 retired x8 (BitVec.ofNat 64 count)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x15740 0x390 count args state
    (.Regidx 8#5) x8 (BitVec.ofNat 64 count) 0x390 0x03 0x34 0x01 0x39
    access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x390#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x8_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

set_option genInjectivity false in
/-- State after the first shared integer encoder call, for payload block number. -/
structure WriteSuccessFirstIntHandoff
    (fromStep prefixUsed parentHashUsed feeUsed stateUsed receiptsUsed logsUsed prevUsed intUsed : Nat)
    (args : WriteSuccessArgs) (before after : EndpointState)
    (values : DecodeCalleeSavedValues) (bytes : Array UInt8) (tailValues : Fin 16 → Nat) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep
    (prefixUsed + parentHashUsed + feeUsed + stateUsed + receiptsUsed + logsUsed + prevUsed +
      3 + intUsed) before after
  atPc : EndpointPc after = some 0x14e94
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ successPrefixBytes ++
    args.decoded.payload.parentHash ++ args.decoded.payload.feeRecipient ++
    args.decoded.payload.stateRoot ++ args.decoded.payload.receiptsRoot ++
    args.decoded.payload.logsBloom ++ args.decoded.payload.prevRandao ++
    encodeNatLE 8 args.decoded.payload.blockNumber
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  destinationRep : BytesRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) bytes
  parentRootRep : BytesRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x3e8) args.decoded.parentBeaconBlockRoot
  versionedHashesRelocation : ByteWindowRelocation after.machine.mem after.machine.mem
    (args.decodedAddress + 592) (args.stackPointer - 0x7d0 + 0x388) 16
  bytesSize : bytes.size = 0x250
  sourceRep : BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes
  fullCopy : ∃ fullBytes : Array UInt8, fullBytes.size = 720 ∧
    BytesRep after.machine.mem args.decodedAddress fullBytes ∧
    BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) fullBytes
  tailReps : ∀ index (inBounds : index < 16),
    UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
      (tailValues ⟨index, inBounds⟩)
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  slotWord : ∃ value, UIntRep 8 after.machine.mem
    (args.stackPointer - 0x7d0 + 0x480) value
  slotTagWord : ∃ value, UIntRep 8 after.machine.mem
    (args.stackPointer - 0x7d0 + 0x488) value
  localTailReps : WriteSuccessLocalTailReps args after
  linkedTailReps : WriteSuccessLinkedTailReps args after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memoryFrame : WriteSuccessMemoryFrame args before.machine after.machine
  payloadRep : ExecutionPayloadRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  decodedBytesRep : BytesRep after.machine.mem args.decodedAddress bytes
  stable : StatelessInputRepStableOutside (writeSuccessMemoryRegion args)
    after.machine.mem args.decodedAddress args.decoded

/-- Compose `ld; auipc; jalr` and the first selected shared integer encoder. -/
theorem writeSuccessFirstIntHandoff
    (prefixChild : WriteSuccessPrefixInstanceContract)
    (parentHash : WriteSuccessParentHashInstanceContract)
    (feeRecipient : WriteSuccessFeeRecipientInstanceContract)
    (stateRoot : WriteSuccessStateRootInstanceContract)
    (receiptsRoot : WriteSuccessReceiptsRootInstanceContract)
    (logsBloom : WriteSuccessLogsBloomInstanceContract)
    (prevRandao : WriteSuccessPrevRandaoInstanceContract)
    (intChild : WriteSuccessIntInstanceContract)
    (fromStep : Nat) (args : WriteSuccessArgs) (state : EndpointState)
    (entry : WriteSuccessEntry args state) :
    ∃ values bytes, ∃ tailValues : Fin 16 → Nat,
      ∃ parentUsed prefixUsed memcpyUsed parentHashUsed feeUsed stateUsed receiptsUsed logsUsed
        prevUsed intUsed after,
        WriteSuccessFirstIntHandoff fromStep
          (20 + parentUsed + 32 + prefixUsed + 5 + memcpyUsed + 1)
          (parentHashUsed + 1) (feeUsed + 1) (stateUsed + 1) (receiptsUsed + 1)
          (logsUsed + 1) prevUsed intUsed args state after values bytes tailValues := by
  obtain ⟨values, bytes, tailValues, parentUsed, prefixUsed, memcpyUsed, parentHashUsed,
    feeUsed, stateUsed, receiptsUsed, logsUsed, prevUsed, before, handoff⟩ :=
    writeSuccessSixRawFieldsHandoff prefixChild parentHash feeRecipient stateRoot receiptsRoot
      logsBloom prevRandao fromStep args state entry
  have aligned : args.stackPointer % 16 = 0 := entry.2.2.1
  have lower : 0x880 ≤ args.stackPointer := entry.2.1
  have fits : args.stackPointer < 2 ^ 64 := entry.2.2.2.1
  let startStep := fromStep +
    (20 + parentUsed + 32 + prefixUsed + 5 + memcpyUsed + 1 +
      (parentHashUsed + 1 + feeUsed + 1 + stateUsed + 1) +
      (receiptsUsed + 1 + logsUsed + 1 + prevUsed))
  have atPc : before.machine.regs.get? PC = some 0x14e88 := by
    simpa [EndpointPc, MachinePc] using handoff.atPc
  have seg0 : Seg writeSuccessParentPc writeSuccessFirstIntExitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      startStep 0 before.machine before.machine 0x14e88 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := handoff.access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact handoff.stack }
  obtain ⟨retired0, run0⟩ := writeSuccessBlockNumberLoadStep _ args before.machine
    handoff.access atPc handoff.stack handoff.payloadRep.1 aligned handoff.loaded
  have seg1 := seg0.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessFirstIntExitPc; native_decide) x10
    (BitVec.ofNat 64 args.decoded.payload.blockNumber) 0x14e8c
    retired0 run0 (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg handoff.access seg1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite before.machine 0x14e88 retired0 x10
        (BitVec.ofNat 64 args.decoded.payload.blockNumber)).mem := by
    simpa [seg1.memEq (by simp)] using handoff.loaded
  obtain ⟨baseMachine, seg2⟩ := seg1.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessFirstIntExitPc; native_decide) x1 0x15e8c 0x14e90
    (writeSuccessFirstIntCallBaseStep _ _ access1.configured seg1.atPc loaded1)
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg handoff.access seg2
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully baseMachine.mem := by
    simpa [seg2.memEq (by simp)] using handoff.loaded
  obtain ⟨retired2, callRun⟩ := writeSuccessFirstIntCallStep _ baseMachine
    access2.configured seg2.atPc (seg2.reg x1 0x15e8c (by simp)) loaded2
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement baseMachine) 0x14e90 0x15d10 x1 0x14e94)
    0x15d10 retired2
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes baseMachine 0x14e90 0x15d10 retired2 x1 0x14e94
  have callAtPc : callMachine.regs.get? PC = some 0x15d10 := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callBaseMemEq : callMachine.mem = baseMachine.mem := by
    change
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement baseMachine) 0x14e90 0x15d10 x1 0x14e94)
        0x15d10 retired2).mem = baseMachine.mem
    rw [tryStepControlFlowAfterRetired_mem]
    change
      (controlFlowJumpState (tryStepControlFlowAfterIncrement baseMachine) 0x14e90 0x15d10).mem =
        baseMachine.mem
    rw [controlFlowJumpState_mem]
    rfl
  have callMemEq : callMachine.mem = before.machine.mem :=
    callBaseMemEq.trans (seg2.memEq (by simp))
  let childArgs : EncoderCallArgs Nat :=
    { returnAddress := 0x14e94
      callerStack := args.stackPointer - 0x7d0
      inputSize := args.inputSize
      value := args.decoded.payload.blockNumber }
  have childEntry : EncoderCallEntry Elflings.writeSuccessIntEntry
      Elflings.writeSuccessIntExitPcs UInt64EncoderBinding childArgs callState := by
    refine ⟨(by show 0x14e94 ∈ Elflings.writeSuccessIntExitPcs; native_decide),
      (by dsimp [childArgs]; omega), ?_, ?_, ?_, ?_, ?_⟩
    · simpa [callState] using callAtPc
    · simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, childArgs]
    · exact (callWrites.get x2 (by decide)).trans
        (seg2.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    · exact ⟨handoff.payloadRep.1.1, (callWrites.get x10 (by decide)).trans
        (seg2.reg x10 (BitVec.ofNat 64 args.decoded.payload.blockNumber) (by simp))⟩
    · simpa [callState, callMemEq] using handoff.loaded
  obtain ⟨intBound, intImpl⟩ := intChild
  obtain ⟨intUsed, after, unit, positive, bounded, childTrace, childPc, allowed, childExit⟩ :=
    intImpl childArgs (startStep + 3) callState childEntry
  rcases childExit with ⟨afterPc, stdout, stdin, cursor, exitCode, frameFits, childMem, childFrame⟩
  have callPrefix : ConfinedPrefix writeSuccessParentPc writeSuccessFirstIntExitPc
      (fun _ _ _ _ _ => False) (startStep + 2) 1 baseMachine callMachine :=
    ConfinedPrefix.ownStep seg2.atPc
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessFirstIntExitPc; native_decide) callRun
  have callEnd : ScopedTrace writeSuccessParentPc writeSuccessFirstIntExitPc
      (fun _ _ _ _ _ => False) (startStep + 3) 0 callMachine callMachine :=
    .exitAt _ _ 0x15d10 callAtPc (Or.inl rfl)
  have parentMachineTrace := seg2.confined.trans callPrefix 0 callMachine callEnd
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) startStep 3 before callState := by
    simpa [callState] using liftWriteSuccessParentTrace before parentMachineTrace
  have childTrace' := childTrace.weaken (fun _ inside =>
    show pcInRanges Elflings.writeSuccessExecutionPcRanges _ from by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lo, hi⟩
      simp only [Elflings.writeSuccessIntExecutionPcRanges, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · simp at member
        subst range
        exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, hi⟩)
  have writerChildMem : WriteSuccessMemoryFrame args callMachine after.machine :=
    childMem.mono (by
      intro address inside
      dsimp [childArgs] at inside
      unfold writeSuccessFrameMemory
      exact writeSuccessChildFrame_mem_frame lower inside)
  have beforeCallMemory : WriteSuccessMemoryFrame args before.machine callMachine := by
    intro address outside
    rw [callMemEq]
  have callMemoryFrame : WriteSuccessMemoryFrame args before.machine after.machine :=
    WritesOnlyWithin.trans_same beforeCallMemory writerChildMem
  have fullMemory := WritesOnlyWithin.trans_same handoff.memoryFrame
    (WritesOnlyWithin.trans_same beforeCallMemory writerChildMem)
  have stableAfter := handoff.stable.afterWrites
    (callMemoryFrame.mono (fun _ inside => Or.inl inside))
  have decodedAfter := stableAfter.of_writesOnlyWithin (fun _ _ => rfl)
  have destinationAtCall := handoff.destinationRep.of_mem_eq callMemEq
  have destinationAfter := destinationAtCall.of_writesOnlyWithin childMem (by
      intro index inBounds inside
      dsimp [childArgs] at inside
      unfold byteRange at inside
      omega)
  have parentRootAtCall := handoff.parentRootRep.of_mem_eq callMemEq
  have parentRootAfter := parentRootAtCall.of_writesOnlyWithin childMem (by
      intro index inBounds inside
      dsimp [childArgs] at inside
      unfold byteRange at inside
      omega)
  have decodedBytesAtCall := handoff.decodedBytesRep.of_mem_eq callMemEq
  have decodedBytesAfter := decodedBytesAtCall.of_writesOnlyWithin childMem (by
      intro index inBounds inside
      dsimp [childArgs] at inside
      unfold byteRange at inside
      have decodedEq := entry.2.2.2.2.1
      rw [decodedEq] at inside
      omega)
  have versionedHashesAfter : ByteWindowRelocation after.machine.mem after.machine.mem
      (args.decodedAddress + 592) (args.stackPointer - 0x7d0 + 0x388) 16 := by
    intro index inBounds
    rw [childMem _ (by
      intro inside
      dsimp [childArgs] at inside
      unfold byteRange at inside
      omega), childMem _ (by
      intro inside
      dsimp [childArgs] at inside
      unfold byteRange at inside
      have decodedEq := entry.2.2.2.2.1
      rw [decodedEq] at inside
      omega), callMemEq, handoff.versionedHashesRelocation index inBounds]
  have payloadAfter : ExecutionPayloadRep after.machine.mem
      (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload := by
    apply decodedAfter.2.1.rebase (by omega)
    have relocation := ByteWindowRelocation.of_same_bytes decodedBytesAfter destinationAfter
    simpa [handoff.bytesSize] using relocation
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have pmaEq := (childFrame.1 pma_regions (by simp [abiCalleePreserved])).trans callPmaEq
  have accessAfter : WriteSuccessMachineAccess args after.machine :=
    { configured := configuredAfterEndpointCall
        (configuredAfterWriteSuccessCall 0x14e90 0x15d10 0x14e94 retired2 access2.configured)
        childFrame
      frameLoad := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access2.frameLoad offset width bound)
      frameStore := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access2.frameStore offset width bound)
      frameNoMMIO := access2.frameNoMMIO
      decodedLoad := fun offset width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access2.decodedLoad offset width bound)
      decodedNoMMIO := access2.decodedNoMMIO
      outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq access2.outputBufferStore
      outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq access2.outputLengthStore
      writerRegionBeforeOutputContext := access2.writerRegionBeforeOutputContext
      frameNotCode := access2.frameNotCode }
  have sourceAtCall := handoff.sourceRep.of_mem_eq callMemEq
  have sourceAfter := sourceAtCall.of_writesOnlyWithin childMem (by
    intro index inBounds inside
    dsimp [childArgs] at inside
    unfold byteRange at inside
    omega)
  have tailAfter : ∀ index (bound : index < 16),
      UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
        (tailValues ⟨index, bound⟩) := by
    intro index bound
    have atCall := (handoff.tailReps index bound).of_mem_eq callMemEq
    exact atCall.of_writesOnlyWithin childMem (by
      intro byte byteBound inside
      dsimp [childArgs] at inside
      unfold byteRange at inside
      have decodedEq := entry.2.2.2.2.1
      rw [decodedEq] at inside
      omega)
  have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
    intro word member
    have atCall := (handoff.saved word member).of_mem_eq callMemEq
    exact atCall.of_writesOnlyWithin childMem (by
      intro index bound inside
      dsimp [childArgs] at inside
      unfold byteRange at inside
      have wordLower : args.stackPointer - 0x7d0 + 0x768 ≤ word.1 := by
        simp [writeSuccessSavedWords] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> omega
      omega)
  obtain ⟨slotValue, slotRep⟩ := handoff.slotWord
  have slotAfter : UIntRep 8 after.machine.mem
      (args.stackPointer - 0x7d0 + 0x480) slotValue :=
    (slotRep.of_mem_eq callMemEq).of_writesOnlyWithin childMem (by
      intro index bound inside
      dsimp [childArgs] at inside
      unfold byteRange at inside
      omega)
  obtain ⟨slotTagValue, slotTagRep⟩ := handoff.slotTagWord
  have slotTagAfter : UIntRep 8 after.machine.mem
      (args.stackPointer - 0x7d0 + 0x488) slotTagValue :=
    (slotTagRep.of_mem_eq callMemEq).of_writesOnlyWithin childMem (by
      intro index bound inside
      dsimp [childArgs] at inside
      unfold byteRange at inside
      omega)
  obtain ⟨localValues, localReps⟩ := handoff.localTailReps
  have localAfter : WriteSuccessLocalTailReps args after := ⟨localValues, by
    intro word member
    have atCall := (localReps word member).of_mem_eq callMemEq
    exact atCall.of_writesOnlyWithin childMem (by
      intro index bound inside
      dsimp [childArgs] at inside
      unfold byteRange at inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega)⟩
  obtain ⟨linkedValues, linkedLocal, linkedSource⟩ := handoff.linkedTailReps
  have linkedLocalAfter : InlineEncoderSavedWords after.machine.mem
      (writeSuccessLocalTailWords args linkedValues) := by
    intro word member
    have atCall := (linkedLocal word member).of_mem_eq callMemEq
    exact atCall.of_writesOnlyWithin childMem (by
      intro index bound inside
      dsimp [childArgs] at inside
      unfold byteRange at inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  have linkedSourceAfter : ∀ index (bound : index < 16),
      UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
        (linkedValues ⟨index, bound⟩) := by
    intro index bound
    have atCall := (linkedSource index bound).of_mem_eq callMemEq
    exact atCall.of_writesOnlyWithin childMem (by
      intro byte byteBound inside
      dsimp [childArgs] at inside
      unfold byteRange at inside
      have decodedEq := entry.2.2.2.2.1
      rw [decodedEq] at inside
      omega)
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem := by
    intro address byte fileByte
    have outside : ¬byteRange (childArgs.callerStack - 16) 16 address := by
      intro inside
      dsimp [childArgs] at inside
      have inWriter := writeSuccessChildFrame_mem_frame lower inside
      unfold byteRange at inWriter
      rw [Nat.sub_add_cancel lower] at inWriter
      have notCode := access2.frameNotCode address inWriter.1 inWriter.2
      exact Option.some_ne_none byte (fileByte.symm.trans notCode)
    rw [childMem address outside]
    exact loaded2 address byte fileByte
  refine ⟨values, bytes, tailValues, parentUsed, prefixUsed, memcpyUsed, parentHashUsed,
    feeUsed, stateUsed, receiptsUsed, logsUsed, prevUsed, intUsed, after, {
      trace := ?_
      atPc := afterPc
      stack := (childFrame.1 x2 (by simp [abiCalleePreserved])).trans
        ((callWrites.get x2 (by decide)).trans
          (seg2.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)))
      stdout := ?_
      stdin := stdin.trans (by simpa [callState] using handoff.stdin)
      cursor := cursor.trans (by simpa [callState] using handoff.cursor)
      exitCode := exitCode.trans (by simpa [callState] using handoff.exitCode)
      destinationRep := destinationAfter
      parentRootRep := parentRootAfter
      versionedHashesRelocation := versionedHashesAfter
      bytesSize := handoff.bytesSize
      sourceRep := sourceAfter
      fullCopy := by
        obtain ⟨fullBytes, fullSize, decodedRep, fullRep⟩ := handoff.fullCopy
        have decodedAtCall := decodedRep.of_mem_eq callMemEq
        have decodedAfter := decodedAtCall.of_writesOnlyWithin childMem (by
          intro index inBounds inside
          dsimp [childArgs] at inside
          unfold byteRange at inside
          have decodedEq := entry.2.2.2.2.1
          rw [decodedEq] at inside
          rw [fullSize] at inBounds
          omega)
        exact ⟨fullBytes, fullSize, decodedAfter,
          fullRep.of_mem_eq callMemEq |>.of_writesOnlyWithin childMem (by
          intro index inBounds inside
          dsimp [childArgs] at inside
          unfold byteRange at inside
          rw [fullSize] at inBounds
          omega)⟩
      tailReps := tailAfter
      saved := savedAfter
      slotWord := ⟨slotValue, slotAfter⟩
      slotTagWord := ⟨slotTagValue, slotTagAfter⟩
      localTailReps := localAfter
      linkedTailReps := ⟨linkedValues, linkedLocalAfter, linkedSourceAfter⟩
      loaded := loadedAfter
      access := accessAfter
      memoryFrame := fullMemory
      payloadRep := payloadAfter
      decodedBytesRep := decodedBytesAfter
      stable := stableAfter }⟩
  · have combined := handoff.trace.append (by simpa [startStep, Nat.add_assoc] using parentTrace)
    have all := combined.append (by simpa [startStep, Nat.add_assoc] using childTrace')
    simpa [startStep, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using all
  · calc
      after.stdout = callState.stdout ++ encodeNatLE 8 args.decoded.payload.blockNumber := stdout
      _ = before.stdout ++ encodeNatLE 8 args.decoded.payload.blockNumber := rfl
      _ = state.stdout ++ successPrefixBytes ++ args.decoded.payload.parentHash ++
          args.decoded.payload.feeRecipient ++ args.decoded.payload.stateRoot ++
          args.decoded.payload.receiptsRoot ++ args.decoded.payload.logsBloom ++
          args.decoded.payload.prevRandao ++ encodeNatLE 8 args.decoded.payload.blockNumber := by
        rw [handoff.stdout]

set_option genInjectivity false in
/-- Reusable result of one parent `ld; auipc; jalr` sequence and the shared integer child. -/
structure WriteSuccessIntCallHandoff
    (fromStep childUsed returnPc value : Nat) (args : WriteSuccessArgs)
    (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (3 + childUsed) before after
  atPc : EndpointPc after = some (BitVec.ofNat 64 returnPc)
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeNatLE 8 value
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : WritesOnlyWithin
    (byteRange (args.stackPointer - 0x7d0 - 16) 16) before.machine after.machine
  x8 : after.machine.regs.get? x8 = before.machine.regs.get? x8
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine

private def writeSuccessIntParentWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x1 ∨ register = x10

set_option genInjectivity false in
/-- Payload bytes and semantics retained while shared encoder calls use their child stack frames. -/
structure WriteSuccessPayloadContext (args : WriteSuccessArgs) (bytes : Array UInt8)
    (state : EndpointState) : Prop where
  fullCopy : ∃ fullBytes : Array UInt8, fullBytes.size = 720 ∧
    BytesRep state.machine.mem args.decodedAddress fullBytes ∧
    BytesRep state.machine.mem (args.stackPointer - 0x7d0 + 0x138) fullBytes
  destinationRep : BytesRep state.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) bytes
  parentRootRep : BytesRep state.machine.mem
    (args.stackPointer - 0x7d0 + 0x3e8) args.decoded.parentBeaconBlockRoot
  decodedBytesRep : BytesRep state.machine.mem args.decodedAddress bytes
  versionedHashesRelocation : ByteWindowRelocation state.machine.mem state.machine.mem
    (args.decodedAddress + 592) (args.stackPointer - 0x7d0 + 0x388) 16
  bytesSize : bytes.size = 0x250
  stable : StatelessInputRepStableOutside (writeSuccessMemoryRegion args)
    state.machine.mem args.decodedAddress args.decoded
  payloadRep : ExecutionPayloadRep state.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  slotWord : ∃ value, UIntRep 8 state.machine.mem
    (args.stackPointer - 0x7d0 + 0x480) value
  slotTagWord : ∃ value, UIntRep 8 state.machine.mem
    (args.stackPointer - 0x7d0 + 0x488) value
  localTailReps : WriteSuccessLocalTailReps args state
  linkedTailReps : WriteSuccessLinkedTailReps args state

/-- Repackage the first integer handoff as the payload context consumed by every later encoder. -/
private theorem WriteSuccessFirstIntHandoff.payloadContext
    {fromStep prefixUsed parentHashUsed feeUsed stateUsed receiptsUsed logsUsed prevUsed intUsed : Nat}
    {args : WriteSuccessArgs} {before after : EndpointState}
    {values : DecodeCalleeSavedValues} {bytes : Array UInt8} {tailValues : Fin 16 → Nat}
    (handoff : WriteSuccessFirstIntHandoff fromStep prefixUsed parentHashUsed feeUsed stateUsed
      receiptsUsed logsUsed prevUsed intUsed args before after values bytes tailValues) :
    WriteSuccessPayloadContext args bytes after := {
  fullCopy := handoff.fullCopy
  destinationRep := handoff.destinationRep
  parentRootRep := handoff.parentRootRep
  decodedBytesRep := handoff.decodedBytesRep
  versionedHashesRelocation := handoff.versionedHashesRelocation
  bytesSize := handoff.bytesSize
  stable := handoff.stable
  payloadRep := handoff.payloadRep
  slotWord := handoff.slotWord
  slotTagWord := handoff.slotTagWord
  localTailReps := handoff.localTailReps
  linkedTailReps := handoff.linkedTailReps }

/-- The first 720-byte copy carries the five execution-request descriptors verbatim. -/
private theorem WriteSuccessPayloadContext.executionRequestsRep
    {args : WriteSuccessArgs} {bytes : Array UInt8} {state : EndpointState}
    (context : WriteSuccessPayloadContext args bytes state)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20)
    (upper : args.stackPointer < 2 ^ 64) :
    ExecutionRequestsRep state.machine.mem
      (args.stackPointer - 0x7d0 + 0x398) args.decoded.executionRequests := by
  obtain ⟨fullBytes, fullSize, decodedBytes, copiedBytes⟩ := context.fullCopy
  have relocation := ByteWindowRelocation.of_same_bytes decodedBytes copiedBytes
  have decoded := context.stable state.machine.mem (fun _ _ => rfl)
  obtain ⟨deposits, withdrawals, consolidations, builderDeposits, builderExits⟩ :=
    decoded.2.2.2.1
  refine ⟨deposits.rebaseDescriptor (by omega) ?_,
    withdrawals.rebaseDescriptor (by omega) ?_,
    consolidations.rebaseDescriptor (by omega) ?_,
    builderDeposits.rebaseDescriptor (by omega) ?_,
    builderExits.rebaseDescriptor (by omega) ?_⟩
  · simpa [decodedAddress, Nat.add_assoc] using relocation.atOffset 608 16 (by
      rw [fullSize]; omega)
  · simpa [decodedAddress, Nat.add_assoc] using relocation.atOffset 624 16 (by
      rw [fullSize]; omega)
  · simpa [decodedAddress, Nat.add_assoc] using relocation.atOffset 640 16 (by
      rw [fullSize]; omega)
  · simpa [decodedAddress, Nat.add_assoc] using relocation.atOffset 656 16 (by
      rw [fullSize]; omega)
  · simpa [decodedAddress, Nat.add_assoc] using relocation.atOffset 672 16 (by
      rw [fullSize]; omega)

/-- A slice whose optimized pointer and count words occupy independently selected stack slots. -/
private def WriteSuccessSeparatedSliceRep (stride : Nat)
    (elementRep : Std.ExtHashMap Nat (BitVec 8) → Nat → α → Prop)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (addressSlot lengthSlot : Nat)
    (values : Array α) : Prop :=
  ∃ data : Nat,
    UIntRep 8 mem addressSlot data ∧
    UIntRep 8 mem lengthSlot values.size ∧
    ArrayRep stride elementRep mem data values

/-- An optional byte slice whose optimized pointer and count use separate stack slots. -/
private def WriteSuccessSeparatedOptionalByteSliceRep
    (mem : Std.ExtHashMap Nat (BitVec 8)) (addressSlot lengthSlot : Nat) :
    Option (Array UInt8) → Prop
  | none => UIntRep 8 mem addressSlot 0
  | some bytes => ∃ data : Nat,
      data ≠ 0 ∧ UIntRep 8 mem addressSlot data ∧
      UIntRep 8 mem lengthSlot bytes.size ∧
      ArrayRep 1 (fun mem address byte => UIntRep 1 mem address byte.toNat) mem data bytes

/-- The linked tail stores materialize the witness-nodes pointer/count in reversed local slots. -/
private theorem WriteSuccessPayloadContext.witnessNodesRep
    {args : WriteSuccessArgs} {bytes : Array UInt8} {state : EndpointState}
    (context : WriteSuccessPayloadContext args bytes state) :
    WriteSuccessSeparatedSliceRep 16 ByteSliceRep state.machine.mem
      (args.stackPointer - 0x7d0 + 0x18) (args.stackPointer - 0x7d0 + 0x10)
      args.decoded.witnessNodes := by
  have decoded := context.stable state.machine.mem (fun _ _ => rfl)
  obtain ⟨address, addressRep, countRep, arrayRep⟩ := decoded.2.2.2.2.2.2.1
  obtain ⟨values, localReps, source⟩ := context.linkedTailReps
  have addressEq : values ⟨0, by omega⟩ = address :=
    WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) addressRep
  have countEq : values ⟨1, by omega⟩ = args.decoded.witnessNodes.size :=
    WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) countRep
  have localAddress := writeSuccessLocalTailRep localReps 0 (by omega)
  have localCount := writeSuccessLocalTailRep localReps 1 (by omega)
  rw [addressEq] at localAddress
  rw [countEq] at localCount
  refine ⟨address, ?_, ?_, arrayRep⟩
  · simpa [writeSuccessLocalTailOffset] using localAddress
  · simpa [writeSuccessLocalTailOffset] using localCount

/-- The linked tail stores materialize the witness-codes pointer/count in reversed local slots. -/
private theorem WriteSuccessPayloadContext.witnessCodesRep
    {args : WriteSuccessArgs} {bytes : Array UInt8} {state : EndpointState}
    (context : WriteSuccessPayloadContext args bytes state) :
    WriteSuccessSeparatedSliceRep 16 ByteSliceRep state.machine.mem
      (args.stackPointer - 0x7d0 + 0x28) (args.stackPointer - 0x7d0 + 0x20)
      args.decoded.witnessCodes := by
  have decoded := context.stable state.machine.mem (fun _ _ => rfl)
  obtain ⟨address, addressRep, countRep, arrayRep⟩ := decoded.2.2.2.2.2.2.2.1
  obtain ⟨values, localReps, source⟩ := context.linkedTailReps
  have addressEq : values ⟨2, by omega⟩ = address :=
    WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) addressRep
  have countEq : values ⟨3, by omega⟩ = args.decoded.witnessCodes.size :=
    WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) countRep
  have localAddress := writeSuccessLocalTailRep localReps 2 (by omega)
  have localCount := writeSuccessLocalTailRep localReps 3 (by omega)
  rw [addressEq] at localAddress
  rw [countEq] at localCount
  refine ⟨address, ?_, ?_, arrayRep⟩
  · simpa [writeSuccessLocalTailOffset] using localAddress
  · simpa [writeSuccessLocalTailOffset] using localCount

/-- The linked tail stores materialize the witness-headers pointer/count in reversed local slots. -/
private theorem WriteSuccessPayloadContext.witnessHeadersRep
    {args : WriteSuccessArgs} {bytes : Array UInt8} {state : EndpointState}
    (context : WriteSuccessPayloadContext args bytes state) :
    WriteSuccessSeparatedSliceRep 16 ByteSliceRep state.machine.mem
      (args.stackPointer - 0x7d0 + 0x38) (args.stackPointer - 0x7d0 + 0x30)
      args.decoded.witnessHeaders := by
  have decoded := context.stable state.machine.mem (fun _ _ => rfl)
  obtain ⟨address, addressRep, countRep, arrayRep⟩ := decoded.2.2.2.2.2.2.2.2.1
  obtain ⟨values, localReps, source⟩ := context.linkedTailReps
  have addressEq : values ⟨4, by omega⟩ = address :=
    WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) addressRep
  have countEq : values ⟨5, by omega⟩ = args.decoded.witnessHeaders.size :=
    WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) countRep
  have localAddress := writeSuccessLocalTailRep localReps 4 (by omega)
  have localCount := writeSuccessLocalTailRep localReps 5 (by omega)
  rw [addressEq] at localAddress
  rw [countEq] at localCount
  refine ⟨address, ?_, ?_, arrayRep⟩
  · simpa [writeSuccessLocalTailOffset] using localAddress
  · simpa [writeSuccessLocalTailOffset] using localCount

/-- The linked tail store at `sp+0x40` is the semantic chain ID. -/
private theorem WriteSuccessPayloadContext.chainIdRep
    {args : WriteSuccessArgs} {bytes : Array UInt8} {state : EndpointState}
    (context : WriteSuccessPayloadContext args bytes state) :
    UIntRep 8 state.machine.mem (args.stackPointer - 0x7d0 + 0x40)
      args.decoded.chainConfig.chainId := by
  have decoded := context.stable state.machine.mem (fun _ _ => rfl)
  have semantic := decoded.2.2.2.2.2.2.2.2.2.1.1
  obtain ⟨values, localReps, source⟩ := context.linkedTailReps
  have valueEq : values ⟨6, by omega⟩ = args.decoded.chainConfig.chainId :=
    WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) semantic
  have localValue := writeSuccessLocalTailRep localReps 6 (by omega)
  rw [valueEq] at localValue
  simpa [writeSuccessLocalTailOffset] using localValue

/-- The linked tail words at `sp+0x48` and `sp+0x08` retain the optional fork name. -/
private theorem WriteSuccessPayloadContext.forkNameRep
    {args : WriteSuccessArgs} {bytes : Array UInt8} {state : EndpointState}
    (context : WriteSuccessPayloadContext args bytes state) :
    WriteSuccessSeparatedOptionalByteSliceRep state.machine.mem
      (args.stackPointer - 0x7d0 + 0x48) (args.stackPointer - 0x7d0 + 0x08)
      args.decoded.chainConfig.forkName := by
  have decoded := context.stable state.machine.mem (fun _ _ => rfl)
  have semantic := decoded.2.2.2.2.2.2.2.2.2.1.2.1
  obtain ⟨values, localReps, source⟩ := context.linkedTailReps
  cases optionEq : args.decoded.chainConfig.forkName with
  | none =>
      rw [optionEq] at semantic
      have addressEq : values ⟨7, by omega⟩ = 0 :=
        WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) semantic
      have localAddress := writeSuccessLocalTailRep localReps 7 (by omega)
      rw [addressEq] at localAddress
      simpa [WriteSuccessSeparatedOptionalByteSliceRep, writeSuccessLocalTailOffset] using
        localAddress
  | some forkName =>
      rw [optionEq] at semantic
      obtain ⟨address, nonzero, addressRep, countRep, arrayRep⟩ := semantic
      have addressEq : values ⟨7, by omega⟩ = address :=
        WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) addressRep
      have countEq : values ⟨8, by omega⟩ = forkName.size :=
        WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) countRep
      have localAddress := writeSuccessLocalTailRep localReps 7 (by omega)
      have localCount : UIntRep 8 state.machine.mem
          (args.stackPointer - 0x7d0 + 0x08) (values ⟨8, by omega⟩) := by
        apply localReps (_, _)
        simp [writeSuccessLocalTailWords]
      rw [addressEq] at localAddress
      rw [countEq] at localCount
      exact ⟨address, nonzero,
        by simpa [writeSuccessLocalTailOffset] using localAddress,
        localCount,
        arrayRep⟩

/-- The linked tail word at `sp+0x50` is the semantic active-fork index. -/
private theorem WriteSuccessPayloadContext.activeForkIndexRep
    {args : WriteSuccessArgs} {bytes : Array UInt8} {state : EndpointState}
    (context : WriteSuccessPayloadContext args bytes state) :
    UIntRep 8 state.machine.mem (args.stackPointer - 0x7d0 + 0x50)
      args.decoded.chainConfig.activeForkIndex := by
  have decoded := context.stable state.machine.mem (fun _ _ => rfl)
  have semantic := decoded.2.2.2.2.2.2.2.2.2.1.2.2.1
  obtain ⟨values, localReps, source⟩ := context.linkedTailReps
  have valueEq : values ⟨9, by omega⟩ = args.decoded.chainConfig.activeForkIndex :=
    WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) semantic
  have localValue := writeSuccessLocalTailRep localReps 9 (by omega)
  rw [valueEq] at localValue
  simpa [writeSuccessLocalTailOffset] using localValue

/-- The linked tail words at `sp+0x128` retain the optional activation block. -/
private theorem WriteSuccessPayloadContext.activationBlockRep
    {args : WriteSuccessArgs} {bytes : Array UInt8} {state : EndpointState}
    (context : WriteSuccessPayloadContext args bytes state) :
    OptionalUIntRep 8 state.machine.mem (args.stackPointer - 0x7d0 + 0x128)
      args.decoded.chainConfig.activationBlock := by
  have decoded := context.stable state.machine.mem (fun _ _ => rfl)
  have semantic := decoded.2.2.2.2.2.2.2.2.2.1.2.2.2.1
  obtain ⟨values, localReps, source⟩ := context.linkedTailReps
  cases optionEq : args.decoded.chainConfig.activationBlock with
  | none =>
      rw [optionEq] at semantic
      simpa [writeSuccessLocalTailOffset] using
        writeSuccessLocalTailTagRep localReps source 11 (by omega) semantic
  | some value =>
      rw [optionEq] at semantic
      refine ⟨?_, ?_⟩
      · have valueEq : values ⟨10, by omega⟩ = value :=
          WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) semantic.1
        have localValue := writeSuccessLocalTailRep localReps 10 (by omega)
        rw [valueEq] at localValue
        simpa [writeSuccessLocalTailOffset] using localValue
      · simpa [writeSuccessLocalTailOffset] using
          writeSuccessLocalTailTagRep localReps source 11 (by omega) semantic.2

/-- The linked tail words at `sp+0x118` retain the optional activation timestamp. -/
private theorem WriteSuccessPayloadContext.activationTimestampRep
    {args : WriteSuccessArgs} {bytes : Array UInt8} {state : EndpointState}
    (context : WriteSuccessPayloadContext args bytes state) :
    OptionalUIntRep 8 state.machine.mem (args.stackPointer - 0x7d0 + 0x118)
      args.decoded.chainConfig.activationTimestamp := by
  have decoded := context.stable state.machine.mem (fun _ _ => rfl)
  have semantic := decoded.2.2.2.2.2.2.2.2.2.1.2.2.2.2
  obtain ⟨values, localReps, source⟩ := context.linkedTailReps
  cases optionEq : args.decoded.chainConfig.activationTimestamp with
  | none =>
      rw [optionEq] at semantic
      simpa [writeSuccessLocalTailOffset] using
        writeSuccessLocalTailTagRep localReps source 13 (by omega) semantic
  | some value =>
      rw [optionEq] at semantic
      refine ⟨?_, ?_⟩
      · have valueEq : values ⟨12, by omega⟩ = value :=
          WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) semantic.1
        have localValue := writeSuccessLocalTailRep localReps 12 (by omega)
        rw [valueEq] at localValue
        simpa [writeSuccessLocalTailOffset] using localValue
      · simpa [writeSuccessLocalTailOffset] using
          writeSuccessLocalTailTagRep localReps source 13 (by omega) semantic.2

/-- The linked tail words at `sp+0x60` and `sp+0x58` retain the public-key slice. -/
private theorem WriteSuccessPayloadContext.publicKeysRep
    {args : WriteSuccessArgs} {bytes : Array UInt8} {state : EndpointState}
    (context : WriteSuccessPayloadContext args bytes state) :
    WriteSuccessSeparatedSliceRep 16 ByteSliceRep state.machine.mem
      (args.stackPointer - 0x7d0 + 0x60) (args.stackPointer - 0x7d0 + 0x58)
      args.decoded.publicKeys := by
  have decoded := context.stable state.machine.mem (fun _ _ => rfl)
  obtain ⟨address, addressRep, countRep, arrayRep⟩ := decoded.2.2.2.2.2.2.2.2.2.2
  obtain ⟨values, localReps, source⟩ := context.linkedTailReps
  have addressEq : values ⟨14, by omega⟩ = address :=
    WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) addressRep
  have countEq : values ⟨15, by omega⟩ = args.decoded.publicKeys.size :=
    WriteSuccessLinkedTailReps.value_eq ⟨localReps, source⟩ (by omega) countRep
  have localAddress := writeSuccessLocalTailRep localReps 14 (by omega)
  have localCount : UIntRep 8 state.machine.mem
      (args.stackPointer - 0x7d0 + 0x58) (values ⟨15, by omega⟩) := by
    apply localReps (_, _)
    simp [writeSuccessLocalTailWords]
  rw [addressEq] at localAddress
  rw [countEq] at localCount
  refine ⟨address, ?_, ?_, arrayRep⟩
  · simpa [writeSuccessLocalTailOffset] using localAddress
  · exact localCount

/-- Transport copied payload semantics through one exact child frame inside the writer frame. -/
private theorem writeSuccessPayloadContextAfterChild
    {args : WriteSuccessArgs} {bytes : Array UInt8} {before after : EndpointState}
    {childMemory : Region}
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20)
    (lower : 0x880 ≤ args.stackPointer) (upper : args.stackPointer < 2 ^ 64)
    (beforeContext : args.stackPointer + 0x380 ≤ Elflings.ioContextAddress)
    (context : WriteSuccessPayloadContext args bytes before)
    (memory : WritesOnlyWithin childMemory before.machine after.machine)
    (insideAllowed : ∀ address, childMemory address → writeSuccessMemoryRegion args address)
    (outsideFirstCopy : ∀ index, index < 720 →
      ¬childMemory (args.stackPointer - 0x7d0 + 0x138 + index))
    (outsideDestination : ∀ index, index < bytes.size →
      ¬childMemory (args.stackPointer - 0x7d0 + 0x408 + index))
    (outsideParentRoot : ∀ index, index < args.decoded.parentBeaconBlockRoot.size →
      ¬childMemory (args.stackPointer - 0x7d0 + 0x3e8 + index))
    (outsideDecoded : ∀ index, index < bytes.size →
      ¬childMemory (args.decodedAddress + index))
    (outsideDecodedHashes : ∀ index, index < 16 →
      ¬childMemory (args.decodedAddress + 592 + index))
    (outsideCopiedHashes : ∀ index, index < 16 →
      ¬childMemory (args.stackPointer - 0x7d0 + 0x388 + index))
    (outsideLocalTail : ∀ values word, word ∈ writeSuccessLocalTailWords args values →
      ∀ index, index < 8 → ¬childMemory (word.1 + index)) :
    WriteSuccessPayloadContext args bytes after := by
  have allowedMemory : WritesOnlyWithin (writeSuccessMemoryRegion args)
      before.machine after.machine := memory.mono insideAllowed
  have stableAfter := context.stable.afterWrites allowedMemory
  obtain ⟨fullBytes, fullSize, fullDecodedRep, fullCopyRep⟩ := context.fullCopy
  have fullDecodedAfter := fullDecodedRep.of_writesOnlyWithin allowedMemory (by
    intro index inBounds inside
    unfold writeSuccessMemoryRegion writeSuccessMemoryRegionAt Region.union byteRange at inside
    rw [decodedAddress] at inside
    rcases inside with inside | inside | inside <;> omega)
  have fullCopyAfter := fullCopyRep.of_writesOnlyWithin memory (by
    intro index inBounds
    exact outsideFirstCopy index (by simpa [fullSize] using inBounds))
  have destinationAfter := context.destinationRep.of_writesOnlyWithin memory outsideDestination
  have parentRootAfter :=
    context.parentRootRep.of_writesOnlyWithin memory outsideParentRoot
  have decodedBytesAfter := context.decodedBytesRep.of_writesOnlyWithin memory outsideDecoded
  have versionedHashesAfter : ByteWindowRelocation after.machine.mem after.machine.mem
      (args.decodedAddress + 592) (args.stackPointer - 0x7d0 + 0x388) 16 := by
    intro index inBounds
    rw [memory _ (outsideCopiedHashes index inBounds),
      context.versionedHashesRelocation index inBounds,
      memory _ (outsideDecodedHashes index inBounds)]
  obtain ⟨slotValue, slotRep⟩ := context.slotWord
  have slotAfter := slotRep.rebase (by omega)
    ((ByteWindowRelocation.of_same_bytes context.destinationRep destinationAfter).atOffset
      0x78 8 (by rw [context.bytesSize]; omega))
  obtain ⟨tagValue, tagRep⟩ := context.slotTagWord
  have tagAfter := tagRep.rebase (by omega)
    ((ByteWindowRelocation.of_same_bytes context.destinationRep destinationAfter).atOffset
      0x80 8 (by rw [context.bytesSize]; omega))
  obtain ⟨tailValues, tailReps⟩ := context.localTailReps
  have tailAfter : InlineEncoderSavedWords after.machine.mem
      (writeSuccessLocalTailWords args tailValues) := by
    intro word member
    exact (tailReps word member).of_writesOnlyWithin memory
      (outsideLocalTail tailValues word member)
  obtain ⟨linkedValues, linkedLocal, linkedSource⟩ := context.linkedTailReps
  have linkedLocalAfter : InlineEncoderSavedWords after.machine.mem
      (writeSuccessLocalTailWords args linkedValues) := by
    intro word member
    exact (linkedLocal word member).of_writesOnlyWithin memory
      (outsideLocalTail linkedValues word member)
  have linkedSourceAfter : ∀ index (bound : index < 16),
      UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
        (linkedValues ⟨index, bound⟩) := by
    intro index bound
    exact (linkedSource index bound).of_writesOnlyWithin allowedMemory (by
      intro byte byteBound inside
      unfold writeSuccessMemoryRegion writeSuccessMemoryRegionAt Region.union byteRange at inside
      rw [decodedAddress] at inside
      rcases inside with inside | inside | inside <;> omega)
  have decodedAfter := stableAfter.of_writesOnlyWithin (fun _ _ => rfl)
  have payloadAfter : ExecutionPayloadRep after.machine.mem
      (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload := by
    apply decodedAfter.2.1.rebase (by
      have := context.bytesSize
      omega)
    have relocation := ByteWindowRelocation.of_same_bytes decodedBytesAfter destinationAfter
    simpa [context.bytesSize] using relocation
  exact {
    fullCopy := ⟨fullBytes, fullSize, fullDecodedAfter, fullCopyAfter⟩
    destinationRep := destinationAfter
    parentRootRep := parentRootAfter
    decodedBytesRep := decodedBytesAfter
    versionedHashesRelocation := versionedHashesAfter
    bytesSize := context.bytesSize
    stable := stableAfter
    payloadRep := payloadAfter
    slotWord := ⟨slotValue, slotAfter⟩
    slotTagWord := ⟨tagValue, tagAfter⟩
    localTailReps := ⟨tailValues, tailAfter⟩
    linkedTailReps := ⟨linkedValues, linkedLocalAfter, linkedSourceAfter⟩ }

/-- Transport the copied payload and its heap references through one integer child frame. -/
private theorem writeSuccessPayloadContextAfterInt
    {fromStep childUsed returnPc value : Nat} {args : WriteSuccessArgs}
    {bytes : Array UInt8} {before after : EndpointState}
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20)
    (lower : 0x880 ≤ args.stackPointer) (upper : args.stackPointer < 2 ^ 64)
    (context : WriteSuccessPayloadContext args bytes before)
    (call : WriteSuccessIntCallHandoff fromStep childUsed returnPc value args before after) :
    WriteSuccessPayloadContext args bytes after := by
  apply writeSuccessPayloadContextAfterChild decodedAddress lower upper
    call.access.writerRegionBeforeOutputContext context call.memory
  · intro address inside
    exact Or.inl (writeSuccessChildFrame_mem_frame lower inside)
  all_goals
    first
    | intro values word member index inBounds inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> unfold byteRange at inside <;> omega
    | intro index inBounds inside
      unfold byteRange at inside
      try rw [decodedAddress] at inside
      omega

/-- Compose one exact parent integer-call setup with the selected shared integer contract. -/
private theorem writeSuccessIntCallHandoff
    (intChild : WriteSuccessIntInstanceContract)
    (fromStep pc returnPc offset value callBase : Nat)
    (args : WriteSuccessArgs) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 before.machine.mem (args.stackPointer - 0x7d0 + offset) value)
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (loadStep : ∀ stepNo state,
      WriteSuccessMachineAccess args state →
      state.regs.get? PC = some (BitVec.ofNat 64 pc) →
      state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) →
      UIntRep 8 state.mem (args.stackPointer - 0x7d0 + offset) value →
      args.stackPointer % 16 = 0 →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state pc retired x10 (BitVec.ofNat 64 value)) false)
    (baseStep : ∀ stepNo state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 (pc + 4)) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 (pc + 4)) retired x1
          (BitVec.ofNat 64 callBase)) false)
    (callStep : ∀ stepNo state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 (pc + 8)) →
      state.regs.get? x1 = some (BitVec.ofNat 64 callBase) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 (pc + 8)) 0x15d10 x1 returnPc)
          0x15d10 retired) false)
    (owned0 : writeSuccessParentPc (BitVec.ofNat 64 pc))
    (owned1 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 4)))
    (owned2 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 8)))
    (notExit0 : ¬writeSuccessIntCallExitPc (BitVec.ofNat 64 pc))
    (notExit1 : ¬writeSuccessIntCallExitPc (BitVec.ofNat 64 (pc + 4)))
    (notExit2 : ¬writeSuccessIntCallExitPc (BitVec.ofNat 64 (pc + 8)))
    (next0 : BitVec.ofNat 64 pc + 4 = BitVec.ofNat 64 (pc + 4))
    (next1 : BitVec.ofNat 64 (pc + 4) + 4 = BitVec.ofNat 64 (pc + 8))
    (returnListed : returnPc ∈ Elflings.writeSuccessIntExitPcs) :
    ∃ childUsed after,
      WriteSuccessIntCallHandoff fromStep childUsed returnPc value args before after := by
  have seg0 : Seg writeSuccessParentPc writeSuccessIntCallExitPc
      (fun _ _ _ _ _ => False) writeSuccessIntParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine (BitVec.ofNat 64 pc) := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  obtain ⟨retired0, run0⟩ := loadStep _ before.machine access atPc stack rep aligned loaded
  have seg1 := seg0.stepKnown owned0 notExit0 x10 (BitVec.ofNat 64 value)
    (BitVec.ofNat 64 (pc + 4)) retired0 run0 next0 (by intro r h; exact Or.inl h)
    (by simp [writeSuccessIntParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access (seg1.widenWrites (by
    intro register written
    rcases written with bookkeeping | rfl | rfl
    · exact Or.inl bookkeeping
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite before.machine pc retired0 x10 (BitVec.ofNat 64 value)).mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨baseMachine, seg2⟩ := seg1.step owned1 notExit1 x1
    (BitVec.ofNat 64 callBase) (BitVec.ofNat 64 (pc + 8))
    (baseStep _ _ access1.configured seg1.atPc loaded1)
    next1 (by intro r h; exact Or.inl h)
    (by simp [writeSuccessIntParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg access (seg2.widenWrites (by
    intro register written
    rcases written with bookkeeping | rfl | rfl
    · exact Or.inl bookkeeping
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully baseMachine.mem := by
    simpa [seg2.memEq (by simp)] using loaded
  obtain ⟨retired2, callRun⟩ := callStep _ baseMachine access2.configured seg2.atPc
    (seg2.reg x1 (BitVec.ofNat 64 callBase) (by simp)) loaded2
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement baseMachine) (BitVec.ofNat 64 (pc + 8))
      0x15d10 x1 returnPc)
    0x15d10 retired2
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes baseMachine (BitVec.ofNat 64 (pc + 8))
    0x15d10 retired2 x1 returnPc
  have callAtPc : callMachine.regs.get? PC = some 0x15d10 := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callBaseMemEq : callMachine.mem = baseMachine.mem := by
    change
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement baseMachine) (BitVec.ofNat 64 (pc + 8))
          0x15d10 x1 returnPc)
        0x15d10 retired2).mem = baseMachine.mem
    rw [tryStepControlFlowAfterRetired_mem]
    change
      (controlFlowJumpState (tryStepControlFlowAfterIncrement baseMachine)
        (BitVec.ofNat 64 (pc + 8)) 0x15d10).mem =
        baseMachine.mem
    rw [controlFlowJumpState_mem]
    rfl
  have callMemEq : callMachine.mem = before.machine.mem :=
    callBaseMemEq.trans (seg2.memEq (by simp))
  let childArgs : EncoderCallArgs Nat :=
    { returnAddress := returnPc
      callerStack := args.stackPointer - 0x7d0
      inputSize := args.inputSize
      value }
  have childEntry : EncoderCallEntry Elflings.writeSuccessIntEntry
      Elflings.writeSuccessIntExitPcs UInt64EncoderBinding childArgs callState := by
    unfold EncoderCallEntry
    constructor
    · exact returnListed
    constructor
    · change args.stackPointer - 0x7d0 < 2 ^ 64
      exact writeSuccessChildStackBound upper
    constructor
    · simpa [callState] using callAtPc
    constructor
    · simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, childArgs]
    constructor
    · exact (callWrites.get x2 (by decide)).trans
        (seg2.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    constructor
    · exact ⟨rep.1, (callWrites.get x10 (by decide)).trans
        (seg2.reg x10 (BitVec.ofNat 64 value) (by simp))⟩
    · simpa [callState, callMemEq] using loaded
  obtain ⟨intBound, intImpl⟩ := intChild
  obtain ⟨childUsed, after, unit, _positive, _bounded, childTrace, _childPc, _allowed,
      childExit⟩ := intImpl childArgs (fromStep + 3) callState childEntry
  rcases childExit with ⟨afterPc, stdout, stdin, cursor, exitCode, _frameFits, childMem,
    childFrame⟩
  have callPrefix : ConfinedPrefix writeSuccessParentPc writeSuccessIntCallExitPc
      (fun _ _ _ _ _ => False) (fromStep + 2) 1 baseMachine callMachine :=
    ConfinedPrefix.ownStep seg2.atPc owned2 notExit2 callRun
  have callEnd : ScopedTrace writeSuccessParentPc writeSuccessIntCallExitPc
      (fun _ _ _ _ _ => False) (fromStep + 3) 0 callMachine callMachine :=
    .exitAt _ _ 0x15d10 callAtPc rfl
  have parentMachineTrace := seg2.confined.trans callPrefix 0 callMachine callEnd
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 3 before callState := by
    simpa [callState] using liftWriteSuccessParentTrace before parentMachineTrace
  have childTrace' := childTrace.weaken (fun _ inside =>
    show pcInRanges Elflings.writeSuccessExecutionPcRanges _ from by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lo, hi⟩
      simp only [Elflings.writeSuccessIntExecutionPcRanges, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · simp at member
        subst range
        exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, hi⟩)
  have exactMemory : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 - 16) 16) before.machine after.machine := by
    intro address outside
    rw [childMem address (by simpa [childArgs] using outside), callMemEq]
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have pmaEq := (childFrame.1 pma_regions (by simp [abiCalleePreserved])).trans callPmaEq
  have accessAfter : WriteSuccessMachineAccess args after.machine :=
    { configured := configuredAfterEndpointCall
        (configuredAfterWriteSuccessCall (BitVec.ofNat 64 (pc + 8)) 0x15d10 returnPc retired2
          access2.configured)
        childFrame
      frameLoad := fun position width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access2.frameLoad position width bound)
      frameStore := fun position width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access2.frameStore position width bound)
      frameNoMMIO := access2.frameNoMMIO
      decodedLoad := fun position width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access2.decodedLoad position width bound)
      decodedNoMMIO := access2.decodedNoMMIO
      outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq access2.outputBufferStore
      outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq access2.outputLengthStore
      writerRegionBeforeOutputContext := access2.writerRegionBeforeOutputContext
      frameNotCode := access2.frameNotCode }
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem := by
    intro address byte fileByte
    have outside : ¬byteRange (args.stackPointer - 0x7d0 - 16) 16 address := by
      intro inside
      have inWriter := writeSuccessChildFrame_mem_frame lower inside
      unfold byteRange at inWriter
      rw [Nat.sub_add_cancel lower] at inWriter
      have notCode := access2.frameNotCode address inWriter.1 inWriter.2
      exact Option.some_ne_none byte (fileByte.symm.trans notCode)
    rw [exactMemory address outside]
    exact loaded address byte fileByte
  refine ⟨childUsed, after, {
    trace := ?_
    atPc := afterPc
    stack := (childFrame.1 x2 (by simp [abiCalleePreserved])).trans
      ((callWrites.get x2 (by decide)).trans
        (seg2.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)))
    stdout := by simpa [callState, childArgs] using stdout
    stdin := by simpa [callState] using stdin
    cursor := by simpa [callState] using cursor
    exitCode := by simpa [callState] using exitCode
    memory := exactMemory
    x8 := (childFrame.1 x8 (by simp [abiCalleePreserved])).trans
      ((callWrites.get x8 (by simp [stepBookkeeping])).trans
        (seg2.writes.get x8 (by simp [writeSuccessIntParentWrites])))
    loaded := loadedAfter
    access := accessAfter }⟩
  have all := parentTrace.append (by simpa [Nat.add_assoc] using childTrace')
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

set_option genInjectivity false in
/-- The common exact parent-owned `ld; ld; auipc; jalr` setup used by the late bytes and
byte-list encoders.  Keeping this prefix existentially opaque avoids rebuilding four successor
states at every one of the eight call sites. -/
structure WriteSuccessSliceCallSetup
    (fromStep pc returnPc target address length : Nat)
    (args : WriteSuccessArgs) (before callState : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 4 before callState
  atPc : EndpointPc callState = some (BitVec.ofNat 64 target)
  link : callState.machine.regs.get? x1 = some (BitVec.ofNat 64 returnPc)
  stack : callState.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  address : callState.machine.regs.get? x10 = some (BitVec.ofNat 64 address)
  length : callState.machine.regs.get? x11 = some (BitVec.ofNat 64 length)
  memory : callState.machine.mem = before.machine.mem
  stdin : callState.stdin = before.stdin
  cursor : callState.stdinCursor = before.stdinCursor
  stdout : callState.stdout = before.stdout
  exitCode : callState.exitCode = before.exitCode
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully callState.machine.mem
  access : WriteSuccessMachineAccess args callState.machine

/-- Factor the repeated late writer call prefix.  The three instruction arguments are the literal
Sail wrappers for the concrete call site; all framing and retirement transport is shared. -/
private theorem writeSuccessSliceCallSetup
    (fromStep pc returnPc target addressOffset lengthOffset address length callBase : Nat)
    (args : WriteSuccessArgs) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (addressRep : UIntRep 8 before.machine.mem
      (args.stackPointer - 0x7d0 + addressOffset) address)
    (lengthRep : UIntRep 8 before.machine.mem
      (args.stackPointer - 0x7d0 + lengthOffset) length)
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0)
    (addressLoad : ∀ stepNo state,
      WriteSuccessMachineAccess args state →
      state.regs.get? PC = some (BitVec.ofNat 64 pc) →
      state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) →
      UIntRep 8 state.mem (args.stackPointer - 0x7d0 + addressOffset) address →
      args.stackPointer % 16 = 0 →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x10
          (BitVec.ofNat 64 address)) false)
    (lengthLoad : ∀ stepNo state,
      WriteSuccessMachineAccess args state →
      state.regs.get? PC = some (BitVec.ofNat 64 (pc + 4)) →
      state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) →
      UIntRep 8 state.mem (args.stackPointer - 0x7d0 + lengthOffset) length →
      args.stackPointer % 16 = 0 →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 (pc + 4)) retired x11
          (BitVec.ofNat 64 length)) false)
    (baseStep : ∀ stepNo state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 (pc + 8)) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 (pc + 8)) retired x1
          (BitVec.ofNat 64 callBase)) false)
    (callStep : ∀ stepNo state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 (pc + 12)) →
      state.regs.get? x1 = some (BitVec.ofNat 64 callBase) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 (pc + 12)) target x1 returnPc)
          target retired) false)
    (owned0 : writeSuccessParentPc (BitVec.ofNat 64 pc))
    (owned1 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 4)))
    (owned2 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 8)))
    (owned3 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 12)))
    (beforeTarget0 : BitVec.ofNat 64 pc ≠ BitVec.ofNat 64 target)
    (beforeTarget1 : BitVec.ofNat 64 (pc + 4) ≠ BitVec.ofNat 64 target)
    (beforeTarget2 : BitVec.ofNat 64 (pc + 8) ≠ BitVec.ofNat 64 target)
    (beforeTarget3 : BitVec.ofNat 64 (pc + 12) ≠ BitVec.ofNat 64 target)
    (next0 : Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4 = BitVec.ofNat 64 (pc + 4))
    (next1 : Sail.BitVec.addInt (BitVec.ofNat 64 (pc + 4)) 4 =
      BitVec.ofNat 64 (pc + 8))
    (next2 : Sail.BitVec.addInt (BitVec.ofNat 64 (pc + 8)) 4 =
      BitVec.ofNat 64 (pc + 12)) :
    ∃ callState,
      WriteSuccessSliceCallSetup fromStep pc returnPc target address length
        args before callState := by
  let exitPc : BitVec 64 → Prop := fun current => current = BitVec.ofNat 64 target
  have seg0 : Seg writeSuccessParentPc exitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine (BitVec.ofNat 64 pc) := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  obtain ⟨retired0, run0⟩ := addressLoad fromStep _ access atPc stack addressRep aligned loaded
  have seg1 := seg0.stepKnown owned0 (by simpa [exitPc] using beforeTarget0) x10
    (BitVec.ofNat 64 address) (BitVec.ofNat 64 (pc + 4)) retired0 run0
    next0
    (by intro r h; exact Or.inl h) (by simp [writeSuccessParentWrites])
    (by native_decide) (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite before.machine pc retired0 x10 (BitVec.ofNat 64 address)).mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨retired1, run1⟩ := lengthLoad (fromStep + 1) _ access1 seg1.atPc
    (seg1.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    (lengthRep.of_writesOnlyWithin seg1.mem (by intro _ _ inside; exact inside)) aligned loaded1
  have seg2 := seg1.stepKnown owned1 (by simpa [exitPc] using beforeTarget1) x11
    (BitVec.ofNat 64 length) (BitVec.ofNat 64 (pc + 8)) retired1
    (by simpa [Nat.add_assoc] using run1) next1
    (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg access seg2
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite
        (afterRegisterWrite before.machine (BitVec.ofNat 64 pc) retired0 x10
          (BitVec.ofNat 64 address))
        (BitVec.ofNat 64 (pc + 4)) retired1 x11 (BitVec.ofNat 64 length)).mem := by
    simpa only [afterRegisterWrite_mem] using loaded
  obtain ⟨baseMachine, seg3⟩ := seg2.step owned2
    (by simpa [exitPc] using beforeTarget2) x1
    (BitVec.ofNat 64 callBase) (BitVec.ofNat 64 (pc + 12))
    (baseStep (fromStep + 2) _ access2.configured seg2.atPc loaded2)
    next2 (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access3 := writeSuccessAccessOfSeg access seg3
  have loaded3 : Artifacts.programImage.fileBytesLoadedFaithfully baseMachine.mem := by
    simpa [seg3.memEq (by simp)] using loaded
  obtain ⟨retired3, callRun⟩ := callStep (fromStep + 3) _ access3.configured seg3.atPc
    (seg3.reg x1 (BitVec.ofNat 64 callBase) (by simp)) loaded3
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement baseMachine)
      (BitVec.ofNat 64 (pc + 12)) target x1 returnPc) target retired3
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes baseMachine (BitVec.ofNat 64 (pc + 12))
    target retired3 x1 returnPc
  have callAtPc : callMachine.regs.get? PC = some (BitVec.ofNat 64 target) := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callMemEq : callMachine.mem = before.machine.mem := by
    calc
      callMachine.mem = baseMachine.mem := by
        change (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement baseMachine)
            (BitVec.ofNat 64 (pc + 12)) target x1 returnPc) target retired3).mem = _
        rw [tryStepControlFlowAfterRetired_mem]
        change (controlFlowJumpState (tryStepControlFlowAfterIncrement baseMachine)
          (BitVec.ofNat 64 (pc + 12)) target).mem = _
        rw [controlFlowJumpState_mem]
        rfl
      _ = before.machine.mem := seg3.memEq (by simp)
  have callPrefix : ConfinedPrefix writeSuccessParentPc exitPc
      (fun _ _ _ _ _ => False) (fromStep + 3) 1 baseMachine callMachine :=
    ConfinedPrefix.ownStep seg3.atPc owned3 (by simpa [exitPc] using beforeTarget3) callRun
  have callEnd : ScopedTrace writeSuccessParentPc exitPc
      (fun _ _ _ _ _ => False) (fromStep + 4) 0 callMachine callMachine :=
    .exitAt _ _ _ callAtPc rfl
  have machineTrace := seg3.confined.trans callPrefix 0 callMachine callEnd
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 4 before callState := by
    simpa [callState] using liftWriteSuccessParentTrace before machineTrace
  have pmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have accessCall : WriteSuccessMachineAccess args callMachine := {
    configured := configuredAfterWriteSuccessCall (BitVec.ofNat 64 (pc + 12)) target returnPc
      retired3 access3.configured
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (access3.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (access3.frameStore offset width bound)
    frameNoMMIO := access3.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (access3.decodedLoad offset width bound)
    decodedNoMMIO := access3.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq access3.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq access3.outputLengthStore
    writerRegionBeforeOutputContext := access3.writerRegionBeforeOutputContext
    frameNotCode := access3.frameNotCode }
  have stackCall : callState.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) := by
    simpa [callState] using (callWrites.get x2 (by decide)).trans
      (seg3.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
  have addressCall : callState.machine.regs.get? x10 = some (BitVec.ofNat 64 address) := by
    simpa [callState] using (callWrites.get x10 (by decide)).trans
      (seg3.reg x10 (BitVec.ofNat 64 address) (by simp))
  have lengthCall : callState.machine.regs.get? x11 = some (BitVec.ofNat 64 length) := by
    simpa [callState] using (callWrites.get x11 (by decide)).trans
      (seg3.reg x11 (BitVec.ofNat 64 length) (by simp))
  exact ⟨callState, {
    trace := parentTrace
    atPc := by simpa [callState, EndpointPc] using callAtPc
    link := by simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
    stack := stackCall
    address := addressCall
    length := lengthCall
    memory := callMemEq
    stdin := rfl
    cursor := rfl
    stdout := rfl
    exitCode := rfl
    loaded := by simpa [callState, callMemEq] using loaded
    access := by simpa [callState] using accessCall }⟩

/-- Literal dword loads used by the eight late slice-call sites. -/
private theorem writeSuccessLateSliceLoadStep (stepNo pc offset value : Nat)
    (rd : regidx) (destination : Register) (result : RegisterType destination)
    (byte0 byte1 byte2 byte3 : UInt8)
    (args : WriteSuccessArgs) (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + offset) value)
    (offsetBound : offset + 8 ≤ 0x7d0)
    (slotAligned : (args.stackPointer - 0x7d0 + offset) % 8 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (writeRun : ∀ premise, Runs (wX_bits rd (BitVec.ofNat 64 value)) premise
      { premise with regs := premise.regs.insert destination result } ())
    (signExtend : sign_extend (m := 64) (BitVec.ofNat 12 offset) = BitVec.ofNat 64 offset)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (BitVec.ofNat 12 offset, .Regidx 2#5, rd, false, 8)))
    (pcFits : pc < 2 ^ 64)
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false := by
  exact writeSuccessFrameDwordLoadStep stepNo pc offset value args state rd destination
    result (BitVec.ofNat 12 offset) byte0 byte1 byte2 byte3 access atPc
    stack rep offsetBound slotAligned loaded
    (by rw [signExtend, ← BitVec.ofNat_add]) writeRun decode
    (pcFits := pcFits) (destinationNotNextPc := destinationNotNextPc)
    (destinationNotHart := destinationNotHart)
    (destinationNotIncrement := destinationNotIncrement)
    (destinationNotRetired := destinationNotRetired) (base := base)
    (read0 := read0) (read1 := read1) (read2 := read2) (read3 := read3)

/-- Literal `auipc ra,0` used by the eight late slice-call sites. -/
private theorem writeSuccessLateSliceCallBaseStep (stepNo pc : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (pcFits : pc < 2 ^ 64)
    (read0 : Artifacts.programImage.readFileByte? pc = some 0x97)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some 0x00)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some 0x00)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some 0x00)
    (decode : Runs (ext_decode (fetchWord 0x97 0x00 0x00 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0, .Regidx 1#5, .AUIPC))) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x1 (BitVec.ofNat 64 pc)) false := by
  obtain ⟨retired, run⟩ := configuredAuipcStep stepNo state pc 0#20 0x97 0x00 0x00 0x00
    configured atPc loaded pcFits read0 read1 read2 read3 (by rfl) decode
  generalize concatEq : (0#20 +++ 0#12) = concatenated at run
  have zeroExtend : sign_extend concatenated = 0#64 := by
    rw [← concatEq]
    native_decide
  rw [zeroExtend, BitVec.add_zero] at run
  refine ⟨retired, ?_⟩
  change Runs (try_step stepNo false) state
    (tryStepControlFlowAfterRetired
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 pc) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 pc)).regs.insert x1 (BitVec.ofNat 64 pc) }
      (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false
  simpa only [afterRegisterWrite] using run

/-- Literal `jalr` used by the eight late slice-call sites. -/
private theorem writeSuccessLateSliceCallStep (stepNo pc target returnPc immediate : Nat)
    (byte0 byte1 byte2 byte3 : UInt8) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (baseRead : state.regs.get? x1 = some (BitVec.ofNat 64 (pc - 4)))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (targetEq : pc - 4 + immediate = target)
    (returnEq : pc + 4 = returnPc)
    (pcFits : pc < 2 ^ 64)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (BitVec.ofNat 12 immediate, .Regidx 1#5, .Regidx 1#5)))
    (targetBits : Sail.BitVec.update
      (BitVec.ofNat 64 (pc - 4) + sign_extend (BitVec.ofNat 12 immediate)) 0 0#1 =
      BitVec.ofNat 64 (pc - 4 + immediate))
    (returnBits : Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4 = BitVec.ofNat 64 (pc + 4))
    (targetBit1 : Sail.BitVec.access
      (BitVec.ofNat 64 (pc - 4) + sign_extend (BitVec.ofNat 12 immediate)) 1 = 0#1) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
          (BitVec.ofNat 64 target) x1 (BitVec.ofNat 64 returnPc))
        (BitVec.ofNat 64 target) retired) false := by
  subst target returnPc
  apply configuredJalrCallStep stepNo state pc (BitVec.ofNat 64 (pc - 4))
    (BitVec.ofNat 12 immediate) (BitVec.ofNat 64 (pc - 4 + immediate))
    (BitVec.ofNat 64 (pc + 4)) byte0 byte1 byte2 byte3 configured atPc baseRead loaded
    pcFits read0 read1 read2 read3 base decode targetBits returnBits targetBit1

set_option genInjectivity false in
/-- One late shared bytes call after the generic four-instruction parent setup. -/
structure WriteSuccessLateBytesHandoff
    (fromStep childUsed returnPc : Nat) (value : Array UInt8)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (before after : EndpointState) (savedValues : DecodeCalleeSavedValues) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges)
    fromStep (4 + childUsed) before after
  atPc : EndpointPc after = some (BitVec.ofNat 64 returnPc)
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeBytes value
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args savedValues)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  writerMemory : WriteSuccessMemoryFrame args before.machine after.machine
  memory : WritesOnlyWithin
    (byteRange (args.stackPointer - 0x7d0 - 48) 48) before.machine after.machine

/-- Concrete Sail instruction proofs for one four-instruction late encoder call site. -/
private structure WriteSuccessLateSliceSiteSteps
    (pc returnPc target addressOffset lengthOffset callBase : Nat)
    (args : WriteSuccessArgs) where
  addressLoad : ∀ address stepNo state,
    WriteSuccessMachineAccess args state →
    state.regs.get? PC = some (BitVec.ofNat 64 pc) →
    state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) →
    UIntRep 8 state.mem (args.stackPointer - 0x7d0 + addressOffset) address →
    args.stackPointer % 16 = 0 →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x10
        (BitVec.ofNat 64 address)) false
  lengthLoad : ∀ length stepNo state,
    WriteSuccessMachineAccess args state →
    state.regs.get? PC = some (BitVec.ofNat 64 (pc + 4)) →
    state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) →
    UIntRep 8 state.mem (args.stackPointer - 0x7d0 + lengthOffset) length →
    args.stackPointer % 16 = 0 →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 (pc + 4)) retired x11
        (BitVec.ofNat 64 length)) false
  callBaseStep : ∀ stepNo state,
    ConfiguredMachinePre EndpointMachinePc state →
    state.regs.get? PC = some (BitVec.ofNat 64 (pc + 8)) →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 (pc + 8)) retired x1
        (BitVec.ofNat 64 callBase)) false
  callStep : ∀ stepNo state,
    ConfiguredMachinePre EndpointMachinePc state →
    state.regs.get? PC = some (BitVec.ofNat 64 (pc + 12)) →
    state.regs.get? x1 = some (BitVec.ofNat 64 callBase) →
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 (pc + 12)) target x1 returnPc)
        target retired) false

/-- Build one concrete late-call instruction bundle from its pinned load and `jalr` bytes. -/
macro "writeSuccessLateSliceSteps(" args:term ";" pc:term "," returnPc:term ","
    target:term "," addressOffset:term "," lengthOffset:term "," callBase:term ";"
    a0:term "," a1:term "," a2:term ","
    a3:term ";" l0:term "," l1:term "," l2:term "," l3:term ";"
    j0:term "," j1:term "," j2:term "," j3:term ";" immediate:term ")" : term =>
  `({
    addressLoad := by
      intro address stepNo state access atPc stack rep _aligned loaded
      exact writeSuccessLateSliceLoadStep stepNo $pc $addressOffset address (.Regidx 10#5) x10
        (BitVec.ofNat 64 address) $a0 $a1 $a2 $a3 $args state access atPc stack rep
        (by omega) (by omega) loaded (fun premise => wX_x10_run premise _)
        (by native_decide)
        (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads access.configured; decode_run)
        (by native_decide) (by decide) (by decide) (by decide) (by decide)
        (by rfl) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    lengthLoad := by
      intro length stepNo state access atPc stack rep _aligned loaded
      exact writeSuccessLateSliceLoadStep stepNo ($pc + 4) $lengthOffset length (.Regidx 11#5) x11
        (BitVec.ofNat 64 length) $l0 $l1 $l2 $l3 $args state access atPc stack rep
        (by omega) (by omega) loaded (fun premise => wX_x11_run premise _)
        (by native_decide)
        (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads access.configured; decode_run)
        (by native_decide) (by decide) (by decide) (by decide) (by decide)
        (by rfl) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    callBaseStep := by
      intro stepNo state configured atPc loaded
      exact writeSuccessLateSliceCallBaseStep stepNo $callBase state configured atPc loaded
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide)
        (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured; decode_run)
    callStep := by
      intro stepNo state configured atPc base loaded
      exact writeSuccessLateSliceCallStep stepNo ($pc + 12) $target $returnPc $immediate
        $j0 $j1 $j2 $j3 state configured atPc base loaded
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by rfl)
        (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured; decode_run)
        (by native_decide) (by native_decide) (by native_decide) })

/-- Consume the selected shared bytes contract from a completed late slice-call setup. -/
private theorem writeSuccessLateBytesHandoff
    (child : WriteSuccessBytesInstanceContract)
    (fromStep pc returnPc dataAddress : Nat)
    (args : WriteSuccessArgs) (payloadBytes value : Array UInt8)
    (savedValues : DecodeCalleeSavedValues) (before callState : EndpointState)
    (setup : WriteSuccessSliceCallSetup fromStep pc returnPc 0x15c6c dataAddress value.size
      args before callState)
    (bytesRep : BytesRep before.machine.mem dataAddress value)
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args savedValues))
    (lower : 0x880 ≤ args.stackPointer) (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20)
    (returnListed : returnPc ∈ Elflings.writeSuccessBytesExitPcs) :
    ∃ childUsed after,
      WriteSuccessLateBytesHandoff fromStep childUsed returnPc value args payloadBytes
        before after savedValues := by
  let childValue : BytesEncoderValue := { address := dataAddress, bytes := value }
  let childArgs : EncoderCallArgs BytesEncoderValue := {
    returnAddress := returnPc
    callerStack := args.stackPointer - 0x7d0
    inputSize := args.inputSize
    value := childValue }
  have childEntry : EncoderCallEntry Elflings.writeSuccessBytesEntry
      Elflings.writeSuccessBytesExitPcs BytesEncoderBinding childArgs callState := by
    unfold EncoderCallEntry
    refine ⟨(by simpa [childArgs] using returnListed),
      writeSuccessChildStackBound upper, setup.atPc, ?_, ?_, ?_, setup.loaded⟩
    · simpa [childArgs] using setup.link
    · simpa [childArgs] using setup.stack
    · refine ⟨bytesRep.1, ?_, ?_, ?_⟩
      · simpa [childArgs, childValue] using setup.address
      · simpa [childArgs, childValue] using setup.length
      · simpa [childArgs, childValue, setup.memory] using bytesRep
  have frameInWriter : ∀ address,
      byteRange (args.stackPointer - 0x7d0 - 48) 48 address →
      writeSuccessFrameMemory args address := by
    intro address inside
    exact writeSuccessChildFrame48_mem_frame lower inside
  obtain ⟨childUsed, after, handoff⟩ := writeSuccessEncoderChildHandoff child
    (fun inside => by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lo, hi⟩
      simp only [Elflings.writeSuccessBytesExecutionPcRanges, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, hi⟩)
    fromStep 4 args childValue before callState childArgs rfl childEntry setup.trace
    ⟨setup.stdin, setup.cursor, setup.stdout, setup.exitCode⟩ setup.memory setup.access setup.loaded
    lower frameInWriter
  have payloadAfter := writeSuccessPayloadContextAfterChild decodedAddress lower upper
    handoff.access.writerRegionBeforeOutputContext context handoff.memory
    (fun address inside => Or.inl (frameInWriter address inside)) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      rw [decodedAddress] at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      rw [decodedAddress] at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro values word member index inBounds inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> unfold byteRange at inside <;> omega)
  have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args savedValues) := by
    intro word member
    exact (saved word member).of_writesOnlyWithin handoff.memory (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  exact ⟨childUsed, after, {
    trace := handoff.trace
    atPc := handoff.atPc
    stack := handoff.stack
    stdout := by simpa [childValue] using handoff.stdout
    stdin := handoff.stdin
    cursor := handoff.cursor
    exitCode := handoff.exitCode
    saved := savedAfter
    payloadContext := payloadAfter
    loaded := handoff.loaded
    access := handoff.access
    writerMemory := writeSuccessChildFrame48_writes_writerFrame lower handoff.memory
    memory := handoff.memory }⟩

/-- The first execution-request bytes call, `0x158e0..0x158ec`, through its selected child. -/
private theorem writeSuccessFirstRequestHandoff
    (child : WriteSuccessBytesInstanceContract) (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (savedValues : DecodeCalleeSavedValues)
    (before : EndpointState) (atPc : before.machine.regs.get? PC = some 0x158e0)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args savedValues))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessLateBytesHandoff fromStep childUsed 0x158f0
        args.decoded.executionRequests.deposits args payloadBytes before after savedValues := by
  obtain ⟨deposits, _withdrawals, _consolidations, _builderDeposits, _builderExits⟩ :=
    context.executionRequestsRep decodedAddress upper
  obtain ⟨address, addressRep, lengthRep, bytesRep⟩ := deposits
  obtain ⟨callState, setup⟩ := writeSuccessSliceCallSetup
    fromStep 0x158e0 0x158f0 0x15c6c 0x398 0x3a0 address
    args.decoded.executionRequests.deposits.size 0x158e8 args before atPc stack addressRep
    lengthRep access loaded aligned
    (fun step state access pc stack rep aligned loaded =>
      writeSuccessLateSliceLoadStep step 0x158e0 0x398 address (.Regidx 10#5) x10
        (BitVec.ofNat 64 address) 0x03 0x35 0x81 0x39 args state access pc stack rep
        (by omega) (by omega) loaded
        (fun premise => wX_x10_run premise _)
        (by native_decide)
        (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads access.configured; decode_run)
        (by native_decide) (by decide) (by decide) (by decide) (by decide)
        (by rfl) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide))
    (fun step state access pc stack rep aligned loaded =>
      writeSuccessLateSliceLoadStep step 0x158e4 0x3a0
        args.decoded.executionRequests.deposits.size (.Regidx 11#5) x11
        (BitVec.ofNat 64 args.decoded.executionRequests.deposits.size)
        0x83 0x35 0x01 0x3a args state access pc stack rep (by omega) (by omega) loaded
        (fun premise => wX_x11_run premise _)
        (by native_decide)
        (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads access.configured; decode_run)
        (by native_decide) (by decide) (by decide) (by decide) (by decide)
        (by rfl) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide))
    (fun step state configured pc loaded =>
      writeSuccessLateSliceCallBaseStep step 0x158e8 state configured pc loaded
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide)
        (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured; decode_run))
    (fun step state configured pc base loaded =>
      writeSuccessLateSliceCallStep step 0x158ec 0x15c6c 0x158f0 0x384
        0xe7 0x80 0x40 0x38 state configured pc base loaded (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by rfl)
        (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads configured; decode_run)
        (by native_decide) (by native_decide) (by native_decide))
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  exact writeSuccessLateBytesHandoff child fromStep 0x158e0 0x158f0 address args payloadBytes
    args.decoded.executionRequests.deposits savedValues before callState setup
    bytesRep.byteSliceBytesRep context saved lower upper decodedAddress (by native_decide)

/-- One literal late bytes site, sharing the four-step `Seg` and selected-child composition. -/
private theorem writeSuccessLateBytesSite
    (child : WriteSuccessBytesInstanceContract)
    (fromStep pc returnPc addressOffset lengthOffset immediate : Nat)
    (args : WriteSuccessArgs) (payloadBytes value : Array UInt8)
    (savedValues : DecodeCalleeSavedValues) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (descriptor : ByteSliceRep before.machine.mem
      (args.stackPointer - 0x7d0 + addressOffset) value)
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args savedValues))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20)
    (lengthOffsetEq : addressOffset + 8 = lengthOffset)
    (steps : WriteSuccessLateSliceSiteSteps pc returnPc 0x15c6c addressOffset
      lengthOffset (pc + 8) args)
    (returnEq : pc + 16 = returnPc)
    (targetEq : pc + 8 + immediate = 0x15c6c)
    (owned0 : writeSuccessParentPc (BitVec.ofNat 64 pc))
    (owned1 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 4)))
    (owned2 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 8)))
    (owned3 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 12)))
    (before0 : BitVec.ofNat 64 pc ≠ 0x15c6c)
    (before1 : BitVec.ofNat 64 (pc + 4) ≠ 0x15c6c)
    (before2 : BitVec.ofNat 64 (pc + 8) ≠ 0x15c6c)
    (before3 : BitVec.ofNat 64 (pc + 12) ≠ 0x15c6c)
    (next0 : Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4 = BitVec.ofNat 64 (pc + 4))
    (next1 : Sail.BitVec.addInt (BitVec.ofNat 64 (pc + 4)) 4 = BitVec.ofNat 64 (pc + 8))
    (next2 : Sail.BitVec.addInt (BitVec.ofNat 64 (pc + 8)) 4 = BitVec.ofNat 64 (pc + 12))
    (returnListed : returnPc ∈ Elflings.writeSuccessBytesExitPcs) :
    ∃ childUsed after,
      WriteSuccessLateBytesHandoff fromStep childUsed returnPc value args payloadBytes
        before after savedValues := by
  obtain ⟨address, addressRep, lengthRep, bytesRep⟩ := descriptor
  have lengthRep' : UIntRep 8 before.machine.mem
      (args.stackPointer - 0x7d0 + lengthOffset) value.size := by
    simpa [← lengthOffsetEq, Nat.add_assoc] using lengthRep
  have setupExists : ∃ callState,
      WriteSuccessSliceCallSetup fromStep pc returnPc 0x15c6c address value.size
        args before callState :=
    writeSuccessSliceCallSetup fromStep pc returnPc 0x15c6c
    addressOffset lengthOffset address value.size (pc + 8) args before atPc stack addressRep
    lengthRep' access loaded aligned
    (steps.addressLoad address) (steps.lengthLoad value.size) steps.callBaseStep steps.callStep
    owned0 owned1 owned2 owned3 before0 before1 before2 before3 next0 next1 next2
  obtain ⟨callState, setup⟩ := setupExists
  exact writeSuccessLateBytesHandoff child fromStep pc returnPc address args payloadBytes value savedValues before
    callState setup bytesRep.byteSliceBytesRep context saved lower upper decodedAddress returnListed

set_option genInjectivity false in
/-- All five execution-request byte slices, in production order through `0x15930`. -/
structure WriteSuccessRequestsHandoff
    (fromStep dUsed wUsed cUsed bdUsed beUsed : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (savedValues : DecodeCalleeSavedValues)
    (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep
    (4 + dUsed + 4 + wUsed + 4 + cUsed + 4 + bdUsed + 4 + beUsed) before after
  atPc : EndpointPc after = some 0x15930
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++
    encodeBytes args.decoded.executionRequests.deposits ++
    encodeBytes args.decoded.executionRequests.withdrawals ++
    encodeBytes args.decoded.executionRequests.consolidations ++
    encodeBytes args.decoded.executionRequests.builderDeposits ++
    encodeBytes args.decoded.executionRequests.builderExits
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args savedValues)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine

/-- Compose the five repeated execution-request byte encoders. -/
private theorem writeSuccessRequestsHandoff
    (child : WriteSuccessBytesInstanceContract) (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (savedValues : DecodeCalleeSavedValues)
    (before : EndpointState) (atPc : before.machine.regs.get? PC = some 0x158e0)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args savedValues))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ dUsed wUsed cUsed bdUsed beUsed after,
      WriteSuccessRequestsHandoff fromStep dUsed wUsed cUsed bdUsed beUsed args payloadBytes
        savedValues before after := by
  obtain ⟨dUsed, s1, h1⟩ := writeSuccessFirstRequestHandoff child fromStep args payloadBytes
    savedValues before atPc stack context saved access loaded aligned lower upper decodedAddress
  obtain ⟨_, withdrawals, _, _, _⟩ := h1.payloadContext.executionRequestsRep decodedAddress upper
  obtain ⟨wUsed, s2, h2⟩ := writeSuccessLateBytesSite child (fromStep + 4 + dUsed)
    0x158f0 0x15900 0x3a8 0x3b0 0x374 args payloadBytes
    args.decoded.executionRequests.withdrawals
    savedValues s1 (by simpa [EndpointPc, MachinePc] using h1.atPc) h1.stack withdrawals
    h1.payloadContext h1.saved h1.access h1.loaded aligned lower upper decodedAddress
    (by native_decide)
    (writeSuccessLateSliceSteps(args; 0x158f0, 0x15900, 0x15c6c, 0x3a8, 0x3b0,
      0x158f8; 0x03, 0x35, 0x81, 0x3a;
      0x83, 0x35, 0x01, 0x3b; 0xe7, 0x80, 0x40, 0x37; 0x374))
    (by native_decide) (by native_decide)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, consolidations, _, _⟩ :=
    h2.payloadContext.executionRequestsRep decodedAddress upper
  obtain ⟨cUsed, s3, h3⟩ := writeSuccessLateBytesSite child
    (fromStep + 4 + dUsed + 4 + wUsed) 0x15900 0x15910 0x3b8 0x3c0 0x364
    args payloadBytes args.decoded.executionRequests.consolidations savedValues s2
    (by simpa [EndpointPc, MachinePc] using h2.atPc) h2.stack consolidations h2.payloadContext
    h2.saved h2.access h2.loaded aligned lower upper decodedAddress (by native_decide)
    (writeSuccessLateSliceSteps(args; 0x15900, 0x15910, 0x15c6c, 0x3b8, 0x3c0,
      0x15908; 0x03, 0x35, 0x81, 0x3b;
      0x83, 0x35, 0x01, 0x3c; 0xe7, 0x80, 0x40, 0x36; 0x364))
    (by native_decide) (by native_decide)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, _, builderDeposits, _⟩ :=
    h3.payloadContext.executionRequestsRep decodedAddress upper
  obtain ⟨bdUsed, s4, h4⟩ := writeSuccessLateBytesSite child
    (fromStep + 4 + dUsed + 4 + wUsed + 4 + cUsed) 0x15910 0x15920 0x3c8 0x3d0 0x354
    args payloadBytes args.decoded.executionRequests.builderDeposits savedValues s3
    (by simpa [EndpointPc, MachinePc] using h3.atPc) h3.stack builderDeposits h3.payloadContext
    h3.saved h3.access h3.loaded aligned lower upper decodedAddress (by native_decide)
    (writeSuccessLateSliceSteps(args; 0x15910, 0x15920, 0x15c6c, 0x3c8, 0x3d0,
      0x15918; 0x03, 0x35, 0x81, 0x3c;
      0x83, 0x35, 0x01, 0x3d; 0xe7, 0x80, 0x40, 0x35; 0x354))
    (by native_decide) (by native_decide)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, _, _, builderExits⟩ := h4.payloadContext.executionRequestsRep decodedAddress upper
  obtain ⟨beUsed, s5, h5⟩ := writeSuccessLateBytesSite child
    (fromStep + 4 + dUsed + 4 + wUsed + 4 + cUsed + 4 + bdUsed)
    0x15920 0x15930 0x3d8 0x3e0 0x344 args payloadBytes
    args.decoded.executionRequests.builderExits
    savedValues s4 (by simpa [EndpointPc, MachinePc] using h4.atPc) h4.stack builderExits
    h4.payloadContext h4.saved h4.access h4.loaded aligned lower upper decodedAddress
    (by native_decide)
    (writeSuccessLateSliceSteps(args; 0x15920, 0x15930, 0x15c6c, 0x3d8, 0x3e0,
      0x15928; 0x03, 0x35, 0x81, 0x3d;
      0x83, 0x35, 0x01, 0x3e; 0xe7, 0x80, 0x40, 0x34; 0x344))
    (by native_decide) (by native_decide)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨dUsed, wUsed, cUsed, bdUsed, beUsed, s5, {
    trace := ?_
    atPc := h5.atPc
    stack := h5.stack
    stdout := ?_
    stdin := h5.stdin.trans (h4.stdin.trans (h3.stdin.trans (h2.stdin.trans h1.stdin)))
    cursor := h5.cursor.trans (h4.cursor.trans (h3.cursor.trans (h2.cursor.trans h1.cursor)))
    exitCode := h5.exitCode.trans
      (h4.exitCode.trans (h3.exitCode.trans (h2.exitCode.trans h1.exitCode)))
    saved := h5.saved
    payloadContext := h5.payloadContext
    loaded := h5.loaded
    access := h5.access
    memory := WritesOnlyWithin.trans_same
      (WritesOnlyWithin.trans_same
        (WritesOnlyWithin.trans_same
          (WritesOnlyWithin.trans_same
            (writeSuccessChildFrame48_writes_writerFrame lower h1.memory)
            (writeSuccessChildFrame48_writes_writerFrame lower h2.memory))
          (writeSuccessChildFrame48_writes_writerFrame lower h3.memory))
        (writeSuccessChildFrame48_writes_writerFrame lower h4.memory))
      (writeSuccessChildFrame48_writes_writerFrame lower h5.memory) }⟩
  · have t2 := h1.trace.append (by simpa [Nat.add_assoc] using h2.trace)
    have t3 := t2.append (by simpa [Nat.add_assoc] using h3.trace)
    have t4 := t3.append (by simpa [Nat.add_assoc] using h4.trace)
    simpa only [Nat.add_assoc] using
      t4.append (by simpa only [Nat.add_assoc] using h5.trace)
  · simp only [h5.stdout, h4.stdout, h3.stdout, h2.stdout, h1.stdout,
      Array.append_assoc]

set_option genInjectivity false in
/-- One late shared byte-list call after its four parent setup instructions. -/
structure WriteSuccessLateByteListsHandoff
    (fromStep childUsed returnPc : Nat) (value : Array (Array UInt8))
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (before after : EndpointState) (savedValues : DecodeCalleeSavedValues) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (4 + childUsed) before after
  atPc : EndpointPc after = some (BitVec.ofNat 64 returnPc)
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeMany encodeBytes value
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args savedValues)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine

/-- Consume the selected byte-list child once its exact four-step parent setup is complete. -/
private theorem writeSuccessLateByteListsFromSetup
    (child : WriteSuccessByteListsInstanceContract)
    (fromStep pc returnPc address : Nat) (value : Array (Array UInt8))
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (before callState : EndpointState) (savedValues : DecodeCalleeSavedValues)
    (setup : WriteSuccessSliceCallSetup fromStep pc returnPc 0x15c10 address value.size
      args before callState)
    (arrayRep : ArrayRep 16 ByteSliceRep before.machine.mem address value)
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args savedValues))
    (lower : 0x880 ≤ args.stackPointer) (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20)
    (returnListed : returnPc ∈ Elflings.writeSuccessByteListsExitPcs) :
    ∃ childUsed after,
      WriteSuccessLateByteListsHandoff fromStep childUsed returnPc value args payloadBytes
        before after savedValues := by
  let childValue : ByteListsEncoderValue := { address := address, values := value }
  let childArgs : EncoderCallArgs ByteListsEncoderValue := {
    returnAddress := returnPc
    callerStack := args.stackPointer - 0x7d0
    inputSize := args.inputSize
    value := childValue }
  have childEntry : EncoderCallEntry Elflings.writeSuccessByteListsEntry
      Elflings.writeSuccessByteListsExitPcs ByteListsEncoderBinding childArgs callState := by
    unfold EncoderCallEntry
    refine ⟨by simpa [childArgs] using returnListed, writeSuccessChildStackBound upper,
      setup.atPc, ?_, ?_, ?_, setup.loaded⟩
    · simpa [childArgs] using setup.link
    · simpa [childArgs] using setup.stack
    · refine ⟨arrayRep.1, ?_, ?_, ?_⟩
      · simpa [childArgs, childValue] using setup.address
      · simpa [childArgs, childValue] using setup.length
      · simpa [childArgs, childValue, setup.memory] using arrayRep
  have frameInWriter : ∀ address,
      byteRange (args.stackPointer - 0x7d0 - 64) 64 address →
      writeSuccessFrameMemory args address := fun _ inside =>
    writeSuccessChildFrame64_mem_frame lower inside
  obtain ⟨childUsed, after, handoff⟩ := writeSuccessEncoderChildHandoff child
    (fun inside => by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lo, hi⟩
      simp [Elflings.writeSuccessByteListsExecutionPcRanges] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩)
    fromStep 4 args childValue before callState childArgs rfl childEntry setup.trace
    ⟨setup.stdin, setup.cursor, setup.stdout, setup.exitCode⟩ setup.memory setup.access setup.loaded
    lower frameInWriter
  have payloadAfter := writeSuccessPayloadContextAfterChild decodedAddress lower upper
    handoff.access.writerRegionBeforeOutputContext context handoff.memory
    (fun address inside => Or.inl (frameInWriter address inside)) (by
      intro index inBounds inside; unfold byteRange at inside; omega) (by
      intro index inBounds inside; unfold byteRange at inside; omega) (by
      intro index inBounds inside; unfold byteRange at inside; omega) (by
      intro index inBounds inside; unfold byteRange at inside; rw [decodedAddress] at inside; omega)
    (by
      intro index inBounds inside; unfold byteRange at inside
      rw [decodedAddress] at inside; omega) (by
      intro index inBounds inside; unfold byteRange at inside; omega) (by
      intro values word member index inBounds inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> unfold byteRange at inside <;> omega)
  have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args savedValues) := by
    intro word member
    exact (saved word member).of_writesOnlyWithin handoff.memory (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  exact ⟨childUsed, after, {
    trace := handoff.trace
    atPc := handoff.atPc
    stack := handoff.stack
    stdout := by simpa [childValue] using handoff.stdout
    stdin := handoff.stdin
    cursor := handoff.cursor
    exitCode := handoff.exitCode
    saved := savedAfter
    payloadContext := payloadAfter
    loaded := handoff.loaded
    access := handoff.access
    memory := writeSuccessChildFrame64_writes_writerFrame lower handoff.memory }⟩

/-- One literal late byte-list site, sharing the four-step `Seg` and selected-child composition. -/
private theorem writeSuccessLateByteListsSite
    (child : WriteSuccessByteListsInstanceContract)
    (fromStep pc returnPc addressOffset lengthOffset immediate : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (value : Array (Array UInt8))
    (savedValues : DecodeCalleeSavedValues) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (descriptor : WriteSuccessSeparatedSliceRep 16 ByteSliceRep before.machine.mem
      (args.stackPointer - 0x7d0 + addressOffset)
      (args.stackPointer - 0x7d0 + lengthOffset) value)
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args savedValues))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20)
    (steps : WriteSuccessLateSliceSiteSteps pc returnPc 0x15c10 addressOffset
      lengthOffset (pc + 8) args)
    (returnEq : pc + 16 = returnPc) (targetEq : pc + 8 + immediate = 0x15c10)
    (owned0 : writeSuccessParentPc (BitVec.ofNat 64 pc))
    (owned1 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 4)))
    (owned2 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 8)))
    (owned3 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 12)))
    (before0 : BitVec.ofNat 64 pc ≠ 0x15c10)
    (before1 : BitVec.ofNat 64 (pc + 4) ≠ 0x15c10)
    (before2 : BitVec.ofNat 64 (pc + 8) ≠ 0x15c10)
    (before3 : BitVec.ofNat 64 (pc + 12) ≠ 0x15c10)
    (next0 : Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4 = BitVec.ofNat 64 (pc + 4))
    (next1 : Sail.BitVec.addInt (BitVec.ofNat 64 (pc + 4)) 4 = BitVec.ofNat 64 (pc + 8))
    (next2 : Sail.BitVec.addInt (BitVec.ofNat 64 (pc + 8)) 4 = BitVec.ofNat 64 (pc + 12))
    (returnListed : returnPc ∈ Elflings.writeSuccessByteListsExitPcs) :
    ∃ childUsed after,
      WriteSuccessLateByteListsHandoff fromStep childUsed returnPc value args payloadBytes
        before after savedValues := by
  obtain ⟨address, addressRep, lengthRep, arrayRep⟩ := descriptor
  obtain ⟨callState, setup⟩ := writeSuccessSliceCallSetup fromStep pc returnPc 0x15c10
    addressOffset lengthOffset address value.size (pc + 8) args before atPc stack addressRep
    lengthRep access loaded aligned
    (steps.addressLoad address) (steps.lengthLoad value.size) steps.callBaseStep steps.callStep
    owned0 owned1 owned2 owned3 before0 before1 before2 before3 next0 next1 next2
  let childValue : ByteListsEncoderValue := { address := address, values := value }
  let childArgs : EncoderCallArgs ByteListsEncoderValue := {
    returnAddress := returnPc
    callerStack := args.stackPointer - 0x7d0
    inputSize := args.inputSize
    value := childValue }
  have childEntry : EncoderCallEntry Elflings.writeSuccessByteListsEntry
      Elflings.writeSuccessByteListsExitPcs ByteListsEncoderBinding childArgs callState := by
    unfold EncoderCallEntry
    refine ⟨by simpa [childArgs] using returnListed, writeSuccessChildStackBound upper,
      setup.atPc, ?_, ?_, ?_, setup.loaded⟩
    · simpa [childArgs] using setup.link
    · simpa [childArgs] using setup.stack
    · refine ⟨arrayRep.1, ?_, ?_, ?_⟩
      · simpa [childArgs, childValue] using setup.address
      · simpa [childArgs, childValue] using setup.length
      · simpa [childArgs, childValue, setup.memory] using arrayRep
  have frameInWriter : ∀ address,
      byteRange (args.stackPointer - 0x7d0 - 64) 64 address →
      writeSuccessFrameMemory args address := fun _ inside =>
    writeSuccessChildFrame64_mem_frame lower inside
  obtain ⟨childUsed, after, handoff⟩ := writeSuccessEncoderChildHandoff child
    (fun inside => by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lo, hi⟩
      simp [Elflings.writeSuccessByteListsExecutionPcRanges] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩)
    fromStep 4 args childValue before callState childArgs rfl childEntry setup.trace
    ⟨setup.stdin, setup.cursor, setup.stdout, setup.exitCode⟩ setup.memory setup.access setup.loaded
    lower frameInWriter
  have payloadAfter := writeSuccessPayloadContextAfterChild decodedAddress lower upper
    handoff.access.writerRegionBeforeOutputContext context handoff.memory
    (fun address inside => Or.inl (frameInWriter address inside)) (by
      intro index inBounds inside; unfold byteRange at inside; omega) (by
      intro index inBounds inside; unfold byteRange at inside; omega) (by
      intro index inBounds inside; unfold byteRange at inside; omega) (by
      intro index inBounds inside; unfold byteRange at inside; rw [decodedAddress] at inside; omega)
    (by
      intro index inBounds inside
      unfold byteRange at inside
      rw [decodedAddress] at inside
      omega) (by
      intro index inBounds inside; unfold byteRange at inside; omega) (by
      intro values word member index inBounds inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> unfold byteRange at inside <;> omega)
  have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args savedValues) := by
    intro word member
    exact (saved word member).of_writesOnlyWithin handoff.memory (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  exact ⟨childUsed, after, {
    trace := handoff.trace
    atPc := handoff.atPc
    stack := handoff.stack
    stdout := by simpa [childValue] using handoff.stdout
    stdin := handoff.stdin
    cursor := handoff.cursor
    exitCode := handoff.exitCode
    saved := savedAfter
    payloadContext := payloadAfter
    loaded := handoff.loaded
    access := handoff.access
    memory := writeSuccessChildFrame64_writes_writerFrame lower handoff.memory }⟩

set_option genInjectivity false in
/-- The three witness byte-list encoders in production order through `0x15960`. -/
structure WriteSuccessWitnessListsHandoff
    (fromStep nodesUsed codesUsed headersUsed : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (savedValues : DecodeCalleeSavedValues)
    (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep
    (4 + nodesUsed + 4 + codesUsed + 4 + headersUsed) before after
  atPc : EndpointPc after = some 0x15960
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeMany encodeBytes args.decoded.witnessNodes ++
    encodeMany encodeBytes args.decoded.witnessCodes ++
    encodeMany encodeBytes args.decoded.witnessHeaders
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args savedValues)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine

/-- Compose the three repeated witness byte-list calls. -/
private theorem writeSuccessWitnessListsHandoff
    (child : WriteSuccessByteListsInstanceContract) (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (savedValues : DecodeCalleeSavedValues)
    (before : EndpointState) (atPc : before.machine.regs.get? PC = some 0x15930)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args savedValues))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ nodesUsed codesUsed headersUsed after,
      WriteSuccessWitnessListsHandoff fromStep nodesUsed codesUsed headersUsed args payloadBytes
        savedValues before after := by
  obtain ⟨nodesUsed, s1, h1⟩ := writeSuccessLateByteListsSite child fromStep
    0x15930 0x15940 0x18 0x10 0x2d8 args payloadBytes args.decoded.witnessNodes
    savedValues before
    atPc stack context.witnessNodesRep context saved access loaded aligned lower upper decodedAddress
    (writeSuccessLateSliceSteps(args; 0x15930, 0x15940, 0x15c10, 0x18, 0x10,
      0x15938; 0x03, 0x35, 0x81, 0x01;
      0x83, 0x35, 0x01, 0x01; 0xe7, 0x80, 0x80, 0x2d; 0x2d8))
    (by native_decide) (by native_decide)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨codesUsed, s2, h2⟩ := writeSuccessLateByteListsSite child
    (fromStep + 4 + nodesUsed) 0x15940 0x15950 0x28 0x20 0x2c8
    args payloadBytes args.decoded.witnessCodes savedValues s1
    (by simpa [EndpointPc, MachinePc] using h1.atPc) h1.stack h1.payloadContext.witnessCodesRep
    h1.payloadContext h1.saved h1.access h1.loaded aligned lower upper decodedAddress
    (writeSuccessLateSliceSteps(args; 0x15940, 0x15950, 0x15c10, 0x28, 0x20,
      0x15948; 0x03, 0x35, 0x81, 0x02;
      0x83, 0x35, 0x01, 0x02; 0xe7, 0x80, 0x80, 0x2c; 0x2c8))
    (by native_decide) (by native_decide)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨headersUsed, s3, h3⟩ := writeSuccessLateByteListsSite child
    (fromStep + 4 + nodesUsed + 4 + codesUsed) 0x15950 0x15960 0x38 0x30 0x2b8
    args payloadBytes args.decoded.witnessHeaders savedValues s2
    (by simpa [EndpointPc, MachinePc] using h2.atPc) h2.stack h2.payloadContext.witnessHeadersRep
    h2.payloadContext h2.saved h2.access h2.loaded aligned lower upper decodedAddress
    (writeSuccessLateSliceSteps(args; 0x15950, 0x15960, 0x15c10, 0x38, 0x30,
      0x15958; 0x03, 0x35, 0x81, 0x03;
      0x83, 0x35, 0x01, 0x03; 0xe7, 0x80, 0x80, 0x2b; 0x2b8))
    (by native_decide) (by native_decide)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have memory1 : WriteSuccessMemoryFrame args before.machine s1.machine :=
    h1.memory
  have memory2 : WriteSuccessMemoryFrame args s1.machine s2.machine :=
    h2.memory
  have memory3 : WriteSuccessMemoryFrame args s2.machine s3.machine :=
    h3.memory
  have memory12 := WritesOnlyWithin.trans_same memory1 memory2
  have memory123 := WritesOnlyWithin.trans_same memory12 memory3
  refine ⟨nodesUsed, codesUsed, headersUsed, s3, {
    trace := ?_
    atPc := h3.atPc
    stack := h3.stack
    stdout := ?_
    stdin := h3.stdin.trans (h2.stdin.trans h1.stdin)
    cursor := h3.cursor.trans (h2.cursor.trans h1.cursor)
    exitCode := h3.exitCode.trans (h2.exitCode.trans h1.exitCode)
    saved := h3.saved
    payloadContext := h3.payloadContext
    loaded := h3.loaded
    access := h3.access
    memory := memory123 }⟩
  · have t2 := h1.trace.append (by simpa [Nat.add_assoc] using h2.trace)
    simpa only [Nat.add_assoc] using
      t2.append (by simpa only [Nat.add_assoc] using h3.trace)
  · rw [h3.stdout, h2.stdout, h1.stdout]

/-- Production `0x15960: ld a0,0x40(sp)`, loading the linked chain ID. -/
private theorem writeSuccessChainIdLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x15960)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x40)
      args.decoded.chainConfig.chainId)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15960 retired x10
        (BitVec.ofNat 64 args.decoded.chainConfig.chainId)) false := by
  exact writeSuccessLateSliceLoadStep stepNo 0x15960 0x40 args.decoded.chainConfig.chainId
    (.Regidx 10#5) x10 (BitVec.ofNat 64 args.decoded.chainConfig.chainId)
    0x03 0x35 0x01 0x04 args state access atPc stack rep (by omega) (by omega) loaded
    (fun premise => wX_x10_run premise _) (by native_decide)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured; decode_run)
    (by native_decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)

/-- Production `0x15964: auipc ra,0`. -/
private theorem writeSuccessChainIdCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15964)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15964 retired x1 0x15964) false :=
  writeSuccessLateSliceCallBaseStep stepNo 0x15964 state configured atPc loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured; decode_run)

/-- Production `0x15968: jalr ra,0x3ac(ra)`, entering the shared integer encoder. -/
private theorem writeSuccessChainIdCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15968)
    (base : state.regs.get? x1 = some 0x15964)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x15968 0x15d10 x1 0x1596c)
        0x15d10 retired) false :=
  writeSuccessLateSliceCallStep stepNo 0x15968 0x15d10 0x1596c 0x3ac
    0xe7 0x80 0xc0 0x3a state configured atPc base loaded (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by rfl)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured; decode_run)
    (by native_decide) (by native_decide) (by native_decide)

set_option genInjectivity false in
/-- Chain ID encoded through the exact `0x15960..0x15968` parent sequence. -/
structure WriteSuccessChainIdHandoff
    (fromStep childUsed : Nat) (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (savedValues : DecodeCalleeSavedValues) (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (3 + childUsed) before after
  atPc : EndpointPc after = some 0x1596c
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeNatLE 8 args.decoded.chainConfig.chainId
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args savedValues)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine

private theorem writeSuccessChainIdHandoff
    (child : WriteSuccessIntInstanceContract) (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (savedValues : DecodeCalleeSavedValues)
    (before : EndpointState) (atPc : before.machine.regs.get? PC = some 0x15960)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args savedValues))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessChainIdHandoff fromStep childUsed args payloadBytes savedValues before after := by
  obtain ⟨childUsed, after, handoff⟩ := writeSuccessIntCallHandoff child fromStep
    0x15960 0x1596c 0x40 args.decoded.chainConfig.chainId 0x15964 args before atPc stack
    context.chainIdRep access loaded aligned lower upper
    (fun step state => writeSuccessChainIdLoadStep step args state)
    writeSuccessChainIdCallBaseStep writeSuccessChainIdCallStep
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have payloadAfter := writeSuccessPayloadContextAfterInt decodedAddress lower upper context handoff
  have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args savedValues) := by
    intro word member
    exact (saved word member).of_writesOnlyWithin handoff.memory (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  exact ⟨childUsed, after, {
    trace := handoff.trace
    atPc := handoff.atPc
    stack := handoff.stack
    stdout := handoff.stdout
    stdin := handoff.stdin
    cursor := handoff.cursor
    exitCode := handoff.exitCode
    saved := savedAfter
    payloadContext := payloadAfter
    loaded := handoff.loaded
    access := handoff.access
    memory := writeSuccessChildFrame_writes_writerFrame lower handoff.memory }⟩

/-- Production `0x1596c: ld s0,0x48(sp)`, loading the optional fork-name pointer. -/
private theorem writeSuccessForkNamePointerLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x1596c)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x48) address)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1596c retired x8 (BitVec.ofNat 64 address)) false := by
  exact writeSuccessLateSliceLoadStep stepNo 0x1596c 0x48 address (.Regidx 8#5) x8
    (BitVec.ofNat 64 address) 0x03 0x34 0x81 0x04 args state access atPc stack rep
    (by omega) (by omega) loaded (fun premise => wX_x8_run premise _) (by native_decide)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured; decode_run)
    (by native_decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- Decode the pinned fork-name null test at `0x15970`. -/
private theorem writeSuccessForkNameBranchDecode (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    Runs (ext_decode (fetchWord 0x63#8 0x02#8 0x04#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x024, .Regidx 0#5, .Regidx 8#5, .BEQ)) := by
  obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
    writeSuccessLoadDecodeReads configured
  decode_run

/-- Production `0x15970: beqz s0,0x15994`, on a present fork name. -/
private theorem writeSuccessForkNamePresentBranchStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15970)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (condition : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 8#5) .BEQ)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15970)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15970) false) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15970)
        0x15974 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext 0x15970 atPc trivial
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x15970 (by native_decide) loadedAfter
    0x63 0x02 0x04 0x02 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  refine ⟨retired, tryStepBranchNotTakenRetires stepNo state 0x15970 retired 0x024
    (.Regidx 0#5) (.Regidx 8#5) .BEQ 0 0 0x63 0x02 0x04 0x02 platform noMMIO bytes
    interrupts (by rfl) (writeSuccessForkNameBranchDecode state configured) notExpected condition
    counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1
    counters.2.2.2.2.2⟩

/-- Production `0x15970: beqz s0,0x15994`, on an absent fork name. -/
private theorem writeSuccessForkNameAbsentBranchStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15970)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (condition : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 8#5) .BEQ)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15970)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15970) true) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x15970 0x15994)
        0x15994 retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext 0x15970 atPc trivial
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x15970 (by native_decide) loadedAfter
    0x63 0x02 0x04 0x02 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have pcRead : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15970)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15970) 0x15970 := by
    apply readReg_run
    simp [coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  cases misaRead : state.regs.get? misa with
  | none =>
      have impossible := configured.normal.2.2.2.2.2.2.2.2.2.2.2
      simp [misaRead] at impossible
  | some misaBits =>
      have zca := currentlyEnabledZca_run_atStepPremise state 0x15970 misaBits misaRead
      refine ⟨retired, ?_⟩
      simpa only [show (0x15970 : BitVec 64) + sign_extend (m := 64) (0x024 : BitVec 13) =
          0x15994 by native_decide] using
        (tryStepBranchTakenRetires stepNo state 0x15970 0x15970 retired 0x024
          (.Regidx 0#5) (.Regidx 8#5) .BEQ 0 0 0x63 0x02 0x04 0x02
          (_get_Misa_C misaBits == 1#1) platform noMMIO bytes interrupts (by rfl)
          (writeSuccessForkNameBranchDecode state configured) notExpected condition pcRead
          (by native_decide) (by native_decide) zca counters.1 counters.2.1 counters.2.2.1
          counters.2.2.2.1 counters.2.2.2.2.1 counters.2.2.2.2.2)

private theorem writeSuccessForkNameCondition (state : State) (value : BitVec 64)
    (valueAt : state.regs.get? x8 = some value) :
    Runs (bTypeTaken (.Regidx 0#5) (.Regidx 8#5) .BEQ) state state (value == 0) := by
  unfold bTypeTaken
  refine Runs.bind (rX_x8_run state value valueAt) ?_
  refine Runs.bind (rX_x0_run state) ?_
  rfl

/-- Execute either pinned `li a0,0/1` used by the fork-name encoder routes. -/
private theorem writeSuccessForkNameBooleanLiteralStep
    (stepNo pc value : Nat) (imm : BitVec 12)
    (byte2 : UInt8) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (resultEq : iTypeResult .ADDI imm 0 = BitVec.ofNat 64 value)
    (decode : Runs (ext_decode (fetchWord 0x13 0x05 (BitVec.ofNat 8 byte2.toNat) 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (imm, .Regidx 0#5, .Regidx 10#5, .ADDI)))
    (pcFits : pc < 2 ^ 64)
    (read0 : Artifacts.programImage.readFileByte? pc = some 0x13 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some 0x05 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some 0x00 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x10
        (BitVec.ofNat 64 value)) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have execute : Runs (execute (.ITYPE (imm, .Regidx 0#5, .Regidx 10#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x10 (BitVec.ofNat 64 value) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE imm (.Regidx 0#5) (.Regidx 10#5) .ADDI) _ _ _
    simpa only [resultEq] using execute_ITYPE_run premise _ imm (.Regidx 0#5)
      (.Regidx 10#5) .ADDI 0 (rX_x0_run premise)
      (wX_x10_run premise (iTypeResult .ADDI imm 0))
  exact configuredRegisterWriteStep stepNo pc state x10 (BitVec.ofNat 64 value)
    (.ITYPE (imm, .Regidx 0#5, .Regidx 10#5, .ADDI)) 0x13 0x05 byte2 0x00
    configured atPc loaded decode execute (pcFits := pcFits) (base := by rfl)
    (read0 := read0) (read1 := read1) (read2 := read2) (read3 := read3)

private theorem writeSuccessForkNamePresentBooleanStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15974)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15974 retired x10 1) false := by
  apply writeSuccessForkNameBooleanLiteralStep stepNo 0x15974 1 1 0x10 state
    configured atPc loaded (by native_decide) (by
      obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
        writeSuccessLoadDecodeReads configured
      decode_run) (by native_decide)

private theorem writeSuccessForkNameAbsentBooleanStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15994)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15994 retired x10 0) false := by
  apply writeSuccessForkNameBooleanLiteralStep stepNo 0x15994 0 0 0x00 state
    configured atPc loaded (by native_decide) (by
      obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
        writeSuccessLoadDecodeReads configured
      decode_run) (by native_decide)

private theorem writeSuccessForkNamePresentBooleanCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15978)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15978 retired x1 0x15978) false := by
  apply writeSuccessLateSliceCallBaseStep stepNo 0x15978 state configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

private theorem writeSuccessForkNamePresentBooleanCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x1597c)
    (base : state.regs.get? x1 = some 0x15978)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x1597c 0x15b9c x1 0x15980)
        0x15b9c retired) false := by
  apply writeSuccessLateSliceCallStep stepNo 0x1597c 0x15b9c 0x15980 0x224
    0xe7 0x80 0x40 0x22 state configured atPc base loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

private theorem writeSuccessForkNameAbsentBooleanCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15998)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15998 retired x1 0x15998) false := by
  apply writeSuccessLateSliceCallBaseStep stepNo 0x15998 state configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

private theorem writeSuccessForkNameAbsentBooleanCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x1599c)
    (base : state.regs.get? x1 = some 0x15998)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x1599c 0x15b9c x1 0x159a0)
        0x15b9c retired) false := by
  apply writeSuccessLateSliceCallStep stepNo 0x1599c 0x15b9c 0x159a0 0x204
    0xe7 0x80 0x40 0x20 state configured atPc base loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x15980: mv a0,s0` on the present fork-name route. -/
private theorem writeSuccessForkNameBytesAddressStep (stepNo : Nat) (state : State)
    (address : Nat) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15980)
    (source : state.regs.get? x8 = some (BitVec.ofNat 64 address))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15980 retired x10 (BitVec.ofNat 64 address)) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x15980
  have source' := (stepPremiseState_writes state 0x15980).get x8 (by decide) |>.trans source
  have resultEq : iTypeResult .ADDI 0 (BitVec.ofNat 64 address) =
      BitVec.ofNat 64 address := by
    simp [iTypeResult, show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
  have execute : Runs (execute (.ITYPE (0, .Regidx 8#5, .Regidx 10#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x10 (BitVec.ofNat 64 address) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 8#5) (.Regidx 10#5) .ADDI) _ _ _
    simpa only [resultEq] using execute_ITYPE_run premise _ 0 (.Regidx 8#5)
      (.Regidx 10#5) .ADDI (BitVec.ofNat 64 address)
      (rX_x8_run premise (BitVec.ofNat 64 address) source')
      (wX_x10_run premise (iTypeResult .ADDI 0 (BitVec.ofNat 64 address)))
  exact configuredRegisterWriteStep stepNo 0x15980 state x10 (BitVec.ofNat 64 address)
    (.ITYPE (0, .Regidx 8#5, .Regidx 10#5, .ADDI)) 0x13 0x05 0x04 0x00
    configured atPc loaded (by
      obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
        writeSuccessLoadDecodeReads configured
      decode_run) execute (base := by rfl)

/-- Production `0x15984: ld a1,8(sp)` on the present fork-name route. -/
private theorem writeSuccessForkNameBytesLengthStep (stepNo : Nat) (state : State)
    (args : WriteSuccessArgs) (length : Nat) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x15984)
    (stack : state.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x08) length)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15984 retired x11 (BitVec.ofNat 64 length)) false := by
  exact writeSuccessLateSliceLoadStep stepNo 0x15984 0x08 length (.Regidx 11#5) x11
    (BitVec.ofNat 64 length) 0x83 0x35 0x81 0x00 args state access atPc stack rep
    (by omega) (by omega) loaded (fun premise => wX_x11_run premise _)
    (by native_decide)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured; decode_run)
    (by native_decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- Production `0x15988: auipc ra,0` before the fork-name bytes child. -/
private theorem writeSuccessForkNameBytesCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15988)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15988 retired x1 0x15988) false := by
  apply writeSuccessLateSliceCallBaseStep stepNo 0x15988 state configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x1598c: jalr 0x2e4(ra)` into the fork-name bytes child. -/
private theorem writeSuccessForkNameBytesCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x1598c)
    (base : state.regs.get? x1 = some 0x15988)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x1598c 0x15c6c x1 0x15990)
        0x15c6c retired) false := by
  apply writeSuccessLateSliceCallStep stepNo 0x1598c 0x15c6c 0x15990 0x2e4
    0xe7 0x80 0x40 0x2e state configured atPc base loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x15990: j 0x159a0`, reconverging after the fork-name bytes child. -/
private theorem writeSuccessForkNameJoinStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15990)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x15990 0x159a0)
        0x159a0 retired) false := by
  apply configuredJStep stepNo 0x15990 0x159a0 state 0x10
    0x6f 0x00 0x00 0x01 configured atPc loaded (base := by rfl)
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Compose either three-instruction fork-name boolean call with the selected shared child. -/
private theorem writeSuccessForkNameBooleanCallHandoff
    (child : WriteSuccessBooleanInstanceContract) (fromStep pc returnPc callBase : Nat)
    (value : Bool) (x8Value : BitVec 64) (args : WriteSuccessArgs) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (x8Reg : before.machine.regs.get? x8 = some x8Value)
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (lower : 0x880 ≤ args.stackPointer) (upper : args.stackPointer < 2 ^ 64)
    (literalStep : ∀ stepNo state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 pc) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x10
          (if value then 1 else 0)) false)
    (baseStep : ∀ stepNo state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 (pc + 4)) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 (pc + 4)) retired x1
          (BitVec.ofNat 64 callBase)) false)
    (callStep : ∀ stepNo state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 (pc + 8)) →
      state.regs.get? x1 = some (BitVec.ofNat 64 callBase) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 (pc + 8)) 0x15b9c x1 (BitVec.ofNat 64 returnPc))
          0x15b9c retired) false)
    (owned0 : writeSuccessParentPc (BitVec.ofNat 64 pc))
    (owned1 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 4)))
    (owned2 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 8)))
    (notExit0 : BitVec.ofNat 64 pc ≠ 0x15b9c)
    (notExit1 : BitVec.ofNat 64 (pc + 4) ≠ 0x15b9c)
    (notExit2 : BitVec.ofNat 64 (pc + 8) ≠ 0x15b9c)
    (next0 : Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4 = BitVec.ofNat 64 (pc + 4))
    (next1 : Sail.BitVec.addInt (BitVec.ofNat 64 (pc + 4)) 4 = BitVec.ofNat 64 (pc + 8))
    (returnListed : returnPc ∈ Elflings.writeSuccessBooleanExitPcs) :
    ∃ childUsed after,
      WriteSuccessEncoderChildHandoff Bool fromStep 3 childUsed 16 returnPc
        (EncoderCallInstanceContract.stepBound child)
        (fun flag => #[if flag then 1 else 0]) value args before before after ∧
      after.machine.regs.get? x8 = before.machine.regs.get? x8 := by
  let valueBits : BitVec 64 := if value then 1 else 0
  have seg0 : Seg writeSuccessParentPc (fun target => target = 0x15b9c)
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩, ⟨x8, x8Value⟩]
      fromStep 0 before.machine before.machine (BitVec.ofNat 64 pc) := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by
      intro pair member
      simp at member
      rcases member with rfl | rfl
      · exact stack
      · exact x8Reg }
  obtain ⟨retired0, run0⟩ := literalStep fromStep before.machine access.configured atPc loaded
  have seg1 := seg0.stepKnown owned0 notExit0 x10 valueBits
    (BitVec.ofNat 64 (pc + 4)) retired0 run0 next0 (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite before.machine (BitVec.ofNat 64 pc) retired0 x10 valueBits).mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨baseMachine, seg2⟩ := seg1.step owned1 notExit1 x1
    (BitVec.ofNat 64 callBase) (BitVec.ofNat 64 (pc + 8))
    (baseStep (fromStep + 1) _ access1.configured seg1.atPc loaded1)
    next1 (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg access seg2
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully baseMachine.mem := by
    simpa [seg2.memEq (by simp)] using loaded
  obtain ⟨retired2, callRun⟩ := callStep (fromStep + 2) baseMachine access2.configured
    seg2.atPc (seg2.reg x1 (BitVec.ofNat 64 callBase) (by simp)) loaded2
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement baseMachine) (BitVec.ofNat 64 (pc + 8))
      0x15b9c x1 (BitVec.ofNat 64 returnPc)) 0x15b9c retired2
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes baseMachine (BitVec.ofNat 64 (pc + 8))
    0x15b9c retired2 x1 (BitVec.ofNat 64 returnPc)
  have callAtPc : callMachine.regs.get? PC = some 0x15b9c := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callMemEq : callMachine.mem = before.machine.mem := by
    have one : callMachine.mem = baseMachine.mem := by
      change
        (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement baseMachine)
            (BitVec.ofNat 64 (pc + 8)) 0x15b9c x1 (BitVec.ofNat 64 returnPc))
          0x15b9c retired2).mem = baseMachine.mem
      rw [tryStepControlFlowAfterRetired_mem]
      change (controlFlowJumpState (tryStepControlFlowAfterIncrement baseMachine)
        (BitVec.ofNat 64 (pc + 8)) 0x15b9c).mem = baseMachine.mem
      rw [controlFlowJumpState_mem]
      rfl
    exact one.trans (seg2.memEq (by simp))
  let childArgs : EncoderCallArgs Bool := {
    returnAddress := returnPc
    callerStack := args.stackPointer - 0x7d0
    inputSize := args.inputSize
    value }
  have childEntry : EncoderCallEntry Elflings.writeSuccessBooleanEntry
      Elflings.writeSuccessBooleanExitPcs BooleanEncoderBinding childArgs callState := by
    refine ⟨returnListed, writeSuccessChildStackBound upper, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [callState] using callAtPc
    · simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, childArgs]
    · exact (callWrites.get x2 (by decide)).trans
        (seg2.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    · exact (callWrites.get x10 (by decide)).trans
        (seg2.reg x10 valueBits (by simp [valueBits]))
    · simpa [callState, callMemEq] using loaded
  have callPrefix : ConfinedPrefix writeSuccessParentPc (fun target => target = 0x15b9c)
      (fun _ _ _ _ _ => False) (fromStep + 2) 1 baseMachine callMachine :=
    ConfinedPrefix.ownStep seg2.atPc
      owned2 notExit2 callRun
  have callEnd : ScopedTrace writeSuccessParentPc (fun target => target = 0x15b9c)
      (fun _ _ _ _ _ => False) (fromStep + 3) 0 callMachine callMachine :=
    .exitAt _ _ 0x15b9c callAtPc rfl
  have parentMachineTrace := seg2.confined.trans callPrefix 0 callMachine callEnd
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 3 before callState := by
    simpa [callState] using liftWriteSuccessParentTrace before parentMachineTrace
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have accessCall : WriteSuccessMachineAccess args callMachine := {
    configured := configuredAfterWriteSuccessCall (BitVec.ofNat 64 (pc + 8)) 0x15b9c
      (BitVec.ofNat 64 returnPc) retired2 access2.configured
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access2.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access2.frameStore offset width bound)
    frameNoMMIO := access2.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access2.decodedLoad offset width bound)
    decodedNoMMIO := access2.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq callPmaEq access2.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq callPmaEq access2.outputLengthStore
    writerRegionBeforeOutputContext := access2.writerRegionBeforeOutputContext
    frameNotCode := access2.frameNotCode }
  have insideWriter : ∀ {pc},
      pcInRanges Elflings.writeSuccessBooleanExecutionPcRanges pc →
      pcInRanges Elflings.writeSuccessExecutionPcRanges pc := fun inside => by
    unfold pcInRanges at inside ⊢
    rcases inside with ⟨range, member, lo, hi⟩
    simp [Elflings.writeSuccessBooleanExecutionPcRanges] at member
    rcases member with rfl | rfl
    · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
    · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
        by omega, by omega⟩
  obtain ⟨childUsed, after, unit, positive, bounded, childTrace, exitPc, allowed,
      childExit⟩ := EncoderCallInstanceContract.implements child childArgs
        (fromStep + 3) callState childEntry
  rcases childExit with ⟨afterPc, stdout, stdin, cursor, exitCode, _frameFits, childMemory,
    childFrame⟩
  have childTrace' := childTrace.weaken (fun _ pc => insideWriter pc)
  have memory : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 - 16) 16)
      before.machine after.machine := by
    intro address outside
    rw [childMemory address (by simpa [childArgs] using outside), callMemEq]
  have pmaEq := childFrame.1 pma_regions (by simp [abiCalleePreserved])
  have accessAfter : WriteSuccessMachineAccess args after.machine := {
    configured := configuredAfterEndpointCall accessCall.configured childFrame
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (accessCall.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (accessCall.frameStore offset width bound)
    frameNoMMIO := accessCall.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (accessCall.decodedLoad offset width bound)
    decodedNoMMIO := accessCall.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq accessCall.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq accessCall.outputLengthStore
    writerRegionBeforeOutputContext := accessCall.writerRegionBeforeOutputContext
    frameNotCode := accessCall.frameNotCode }
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem := by
    intro address byte fileByte
    have outside : ¬byteRange (args.stackPointer - 0x7d0 - 16) 16 address := by
      intro inside
      have inWriter := writeSuccessChildFrame_mem_frame lower inside
      unfold byteRange at inWriter
      have notCode := accessCall.frameNotCode address inWriter.1 (by omega)
      exact Option.some_ne_none byte (fileByte.symm.trans notCode)
    rw [memory address outside]
    exact loaded address byte fileByte
  have x8Preserved : after.machine.regs.get? x8 = before.machine.regs.get? x8 :=
    (childFrame.1 x8 (by simp [abiCalleePreserved])).trans
      ((callWrites.get x8 (by simp [stepBookkeeping])).trans
        ((seg2.reg x8 x8Value (by simp)).trans x8Reg.symm))
  exact ⟨childUsed, after, {
    trace := by
      have all := parentTrace.append (by simpa [Nat.add_assoc] using childTrace')
      simpa [Nat.add_assoc] using all
    childBounded := by simpa [encoderCallContract, childArgs] using bounded
    atPc := by simpa [childArgs] using afterPc
    stack := by
      have preserved := childFrame.1 x2 (by simp [abiCalleePreserved])
      simpa [childArgs] using preserved.trans childEntry.2.2.2.2.1
    stdout := by simpa [childArgs] using stdout
    stdin := by simpa [callState] using stdin
    cursor := by simpa [callState] using cursor
    exitCode := by simpa [callState] using exitCode
    memory := memory
    calleeX8 := x8Preserved
    loaded := loadedAfter
    access := accessAfter }, x8Preserved⟩

set_option genInjectivity false in
/-- The exact fork-name pointer load and null branch, retaining the writer context. -/
structure WriteSuccessForkNameBranchHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues)
    (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 2 before after
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  stdout : after.stdout = before.stdout
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  route :
    (args.decoded.chainConfig.forkName = none ∧ EndpointPc after = some 0x15994 ∧
      after.machine.regs.get? x8 = some 0) ∨
    (∃ bytes address,
      args.decoded.chainConfig.forkName = some bytes ∧ address ≠ 0 ∧
      EndpointPc after = some 0x15974 ∧
      after.machine.regs.get? x8 = some (BitVec.ofNat 64 address) ∧
      UIntRep 8 after.machine.mem (args.stackPointer - 0x7d0 + 0x48) address ∧
      UIntRep 8 after.machine.mem (args.stackPointer - 0x7d0 + 0x08) bytes.size ∧
      ArrayRep 1 (fun mem address byte => UIntRep 1 mem address byte.toNat)
        after.machine.mem address bytes)

private theorem writeSuccessForkNameBranchHandoff
    (fromStep : Nat) (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (atPc : EndpointPc before = some 0x1596c)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ after, WriteSuccessForkNameBranchHandoff fromStep args payloadBytes values before after := by
  have seg0 : Seg writeSuccessParentPc (fun pc => pc = 0x15994 ∨ pc = 0x15974)
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine 0x1596c := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  cases optionEq : args.decoded.chainConfig.forkName with
  | none =>
      have pointerRep : UIntRep 8 before.machine.mem
          (args.stackPointer - 0x7d0 + 0x48) 0 := by
        simpa [WriteSuccessSeparatedOptionalByteSliceRep, optionEq] using context.forkNameRep
      obtain ⟨retired0, run0⟩ := writeSuccessForkNamePointerLoadStep (address := 0)
        fromStep args before.machine access atPc stack pointerRep aligned loaded
      have seg1 := seg0.stepKnown
        (by unfold writeSuccessParentPc; exact
          ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
        (by simp) x8 0 0x15970 retired0 run0 (by native_decide)
        (by intro r h; exact Or.inl h) (by simp [writeSuccessParentWrites])
        (by native_decide) (by native_decide) (by simp [RegsOutside, stepBookkeeping])
      have premiseX8 :
          (coreControlFlowNextState
            (tryStepControlFlowAfterIncrement
              (afterRegisterWrite before.machine 0x1596c retired0 x8 0)) 0x15970).regs.get? x8 =
            some 0 := by
        simpa [coreControlFlowNextState, tryStepControlFlowAfterIncrement,
          Std.ExtDHashMap.get?_insert] using seg1.reg x8 0 (by simp)
      have condition := writeSuccessForkNameCondition _ 0 premiseX8
      obtain ⟨final, seg2⟩ := seg1.stepJump 0x15994
        (by unfold writeSuccessParentPc; exact
          ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
        (by simp)
        (writeSuccessForkNameAbsentBranchStep (fromStep + 1) _
          (writeSuccessAccessOfSeg access seg1).configured seg1.atPc
          (by simpa [seg1.memEq (by simp)] using loaded) (by simpa using condition))
        (by intro r h; exact Or.inl h) (by simp [RegsOutside, stepBookkeeping])
      let after : EndpointState := { before with machine := final }
      have machineTrace := seg2.confined 0 final
        (.exitAt (fromStep + 2) final 0x15994 seg2.atPc (Or.inl rfl))
      have memEq : final.mem = before.machine.mem := seg2.memEq (by simp)
      exact ⟨after, {
        trace := by simpa [after] using liftWriteSuccessParentTrace before machineTrace
        stack := by simpa [after] using seg2.reg x2 _ (by simp)
        stdin := rfl
        cursor := rfl
        stdout := rfl
        exitCode := rfl
        saved := by
          intro word member
          exact (saved word member).of_writesOnlyWithin seg2.mem (by
            intro _ _ inside
            exact inside.elim)
        payloadContext := by
          apply writeSuccessPayloadContextAfterChild decodedAddress lower upper
            access.writerRegionBeforeOutputContext context seg2.mem
          all_goals simp
        loaded := by simpa [after, memEq] using loaded
        access := by simpa [after] using writeSuccessAccessOfSeg access seg2
        route := Or.inl ⟨optionEq, by
          change final.regs.get? PC = some 0x15994
          exact seg2.atPc, by
          change final.regs.get? x8 = some 0
          exact seg2.reg x8 0 (by simp)⟩ }⟩
  | some bytes =>
      have forkNameRep := context.forkNameRep
      rw [optionEq] at forkNameRep
      change ∃ data : Nat, data ≠ 0 ∧
        UIntRep 8 before.machine.mem (args.stackPointer - 0x7d0 + 0x48) data ∧
        UIntRep 8 before.machine.mem (args.stackPointer - 0x7d0 + 0x08) bytes.size ∧
        ArrayRep 1 (fun mem address byte => UIntRep 1 mem address byte.toNat)
          before.machine.mem data bytes at forkNameRep
      obtain ⟨address, nonzero, pointerRep, countRep, arrayRep⟩ := forkNameRep
      obtain ⟨retired0, run0⟩ := writeSuccessForkNamePointerLoadStep (address := address)
        fromStep args before.machine access atPc stack pointerRep aligned loaded
      have seg1 := seg0.stepKnown
        (by unfold writeSuccessParentPc; exact
          ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
        (by simp) x8 (BitVec.ofNat 64 address) 0x15970 retired0 run0 (by native_decide)
        (by intro r h; exact Or.inl h) (by simp [writeSuccessParentWrites])
        (by native_decide) (by native_decide) (by simp [RegsOutside, stepBookkeeping])
      have addressBits : BitVec.ofNat 64 address ≠ 0 := by
        intro zero
        have addressBound : address < 2 ^ 64 := by
          simpa using pointerRep.1
        apply nonzero
        have equalNat := congrArg BitVec.toNat zero
        simpa [Nat.mod_eq_of_lt addressBound] using equalNat
      have premiseX8 :
          (coreControlFlowNextState
            (tryStepControlFlowAfterIncrement
              (afterRegisterWrite before.machine 0x1596c retired0 x8
                (BitVec.ofNat 64 address))) 0x15970).regs.get? x8 =
            some (BitVec.ofNat 64 address) := by
        simpa [coreControlFlowNextState, tryStepControlFlowAfterIncrement,
          Std.ExtDHashMap.get?_insert] using
            seg1.reg x8 (BitVec.ofNat 64 address) (by simp)
      have condition := writeSuccessForkNameCondition _ (BitVec.ofNat 64 address) premiseX8
      have conditionFalse : (BitVec.ofNat 64 address == 0) = false := by
        exact beq_eq_false_iff_ne.mpr addressBits
      rw [conditionFalse] at condition
      obtain ⟨final, seg2⟩ := seg1.stepFallThrough 0x15974
        (by unfold writeSuccessParentPc; exact
          ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
        (by simp)
        (writeSuccessForkNamePresentBranchStep (fromStep + 1) _
          (writeSuccessAccessOfSeg access seg1).configured seg1.atPc
          (by simpa [seg1.memEq (by simp)] using loaded) condition)
        (by intro r h; exact Or.inl h) (by simp [RegsOutside, stepBookkeeping])
      let after : EndpointState := { before with machine := final }
      have machineTrace := seg2.confined 0 final
        (.exitAt (fromStep + 2) final 0x15974 seg2.atPc (Or.inr rfl))
      have memEq : final.mem = before.machine.mem := seg2.memEq (by simp)
      exact ⟨after, {
        trace := by simpa [after] using liftWriteSuccessParentTrace before machineTrace
        stack := by simpa [after] using seg2.reg x2 _ (by simp)
        stdin := rfl
        cursor := rfl
        stdout := rfl
        exitCode := rfl
        saved := by
          intro word member
          exact (saved word member).of_writesOnlyWithin seg2.mem (by
            intro _ _ inside
            exact inside.elim)
        payloadContext := by
          apply writeSuccessPayloadContextAfterChild decodedAddress lower upper
            access.writerRegionBeforeOutputContext context seg2.mem
          all_goals simp
        loaded := by simpa [after, memEq] using loaded
        access := by simpa [after] using writeSuccessAccessOfSeg access seg2
        route := Or.inr ⟨bytes, address, optionEq, nonzero,
          by change final.regs.get? PC = some 0x15974; exact seg2.atPc,
          by change final.regs.get? x8 = some (BitVec.ofNat 64 address)
             exact seg2.reg x8 _ (by simp),
          by simpa [after, memEq] using pointerRep,
          by simpa [after, memEq] using countRep,
          by simpa [after, memEq] using arrayRep⟩ }⟩

set_option genInjectivity false in
/-- The fork-name branch followed by its selected boolean child. -/
structure WriteSuccessForkNameBooleanHandoff
    (fromStep childUsed : Nat) (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (values : DecodeCalleeSavedValues) (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (5 + childUsed) before after
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  route :
    (args.decoded.chainConfig.forkName = none ∧ EndpointPc after = some 0x159a0 ∧
      after.stdout = before.stdout ++ #[0]) ∨
    (∃ bytes address,
      args.decoded.chainConfig.forkName = some bytes ∧ address ≠ 0 ∧
      EndpointPc after = some 0x15980 ∧
      after.stdout = before.stdout ++ #[1] ∧
      after.machine.regs.get? x8 = some (BitVec.ofNat 64 address) ∧
      UIntRep 8 after.machine.mem (args.stackPointer - 0x7d0 + 0x08) bytes.size ∧
      ArrayRep 1 (fun mem address byte => UIntRep 1 mem address byte.toNat)
        after.machine.mem address bytes)

/-- Consume the selected boolean encoder on both exact fork-name routes. -/
private theorem writeSuccessForkNameBooleanHandoff
    (child : WriteSuccessBooleanInstanceContract) (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues)
    (before : EndpointState) (atPc : EndpointPc before = some 0x1596c)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessForkNameBooleanHandoff fromStep childUsed args payloadBytes values
        before after := by
  obtain ⟨branched, branch⟩ := writeSuccessForkNameBranchHandoff fromStep args payloadBytes
    values before atPc stack context saved access loaded aligned lower upper decodedAddress
  rcases branch.route with absent | present
  · obtain ⟨optionEq, branchPc, x8Reg⟩ := absent
    obtain ⟨childUsed, after, boolean, _x8Preserved⟩ :=
      writeSuccessForkNameBooleanCallHandoff child
      (fromStep + 2) 0x15994 0x159a0 0x15998 false 0 args branched branchPc branch.stack
      x8Reg branch.access branch.loaded lower upper writeSuccessForkNameAbsentBooleanStep
      writeSuccessForkNameAbsentBooleanCallBaseStep writeSuccessForkNameAbsentBooleanCallStep
      (by unfold writeSuccessParentPc; exact
        ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    have payloadAfter := writeSuccessPayloadContextAfterChild decodedAddress lower upper
      boolean.access.writerRegionBeforeOutputContext branch.payloadContext boolean.memory
      (fun address inside => Or.inl (writeSuccessChildFrame_mem_frame lower inside))
      (by intro index bound inside; unfold byteRange at inside; omega)
      (by intro index bound inside; unfold byteRange at inside; omega)
      (by intro index bound inside; unfold byteRange at inside; omega)
      (by intro index bound inside; unfold byteRange at inside; rw [decodedAddress] at inside; omega)
      (by intro index bound inside; unfold byteRange at inside; rw [decodedAddress] at inside; omega)
      (by intro index bound inside; unfold byteRange at inside; omega)
      (by
        intro tailValues word member index bound inside
        simp [writeSuccessLocalTailWords] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;> unfold byteRange at inside <;> omega)
    have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
      intro word member
      exact (branch.saved word member).of_writesOnlyWithin boolean.memory (by
        intro index bound inside
        unfold byteRange at inside
        simp [writeSuccessSavedWords] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> omega)
    exact ⟨childUsed, after, {
      trace := by
        have all := branch.trace.append (by simpa [Nat.add_assoc] using boolean.trace)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all
      stack := boolean.stack
      stdin := boolean.stdin.trans branch.stdin
      cursor := boolean.cursor.trans branch.cursor
      exitCode := boolean.exitCode.trans branch.exitCode
      saved := savedAfter
      payloadContext := payloadAfter
      loaded := boolean.loaded
      access := boolean.access
      route := Or.inl ⟨optionEq, boolean.atPc, by
        calc
          after.stdout = branched.stdout ++ #[0] := by simpa using boolean.stdout
          _ = before.stdout ++ #[0] := by rw [branch.stdout]⟩ }⟩
  · obtain ⟨bytes, address, optionEq, nonzero, branchPc, addressReg, pointerRep,
      countRep, _arrayRep⟩ := present
    obtain ⟨childUsed, after, boolean, x8Preserved⟩ :=
      writeSuccessForkNameBooleanCallHandoff child
      (fromStep + 2) 0x15974 0x15980 0x15978 true (BitVec.ofNat 64 address) args branched
      branchPc branch.stack addressReg branch.access branch.loaded lower upper
      writeSuccessForkNamePresentBooleanStep
      writeSuccessForkNamePresentBooleanCallBaseStep writeSuccessForkNamePresentBooleanCallStep
      (by unfold writeSuccessParentPc; exact
        ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    have payloadAfter := writeSuccessPayloadContextAfterChild decodedAddress lower upper
      boolean.access.writerRegionBeforeOutputContext branch.payloadContext boolean.memory
      (fun address inside => Or.inl (writeSuccessChildFrame_mem_frame lower inside))
      (by intro index bound inside; unfold byteRange at inside; omega)
      (by intro index bound inside; unfold byteRange at inside; omega)
      (by intro index bound inside; unfold byteRange at inside; omega)
      (by intro index bound inside; unfold byteRange at inside; rw [decodedAddress] at inside; omega)
      (by intro index bound inside; unfold byteRange at inside; rw [decodedAddress] at inside; omega)
      (by intro index bound inside; unfold byteRange at inside; omega)
      (by
        intro tailValues word member index bound inside
        simp [writeSuccessLocalTailWords] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;> unfold byteRange at inside <;> omega)
    have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
      intro word member
      exact (branch.saved word member).of_writesOnlyWithin boolean.memory (by
        intro index bound inside
        unfold byteRange at inside
        simp [writeSuccessSavedWords] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> omega)
    have countAfter : UIntRep 8 after.machine.mem
        (args.stackPointer - 0x7d0 + 0x08) bytes.size :=
      countRep.of_writesOnlyWithin boolean.memory (by
        intro index bound inside; unfold byteRange at inside; omega)
    have pointerAfter : UIntRep 8 after.machine.mem
        (args.stackPointer - 0x7d0 + 0x48) address :=
      pointerRep.of_writesOnlyWithin boolean.memory (by
        intro index bound inside; unfold byteRange at inside; omega)
    have forkAfter := payloadAfter.forkNameRep
    rw [optionEq] at forkAfter
    change ∃ data : Nat, data ≠ 0 ∧
      UIntRep 8 after.machine.mem (args.stackPointer - 0x7d0 + 0x48) data ∧
      UIntRep 8 after.machine.mem (args.stackPointer - 0x7d0 + 0x08) bytes.size ∧
      ArrayRep 1 (fun mem address byte => UIntRep 1 mem address byte.toNat)
        after.machine.mem data bytes at forkAfter
    obtain ⟨semanticAddress, _semanticNonzero, semanticPointer, _semanticCount,
      semanticArray⟩ := forkAfter
    have addressEq : semanticAddress = address :=
      UIntRep.eight_unique semanticPointer pointerAfter
    have arrayAfter : ArrayRep 1 (fun mem address byte => UIntRep 1 mem address byte.toNat)
        after.machine.mem address bytes := by
      simpa [addressEq] using semanticArray
    exact ⟨childUsed, after, {
      trace := by
        have all := branch.trace.append (by simpa [Nat.add_assoc] using boolean.trace)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all
      stack := boolean.stack
      stdin := boolean.stdin.trans branch.stdin
      cursor := boolean.cursor.trans branch.cursor
      exitCode := boolean.exitCode.trans branch.exitCode
      saved := savedAfter
      payloadContext := payloadAfter
      loaded := boolean.loaded
      access := boolean.access
      route := Or.inr ⟨bytes, address, optionEq, nonzero, boolean.atPc,
        by
          calc
            after.stdout = branched.stdout ++ #[1] := by simpa using boolean.stdout
            _ = before.stdout ++ #[1] := by rw [branch.stdout],
        x8Preserved.trans addressReg,
        countAfter, arrayAfter⟩ }⟩

/-- Compose the present fork-name route's four parent instructions and selected bytes child. -/
private theorem writeSuccessForkNamePresentBytesHandoff
    (child : WriteSuccessBytesInstanceContract) (fromStep address : Nat)
    (args : WriteSuccessArgs) (payloadBytes bytes : Array UInt8)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (atPc : EndpointPc before = some 0x15980)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (addressReg : before.machine.regs.get? x8 = some (BitVec.ofNat 64 address))
    (countRep : UIntRep 8 before.machine.mem
      (args.stackPointer - 0x7d0 + 0x08) bytes.size)
    (arrayRep : ArrayRep 1 (fun mem address byte => UIntRep 1 mem address byte.toNat)
      before.machine.mem address bytes)
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessLateBytesHandoff fromStep childUsed 0x15990 bytes args payloadBytes
        before after values := by
  let exitPc : BitVec 64 → Prop := fun pc => pc = 0x15c6c
  have seg0 : Seg writeSuccessParentPc exitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
        ⟨x8, BitVec.ofNat 64 address⟩]
      fromStep 0 before.machine before.machine 0x15980 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by
      intro pair member
      simp at member
      rcases member with rfl | rfl
      · exact stack
      · exact addressReg }
  obtain ⟨retired0, run0⟩ := writeSuccessForkNameBytesAddressStep fromStep before.machine
    address access.configured atPc addressReg loaded
  have seg1 := seg0.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by simp [exitPc]) x10 (BitVec.ofNat 64 address) 0x15984 retired0 run0
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite before.machine 0x15980 retired0 x10
        (BitVec.ofNat 64 address)).mem := by
    simpa [seg1.memEq (by simp)] using loaded
  have countRep1 : UIntRep 8
      (afterRegisterWrite before.machine 0x15980 retired0 x10
        (BitVec.ofNat 64 address)).mem
      (args.stackPointer - 0x7d0 + 0x08) bytes.size := by
    simpa only [afterRegisterWrite_mem] using countRep
  obtain ⟨retired1, run1⟩ := writeSuccessForkNameBytesLengthStep (fromStep + 1) _ args
    bytes.size access1 seg1.atPc (seg1.reg x2 _ (by simp)) countRep1 aligned loaded1
  have seg2 := seg1.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by simp [exitPc]) x11 (BitVec.ofNat 64 bytes.size) 0x15988 retired1 run1
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg access seg2
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite
        (afterRegisterWrite before.machine 0x15980 retired0 x10 (BitVec.ofNat 64 address))
        0x15984 retired1 x11 (BitVec.ofNat 64 bytes.size)).mem := by
    simpa only [afterRegisterWrite_mem] using loaded
  obtain ⟨baseMachine, seg3⟩ := seg2.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by simp [exitPc]) x1 0x15988 0x1598c
    (writeSuccessForkNameBytesCallBaseStep (fromStep + 2) _ access2.configured seg2.atPc loaded2)
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access3 := writeSuccessAccessOfSeg access seg3
  have loaded3 : Artifacts.programImage.fileBytesLoadedFaithfully baseMachine.mem := by
    simpa [seg3.memEq (by simp)] using loaded
  obtain ⟨retired3, callRun⟩ := writeSuccessForkNameBytesCallStep (fromStep + 3)
    baseMachine access3.configured seg3.atPc (seg3.reg x1 0x15988 (by simp)) loaded3
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement baseMachine) 0x1598c 0x15c6c x1 0x15990)
    0x15c6c retired3
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes baseMachine 0x1598c 0x15c6c retired3 x1 0x15990
  have callAtPc : callMachine.regs.get? PC = some 0x15c6c := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callMemEq : callMachine.mem = before.machine.mem := by
    calc
      callMachine.mem = baseMachine.mem := by
        change (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement baseMachine)
            0x1598c 0x15c6c x1 0x15990) 0x15c6c retired3).mem = _
        rw [tryStepControlFlowAfterRetired_mem]
        change (controlFlowJumpState (tryStepControlFlowAfterIncrement baseMachine)
          0x1598c 0x15c6c).mem = _
        rw [controlFlowJumpState_mem]
        rfl
      _ = before.machine.mem := seg3.memEq (by simp)
  have callPrefix : ConfinedPrefix writeSuccessParentPc exitPc
      (fun _ _ _ _ _ => False) (fromStep + 3) 1 baseMachine callMachine :=
    ConfinedPrefix.ownStep seg3.atPc
      (by unfold writeSuccessParentPc; exact
        ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
      (by simp [exitPc]) callRun
  have callEnd : ScopedTrace writeSuccessParentPc exitPc
      (fun _ _ _ _ _ => False) (fromStep + 4) 0 callMachine callMachine :=
    .exitAt _ _ 0x15c6c callAtPc rfl
  have machineTrace := seg3.confined.trans callPrefix 0 callMachine callEnd
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 4 before callState := by
    simpa [callState] using liftWriteSuccessParentTrace before machineTrace
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have accessCall : WriteSuccessMachineAccess args callMachine := {
    configured := configuredAfterWriteSuccessCall 0x1598c 0x15c6c 0x15990 retired3
      access3.configured
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.frameStore offset width bound)
    frameNoMMIO := access3.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.decodedLoad offset width bound)
    decodedNoMMIO := access3.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq callPmaEq access3.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq callPmaEq access3.outputLengthStore
    writerRegionBeforeOutputContext := access3.writerRegionBeforeOutputContext
    frameNotCode := access3.frameNotCode }
  have setup : WriteSuccessSliceCallSetup fromStep 0x15980 0x15990 0x15c6c
      address bytes.size args before callState := {
    trace := parentTrace
    atPc := by simpa [callState, EndpointPc] using callAtPc
    link := by simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
    stack := by simpa [callState] using ((callWrites.get x2 (by decide)).trans
      (seg3.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)))
    address := by simpa [callState] using ((callWrites.get x10 (by decide)).trans
      (seg3.reg x10 (BitVec.ofNat 64 address) (by simp)))
    length := by simpa [callState] using ((callWrites.get x11 (by decide)).trans
      (seg3.reg x11 (BitVec.ofNat 64 bytes.size) (by simp)))
    memory := callMemEq
    stdin := rfl
    cursor := rfl
    stdout := rfl
    exitCode := rfl
    loaded := by simpa [callState, callMemEq] using loaded
    access := by simpa [callState] using accessCall }
  exact writeSuccessLateBytesHandoff child fromStep 0x15980 0x15990 address args payloadBytes
    bytes values before callState setup arrayRep.byteSliceBytesRep context saved lower upper
    decodedAddress (by native_decide)

/-- Production loads at `0x159a0/0x159a4`, retaining the public-key pointer and active-fork index. -/
private theorem writeSuccessPublicKeysPointerLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x159a0)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x60) address)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x159a0 retired x8 (BitVec.ofNat 64 address)) false := by
  exact writeSuccessLateSliceLoadStep stepNo 0x159a0 0x60 address (.Regidx 8#5) x8
    (BitVec.ofNat 64 address) 0x03 0x34 0x01 0x06 args state access atPc stack rep
    (by omega) (by omega) loaded (fun premise => wX_x8_run premise _) (by native_decide)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured; decode_run)
    (by native_decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by native_decide) (by native_decide) (by native_decide) (by native_decide)

private theorem writeSuccessActiveForkLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x159a4)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x50)
      args.decoded.chainConfig.activeForkIndex)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x159a4 retired x10
        (BitVec.ofNat 64 args.decoded.chainConfig.activeForkIndex)) false := by
  exact writeSuccessLateSliceLoadStep stepNo 0x159a4 0x50
    args.decoded.chainConfig.activeForkIndex (.Regidx 10#5) x10
    (BitVec.ofNat 64 args.decoded.chainConfig.activeForkIndex)
    0x03 0x35 0x01 0x05 args state access atPc stack rep (by omega) (by omega) loaded
    (fun premise => wX_x10_run premise _) (by native_decide)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured; decode_run)
    (by native_decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by native_decide) (by native_decide) (by native_decide) (by native_decide)

private theorem writeSuccessActiveForkCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x159a8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x159a8 retired x1 0x159a8) false :=
  writeSuccessLateSliceCallBaseStep stepNo 0x159a8 state configured atPc loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured; decode_run)

private theorem writeSuccessActiveForkCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x159ac)
    (base : state.regs.get? x1 = some 0x159a8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x159ac 0x15d10 x1 0x159b0)
        0x15d10 retired) false :=
  writeSuccessLateSliceCallStep stepNo 0x159ac 0x15d10 0x159b0 0x368
    0xe7 0x80 0x80 0x36 state configured atPc base loaded (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by rfl)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured; decode_run)
    (by native_decide) (by native_decide) (by native_decide)

/-- Production `0x159b0: addi a0,sp,0x128`. -/
private theorem writeSuccessActivationBlockSourceStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x159b0)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x159b0 retired x10
        (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x128))) false := by
  apply writeSuccessPayloadFieldSourceStep stepNo 0x159b0 0x128 0x128
    0x13 0x05 0x81 0x12 state (args.stackPointer - 0x7d0) configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x128#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  all_goals native_decide

private theorem writeSuccessActivationBlockCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x159b4)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x159b4 retired x1 0x159b4) false :=
  writeSuccessLateSliceCallBaseStep stepNo 0x159b4 state configured atPc loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured; decode_run)

private theorem writeSuccessActivationBlockCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x159b8)
    (base : state.regs.get? x1 = some 0x159b4)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x159b8 0x15bc8 x1 0x159bc)
        0x15bc8 retired) false :=
  writeSuccessLateSliceCallStep stepNo 0x159b8 0x15bc8 0x159bc 0x214
    0xe7 0x80 0x40 0x21 state configured atPc base loaded (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by rfl)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured; decode_run)
    (by native_decide) (by native_decide) (by native_decide)

/-- Production `0x159bc: addi a0,sp,0x118`. -/
private theorem writeSuccessActivationTimestampSourceStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x159bc)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x159bc retired x10
        (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x118))) false := by
  apply writeSuccessPayloadFieldSourceStep stepNo 0x159bc 0x118 0x118
    0x13 0x05 0x81 0x11 state (args.stackPointer - 0x7d0) configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x118#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  all_goals native_decide

private theorem writeSuccessActivationTimestampCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x159c0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x159c0 retired x1 0x159c0) false :=
  writeSuccessLateSliceCallBaseStep stepNo 0x159c0 state configured atPc loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured; decode_run)

private theorem writeSuccessActivationTimestampCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x159c4)
    (base : state.regs.get? x1 = some 0x159c0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x159c4 0x15bc8 x1 0x159c8)
        0x15bc8 retired) false :=
  writeSuccessLateSliceCallStep stepNo 0x159c4 0x15bc8 0x159c8 0x208
    0xe7 0x80 0x80 0x20 state configured atPc base loaded (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by rfl)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured; decode_run)
    (by native_decide) (by native_decide) (by native_decide)

/-- Production `0x159c8: mv a0,s0` before the public-key byte-list child. -/
private theorem writeSuccessPublicKeysAddressStep (stepNo : Nat) (state : State)
    (address : Nat) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x159c8)
    (source : state.regs.get? x8 = some (BitVec.ofNat 64 address))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x159c8 retired x10 (BitVec.ofNat 64 address)) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x159c8
  have source' := (stepPremiseState_writes state 0x159c8).get x8 (by decide) |>.trans source
  have resultEq : iTypeResult .ADDI 0 (BitVec.ofNat 64 address) =
      BitVec.ofNat 64 address := by
    simp [iTypeResult, show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
  have execute : Runs (execute (.ITYPE (0, .Regidx 8#5, .Regidx 10#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x10 (BitVec.ofNat 64 address) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 8#5) (.Regidx 10#5) .ADDI) _ _ _
    simpa only [resultEq] using execute_ITYPE_run premise _ 0 (.Regidx 8#5)
      (.Regidx 10#5) .ADDI (BitVec.ofNat 64 address)
      (rX_x8_run premise (BitVec.ofNat 64 address) source')
      (wX_x10_run premise (iTypeResult .ADDI 0 (BitVec.ofNat 64 address)))
  exact configuredRegisterWriteStep stepNo 0x159c8 state x10 (BitVec.ofNat 64 address)
    (.ITYPE (0, .Regidx 8#5, .Regidx 10#5, .ADDI)) 0x13 0x05 0x04 0x00
    configured atPc loaded (by
      obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
        writeSuccessLoadDecodeReads configured
      decode_run) execute (base := by rfl)

/-- Production `0x159cc: ld a1,0x58(sp)` before the public-key byte-list child. -/
private theorem writeSuccessPublicKeysLengthStep (stepNo : Nat) (state : State)
    (args : WriteSuccessArgs) (length : Nat) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x159cc)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x58) length)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x159cc retired x11 (BitVec.ofNat 64 length)) false := by
  exact writeSuccessLateSliceLoadStep stepNo 0x159cc 0x58 length (.Regidx 11#5) x11
    (BitVec.ofNat 64 length) 0x83 0x35 0x81 0x05 args state access atPc stack rep
    (by omega) (by omega) loaded (fun premise => wX_x11_run premise _) (by native_decide)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured; decode_run)
    (by native_decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by native_decide) (by native_decide) (by native_decide) (by native_decide)

private theorem writeSuccessPublicKeysCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x159d0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x159d0 retired x1 0x159d0) false :=
  writeSuccessLateSliceCallBaseStep stepNo 0x159d0 state configured atPc loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured; decode_run)

private theorem writeSuccessPublicKeysCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x159d4)
    (base : state.regs.get? x1 = some 0x159d0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x159d4 0x15c10 x1 0x159d8)
        0x15c10 retired) false :=
  writeSuccessLateSliceCallStep stepNo 0x159d4 0x15c10 0x159d8 0x240
    0xe7 0x80 0x00 0x24 state configured atPc base loaded (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by rfl)
    (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured; decode_run)
    (by native_decide) (by native_decide) (by native_decide)

macro "writeSuccessRestoreStep(" name:ident ";" pc:term "," offset:term ","
    rd:term "," destination:term "," wrun:term ";"
    b0:term "," b1:term "," b2:term "," b3:term ")" : command =>
  `(private theorem $name (stepNo : Nat) (args : WriteSuccessArgs) (state : State)
      (value : Nat) (access : WriteSuccessMachineAccess args state)
      (atPc : state.regs.get? PC = some (BitVec.ofNat 64 $pc))
      (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
      (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + $offset) value)
      (aligned : args.stackPointer % 16 = 0)
      (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state $pc retired $destination (BitVec.ofNat 64 value)) false := by
      exact writeSuccessLateSliceLoadStep stepNo $pc $offset value $rd $destination
        (BitVec.ofNat 64 value) $b0 $b1 $b2 $b3 args state access atPc stack rep
        (by omega) (by omega) loaded
        (fun premise => $wrun premise (BitVec.ofNat 64 value))
        (by native_decide)
        (by obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
          writeSuccessLoadDecodeReads access.configured; decode_run)
        (by native_decide) (by decide) (by decide) (by decide) (by decide)
        (by rfl) (by native_decide) (by native_decide) (by native_decide) (by native_decide))

writeSuccessRestoreStep(writeSuccessRestoreRaStep;
  0x159d8, 0x7c8, .Regidx 1#5, x1, wX_x1_run; 0x83, 0x30, 0x81, 0x7c)
writeSuccessRestoreStep(writeSuccessRestoreS0Step;
  0x159dc, 0x7c0, .Regidx 8#5, x8, wX_x8_run; 0x03, 0x34, 0x01, 0x7c)
writeSuccessRestoreStep(writeSuccessRestoreS1Step;
  0x159e0, 0x7b8, .Regidx 9#5, x9, wX_x9_run; 0x83, 0x34, 0x81, 0x7b)
writeSuccessRestoreStep(writeSuccessRestoreS2Step;
  0x159e4, 0x7b0, .Regidx 18#5, x18, wX_x18_run; 0x03, 0x39, 0x01, 0x7b)
writeSuccessRestoreStep(writeSuccessRestoreS3Step;
  0x159e8, 0x7a8, .Regidx 19#5, x19, wX_x19_run; 0x83, 0x39, 0x81, 0x7a)
writeSuccessRestoreStep(writeSuccessRestoreS4Step;
  0x159ec, 0x7a0, .Regidx 20#5, x20, wX_x20_run; 0x03, 0x3a, 0x01, 0x7a)
writeSuccessRestoreStep(writeSuccessRestoreS5Step;
  0x159f0, 0x798, .Regidx 21#5, x21, wX_x21_run; 0x83, 0x3a, 0x81, 0x79)
writeSuccessRestoreStep(writeSuccessRestoreS6Step;
  0x159f4, 0x790, .Regidx 22#5, x22, wX_x22_run; 0x03, 0x3b, 0x01, 0x79)
writeSuccessRestoreStep(writeSuccessRestoreS7Step;
  0x159f8, 0x788, .Regidx 23#5, x23, wX_x23_run; 0x83, 0x3b, 0x81, 0x78)
writeSuccessRestoreStep(writeSuccessRestoreS8Step;
  0x159fc, 0x780, .Regidx 24#5, x24, wX_x24_run; 0x03, 0x3c, 0x01, 0x78)
writeSuccessRestoreStep(writeSuccessRestoreS9Step;
  0x15a00, 0x778, .Regidx 25#5, x25, wX_x25_run; 0x83, 0x3c, 0x81, 0x77)
writeSuccessRestoreStep(writeSuccessRestoreS10Step;
  0x15a04, 0x770, .Regidx 26#5, x26, wX_x26_run; 0x03, 0x3d, 0x01, 0x77)
writeSuccessRestoreStep(writeSuccessRestoreS11Step;
  0x15a08, 0x768, .Regidx 27#5, x27, wX_x27_run; 0x83, 0x3d, 0x81, 0x76)

/-- Production `0x15a0c: addi sp,sp,2000`. -/
private theorem writeSuccessRestoreStackStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15a0c)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (lower : 0x880 ≤ args.stackPointer) (fits : args.stackPointer < 2 ^ 64) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15a0c retired x2 (BitVec.ofNat 64 args.stackPointer)) false := by
  have decode : Runs
      (ext_decode (fetchWord (0x13 : BitVec 8) (0x01 : BitVec 8) (0x01 : BitVec 8)
        (0x7d : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x7d0, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
    have privilegeAfter :
        (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
          some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using writeReg_read_unchanged
            state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using writeReg_read_unchanged
            state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    decode_run
  exact decodeInputAddiX2Step stepNo 0x15a0c state 0x7d0
    (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (BitVec.ofNat 64 args.stackPointer)
    0x13 0x01 0x01 0x7d configured atPc stack loaded
    (writeSuccessFinalStackResult args.stackPointer lower fits) decode (base := by rfl)

/-- Production `0x15a10: ret`. -/
private theorem writeSuccessReturnStep (stepNo : Nat) (state : State)
    (returnAddress : BitVec 64) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15a10)
    (link : state.regs.get? x1 = some returnAddress)
    (targetAligned : Sail.BitVec.access returnAddress 1 = 0#1)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x15a10
          (Sail.BitVec.update returnAddress 0 0#1))
        (Sail.BitVec.update returnAddress 0 0#1) retired) false :=
  configuredRetStep stepNo 0x15a10 state returnAddress configured atPc link targetAligned loaded

private theorem writeSuccessRestoreOne
    {kv : List RegVal} {base current : State}
    (fromStep used pc nextPc offset value : Nat) (destination : Register)
    (result : RegisterType destination)
    (args : WriteSuccessArgs) (values : DecodeCalleeSavedValues)
    (seg : Seg writeSuccessParentPc (fun _ => False) (fun _ _ _ _ _ => False)
      writeSuccessParentWrites (fun _ => False) kv fromStep used base current
      (BitVec.ofNat 64 pc))
    (access : WriteSuccessMachineAccess args base)
    (saved : SavedWordReps base (writeSuccessSavedWords args values))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (aligned : args.stackPointer % 16 = 0)
    (member : (args.stackPointer - 0x7d0 + offset, value) ∈
      writeSuccessSavedWords args values)
    (owned : writeSuccessParentPc (BitVec.ofNat 64 pc))
    (nextEq : Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4 = BitVec.ofNat 64 nextPc)
    (inWrites : writeSuccessParentWrites destination)
    (destinationNotPc : destination ≠ PC) (destinationNotRetired : destination ≠ minstret)
    (keep : RegsOutside (RegSet.union stepBookkeeping (RegSet.only destination)) kv)
    (stackMember : ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩ ∈ kv)
    (step : ∀ stepNo state,
      WriteSuccessMachineAccess args state →
      state.regs.get? PC = some (BitVec.ofNat 64 pc) →
      state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) →
      UIntRep 8 state.mem (args.stackPointer - 0x7d0 + offset) value →
      args.stackPointer % 16 = 0 →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false) :
    ∃ next, Seg writeSuccessParentPc (fun _ => False) (fun _ _ _ _ _ => False)
      writeSuccessParentWrites (fun _ => False) (⟨destination, result⟩ :: kv)
      fromStep (used + 1) base next (BitVec.ofNat 64 nextPc) := by
  have currentAccess := writeSuccessAccessOfSeg access seg
  have noMemory : ∀ address : Nat, ¬(fun _ => False) address := by simp
  have currentLoaded : Artifacts.programImage.fileBytesLoadedFaithfully current.mem := by
    simpa [seg.memEq noMemory] using loaded
  have currentRep : UIntRep 8 current.mem
      (args.stackPointer - 0x7d0 + offset) value := by
    rw [seg.memEq noMemory]
    exact saved _ member
  obtain ⟨retired, run⟩ := step (fromStep + used) current currentAccess seg.atPc
    (seg.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) stackMember)
    currentRep aligned currentLoaded
  exact seg.step
    owned
    (by simp) destination result (BitVec.ofNat 64 nextPc) ⟨retired, run⟩
    nextEq (by intro r h; exact Or.inl h)
    inWrites destinationNotPc destinationNotRetired keep

set_option genInjectivity false in
/-- Both fork-name routes reconverged at `0x159a0`. -/
structure WriteSuccessForkNameHandoff
    (fromStep booleanUsed routeUsed : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues)
    (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges)
    fromStep (5 + booleanUsed + routeUsed) before after
  atPc : EndpointPc after = some 0x159a0
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  stdout : after.stdout = before.stdout ++
    match args.decoded.chainConfig.forkName with
    | none => #[0]
    | some bytes => #[1] ++ encodeBytes bytes
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine

/-- Consume the optional fork-name bytes child and reconverge both routes. -/
private theorem writeSuccessForkNameHandoff
    (booleanChild : WriteSuccessBooleanInstanceContract)
    (bytesChild : WriteSuccessBytesInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (atPc : EndpointPc before = some 0x1596c)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ booleanUsed routeUsed after,
      WriteSuccessForkNameHandoff fromStep booleanUsed routeUsed args payloadBytes values
        before after := by
  obtain ⟨booleanUsed, booleanAfter, boolean⟩ := writeSuccessForkNameBooleanHandoff
    booleanChild fromStep args payloadBytes values before atPc stack context saved access loaded
    aligned lower upper decodedAddress
  rcases boolean.route with absent | present
  · obtain ⟨optionEq, afterPc, stdout⟩ := absent
    exact ⟨booleanUsed, 0, booleanAfter, {
      trace := by simpa [Nat.add_assoc] using boolean.trace
      atPc := afterPc
      stack := boolean.stack
      stdin := boolean.stdin
      cursor := boolean.cursor
      exitCode := boolean.exitCode
      stdout := by simpa [optionEq] using stdout
      saved := boolean.saved
      payloadContext := boolean.payloadContext
      loaded := boolean.loaded
      access := boolean.access }⟩
  · obtain ⟨bytes, address, optionEq, _nonzero, afterPc, stdout, addressReg,
      countRep, arrayRep⟩ := present
    obtain ⟨bytesUsed, bytesAfter, bytesHandoff⟩ :=
      writeSuccessForkNamePresentBytesHandoff bytesChild (fromStep + 5 + booleanUsed)
        address args payloadBytes bytes values booleanAfter afterPc boolean.stack addressReg
        countRep arrayRep boolean.payloadContext boolean.saved boolean.access boolean.loaded
        aligned lower upper decodedAddress
    have seg0 : Seg writeSuccessParentPc (fun pc => pc = 0x159a0)
        (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
        [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
        (fromStep + 5 + booleanUsed + 4 + bytesUsed) 0 bytesAfter.machine
        bytesAfter.machine 0x15990 := {
      trace := .refl _ _
      confined := .nil
      writes := .refl _ _
      mem := fun _ _ => rfl
      retired := bytesHandoff.access.configured.retiredCounter
      atPc := bytesHandoff.atPc
      regs := by intro pair member; simp at member; subst pair; exact bytesHandoff.stack }
    obtain ⟨retired, jumpRun⟩ := writeSuccessForkNameJoinStep
      (fromStep + 5 + booleanUsed + 4 + bytesUsed) bytesAfter.machine
      bytesHandoff.access.configured bytesHandoff.atPc bytesHandoff.loaded
    obtain ⟨finalMachine, seg1⟩ := seg0.stepJump 0x159a0
      (by unfold writeSuccessParentPc; exact
        ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
      (by simp) ⟨retired, jumpRun⟩ (by intro r h; exact Or.inl h)
      (by simp [RegsOutside, stepBookkeeping])
    let after : EndpointState := { bytesAfter with machine := finalMachine }
    have jumpMachineTrace := seg1.confined 0 finalMachine
      (.exitAt _ _ 0x159a0 seg1.atPc rfl)
    have jumpTrace : ConfinedTrace EndpointStep EndpointPc
        (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        (fromStep + 5 + booleanUsed + 4 + bytesUsed) 1 bytesAfter after := by
      simpa [after] using liftWriteSuccessParentTrace bytesAfter jumpMachineTrace
    have payloadAfter : WriteSuccessPayloadContext args payloadBytes after := by
      apply writeSuccessPayloadContextAfterChild decodedAddress lower upper
        bytesHandoff.access.writerRegionBeforeOutputContext bytesHandoff.payloadContext seg1.mem
      · intro address inside
        exact inside.elim
      · intro index bound inside
        exact inside.elim
      · intro index bound inside
        exact inside.elim
      · intro index bound inside
        exact inside.elim
      · intro index bound inside
        exact inside.elim
      · intro index bound inside
        exact inside.elim
      · intro index bound inside
        exact inside.elim
      · intro tailValues word member index bound inside
        exact inside.elim
    have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
      intro word member
      exact (bytesHandoff.saved word member).of_writesOnlyWithin seg1.mem (by
        intro index bound inside
        exact inside.elim)
    exact ⟨booleanUsed, 5 + bytesUsed, after, {
      trace := by
        have prefixTrace := boolean.trace.append
          (by simpa [Nat.add_assoc] using bytesHandoff.trace)
        have all := prefixTrace.append (by simpa [Nat.add_assoc] using jumpTrace)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all
      atPc := by simpa [after, EndpointPc] using seg1.atPc
      stack := by simpa [after] using seg1.reg x2 _ (by simp)
      stdin := by simpa [after, bytesHandoff.stdin] using boolean.stdin
      cursor := by simpa [after, bytesHandoff.cursor] using boolean.cursor
      exitCode := by simpa [after, bytesHandoff.exitCode] using boolean.exitCode
      stdout := by
        simp only [optionEq]
        calc
          after.stdout = bytesAfter.stdout := rfl
          _ = booleanAfter.stdout ++ encodeBytes bytes := bytesHandoff.stdout
          _ = before.stdout ++ #[1] ++ encodeBytes bytes := by rw [stdout]
          _ = before.stdout ++ (#[1] ++ encodeBytes bytes) := by simp
      saved := savedAfter
      payloadContext := payloadAfter
      loaded := by
        have memEq : finalMachine.mem = bytesAfter.machine.mem := seg1.memEq (by simp)
        simpa [after, memEq] using bytesHandoff.loaded
      access := by simpa [after] using writeSuccessAccessOfSeg bytesHandoff.access seg1 }⟩

set_option genInjectivity false in
structure WriteSuccessActiveForkHandoff
    (fromStep childUsed : Nat) (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (values : DecodeCalleeSavedValues) (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (4 + childUsed) before after
  atPc : EndpointPc after = some 0x159b0
  stack : after.machine.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  publicKeysAddress : ∃ address, after.machine.regs.get? x8 = some (BitVec.ofNat 64 address) ∧
    UIntRep 8 after.machine.mem (args.stackPointer - 0x7d0 + 0x60) address
  stdout : after.stdout = before.stdout ++ encodeNatLE 8 args.decoded.chainConfig.activeForkIndex
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine

set_option genInjectivity false in
structure WriteSuccessLateOptionalHandoff
    (fromStep childUsed returnPc descriptor : Nat) (value : Option Nat)
    (args : WriteSuccessArgs) (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (3 + childUsed) before after
  atPc : EndpointPc after = some (BitVec.ofNat 64 returnPc)
  stack : after.machine.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  x8 : after.machine.regs.get? x8 = before.machine.regs.get? x8
  stdout : after.stdout = before.stdout ++ encodeOptional (encodeNatLE 8) value
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : WritesOnlyWithin (byteRange (args.stackPointer - 0x7d0 - 16) 16)
    before.machine after.machine
  descriptorRep : OptionalUIntRep 8 after.machine.mem
    (args.stackPointer - 0x7d0 + descriptor) value
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine

private theorem writeSuccessLateOptionalHandoff
    (child : WriteSuccessOptionalU64InstanceContract)
    (fromStep pc returnPc descriptor callBase : Nat) (value : Option Nat)
    (args : WriteSuccessArgs) (before : EndpointState)
    (atPc : EndpointPc before = some (BitVec.ofNat 64 pc))
    (stack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (x8Value : BitVec 64) (x8Reg : before.machine.regs.get? x8 = some x8Value)
    (rep : OptionalUIntRep 8 before.machine.mem
      (args.stackPointer - 0x7d0 + descriptor) value)
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (lower : 0x880 ≤ args.stackPointer) (upper : args.stackPointer < 2 ^ 64)
    (sourceStep : ∀ step state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 pc) →
      state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step step false) state
        (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x10
          (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + descriptor))) false)
    (baseStep : ∀ step state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 (pc + 4)) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step step false) state
        (afterRegisterWrite state (BitVec.ofNat 64 (pc + 4)) retired x1
          (BitVec.ofNat 64 callBase)) false)
    (callStep : ∀ step state,
      ConfiguredMachinePre EndpointMachinePc state →
      state.regs.get? PC = some (BitVec.ofNat 64 (pc + 8)) →
      state.regs.get? x1 = some (BitVec.ofNat 64 callBase) →
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem →
      ∃ retired, Runs (try_step step false) state
        (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 (pc + 8))
            0x15bc8 x1 returnPc) 0x15bc8 retired) false)
    (owned0 : writeSuccessParentPc (BitVec.ofNat 64 pc))
    (owned1 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 4)))
    (owned2 : writeSuccessParentPc (BitVec.ofNat 64 (pc + 8)))
    (notExit0 : ¬writeSuccessOptionalCallExitPc (BitVec.ofNat 64 pc))
    (notExit1 : ¬writeSuccessOptionalCallExitPc (BitVec.ofNat 64 (pc + 4)))
    (notExit2 : ¬writeSuccessOptionalCallExitPc (BitVec.ofNat 64 (pc + 8)))
    (next0 : Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4 = BitVec.ofNat 64 (pc + 4))
    (next1 : Sail.BitVec.addInt (BitVec.ofNat 64 (pc + 4)) 4 = BitVec.ofNat 64 (pc + 8))
    (returnListed : returnPc ∈ Elflings.writeSuccessOptionalU64ExitPcs) :
    ∃ childUsed after,
      WriteSuccessLateOptionalHandoff fromStep childUsed returnPc descriptor value args
        before after := by
  have seg0 : Seg writeSuccessParentPc writeSuccessOptionalCallExitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩, ⟨x8, x8Value⟩]
      fromStep 0 before.machine before.machine (BitVec.ofNat 64 pc) := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by
      intro pair member
      simp at member
      rcases member with rfl | rfl
      · exact stack
      · exact x8Reg }
  obtain ⟨machine1, seg1⟩ := seg0.step owned0 notExit0
    x10 (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + descriptor))
    (BitVec.ofNat 64 (pc + 4))
    (sourceStep fromStep before.machine access.configured atPc stack loaded) next0
    (by intro r h; exact Or.inl h) (by simp [writeSuccessParentWrites])
    (by native_decide) (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully machine1.mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨machine2, seg2⟩ := seg1.step owned1 notExit1
    x1 (BitVec.ofNat 64 callBase) (BitVec.ofNat 64 (pc + 8))
    (baseStep (fromStep + 1) machine1 access1.configured seg1.atPc loaded1) next1
    (by intro r h; exact Or.inl h) (by simp [writeSuccessParentWrites])
    (by native_decide) (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg access seg2
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully machine2.mem := by
    simpa [seg2.memEq (by simp)] using loaded
  obtain ⟨retired2, callRun⟩ := callStep (fromStep + 2) machine2 access2.configured
    seg2.atPc (seg2.reg x1 (BitVec.ofNat 64 callBase) (by simp)) loaded2
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement machine2) (BitVec.ofNat 64 (pc + 8))
      0x15bc8 x1 returnPc) 0x15bc8 retired2
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes machine2 (BitVec.ofNat 64 (pc + 8))
    0x15bc8 retired2 x1 returnPc
  have callAtPc : callMachine.regs.get? PC = some 0x15bc8 := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callMemEq : callMachine.mem = before.machine.mem := by
    have baseMem : callMachine.mem = machine2.mem := by
      change (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement machine2) (BitVec.ofNat 64 (pc + 8))
          0x15bc8 x1 returnPc) 0x15bc8 retired2).mem = machine2.mem
      rw [tryStepControlFlowAfterRetired_mem]
      change (controlFlowJumpState (tryStepControlFlowAfterIncrement machine2)
        (BitVec.ofNat 64 (pc + 8)) 0x15bc8).mem = machine2.mem
      rw [controlFlowJumpState_mem]
      rfl
    exact baseMem.trans (seg2.memEq (by simp))
  have parentPrefix : ConfinedPrefix writeSuccessParentPc writeSuccessOptionalCallExitPc
      (fun _ _ _ _ _ => False) (fromStep + 2) 1 machine2 callMachine :=
    .ownStep seg2.atPc owned2 notExit2 callRun
  have parentMachineTrace := seg2.confined.trans parentPrefix 0 callMachine
    (.exitAt _ _ 0x15bc8 callAtPc (by unfold writeSuccessOptionalCallExitPc; rfl))
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 3 before callState := by
    simpa [callState] using liftWriteSuccessParentTrace before parentMachineTrace
  let childValue : OptionalUInt64EncoderValue :=
    { address := args.stackPointer - 0x7d0 + descriptor, value }
  let childArgs : EncoderCallArgs OptionalUInt64EncoderValue :=
    { returnAddress := returnPc, callerStack := args.stackPointer - 0x7d0,
      inputSize := args.inputSize, value := childValue }
  have childEntry : EncoderCallEntry Elflings.writeSuccessOptionalU64Entry
      Elflings.writeSuccessOptionalU64ExitPcs OptionalUInt64EncoderBinding childArgs callState := by
    unfold EncoderCallEntry
    refine ⟨(by simpa [childArgs] using returnListed), writeSuccessChildStackBound upper,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [callState] using callAtPc
    · simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, childArgs]
    · exact (callWrites.get x2 (by decide)).trans
        (seg2.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    · refine ⟨?_, ?_, ?_⟩
      · cases optionEq : value with
        | none =>
          rw [optionEq] at rep
          simpa [callState, callMemEq, childValue] using rep.2.1
        | some item =>
          have active := rep
          rw [optionEq] at active
          simpa [callState, callMemEq] using active.2.2.1
      · exact (callWrites.get x10 (by decide)).trans
          (seg2.reg x10 (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + descriptor)) (by simp))
      · simpa [callState, callMemEq, childValue] using rep
    · simpa [callState, callMemEq] using loaded
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have callAccess : WriteSuccessMachineAccess args callMachine := {
    configured := configuredAfterWriteSuccessCall (BitVec.ofNat 64 (pc + 8)) 0x15bc8
      returnPc retired2 access2.configured
    frameLoad := fun o w b => dataPmaAllows_of_pma_regions_eq callPmaEq (access2.frameLoad o w b)
    frameStore := fun o w b => dataPmaAllows_of_pma_regions_eq callPmaEq (access2.frameStore o w b)
    frameNoMMIO := access2.frameNoMMIO
    decodedLoad := fun o w b => dataPmaAllows_of_pma_regions_eq callPmaEq (access2.decodedLoad o w b)
    decodedNoMMIO := access2.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq callPmaEq access2.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq callPmaEq access2.outputLengthStore
    writerRegionBeforeOutputContext := access2.writerRegionBeforeOutputContext
    frameNotCode := access2.frameNotCode }
  have frameInWriter : ∀ address, byteRange (args.stackPointer - 0x7d0 - 16) 16 address →
      writeSuccessFrameMemory args address := fun _ inside =>
    writeSuccessChildFrame_mem_frame lower inside
  obtain ⟨childUsed, after, handoff⟩ := writeSuccessEncoderChildHandoff child
    (fun inside => by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lo, hi⟩
      simp [Elflings.writeSuccessOptionalU64ExecutionPcRanges] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges], by omega, by omega⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges], by omega, by omega⟩)
    fromStep 3 args childValue before callState childArgs rfl childEntry parentTrace
    ⟨rfl, rfl, rfl, rfl⟩ callMemEq (by simpa [callState] using callAccess)
    (by simpa [callState, callMemEq] using loaded) lower frameInWriter
  have descriptorAfter : OptionalUIntRep 8 after.machine.mem
      (args.stackPointer - 0x7d0 + descriptor) value := by
    cases optionEq : value with
    | none =>
      rw [optionEq] at rep
      change UIntRep 1 after.machine.mem (args.stackPointer - 0x7d0 + descriptor + 8) 0
      exact rep.of_writesOnlyWithin handoff.memory (by
        intro index inBounds inside
        unfold byteRange at inside
        omega)
    | some item =>
      rw [optionEq] at rep
      change UIntRep 8 after.machine.mem (args.stackPointer - 0x7d0 + descriptor) item ∧
        UIntRep 1 after.machine.mem (args.stackPointer - 0x7d0 + descriptor + 8) 1
      exact ⟨rep.1.of_writesOnlyWithin handoff.memory (by
          intro index inBounds inside
          unfold byteRange at inside
          omega),
        rep.2.of_writesOnlyWithin handoff.memory (by
          intro index inBounds inside
          unfold byteRange at inside
          omega)⟩
  refine ⟨childUsed, after, {
    trace := handoff.trace
    atPc := handoff.atPc
    stack := handoff.stack
    x8 := handoff.calleeX8.trans (by
      simpa [callState] using ((callWrites.get x8 (by simp [stepBookkeeping])).trans
        ((seg2.reg x8 x8Value (by simp)).trans x8Reg.symm)))
    stdout := handoff.stdout
    stdin := handoff.stdin
    cursor := handoff.cursor
    exitCode := handoff.exitCode
    memory := handoff.memory
    descriptorRep := descriptorAfter
    loaded := handoff.loaded
    access := handoff.access }⟩

private theorem writeSuccessPayloadContextAfterLateOptional
    {fromStep childUsed returnPc descriptor : Nat} {value : Option Nat}
    {args : WriteSuccessArgs} {bytes : Array UInt8} {before after : EndpointState}
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20)
    (lower : 0x880 ≤ args.stackPointer) (upper : args.stackPointer < 2 ^ 64)
    (context : WriteSuccessPayloadContext args bytes before)
    (call : WriteSuccessLateOptionalHandoff fromStep childUsed returnPc descriptor value args
      before after) : WriteSuccessPayloadContext args bytes after := by
  apply writeSuccessPayloadContextAfterChild decodedAddress lower upper
    call.access.writerRegionBeforeOutputContext context call.memory
  · intro address inside
    exact Or.inl (writeSuccessChildFrame_mem_frame lower inside)
  all_goals
    first
    | intro values word member index inBounds inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> unfold byteRange at inside <;> omega
    | intro index inBounds inside
      unfold byteRange at inside
      try rw [decodedAddress] at inside
      omega

set_option genInjectivity false in
structure WriteSuccessChainOptionalsHandoff
    (fromStep blockUsed timestampUsed : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues)
    (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges)
    fromStep (3 + blockUsed + 3 + timestampUsed) before after
  atPc : EndpointPc after = some 0x159c8
  stack : after.machine.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  publicKeysAddress : ∃ address,
    after.machine.regs.get? x8 = some (BitVec.ofNat 64 address) ∧
    UIntRep 8 after.machine.mem (args.stackPointer - 0x7d0 + 0x60) address
  stdout : after.stdout = before.stdout ++
    encodeOptional (encodeNatLE 8) args.decoded.chainConfig.activationBlock ++
    encodeOptional (encodeNatLE 8) args.decoded.chainConfig.activationTimestamp
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine

private theorem writeSuccessChainOptionalsHandoff
    (child : WriteSuccessOptionalU64InstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues)
    (before : EndpointState) (atPc : EndpointPc before = some 0x159b0)
    (stack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (publicKeysAddress : ∃ address,
      before.machine.regs.get? x8 = some (BitVec.ofNat 64 address) ∧
      UIntRep 8 before.machine.mem (args.stackPointer - 0x7d0 + 0x60) address)
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (lower : 0x880 ≤ args.stackPointer) (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ blockUsed timestampUsed after,
      WriteSuccessChainOptionalsHandoff fromStep blockUsed timestampUsed args payloadBytes values
        before after := by
  obtain ⟨address, x8Reg, addressRep⟩ := publicKeysAddress
  obtain ⟨blockUsed, blockAfter, block⟩ := writeSuccessLateOptionalHandoff child
    fromStep 0x159b0 0x159bc 0x128 0x159b4 args.decoded.chainConfig.activationBlock args before
    atPc stack (BitVec.ofNat 64 address) x8Reg context.activationBlockRep access loaded lower upper
    (fun step state => writeSuccessActivationBlockSourceStep step args state)
    writeSuccessActivationBlockCallBaseStep writeSuccessActivationBlockCallStep
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessOptionalCallExitPc; native_decide)
    (by unfold writeSuccessOptionalCallExitPc; native_decide)
    (by unfold writeSuccessOptionalCallExitPc; native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have blockContext := writeSuccessPayloadContextAfterLateOptional decodedAddress lower upper
    context block
  have blockSaved : SavedWordReps blockAfter.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact (saved word member).of_writesOnlyWithin block.memory (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  have addressRepAfter := addressRep.of_writesOnlyWithin block.memory (by
    intro index inBounds inside
    unfold byteRange at inside
    omega)
  obtain ⟨timestampUsed, after, timestamp⟩ := writeSuccessLateOptionalHandoff child
    (fromStep + 3 + blockUsed) 0x159bc 0x159c8 0x118 0x159c0
    args.decoded.chainConfig.activationTimestamp args blockAfter block.atPc block.stack
    (BitVec.ofNat 64 address) (block.x8.trans x8Reg)
    blockContext.activationTimestampRep block.access block.loaded lower upper
    (fun step state => writeSuccessActivationTimestampSourceStep step args state)
    writeSuccessActivationTimestampCallBaseStep writeSuccessActivationTimestampCallStep
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessOptionalCallExitPc; native_decide)
    (by unfold writeSuccessOptionalCallExitPc; native_decide)
    (by unfold writeSuccessOptionalCallExitPc; native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have finalContext := writeSuccessPayloadContextAfterLateOptional decodedAddress lower upper
    blockContext timestamp
  have finalSaved : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact (blockSaved word member).of_writesOnlyWithin timestamp.memory (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  have finalAddressRep := addressRepAfter.of_writesOnlyWithin timestamp.memory (by
    intro index inBounds inside
    unfold byteRange at inside
    omega)
  refine ⟨blockUsed, timestampUsed, after, {
    trace := by
      have timestampTrace : ConfinedTrace EndpointStep EndpointPc
          (pcInRanges Elflings.writeSuccessExecutionPcRanges)
          (fromStep + (3 + blockUsed)) (3 + timestampUsed) blockAfter after := by
        simpa only [Nat.add_assoc] using timestamp.trace
      simpa only [Nat.add_assoc] using block.trace.append timestampTrace
    atPc := timestamp.atPc
    stack := timestamp.stack
    publicKeysAddress := ⟨address, timestamp.x8.trans (block.x8.trans x8Reg), finalAddressRep⟩
    stdout := by rw [timestamp.stdout, block.stdout]
    stdin := timestamp.stdin.trans block.stdin
    cursor := timestamp.cursor.trans block.cursor
    exitCode := timestamp.exitCode.trans block.exitCode
    saved := finalSaved
    payloadContext := finalContext
    loaded := timestamp.loaded
    access := timestamp.access
    memory := WritesOnlyWithin.trans_same
      (writeSuccessChildFrame_writes_writerFrame lower block.memory)
      (writeSuccessChildFrame_writes_writerFrame lower timestamp.memory) }⟩

/-- The public-key site's exact `mv; ld; auipc; jalr` parent setup. -/
private theorem writeSuccessPublicKeysSetup
    (fromStep address length : Nat) (args : WriteSuccessArgs) (before : EndpointState)
    (atPc : EndpointPc before = some 0x159c8)
    (stack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (addressReg : before.machine.regs.get? x8 = some (BitVec.ofNat 64 address))
    (lengthRep : UIntRep 8 before.machine.mem (args.stackPointer - 0x7d0 + 0x58) length)
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) :
    ∃ callState,
      WriteSuccessSliceCallSetup fromStep 0x159c8 0x159d8 0x15c10 address length
        args before callState := by
  let exitPc : BitVec 64 → Prop := fun pc => pc = 0x15c10
  have seg0 : Seg writeSuccessParentPc exitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
        ⟨x8, BitVec.ofNat 64 address⟩]
      fromStep 0 before.machine before.machine 0x159c8 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by
      intro pair member
      simp at member
      rcases member with rfl | rfl
      · exact stack
      · exact addressReg }
  obtain ⟨retired0, run0⟩ := writeSuccessPublicKeysAddressStep fromStep before.machine
    address access.configured atPc addressReg loaded
  have seg1 := seg0.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by simp [exitPc]) x10 (BitVec.ofNat 64 address) 0x159cc retired0 run0
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite before.machine 0x159c8 retired0 x10 (BitVec.ofNat 64 address)).mem := by
    simpa [seg1.memEq (by simp)] using loaded
  have lengthRep1 : UIntRep 8
      (afterRegisterWrite before.machine 0x159c8 retired0 x10 (BitVec.ofNat 64 address)).mem
      (args.stackPointer - 0x7d0 + 0x58) length := by
    simpa only [afterRegisterWrite_mem] using lengthRep
  obtain ⟨retired1, run1⟩ := writeSuccessPublicKeysLengthStep (fromStep + 1) _ args length
    access1 seg1.atPc (seg1.reg x2 _ (by simp)) lengthRep1 aligned loaded1
  have seg2 := seg1.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by simp [exitPc]) x11 (BitVec.ofNat 64 length) 0x159d0 retired1 run1
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg access seg2
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite
        (afterRegisterWrite before.machine 0x159c8 retired0 x10 (BitVec.ofNat 64 address))
        0x159cc retired1 x11 (BitVec.ofNat 64 length)).mem := by
    simpa only [afterRegisterWrite_mem] using loaded
  obtain ⟨baseMachine, seg3⟩ := seg2.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by simp [exitPc]) x1 0x159d0 0x159d4
    (writeSuccessPublicKeysCallBaseStep (fromStep + 2) _ access2.configured seg2.atPc loaded2)
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access3 := writeSuccessAccessOfSeg access seg3
  have loaded3 : Artifacts.programImage.fileBytesLoadedFaithfully baseMachine.mem := by
    simpa [seg3.memEq (by simp)] using loaded
  obtain ⟨retired3, callRun⟩ := writeSuccessPublicKeysCallStep (fromStep + 3)
    baseMachine access3.configured seg3.atPc (seg3.reg x1 0x159d0 (by simp)) loaded3
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement baseMachine) 0x159d4 0x15c10 x1 0x159d8)
    0x15c10 retired3
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes baseMachine 0x159d4 0x15c10 retired3 x1 0x159d8
  have callAtPc : callMachine.regs.get? PC = some 0x15c10 := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callMemEq : callMachine.mem = before.machine.mem := by
    calc
      callMachine.mem = baseMachine.mem := by
        change (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement baseMachine)
            0x159d4 0x15c10 x1 0x159d8) 0x15c10 retired3).mem = _
        rw [tryStepControlFlowAfterRetired_mem]
        change (controlFlowJumpState (tryStepControlFlowAfterIncrement baseMachine)
          0x159d4 0x15c10).mem = _
        rw [controlFlowJumpState_mem]
        rfl
      _ = before.machine.mem := seg3.memEq (by simp)
  have callPrefix : ConfinedPrefix writeSuccessParentPc exitPc
      (fun _ _ _ _ _ => False) (fromStep + 3) 1 baseMachine callMachine :=
    ConfinedPrefix.ownStep seg3.atPc
      (by unfold writeSuccessParentPc; exact
        ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
      (by simp [exitPc]) callRun
  have callEnd : ScopedTrace writeSuccessParentPc exitPc
      (fun _ _ _ _ _ => False) (fromStep + 4) 0 callMachine callMachine :=
    .exitAt _ _ 0x15c10 callAtPc rfl
  have machineTrace := seg3.confined.trans callPrefix 0 callMachine callEnd
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 4 before callState := by
    simpa [callState] using liftWriteSuccessParentTrace before machineTrace
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have accessCall : WriteSuccessMachineAccess args callMachine := {
    configured := configuredAfterWriteSuccessCall 0x159d4 0x15c10 0x159d8 retired3
      access3.configured
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.frameStore offset width bound)
    frameNoMMIO := access3.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.decodedLoad offset width bound)
    decodedNoMMIO := access3.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq callPmaEq access3.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq callPmaEq access3.outputLengthStore
    writerRegionBeforeOutputContext := access3.writerRegionBeforeOutputContext
    frameNotCode := access3.frameNotCode }
  exact ⟨callState, {
    trace := parentTrace
    atPc := by simpa [callState, EndpointPc] using callAtPc
    link := by simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
    stack := by simpa [callState] using ((callWrites.get x2 (by decide)).trans
      (seg3.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)))
    address := by simpa [callState] using ((callWrites.get x10 (by decide)).trans
      (seg3.reg x10 (BitVec.ofNat 64 address) (by simp)))
    length := by simpa [callState] using ((callWrites.get x11 (by decide)).trans
      (seg3.reg x11 (BitVec.ofNat 64 length) (by simp)))
    memory := callMemEq
    stdin := rfl
    cursor := rfl
    stdout := rfl
    exitCode := rfl
    loaded := by simpa [callState, callMemEq] using loaded
    access := by simpa [callState] using accessCall }⟩

/-- Compose the final public-key byte-list call, landing at the writer epilogue. -/
private theorem writeSuccessPublicKeysHandoff
    (child : WriteSuccessByteListsInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (atPc : EndpointPc before = some 0x159c8)
    (stack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (publicKeysAddress : ∃ address,
      before.machine.regs.get? x8 = some (BitVec.ofNat 64 address) ∧
      UIntRep 8 before.machine.mem (args.stackPointer - 0x7d0 + 0x60) address)
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessLateByteListsHandoff fromStep childUsed 0x159d8 args.decoded.publicKeys
        args payloadBytes before after values := by
  obtain ⟨registerAddress, addressReg, registerRep⟩ := publicKeysAddress
  obtain ⟨semanticAddress, semanticRep, countRep, arrayRep⟩ := context.publicKeysRep
  have addressEq : registerAddress = semanticAddress :=
    UIntRep.eight_unique registerRep semanticRep
  subst registerAddress
  obtain ⟨callState, setup⟩ := writeSuccessPublicKeysSetup fromStep semanticAddress
    args.decoded.publicKeys.size args before atPc stack addressReg countRep access loaded aligned
  exact writeSuccessLateByteListsFromSetup child fromStep 0x159c8 0x159d8 semanticAddress
    args.decoded.publicKeys args payloadBytes before callState values setup arrayRep context saved
    lower upper decodedAddress (by native_decide)

private def writeSuccessRestoredRegs (args : WriteSuccessArgs)
    (values : DecodeCalleeSavedValues) : List RegVal :=
  [⟨x27, BitVec.ofNat 64 values.s11.toNat⟩,
   ⟨x26, BitVec.ofNat 64 values.s10.toNat⟩,
   ⟨x25, BitVec.ofNat 64 values.s9.toNat⟩,
   ⟨x24, BitVec.ofNat 64 values.s8.toNat⟩,
   ⟨x23, BitVec.ofNat 64 values.s7.toNat⟩,
   ⟨x22, BitVec.ofNat 64 values.s6.toNat⟩,
   ⟨x21, BitVec.ofNat 64 values.s5.toNat⟩,
   ⟨x20, BitVec.ofNat 64 values.s4.toNat⟩,
   ⟨x19, BitVec.ofNat 64 values.s3.toNat⟩,
   ⟨x18, BitVec.ofNat 64 values.s2.toNat⟩,
   ⟨x9, BitVec.ofNat 64 values.s1.toNat⟩,
   ⟨x8, BitVec.ofNat 64 values.s0.toNat⟩,
   ⟨x1, BitVec.ofNat 64 (BitVec.ofNat 64 args.returnAddress).toNat⟩,
   ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]

private def writeSuccessFinalRegs (args : WriteSuccessArgs)
    (values : DecodeCalleeSavedValues) : List RegVal :=
  ⟨x2, BitVec.ofNat 64 args.stackPointer⟩ ::
    (writeSuccessRestoredRegs args values).dropLast

/-- Restore the thirteen ABI-saved registers in production order. -/
private theorem writeSuccessRestoreRegisters
    (fromStep : Nat) (args : WriteSuccessArgs) (values : DecodeCalleeSavedValues)
    (before : EndpointState) (atPc : EndpointPc before = some 0x159d8)
    (stack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) :
    ∃ after,
      Seg writeSuccessParentPc (fun _ => False) (fun _ _ _ _ _ => False)
        writeSuccessParentWrites (fun _ => False)
        (writeSuccessRestoredRegs args values)
        fromStep 13 before.machine after 0x15a0c := by
  have seg0 : Seg writeSuccessParentPc (fun _ => False) (fun _ _ _ _ _ => False)
      writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine 0x159d8 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  have parentOwned : ∀ pc : Nat, 0x159d8 ≤ pc → pc < 0x15a14 →
      writeSuccessParentPc (BitVec.ofNat 64 pc) := by
    intro pc lo hi
    have fits : pc < 2 ^ 64 := by omega
    unfold writeSuccessParentPc
    exact ⟨(0x158e0, 0x15a14), by native_decide,
      by simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] using
        (show 0x158e0 ≤ pc by omega),
      by simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] using hi⟩
  obtain ⟨_, seg1⟩ := writeSuccessRestoreOne fromStep 0 0x159d8 0x159dc 0x7c8
    (BitVec.ofNat 64 args.returnAddress).toNat
    x1 (BitVec.ofNat 64 (BitVec.ofNat 64 args.returnAddress).toNat) args values seg0
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreRaStep step args state _)
  obtain ⟨_, seg2⟩ := writeSuccessRestoreOne fromStep 1 0x159dc 0x159e0 0x7c0
    values.s0.toNat x8 (BitVec.ofNat 64 values.s0.toNat) args values seg1
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreS0Step step args state _)
  obtain ⟨_, seg3⟩ := writeSuccessRestoreOne fromStep 2 0x159e0 0x159e4 0x7b8
    values.s1.toNat x9 (BitVec.ofNat 64 values.s1.toNat) args values seg2
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreS1Step step args state _)
  obtain ⟨_, seg4⟩ := writeSuccessRestoreOne fromStep 3 0x159e4 0x159e8 0x7b0
    values.s2.toNat x18 (BitVec.ofNat 64 values.s2.toNat) args values seg3
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreS2Step step args state _)
  obtain ⟨_, seg5⟩ := writeSuccessRestoreOne fromStep 4 0x159e8 0x159ec 0x7a8
    values.s3.toNat x19 (BitVec.ofNat 64 values.s3.toNat) args values seg4
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreS3Step step args state _)
  obtain ⟨_, seg6⟩ := writeSuccessRestoreOne fromStep 5 0x159ec 0x159f0 0x7a0
    values.s4.toNat x20 (BitVec.ofNat 64 values.s4.toNat) args values seg5
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreS4Step step args state _)
  obtain ⟨_, seg7⟩ := writeSuccessRestoreOne fromStep 6 0x159f0 0x159f4 0x798
    values.s5.toNat x21 (BitVec.ofNat 64 values.s5.toNat) args values seg6
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreS5Step step args state _)
  obtain ⟨_, seg8⟩ := writeSuccessRestoreOne fromStep 7 0x159f4 0x159f8 0x790
    values.s6.toNat x22 (BitVec.ofNat 64 values.s6.toNat) args values seg7
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreS6Step step args state _)
  obtain ⟨_, seg9⟩ := writeSuccessRestoreOne fromStep 8 0x159f8 0x159fc 0x788
    values.s7.toNat x23 (BitVec.ofNat 64 values.s7.toNat) args values seg8
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreS7Step step args state _)
  obtain ⟨_, seg10⟩ := writeSuccessRestoreOne fromStep 9 0x159fc 0x15a00 0x780
    values.s8.toNat x24 (BitVec.ofNat 64 values.s8.toNat) args values seg9
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreS8Step step args state _)
  obtain ⟨_, seg11⟩ := writeSuccessRestoreOne fromStep 10 0x15a00 0x15a04 0x778
    values.s9.toNat x25 (BitVec.ofNat 64 values.s9.toNat) args values seg10
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreS9Step step args state _)
  obtain ⟨_, seg12⟩ := writeSuccessRestoreOne fromStep 11 0x15a04 0x15a08 0x770
    values.s10.toNat x26 (BitVec.ofNat 64 values.s10.toNat) args values seg11
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreS10Step step args state _)
  obtain ⟨after, seg13⟩ := writeSuccessRestoreOne fromStep 12 0x15a08 0x15a0c 0x768
    values.s11.toNat x27 (BitVec.ofNat 64 values.s11.toNat) args values seg12
    access saved loaded aligned (by simp [writeSuccessSavedWords])
    (parentOwned _ (by omega) (by omega)) (by native_decide)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
    (by simp)
    (fun step state => writeSuccessRestoreS11Step step args state _)
  exact ⟨after, by simpa only [writeSuccessRestoredRegs] using seg13⟩

/-- Restore the stack pointer and return after the thirteen saved-register loads. -/
private theorem writeSuccessEpilogueHandoff
    (fromStep : Nat) (args : WriteSuccessArgs) (values : DecodeCalleeSavedValues)
    (before : EndpointState) (atPc : EndpointPc before = some 0x159d8)
    (stack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (fits : args.stackPointer < 2 ^ 64)
    (returnListed : args.returnAddress ∈ Elflings.writeSuccessExitPcs) :
    ∃ after,
      Seg writeSuccessParentPc (fun _ => False) (fun _ _ _ _ _ => False)
        writeSuccessParentWrites (fun _ => False) (writeSuccessFinalRegs args values)
        fromStep 15 before.machine after (BitVec.ofNat 64 args.returnAddress) := by
  obtain ⟨restored, seg13⟩ := writeSuccessRestoreRegisters fromStep args values before atPc
    stack saved access loaded aligned
  have seg13' := seg13.forget
    (kv' := (writeSuccessRestoredRegs args values).dropLast) (by
      intro pair member
      exact List.Sublist.mem member (List.dropLast_sublist _))
  have access13 := writeSuccessAccessOfSeg access seg13'
  have noMemory : ∀ address : Nat, ¬(fun _ => False) address := by simp
  have loaded13 : Artifacts.programImage.fileBytesLoadedFaithfully restored.mem := by
    simpa [seg13'.memEq noMemory] using loaded
  obtain ⟨retired13, run13⟩ := writeSuccessRestoreStackStep (fromStep + 13) args restored
    access13.configured seg13'.atPc
    (seg13.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by
      simp [writeSuccessRestoredRegs])) loaded13 lower fits
  obtain ⟨returning, seg14⟩ := seg13'.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by simp) x2 (BitVec.ofNat 64 args.stackPointer) 0x15a10 ⟨retired13, run13⟩
    (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [writeSuccessRestoredRegs, RegsOutside, stepBookkeeping])
  have access14 := writeSuccessAccessOfSeg access seg14
  have loaded14 : Artifacts.programImage.fileBytesLoadedFaithfully returning.mem := by
    simpa [seg14.memEq noMemory] using loaded
  have returnEq : args.returnAddress = 0x14d10 := by
    simpa [Elflings.writeSuccessExitPcs] using returnListed
  have targetAligned : Sail.BitVec.access (BitVec.ofNat 64 args.returnAddress) 1 = 0#1 := by
    rw [returnEq]
    native_decide
  have link : returning.regs.get? x1 = some (BitVec.ofNat 64 args.returnAddress) := by
    have valueEq : BitVec.ofNat 64 (BitVec.ofNat 64 args.returnAddress).toNat =
        BitVec.ofNat 64 args.returnAddress := by
      rw [returnEq]
      native_decide
    rw [← valueEq]
    exact seg14.reg x1 (BitVec.ofNat 64 (BitVec.ofNat 64 args.returnAddress).toNat) (by
      simp [writeSuccessRestoredRegs])
  obtain ⟨retired14, run14⟩ := writeSuccessReturnStep (fromStep + 14) returning
    (BitVec.ofNat 64 args.returnAddress) access14.configured seg14.atPc
    link targetAligned loaded14
  have targetEq : Sail.BitVec.update (BitVec.ofNat 64 args.returnAddress) 0 0#1 =
      BitVec.ofNat 64 args.returnAddress := by
    rw [returnEq]
    native_decide
  obtain ⟨after, seg15⟩ := seg14.stepJump (BitVec.ofNat 64 args.returnAddress)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by simp) (targetEq ▸ ⟨retired14, run14⟩)
    (fun _ bookkeeping => Or.inl bookkeeping)
    (by simp [writeSuccessRestoredRegs, RegsOutside, stepBookkeeping])
  exact ⟨after, by simpa [writeSuccessFinalRegs] using seg15⟩

private theorem writeSuccessActiveForkHandoff
    (child : WriteSuccessIntInstanceContract) (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues) (before : EndpointState)
    (atPc : EndpointPc before = some 0x159a0)
    (stack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessActiveForkHandoff fromStep childUsed args payloadBytes values before after := by
  obtain ⟨address, addressRep, _countRep, _arrayRep⟩ := context.publicKeysRep
  have seg0 : Seg writeSuccessParentPc (fun pc => pc = 0x159a4)
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine 0x159a0 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  obtain ⟨retired0, run0⟩ := writeSuccessPublicKeysPointerLoadStep
    fromStep args before.machine access atPc stack addressRep aligned loaded
  have seg1 := seg0.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by simp) x8 (BitVec.ofNat 64 address) 0x159a4 retired0 run0 (by native_decide)
    (by intro r h; exact Or.inl h) (by simp [writeSuccessParentWrites])
    (by native_decide) (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  let pointerState : EndpointState := { before with machine :=
    (afterRegisterWrite before.machine 0x159a0 retired0 x8 (BitVec.ofNat 64 address)) }
  have pointerContext : WriteSuccessPayloadContext args payloadBytes pointerState := by
    apply writeSuccessPayloadContextAfterChild (after := pointerState) decodedAddress lower upper
      access.writerRegionBeforeOutputContext context (by simpa [pointerState] using seg1.mem)
    all_goals simp
  have pointerSaved : SavedWordReps pointerState.machine (writeSuccessSavedWords args values) := by
    simpa only [pointerState, afterRegisterWrite_mem] using saved
  have pointerAccess : WriteSuccessMachineAccess args pointerState.machine := by
    simpa only [pointerState] using writeSuccessAccessOfSeg access seg1
  have pointerLoaded : Artifacts.programImage.fileBytesLoadedFaithfully pointerState.machine.mem := by
    simpa only [pointerState, afterRegisterWrite_mem] using loaded
  obtain ⟨childUsed, after, call⟩ := writeSuccessIntCallHandoff child (fromStep + 1)
    0x159a4 0x159b0 0x50 args.decoded.chainConfig.activeForkIndex 0x159a8 args pointerState
    seg1.atPc (by simpa [pointerState] using seg1.reg x2 _ (by simp))
    pointerContext.activeForkIndexRep pointerAccess pointerLoaded aligned lower upper
    (fun step state => writeSuccessActiveForkLoadStep step args state)
    writeSuccessActiveForkCallBaseStep writeSuccessActiveForkCallStep
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x158e0, 0x15a14), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have payloadAfter := writeSuccessPayloadContextAfterInt decodedAddress lower upper pointerContext call
  have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact (pointerSaved word member).of_writesOnlyWithin call.memory (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  have firstMachineTrace := seg1.confined 0 _ (.exitAt _ _ 0x159a4 seg1.atPc rfl)
  have firstTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 1 before pointerState := by
    simpa [pointerState] using liftWriteSuccessParentTrace before firstMachineTrace
  have addressAfter : UIntRep 8 after.machine.mem
      (args.stackPointer - 0x7d0 + 0x60) address := by
    apply (show UIntRep 8 pointerState.machine.mem
      (args.stackPointer - 0x7d0 + 0x60) address by
        simpa only [pointerState, afterRegisterWrite_mem] using addressRep).of_writesOnlyWithin
      call.memory
    intro index inBounds inside
    unfold byteRange at inside
    omega
  refine ⟨childUsed, after, {
    trace := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        firstTrace.append call.trace
    atPc := call.atPc
    stack := call.stack
    publicKeysAddress := ⟨address, call.x8.trans (by
      simpa [pointerState] using seg1.reg x8 (BitVec.ofNat 64 address) (by simp)),
      addressAfter⟩
    stdout := call.stdout
    stdin := call.stdin
    cursor := call.cursor
    exitCode := call.exitCode
    saved := savedAfter
    payloadContext := payloadAfter
    loaded := call.loaded
    access := call.access
    memory := by
      have pointerMemory : WriteSuccessMemoryFrame args before.machine pointerState.machine := by
        intro address outside
        rfl
      exact WritesOnlyWithin.trans_same pointerMemory
        (writeSuccessChildFrame_writes_writerFrame lower call.memory) }⟩

set_option genInjectivity false in
/-- Exact parent setup plus the shared bytes child for payload extra data. -/
structure WriteSuccessExtraDataHandoff
    (fromStep childUsed : Nat) (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (4 + childUsed) before after
  atPc : EndpointPc after = some 0x14ec8
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeBytes args.decoded.payload.extraData
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : WritesOnlyWithin
    (byteRange (args.stackPointer - 0x7d0 - 48) 48) before.machine after.machine
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  payload : WriteSuccessPayloadContext args payloadBytes after

/-- Transport the copied payload through the 48-byte shared bytes-encoder frame. -/
private theorem writeSuccessPayloadContextAfterBytes
    {args : WriteSuccessArgs} {payloadBytes : Array UInt8}
    {before after : EndpointState}
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20)
    (lower : 0x880 ≤ args.stackPointer) (upper : args.stackPointer < 2 ^ 64)
    (beforeContext : args.stackPointer + 0x380 ≤ Elflings.ioContextAddress)
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (memory : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 - 48) 48) before.machine after.machine) :
    WriteSuccessPayloadContext args payloadBytes after := by
  apply writeSuccessPayloadContextAfterChild decodedAddress lower upper beforeContext context memory
  · intro address inside
    exact Or.inl (writeSuccessChildFrame48_mem_frame lower inside)
  all_goals
    first
    | intro values word member index inBounds inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> unfold byteRange at inside <;> omega
    | intro index inBounds inside
      unfold byteRange at inside
      try rw [decodedAddress] at inside
      omega

/-- Compose the exact extra-data descriptor loads and selected shared bytes encoder. -/
private theorem writeSuccessExtraDataHandoff
    (bytesChild : WriteSuccessBytesInstanceContract) (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x14eb8)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessExtraDataHandoff fromStep childUsed args payloadBytes before after := by
  obtain ⟨extraAddress, pointerRep, lengthRep, extraRep⟩ := context.payloadRep.2.2.2.2.1
  have seg0 : Seg writeSuccessParentPc writeSuccessBytesCallExitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine 0x14eb8 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  obtain ⟨retired0, run0⟩ := writeSuccessExtraDataPointerLoadStep _ args before.machine
    extraAddress access atPc stack pointerRep aligned loaded
  have seg1 := seg0.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessBytesCallExitPc; native_decide) x10 (BitVec.ofNat 64 extraAddress)
    0x14ebc retired0 run0 (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite before.machine 0x14eb8 retired0 x10
        (BitVec.ofNat 64 extraAddress)).mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨retired1, run1⟩ := writeSuccessExtraDataLengthLoadStep _ args _
    args.decoded.payload.extraData.size access1 seg1.atPc
    (seg1.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)) lengthRep
    aligned loaded1
  have seg2 := seg1.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessBytesCallExitPc; native_decide) x11
    (BitVec.ofNat 64 args.decoded.payload.extraData.size) 0x14ec0 retired1 run1
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg access seg2
  obtain ⟨baseMachine, seg3⟩ := seg2.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessBytesCallExitPc; native_decide) x1 0x15ec0 0x14ec4
    (writeSuccessExtraDataCallBaseStep _ _ access2.configured seg2.atPc (by
      simpa [seg2.memEq (by simp)] using loaded))
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access3 := writeSuccessAccessOfSeg access seg3
  have loaded3 : Artifacts.programImage.fileBytesLoadedFaithfully baseMachine.mem := by
    simpa [seg3.memEq (by simp)] using loaded
  obtain ⟨retired3, callRun⟩ := writeSuccessExtraDataCallStep _ baseMachine
    access3.configured seg3.atPc (seg3.reg x1 0x15ec0 (by simp)) loaded3
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement baseMachine) 0x14ec4 0x15c6c x1 0x14ec8)
    0x15c6c retired3
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes baseMachine 0x14ec4 0x15c6c retired3 x1 0x14ec8
  have callAtPc : callMachine.regs.get? PC = some 0x15c6c := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callBaseMemEq : callMachine.mem = baseMachine.mem := by
    change
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement baseMachine) 0x14ec4 0x15c6c x1 0x14ec8)
        0x15c6c retired3).mem = baseMachine.mem
    rw [tryStepControlFlowAfterRetired_mem]
    change (controlFlowJumpState (tryStepControlFlowAfterIncrement baseMachine)
      0x14ec4 0x15c6c).mem = baseMachine.mem
    rw [controlFlowJumpState_mem]
    rfl
  have callMemEq : callMachine.mem = before.machine.mem :=
    callBaseMemEq.trans (seg3.memEq (by simp))
  let value : BytesEncoderValue :=
    { address := extraAddress, bytes := args.decoded.payload.extraData }
  let childArgs : EncoderCallArgs BytesEncoderValue :=
    { returnAddress := 0x14ec8
      callerStack := args.stackPointer - 0x7d0
      inputSize := args.inputSize
      value }
  have extraBytes : BytesRep before.machine.mem extraAddress
      args.decoded.payload.extraData := extraRep.byteSliceBytesRep
  have childEntry : EncoderCallEntry Elflings.writeSuccessBytesEntry
      Elflings.writeSuccessBytesExitPcs BytesEncoderBinding childArgs callState := by
    unfold EncoderCallEntry
    refine ⟨(by show 0x14ec8 ∈ Elflings.writeSuccessBytesExitPcs; native_decide),
      writeSuccessChildStackBound upper, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [callState] using callAtPc
    · simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, childArgs]
    · exact (callWrites.get x2 (by decide)).trans
        (seg3.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    · refine ⟨(by dsimp [childArgs, value]; simpa using extraBytes.1), ?_, ?_, ?_⟩
      · exact (callWrites.get x10 (by decide)).trans
          (seg3.reg x10 (BitVec.ofNat 64 extraAddress) (by simp))
      · exact (callWrites.get x11 (by decide)).trans
          (seg3.reg x11 (BitVec.ofNat 64 args.decoded.payload.extraData.size) (by simp))
      · simpa [childArgs, value, callState, callMemEq] using extraBytes
    · simpa [callState, callMemEq] using loaded
  obtain ⟨bytesBound, bytesImpl⟩ := bytesChild
  obtain ⟨childUsed, after, unit, _positive, _bounded, childTrace, _childPc, _allowed,
      childExit⟩ := bytesImpl childArgs (fromStep + 4) callState childEntry
  rcases childExit with ⟨afterPc, stdout, stdin, cursor, exitCode, _frameFits, childMem,
    childFrame⟩
  have callPrefix : ConfinedPrefix writeSuccessParentPc writeSuccessBytesCallExitPc
      (fun _ _ _ _ _ => False) (fromStep + 3) 1 baseMachine callMachine :=
    ConfinedPrefix.ownStep seg3.atPc
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessBytesCallExitPc; native_decide) callRun
  have callEnd : ScopedTrace writeSuccessParentPc writeSuccessBytesCallExitPc
      (fun _ _ _ _ _ => False) (fromStep + 4) 0 callMachine callMachine :=
    .exitAt _ _ 0x15c6c callAtPc rfl
  have parentMachineTrace := seg3.confined.trans callPrefix 0 callMachine callEnd
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 4 before callState := by
    simpa [callState] using liftWriteSuccessParentTrace before parentMachineTrace
  have childTrace' := childTrace.weaken (fun _ inside =>
    show pcInRanges Elflings.writeSuccessExecutionPcRanges _ from by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lo, hi⟩
      simp only [Elflings.writeSuccessBytesExecutionPcRanges, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, hi⟩)
  have exactMemory : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 - 48) 48) before.machine after.machine := by
    intro address outside
    rw [childMem address (by simpa [childArgs] using outside), callMemEq]
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have pmaEq := (childFrame.1 pma_regions (by simp [abiCalleePreserved])).trans callPmaEq
  have accessAfter : WriteSuccessMachineAccess args after.machine :=
    { configured := configuredAfterEndpointCall
        (configuredAfterWriteSuccessCall 0x14ec4 0x15c6c 0x14ec8 retired3 access3.configured)
        childFrame
      frameLoad := fun position width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access3.frameLoad position width bound)
      frameStore := fun position width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access3.frameStore position width bound)
      frameNoMMIO := access3.frameNoMMIO
      decodedLoad := fun position width bound =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access3.decodedLoad position width bound)
      decodedNoMMIO := access3.decodedNoMMIO
      outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq access3.outputBufferStore
      outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq access3.outputLengthStore
      writerRegionBeforeOutputContext := access3.writerRegionBeforeOutputContext
      frameNotCode := access3.frameNotCode }
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem := by
    intro address byte fileByte
    have outside : ¬byteRange (args.stackPointer - 0x7d0 - 48) 48 address := by
      intro inside
      have inWriter := writeSuccessChildFrame48_mem_frame lower inside
      unfold byteRange at inWriter
      rw [Nat.sub_add_cancel lower] at inWriter
      have notCode := access3.frameNotCode address inWriter.1 inWriter.2
      exact Option.some_ne_none byte (fileByte.symm.trans notCode)
    rw [exactMemory address outside]
    exact loaded address byte fileByte
  have payloadAfter := writeSuccessPayloadContextAfterBytes decodedAddress lower upper
    access.writerRegionBeforeOutputContext context exactMemory
  exact ⟨childUsed, after, {
    trace := by
      have all := parentTrace.append (by simpa [Nat.add_assoc] using childTrace')
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all
    atPc := afterPc
    stack := (childFrame.1 x2 (by simp [abiCalleePreserved])).trans
      ((callWrites.get x2 (by decide)).trans
        (seg3.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)))
    stdout := by simpa [callState, childArgs, value] using stdout
    stdin := by simpa [callState] using stdin
    cursor := by simpa [callState] using cursor
    exitCode := by simpa [callState] using exitCode
    memory := exactMemory
    loaded := loadedAfter
    access := accessAfter
    payload := payloadAfter }⟩

set_option genInjectivity false in
/-- The gas-limit, gas-used, and timestamp integer calls following the block-number call. -/
structure WriteSuccessThreeIntHandoff
    (fromStep gasLimitUsed gasUsedUsed timestampUsed : Nat) (args : WriteSuccessArgs)
    (bytes : Array UInt8) (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep
    (3 + gasLimitUsed + 3 + gasUsedUsed + 3 + timestampUsed) before after
  atPc : EndpointPc after = some 0x14eb8
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeNatLE 8 args.decoded.payload.gasLimit ++
    encodeNatLE 8 args.decoded.payload.gasUsed ++ encodeNatLE 8 args.decoded.payload.timestamp
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : WritesOnlyWithin
    (byteRange (args.stackPointer - 0x7d0 - 16) 16) before.machine after.machine
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  payload : WriteSuccessPayloadContext args bytes after

/-- Compose the three consecutive shared integer calls ending at the extra-data setup. -/
private theorem writeSuccessThreeIntHandoff
    (intChild : WriteSuccessIntInstanceContract) (fromStep : Nat) (args : WriteSuccessArgs)
    (bytes : Array UInt8) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x14e94)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args bytes before)
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ gasLimitUsed gasUsedUsed timestampUsed after,
      WriteSuccessThreeIntHandoff fromStep gasLimitUsed gasUsedUsed timestampUsed
        args bytes before after := by
  obtain ⟨gasLimitUsed, afterGasLimit, gasLimitCall⟩ :=
    writeSuccessIntCallHandoff intChild fromStep 0x14e94 0x14ea0 0x410
      args.decoded.payload.gasLimit 0x15e98 args before atPc stack context.payloadRep.2.1
      access loaded aligned lower upper (fun step state => writeSuccessGasLimitLoadStep step args state)
      writeSuccessGasLimitCallBaseStep writeSuccessGasLimitCallStep
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessIntCallExitPc; native_decide)
      (by unfold writeSuccessIntCallExitPc; native_decide)
      (by unfold writeSuccessIntCallExitPc; native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have contextGasLimit := writeSuccessPayloadContextAfterInt decodedAddress lower upper context
    gasLimitCall
  obtain ⟨gasUsedUsed, afterGasUsed, gasUsedCall⟩ :=
    writeSuccessIntCallHandoff intChild (fromStep + 3 + gasLimitUsed) 0x14ea0 0x14eac 0x418
      args.decoded.payload.gasUsed 0x15ea4 args afterGasLimit gasLimitCall.atPc gasLimitCall.stack
      contextGasLimit.payloadRep.2.2.1 gasLimitCall.access gasLimitCall.loaded aligned lower upper
      (fun step state => writeSuccessGasUsedLoadStep step args state)
      writeSuccessGasUsedCallBaseStep writeSuccessGasUsedCallStep
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessIntCallExitPc; native_decide)
      (by unfold writeSuccessIntCallExitPc; native_decide)
      (by unfold writeSuccessIntCallExitPc; native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have contextGasUsed := writeSuccessPayloadContextAfterInt decodedAddress lower upper
    contextGasLimit gasUsedCall
  obtain ⟨timestampUsed, after, timestampCall⟩ :=
    writeSuccessIntCallHandoff intChild
      (fromStep + 3 + gasLimitUsed + 3 + gasUsedUsed) 0x14eac 0x14eb8 0x420
      args.decoded.payload.timestamp 0x15eb0 args afterGasUsed gasUsedCall.atPc gasUsedCall.stack
      contextGasUsed.payloadRep.2.2.2.1 gasUsedCall.access gasUsedCall.loaded aligned lower upper
      (fun step state => writeSuccessTimestampLoadStep step args state)
      writeSuccessTimestampCallBaseStep writeSuccessTimestampCallStep
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessParentPc; exact
        ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessIntCallExitPc; native_decide)
      (by unfold writeSuccessIntCallExitPc; native_decide)
      (by unfold writeSuccessIntCallExitPc; native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have contextTimestamp := writeSuccessPayloadContextAfterInt decodedAddress lower upper
    contextGasUsed timestampCall
  refine ⟨gasLimitUsed, gasUsedUsed, timestampUsed, after, {
    trace := ?_
    atPc := timestampCall.atPc
    stack := timestampCall.stack
    stdout := ?_
    stdin := timestampCall.stdin.trans (gasUsedCall.stdin.trans gasLimitCall.stdin)
    cursor := timestampCall.cursor.trans (gasUsedCall.cursor.trans gasLimitCall.cursor)
    exitCode := timestampCall.exitCode.trans (gasUsedCall.exitCode.trans gasLimitCall.exitCode)
    memory := WritesOnlyWithin.trans_same gasLimitCall.memory
      (WritesOnlyWithin.trans_same gasUsedCall.memory timestampCall.memory)
    loaded := timestampCall.loaded
    access := timestampCall.access
    payload := contextTimestamp }⟩
  · have firstTwo := gasLimitCall.trace.append (by
      simpa [Nat.add_assoc] using gasUsedCall.trace)
    have all := firstTwo.append (by simpa [Nat.add_assoc] using timestampCall.trace)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all
  · rw [timestampCall.stdout, gasUsedCall.stdout, gasLimitCall.stdout]

set_option genInjectivity false in
/-- All scalar/byte encoder calls after block number and before the block-hash field. -/
structure WriteSuccessPostBlockNumberHandoff
    (fromStep gasLimitUsed gasUsedUsed timestampUsed extraDataUsed baseFeeUsed : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep
    (3 + gasLimitUsed + 3 + gasUsedUsed + 3 + timestampUsed + 4 + extraDataUsed +
      3 + baseFeeUsed) before after
  atPc : EndpointPc after = some 0x14ed4
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeNatLE 8 args.decoded.payload.gasLimit ++
    encodeNatLE 8 args.decoded.payload.gasUsed ++ encodeNatLE 8 args.decoded.payload.timestamp ++
    encodeBytes args.decoded.payload.extraData ++ encodeNatLE 8 args.decoded.payload.baseFeePerGas
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : WritesOnlyWithin
    (byteRange (args.stackPointer - 0x7d0 - 48) 48) before.machine after.machine
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  payload : WriteSuccessPayloadContext args payloadBytes after

/-- Compose gas limit, gas used, timestamp, extra data, and base fee in production order. -/
private theorem writeSuccessPostBlockNumberHandoff
    (intChild : WriteSuccessIntInstanceContract) (bytesChild : WriteSuccessBytesInstanceContract)
    (fromStep : Nat) (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (before : EndpointState) (atPc : before.machine.regs.get? PC = some 0x14e94)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ gasLimitUsed gasUsedUsed timestampUsed extraDataUsed baseFeeUsed after,
      WriteSuccessPostBlockNumberHandoff fromStep gasLimitUsed gasUsedUsed timestampUsed
        extraDataUsed baseFeeUsed args payloadBytes before after := by
  obtain ⟨gasLimitUsed, gasUsedUsed, timestampUsed, afterThree, three⟩ :=
    writeSuccessThreeIntHandoff intChild fromStep args payloadBytes before atPc stack context
      access loaded aligned lower upper decodedAddress
  let afterThreeStep := fromStep + 3 + gasLimitUsed + 3 + gasUsedUsed + 3 + timestampUsed
  obtain ⟨extraDataUsed, afterExtra, extra⟩ := writeSuccessExtraDataHandoff bytesChild
    afterThreeStep args payloadBytes afterThree three.atPc three.stack three.payload three.access
    three.loaded aligned lower upper decodedAddress
  let afterExtraStep := afterThreeStep + 4 + extraDataUsed
  obtain ⟨baseFeeUsed, after, baseFee⟩ := writeSuccessIntCallHandoff intChild afterExtraStep
    0x14ec8 0x14ed4 0x438 args.decoded.payload.baseFeePerGas 0x15ecc args afterExtra
    extra.atPc extra.stack extra.payload.payloadRep.2.2.2.2.2.1 extra.access extra.loaded aligned
    lower upper (fun step state => writeSuccessBaseFeeLoadStep step args state)
    writeSuccessBaseFeeCallBaseStep writeSuccessBaseFeeCallStep
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by native_decide) (by native_decide) (by native_decide)

  have payloadAfter := writeSuccessPayloadContextAfterInt decodedAddress lower upper extra.payload
    baseFee
  have threeMemory : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 - 48) 48) before.machine afterThree.machine :=
    three.memory.mono (by
      intro address inside
      exact writeSuccessChild16_in_child48 lower inside)
  have baseFeeMemory : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 - 48) 48) afterExtra.machine after.machine :=
    baseFee.memory.mono (by
      intro address inside
      exact writeSuccessChild16_in_child48 lower inside)
  refine ⟨gasLimitUsed, gasUsedUsed, timestampUsed, extraDataUsed, baseFeeUsed, after, {
    trace := ?_
    atPc := baseFee.atPc
    stack := baseFee.stack
    stdout := ?_
    stdin := baseFee.stdin.trans (extra.stdin.trans three.stdin)
    cursor := baseFee.cursor.trans (extra.cursor.trans three.cursor)
    exitCode := baseFee.exitCode.trans (extra.exitCode.trans three.exitCode)
    memory := WritesOnlyWithin.trans_same threeMemory
      (WritesOnlyWithin.trans_same extra.memory baseFeeMemory)
    loaded := baseFee.loaded
    access := baseFee.access
    payload := payloadAfter }⟩
  · have throughExtra := three.trace.append (by
      simpa [afterThreeStep, Nat.add_assoc] using extra.trace)
    have all := throughExtra.append (by
      simpa [afterThreeStep, afterExtraStep, Nat.add_assoc] using baseFee.trace)
    simpa [afterThreeStep, afterExtraStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all
  · rw [baseFee.stdout, extra.stdout, three.stdout]

set_option genInjectivity false in
/-- Parent block-hash pointer setup followed by the selected raw encoder. -/
structure WriteSuccessBlockHashHandoff
    (fromStep childUsed : Nat) (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (1 + childUsed) before after
  atPc : EndpointPc after = some 0x14ee4
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ args.decoded.payload.blockHash
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  memory : after.machine.mem = before.machine.mem
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  payload : WriteSuccessPayloadContext args payloadBytes after

/-- Execute `addi a0,sp,0x634` and consume the selected block-hash raw encoder. -/
private theorem writeSuccessBlockHashHandoff
    (child : WriteSuccessBlockHashInstanceContract) (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x14ed4)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem) :
    ∃ childUsed after,
      WriteSuccessBlockHashHandoff fromStep childUsed args payloadBytes before after := by
  have seg0 : Seg writeSuccessParentPc (fun pc => pc = 0x14ed8)
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine 0x14ed4 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  obtain ⟨pointerMachine, seg1⟩ := seg0.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14e88, 0x14ed8), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) x10 (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x634)) 0x14ed8
    (writeSuccessBlockHashSourceStep _ before.machine (args.stackPointer - 0x7d0)
      access.configured atPc stack loaded)
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  let pointerState : EndpointState := { before with machine := pointerMachine }
  have pointerTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 1 before pointerState := by
    have machineTrace := seg1.confined 0 pointerMachine
      (.exitAt _ _ 0x14ed8 seg1.atPc rfl)
    simpa [pointerState] using liftWriteSuccessParentTrace before machineTrace
  let rawArgs : RawEncoderArgs :=
    { sourceAddress := args.stackPointer - 0x7d0 + 0x634
      bytes := args.decoded.payload.blockHash }
  have payloadFields := context.payloadRep
  rcases payloadFields with ⟨blockNumber, gasLimit, gasUsed, timestamp, extraData, baseFee,
    transactions, rawTransactions, withdrawals, blobGasUsed, excessBlobGas, slotNumber,
    blockAccessList, parentHashSize, parentHash, feeRecipientSize, feeRecipient, stateRootSize,
    stateRoot, receiptsRootSize, receiptsRoot, logsBloomSize, logsBloom, prevRandaoSize,
    prevRandao, blockHashSize, blockHash⟩
  have blockHashRep : BytesRep pointerMachine.mem rawArgs.sourceAddress rawArgs.bytes := by
    simpa [rawArgs, seg1.memEq (by simp)] using blockHash
  have childEntry : RawEncoderEntry Elflings.writeSuccessRawLine147Entry rawArgs pointerState := by
    refine ⟨?_, ?_, blockHashRep, ?_⟩
    · simpa [pointerState, EndpointPc, MachinePc] using seg1.atPc
    · simpa [pointerState] using
        seg1.reg x10 (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x634)) (by simp)
    · simpa [pointerState, seg1.memEq (by simp)] using loaded
  obtain ⟨childUsed, after, _childBounded, childTrace, childExit⟩ :=
    writeSuccessRawEncoderHandoff child
    (fun inside => by
      simpa [Elflings.writeSuccessRawLine147ExecutionPcRanges] using
        writeSuccessRawPc_in_writeSuccess inside (by omega) (by omega))
    (fromStep + 1) rawArgs pointerState childEntry
  rcases childExit with ⟨afterPc, stdout, stdin, cursor, exitCode, childMem, childFrame⟩
  have memory : after.machine.mem = before.machine.mem :=
    childMem.trans (seg1.memEq (by simp))
  have pmaEq := childFrame.1 pma_regions (by simp [abiCalleePreserved])
  have parentPmaEq := seg1.writes.get pma_regions (by simp [writeSuccessParentWrites])
  have fullPmaEq := pmaEq.trans parentPmaEq
  have childAccess : WriteSuccessMachineAccess args after.machine :=
    { configured := configuredAfterEndpointCall (writeSuccessAccessOfSeg access seg1).configured
        childFrame
      frameLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq fullPmaEq (access.frameLoad offset width inBounds)
      frameStore := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq fullPmaEq (access.frameStore offset width inBounds)
      frameNoMMIO := access.frameNoMMIO
      decodedLoad := fun offset width inBounds =>
        dataPmaAllows_of_pma_regions_eq fullPmaEq (access.decodedLoad offset width inBounds)
      decodedNoMMIO := access.decodedNoMMIO
      outputBufferStore := dataPmaAllows_of_pma_regions_eq fullPmaEq access.outputBufferStore
      outputLengthStore := dataPmaAllows_of_pma_regions_eq fullPmaEq access.outputLengthStore
      writerRegionBeforeOutputContext := access.writerRegionBeforeOutputContext
      frameNotCode := access.frameNotCode }
  refine ⟨childUsed, after, {
    trace := by
      have all := pointerTrace.append (by simpa [Nat.add_assoc] using childTrace)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all
    atPc := afterPc
    stack := (childFrame.1 x2 (by simp [abiCalleePreserved])).trans
      (seg1.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    stdout := by simpa [rawArgs, pointerState] using stdout
    stdin := by simpa [pointerState] using stdin
    cursor := by simpa [pointerState] using cursor
    exitCode := by simpa [pointerState] using exitCode
    memory := memory
    loaded := by simpa [memory] using loaded
    access := childAccess
    payload := {
      fullCopy := by simpa [memory] using context.fullCopy
      destinationRep := by simpa [memory] using context.destinationRep
      parentRootRep := by simpa [memory] using context.parentRootRep
      decodedBytesRep := by simpa [memory] using context.decodedBytesRep
      versionedHashesRelocation := by simpa [memory] using context.versionedHashesRelocation
      bytesSize := context.bytesSize
      stable := by simpa [memory] using context.stable
      payloadRep := by simpa [memory] using context.payloadRep
      slotWord := by simpa [memory] using context.slotWord
      slotTagWord := by simpa [memory] using context.slotTagWord
      localTailReps := by
        obtain ⟨tailValues, tailReps⟩ := context.localTailReps
        refine ⟨tailValues, ?_⟩
        intro word member
        rw [memory]
        exact tailReps word member
      linkedTailReps := by
        obtain ⟨tailValues, localReps, sourceReps⟩ := context.linkedTailReps
        refine ⟨tailValues, ?_, ?_⟩
        · intro word member
          rw [memory]
          exact localReps word member
        · intro index bound
          rw [memory]
          exact sourceReps index bound } }⟩

/-- Production `0x14ee4: ld a0,0x440(sp)`. -/
private theorem writeSuccessTransactionsPointerLoadStep (stepNo : Nat)
    (args : WriteSuccessArgs) (state : State) (address : Nat)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x14ee4)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x440) address)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14ee4 retired x10 (BitVec.ofNat 64 address)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x14ee4 0x440 address args state
    (.Regidx 10#5) x10 (BitVec.ofNat 64 address) 0x440 0x03 0x35 0x01 0x44
    access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x440#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x10_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x14ee8: sd a0,0x68(sp)`. -/
private theorem writeSuccessTransactionsPointerStoreStep (stepNo : Nat)
    (args : WriteSuccessArgs) (state : State) (address : Nat)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x14ee8)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (data : state.regs.get? x10 = some (BitVec.ofNat 64 address))
    (aligned : args.stackPointer % 16 = 0)
    (upper : args.stackPointer < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x14ee8)
          (args.stackPointer - 0x7d0 + 104) (BitVec.ofNat 64 address))
        0x14ee8 retired) false := by
  apply writeSuccessFrameDwordStoreStep stepNo 0x14ee8 104 address args state 0x068
    0x23 0x34 0xa1 0x06 access atPc stack data (by omega) (by omega) loaded upper
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x68#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessStoreDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x14eec: ld a0,0x448(sp)`. -/
private theorem writeSuccessTransactionsCountLoadStep (stepNo : Nat)
    (args : WriteSuccessArgs) (state : State) (count : Nat)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x14eec)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x448) count)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14eec retired x10 (BitVec.ofNat 64 count)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x14eec 0x448 count args state
    (.Regidx 10#5) x10 (BitVec.ofNat 64 count) 0x448 0x03 0x35 0x81 0x44
    access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x448#64 = _
    rw [← BitVec.ofNat_add]
  · intro premise
    exact wX_x10_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x14ef0: sd a0,0x70(sp)`. -/
private theorem writeSuccessTransactionsCountStoreStep (stepNo : Nat)
    (args : WriteSuccessArgs) (state : State) (count : Nat)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x14ef0)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (data : state.regs.get? x10 = some (BitVec.ofNat 64 count))
    (aligned : args.stackPointer % 16 = 0)
    (upper : args.stackPointer < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x14ef0)
          (args.stackPointer - 0x7d0 + 112) (BitVec.ofNat 64 count))
        0x14ef0 retired) false := by
  apply writeSuccessFrameDwordStoreStep stepNo 0x14ef0 112 count args state 0x070
    0x23 0x38 0xa1 0x06 access atPc stack data (by omega) (by omega) loaded upper
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x70#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessStoreDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x15668: ld a0,0x450(sp)`. -/
private theorem writeSuccessRawTransactionsAddressLoadStep (stepNo : Nat)
    (args : WriteSuccessArgs) (state : State) (address : Nat)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x15668)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x450) address)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15668 retired x10 (BitVec.ofNat 64 address)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x15668 0x450 address args state
    (.Regidx 10#5) x10 (BitVec.ofNat 64 address) 0x450 0x03 0x35 0x01 0x45
    access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x450#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x1566c: ld a1,0x458(sp)`. -/
private theorem writeSuccessRawTransactionsCountLoadStep (stepNo : Nat)
    (args : WriteSuccessArgs) (state : State) (count : Nat)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x1566c)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x458) count)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1566c retired x11 (BitVec.ofNat 64 count)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x1566c 0x458 count args state
    (.Regidx 11#5) x11 (BitVec.ofNat 64 count) 0x458 0x83 0x35 0x81 0x45
    access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x458#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x11_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x15670: auipc ra,0`. -/
private theorem writeSuccessByteListsCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15670)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15670 retired x1 0x15670) false := by
  apply configuredAuipcStep stepNo state 0x15670 0 0x97 0x00 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x15674: jalr ra,0x5a0(ra)`, entering the byte-list encoder. -/
private theorem writeSuccessByteListsCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15674)
    (baseRead : state.regs.get? x1 = some 0x15670)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x15674 0x15c10 x1 0x15678)
        0x15c10 retired) false := by
  apply configuredJalrCallStep stepNo state 0x15674 0x15670 0x5a0 0x15c10 0x15678
    0xe7 0x80 0x00 0x5a configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x15678: ld s0,0x460(sp)`. -/
private theorem writeSuccessWithdrawalsAddressLoadStep (stepNo : Nat)
    (args : WriteSuccessArgs) (state : State) (address : Nat)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x15678)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x460) address)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15678 retired x8 (BitVec.ofNat 64 address)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x15678 0x460 address args state
    (.Regidx 8#5) x8 (BitVec.ofNat 64 address) 0x460 0x03 0x34 0x01 0x46
    access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x460#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x8_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x1567c: ld s1,0x468(sp)`. -/
private theorem writeSuccessWithdrawalsCountLoadStep (stepNo : Nat)
    (args : WriteSuccessArgs) (state : State) (count : Nat)
    (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x1567c)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x468) count)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1567c retired x9 (BitVec.ofNat 64 count)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x1567c 0x468 count args state
    (.Regidx 9#5) x9 (BitVec.ofNat 64 count) 0x468 0x83 0x34 0x81 0x46
    access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x468#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x9_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

set_option genInjectivity false in
/-- Exact four-instruction transactions setup followed by the selected optimized encoder. -/
structure WriteSuccessTransactionsHandoff (fromStep childUsed : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (before after : EndpointState)
    (values : DecodeCalleeSavedValues) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (4 + childUsed) before after
  atPc : EndpointPc after = some 0x15668
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeMany encodeTransaction
    args.decoded.payload.transactions
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  decoded : StatelessInputRep after.machine.mem args.decodedAddress args.decoded
  payload : ExecutionPayloadRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine
  payloadContext : WriteSuccessPayloadContext args payloadBytes after

private theorem writeSuccessTransactionsHandoff
    (child : WriteSuccessTransactionsInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues)
    (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x14ee4)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessTransactionsHandoff fromStep childUsed args payloadBytes before after values := by
  rcases context.payloadRep with ⟨blockNumber, gasLimit, gasUsed, timestamp, extraData, baseFee,
    transactions, rawTransactions, withdrawals, blobGasUsed, excessBlobGas, slotNumber,
    blockAccessList, parentHashSize, parentHash, feeRecipientSize, feeRecipient, stateRootSize,
    stateRoot, receiptsRootSize, receiptsRoot, logsBloomSize, logsBloom, prevRandaoSize,
    prevRandao, blockHashSize, blockHash⟩
  rcases transactions with ⟨transactionAddress, transactionAddressRep, transactionCountRep,
    transactionArrayRep⟩
  let setupMemory := writeSuccessTransactionSetupMemory args
  have setupInWriter : ∀ address, writeSuccessTransactionSetupMemory args address →
      writeSuccessFrameMemory args address := by
    intro address inside
    unfold writeSuccessTransactionSetupMemory at inside
    unfold writeSuccessFrameMemory
    unfold byteRange at inside ⊢
    rcases inside with inside | inside <;> omega
  have codeOfSeg {kv n cur pc}
      (seg : Seg writeSuccessParentPc (fun pc => pc = 0x14ef4)
        (fun _ _ _ _ _ => False) writeSuccessParentWrites setupMemory kv fromStep n
        before.machine cur pc) :
      Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
    intro address byte fileByte
    have unchanged := seg.mem address (by
      intro inside
      have inWriter := setupInWriter address inside
      unfold writeSuccessFrameMemory byteRange at inWriter
      have none := access.frameNotCode address inWriter.1 (by omega)
      rw [fileByte] at none
      cases none)
    exact unchanged.trans (loaded address byte fileByte)
  have seg0 : Seg writeSuccessParentPc (fun pc => pc = 0x14ef4)
      (fun _ _ _ _ _ => False) writeSuccessParentWrites setupMemory
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine 0x14ee4 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  obtain ⟨retired0, run0⟩ := writeSuccessTransactionsPointerLoadStep fromStep args
    before.machine transactionAddress access atPc stack transactionAddressRep aligned loaded
  obtain ⟨machine1, seg1⟩ := seg0.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14ee4, 0x14ef4), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) x10 (BitVec.ofNat 64 transactionAddress) 0x14ee8 ⟨retired0, run0⟩
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have loaded1 := codeOfSeg seg1
  obtain ⟨retired1, run1⟩ := writeSuccessTransactionsPointerStoreStep (fromStep + 1) args
    machine1 transactionAddress access1 seg1.atPc
    (seg1.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    (seg1.reg x10 (BitVec.ofNat 64 transactionAddress) (by simp)) aligned upper loaded1
  obtain ⟨retired1', machine2, machine2Eq, seg2⟩ := seg1.stepStoreWitness
    (width := 8) (args.stackPointer - 0x7d0 + 104) (BitVec.ofNat 64 transactionAddress)
    0x14eec
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14ee4, 0x14ef4), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) ⟨retired1, run1⟩ (by native_decide)
    (by intro address lo hi; exact Or.inl ⟨lo, hi⟩)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have seg2' := seg2.forget (kv' :=
    [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]) (by simp)
  have access2 := writeSuccessAccessOfSeg access seg2'
  have loaded2 := codeOfSeg seg2'
  obtain ⟨retired2, run2⟩ := writeSuccessTransactionsCountLoadStep (fromStep + 2) args
    machine2 args.decoded.payload.transactions.size access2 seg2'.atPc
    (seg2'.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    (transactionCountRep.of_writesOnlyWithin seg2'.mem (by
      intro index inBounds inside
      unfold setupMemory writeSuccessTransactionSetupMemory byteRange at inside
      omega)) aligned loaded2
  obtain ⟨retired2', machine3, machine3Eq, seg3⟩ := seg2'.stepWitness
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14ee4, 0x14ef4), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) x10 (BitVec.ofNat 64 args.decoded.payload.transactions.size) 0x14ef0
    ⟨retired2, by simpa [Nat.add_assoc] using run2⟩
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access3 := writeSuccessAccessOfSeg access seg3
  have loaded3 := codeOfSeg seg3
  obtain ⟨retired3, run3⟩ := writeSuccessTransactionsCountStoreStep (fromStep + 3) args
    machine3 args.decoded.payload.transactions.size access3 seg3.atPc
    (seg3.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    (seg3.reg x10 (BitVec.ofNat 64 args.decoded.payload.transactions.size) (by simp))
    aligned upper loaded3
  obtain ⟨retired3', machine4, machine4Eq, seg4⟩ := seg3.stepStoreWitness
    (width := 8) (args.stackPointer - 0x7d0 + 112)
    (BitVec.ofNat 64 args.decoded.payload.transactions.size) 0x14ef4
    (by unfold writeSuccessParentPc; exact
      ⟨(0x14ee4, 0x14ef4), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) ⟨retired3, run3⟩ (by native_decide)
    (by intro address lo hi; exact Or.inr ⟨lo, hi⟩)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  let childState : EndpointState := { before with machine := machine4 }
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 4 before childState := by
    have machineTrace := seg4.confined 0 machine4 (.exitAt _ _ 0x14ef4 seg4.atPc rfl)
    simpa [childState] using liftWriteSuccessParentTrace before machineTrace
  have setupWrites : WriteSuccessMemoryFrame args before.machine machine4 :=
    seg4.mem.mono setupInWriter
  have decodedAtChild := context.stable.of_writesOnlyWithin
    (setupWrites.mono (fun _ inside => Or.inl inside))
  have stableAtChild := context.stable.afterWrites
    (setupWrites.mono (fun _ inside => Or.inl inside))
  have destinationAtChild := context.destinationRep.of_writesOnlyWithin seg4.mem (by
    intro index inBounds inside
    unfold setupMemory writeSuccessTransactionSetupMemory byteRange at inside
    omega)
  have decodedBytesAtChild := context.decodedBytesRep.of_writesOnlyWithin seg4.mem (by
    intro index inBounds inside
    unfold setupMemory writeSuccessTransactionSetupMemory byteRange at inside
    rw [decodedEq] at inside
    omega)
  have payloadAtChild : ExecutionPayloadRep machine4.mem
      (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload :=
    (decodedAtChild.2.1).rebase (by omega) (by
      have relocation := ByteWindowRelocation.of_same_bytes decodedBytesAtChild destinationAtChild
      have bound : 592 ≤ payloadBytes.size := by rw [context.bytesSize]; decide
      simpa using relocation.atOffset 0 592 bound)
  have savedAtChild : InlineEncoderSavedWords machine4.mem
      (writeSuccessSavedWords args values) := by
    intro word member
    exact (saved word member).of_writesOnlyWithin seg4.mem (by
      intro index inBounds inside
      unfold setupMemory writeSuccessTransactionSetupMemory byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  have pointerLocal : UIntRep 8 machine4.mem
      (args.stackPointer - 0x7d0 + 104) transactionAddress := by
    have atMachine2 : UIntRep 8 machine2.mem
        (args.stackPointer - 0x7d0 + 104) transactionAddress := by
      rw [machine2Eq]
      simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
        uintRep_afterWriteBytes_eight
          (coreStoreNextState (tryStepStoreAfterIncrement machine1) 0x14ee8)
          (args.stackPointer - 0x7d0 + 104) transactionAddress
          (by exact transactionAddressRep.1) (by omega)
    have atMachine3 : UIntRep 8 machine3.mem
        (args.stackPointer - 0x7d0 + 104) transactionAddress := by
      rw [machine3Eq]
      simpa using atMachine2
    rw [machine4Eq]
    exact atMachine3.of_writesOnlyWithin
      (storeRetirement_mem_writes (width := 8) machine3 0x14ef0 0x14ef4 retired3'
        (args.stackPointer - 0x7d0 + 112)
        (BitVec.ofNat 64 args.decoded.payload.transactions.size)) (by
          intro index inBounds inside
          omega)
  rcases payloadAtChild with ⟨blockNumber4, gasLimit4, gasUsed4, timestamp4, extraData4,
    baseFee4, transactions4, rawTransactions4, withdrawals4, blobGasUsed4, excessBlobGas4,
    slotNumber4, blockAccessList4, parentHashSize4, parentHash4, feeRecipientSize4,
    feeRecipient4, stateRootSize4, stateRoot4, receiptsRootSize4, receiptsRoot4,
    logsBloomSize4, logsBloom4, prevRandaoSize4, prevRandao4, blockHashSize4, blockHash4⟩
  rcases transactions4 with ⟨transactionAddress4, addressRep4, countRep4, arrayRep4⟩
  have originalAddressAtChild := transactionAddressRep.of_writesOnlyWithin seg4.mem (by
    intro index inBounds inside
    unfold setupMemory writeSuccessTransactionSetupMemory byteRange at inside
    rcases inside with inside | inside <;> omega)
  have sameAddress : transactionAddress4 = transactionAddress :=
    UIntRep.eight_unique addressRep4 originalAddressAtChild
  subst transactionAddress4
  obtain ⟨tailValues, tailBefore, tailSourceBefore⟩ := context.linkedTailReps
  have tailAtChild : InlineEncoderSavedWords childState.machine.mem
      (writeSuccessLocalTailWords args tailValues) := by
    intro word member
    exact (tailBefore word member).of_writesOnlyWithin seg4.mem (by
      intro index inBounds inside
      unfold setupMemory writeSuccessTransactionSetupMemory byteRange at inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> rcases inside with inside | inside <;> omega)
  have retainedAtChild : InlineEncoderSavedWords childState.machine.mem
      (writeSuccessSavedWords args values ++ writeSuccessLocalTailWords args tailValues) := by
    intro word member
    rw [List.mem_append] at member
    exact member.elim (savedAtChild word) (tailAtChild word)
  obtain ⟨fullCopyBytes, fullCopySize, fullDecodedRep, fullCopyRep⟩ := context.fullCopy
  let childArgs : InlineEncoderArgs (InlineArrayEncoderValue Transaction) :=
    { stackPointer := args.stackPointer - 0x7d0
      inputSize := args.inputSize
      value := ⟨transactionAddress, args.decoded.payload.transactions⟩
      savedWords := writeSuccessSavedWords args values ++ writeSuccessLocalTailWords args tailValues
      decodedAddress := args.decodedAddress
      copiedParentRootAddress := args.stackPointer - 0x7d0 + 0x3e8
      copiedVersionedHashesAddress := args.stackPointer - 0x7d0 + 0x388
      copiedPayloadAddress := args.stackPointer - 0x7d0 + 0x408
      copiedSourceAddress := args.stackPointer - 0x7d0 + 0x138
      copiedParentRootBytes := args.decoded.parentBeaconBlockRoot
      copiedPayloadBytes := payloadBytes
      copiedSourceBytes := fullCopyBytes
      decoded := args.decoded }
  have childEntry : InlineEncoderEntry Elflings.writeSuccessTransactionsEntry
      (InlineArrayEncoderBinding
        (fun state count => state.machine.regs.get? x10 = some (BitVec.ofNat 64 count))
        (fun state address => ∃ stackPointer,
          state.machine.regs.get? x2 = some (BitVec.ofNat 64 stackPointer) ∧
          UIntRep 8 state.machine.mem (stackPointer + 104) address)
        288 TransactionRep) childArgs childState := by
    change 0xb0 ≤ args.stackPointer - 0x7d0 ∧
      args.stackPointer - 0x7d0 + 0x740 ≤ 2 ^ 64 ∧ _
    refine ⟨(by omega), (by omega), ?_, ?_, ?_, retainedAtChild, decodedAtChild, rfl, ?_, ?_,
      ?_, destinationAtChild, ?_⟩
    · simpa [childState, EndpointPc, MachinePc] using seg4.atPc
    · simpa [childState] using
        seg4.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
    · refine ⟨(by simpa using arrayRep4.1), ?_, ?_, arrayRep4⟩
      · simpa [childState, childArgs] using
          seg4.reg x10 (BitVec.ofNat 64 args.decoded.payload.transactions.size) (by simp)
      · exact ⟨args.stackPointer - 0x7d0, by
          simpa [childState] using
          seg4.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp), pointerLocal⟩
    · exact context.parentRootRep.of_writesOnlyWithin seg4.mem (by
        intro index inBounds inside
        unfold setupMemory writeSuccessTransactionSetupMemory byteRange at inside
        rcases inside with inside | inside <;> omega)
    · dsimp [childArgs]
      intro index inBounds
      rw [seg4.mem _ (by
        intro inside
        unfold setupMemory writeSuccessTransactionSetupMemory byteRange at inside
        rcases inside with inside | inside <;> omega),
        context.versionedHashesRelocation index inBounds,
        seg4.mem _ (by
          intro inside
          unfold setupMemory writeSuccessTransactionSetupMemory byteRange at inside
          rw [decodedEq] at inside
          rcases inside with inside | inside <;> omega)]
    · exact ⟨blockNumber4, gasLimit4, gasUsed4, timestamp4, extraData4, baseFee4,
        ⟨transactionAddress, addressRep4, countRep4, arrayRep4⟩, rawTransactions4,
        withdrawals4, blobGasUsed4, excessBlobGas4, slotNumber4, blockAccessList4,
        parentHashSize4, parentHash4, feeRecipientSize4, feeRecipient4, stateRootSize4,
        stateRoot4, receiptsRootSize4, receiptsRoot4, logsBloomSize4, logsBloom4,
        prevRandaoSize4, prevRandao4, blockHashSize4, blockHash4⟩
    · exact ⟨fullDecodedRep.of_writesOnlyWithin seg4.mem (by
        intro index inBounds inside
        unfold setupMemory writeSuccessTransactionSetupMemory byteRange at inside
        rcases inside with inside | inside <;> omega),
      fullCopyRep.of_writesOnlyWithin seg4.mem (by
        intro index inBounds inside
        unfold setupMemory writeSuccessTransactionSetupMemory byteRange at inside
        rcases inside with inside | inside <;> omega), codeOfSeg seg4⟩
  obtain ⟨childUsed, after, _childBounded, childTrace, childExit⟩ :=
    writeSuccessInlineEncoderHandoff child
    (fun inside => by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, rangeLower, rangeUpper⟩
      simp [Elflings.writeSuccessTransactionsExecutionPcRanges] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges],
          rangeLower, rangeUpper⟩
      · exact ⟨(0x101d4, 0x101f8), by simp [Elflings.writeSuccessExecutionPcRanges],
          rangeLower, rangeUpper⟩
      · exact ⟨(0x14d30, 0x15a14), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩)
    (fromStep + 4) childArgs childState childEntry
  rcases childExit with ⟨afterPc, stdout, stdin, cursor, exitCode, stackAfter,
    bindingAfter, savedAfter, decodedAfter, parentRootAfter, versionedHashesAfter,
    payloadAfter, destinationAfter, sourceAfter, copiedSourceAfter,
    childMemory, childAgree, childRetired, loadedAfter⟩
  have childInWriter : ∀ address, inlineEncoderMemoryRegion childArgs.stackPointer address →
      writeSuccessFrameMemory args address := by
    intro address inside
    unfold inlineEncoderMemoryRegion at inside
    unfold writeSuccessFrameMemory
    unfold byteRange at inside ⊢
    dsimp [childArgs] at inside
    omega
  have fullMemory := WritesOnlyWithin.trans_same setupWrites (childMemory.mono childInWriter)
  have decodedBytesAfter := context.decodedBytesRep.of_writesOnlyWithin fullMemory (by
    intro index inBounds inside
    unfold writeSuccessFrameMemory byteRange at inside
    rw [decodedEq] at inside
    omega)
  have stableAfter := context.stable.afterWrites
    (fullMemory.mono (fun _ inside => Or.inl inside))
  obtain ⟨slotValue, slotRep⟩ := context.slotWord
  have slotFits : args.stackPointer - 0x7d0 + 0x480 + 8 ≤ 2 ^ 64 := by
    have fit := destinationAfter.1
    rw [context.bytesSize] at fit
    dsimp [childArgs] at fit
    omega
  have slotAfter := slotRep.rebase slotFits
    ((ByteWindowRelocation.of_same_bytes context.destinationRep destinationAfter).atOffset
      0x78 8 (by rw [context.bytesSize]; omega))
  obtain ⟨tagValue, tagRep⟩ := context.slotTagWord
  have tagFits : args.stackPointer - 0x7d0 + 0x488 + 8 ≤ 2 ^ 64 := by
    have fit := destinationAfter.1
    rw [context.bytesSize] at fit
    dsimp [childArgs] at fit
    omega
  have tagAfter := tagRep.rebase tagFits
    ((ByteWindowRelocation.of_same_bytes context.destinationRep destinationAfter).atOffset
      0x80 8 (by rw [context.bytesSize]; omega))
  have accessAtChild := writeSuccessAccessOfSeg access seg4
  have savedAbiAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact savedAfter word (List.mem_append_left _ member)
  have tailAfter : InlineEncoderSavedWords after.machine.mem
      (writeSuccessLocalTailWords args tailValues) := by
    intro word member
    exact savedAfter word (List.mem_append_right _ member)
  have tailSourceAfter : ∀ index (bound : index < 16),
      UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
        (tailValues ⟨index, bound⟩) := by
    intro index bound
    exact (tailSourceBefore index bound).of_writesOnlyWithin fullMemory (by
      intro byte byteBound inside
      unfold writeSuccessFrameMemory byteRange at inside
      rw [decodedEq] at inside
      omega)
  have pmaEq := childAgree pma_regions (by simp [inlineEncoderPreserved])
  have accessAfter : WriteSuccessMachineAccess args after.machine := {
    configured := accessAtChild.configured.mono
      (childAgree.weaken instructionPreserved_inlineEncoderPreserved) childRetired
    frameLoad := fun offset width inBounds =>
      dataPmaAllows_of_pma_regions_eq pmaEq (accessAtChild.frameLoad offset width inBounds)
    frameStore := fun offset width inBounds =>
      dataPmaAllows_of_pma_regions_eq pmaEq (accessAtChild.frameStore offset width inBounds)
    frameNoMMIO := accessAtChild.frameNoMMIO
    decodedLoad := fun offset width inBounds =>
      dataPmaAllows_of_pma_regions_eq pmaEq (accessAtChild.decodedLoad offset width inBounds)
    decodedNoMMIO := accessAtChild.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq accessAtChild.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq accessAtChild.outputLengthStore
    writerRegionBeforeOutputContext := accessAtChild.writerRegionBeforeOutputContext
    frameNotCode := accessAtChild.frameNotCode }
  refine ⟨childUsed, after, {
    trace := by
      have all := parentTrace.append (by simpa [Nat.add_assoc] using childTrace)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all
    atPc := afterPc
    stack := stackAfter
    stdout := by simpa [childArgs, childState] using stdout
    stdin := by simpa [childState] using stdin
    cursor := by simpa [childState] using cursor
    exitCode := by simpa [childState] using exitCode
    saved := savedAbiAfter
    decoded := decodedAfter
    payload := payloadAfter
    loaded := loadedAfter
    access := accessAfter
    memory := fullMemory
    payloadContext := {
      fullCopy := ⟨fullCopyBytes, fullCopySize,
        by simpa [childArgs] using And.intro sourceAfter copiedSourceAfter⟩
      destinationRep := destinationAfter
      parentRootRep := parentRootAfter
      decodedBytesRep := decodedBytesAfter
      versionedHashesRelocation := versionedHashesAfter
      bytesSize := context.bytesSize
      stable := stableAfter
      payloadRep := payloadAfter
      slotWord := ⟨slotValue, slotAfter⟩
      slotTagWord := ⟨tagValue, tagAfter⟩
      localTailReps := ⟨tailValues, tailAfter⟩
      linkedTailReps := ⟨tailValues, tailAfter, tailSourceAfter⟩ } }⟩

set_option genInjectivity false in
/-- Exact raw-transactions descriptor setup followed by the shared byte-list encoder. -/
structure WriteSuccessRawTransactionsHandoff (fromStep childUsed : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (before after : EndpointState)
    (values : DecodeCalleeSavedValues) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (4 + childUsed) before after
  atPc : EndpointPc after = some 0x15678
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeMany encodeBytes
    args.decoded.payload.rawTransactions
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine
  payloadContext : WriteSuccessPayloadContext args payloadBytes after

private theorem writeSuccessRawTransactionsHandoff
    (child : WriteSuccessByteListsInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues)
    (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x15668)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessRawTransactionsHandoff fromStep childUsed args payloadBytes before after values := by
  rcases context.payloadRep with ⟨blockNumber, gasLimit, gasUsed, timestamp, extraData, baseFee,
    transactions, rawTransactions, withdrawals, blobGasUsed, excessBlobGas, slotNumber,
    blockAccessList, parentHashSize, parentHash, feeRecipientSize, feeRecipient, stateRootSize,
    stateRoot, receiptsRootSize, receiptsRoot, logsBloomSize, logsBloom, prevRandaoSize,
    prevRandao, blockHashSize, blockHash⟩
  rcases rawTransactions with ⟨rawAddress, rawAddressRep, rawCountRep, rawArrayRep⟩
  have seg0 : Seg writeSuccessParentPc writeSuccessByteListsCallExitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine 0x15668 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  obtain ⟨retired0, run0⟩ := writeSuccessRawTransactionsAddressLoadStep fromStep args
    before.machine rawAddress access atPc stack rawAddressRep aligned loaded
  obtain ⟨machine1, seg1⟩ := seg0.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x15668, 0x15680), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessByteListsCallExitPc; native_decide) x10
    (BitVec.ofNat 64 rawAddress) 0x1566c ⟨retired0, run0⟩ (by native_decide)
    (by intro r h; exact Or.inl h) (by simp [writeSuccessParentWrites])
    (by native_decide) (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully machine1.mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨retired1, run1⟩ := writeSuccessRawTransactionsCountLoadStep (fromStep + 1) args
    machine1 args.decoded.payload.rawTransactions.size access1 seg1.atPc
    (seg1.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    (rawCountRep.of_writesOnlyWithin seg1.mem (by
      intro index inBounds inside
      exact inside)) aligned loaded1
  obtain ⟨machine2, seg2⟩ := seg1.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x15668, 0x15680), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessByteListsCallExitPc; native_decide) x11
    (BitVec.ofNat 64 args.decoded.payload.rawTransactions.size) 0x15670
    ⟨retired1, by simpa [Nat.add_assoc] using run1⟩ (by native_decide)
    (by intro r h; exact Or.inl h) (by simp [writeSuccessParentWrites])
    (by native_decide) (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg access seg2
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully machine2.mem := by
    simpa [seg2.memEq (by simp)] using loaded
  obtain ⟨machine3, seg3⟩ := seg2.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x15668, 0x15680), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessByteListsCallExitPc; native_decide) x1 0x15670 0x15674
    (writeSuccessByteListsCallBaseStep (fromStep + 2) machine2 access2.configured
      seg2.atPc loaded2)
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access3 := writeSuccessAccessOfSeg access seg3
  have loaded3 : Artifacts.programImage.fileBytesLoadedFaithfully machine3.mem := by
    simpa [seg3.memEq (by simp)] using loaded
  obtain ⟨retired3, callRun⟩ := writeSuccessByteListsCallStep (fromStep + 3) machine3
    access3.configured seg3.atPc (seg3.reg x1 0x15670 (by simp)) loaded3
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement machine3) 0x15674 0x15c10 x1 0x15678)
    0x15c10 retired3
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes machine3 0x15674 0x15c10 retired3 x1 0x15678
  have callAtPc : callMachine.regs.get? PC = some 0x15c10 := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callMemEq : callMachine.mem = before.machine.mem := by
    have callBaseMemEq : callMachine.mem = machine3.mem := by
      change
        (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement machine3) 0x15674 0x15c10 x1 0x15678)
          0x15c10 retired3).mem = machine3.mem
      rw [tryStepControlFlowAfterRetired_mem]
      change
        (controlFlowJumpState (tryStepControlFlowAfterIncrement machine3) 0x15674 0x15c10).mem =
          machine3.mem
      rw [controlFlowJumpState_mem]
      rfl
    exact callBaseMemEq.trans (seg3.memEq (by simp))
  have callPrefix : ConfinedPrefix writeSuccessParentPc writeSuccessByteListsCallExitPc
      (fun _ _ _ _ _ => False) (fromStep + 3) 1 machine3 callMachine :=
    ConfinedPrefix.ownStep seg3.atPc
      (by unfold writeSuccessParentPc; exact
        ⟨(0x15668, 0x15680), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessByteListsCallExitPc; native_decide) callRun
  have callEnd : ScopedTrace writeSuccessParentPc writeSuccessByteListsCallExitPc
      (fun _ _ _ _ _ => False) (fromStep + 4) 0 callMachine callMachine :=
    .exitAt _ _ 0x15c10 callAtPc (by unfold writeSuccessByteListsCallExitPc; rfl)
  have parentMachineTrace := seg3.confined.trans callPrefix 0 callMachine callEnd
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 4 before callState := by
    simpa [callState] using liftWriteSuccessParentTrace before parentMachineTrace
  let childValue : ByteListsEncoderValue :=
    { address := rawAddress, values := args.decoded.payload.rawTransactions }
  let childArgs : EncoderCallArgs ByteListsEncoderValue :=
    { returnAddress := 0x15678
      callerStack := args.stackPointer - 0x7d0
      inputSize := args.inputSize
      value := childValue }
  have childEntry : EncoderCallEntry Elflings.writeSuccessByteListsEntry
      Elflings.writeSuccessByteListsExitPcs ByteListsEncoderBinding childArgs callState := by
    unfold EncoderCallEntry
    refine ⟨(by dsimp [childArgs]; native_decide), writeSuccessChildStackBound upper,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [callState] using callAtPc
    · simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, childArgs]
    · exact (callWrites.get x2 (by decide)).trans
        (seg3.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    · refine ⟨rawArrayRep.1, ?_, ?_, ?_⟩
      · exact (callWrites.get x10 (by decide)).trans
          (seg3.reg x10 (BitVec.ofNat 64 rawAddress) (by simp))
      · exact (callWrites.get x11 (by decide)).trans
          (seg3.reg x11 (BitVec.ofNat 64 args.decoded.payload.rawTransactions.size) (by simp))
      · simpa [callState, callMemEq] using rawArrayRep
    · simpa [callState, callMemEq] using loaded
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have accessCall : WriteSuccessMachineAccess args callMachine := {
    configured := configuredAfterWriteSuccessCall 0x15674 0x15c10 0x15678 retired3
      access3.configured
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.frameStore offset width bound)
    frameNoMMIO := access3.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.decodedLoad offset width bound)
    decodedNoMMIO := access3.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq callPmaEq access3.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq callPmaEq access3.outputLengthStore
    writerRegionBeforeOutputContext := access3.writerRegionBeforeOutputContext
    frameNotCode := access3.frameNotCode }
  have frameInWriter : ∀ address,
      byteRange (args.stackPointer - 0x7d0 - 64) 64 address →
      writeSuccessFrameMemory args address := by
    intro address inside
    exact writeSuccessChildFrame64_mem_frame lower inside
  obtain ⟨childUsed, after, handoff⟩ := writeSuccessEncoderChildHandoff child
    (fun inside => by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lo, hi⟩
      simp [Elflings.writeSuccessByteListsExecutionPcRanges] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩)
    fromStep 4 args childValue before callState childArgs rfl childEntry parentTrace
    ⟨rfl, rfl, rfl, rfl⟩ callMemEq accessCall (by simpa [callState, callMemEq] using loaded)
    lower frameInWriter
  have payloadAfter := writeSuccessPayloadContextAfterChild decodedEq lower upper
    access.writerRegionBeforeOutputContext context handoff.memory
    (fun address inside => Or.inl (frameInWriter address inside)) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      rw [decodedEq] at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      rw [decodedEq] at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro values word member index inBounds inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> unfold byteRange at inside <;> omega)
  have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact (saved word member).of_writesOnlyWithin handoff.memory (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  exact ⟨childUsed, after, {
    trace := handoff.trace
    atPc := handoff.atPc
    stack := handoff.stack
    stdout := handoff.stdout
    stdin := handoff.stdin
    cursor := handoff.cursor
    exitCode := handoff.exitCode
    saved := savedAfter
    payloadContext := payloadAfter
    loaded := handoff.loaded
    access := handoff.access
    memory := handoff.memory.mono frameInWriter }⟩

set_option genInjectivity false in
/-- Exact withdrawals descriptor loads followed by the selected inline encoder. -/
structure WriteSuccessWithdrawalsHandoff (fromStep childUsed : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (before after : EndpointState)
    (values : DecodeCalleeSavedValues) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (2 + childUsed) before after
  atPc : EndpointPc after = some 0x156e8
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeMany encodeWithdrawal
    args.decoded.payload.withdrawals
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine

private theorem writeSuccessWithdrawalsHandoff
    (child : WriteSuccessWithdrawalsInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues)
    (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x15678)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessWithdrawalsHandoff fromStep childUsed args payloadBytes before after values := by
  rcases context.payloadRep with ⟨blockNumber, gasLimit, gasUsed, timestamp, extraData, baseFee,
    transactions, rawTransactions, withdrawals, blobGasUsed, excessBlobGas, slotNumber,
    blockAccessList, parentHashSize, parentHash, feeRecipientSize, feeRecipient, stateRootSize,
    stateRoot, receiptsRootSize, receiptsRoot, logsBloomSize, logsBloom, prevRandaoSize,
    prevRandao, blockHashSize, blockHash⟩
  rcases withdrawals with ⟨withdrawalAddress, withdrawalAddressRep, withdrawalCountRep,
    withdrawalArrayRep⟩
  have seg0 : Seg writeSuccessParentPc (fun pc => pc = 0x15680)
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine 0x15678 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  obtain ⟨retired0, run0⟩ := writeSuccessWithdrawalsAddressLoadStep fromStep args
    before.machine withdrawalAddress access atPc stack withdrawalAddressRep aligned loaded
  obtain ⟨machine1, seg1⟩ := seg0.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x15668, 0x15680), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) x8 (BitVec.ofNat 64 withdrawalAddress) 0x1567c ⟨retired0, run0⟩
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully machine1.mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨retired1, run1⟩ := writeSuccessWithdrawalsCountLoadStep (fromStep + 1) args
    machine1 args.decoded.payload.withdrawals.size access1 seg1.atPc
    (seg1.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    (withdrawalCountRep.of_writesOnlyWithin seg1.mem (by
      intro index inBounds inside
      exact inside)) aligned loaded1
  obtain ⟨machine2, seg2⟩ := seg1.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x15668, 0x15680), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) x9 (BitVec.ofNat 64 args.decoded.payload.withdrawals.size) 0x15680
    ⟨retired1, by simpa [Nat.add_assoc] using run1⟩ (by native_decide)
    (by intro r h; exact Or.inl h) (by simp [writeSuccessParentWrites])
    (by native_decide) (by native_decide) (by simp [RegsOutside, stepBookkeeping])
  let childState : EndpointState := { before with machine := machine2 }
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 2 before childState := by
    have machineTrace := seg2.confined 0 machine2 (.exitAt _ _ 0x15680 seg2.atPc rfl)
    simpa [childState] using liftWriteSuccessParentTrace before machineTrace
  have decodedAtChild := context.stable.of_writesOnlyWithin
    (seg2.mem.mono (fun _ inside => inside.elim))
  have savedAtChild : InlineEncoderSavedWords machine2.mem
      (writeSuccessSavedWords args values) := by
    intro word member
    exact (saved word member).of_writesOnlyWithin seg2.mem (by
      intro index inBounds inside
      exact inside)
  obtain ⟨tailValues, tailBefore, tailSourceBefore⟩ := context.linkedTailReps
  have tailAtChild : InlineEncoderSavedWords machine2.mem
      (writeSuccessLocalTailWords args tailValues) := by
    simpa [childState, seg2.memEq (by simp)] using tailBefore
  have retainedAtChild : InlineEncoderSavedWords machine2.mem
      (writeSuccessSavedWords args values ++ writeSuccessLocalTailWords args tailValues) := by
    intro word member
    rw [List.mem_append] at member
    exact member.elim (savedAtChild word) (tailAtChild word)
  obtain ⟨fullCopyBytes, fullCopySize, fullDecodedRep, fullCopyRep⟩ := context.fullCopy
  let childArgs : InlineEncoderArgs (InlineArrayEncoderValue Withdrawal) :=
    { stackPointer := args.stackPointer - 0x7d0
      inputSize := args.inputSize
      value := ⟨withdrawalAddress, args.decoded.payload.withdrawals⟩
      savedWords := writeSuccessSavedWords args values ++ writeSuccessLocalTailWords args tailValues
      decodedAddress := args.decodedAddress
      copiedParentRootAddress := args.stackPointer - 0x7d0 + 0x3e8
      copiedVersionedHashesAddress := args.stackPointer - 0x7d0 + 0x388
      copiedPayloadAddress := args.stackPointer - 0x7d0 + 0x408
      copiedSourceAddress := args.stackPointer - 0x7d0 + 0x138
      copiedParentRootBytes := args.decoded.parentBeaconBlockRoot
      copiedPayloadBytes := payloadBytes
      copiedSourceBytes := fullCopyBytes
      decoded := args.decoded }
  have childEntry : InlineEncoderEntry Elflings.writeSuccessWithdrawalsEntry
      (InlineArrayEncoderBinding
        (fun state count => state.machine.regs.get? x9 = some (BitVec.ofNat 64 count))
        (fun state address => state.machine.regs.get? x8 = some (BitVec.ofNat 64 address))
        48 WithdrawalRep) childArgs childState := by
    change 0xb0 ≤ args.stackPointer - 0x7d0 ∧
      args.stackPointer - 0x7d0 + 0x740 ≤ 2 ^ 64 ∧ _
    refine ⟨by omega, by omega, ?_, ?_, ?_, retainedAtChild, decodedAtChild, rfl,
      (by
        change BytesRep childState.machine.mem
          (args.stackPointer - 0x7d0 + 0x3e8) args.decoded.parentBeaconBlockRoot
        rw [show childState.machine.mem = before.machine.mem by
          simpa [childState] using seg2.memEq (by simp)]
        exact context.parentRootRep),
      (by simpa [childState, childArgs, seg2.memEq (by simp)] using
        context.versionedHashesRelocation),
      (by
        change ExecutionPayloadRep childState.machine.mem
          (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
        rw [show childState.machine.mem = before.machine.mem by
          simpa [childState] using seg2.memEq (by simp)]
        exact context.payloadRep),
      (by
        change BytesRep childState.machine.mem
          (args.stackPointer - 0x7d0 + 0x408) payloadBytes
        rw [show childState.machine.mem = before.machine.mem by
          simpa [childState] using seg2.memEq (by simp)]
        exact context.destinationRep),
      (by exact ⟨by simpa [childState, seg2.memEq (by simp)] using fullDecodedRep,
        by simpa [childState, seg2.memEq (by simp)] using fullCopyRep,
        by simpa [childState, seg2.memEq (by simp)] using loaded⟩)⟩
    · simpa [childState, EndpointPc, MachinePc] using seg2.atPc
    · simpa [childState] using
        seg2.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
    · exact ⟨withdrawalArrayRep.1,
        by simpa [childState] using
          seg2.reg x9 (BitVec.ofNat 64 args.decoded.payload.withdrawals.size) (by simp),
        by simpa [childState] using
          seg2.reg x8 (BitVec.ofNat 64 withdrawalAddress) (by simp),
        by
          change ArrayRep 48 WithdrawalRep childState.machine.mem withdrawalAddress
            args.decoded.payload.withdrawals
          rw [show childState.machine.mem = before.machine.mem by
            simpa [childState] using seg2.memEq (by simp)]
          exact withdrawalArrayRep⟩
  obtain ⟨childUsed, after, _childBounded, childTrace, childExit⟩ :=
    writeSuccessInlineEncoderHandoff child
    (fun inside => by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lo, hi⟩
      simp [Elflings.writeSuccessWithdrawalsExecutionPcRanges] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · exact ⟨(0x101d4, 0x101f8), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · exact ⟨(0x14d30, 0x15a14), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩)
    (fromStep + 2) childArgs childState childEntry
  rcases childExit with ⟨afterPc, stdout, stdin, cursor, exitCode, stackAfter,
    bindingAfter, savedAfter, decodedAfter, parentRootAfter, versionedHashesAfter,
    payloadAfter, destinationAfter, sourceAfter, copiedSourceAfter,
    childMemory, childAgree, childRetired, loadedAfter⟩
  have childInWriter : ∀ address, inlineEncoderMemoryRegion childArgs.stackPointer address →
      writeSuccessFrameMemory args address := by
    intro address inside
    unfold inlineEncoderMemoryRegion at inside
    unfold writeSuccessFrameMemory
    unfold byteRange at inside ⊢
    dsimp [childArgs] at inside
    omega
  have parentMemory : WriteSuccessMemoryFrame args before.machine machine2 :=
    seg2.mem.mono (fun _ inside => inside.elim)
  have fullMemory : WriteSuccessMemoryFrame args before.machine after.machine :=
    WritesOnlyWithin.trans_same parentMemory (childMemory.mono childInWriter)
  have decodedBytesAfter := context.decodedBytesRep.of_writesOnlyWithin fullMemory (by
    intro index inBounds inside
    unfold writeSuccessFrameMemory byteRange at inside
    rw [decodedEq] at inside
    omega)
  have stableAfter := context.stable.afterWrites
    (fullMemory.mono (fun _ inside => Or.inl inside))
  obtain ⟨slotValue, slotRep⟩ := context.slotWord
  have slotFits : args.stackPointer - 0x7d0 + 0x480 + 8 ≤ 2 ^ 64 := by
    have fit := destinationAfter.1
    rw [context.bytesSize] at fit
    dsimp [childArgs] at fit
    omega
  have slotAfter := slotRep.rebase slotFits
    ((ByteWindowRelocation.of_same_bytes context.destinationRep destinationAfter).atOffset
      0x78 8 (by rw [context.bytesSize]; omega))
  obtain ⟨tagValue, tagRep⟩ := context.slotTagWord
  have tagFits : args.stackPointer - 0x7d0 + 0x488 + 8 ≤ 2 ^ 64 := by
    have fit := destinationAfter.1
    rw [context.bytesSize] at fit
    dsimp [childArgs] at fit
    omega
  have tagAfter := tagRep.rebase tagFits
    ((ByteWindowRelocation.of_same_bytes context.destinationRep destinationAfter).atOffset
      0x80 8 (by rw [context.bytesSize]; omega))
  have accessAtChild := writeSuccessAccessOfSeg access seg2
  have savedAbiAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact savedAfter word (List.mem_append_left _ member)
  have tailAfter : InlineEncoderSavedWords after.machine.mem
      (writeSuccessLocalTailWords args tailValues) := by
    intro word member
    exact savedAfter word (List.mem_append_right _ member)
  have tailSourceAfter : ∀ index (bound : index < 16),
      UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
        (tailValues ⟨index, bound⟩) := by
    intro index bound
    exact (tailSourceBefore index bound).of_writesOnlyWithin fullMemory (by
      intro byte byteBound inside
      unfold writeSuccessFrameMemory byteRange at inside
      rw [decodedEq] at inside
      omega)
  have pmaEq := childAgree pma_regions (by simp [inlineEncoderPreserved])
  have accessAfter : WriteSuccessMachineAccess args after.machine := {
    configured := accessAtChild.configured.mono
      (childAgree.weaken instructionPreserved_inlineEncoderPreserved) childRetired
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (accessAtChild.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (accessAtChild.frameStore offset width bound)
    frameNoMMIO := accessAtChild.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (accessAtChild.decodedLoad offset width bound)
    decodedNoMMIO := accessAtChild.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq accessAtChild.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq accessAtChild.outputLengthStore
    writerRegionBeforeOutputContext := accessAtChild.writerRegionBeforeOutputContext
    frameNotCode := accessAtChild.frameNotCode }
  exact ⟨childUsed, after, {
    trace := by
      have all := parentTrace.append (by simpa [Nat.add_assoc] using childTrace)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all
    atPc := afterPc
    stack := stackAfter
    stdout := by simpa [childArgs, childState] using stdout
    stdin := by simpa [childState] using stdin
    cursor := by simpa [childState] using cursor
    exitCode := by simpa [childState] using exitCode
    saved := savedAbiAfter
    payloadContext := {
      fullCopy := ⟨fullCopyBytes, fullCopySize,
        by simpa [childArgs] using And.intro sourceAfter copiedSourceAfter⟩
      destinationRep := destinationAfter
      parentRootRep := parentRootAfter
      decodedBytesRep := decodedBytesAfter
      versionedHashesRelocation := versionedHashesAfter
      bytesSize := context.bytesSize
      stable := stableAfter
      payloadRep := payloadAfter
      slotWord := ⟨slotValue, slotAfter⟩
      slotTagWord := ⟨tagValue, tagAfter⟩
      localTailReps := ⟨tailValues, tailAfter⟩
      linkedTailReps := ⟨tailValues, tailAfter, tailSourceAfter⟩ }
    loaded := loadedAfter
    access := accessAfter
    memory := fullMemory }⟩

set_option genInjectivity false in
/-- The transaction, raw-transaction, and withdrawal encoders in production order. -/
structure WriteSuccessArrayPrefixHandoff (fromStep transactionsUsed rawUsed withdrawalsUsed : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (before after : EndpointState)
    (values : DecodeCalleeSavedValues) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep
    (4 + transactionsUsed + 4 + rawUsed + 2 + withdrawalsUsed) before after
  atPc : EndpointPc after = some 0x156e8
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++
    encodeMany encodeTransaction args.decoded.payload.transactions ++
    encodeMany encodeBytes args.decoded.payload.rawTransactions ++
    encodeMany encodeWithdrawal args.decoded.payload.withdrawals
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine

private theorem writeSuccessArrayPrefixHandoff
    (transactionsChild : WriteSuccessTransactionsInstanceContract)
    (rawChild : WriteSuccessByteListsInstanceContract)
    (withdrawalsChild : WriteSuccessWithdrawalsInstanceContract)
    (fromStep : Nat) (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x14ee4)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ transactionsUsed rawUsed withdrawalsUsed after,
      WriteSuccessArrayPrefixHandoff fromStep transactionsUsed rawUsed withdrawalsUsed
        args payloadBytes before after values := by
  obtain ⟨transactionsUsed, afterTransactions, transactions⟩ :=
    writeSuccessTransactionsHandoff transactionsChild fromStep args payloadBytes values before
      atPc stack context saved access loaded aligned lower upper decodedEq
  let rawStart := fromStep + 4 + transactionsUsed
  obtain ⟨rawUsed, afterRaw, raw⟩ :=
    writeSuccessRawTransactionsHandoff rawChild rawStart args payloadBytes values
      afterTransactions transactions.atPc transactions.stack transactions.payloadContext
      transactions.saved transactions.access transactions.loaded aligned lower upper decodedEq
  let withdrawalsStart := rawStart + 4 + rawUsed
  obtain ⟨withdrawalsUsed, after, withdrawals⟩ :=
    writeSuccessWithdrawalsHandoff withdrawalsChild withdrawalsStart args payloadBytes values
      afterRaw raw.atPc raw.stack raw.payloadContext raw.saved raw.access raw.loaded aligned lower
      upper decodedEq
  refine ⟨transactionsUsed, rawUsed, withdrawalsUsed, after, {
    trace := ?_
    atPc := withdrawals.atPc
    stack := withdrawals.stack
    stdout := ?_
    stdin := withdrawals.stdin.trans (raw.stdin.trans transactions.stdin)
    cursor := withdrawals.cursor.trans (raw.cursor.trans transactions.cursor)
    exitCode := withdrawals.exitCode.trans (raw.exitCode.trans transactions.exitCode)
    saved := withdrawals.saved
    payloadContext := withdrawals.payloadContext
    loaded := withdrawals.loaded
    access := withdrawals.access
    memory := WritesOnlyWithin.trans_same
      (WritesOnlyWithin.trans_same transactions.memory raw.memory) withdrawals.memory }⟩
  · have firstTwo := transactions.trace.append (by
      simpa [rawStart, Nat.add_assoc] using raw.trace)
    have firstTwo' : ConfinedTrace EndpointStep EndpointPc
        (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep
        (4 + transactionsUsed + 4 + rawUsed) before afterRaw := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using firstTwo
    have last : ConfinedTrace EndpointStep EndpointPc
        (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        (fromStep + (4 + transactionsUsed + 4 + rawUsed)) (2 + withdrawalsUsed)
        afterRaw after := by
      simpa only [rawStart, withdrawalsStart, Nat.add_assoc] using withdrawals.trace
    simpa [Nat.add_assoc] using firstTwo'.append last
  · rw [withdrawals.stdout, raw.stdout, transactions.stdout]

/-- Production `0x156e8: ld a0,0x470(sp)`. -/
private theorem writeSuccessBlobGasUsedLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x156e8)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x470)
      args.decoded.payload.blobGasUsed)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x156e8 retired x10
        (BitVec.ofNat 64 args.decoded.payload.blobGasUsed)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x156e8 0x470 args.decoded.payload.blobGasUsed
    args state (.Regidx 10#5) x10 (BitVec.ofNat 64 args.decoded.payload.blobGasUsed)
    0x470 0x03 0x35 0x01 0x47 access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x470#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x156ec: auipc ra,0`. -/
private theorem writeSuccessBlobGasUsedCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x156ec)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x156ec retired x1 0x156ec) false := by
  apply configuredAuipcStep stepNo state 0x156ec 0 0x97 0x00 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x156f0: jalr ra,0x624(ra)`. -/
private theorem writeSuccessBlobGasUsedCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x156f0)
    (baseRead : state.regs.get? x1 = some 0x156ec)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x156f0 0x15d10 x1 0x156f4)
        0x15d10 retired) false := by
  apply configuredJalrCallStep stepNo state 0x156f0 0x156ec 0x624 0x15d10 0x156f4
    0xe7 0x80 0x40 0x62 configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x156f4: ld a0,0x478(sp)`. -/
private theorem writeSuccessExcessBlobGasLoadStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x156f4)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x478)
      args.decoded.payload.excessBlobGas)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x156f4 retired x10
        (BitVec.ofNat 64 args.decoded.payload.excessBlobGas)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x156f4 0x478 args.decoded.payload.excessBlobGas
    args state (.Regidx 10#5) x10 (BitVec.ofNat 64 args.decoded.payload.excessBlobGas)
    0x478 0x03 0x35 0x81 0x47 access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x478#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x156f8: auipc ra,0`. -/
private theorem writeSuccessExcessBlobGasCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x156f8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x156f8 retired x1 0x156f8) false := by
  apply configuredAuipcStep stepNo state 0x156f8 0 0x97 0x00 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x156fc: jalr ra,0x618(ra)`. -/
private theorem writeSuccessExcessBlobGasCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x156fc)
    (baseRead : state.regs.get? x1 = some 0x156f8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x156fc 0x15d10 x1 0x15700)
        0x15d10 retired) false := by
  apply configuredJalrCallStep stepNo state 0x156fc 0x156f8 0x618 0x15d10 0x15700
    0xe7 0x80 0x80 0x61 configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x15700: ld a0,0x480(sp)`. -/
private theorem writeSuccessSlotWordLoadStep (stepNo value : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x15700)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x480) value)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15700 retired x10 (BitVec.ofNat 64 value)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x15700 0x480 value args state
    (.Regidx 10#5) x10 (BitVec.ofNat 64 value) 0x480 0x03 0x35 0x01 0x48
    access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x480#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x15704: ld a1,0x488(sp)`. -/
private theorem writeSuccessSlotTagLoadStep (stepNo tag : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x15704)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x488) tag)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15704 retired x11 (BitVec.ofNat 64 tag)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x15704 0x488 tag args state
    (.Regidx 11#5) x11 (BitVec.ofNat 64 tag) 0x488 0x83 0x35 0x81 0x48
    access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x488#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x11_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x15708: sd a0,0x658(sp)`. -/
private theorem writeSuccessSlotWordStoreStep (stepNo value : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x15708)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (data : state.regs.get? x10 = some (BitVec.ofNat 64 value))
    (aligned : args.stackPointer % 16 = 0) (upper : args.stackPointer < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x15708)
          (args.stackPointer - 0x7d0 + 0x658) (BitVec.ofNat 64 value))
        0x15708 retired) false := by
  apply writeSuccessFrameDwordStoreStep stepNo 0x15708 0x658 value args state 0x658
    0x23 0x3c 0xa1 0x64 access atPc stack data (by omega) (by omega) loaded upper
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x658#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessStoreDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x1570c: sd a1,0x660(sp)`. -/
private theorem writeSuccessSlotTagStoreStep (stepNo tag : Nat) (args : WriteSuccessArgs)
    (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x1570c)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (data : state.regs.get? x11 = some (BitVec.ofNat 64 tag))
    (aligned : args.stackPointer % 16 = 0) (upper : args.stackPointer < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x1570c)
          (args.stackPointer - 0x7d0 + 0x660) (BitVec.ofNat 64 tag))
        0x1570c retired) false := by
  apply writeSuccessFrameDwordStoreRegStep stepNo 0x1570c 0x660 tag args state
    (.Regidx 11#5) 0x660 0x23 0x30 0xb1 0x66 access atPc stack (by omega) (by omega)
    loaded upper
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x660#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessStoreDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro premise writes
    exact rX_x11_run premise _ ((writes.get x11 (by decide)).trans data)

/-- Production `0x15710: addi a0,sp,0x658`. -/
private theorem writeSuccessSlotSourceStep (stepNo : Nat) (args : WriteSuccessArgs)
    (state : State) (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15710)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15710 retired x10
        (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x658))) false := by
  apply writeSuccessPayloadFieldSourceStep stepNo 0x15710 0x658 0x658
    0x13 0x05 0x81 0x65 state (args.stackPointer - 0x7d0) configured atPc stack loaded
  · simp only [iTypeResult]
    change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x658#64 = _
    rw [← BitVec.ofNat_add]
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  all_goals native_decide

/-- Production `0x15714: auipc ra,0`. -/
private theorem writeSuccessOptionalCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15714)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15714 retired x1 0x15714) false := by
  apply configuredAuipcStep stepNo state 0x15714 0 0x97 0x00 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x15718: jalr ra,0x4b4(ra)`, entering optional-u64. -/
private theorem writeSuccessOptionalCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15718)
    (baseRead : state.regs.get? x1 = some 0x15714)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x15718 0x15bc8 x1 0x1571c)
        0x15bc8 retired) false := by
  apply configuredJalrCallStep stepNo state 0x15718 0x15714 0x4b4 0x15bc8 0x1571c
    0xe7 0x80 0x40 0x4b configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x1571c: ld a0,0x490(sp)`. -/
private theorem writeSuccessBlockAccessPointerLoadStep (stepNo address : Nat)
    (args : WriteSuccessArgs) (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x1571c)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (rep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x490) address)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1571c retired x10 (BitVec.ofNat 64 address)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x1571c 0x490 address args state
    (.Regidx 10#5) x10 (BitVec.ofNat 64 address) 0x490 0x03 0x35 0x01 0x49
    access atPc stack rep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x490#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x10_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x15720: ld a1,0x498(sp)`. -/
private theorem writeSuccessBlockAccessLengthLoadStep (stepNo address length : Nat)
    (args : WriteSuccessArgs) (state : State) (access : WriteSuccessMachineAccess args state)
    (atPc : state.regs.get? PC = some 0x15720)
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (lengthRep : UIntRep 8 state.mem (args.stackPointer - 0x7d0 + 0x498) length)
    (aligned : args.stackPointer % 16 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15720 retired x11 (BitVec.ofNat 64 length)) false := by
  apply writeSuccessFrameDwordLoadStep stepNo 0x15720 0x498 length args state
    (.Regidx 11#5) x11 (BitVec.ofNat 64 length) 0x498 0x83 0x35 0x81 0x49
    access atPc stack lengthRep (by omega) (by omega) loaded
  · change BitVec.ofNat 64 (args.stackPointer - 0x7d0) + 0x498#64 = _
    rw [← BitVec.ofNat_add]
  · exact fun premise => wX_x11_run premise _
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads access.configured
    decode_run
  · native_decide
  · rfl
  all_goals native_decide

/-- Production `0x15724: auipc ra,0`. -/
private theorem writeSuccessBlockAccessCallBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15724)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x15724 retired x1 0x15724) false := by
  apply configuredAuipcStep stepNo state 0x15724 0 0x97 0x00 0x00 0x00 configured atPc loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run

/-- Production `0x15728: jalr ra,0x548(ra)`, entering the shared bytes encoder. -/
private theorem writeSuccessBlockAccessCallStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x15728)
    (baseRead : state.regs.get? x1 = some 0x15724)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) 0x15728 0x15c6c x1 0x1572c)
        0x15c6c retired) false := by
  apply configuredJalrCallStep stepNo state 0x15728 0x15724 0x548 0x15c6c 0x1572c
    0xe7 0x80 0x80 0x54 configured atPc baseRead loaded
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl
  · obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      writeSuccessLoadDecodeReads configured
    decode_run
  · native_decide
  · native_decide
  · native_decide

set_option genInjectivity false in
/-- The four parent loads/stores that materialize the optional slot descriptor. -/
structure WriteSuccessSlotSetupHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (before after : EndpointState)
    (values : DecodeCalleeSavedValues) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 4 before after
  atPc : EndpointPc after = some 0x15710
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  stdout : after.stdout = before.stdout
  exitCode : after.exitCode = before.exitCode
  localRep : OptionalUIntRep 8 after.machine.mem
    (args.stackPointer - 0x7d0 + 0x658) args.decoded.payload.slotNumber
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WritesOnlyWithin (writeSuccessSlotSetupMemory args) before.machine after.machine

private theorem writeSuccessSlotSetupHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x15700)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ after, WriteSuccessSlotSetupHandoff fromStep args payloadBytes before after values := by
  obtain ⟨rawValue, rawRep⟩ := context.slotWord
  obtain ⟨tagWord, tagWordRep⟩ := context.slotTagWord
  rcases context.payloadRep with ⟨blockNumber, gasLimit, gasUsed, timestamp, extraData, baseFee,
    transactions, rawTransactions, withdrawals, blobGasUsed, excessBlobGas, slotNumber,
    blockAccessList, parentHashSize, parentHash, feeRecipientSize, feeRecipient, stateRootSize,
    stateRoot, receiptsRootSize, receiptsRoot, logsBloomSize, logsBloom, prevRandaoSize,
    prevRandao, blockHashSize, blockHash⟩
  have tagByteRep : UIntRep 1 before.machine.mem
      (args.stackPointer - 0x7d0 + 0x488)
      (if args.decoded.payload.slotNumber.isSome then 1 else 0) := by
    cases optionEq : args.decoded.payload.slotNumber with
    | none =>
      rw [optionEq] at slotNumber
      simpa [OptionalUIntRep, Nat.add_assoc] using slotNumber
    | some value =>
      rw [optionEq] at slotNumber
      simpa [OptionalUIntRep, Nat.add_assoc] using slotNumber.2
  have rawActive : ∀ value, args.decoded.payload.slotNumber = some value → rawValue = value := by
    intro value optionEq
    rw [optionEq] at slotNumber
    exact UIntRep.eight_unique rawRep slotNumber.1
  let setupMemory := writeSuccessSlotSetupMemory args
  have setupInWriter : ∀ address, setupMemory address → writeSuccessFrameMemory args address := by
    intro address inside
    unfold setupMemory writeSuccessSlotSetupMemory at inside
    unfold writeSuccessFrameMemory
    unfold byteRange at inside ⊢
    rcases inside with inside | inside <;> omega
  have codeOfSeg {kv n cur pc}
      (seg : Seg writeSuccessParentPc (fun pc => pc = 0x15710)
        (fun _ _ _ _ _ => False) writeSuccessParentWrites setupMemory kv fromStep n
        before.machine cur pc) :
      Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
    intro address byte fileByte
    have unchanged := seg.mem address (by
      intro inside
      have inWriter := setupInWriter address inside
      unfold writeSuccessFrameMemory byteRange at inWriter
      have none := access.frameNotCode address inWriter.1 (by omega)
      rw [fileByte] at none
      cases none)
    exact unchanged.trans (loaded address byte fileByte)
  have seg0 : Seg writeSuccessParentPc (fun pc => pc = 0x15710)
      (fun _ _ _ _ _ => False) writeSuccessParentWrites setupMemory
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine 0x15700 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  obtain ⟨retired0, run0⟩ := writeSuccessSlotWordLoadStep fromStep rawValue args
    before.machine access atPc stack rawRep aligned loaded
  obtain ⟨machine1, seg1⟩ := seg0.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) x10 (BitVec.ofNat 64 rawValue) 0x15704 ⟨retired0, run0⟩
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have tagWordRep1 := tagWordRep.of_writesOnlyWithin seg1.mem (by
    intro index inBounds inside
    unfold setupMemory writeSuccessSlotSetupMemory byteRange at inside
    rcases inside with inside | inside <;> omega)
  obtain ⟨retired1, run1⟩ := writeSuccessSlotTagLoadStep (fromStep + 1) tagWord args
    machine1 access1 seg1.atPc
    (seg1.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    tagWordRep1 aligned (codeOfSeg seg1)
  obtain ⟨machine2, seg2⟩ := seg1.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) x11 (BitVec.ofNat 64 tagWord) 0x15708 ⟨retired1, by simpa using run1⟩
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg access seg2
  obtain ⟨retired2, run2⟩ := writeSuccessSlotWordStoreStep (fromStep + 2) rawValue args
    machine2 access2 seg2.atPc
    (seg2.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    (seg2.reg x10 (BitVec.ofNat 64 rawValue) (by simp)) aligned upper (codeOfSeg seg2)
  obtain ⟨retired2', machine3, machine3Eq, seg3⟩ := seg2.stepStoreWitness
    (width := 8) (args.stackPointer - 0x7d0 + 0x658) (BitVec.ofNat 64 rawValue) 0x1570c
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) ⟨retired2, run2⟩ (by native_decide)
    (by intro address lo hi; exact Or.inl ⟨lo, hi⟩)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have access3 := writeSuccessAccessOfSeg access seg3
  obtain ⟨retired3, run3⟩ := writeSuccessSlotTagStoreStep (fromStep + 3) tagWord args
    machine3 access3 seg3.atPc
    (seg3.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    (seg3.reg x11 (BitVec.ofNat 64 tagWord) (by simp)) aligned upper (codeOfSeg seg3)
  obtain ⟨retired3', machine4, machine4Eq, seg4⟩ := seg3.stepStoreWitness
    (width := 8) (args.stackPointer - 0x7d0 + 0x660) (BitVec.ofNat 64 tagWord) 0x15710
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) ⟨retired3, run3⟩ (by native_decide)
    (by intro address lo hi; exact Or.inr ⟨lo, hi⟩)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    (by simp [RegsOutside, stepBookkeeping])
  have wordAt3 : UIntRep 8 machine3.mem
      (args.stackPointer - 0x7d0 + 0x658) rawValue := by
    rw [machine3Eq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement machine2) 0x15708)
        (args.stackPointer - 0x7d0 + 0x658) rawValue rawRep.1 (by omega)
  have secondWrites : WritesOnlyWithin
      (byteRange (args.stackPointer - 0x7d0 + 0x660) 8) machine3 machine4 := by
    intro address outside
    rw [machine4Eq]
    exact storeRetirement_mem_writes machine3 0x1570c 0x15710 retired3'
      (args.stackPointer - 0x7d0 + 0x660) (BitVec.ofNat 64 tagWord) address outside
  have wordAt4 := wordAt3.of_writesOnlyWithin secondWrites (by
    intro index bound inside
    unfold byteRange at inside
    omega)
  have tagWordAt4 : UIntRep 8 machine4.mem
      (args.stackPointer - 0x7d0 + 0x660) tagWord := by
    rw [machine4Eq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement machine3) 0x1570c)
        (args.stackPointer - 0x7d0 + 0x660) tagWord tagWordRep.1 (by omega)
  have tagByteAt4 : UIntRep 1 machine4.mem
      (args.stackPointer - 0x7d0 + 0x660)
      (if args.decoded.payload.slotNumber.isSome then 1 else 0) := by
    apply tagByteRep.rebase (by omega)
    intro index inBounds
    rw [tagWordAt4.2.2 index (by omega), tagWordRep.2.2 index (by omega)]
  have localRep : OptionalUIntRep 8 machine4.mem
      (args.stackPointer - 0x7d0 + 0x658) args.decoded.payload.slotNumber := by
    cases optionEq : args.decoded.payload.slotNumber with
    | none => simpa [OptionalUIntRep, optionEq] using tagByteAt4
    | some value =>
      have valueEq := rawActive value optionEq
      subst rawValue
      exact ⟨wordAt4, by simpa [optionEq] using tagByteAt4⟩
  let after : EndpointState := { before with machine := machine4 }
  have setupWrites : WritesOnlyWithin setupMemory before.machine after.machine := by
    simpa [after] using seg4.mem
  have parentRootSize : args.decoded.parentBeaconBlockRoot.size = 32 :=
    (context.stable before.machine.mem (fun _ _ => rfl)).2.2.2.2.1
  have payloadAfter := writeSuccessPayloadContextAfterChild decodedEq lower upper
    access.writerRegionBeforeOutputContext context setupWrites
    (fun address inside => Or.inl (setupInWriter address inside)) (by
      intro index inBounds inside
      unfold setupMemory writeSuccessSlotSetupMemory byteRange at inside
      rcases inside with inside | inside <;> omega)
    (by
      intro index inBounds inside
      rw [context.bytesSize] at inBounds
      unfold setupMemory writeSuccessSlotSetupMemory byteRange at inside
      rcases inside with inside | inside <;> omega)
    (by
      intro index inBounds inside
      unfold setupMemory writeSuccessSlotSetupMemory byteRange at inside
      rw [parentRootSize] at inBounds
      rcases inside with inside | inside <;> omega)
    (by
      intro index inBounds inside
      unfold setupMemory writeSuccessSlotSetupMemory byteRange at inside
      rw [decodedEq] at inside
      rcases inside with inside | inside <;> omega)
    (by
      intro index inBounds inside
      unfold setupMemory writeSuccessSlotSetupMemory byteRange at inside
      rw [decodedEq] at inside
      rcases inside with inside | inside <;> omega)
    (by
      intro index inBounds inside
      unfold setupMemory writeSuccessSlotSetupMemory byteRange at inside
      rcases inside with inside | inside <;> omega) (by
      intro values word member index inBounds inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        unfold setupMemory writeSuccessSlotSetupMemory byteRange at inside <;>
        rcases inside with inside | inside <;> omega)
  refine ⟨after, {
    trace := by
      have machineTrace := seg4.confined 0 machine4 (.exitAt _ _ 0x15710 seg4.atPc rfl)
      simpa [after] using liftWriteSuccessParentTrace before machineTrace
    atPc := by simpa [after] using seg4.atPc
    stack := by
      simpa [after] using
        seg4.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp)
    stdin := rfl
    cursor := rfl
    stdout := rfl
    exitCode := rfl
    localRep := by simpa [after] using localRep
    saved := by
      intro word member
      simpa [after] using (saved word member).of_writesOnlyWithin seg4.mem (by
        intro index inBounds inside
        unfold setupMemory writeSuccessSlotSetupMemory byteRange at inside
        simp [writeSuccessSavedWords] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> rcases inside with inside | inside <;> omega)
    payloadContext := by simpa [after] using payloadAfter
    loaded := by simpa [after] using codeOfSeg seg4
    access := by simpa [after] using writeSuccessAccessOfSeg access seg4
    memory := by simpa [after] using seg4.mem }⟩

set_option genInjectivity false in
/-- The optional slot descriptor and selected optional-u64 encoder through `0x1571c`. -/
structure WriteSuccessOptionalHandoff (fromStep childUsed : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (before after : EndpointState)
    (values : DecodeCalleeSavedValues) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (7 + childUsed) before after
  atPc : EndpointPc after = some 0x1571c
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++
    encodeOptional (encodeNatLE 8) args.decoded.payload.slotNumber
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine

private theorem writeSuccessOptionalHandoff
    (child : WriteSuccessOptionalU64InstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues)
    (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x15700)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessOptionalHandoff fromStep childUsed args payloadBytes before after values := by
  obtain ⟨setupState, setup⟩ := writeSuccessSlotSetupHandoff fromStep args payloadBytes values before
    atPc stack context saved access loaded aligned lower upper decodedEq
  let parentStart := fromStep + 4
  have seg0 : Seg writeSuccessParentPc writeSuccessOptionalCallExitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      parentStart 0 setupState.machine setupState.machine 0x15710 := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := setup.access.configured.retiredCounter
    atPc := setup.atPc
    regs := by intro pair member; simp at member; subst pair; exact setup.stack }
  obtain ⟨machine1, seg1⟩ := seg0.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessOptionalCallExitPc; native_decide) x10
    (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x658)) 0x15714
    (writeSuccessSlotSourceStep parentStart args setupState.machine setup.access.configured
      setup.atPc setup.stack setup.loaded)
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg setup.access seg1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully machine1.mem := by
    simpa [seg1.memEq (by simp)] using setup.loaded
  obtain ⟨machine2, seg2⟩ := seg1.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessOptionalCallExitPc; native_decide) x1 0x15714 0x15718
    (writeSuccessOptionalCallBaseStep (parentStart + 1) machine1 access1.configured
      seg1.atPc loaded1)
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg setup.access seg2
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully machine2.mem := by
    simpa [seg2.memEq (by simp)] using setup.loaded
  obtain ⟨retired2, callRun⟩ := writeSuccessOptionalCallStep (parentStart + 2) machine2
    access2.configured seg2.atPc (seg2.reg x1 0x15714 (by simp)) loaded2
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement machine2) 0x15718 0x15bc8 x1 0x1571c)
    0x15bc8 retired2
  let callState : EndpointState := { setupState with machine := callMachine }
  have callWrites := callRetirement_writes machine2 0x15718 0x15bc8 retired2 x1 0x1571c
  have callAtPc : callMachine.regs.get? PC = some 0x15bc8 := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callMemEq : callMachine.mem = setupState.machine.mem := by
    have callMachineMem : callMachine.mem = machine2.mem := by
      change
        (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement machine2) 0x15718 0x15bc8 x1 0x1571c)
          0x15bc8 retired2).mem = machine2.mem
      rw [tryStepControlFlowAfterRetired_mem]
      change (controlFlowJumpState (tryStepControlFlowAfterIncrement machine2)
        0x15718 0x15bc8).mem = machine2.mem
      rw [controlFlowJumpState_mem]
      rfl
    exact callMachineMem.trans (seg2.memEq (by simp))
  have callPrefix : ConfinedPrefix writeSuccessParentPc writeSuccessOptionalCallExitPc
      (fun _ _ _ _ _ => False) (parentStart + 2) 1 machine2 callMachine :=
    ConfinedPrefix.ownStep seg2.atPc
      (by unfold writeSuccessParentPc; exact
        ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessOptionalCallExitPc; native_decide) callRun
  have callEnd : ScopedTrace writeSuccessParentPc writeSuccessOptionalCallExitPc
      (fun _ _ _ _ _ => False) (parentStart + 3) 0 callMachine callMachine :=
    .exitAt _ _ 0x15bc8 callAtPc (by unfold writeSuccessOptionalCallExitPc; rfl)
  have parentMachineTrace := seg2.confined.trans callPrefix 0 callMachine callEnd
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) parentStart 3 setupState callState := by
    simpa [callState] using liftWriteSuccessParentTrace setupState parentMachineTrace
  let childValue : OptionalUInt64EncoderValue :=
    { address := args.stackPointer - 0x7d0 + 0x658
      value := args.decoded.payload.slotNumber }
  let childArgs : EncoderCallArgs OptionalUInt64EncoderValue :=
    { returnAddress := 0x1571c
      callerStack := args.stackPointer - 0x7d0
      inputSize := args.inputSize
      value := childValue }
  have childEntry : EncoderCallEntry Elflings.writeSuccessOptionalU64Entry
      Elflings.writeSuccessOptionalU64ExitPcs OptionalUInt64EncoderBinding childArgs callState := by
    unfold EncoderCallEntry
    refine ⟨(by dsimp [childArgs]; native_decide), writeSuccessChildStackBound upper,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [callState] using callAtPc
    · simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, childArgs]
    · exact (callWrites.get x2 (by decide)).trans
        (seg2.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    · refine ⟨?_, ?_, ?_⟩
      · dsimp [childValue]
        cases optionEq : args.decoded.payload.slotNumber with
        | none =>
          have tagRep : UIntRep 1 callState.machine.mem
              (args.stackPointer - 0x7d0 + 0x658 + 8) 0 := by
            simpa [callState, callMemEq, OptionalUIntRep, optionEq] using setup.localRep
          exact tagRep.2.1
        | some value =>
          have localValueRep := setup.localRep
          rw [optionEq] at localValueRep
          have tagRep : UIntRep 1 callState.machine.mem
              (args.stackPointer - 0x7d0 + 0x658 + 8) 1 := by
            simpa [callState, callMemEq] using localValueRep.2
          exact tagRep.2.1
      · exact (callWrites.get x10 (by decide)).trans
          (seg2.reg x10 (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x658)) (by simp))
      · simpa [callState, callMemEq, childValue] using setup.localRep
    · simpa [callState, callMemEq] using setup.loaded
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have accessCall : WriteSuccessMachineAccess args callMachine := {
    configured := configuredAfterWriteSuccessCall 0x15718 0x15bc8 0x1571c retired2
      access2.configured
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access2.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access2.frameStore offset width bound)
    frameNoMMIO := access2.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access2.decodedLoad offset width bound)
    decodedNoMMIO := access2.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq callPmaEq access2.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq callPmaEq access2.outputLengthStore
    writerRegionBeforeOutputContext := access2.writerRegionBeforeOutputContext
    frameNotCode := access2.frameNotCode }
  have frameInWriter : ∀ address,
      byteRange (args.stackPointer - 0x7d0 - 16) 16 address →
      writeSuccessFrameMemory args address := by
    intro address inside
    exact writeSuccessChildFrame_mem_frame lower inside
  obtain ⟨childUsed, after, handoff⟩ := writeSuccessEncoderChildHandoff child
    (fun inside => by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lo, hi⟩
      simp [Elflings.writeSuccessOptionalU64ExecutionPcRanges] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩)
    parentStart 3 args childValue setupState callState childArgs rfl childEntry parentTrace
    ⟨rfl, rfl, rfl, rfl⟩ callMemEq accessCall (by simpa [callState, callMemEq] using setup.loaded)
    lower frameInWriter
  have payloadAfter := writeSuccessPayloadContextAfterChild decodedEq lower upper
    access.writerRegionBeforeOutputContext setup.payloadContext handoff.memory
    (fun address inside => Or.inl (frameInWriter address inside)) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      rw [decodedEq] at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      rw [decodedEq] at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro values word member index inBounds inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> unfold byteRange at inside <;> omega)
  have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact (setup.saved word member).of_writesOnlyWithin handoff.memory (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  refine ⟨childUsed, after, {
    trace := ?_
    atPc := handoff.atPc
    stack := handoff.stack
    stdout := by rw [handoff.stdout, setup.stdout]
    stdin := handoff.stdin.trans setup.stdin
    cursor := handoff.cursor.trans setup.cursor
    exitCode := handoff.exitCode.trans setup.exitCode
    saved := savedAfter
    payloadContext := payloadAfter
    loaded := handoff.loaded
    access := handoff.access
    memory := WritesOnlyWithin.trans_same
      (setup.memory.mono (fun address inside => by
        unfold writeSuccessSlotSetupMemory at inside
        unfold writeSuccessFrameMemory
        unfold byteRange at inside ⊢
        rcases inside with inside | inside <;> omega))
      (handoff.memory.mono frameInWriter) }⟩
  have all := setup.trace.append (by
    simpa [parentStart, Nat.add_assoc] using handoff.trace)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

set_option genInjectivity false in
/-- The block-access-list descriptor and selected bytes encoder through `0x1572c`. -/
structure WriteSuccessBlockAccessHandoff (fromStep childUsed : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (before after : EndpointState)
    (values : DecodeCalleeSavedValues) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (4 + childUsed) before after
  atPc : EndpointPc after = some 0x1572c
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeBytes args.decoded.payload.blockAccessList
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WritesOnlyWithin
    (byteRange (args.stackPointer - 0x7d0 - 48) 48) before.machine after.machine

private theorem writeSuccessBlockAccessHandoff
    (child : WriteSuccessBytesInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues)
    (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x1571c)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessBlockAccessHandoff fromStep childUsed args payloadBytes before after values := by
  rcases context.payloadRep with ⟨blockNumber, gasLimit, gasUsed, timestamp, extraData, baseFee,
    transactions, rawTransactions, withdrawals, blobGasUsed, excessBlobGas, slotNumber,
    blockAccessList, parentHashSize, parentHash, feeRecipientSize, feeRecipient, stateRootSize,
    stateRoot, receiptsRootSize, receiptsRoot, logsBloomSize, logsBloom, prevRandaoSize,
    prevRandao, blockHashSize, blockHash⟩
  obtain ⟨address, pointerRep, lengthRep, bytesRep⟩ := blockAccessList
  have seg0 : Seg writeSuccessParentPc writeSuccessBytesCallExitPc
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine 0x1571c := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  obtain ⟨retired0, run0⟩ := writeSuccessBlockAccessPointerLoadStep fromStep address args
    before.machine access atPc stack pointerRep aligned loaded
  have seg1 := seg0.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessBytesCallExitPc; native_decide) x10 (BitVec.ofNat 64 address)
    0x15720 retired0 run0 (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite before.machine 0x1571c retired0 x10 (BitVec.ofNat 64 address)).mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨retired1, run1⟩ := writeSuccessBlockAccessLengthLoadStep (fromStep + 1) address
    args.decoded.payload.blockAccessList.size args _ access1 seg1.atPc
    (seg1.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    lengthRep aligned loaded1
  have seg2 := seg1.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessBytesCallExitPc; native_decide) x11
    (BitVec.ofNat 64 args.decoded.payload.blockAccessList.size) 0x15724 retired1 run1
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg access seg2
  obtain ⟨baseMachine, seg3⟩ := seg2.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessBytesCallExitPc; native_decide) x1 0x15724 0x15728
    (writeSuccessBlockAccessCallBaseStep (fromStep + 2) _ access2.configured seg2.atPc (by
      simpa [seg2.memEq (by simp)] using loaded))
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access3 := writeSuccessAccessOfSeg access seg3
  have loaded3 : Artifacts.programImage.fileBytesLoadedFaithfully baseMachine.mem := by
    simpa [seg3.memEq (by simp)] using loaded
  obtain ⟨retired3, callRun⟩ := writeSuccessBlockAccessCallStep (fromStep + 3) baseMachine
    access3.configured seg3.atPc (seg3.reg x1 0x15724 (by simp)) loaded3
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement baseMachine) 0x15728 0x15c6c x1 0x1572c)
    0x15c6c retired3
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes baseMachine 0x15728 0x15c6c retired3 x1 0x1572c
  have callAtPc : callMachine.regs.get? PC = some 0x15c6c := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callMemEq : callMachine.mem = before.machine.mem := by
    have callBaseMemEq : callMachine.mem = baseMachine.mem := by
      change
        (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement baseMachine) 0x15728 0x15c6c x1 0x1572c)
          0x15c6c retired3).mem = baseMachine.mem
      rw [tryStepControlFlowAfterRetired_mem]
      change (controlFlowJumpState (tryStepControlFlowAfterIncrement baseMachine)
        0x15728 0x15c6c).mem = baseMachine.mem
      rw [controlFlowJumpState_mem]
      rfl
    exact callBaseMemEq.trans (seg3.memEq (by simp))
  have callPrefix : ConfinedPrefix writeSuccessParentPc writeSuccessBytesCallExitPc
      (fun _ _ _ _ _ => False) (fromStep + 3) 1 baseMachine callMachine :=
    ConfinedPrefix.ownStep seg3.atPc
      (by unfold writeSuccessParentPc; exact
        ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
      (by unfold writeSuccessBytesCallExitPc; native_decide) callRun
  have callEnd : ScopedTrace writeSuccessParentPc writeSuccessBytesCallExitPc
      (fun _ _ _ _ _ => False) (fromStep + 4) 0 callMachine callMachine :=
    .exitAt _ _ 0x15c6c callAtPc rfl
  have parentMachineTrace := seg3.confined.trans callPrefix 0 callMachine callEnd
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 4 before callState := by
    simpa [callState] using liftWriteSuccessParentTrace before parentMachineTrace
  let value : BytesEncoderValue :=
    { address, bytes := args.decoded.payload.blockAccessList }
  let childArgs : EncoderCallArgs BytesEncoderValue :=
    { returnAddress := 0x1572c
      callerStack := args.stackPointer - 0x7d0
      inputSize := args.inputSize
      value }
  have childEntry : EncoderCallEntry Elflings.writeSuccessBytesEntry
      Elflings.writeSuccessBytesExitPcs BytesEncoderBinding childArgs callState := by
    unfold EncoderCallEntry
    refine ⟨(by dsimp [childArgs]; native_decide), writeSuccessChildStackBound upper,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [callState] using callAtPc
    · simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert, childArgs]
    · exact (callWrites.get x2 (by decide)).trans
        (seg3.reg x2 (BitVec.ofNat 64 (args.stackPointer - 0x7d0)) (by simp))
    · refine ⟨bytesRep.byteSliceBytesRep.1, ?_, ?_, ?_⟩
      · exact (callWrites.get x10 (by decide)).trans
          (seg3.reg x10 (BitVec.ofNat 64 address) (by simp))
      · exact (callWrites.get x11 (by decide)).trans
          (seg3.reg x11 (BitVec.ofNat 64 args.decoded.payload.blockAccessList.size) (by simp))
      · simpa [callState, callMemEq, childArgs, value] using bytesRep.byteSliceBytesRep
    · simpa [callState, callMemEq] using loaded
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have accessCall : WriteSuccessMachineAccess args callMachine := {
    configured := configuredAfterWriteSuccessCall 0x15728 0x15c6c 0x1572c retired3
      access3.configured
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.frameStore offset width bound)
    frameNoMMIO := access3.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.decodedLoad offset width bound)
    decodedNoMMIO := access3.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq callPmaEq access3.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq callPmaEq access3.outputLengthStore
    writerRegionBeforeOutputContext := access3.writerRegionBeforeOutputContext
    frameNotCode := access3.frameNotCode }
  have frameInWriter : ∀ address,
      byteRange (args.stackPointer - 0x7d0 - 48) 48 address →
      writeSuccessFrameMemory args address := by
    intro point inside
    exact writeSuccessChildFrame48_mem_frame lower inside
  obtain ⟨childUsed, after, handoff⟩ := writeSuccessEncoderChildHandoff child
    (fun inside => by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lo, hi⟩
      simp [Elflings.writeSuccessBytesExecutionPcRanges] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, hi⟩)
    fromStep 4 args value before callState childArgs rfl childEntry parentTrace
    ⟨rfl, rfl, rfl, rfl⟩ callMemEq accessCall (by simpa [callState, callMemEq] using loaded)
    lower frameInWriter
  have payloadAfter := writeSuccessPayloadContextAfterChild decodedEq lower upper
    access.writerRegionBeforeOutputContext context handoff.memory
    (fun address inside => Or.inl (frameInWriter address inside)) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      rw [decodedEq] at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      rw [decodedEq] at inside
      omega) (by
      intro index inBounds inside
      unfold byteRange at inside
      omega) (by
      intro values word member index inBounds inside
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> unfold byteRange at inside <;> omega)
  have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact (saved word member).of_writesOnlyWithin handoff.memory (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  exact ⟨childUsed, after, {
    trace := handoff.trace
    atPc := handoff.atPc
    stack := handoff.stack
    stdout := handoff.stdout
    stdin := handoff.stdin
    cursor := handoff.cursor
    exitCode := handoff.exitCode
    saved := savedAfter
    payloadContext := payloadAfter
    loaded := handoff.loaded
    access := handoff.access
    memory := handoff.memory }⟩

set_option genInjectivity false in
/-- The parent call setup and exact bare-metal `write_output` leaf, returning at `0x1573c`. -/
structure WriteSuccessOutputHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (before after : EndpointState)
    (values : DecodeCalleeSavedValues) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 9 before after
  atPc : EndpointPc after = some 0x1573c
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ args.decoded.parentBeaconBlockRoot
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WritesOnlyWithin writeOutputMemory before.machine after.machine

private theorem writeSuccessOutputHandoff (fromStep : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x1572c)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (lower : 0x880 ≤ args.stackPointer) (upper : args.stackPointer < 2 ^ 64)
    (decodedAddress : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ after, WriteSuccessOutputHandoff fromStep args payloadBytes before after values := by
  have rootSize : args.decoded.parentBeaconBlockRoot.size = 32 :=
    (context.stable before.machine.mem (fun _ _ => rfl)).2.2.2.2.1
  have seg0 : Seg writeSuccessOutputSetupPc (fun pc => pc = 0x10190)
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine 0x1572c := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  obtain ⟨retired0, run0⟩ := writeSuccessOutputBufferStep fromStep args before.machine
    access atPc stack loaded
  have seg1 := seg0.stepKnown
    (by exact Or.inl ⟨(0x156e8, 0x15730), by native_decide, by native_decide,
      by native_decide⟩)
    (by native_decide) x10
    (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x3e8)) 0x15730 retired0 run0
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite before.machine 0x1572c retired0 x10
        (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x3e8))).mem := by
    simpa [seg1.memEq (by simp)] using loaded
  obtain ⟨retired1, run1⟩ := writeSuccessOutputLengthStep (fromStep + 1) _
    access1.configured seg1.atPc loaded1
  have seg2 := seg1.stepKnown
    (by exact Or.inr ⟨(0x15730, 0x1573c), by native_decide, by native_decide,
      by native_decide⟩)
    (by native_decide) x11 32 0x15734 retired1 run1
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access2 := writeSuccessAccessOfSeg access seg2
  have outputSetupMemEq :
      (afterRegisterWrite
        (afterRegisterWrite before.machine 0x1572c retired0 x10
          (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x3e8)))
        0x15730 retired1 x11 32).mem = before.machine.mem := seg2.memEq (by simp)
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite
        (afterRegisterWrite before.machine 0x1572c retired0 x10
          (BitVec.ofNat 64 (args.stackPointer - 0x7d0 + 0x3e8)))
        0x15730 retired1 x11 32).mem := by
    rw [outputSetupMemEq]
    exact loaded
  obtain ⟨baseMachine, seg3⟩ := seg2.step
    (by exact Or.inr ⟨(0x15730, 0x1573c), by native_decide, by native_decide,
      by native_decide⟩)
    (by native_decide) x1 0x10734 0x15738
    (writeSuccessOutputCallBaseStep (fromStep + 2) _ access2.configured seg2.atPc loaded2)
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access3 := writeSuccessAccessOfSeg access seg3
  have loaded3 : Artifacts.programImage.fileBytesLoadedFaithfully baseMachine.mem := by
    simpa [seg3.memEq (by simp)] using loaded
  obtain ⟨retired3, callRun⟩ := writeSuccessOutputCallStep (fromStep + 3) baseMachine
    access3.configured seg3.atPc (seg3.reg x1 0x10734 (by simp)) loaded3
  let callMachine := tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement baseMachine) 0x15738 0x10190 x1 0x1573c)
    0x10190 retired3
  let callState : EndpointState := { before with machine := callMachine }
  have callWrites := callRetirement_writes baseMachine 0x15738 0x10190 retired3 x1 0x1573c
  have callAtPc : callMachine.regs.get? PC = some 0x10190 := by
    simp [callMachine, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  have callMemEq : callMachine.mem = before.machine.mem := by
    have callBaseMemEq : callMachine.mem = baseMachine.mem := by
      change
        (tryStepControlFlowAfterRetired
          (callLinkState (tryStepControlFlowAfterIncrement baseMachine) 0x15738 0x10190 x1 0x1573c)
          0x10190 retired3).mem = baseMachine.mem
      rw [tryStepControlFlowAfterRetired_mem]
      change (controlFlowJumpState (tryStepControlFlowAfterIncrement baseMachine)
        0x15738 0x10190).mem = baseMachine.mem
      rw [controlFlowJumpState_mem]
      rfl
    exact callBaseMemEq.trans (seg3.memEq (by simp))
  have callPrefix : ConfinedPrefix writeSuccessOutputSetupPc (fun pc => pc = 0x10190)
      (fun _ _ _ _ _ => False) (fromStep + 3) 1 baseMachine callMachine :=
    ConfinedPrefix.ownStep seg3.atPc
      (by exact Or.inr ⟨(0x15730, 0x1573c), by native_decide, by native_decide,
        by native_decide⟩)
      (by native_decide) callRun
  have callEnd : ScopedTrace writeSuccessOutputSetupPc (fun pc => pc = 0x10190)
      (fun _ _ _ _ _ => False) (fromStep + 4) 0 callMachine callMachine :=
    .exitAt _ _ 0x10190 callAtPc rfl
  have parentMachineTrace := seg3.confined.trans callPrefix 0 callMachine callEnd
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 4 before callState := by
    simpa [callState] using liftWriteSuccessOutputTrace before parentMachineTrace
  have callPmaEq := callWrites.get pma_regions (by simp [stepBookkeeping])
  have accessCall : WriteSuccessMachineAccess args callMachine := {
    configured := configuredAfterWriteSuccessCall 0x15738 0x10190 0x1573c retired3
      access3.configured
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.frameStore offset width bound)
    frameNoMMIO := access3.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq callPmaEq (access3.decodedLoad offset width bound)
    decodedNoMMIO := access3.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq callPmaEq access3.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq callPmaEq access3.outputLengthStore
    writerRegionBeforeOutputContext := access3.writerRegionBeforeOutputContext
    frameNotCode := access3.frameNotCode }
  have bufferOutside : ∀ index, index < args.decoded.parentBeaconBlockRoot.size →
      ¬ writeOutputMemory (args.stackPointer - 0x7d0 + 0x3e8 + index) := by
    intro index inBounds inside
    rw [rootSize] at inBounds
    unfold writeOutputMemory byteRange at inside
    rcases inside with inside | inside
    · have bound := access.writerRegionBeforeOutputContext
      omega
    · have bound := access.writerRegionBeforeOutputContext
      omega
  obtain ⟨after, output⟩ := writeOutputHandoff (fromStep + 4)
    (args.stackPointer - 0x7d0 + 0x3e8) args.decoded.parentBeaconBlockRoot 0x1573c callState
    (by simpa [callState] using callAtPc)
    (by simp [callState, callMachine, callLinkState, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert])
    (by simpa [callState] using ((callWrites.get x10 (by decide)).trans
      (seg3.reg x10 _ (by simp))))
    (by rw [rootSize]; simpa [callState] using ((callWrites.get x11 (by decide)).trans
      (seg3.reg x11 32 (by simp))))
    (by simpa [callState, callMemEq] using context.parentRootRep)
    bufferOutside accessCall.outputBufferStore accessCall.outputLengthStore
    (by native_decide) accessCall.configured
    (by simpa [callState, callMemEq] using loaded)
  have outputMemory : WritesOnlyWithin writeOutputMemory before.machine after.machine := by
    intro address outside
    exact (output.memory address outside).trans
      (congrArg (fun mem => mem.get? address) callMemEq)
  have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact (saved word member).of_writesOnlyWithin outputMemory (by
      intro index inBounds inside
      have bound := access.writerRegionBeforeOutputContext
      unfold writeOutputMemory Region.union byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> rcases inside with inside | inside <;> omega)
  have payloadAfter := writeSuccessPayloadContextAfterChild
    (childMemory := writeOutputMemory) decodedAddress lower upper
    access.writerRegionBeforeOutputContext context outputMemory
    (fun _ inside => Or.inr inside) (by
      intro index inBounds inside
      have bound := access.writerRegionBeforeOutputContext
      unfold writeOutputMemory Region.union byteRange at inside
      rcases inside with inside | inside <;> omega) (by
      intro index inBounds inside
      have bound := access.writerRegionBeforeOutputContext
      rw [context.bytesSize] at inBounds
      unfold writeOutputMemory Region.union byteRange at inside
      rcases inside with inside | inside <;> omega) bufferOutside (by
      intro index inBounds inside
      have bound := access.writerRegionBeforeOutputContext
      rw [context.bytesSize] at inBounds
      rw [decodedAddress] at inside
      unfold writeOutputMemory Region.union byteRange at inside
      rcases inside with inside | inside <;> omega) (by
      intro index inBounds inside
      have bound := access.writerRegionBeforeOutputContext
      rw [decodedAddress] at inside
      unfold writeOutputMemory Region.union byteRange at inside
      rcases inside with inside | inside <;> omega) (by
      intro index inBounds inside
      have bound := access.writerRegionBeforeOutputContext
      unfold writeOutputMemory Region.union byteRange at inside
      rcases inside with inside | inside <;> omega) (by
      intro tailValues word member index inBounds inside
      have bound := access.writerRegionBeforeOutputContext
      simp [writeSuccessLocalTailWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        unfold writeOutputMemory Region.union byteRange at inside <;>
        rcases inside with inside | inside <;> omega)
  have outputPmaEq := output.preserved pma_regions
    (by simp [instructionPreserved, platformPreserved])
  have accessAfter : WriteSuccessMachineAccess args after.machine := {
    configured := output.configured
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq outputPmaEq (accessCall.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq outputPmaEq (accessCall.frameStore offset width bound)
    frameNoMMIO := accessCall.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq outputPmaEq (accessCall.decodedLoad offset width bound)
    decodedNoMMIO := accessCall.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq outputPmaEq accessCall.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq outputPmaEq accessCall.outputLengthStore
    writerRegionBeforeOutputContext := accessCall.writerRegionBeforeOutputContext
    frameNotCode := accessCall.frameNotCode }
  refine ⟨after, {
    trace := by simpa [Nat.add_assoc] using parentTrace.append output.trace
    atPc := output.atPc
    stack := output.stackPreserved.trans
      ((callWrites.get x2 (by decide)).trans (seg3.reg x2 _ (by simp)))
    stdout := by simpa [callState] using output.stdout
    stdin := by simpa [callState] using output.stdin
    cursor := by simpa [callState] using output.cursor
    exitCode := by simpa [callState] using output.exitCode
    saved := savedAfter
    payloadContext := payloadAfter
    loaded := output.loaded
    access := accessAfter
    memory := by
      intro address outside
      exact (output.memory address outside).trans (congrArg (fun mem => mem.get? address) callMemEq) }⟩

set_option genInjectivity false in
/-- The two parent descriptor loads and selected inline versioned-hashes encoder through `0x158e0`. -/
structure WriteSuccessHashesHandoff (fromStep childUsed : Nat) (args : WriteSuccessArgs)
    (payloadBytes : Array UInt8) (before after : EndpointState)
    (values : DecodeCalleeSavedValues) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep (2 + childUsed) before after
  atPc : EndpointPc after = some 0x158e0
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeMany (fun hash => hash)
    args.decoded.versionedHashes
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine
  payloadContext : WriteSuccessPayloadContext args payloadBytes after

private theorem writeSuccessHashesHandoff (child : WriteSuccessHashesInstanceContract)
    (fromStep : Nat) (args : WriteSuccessArgs) (payloadBytes : Array UInt8)
    (values : DecodeCalleeSavedValues) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x1573c)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ childUsed after,
      WriteSuccessHashesHandoff fromStep childUsed args payloadBytes before after values := by
  have decoded := context.stable before.machine.mem (fun _ _ => rfl)
  have hashesRep : SliceRep 32
      (fun mem address hash => hash.size = 32 ∧ BytesRep mem address hash)
      before.machine.mem (args.stackPointer - 0x7d0 + 0x388)
      args.decoded.versionedHashes := by
    apply decoded.2.2.1.rebaseDescriptor (by
      have bound := access.writerRegionBeforeOutputContext
      have contextFits : Elflings.ioContextAddress < 2 ^ 64 := by native_decide
      omega)
    exact context.versionedHashesRelocation
  obtain ⟨hashAddress, addressRep, countRep, arrayRep⟩ := hashesRep
  have seg0 : Seg writeSuccessParentPc (fun pc => pc = 0x15744)
      (fun _ _ _ _ _ => False) writeSuccessParentWrites (fun _ => False)
      [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩]
      fromStep 0 before.machine before.machine 0x1573c := {
    trace := .refl _ _
    confined := .nil
    writes := .refl _ _
    mem := fun _ _ => rfl
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := by intro pair member; simp at member; subst pair; exact stack }
  obtain ⟨retired0, run0⟩ := writeSuccessHashesAddressLoadStep fromStep hashAddress args
    before.machine access atPc stack addressRep aligned loaded
  have seg1 := seg0.stepKnown
    (by unfold writeSuccessParentPc; exact
      ⟨(0x1573c, 0x15744), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) x9 (BitVec.ofNat 64 hashAddress) 0x15740 retired0 run0
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  have access1 := writeSuccessAccessOfSeg access seg1
  have hashesAddressMemEq :
      (afterRegisterWrite before.machine 0x1573c retired0 x9
        (BitVec.ofNat 64 hashAddress)).mem = before.machine.mem := seg1.memEq (by simp)
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully
      (afterRegisterWrite before.machine 0x1573c retired0 x9
        (BitVec.ofNat 64 hashAddress)).mem := by
    rw [hashesAddressMemEq]
    exact loaded
  obtain ⟨machine2, seg2⟩ := seg1.step
    (by unfold writeSuccessParentPc; exact
      ⟨(0x1573c, 0x15744), by native_decide, by native_decide, by native_decide⟩)
    (by native_decide) x8 (BitVec.ofNat 64 args.decoded.versionedHashes.size)
    0x15744 (writeSuccessHashesCountLoadStep (fromStep + 1)
      args.decoded.versionedHashes.size args _ access1 seg1.atPc
      (seg1.reg x2 _ (by simp))
      (by simpa [seg1.memEq (by simp)] using
        (countRep : UIntRep 8 before.machine.mem
          (args.stackPointer - 0x7d0 + 0x390) args.decoded.versionedHashes.size))
      aligned loaded1)
    (by native_decide) (by intro r h; exact Or.inl h)
    (by simp [writeSuccessParentWrites]) (by native_decide) (by native_decide)
    (by simp [RegsOutside, stepBookkeeping])
  let childState : EndpointState := { before with machine := machine2 }
  have parentTrace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep 2 before childState := by
    have machineTrace := seg2.confined 0 machine2 (.exitAt _ _ 0x15744 seg2.atPc rfl)
    simpa [childState] using liftWriteSuccessParentTrace before machineTrace
  obtain ⟨tailValues, tailBefore, tailSourceBefore⟩ := context.linkedTailReps
  have savedAtChild : InlineEncoderSavedWords childState.machine.mem
      (writeSuccessSavedWords args values) := by
    simpa [childState, seg2.memEq (by simp)] using saved
  have tailAtChild : InlineEncoderSavedWords childState.machine.mem
      (writeSuccessLocalTailWords args tailValues) := by
    simpa [childState, seg2.memEq (by simp)] using tailBefore
  have retainedAtChild : InlineEncoderSavedWords childState.machine.mem
      (writeSuccessSavedWords args values ++ writeSuccessLocalTailWords args tailValues) := by
    intro word member
    rw [List.mem_append] at member
    exact member.elim (savedAtChild word) (tailAtChild word)
  obtain ⟨fullCopyBytes, fullCopySize, fullDecodedRep, fullCopyRep⟩ := context.fullCopy
  let childArgs : InlineEncoderArgs (InlineArrayEncoderValue (Array UInt8)) := {
    stackPointer := args.stackPointer - 0x7d0
    inputSize := args.inputSize
    value := ⟨hashAddress, args.decoded.versionedHashes⟩
    savedWords := writeSuccessSavedWords args values ++ writeSuccessLocalTailWords args tailValues
    decodedAddress := args.decodedAddress
    copiedParentRootAddress := args.stackPointer - 0x7d0 + 0x3e8
    copiedVersionedHashesAddress := args.stackPointer - 0x7d0 + 0x388
    copiedPayloadAddress := args.stackPointer - 0x7d0 + 0x408
    copiedSourceAddress := args.stackPointer - 0x7d0 + 0x138
    copiedParentRootBytes := args.decoded.parentBeaconBlockRoot
    copiedPayloadBytes := payloadBytes
    copiedSourceBytes := fullCopyBytes
    decoded := args.decoded }
  have childEntry : InlineEncoderEntry Elflings.writeSuccessHashesEntry
      (InlineArrayEncoderBinding
        (fun state count => state.machine.regs.get? x8 = some (BitVec.ofNat 64 count))
        (fun state address => state.machine.regs.get? x9 = some (BitVec.ofNat 64 address)) 32
        (fun mem address hash => hash.size = 32 ∧ BytesRep mem address hash))
      childArgs childState := by
    unfold InlineEncoderEntry
    dsimp only [childArgs]
    refine ⟨(by omega), (by omega), (by simpa [childState, EndpointPc, MachinePc] using seg2.atPc),
      (by simpa [childState] using seg2.reg x2 _ (by simp)), ?_, ?_, ?_, rfl,
      ?_, ?_, ?_, ?_, ?_⟩
    · unfold InlineArrayEncoderBinding
      exact ⟨arrayRep.1,
        by simpa [childState] using seg2.reg x8 _ (by simp),
        by simpa [childState] using seg2.reg x9 _ (by simp),
        by simpa [childState, seg2.memEq (by simp)] using arrayRep⟩
    · exact retainedAtChild
    · simpa [childState, seg2.memEq (by simp)] using decoded
    · simpa [childState, seg2.memEq (by simp)] using context.parentRootRep
    · simpa [childState, childArgs, seg2.memEq (by simp)] using
        context.versionedHashesRelocation
    · simpa [childState, seg2.memEq (by simp)] using context.payloadRep
    · simpa [childState, seg2.memEq (by simp)] using context.destinationRep
    · exact ⟨by simpa [childState, seg2.memEq (by simp)] using fullDecodedRep,
        by simpa [childState, seg2.memEq (by simp)] using fullCopyRep,
        by simpa [childState, seg2.memEq (by simp)] using loaded⟩
  obtain ⟨childUsed, after, _childBounded, childTrace, childExit⟩ :=
    writeSuccessInlineEncoderHandoff child
    (fun inside => by
      unfold pcInRanges at inside ⊢
      rcases inside with ⟨range, member, lo, hi⟩
      simp [Elflings.writeSuccessHashesExecutionPcRanges] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges], lo, hi⟩
      · exact ⟨(0x14d30, 0x15a14), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩
      · exact ⟨(0x15b9c, 0x15d38), by simp [Elflings.writeSuccessExecutionPcRanges],
          by omega, by omega⟩)
    (fromStep + 2) childArgs childState childEntry
  rcases childExit with ⟨afterPc, stdout, stdin, cursor, exitCode, stackAfter,
    bindingAfter, savedAfter, decodedAfter, parentRootAfter, versionedHashesAfter,
    payloadAfter, destinationAfter, sourceAfter, copiedSourceAfter, childMemory, childAgree,
    childRetired, loadedAfter⟩
  have childInWriter : ∀ address, inlineEncoderMemoryRegion childArgs.stackPointer address →
      writeSuccessFrameMemory args address := by
    intro address inside
    unfold inlineEncoderMemoryRegion byteRange at inside
    unfold writeSuccessFrameMemory byteRange
    dsimp [childArgs] at inside
    omega
  have setupMemory : WriteSuccessMemoryFrame args before.machine childState.machine := by
    simpa [childState] using seg2.mem.mono (by
      intro address impossible
      exact impossible.elim)
  have fullMemory : WriteSuccessMemoryFrame args before.machine after.machine :=
    WritesOnlyWithin.trans_same setupMemory (childMemory.mono childInWriter)
  have decodedBytesAfter := context.decodedBytesRep.of_writesOnlyWithin fullMemory (by
    intro index inBounds inside
    unfold writeSuccessFrameMemory byteRange at inside
    rw [decodedEq] at inside
    omega)
  have stableAfter := context.stable.afterWrites
    (fullMemory.mono (fun _ inside => Or.inl inside))
  have destinationRelocation : ByteWindowRelocation before.machine.mem after.machine.mem
      (args.stackPointer - 0x7d0 + 0x408) (args.stackPointer - 0x7d0 + 0x408) 0x250 := by
    simpa [childArgs, context.bytesSize] using
      ByteWindowRelocation.of_same_bytes context.destinationRep destinationAfter
  obtain ⟨slotValue, slotRep⟩ := context.slotWord
  have slotAfter := slotRep.rebase slotRep.2.1
    (destinationRelocation.atOffset 0x78 8 (by omega))
  obtain ⟨tagValue, tagRep⟩ := context.slotTagWord
  have tagAfter := tagRep.rebase tagRep.2.1
    (destinationRelocation.atOffset 0x80 8 (by omega))
  have savedAbiAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact savedAfter word (List.mem_append_left _ member)
  have tailAfter : InlineEncoderSavedWords after.machine.mem
      (writeSuccessLocalTailWords args tailValues) := by
    intro word member
    exact savedAfter word (List.mem_append_right _ member)
  have tailSourceAfter : ∀ index (bound : index < 16),
      UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
        (tailValues ⟨index, bound⟩) := by
    intro index bound
    exact (tailSourceBefore index bound).of_writesOnlyWithin fullMemory (by
      intro byte byteBound inside
      unfold writeSuccessFrameMemory byteRange at inside
      rw [decodedEq] at inside
      omega)
  have accessAtChild := writeSuccessAccessOfSeg access seg2
  have pmaEq := childAgree pma_regions (by simp [inlineEncoderPreserved])
  have accessAfter : WriteSuccessMachineAccess args after.machine := {
    configured := accessAtChild.configured.mono
      (childAgree.weaken instructionPreserved_inlineEncoderPreserved) childRetired
    frameLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (accessAtChild.frameLoad offset width bound)
    frameStore := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (accessAtChild.frameStore offset width bound)
    frameNoMMIO := accessAtChild.frameNoMMIO
    decodedLoad := fun offset width bound =>
      dataPmaAllows_of_pma_regions_eq pmaEq (accessAtChild.decodedLoad offset width bound)
    decodedNoMMIO := accessAtChild.decodedNoMMIO
    outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq accessAtChild.outputBufferStore
    outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq accessAtChild.outputLengthStore
    writerRegionBeforeOutputContext := accessAtChild.writerRegionBeforeOutputContext
    frameNotCode := accessAtChild.frameNotCode }
  refine ⟨childUsed, after, {
    trace := by simpa [Nat.add_assoc] using parentTrace.append childTrace
    atPc := afterPc
    stack := stackAfter
    stdout := by simpa [childArgs, childState] using stdout
    stdin := by simpa [childState] using stdin
    cursor := by simpa [childState] using cursor
    exitCode := by simpa [childState] using exitCode
    saved := savedAbiAfter
    loaded := loadedAfter
    access := accessAfter
    memory := fullMemory
    payloadContext := {
      fullCopy := ⟨fullCopyBytes, fullCopySize,
        by simpa [childArgs] using And.intro sourceAfter copiedSourceAfter⟩
      destinationRep := destinationAfter
      parentRootRep := parentRootAfter
      decodedBytesRep := decodedBytesAfter
      versionedHashesRelocation := versionedHashesAfter
      bytesSize := context.bytesSize
      stable := stableAfter
      payloadRep := payloadAfter
      slotWord := ⟨slotValue, slotAfter⟩
      slotTagWord := ⟨tagValue, tagAfter⟩
      localTailReps := ⟨tailValues, tailAfter⟩
      linkedTailReps := ⟨tailValues, tailAfter, tailSourceAfter⟩ } }⟩

set_option genInjectivity false in
/-- The two blob-gas scalar encoders following withdrawals. -/
structure WriteSuccessBlobScalarsHandoff (fromStep blobUsed excessUsed : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (before after : EndpointState)
    (values : DecodeCalleeSavedValues) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep
    (3 + blobUsed + 3 + excessUsed) before after
  atPc : EndpointPc after = some 0x15700
  stack : after.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - 0x7d0))
  stdout : after.stdout = before.stdout ++ encodeNatLE 8 args.decoded.payload.blobGasUsed ++
    encodeNatLE 8 args.decoded.payload.excessBlobGas
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  payloadContext : WriteSuccessPayloadContext args payloadBytes after
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memory : WriteSuccessMemoryFrame args before.machine after.machine

private theorem writeSuccessBlobScalarsHandoff
    (child : WriteSuccessIntInstanceContract) (fromStep : Nat)
    (args : WriteSuccessArgs) (payloadBytes : Array UInt8) (values : DecodeCalleeSavedValues)
    (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x156e8)
    (stack : before.machine.regs.get? x2 =
      some (BitVec.ofNat 64 (args.stackPointer - 0x7d0)))
    (context : WriteSuccessPayloadContext args payloadBytes before)
    (saved : SavedWordReps before.machine (writeSuccessSavedWords args values))
    (access : WriteSuccessMachineAccess args before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem)
    (aligned : args.stackPointer % 16 = 0) (lower : 0x880 ≤ args.stackPointer)
    (upper : args.stackPointer < 2 ^ 64)
    (decodedEq : args.decodedAddress = args.stackPointer + 0x20) :
    ∃ blobUsed excessUsed after,
      WriteSuccessBlobScalarsHandoff fromStep blobUsed excessUsed
        args payloadBytes before after values := by
  rcases context.payloadRep with ⟨blockNumber, gasLimit, gasUsed, timestamp, extraData, baseFee,
    transactions, rawTransactions, withdrawals, blobGasUsed, excessBlobGas, slotNumber,
    blockAccessList, parentHashSize, parentHash, feeRecipientSize, feeRecipient, stateRootSize,
    stateRoot, receiptsRootSize, receiptsRoot, logsBloomSize, logsBloom, prevRandaoSize,
    prevRandao, blockHashSize, blockHash⟩
  obtain ⟨blobUsed, afterBlob, blob⟩ := writeSuccessIntCallHandoff child fromStep
    0x156e8 0x156f4 0x470 args.decoded.payload.blobGasUsed 0x156ec args before atPc stack
    blobGasUsed access loaded aligned lower upper
    (fun stepNo state => writeSuccessBlobGasUsedLoadStep stepNo args state)
    writeSuccessBlobGasUsedCallBaseStep writeSuccessBlobGasUsedCallStep
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have contextBlob := writeSuccessPayloadContextAfterInt decodedEq lower upper context blob
  have savedBlob : SavedWordReps afterBlob.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact (saved word member).of_writesOnlyWithin blob.memory (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  let excessStart := fromStep + 3 + blobUsed
  obtain ⟨excessUsed, after, excess⟩ := writeSuccessIntCallHandoff child excessStart
    0x156f4 0x15700 0x478 args.decoded.payload.excessBlobGas 0x156f8 args afterBlob blob.atPc
    blob.stack contextBlob.payloadRep.2.2.2.2.2.2.2.2.2.2.1 blob.access blob.loaded aligned
    lower upper (fun stepNo state => writeSuccessExcessBlobGasLoadStep stepNo args state)
    writeSuccessExcessBlobGasCallBaseStep
    writeSuccessExcessBlobGasCallStep
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessParentPc; exact
      ⟨(0x156e8, 0x15730), by native_decide, by native_decide, by native_decide⟩)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by unfold writeSuccessIntCallExitPc; native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have contextAfter := writeSuccessPayloadContextAfterInt decodedEq lower upper contextBlob excess
  have savedAfter : SavedWordReps after.machine (writeSuccessSavedWords args values) := by
    intro word member
    exact (savedBlob word member).of_writesOnlyWithin excess.memory (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [writeSuccessSavedWords] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega)
  refine ⟨blobUsed, excessUsed, after, {
    trace := ?_
    atPc := excess.atPc
    stack := excess.stack
    stdout := ?_
    stdin := excess.stdin.trans blob.stdin
    cursor := excess.cursor.trans blob.cursor
    exitCode := excess.exitCode.trans blob.exitCode
    saved := savedAfter
    payloadContext := contextAfter
    loaded := excess.loaded
    access := excess.access
    memory := WritesOnlyWithin.trans_same
      (blob.memory.mono (fun address inside => by
        unfold writeSuccessFrameMemory
        exact writeSuccessChildFrame_mem_frame lower inside))
      (excess.memory.mono (fun address inside => by
        unfold writeSuccessFrameMemory
        exact writeSuccessChildFrame_mem_frame lower inside)) }⟩
  · have second : ConfinedTrace EndpointStep EndpointPc
        (pcInRanges Elflings.writeSuccessExecutionPcRanges)
        (fromStep + (3 + blobUsed)) (3 + excessUsed) afterBlob after := by
      simpa [excessStart, Nat.add_assoc] using excess.trace
    simpa [Nat.add_assoc] using blob.trace.append second
  · rw [excess.stdout, blob.stdout]
end BinaryFv.Zesu.MachineExecution
