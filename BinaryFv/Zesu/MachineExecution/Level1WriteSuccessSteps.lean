import BinaryFv.Zesu.MachineExecution.Level1DecodeInputSteps
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
  byteRange (args.stackPointer - 0x810) 0x810

def WriteSuccessIoFrame (before after : EndpointState) : Prop :=
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.stdout = before.stdout ∧ after.exitCode = before.exitCode

def WriteSuccessMemoryFrame (args : WriteSuccessArgs) (before after : State) : Prop :=
  WritesOnlyWithin (writeSuccessFrameMemory args) before after

private theorem writeSuccessChildFrame_mem_frame {stackPointer address : Nat}
    (lower : 0x810 ≤ stackPointer)
    (inside : byteRange (stackPointer - 0x7d0 - 16) 16 address) :
    byteRange (stackPointer - 0x810) 0x810 address := by
  rcases inside with ⟨insideLower, insideUpper⟩
  constructor
  · have frameLower : stackPointer - 0x810 ≤ stackPointer - 0x7e0 :=
      Nat.sub_le_sub_left (by decide : 0x7e0 ≤ 0x810) stackPointer
    have childLower : stackPointer - 0x7e0 = stackPointer - 0x7d0 - 16 := by omega
    rw [childLower] at frameLower
    exact Nat.le_trans frameLower insideLower
  · rw [Nat.sub_add_cancel lower]
    omega

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

private theorem writeSuccessStackResult (stackPointer : Nat) (lower : 0x810 ≤ stackPointer)
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
    (stackLower : 0x810 ≤ args.stackPointer)
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

private theorem writeSuccessAccessOfSeg {args : WriteSuccessArgs} {exit M kv a n base cur pc}
    (access : WriteSuccessMachineAccess args base)
    (seg : Seg writeSuccessParentPc exit
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
    (stackLower : 0x810 ≤ args.stackPointer) (stackFits : args.stackPointer < 2 ^ 64)
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
    (stackLower : 0x810 ≤ args.stackPointer) (stackFits : args.stackPointer < 2 ^ 64)
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
  have initializedNext := initializedByteWindow_of_writeSuccessStore initializedAtLoad nextEq
  have destinationNext := bytesRep_of_writeSuccessStore destinationAtLoad (by omega) nextEq
  exact ⟨next, trace, seg2, destinationRep, sourceRep, bytesSize, fieldBytes, tailAtBase, loadedAtBase, accessAtBase,
    tailNext, tailNextReps, savedNext,
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
    (lower : 0x810 ≤ args.stackPointer) (fits : args.stackPointer < 2 ^ 64)
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
  have initializedNext := initializedByteWindow_of_writeSuccessStore initializedLoaded nextEq
  have copiedNext := bytesRep_of_writeSuccessStore copiedLoaded (by omega) nextEq
  exact ⟨next, by simpa [Nat.add_assoc] using seg2, tailNext, savedNext, copiedNext, initializedNext,
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
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMachineAccess args next ∧
      WriteSuccessMemoryFrame args state.machine after.machine ∧
      WriteSuccessIoFrame state after := by
  obtain ⟨values, bytes, tailValues, used, after, first, trace, seg, destinationRep,
    sourceRep, bytesSize, fieldBytes, tailBase, loaded, access, _tailWindow, tailFirst, saved, _code, _accessFirst,
    copiedFirst, initializedFirst, memoryFrame, ioFrame⟩ :=
    writeSuccessFirstTailPairHandoff fromStep args state entry
  rcases entry with ⟨_, lower, aligned, fits, decodedEq, _, _, _, _, _, _, _, _, _, _, _⟩
  obtain ⟨next, seg2, tailNext, savedNext, copiedNext, initializedNext, accessNext⟩ :=
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
  exact ⟨values, bytes, tailValues, used, after, next, trace, seg2, destinationRep, sourceRep, bytesSize,
    fieldBytes, tailBase, loaded, access, tailNext, savedNext, copiedNext, initializedNext, accessNext,
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
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMachineAccess args next ∧
      WriteSuccessMemoryFrame args state.machine after.machine ∧
      WriteSuccessIoFrame state after := by
  obtain ⟨values, bytes, tailValues, used, after, cur1, trace, seg1, destinationRep,
    sourceRep, bytesSize, fieldBytes, tailBase, loaded, access, tail1, saved1, copied1, initialized1, access1, memoryFrame,
    ioFrame⟩ :=
    writeSuccessSecondTailPairHandoff fromStep args state entry
  rcases entry with ⟨_, lower, aligned, fits, decodedEq, _, _, _, _, _, _, _, _, _, _, _⟩
  obtain ⟨cur2, seg2, tail2, saved2, copied2, initialized2, access2⟩ :=
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
  obtain ⟨cur3, seg3, tail3, saved3, copied3, initialized3, access3⟩ :=
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
  obtain ⟨cur4, seg4, tail4, saved4, copied4, initialized4, access4⟩ :=
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
  obtain ⟨cur5, seg5, tail5, saved5, copied5, initialized5, access5⟩ :=
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
  obtain ⟨cur6, seg6, tail6, saved6, copied6, initialized6, access6⟩ :=
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
  obtain ⟨cur7, seg7, tail7, saved7, copied7, initialized7, access7⟩ :=
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
  obtain ⟨cur8, seg8, tail8, saved8, copied8, initialized8, access8⟩ :=
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
  obtain ⟨cur9, seg9, tail9, saved9, copied9, initialized9, access9⟩ :=
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
  exact ⟨values, bytes, tailValues, used, after, cur9, trace, seg9, destinationRep,
    sourceRep, bytesSize, fieldBytes, tailBase, loaded, access, tail9, saved9, copied9, initialized9, access9,
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
    (stackLower : 0x810 ≤ args.stackPointer)
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
  exact ⟨next, nextSeg, tailNext, savedNext, copiedNext, initializedNext,
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
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMachineAccess args next ∧
      WriteSuccessMemoryFrame args state.machine after.machine ∧
      WriteSuccessIoFrame state after := by
  obtain ⟨values, bytes, tailValues, used, after, cur9, trace, seg9, destinationRep,
    sourceRep, bytesSize, fieldBytes, tailBase, loaded, access, _tail9, saved9, copied9, initialized9, _access9, memoryFrame,
    ioFrame⟩ :=
    writeSuccessFirstTenTailPairsHandoff fromStep args state entry
  rcases entry with ⟨_, lower, aligned, _, decodedEq, _, _, _, _, _, _, _, _, _, _, _⟩
  let kv0 : List RegVal :=
    [⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
     ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
  have seg0 := seg9.forget (kv' := kv0) (by simp [kv0])
  obtain ⟨cur10, seg10, tail10, saved10, copied10, initialized10, access10⟩ :=
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
  obtain ⟨cur11, seg11, tail11, saved11, copied11, initialized11, access11⟩ :=
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
  obtain ⟨cur12, seg12, tail12, saved12, copied12, initialized12, access12⟩ :=
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
  obtain ⟨cur13, seg13, tail13, saved13, copied13, initialized13, access13⟩ :=
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
  exact ⟨values, bytes, tailValues, used, after, cur13, trace,
    by simpa [Nat.add_assoc] using seg13, destinationRep, sourceRep, bytesSize, fieldBytes, tailBase, loaded, access,
    tail13, saved13, copied13, initialized13, access13, memoryFrame, ioFrame⟩

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
    (stackLower : 0x810 ≤ args.stackPointer) (stackFits : args.stackPointer < 2 ^ 64)
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
  have initializedNext := initializedByteWindow_of_writeSuccessStore initialized nextEq
  have copiedNext := bytesRep_of_writeSuccessStore copied (by omega) nextEq
  exact ⟨next, nextSeg, tailNext, savedNext, copiedNext, initializedNext,
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
      Artifacts.programImage.fileBytesLoadedFaithfully next.mem ∧
      WriteSuccessMachineAccess args next ∧
      BytesRep next.mem (args.stackPointer - 0x7d0 + 0x138) bytes ∧
      InitializedByteWindow next.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMemoryFrame args state.machine next ∧
      WriteSuccessIoFrame state after := by
  obtain ⟨values, bytes, tailValues, used, after, cur13, trace, seg13, destinationRep,
    sourceRep, bytesSize, fieldBytes, tailBase, loaded, access, _tail13, saved13, copied13, initialized13, _access13, memoryFrame,
    ioFrame⟩ :=
    writeSuccessFirstFourFinalLoadsHandoff fromStep args state entry
  rcases entry with ⟨_, lower, aligned, fits, decodedEq, _, _, _, _, _, _, _, _, _, _, _⟩
  let kvBase : List RegVal := [⟨x13, BitVec.ofNat 64 (tailValues ⟨13, by omega⟩)⟩,
     ⟨x12, BitVec.ofNat 64 (tailValues ⟨12, by omega⟩)⟩,
     ⟨x11, BitVec.ofNat 64 (tailValues ⟨11, by omega⟩)⟩,
     ⟨x10, BitVec.ofNat 64 (tailValues ⟨10, by omega⟩)⟩,
     ⟨x2, BitVec.ofNat 64 (args.stackPointer - 0x7d0)⟩,
     ⟨x8, BitVec.ofNat 64 args.decodedAddress⟩]
  obtain ⟨curL14, segL14, tailL14, savedL14, copiedL14, initializedL14, accessL14⟩ :=
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
  obtain ⟨curS14, segS14, tailS14, savedS14, copiedS14, initializedS14, accessS14⟩ :=
    writeSuccessTailStoreStep args values tailValues (tailValues ⟨14, by omega⟩)
      0x14de4 0x60 0x60 (.Regidx 14#5) 0x23 0x30 0xe1 0x06 segL14 access loaded
      lower fits decodedEq tailBase savedL14 initializedL14 copiedL14 (by simp)
      (fun premise writes => rX_x14_run premise
        (BitVec.ofNat 64 (tailValues ⟨14, by omega⟩))
        ((writes.get x14 (by decide)).trans
          (segL14.reg x14 (BitVec.ofNat 64 (tailValues ⟨14, by omega⟩))
            (by simp))))
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
  obtain ⟨curL15, segL15, tailL15, savedL15, copiedL15, initializedL15, accessL15⟩ :=
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
  obtain ⟨curS15, segS15, tailS15, savedS15, copiedS15, initializedS15, accessS15⟩ :=
    writeSuccessTailStoreStep args values tailValues (tailValues ⟨15, by omega⟩)
      0x14dec 0x58 0x58 (.Regidx 14#5) 0x23 0x3c 0xe1 0x04 segL15 access loaded
      lower fits decodedEq tailBase savedL15 initializedL15 copiedL15 (by simp [kvBase])
      (fun premise writes => rX_x14_run premise
        (BitVec.ofNat 64 (tailValues ⟨15, by omega⟩))
        ((writes.get x14 (by decide)).trans
          (segL15.reg x14 (BitVec.ofNat 64 (tailValues ⟨15, by omega⟩))
            (by simp [kvBase]))))
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
  obtain ⟨curS10, segS10, tailS10, savedS10, copiedS10, initializedS10, accessS10⟩ :=
    writeSuccessTailStoreStep args values tailValues (tailValues ⟨10, by omega⟩)
      0x14df0 0x128 0x128 (.Regidx 10#5) 0x23 0x34 0xa1 0x12 segS15 access loaded
      lower fits decodedEq tailBase savedS15 initializedS15 copiedS15 (by simp [kvBase])
      (fun premise writes => rX_x10_run premise
        (BitVec.ofNat 64 (tailValues ⟨10, by omega⟩))
        ((writes.get x10 (by decide)).trans
          (segS15.reg x10 (BitVec.ofNat 64 (tailValues ⟨10, by omega⟩))
            (by simp [kvBase]))))
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
  obtain ⟨curS11, segS11, tailS11, savedS11, copiedS11, initializedS11, accessS11⟩ :=
    writeSuccessTailStoreStep args values tailValues (tailValues ⟨11, by omega⟩)
      0x14df4 0x130 0x130 (.Regidx 11#5) 0x23 0x38 0xb1 0x12 segS10 access loaded
      lower fits decodedEq tailBase savedS10 initializedS10 copiedS10 (by simp [kvBase])
      (fun premise writes => rX_x11_run premise
        (BitVec.ofNat 64 (tailValues ⟨11, by omega⟩))
        ((writes.get x11 (by decide)).trans
          (segS10.reg x11 (BitVec.ofNat 64 (tailValues ⟨11, by omega⟩))
            (by simp [kvBase]))))
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
  obtain ⟨curS12, segS12, tailS12, savedS12, copiedS12, initializedS12, accessS12⟩ :=
    writeSuccessTailStoreStep args values tailValues (tailValues ⟨12, by omega⟩)
      0x14df8 0x118 0x118 (.Regidx 12#5) 0x23 0x3c 0xc1 0x10 segS11 access loaded
      lower fits decodedEq tailBase savedS11 initializedS11 copiedS11 (by simp [kvBase])
      (fun premise writes => rX_x12_run premise
        (BitVec.ofNat 64 (tailValues ⟨12, by omega⟩))
        ((writes.get x12 (by decide)).trans
          (segS11.reg x12 (BitVec.ofNat 64 (tailValues ⟨12, by omega⟩))
            (by simp [kvBase]))))
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
  obtain ⟨curS13, segS13, tailS13, savedS13, copiedS13, initializedS13, accessS13⟩ :=
    writeSuccessTailStoreStep args values tailValues (tailValues ⟨13, by omega⟩)
      0x14dfc 0x120 0x120 (.Regidx 13#5) 0x23 0x30 0xd1 0x12 segS12 access loaded
      lower fits decodedEq tailBase savedS12 initializedS12 copiedS12 (by simp [kvBase])
      (fun premise writes => rX_x13_run premise
        (BitVec.ofNat 64 (tailValues ⟨13, by omega⟩))
        ((writes.get x13 (by decide)).trans
          (segS12.reg x13 (BitVec.ofNat 64 (tailValues ⟨13, by omega⟩))
            (by simp [kvBase]))))
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
  exact ⟨values, bytes, tailValues, used, after, curS13, trace,
    by simpa [kvBase, kvFinal, Nat.add_assoc] using segS13, destinationRep, sourceRep, bytesSize,
    fieldBytes, tailS13, savedS13, writeSuccessCodeOfSeg access loaded lower segS13, accessS13, copiedS13,
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
      Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
      WriteSuccessMachineAccess args after.machine ∧
      InitializedByteWindow after.machine.mem (args.stackPointer - 0x7d0 + 0x138) 720 ∧
      WriteSuccessMemoryFrame args state.machine after.machine := by
  obtain ⟨values, bytes, tailValues, parentUsed, parentAfter, tailMachine, parentTrace,
    tailSeg, destinationRep, sourceRep, bytesSize, fieldBytes, tailReps, saved, loaded, access, copied, initialized,
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
  have stackLower : 0x810 ≤ args.stackPointer := entry.2.1
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
      frameNotCode := access.frameNotCode }
  refine ⟨values, bytes, tailValues, parentUsed, childUsed, final, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, bytesSize, fieldBytes, ?_, ?_, childFrame.2.2.1, accessFinal, ?_, finalMemory⟩
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
  sourceRep : BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes
  tailReps : ∀ index (inBounds : index < 16),
    UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
      (tailValues ⟨index, inBounds⟩)
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memoryFrame : WriteSuccessMemoryFrame args state.machine after.machine
  fieldBytes : RawPayloadFieldBytes bytes args.decoded.payload
  fieldReps : RawPayloadFieldReps after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  payloadRep : ExecutionPayloadRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  decodedBytesRep : BytesRep after.machine.mem args.decodedAddress bytes
  stable : StatelessInputRepStableOutside (writeSuccessFrameMemory args)
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
    decodedFullRep, fullSize, fullFieldBytes, tailReps, saved, loaded, access, initialized,
    memoryFrame⟩ :=
    writeSuccessPrefixHandoff child fromStep args state entry
  have stackLower : 0x810 ≤ args.stackPointer := entry.2.1
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
    stable.of_writesOnlyWithin finalMemory
  have decodedBytesAtCall : BytesRep callMachine.mem args.decodedAddress fullBytes :=
    decodedFullRep.of_mem_eq callPrefixMemEq
  have decodedBytesAtChild : BytesRep childAfter.machine.mem args.decodedAddress fullBytes :=
    decodedBytesAtCall.of_writesOnlyWithin childMem (by
      intro index inBounds inside
      unfold byteRange at inside
      simp [memcpyArgs, bytesSize] at inside
      rw [decodedEq] at inside
      omega)
  have decodedBytesFinal : BytesRep finalMachine.mem args.decodedAddress bytes := by
    have fullFinal : BytesRep finalMachine.mem args.decodedAddress fullBytes := by
      simpa [finalSeg.memEq (by simp)] using decodedBytesAtChild
    dsimp [bytes]
    exact fullFinal.extractPrefix (by rw [fullSize]; omega)
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
    tailReps := tailAfter
    saved := savedAfter
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
    stable := by simpa [finalState] using stable.afterWrites finalMemory }⟩
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
      ConfinedTrace EndpointStep EndpointPc
        (pcInRanges Elflings.writeSuccessExecutionPcRanges) fromStep used before after ∧
      RawEncoderExit success args () before after := by
  obtain ⟨stepBound, implements⟩ := child
  obtain ⟨used, after, unit, positive, bounded, trace, exitPc, allowed, exit⟩ :=
    implements args fromStep before childEntry
  exact ⟨used, after, trace.weaken (fun _ pc => insideWriter pc), exit⟩

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
  obtain ⟨childUsed, childAfter, childTrace, childExit⟩ :=
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
  apply writeSuccessRawEncoderHandoff child (fun inside => by
    simpa [Elflings.writeSuccessRawLine140ExecutionPcRanges] using
      writeSuccessRawPc_in_writeSuccess inside (by omega) (by omega))
    fromStep rawArgs before
  exact ⟨by simpa [EndpointPc, MachinePc] using atPc, by simpa [rawArgs] using source,
    by simpa [rawArgs] using rep, loaded⟩

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
  bytesSize : bytes.size = 0x250
  sourceRep : BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes
  tailReps : ∀ index (inBounds : index < 16),
    UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
      (tailValues ⟨index, inBounds⟩)
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memoryFrame : WriteSuccessMemoryFrame args before.machine after.machine
  fieldReps : RawPayloadFieldReps after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  payloadRep : ExecutionPayloadRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  decodedBytesRep : BytesRep after.machine.mem args.decodedAddress bytes
  stable : StatelessInputRepStableOutside (writeSuccessFrameMemory args)
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
      bytesSize := initialHandoff.bytesSize
      sourceRep := by simpa [rawMemory] using initialHandoff.sourceRep
      tailReps := by
        intro index inBounds
        simpa [rawMemory] using initialHandoff.tailReps index inBounds
      saved := by
        intro word member
        simpa [rawMemory] using initialHandoff.saved word member
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
  bytesSize : bytes.size = 0x250
  sourceRep : BytesRep after.machine.mem (args.stackPointer - 0x7d0 + 0x138) bytes
  tailReps : ∀ index (inBounds : index < 16),
    UIntRep 8 after.machine.mem (args.decodedAddress + 720 + index * 8)
      (tailValues ⟨index, inBounds⟩)
  saved : SavedWordReps after.machine (writeSuccessSavedWords args values)
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem
  access : WriteSuccessMachineAccess args after.machine
  memoryFrame : WriteSuccessMemoryFrame args before.machine after.machine
  payloadRep : ExecutionPayloadRep after.machine.mem
    (args.stackPointer - 0x7d0 + 0x408) args.decoded.payload
  decodedBytesRep : BytesRep after.machine.mem args.decodedAddress bytes
  stable : StatelessInputRepStableOutside (writeSuccessFrameMemory args)
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
  have lower : 0x810 ≤ args.stackPointer := entry.2.1
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
  have fullMemory := WritesOnlyWithin.trans_same handoff.memoryFrame
    (WritesOnlyWithin.trans_same beforeCallMemory writerChildMem)
  have stableAfter := handoff.stable.afterWrites
    (WritesOnlyWithin.trans_same beforeCallMemory writerChildMem)
  have decodedAfter := stableAfter.of_writesOnlyWithin (fun _ _ => rfl)
  have destinationAtCall := handoff.destinationRep.of_mem_eq callMemEq
  have destinationAfter := destinationAtCall.of_writesOnlyWithin childMem (by
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
      bytesSize := handoff.bytesSize
      sourceRep := sourceAfter
      tailReps := tailAfter
      saved := savedAfter
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
end BinaryFv.Zesu.MachineExecution
