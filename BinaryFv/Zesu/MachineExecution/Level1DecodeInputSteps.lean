import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.RiscV.Instruction.DecodeTactic
import BinaryFv.RiscV.Elfling.Seg

/-!
# Parent-owned `decodeInput` steps

These instruction-class adapters and `Seg` compositions cover the optimized `decodeInput`
instructions outside the selected inline `ssz.decode` child. The Level-2 refinement edge consumes
the child contracts between these parent-owned traces.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.Binary BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register
open MemoryAccessType mem_payload page_based_mem_type

private theorem ofNatAlignedEight (address : Nat) (fits : address < 2 ^ 64)
    (aligned : address % 8 = 0) :
    is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 address)) 8 = true ∧
      is_aligned_paddr (physaddr.Physaddr (BitVec.ofNat 64 address)) 8 = true := by
  have tmodEight : ((address : Nat) : Int).tmod 8 = 0 := congrArg Int.ofNat aligned
  constructor <;> simp only [is_aligned_vaddr, is_aligned_paddr] <;>
    change ((((BitVec.ofNat 64 address).toNat : Int).tmod 8) == 0) = true <;>
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] <;> simpa [tmodEight]

/-- An exact `addi sp, sp, immediate`. -/
theorem decodeInputAddiX2Step (stepNo pc : Nat) (state : State) (immediate : BitVec 12)
    (source result : BitVec 64)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (atSource : state.regs.get? x2 = some source)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (resultEq : result = iTypeResult .ADDI immediate source)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (immediate, .Regidx 2#5, .Regidx 2#5, .ADDI)))
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x2 result) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have writes := stepPremiseState_writes state (BitVec.ofNat 64 pc)
  have sourceRead : premise.regs.get? x2 = some source :=
    writes.get x2 (by decide) |>.trans atSource
  have execute : Runs (execute (.ITYPE (immediate, .Regidx 2#5, .Regidx 2#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x2 result } (.Retire_Success ()) := by
    change Runs (execute_ITYPE immediate (.Regidx 2#5) (.Regidx 2#5) .ADDI) _ _ _
    rw [resultEq]
    exact execute_ITYPE_run premise _ immediate (.Regidx 2#5) (.Regidx 2#5) .ADDI source
      (rX_x2_run premise source sourceRead) (wX_x2_run premise _)
  exact configuredRegisterWriteStep stepNo pc state x2 result
    (.ITYPE (immediate, .Regidx 2#5, .Regidx 2#5, .ADDI)) byte0 byte1 byte2 byte3
    configured atPc loaded
    decode execute (pcFits := pcFits) (base := base) (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3)

/-- Production `0x121a4: mv s2, a2`. -/
theorem decodeInputBindS2Step (stepNo : Nat) (state : State) (value : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x121a4)
    (source : state.regs.get? x12 = some value)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x121a4 retired x18 value) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x121a4
  have source' := (stepPremiseState_writes state 0x121a4).get x12 (by decide) |>.trans source
  have execute : Runs (execute (.ITYPE (0, .Regidx 12#5, .Regidx 18#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x18 value } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 12#5) (.Regidx 18#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 0 value = value := by
      simp [iTypeResult, show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
    simpa only [resultEq] using
      execute_ITYPE_run premise _ 0 (.Regidx 12#5) (.Regidx 18#5)
        .ADDI value (rX_x12_run premise value source')
        (wX_x18_run premise (iTypeResult .ADDI 0 value))
  exact configuredRegisterWriteStep stepNo 0x121a4 state x18 value
    (.ITYPE (0, .Regidx 12#5, .Regidx 18#5, .ADDI)) 0x13 0x09 0x06 0x00
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

/-- Production `0x121a8: mv s0, a0`. -/
theorem decodeInputBindS0Step (stepNo : Nat) (state : State) (value : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x121a8)
    (source : state.regs.get? x10 = some value)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x121a8 retired x8 value) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x121a8
  have source' := (stepPremiseState_writes state 0x121a8).get x10 (by decide) |>.trans source
  have execute : Runs (execute (.ITYPE (0, .Regidx 10#5, .Regidx 8#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x8 value } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 10#5) (.Regidx 8#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 0 value = value := by
      simp [iTypeResult, show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
    simpa only [resultEq] using
      execute_ITYPE_run premise _ 0 (.Regidx 10#5) (.Regidx 8#5)
        .ADDI value (rX_x10_run premise value source')
        (wX_x8_run premise (iTypeResult .ADDI 0 value))
  exact configuredRegisterWriteStep stepNo 0x121a8 state x8 value
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

/-- Production error continuation `0x14ca8: mv s6, a0`. -/
theorem decodeInputBindErrorS6Step (stepNo : Nat) (state : State) (status : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14ca8)
    (source : state.regs.get? x10 = some status)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14ca8 retired x22 status) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14ca8
  have source' := (stepPremiseState_writes state 0x14ca8).get x10 (by decide) |>.trans source
  have execute : Runs (execute (.ITYPE (0, .Regidx 10#5, .Regidx 22#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x22 status } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 10#5) (.Regidx 22#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 0 status = status := by
      simp [iTypeResult, show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
    simpa only [resultEq] using
      execute_ITYPE_run premise _ 0 (.Regidx 10#5) (.Regidx 22#5)
        .ADDI status (rX_x10_run premise status source')
        (wX_x22_run premise (iTypeResult .ADDI 0 status))
  exact configuredRegisterWriteStep stepNo 0x14ca8 state x22 status
    (.ITYPE (0, .Regidx 10#5, .Regidx 22#5, .ADDI)) 0x13 0x0b 0x05 0x00
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

/-- An exact `sd offset(sp)`, parameterized by its generated source-register witness. -/
theorem decodeInputStoreStep (stepNo pc offset : Nat) (state : State)
    (stackPointer : Nat) (value : BitVec 64) (imm : BitVec 12) (rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (stackPointer + offset)) 8)
    (notMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + offset)) 8)
    (aligned : (stackPointer + offset) % 8 = 0)
    (fits : stackPointer + offset + 8 ≤ 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 stackPointer + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (stackPointer + offset))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (imm, rs2, .Regidx 2#5, 8)))
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits rs2) premise premise value)
    (pcFits : pc < 2 ^ 64 := by native_decide)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat) := by native_decide)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc))
          (stackPointer + offset) value)
        (BitVec.ofNat 64 pc) retired) false := by
  let premise := coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc)
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise := (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have mseccfgPremise := (agree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have stackPremise := (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x2
    (by decide) |>.trans stackRead
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 2#5) (sign_extend (m := 64) imm) (Store Data) 8)
      premise premise (.Ext_DataAddr_OK
        (virtaddr.Virtaddr (BitVec.ofNat 64 (stackPointer + offset)))) := by
    simpa [addressEq] using get_transformed_data_addr_machine_data_run .store premise
      (.Regidx 2#5) 8 (BitVec.ofNat 64 stackPointer) (sign_extend (m := 64) imm)
      mstatusBits mseccfgBits (rX_x2_run premise (BitVec.ofNat 64 stackPointer) stackPremise)
      mstatusPremise privilegePremise mprvZero mseccfgPremise pmmDisabled
  have physical := phys_access_check_machine_store_allowed premise
    (BitVec.ofNat 64 (stackPointer + offset)) 8
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (storePmaAllows_of_agree agree pma)
    (ofNatAlignedEight (stackPointer + offset) (by omega) aligned).2
  have noMMIO := storeMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (stackPointer + offset)) 8 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  let afterWrite := afterWriteBytes (width := 8) premise (stackPointer + offset) value
  have access : ConfiguredDwordStoreAccess state afterWrite (BitVec.ofNat 64 pc) imm
      (.Regidx 2#5) rs2 :=
    ⟨_, mstatusBits, _, mstatusPremise, privilegePremise, mprvZero,
      dataRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc)), addressRun,
      (ofNatAlignedEight (stackPointer + offset) (by omega) aligned).1,
      physical, noMMIO, by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact writeBytes_run_exact premise (stackPointer + offset) value⟩
  simpa [afterWrite] using configuredDwordStoreStep stepNo pc state afterWrite imm
    (.Regidx 2#5) rs2 byte0 byte1 byte2 byte3 configured atPc loaded decode access
    (pcFits := pcFits) (base := base) (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3)

def decodeInputParentPc (pc : BitVec 64) : Prop :=
  pcInRanges Elflings.decodeInputOwnedPcRanges pc

def decodeInputParentWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x2 ∨ register = x8 ∨ register = x18 ∨
    register = x22

def decodeInputFrameMemory (args : DecodeInlineArgs) : Region :=
  byteRange (args.boundary.stackPointer - 0xbb0) 0xbb0

def SavedWordReps (state : State) (words : List (Nat × Nat)) : Prop :=
  ∀ word ∈ words, UIntRep 8 state.mem word.1 word.2

def SavedWordsAtOrAbove (address : Nat) (words : List (Nat × Nat)) : Prop :=
  ∀ word ∈ words, address ≤ word.1

private theorem savedWordsAtOrAbove_cons {address : Nat} {value : Nat}
    {words : List (Nat × Nat)} (above : SavedWordsAtOrAbove (address + 8) words) :
    SavedWordsAtOrAbove address ((address, value) :: words) := by
  intro word member
  simp only [List.mem_cons] at member
  rcases member with rfl | tail
  · omega
  · exact Nat.le_trans (by omega) (above word tail)

def decodeInputIncomingRegs (args : DecodeInlineArgs) (values : DecodeCalleeSavedValues) :
    List RegVal :=
  [⟨x1, BitVec.ofNat 64 args.boundary.returnAddress⟩,
   ⟨x8, values.s0⟩, ⟨x9, values.s1⟩, ⟨x18, values.s2⟩, ⟨x19, values.s3⟩,
   ⟨x20, values.s4⟩, ⟨x21, values.s5⟩, ⟨x22, values.s6⟩, ⟨x23, values.s7⟩,
   ⟨x24, values.s8⟩, ⟨x25, values.s9⟩, ⟨x26, values.s10⟩, ⟨x27, values.s11⟩,
   ⟨x10, BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)⟩,
   ⟨x12, BitVec.ofNat 64 args.boundary.inputAddress⟩,
   ⟨x13, BitVec.ofNat 64 args.boundary.input.size⟩]

private theorem decodeInputIncomingRegs_hold (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (entry : DecodeBoundaryEntry args.boundary args.origin)
    (saved : DecodeCalleeSavedAtRegisters values args.origin) :
    RegsHold args.origin.machine (decodeInputIncomingRegs args values) := by
  rcases entry with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, link, result, _, input, inputSize,
    _, _, _, _, _, _, _, _, _⟩
  rcases saved with ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
  intro pair member
  simp only [decodeInputIncomingRegs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> assumption

private theorem decodeInputFirstStackResult (stackPointer : Nat) (lower : 0xbb0 ≤ stackPointer)
    (upper : stackPointer + 0x380 < 2 ^ 64) :
    BitVec.ofNat 64 (stackPointer - 0x7f0) =
      iTypeResult .ADDI 0x810 (BitVec.ofNat 64 stackPointer) := by
  have sign : sign_extend (m := 64) (0x810#12) =
      BitVec.ofNat 64 (2 ^ 64 - 0x7f0) := by native_decide
  unfold iTypeResult
  change BitVec.ofNat 64 (stackPointer - 0x7f0) =
    BitVec.ofNat 64 stackPointer + sign_extend (m := 64) (0x810#12)
  rw [sign, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have sum : stackPointer + (2 ^ 64 - 0x7f0) =
      (stackPointer - 0x7f0) + 2 ^ 64 := by omega
  rw [sum, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

private theorem decodeInputFinalStackResult (stackPointer : Nat) (lower : 0xbb0 ≤ stackPointer)
    (upper : stackPointer + 0x380 < 2 ^ 64) :
    BitVec.ofNat 64 (stackPointer - 0xbb0) =
      iTypeResult .ADDI 0xc40 (BitVec.ofNat 64 (stackPointer - 0x7f0)) := by
  have sign : sign_extend (m := 64) (0xc40#12) =
      BitVec.ofNat 64 (2 ^ 64 - 0x3c0) := by native_decide
  unfold iTypeResult
  change BitVec.ofNat 64 (stackPointer - 0xbb0) =
    BitVec.ofNat 64 (stackPointer - 0x7f0) + sign_extend (m := 64) (0xc40#12)
  rw [sign, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have sum : stackPointer - 0x7f0 + (2 ^ 64 - 0x3c0) =
      (stackPointer - 0xbb0) + 2 ^ 64 := by omega
  rw [sum, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

/-- The first parent-owned instruction allocates the save area and seeds the live-register
accumulator used by all thirteen following saves. -/
theorem decodeInputAllocateSaveArea (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (entry : DecodeBoundaryEntry args.boundary args.origin)
    (saved : DecodeCalleeSavedAtRegisters values args.origin) :
    ∃ next,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 1 args.origin.machine next 0x1216c := by
  rcases entry with ⟨_stdin, _returnPc, _allocator, atPc, loaded, stackLower, _stackAligned,
    stackUpper, _inputFits, _separated, stackRead, _link, _result, _allocatorReg, _inputReg,
    _sizeReg, _inputAddress, _inputSize, _allocatorState, _allocatorVtable, _savedReturn,
    _input, access, _entrySaved⟩
  let kv := decodeInputIncomingRegs args values
  have seg0 : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      kv fromStep 0 args.origin.machine args.origin.machine 0x12168 := {
    trace := Trace.refl fromStep args.origin.machine
    confined := .nil
    writes := WritesOnlyRegs.refl decodeInputParentWrites args.origin.machine
    mem := fun _ _ => rfl
    aux := AuxStateAgree.refl _
    retired := access.configured.retiredCounter
    atPc := atPc
    regs := decodeInputIncomingRegs_hold args values
      ⟨_stdin, _returnPc, _allocator, atPc, loaded, stackLower, _stackAligned, stackUpper,
        _inputFits, _separated, stackRead, _link, _result, _allocatorReg, _inputReg, _sizeReg,
        _inputAddress, _inputSize, _allocatorState, _allocatorVtable, _savedReturn, _input,
        access, _entrySaved⟩ saved }
  have decode : Runs
      (ext_decode (fetchWord (0x13 : BitVec 8) (0x01 : BitVec 8) (0x01 : BitVec 8)
        (0x81 : BitVec 8)))
      (tryStepControlFlowAfterIncrement args.origin.machine)
      (tryStepControlFlowAfterIncrement args.origin.machine)
      (.ITYPE (0x810, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := access.configured.seccfgPresent
    have privilegeAfter :
        (tryStepControlFlowAfterIncrement args.origin.machine).regs.get? cur_privilege =
          some Privilege.Machine := by
      calc
        _ = args.origin.machine.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using writeReg_read_unchanged
            args.origin.machine minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := access.configured.normal.2.1
    have seccfgAfter :
        (tryStepControlFlowAfterIncrement args.origin.machine).regs.get? mseccfg =
          some seccfgBits := by
      calc
        _ = args.origin.machine.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using writeReg_read_unchanged
            args.origin.machine minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    decode_run
  obtain ⟨retired, run⟩ := decodeInputAddiX2Step fromStep 0x12168 args.origin.machine 0x810
    (BitVec.ofNat 64 args.boundary.stackPointer)
    (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) 0x13 0x01 0x01 0x81
    access.configured atPc stackRead loaded
    (decodeInputFirstStackResult args.boundary.stackPointer stackLower stackUpper) decode
    (base := by rfl)
  exact seg0.step (by
      exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩)
    (by unfold DecodeInlineInitialExecutionPc pcInRanges; native_decide) x2
    (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) 0x1216c ⟨retired, run⟩
    (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by
      simpa [kv, decodeInputIncomingRegs, RegsOutside, RegSet.union, RegSet.only,
        stepBookkeeping] using
        (show RegsOutside (RegSet.union stepBookkeeping (RegSet.only x2)) kv by decide))

private theorem instructionPreserved_disjoint_decodeInputParentWrites :
    RegSet.Disjoint instructionPreserved decodeInputParentWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem platformPreserved_disjoint_decodeInputParentWrites :
    RegSet.Disjoint platformPreserved decodeInputParentWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved bookkeeping
  all_goals simp [platformPreserved] at preserved

private theorem decodeInputStoreDecodeReads {state : State}
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

private theorem decodeInputCodeOfSeg {args : DecodeInlineArgs} {W kv a n base cur pc}
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem)
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) W (decodeInputFrameMemory args) kv a n base cur pc)
    (baseEq : base = args.origin.machine) (stackLower : 0xbb0 ≤ args.boundary.stackPointer) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  subst baseEq
  intro address byte fileByte
  have unchanged := seg.mem address (by
    intro inside
    unfold decodeInputFrameMemory byteRange at inside
    have none := access.frameNotCode address inside.1 (by omega)
    rw [fileByte] at none
    cases none)
  exact unchanged.trans (loaded address byte fileByte)

private theorem decodeInputParentPc_in_execution {pc : BitVec 64}
    (inside : decodeInputParentPc pc) : pcInRanges Elflings.decodeInputExecutionPcRanges pc := by
  unfold decodeInputParentPc at inside
  unfold pcInRanges at inside ⊢
  rcases inside with ⟨range, member, lower, upper⟩
  simp [Elflings.decodeInputOwnedPcRanges] at member
  rcases member with rfl | rfl | rfl <;>
    exact ⟨(0x101d4, 0x14cb0), by simp [Elflings.decodeInputExecutionPcRanges], by omega, by omega⟩

private theorem decodeInputParentPc_not_observed {pc : BitVec 64}
    (inside : decodeInputParentPc pc) : ¬ BareMetalHostTransitionPc pc := by
  unfold decodeInputParentPc pcInRanges at inside
  rcases inside with ⟨range, member, lower, upper⟩
  simp [Elflings.decodeInputOwnedPcRanges] at member
  rcases member with rfl | rfl | rfl <;>
    simp [BareMetalHostTransitionPc, readContextReturnPc, writeContextReturnPc,
      exitContextStorePc] <;>
      omega

private theorem liftDecodeInputParentTrace (template : EndpointState)
    {fromStep count : Nat} {before after : State}
    (trace : ScopedTrace decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.decodeInputExecutionPcRanges)
      fromStep count { template with machine := before } { template with machine := after } := by
  induction trace with
  | exitAt fromStep state pc atPc exitPc =>
      exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step fromStep count pc
        { template with machine := before } { template with machine := middle }
        { template with machine := after } ?_ ?_ ?_ ?_
      · exact atPc
      · exact decodeInputParentPc_in_execution inside
      · exact endpointStep_sail fromStep { template with machine := before } middle
          (fun observed observedPc => by
            change before.regs.get? PC = some observed at observedPc
            rw [atPc] at observedPc
            cases Option.some.inj observedPc
            exact decodeInputParentPc_not_observed inside)
          machineStep
      · simpa using ih
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count call program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

/-- Extend a `decodeInput` segment with one save and retain every earlier, higher-addressed word. -/
theorem decodeInputSaveStep {args : DecodeInlineArgs}
    {kv : List ((r : Register) × RegisterType r)} {a n : Nat} {cur : State} {pc : BitVec 64}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      kv a n args.origin.machine cur pc)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem)
    (words : List (Nat × Nat)) (wordsRep : SavedWordReps cur words)
    (storePc stackPointer offset frameOffset : Nat) (source : BitVec 64) (imm : BitVec 12)
    (rs2 : regidx) (byte0 byte1 byte2 byte3 : UInt8)
    (stackRead : cur.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping cur premise →
      Runs (rX_bits rs2) premise premise source)
    (addressEqNat : stackPointer + offset = args.boundary.stackPointer - 0xbb0 + frameOffset)
    (frameBound : frameOffset + 8 ≤ 0xbb0)
    (belowWords : ∀ word ∈ words, stackPointer + offset + 8 ≤ word.1)
    (pcEq : pc = BitVec.ofNat 64 storePc)
    (inRegion : decodeInputParentPc (BitVec.ofNat 64 storePc))
    (notExit : ¬ DecodeInlineInitialExecutionPc (BitVec.ofNat 64 storePc))
    (decodeOfConfigured : ConfiguredMachinePre EndpointMachinePc cur →
      Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
        (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
        (BitVec.ofNat 8 byte3.toNat)))
        (tryStepStoreAfterIncrement cur) (tryStepStoreAfterIncrement cur)
        (.STORE (imm, rs2, .Regidx 2#5, 8)))
    (addressEq : BitVec.ofNat 64 stackPointer + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (stackPointer + offset))
    (aligned : (stackPointer + offset) % 8 = 0)
    (fits : stackPointer + offset + 8 ≤ 2 ^ 64)
    (keep : RegsOutside stepBookkeeping kv)
    (pcFits : storePc < 2 ^ 64) (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? storePc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (storePc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (storePc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (storePc + 3) = some byte3)
    (advance : Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4 =
      BitVec.ofNat 64 (storePc + 4)) :
    ∃ next,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args) kv a (n + 1)
        args.origin.machine next (BitVec.ofNat 64 (storePc + 4)) ∧
      SavedWordReps next ((stackPointer + offset, source.toNat) :: words) := by
  subst pc
  have configured := access.configured.mono
    (seg.agree instructionPreserved_disjoint_decodeInputParentWrites) seg.retired
  have code := decodeInputCodeOfSeg access loaded seg rfl stackLower
  have decode := decodeOfConfigured configured
  have pma := storePmaAllows_of_agree
    (seg.agree platformPreserved_disjoint_decodeInputParentWrites)
    (access.frameStore frameOffset 8 frameBound)
  have pma' : StorePmaAllows cur (BitVec.ofNat 64 (stackPointer + offset)) 8 := by
    simpa [addressEqNat] using pma
  have noMMIO : StoreMMIOAddressExcluded
      (BitVec.ofNat 64 (stackPointer + offset)) 8 := by
    simpa [addressEqNat] using access.frameNoMMIO frameOffset 8 frameBound
  obtain ⟨retired, run⟩ := decodeInputStoreStep (a + n) storePc offset cur stackPointer source
    imm rs2 byte0 byte1 byte2 byte3 configured seg.atPc stackRead pma' noMMIO
    aligned fits code addressEq decode dataRun (pcFits := pcFits) (base := base)
    (read0 := read0) (read1 := read1) (read2 := read2) (read3 := read3)
  obtain ⟨retired', next, nextEq, nextSeg⟩ := seg.stepStoreWitness
    (width := 8) (stackPointer + offset) source
    (BitVec.ofNat 64 (storePc + 4)) inRegion notExit ⟨retired, run⟩ advance
    (by
      intro address lower upper
      unfold decodeInputFrameMemory byteRange
      omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping)
    keep
  have stepWrites : WritesOnlyWithin (byteRange (stackPointer + offset) 8) cur next := by
    intro address outside
    rw [nextEq]
    exact storeRetirement_mem_writes cur (BitVec.ofNat 64 storePc)
      (Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4) retired'
      (stackPointer + offset) source address outside
  have oldReps : SavedWordReps next words := by
    intro word member
    exact (wordsRep word member).of_writesOnlyWithin stepWrites (by
      intro index indexBound inside
      unfold byteRange at inside
      have below := belowWords word member
      omega)
  have currentRep : UIntRep 8 next.mem (stackPointer + offset) source.toNat := by
    have sourceFits : source.toNat < 2 ^ 64 := source.isLt
    rw [nextEq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
      (coreStoreNextState (tryStepStoreAfterIncrement cur) (BitVec.ofNat 64 storePc))
      (stackPointer + offset) source.toNat sourceFits fits
  refine ⟨next, nextSeg, ?_⟩
  intro word member
  simp only [List.mem_cons] at member
  rcases member with head | tail
  · simpa [head] using currentRep
  · exact oldReps word tail

/-- The first concrete save, `0x1216c: sd ra, 2024(sp)`. -/
theorem decodeInputSaveRa {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 1 args.origin.machine cur 0x1216c)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ next,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 2 args.origin.machine next 0x12170 ∧
      SavedWordReps next
        [(args.boundary.stackPointer - 0x7f0 + 0x7e8,
          (BitVec.ofNat 64 args.boundary.returnAddress).toNat)] := by
  apply decodeInputSaveStep seg access stackLower loaded [] (by
    intro word member
    simp at member) 0x1216c (args.boundary.stackPointer - 0x7f0) 0x7e8 0xba8
    (BitVec.ofNat 64 args.boundary.returnAddress) 0x7e8 (.Regidx 1#5)
    0x23 0x34 0x11 0x7e
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x1_run premise (BitVec.ofNat 64 args.boundary.returnAddress)
      ((writes.get x1 (by decide)).trans
        (seg.reg x1 (BitVec.ofNat 64 args.boundary.returnAddress) (by
          simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · intro word member
    simp at member
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x7e8#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- The second concrete save, `0x12170: sd s0, 2016(sp)`. -/
theorem decodeInputSaveS0 {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 2 args.origin.machine cur 0x12170)
    (words : SavedWordReps cur
      [(args.boundary.stackPointer - 0x7f0 + 0x7e8,
        (BitVec.ofNat 64 args.boundary.returnAddress).toNat)])
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ next,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 3 args.origin.machine next 0x12174 ∧
      SavedWordReps next
        [(args.boundary.stackPointer - 0x7f0 + 0x7e0, values.s0.toNat),
         (args.boundary.stackPointer - 0x7f0 + 0x7e8,
          (BitVec.ofNat 64 args.boundary.returnAddress).toNat)] := by
  apply decodeInputSaveStep seg access stackLower loaded
    [(args.boundary.stackPointer - 0x7f0 + 0x7e8,
      (BitVec.ofNat 64 args.boundary.returnAddress).toNat)] words
    0x12170 (args.boundary.stackPointer - 0x7f0) 0x7e0 0xba0 values.s0 0x7e0
    (.Regidx 8#5) 0x23 0x30 0x81 0x7e
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x8_run premise values.s0
      ((writes.get x8 (by decide)).trans
        (seg.reg x8 values.s0 (by simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · intro word member
    simp only [List.mem_singleton] at member
    subst word
    omega
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x7e0#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- The third concrete save, `0x12174: sd s1, 2008(sp)`. -/
theorem decodeInputSaveS1 {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 3 args.origin.machine cur 0x12174)
    (prior : List (Nat × Nat)) (words : SavedWordReps cur prior)
    (priorAbove : ∀ word ∈ prior,
      args.boundary.stackPointer - 0x7f0 + 0x7d8 + 8 ≤ word.1)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ next,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 4 args.origin.machine next 0x12178 ∧
      SavedWordReps next
        ((args.boundary.stackPointer - 0x7f0 + 0x7d8, values.s1.toNat) :: prior) := by
  apply decodeInputSaveStep seg access stackLower loaded prior words
    0x12174 (args.boundary.stackPointer - 0x7f0) 0x7d8 0xb98 values.s1 0x7d8
    (.Regidx 9#5) 0x23 0x3c 0x91 0x7c
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x9_run premise values.s1
      ((writes.get x9 (by decide)).trans
        (seg.reg x9 values.s1 (by simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · exact priorAbove
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x7d8#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- Production `0x12178: sd s2, 0x7d0(sp)`. -/
theorem decodeInputSaveS2 {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 4 args.origin.machine cur 0x12178)
    (prior : List (Nat × Nat)) (words : SavedWordReps cur prior)
    (priorAbove : ∀ word ∈ prior,
      args.boundary.stackPointer - 0x7f0 + 0x7d0 + 8 ≤ word.1)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ nextState,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 5 args.origin.machine nextState 0x1217c ∧
      SavedWordReps nextState
        ((args.boundary.stackPointer - 0x7f0 + 0x7d0, values.s2.toNat) :: prior) := by
  apply decodeInputSaveStep seg access stackLower loaded prior words
    0x12178 (args.boundary.stackPointer - 0x7f0) 0x7d0 0xb90 values.s2 0x7d0
    (.Regidx 18#5) 0x23 0x38 0x21 0x7d
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x18_run premise values.s2
      ((writes.get x18 (by decide)).trans
        (seg.reg x18 values.s2 (by simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · exact priorAbove
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x7d0#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x1217c: sd s3, 0x7c8(sp)`. -/
theorem decodeInputSaveS3 {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 5 args.origin.machine cur 0x1217c)
    (prior : List (Nat × Nat)) (words : SavedWordReps cur prior)
    (priorAbove : ∀ word ∈ prior,
      args.boundary.stackPointer - 0x7f0 + 0x7c8 + 8 ≤ word.1)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ nextState,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 6 args.origin.machine nextState 0x12180 ∧
      SavedWordReps nextState
        ((args.boundary.stackPointer - 0x7f0 + 0x7c8, values.s3.toNat) :: prior) := by
  apply decodeInputSaveStep seg access stackLower loaded prior words
    0x1217c (args.boundary.stackPointer - 0x7f0) 0x7c8 0xb88 values.s3 0x7c8
    (.Regidx 19#5) 0x23 0x34 0x31 0x7d
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x19_run premise values.s3
      ((writes.get x19 (by decide)).trans
        (seg.reg x19 values.s3 (by simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · exact priorAbove
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x7c8#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x12180: sd s4, 0x7c0(sp)`. -/
theorem decodeInputSaveS4 {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 6 args.origin.machine cur 0x12180)
    (prior : List (Nat × Nat)) (words : SavedWordReps cur prior)
    (priorAbove : ∀ word ∈ prior,
      args.boundary.stackPointer - 0x7f0 + 0x7c0 + 8 ≤ word.1)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ nextState,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 7 args.origin.machine nextState 0x12184 ∧
      SavedWordReps nextState
        ((args.boundary.stackPointer - 0x7f0 + 0x7c0, values.s4.toNat) :: prior) := by
  apply decodeInputSaveStep seg access stackLower loaded prior words
    0x12180 (args.boundary.stackPointer - 0x7f0) 0x7c0 0xb80 values.s4 0x7c0
    (.Regidx 20#5) 0x23 0x30 0x41 0x7d
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x20_run premise values.s4
      ((writes.get x20 (by decide)).trans
        (seg.reg x20 values.s4 (by simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · exact priorAbove
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x7c0#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x12184: sd s5, 0x7b8(sp)`. -/
theorem decodeInputSaveS5 {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 7 args.origin.machine cur 0x12184)
    (prior : List (Nat × Nat)) (words : SavedWordReps cur prior)
    (priorAbove : ∀ word ∈ prior,
      args.boundary.stackPointer - 0x7f0 + 0x7b8 + 8 ≤ word.1)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ nextState,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 8 args.origin.machine nextState 0x12188 ∧
      SavedWordReps nextState
        ((args.boundary.stackPointer - 0x7f0 + 0x7b8, values.s5.toNat) :: prior) := by
  apply decodeInputSaveStep seg access stackLower loaded prior words
    0x12184 (args.boundary.stackPointer - 0x7f0) 0x7b8 0xb78 values.s5 0x7b8
    (.Regidx 21#5) 0x23 0x3c 0x51 0x7b
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x21_run premise values.s5
      ((writes.get x21 (by decide)).trans
        (seg.reg x21 values.s5 (by simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · exact priorAbove
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x7b8#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x12188: sd s6, 0x7b0(sp)`. -/
theorem decodeInputSaveS6 {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 8 args.origin.machine cur 0x12188)
    (prior : List (Nat × Nat)) (words : SavedWordReps cur prior)
    (priorAbove : ∀ word ∈ prior,
      args.boundary.stackPointer - 0x7f0 + 0x7b0 + 8 ≤ word.1)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ nextState,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 9 args.origin.machine nextState 0x1218c ∧
      SavedWordReps nextState
        ((args.boundary.stackPointer - 0x7f0 + 0x7b0, values.s6.toNat) :: prior) := by
  apply decodeInputSaveStep seg access stackLower loaded prior words
    0x12188 (args.boundary.stackPointer - 0x7f0) 0x7b0 0xb70 values.s6 0x7b0
    (.Regidx 22#5) 0x23 0x38 0x61 0x7b
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x22_run premise values.s6
      ((writes.get x22 (by decide)).trans
        (seg.reg x22 values.s6 (by simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · exact priorAbove
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x7b0#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x1218c: sd s7, 0x7a8(sp)`. -/
theorem decodeInputSaveS7 {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 9 args.origin.machine cur 0x1218c)
    (prior : List (Nat × Nat)) (words : SavedWordReps cur prior)
    (priorAbove : ∀ word ∈ prior,
      args.boundary.stackPointer - 0x7f0 + 0x7a8 + 8 ≤ word.1)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ nextState,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 10 args.origin.machine nextState 0x12190 ∧
      SavedWordReps nextState
        ((args.boundary.stackPointer - 0x7f0 + 0x7a8, values.s7.toNat) :: prior) := by
  apply decodeInputSaveStep seg access stackLower loaded prior words
    0x1218c (args.boundary.stackPointer - 0x7f0) 0x7a8 0xb68 values.s7 0x7a8
    (.Regidx 23#5) 0x23 0x34 0x71 0x7b
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x23_run premise values.s7
      ((writes.get x23 (by decide)).trans
        (seg.reg x23 values.s7 (by simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · exact priorAbove
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x7a8#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x12190: sd s8, 0x7a0(sp)`. -/
theorem decodeInputSaveS8 {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 10 args.origin.machine cur 0x12190)
    (prior : List (Nat × Nat)) (words : SavedWordReps cur prior)
    (priorAbove : ∀ word ∈ prior,
      args.boundary.stackPointer - 0x7f0 + 0x7a0 + 8 ≤ word.1)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ nextState,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 11 args.origin.machine nextState 0x12194 ∧
      SavedWordReps nextState
        ((args.boundary.stackPointer - 0x7f0 + 0x7a0, values.s8.toNat) :: prior) := by
  apply decodeInputSaveStep seg access stackLower loaded prior words
    0x12190 (args.boundary.stackPointer - 0x7f0) 0x7a0 0xb60 values.s8 0x7a0
    (.Regidx 24#5) 0x23 0x30 0x81 0x7b
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x24_run premise values.s8
      ((writes.get x24 (by decide)).trans
        (seg.reg x24 values.s8 (by simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · exact priorAbove
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x7a0#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x12194: sd s9, 0x798(sp)`. -/
theorem decodeInputSaveS9 {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 11 args.origin.machine cur 0x12194)
    (prior : List (Nat × Nat)) (words : SavedWordReps cur prior)
    (priorAbove : ∀ word ∈ prior,
      args.boundary.stackPointer - 0x7f0 + 0x798 + 8 ≤ word.1)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ nextState,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 12 args.origin.machine nextState 0x12198 ∧
      SavedWordReps nextState
        ((args.boundary.stackPointer - 0x7f0 + 0x798, values.s9.toNat) :: prior) := by
  apply decodeInputSaveStep seg access stackLower loaded prior words
    0x12194 (args.boundary.stackPointer - 0x7f0) 0x798 0xb58 values.s9 0x798
    (.Regidx 25#5) 0x23 0x3c 0x91 0x79
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x25_run premise values.s9
      ((writes.get x25 (by decide)).trans
        (seg.reg x25 values.s9 (by simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · exact priorAbove
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x798#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x12198: sd s10, 0x790(sp)`. -/
theorem decodeInputSaveS10 {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 12 args.origin.machine cur 0x12198)
    (prior : List (Nat × Nat)) (words : SavedWordReps cur prior)
    (priorAbove : ∀ word ∈ prior,
      args.boundary.stackPointer - 0x7f0 + 0x790 + 8 ≤ word.1)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ nextState,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 13 args.origin.machine nextState 0x1219c ∧
      SavedWordReps nextState
        ((args.boundary.stackPointer - 0x7f0 + 0x790, values.s10.toNat) :: prior) := by
  apply decodeInputSaveStep seg access stackLower loaded prior words
    0x12198 (args.boundary.stackPointer - 0x7f0) 0x790 0xb50 values.s10 0x790
    (.Regidx 26#5) 0x23 0x38 0xa1 0x79
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x26_run premise values.s10
      ((writes.get x26 (by decide)).trans
        (seg.reg x26 values.s10 (by simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · exact priorAbove
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x790#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Production `0x1219c: sd s11, 0x788(sp)`. -/
theorem decodeInputSaveS11 {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {cur : State}
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 13 args.origin.machine cur 0x1219c)
    (prior : List (Nat × Nat)) (words : SavedWordReps cur prior)
    (priorAbove : ∀ word ∈ prior,
      args.boundary.stackPointer - 0x7f0 + 0x788 + 8 ≤ word.1)
    (access : DecodeBoundaryMachineAccess args.boundary args.origin.machine)
    (stackLower : 0xbb0 ≤ args.boundary.stackPointer)
    (stackAligned : args.boundary.stackPointer % 16 = 0)
    (stackUpper : args.boundary.stackPointer + 0x380 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully args.origin.machine.mem) :
    ∃ nextState,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 14 args.origin.machine nextState 0x121a0 ∧
      SavedWordReps nextState
        ((args.boundary.stackPointer - 0x7f0 + 0x788, values.s11.toNat) :: prior) := by
  apply decodeInputSaveStep seg access stackLower loaded prior words
    0x1219c (args.boundary.stackPointer - 0x7f0) 0x788 0xb48 values.s11 0x788
    (.Regidx 27#5) 0x23 0x34 0xb1 0x79
  · exact seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)
  · intro premise writes
    exact rX_x27_run premise values.s11
      ((writes.get x27 (by decide)).trans
        (seg.reg x27 values.s11 (by simp [decodeInputIncomingRegs])))
  · omega
  · native_decide
  · exact priorAbove
  · rfl
  · exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩
  · unfold DecodeInlineInitialExecutionPc pcInRanges
    native_decide
  · intro configured
    obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
      decodeInputStoreDecodeReads configured
    decode_run
  · change BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0) + 0x788#64 = _
    rw [← BitVec.ofNat_add]
  · omega
  · omega
  · exact of_decide_eq_true rfl
  · native_decide
  · rfl
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide


/-- The exact initial stack-allocation and thirteen-save prefix, ending before the final stack
adjustment. All saved words are retained by one fixed-region `Seg`. -/
theorem decodeInputSavePrefix (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (entry : DecodeBoundaryEntry args.boundary args.origin)
    (saved : DecodeCalleeSavedAtRegisters values args.origin) :
    ∃ state,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
          decodeInputIncomingRegs args values)
        fromStep 14 args.origin.machine state 0x121a0 ∧
      DecodeCalleeSavedAtStack (args.boundary.stackPointer - 0xbb0)
        args.boundary.returnAddress values { args.origin with machine := state } := by
  obtain ⟨s1, seg1⟩ := decodeInputAllocateSaveArea fromStep args values entry saved
  rcases entry with ⟨_stdin, _returnPc, _allocator, _atPc, loaded, stackLower, stackAligned,
    stackUpper, _inputFits, _separated, _stackRead, _link, _result, _allocatorReg, _inputReg,
    _sizeReg, _inputAddress, _inputSize, _allocatorState, _allocatorVtable, _savedReturn,
    _input, access, _entrySaved⟩
  obtain ⟨s2, seg2, words2⟩ :=
    decodeInputSaveRa seg1 access stackLower stackAligned stackUpper loaded
  have above2 : SavedWordsAtOrAbove
      (args.boundary.stackPointer - 0x7f0 + 0x7e8)
      [(args.boundary.stackPointer - 0x7f0 + 0x7e8,
        (BitVec.ofNat 64 args.boundary.returnAddress).toNat)] := by
    exact savedWordsAtOrAbove_cons (by
      intro word member
      simp at member)
  obtain ⟨s3, seg3, words3⟩ :=
    decodeInputSaveS0 seg2 words2 access stackLower stackAligned stackUpper loaded
  have above3 : SavedWordsAtOrAbove
      (args.boundary.stackPointer - 0x7f0 + 0x7e0)
      [(args.boundary.stackPointer - 0x7f0 + 0x7e0, values.s0.toNat),
       (args.boundary.stackPointer - 0x7f0 + 0x7e8,
        (BitVec.ofNat 64 args.boundary.returnAddress).toNat)] :=
    savedWordsAtOrAbove_cons (by
      intro word member
      exact Nat.le_trans (by omega) (above2 word member))
  obtain ⟨s4, seg4, words4⟩ :=
    decodeInputSaveS1 seg3 _ words3 (by
      intro word member
      exact Nat.le_trans (by omega) (above3 word member))
      access stackLower stackAligned stackUpper loaded
  have above4 := savedWordsAtOrAbove_cons
    (address := args.boundary.stackPointer - 0x7f0 + 0x7d8)
    (value := values.s1.toNat) (by
      intro word member
      exact Nat.le_trans (by omega) (above3 word member))
  obtain ⟨s5, seg5, words5⟩ :=
    decodeInputSaveS2 seg4 _ words4 (by
      intro word member
      exact Nat.le_trans (by omega) (above4 word member))
      access stackLower stackAligned stackUpper loaded
  have above5 := savedWordsAtOrAbove_cons
    (address := args.boundary.stackPointer - 0x7f0 + 0x7d0)
    (value := values.s2.toNat) (by
      intro word member
      exact Nat.le_trans (by omega) (above4 word member))
  obtain ⟨s6, seg6, words6⟩ :=
    decodeInputSaveS3 seg5 _ words5 (by
      intro word member
      exact Nat.le_trans (by omega) (above5 word member))
      access stackLower stackAligned stackUpper loaded
  have above6 := savedWordsAtOrAbove_cons
    (address := args.boundary.stackPointer - 0x7f0 + 0x7c8)
    (value := values.s3.toNat) (by
      intro word member
      exact Nat.le_trans (by omega) (above5 word member))
  obtain ⟨s7, seg7, words7⟩ :=
    decodeInputSaveS4 seg6 _ words6 (by
      intro word member
      exact Nat.le_trans (by omega) (above6 word member))
      access stackLower stackAligned stackUpper loaded
  have above7 := savedWordsAtOrAbove_cons
    (address := args.boundary.stackPointer - 0x7f0 + 0x7c0)
    (value := values.s4.toNat) (by
      intro word member
      exact Nat.le_trans (by omega) (above6 word member))
  obtain ⟨s8, seg8, words8⟩ :=
    decodeInputSaveS5 seg7 _ words7 (by
      intro word member
      exact Nat.le_trans (by omega) (above7 word member))
      access stackLower stackAligned stackUpper loaded
  have above8 := savedWordsAtOrAbove_cons
    (address := args.boundary.stackPointer - 0x7f0 + 0x7b8)
    (value := values.s5.toNat) (by
      intro word member
      exact Nat.le_trans (by omega) (above7 word member))
  obtain ⟨s9, seg9, words9⟩ :=
    decodeInputSaveS6 seg8 _ words8 (by
      intro word member
      exact Nat.le_trans (by omega) (above8 word member))
      access stackLower stackAligned stackUpper loaded
  have above9 := savedWordsAtOrAbove_cons
    (address := args.boundary.stackPointer - 0x7f0 + 0x7b0)
    (value := values.s6.toNat) (by
      intro word member
      exact Nat.le_trans (by omega) (above8 word member))
  obtain ⟨s10, seg10, words10⟩ :=
    decodeInputSaveS7 seg9 _ words9 (by
      intro word member
      exact Nat.le_trans (by omega) (above9 word member))
      access stackLower stackAligned stackUpper loaded
  have above10 := savedWordsAtOrAbove_cons
    (address := args.boundary.stackPointer - 0x7f0 + 0x7a8)
    (value := values.s7.toNat) (by
      intro word member
      exact Nat.le_trans (by omega) (above9 word member))
  obtain ⟨s11, seg11, words11⟩ :=
    decodeInputSaveS8 seg10 _ words10 (by
      intro word member
      exact Nat.le_trans (by omega) (above10 word member))
      access stackLower stackAligned stackUpper loaded
  have above11 := savedWordsAtOrAbove_cons
    (address := args.boundary.stackPointer - 0x7f0 + 0x7a0)
    (value := values.s8.toNat) (by
      intro word member
      exact Nat.le_trans (by omega) (above10 word member))
  obtain ⟨s12, seg12, words12⟩ :=
    decodeInputSaveS9 seg11 _ words11 (by
      intro word member
      exact Nat.le_trans (by omega) (above11 word member))
      access stackLower stackAligned stackUpper loaded
  have above12 := savedWordsAtOrAbove_cons
    (address := args.boundary.stackPointer - 0x7f0 + 0x798)
    (value := values.s9.toNat) (by
      intro word member
      exact Nat.le_trans (by omega) (above11 word member))
  obtain ⟨s13, seg13, words13⟩ :=
    decodeInputSaveS10 seg12 _ words12 (by
      intro word member
      exact Nat.le_trans (by omega) (above12 word member))
      access stackLower stackAligned stackUpper loaded
  have above13 := savedWordsAtOrAbove_cons
    (address := args.boundary.stackPointer - 0x7f0 + 0x790)
    (value := values.s10.toNat) (by
      intro word member
      exact Nat.le_trans (by omega) (above12 word member))
  obtain ⟨s14, seg14, words14⟩ :=
    decodeInputSaveS11 seg13 _ words13 (by
      intro word member
      exact Nat.le_trans (by omega) (above13 word member))
      access stackLower stackAligned stackUpper loaded
  have above14 := savedWordsAtOrAbove_cons
    (address := args.boundary.stackPointer - 0x7f0 + 0x788)
    (value := values.s11.toNat) (by
      intro word member
      exact Nat.le_trans (by omega) (above13 word member))
  have returnEq : args.boundary.returnAddress = 0x14cfc := by
    simpa [Elflings.decodeInputExitPcs] using _returnPc
  have ra := words14
    (args.boundary.stackPointer - 0x7f0 + 0x7e8,
      (BitVec.ofNat 64 args.boundary.returnAddress).toNat) (by simp)
  have s0 := words14
    (args.boundary.stackPointer - 0x7f0 + 0x7e0, values.s0.toNat) (by simp)
  have s1 := words14
    (args.boundary.stackPointer - 0x7f0 + 0x7d8, values.s1.toNat) (by simp)
  have s2 := words14
    (args.boundary.stackPointer - 0x7f0 + 0x7d0, values.s2.toNat) (by simp)
  have s3 := words14
    (args.boundary.stackPointer - 0x7f0 + 0x7c8, values.s3.toNat) (by simp)
  have s4 := words14
    (args.boundary.stackPointer - 0x7f0 + 0x7c0, values.s4.toNat) (by simp)
  have s5 := words14
    (args.boundary.stackPointer - 0x7f0 + 0x7b8, values.s5.toNat) (by simp)
  have s6 := words14
    (args.boundary.stackPointer - 0x7f0 + 0x7b0, values.s6.toNat) (by simp)
  have s7 := words14
    (args.boundary.stackPointer - 0x7f0 + 0x7a8, values.s7.toNat) (by simp)
  have s8 := words14
    (args.boundary.stackPointer - 0x7f0 + 0x7a0, values.s8.toNat) (by simp)
  have s9 := words14
    (args.boundary.stackPointer - 0x7f0 + 0x798, values.s9.toNat) (by simp)
  have s10 := words14
    (args.boundary.stackPointer - 0x7f0 + 0x790, values.s10.toNat) (by simp)
  have s11 := words14
    (args.boundary.stackPointer - 0x7f0 + 0x788, values.s11.toNat) (by simp)
  refine ⟨s14, seg14, ?_⟩
  unfold DecodeCalleeSavedAtStack
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xba8)
      args.boundary.returnAddress
    have returnFits : args.boundary.returnAddress < 2 ^ 64 := by omega
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xba8 =
        args.boundary.stackPointer - 0x7f0 + 0x7e8 by omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt returnFits] using ra
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xba0) values.s0.toNat
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xba0 =
      args.boundary.stackPointer - 0x7f0 + 0x7e0 by omega] using s0
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xb98) values.s1.toNat
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xb98 =
      args.boundary.stackPointer - 0x7f0 + 0x7d8 by omega] using s1
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xb90) values.s2.toNat
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xb90 =
      args.boundary.stackPointer - 0x7f0 + 0x7d0 by omega] using s2
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xb88) values.s3.toNat
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xb88 =
      args.boundary.stackPointer - 0x7f0 + 0x7c8 by omega] using s3
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xb80) values.s4.toNat
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xb80 =
      args.boundary.stackPointer - 0x7f0 + 0x7c0 by omega] using s4
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xb78) values.s5.toNat
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xb78 =
      args.boundary.stackPointer - 0x7f0 + 0x7b8 by omega] using s5
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xb70) values.s6.toNat
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xb70 =
      args.boundary.stackPointer - 0x7f0 + 0x7b0 by omega] using s6
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xb68) values.s7.toNat
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xb68 =
      args.boundary.stackPointer - 0x7f0 + 0x7a8 by omega] using s7
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xb60) values.s8.toNat
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xb60 =
      args.boundary.stackPointer - 0x7f0 + 0x7a0 by omega] using s8
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xb58) values.s9.toNat
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xb58 =
      args.boundary.stackPointer - 0x7f0 + 0x798 by omega] using s9
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xb50) values.s10.toNat
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xb50 =
      args.boundary.stackPointer - 0x7f0 + 0x790 by omega] using s10
  · change UIntRep 8 s14.mem (args.boundary.stackPointer - 0xbb0 + 0xb48) values.s11.toNat
    simpa only [show args.boundary.stackPointer - 0xbb0 + 0xb48 =
      args.boundary.stackPointer - 0x7f0 + 0x788 by omega] using s11

/-- Finish the parent-owned prologue at the exact inline `ssz.decode` entry. -/
theorem decodeInputFinishPrologue {fromStep : Nat} {args : DecodeInlineArgs}
    {values : DecodeCalleeSavedValues} {state : State}
    (entry : DecodeBoundaryEntry args.boundary args.origin)
    (seg : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites (decodeInputFrameMemory args)
      (⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)⟩ ::
        decodeInputIncomingRegs args values)
      fromStep 14 args.origin.machine state 0x121a0)
    (saved : DecodeCalleeSavedAtStack (args.boundary.stackPointer - 0xbb0)
      args.boundary.returnAddress values { args.origin with machine := state }) :
    ∃ final,
      Seg decodeInputParentPc DecodeInlineInitialExecutionPc (fun _ _ _ _ _ => False)
        decodeInputParentWrites (decodeInputFrameMemory args)
        [⟨x8, BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)⟩,
         ⟨x18, BitVec.ofNat 64 args.boundary.inputAddress⟩,
         ⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)⟩]
        fromStep 17 args.origin.machine final 0x121ac ∧
      DecodeCalleeSavedAtStack (args.boundary.stackPointer - 0xbb0)
        args.boundary.returnAddress values { args.origin with machine := final } := by
  rcases entry with ⟨_stdin, _returnPc, _allocator, _atPc, loaded, stackLower, _stackAligned,
    stackUpper, _inputFits, _separated, _stackRead, _link, resultReg, _allocatorReg, inputReg,
    _sizeReg, _inputAddress, _inputSize, _allocatorState, _allocatorVtable, _savedReturn,
    _input, access, _entrySaved⟩
  have seg0 := seg.forget (kv' := []) (by simp)
  have configured0 := access.configured.mono
    (seg0.agree instructionPreserved_disjoint_decodeInputParentWrites) seg0.retired
  have code0 := decodeInputCodeOfSeg access loaded seg0 rfl stackLower
  have decode0 : Runs
      (ext_decode (fetchWord (0x13 : BitVec 8) (0x01 : BitVec 8) (0x01 : BitVec 8)
        (0xc4 : BitVec 8)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0xc40, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured0.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using writeReg_read_unchanged state
            minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured0.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using writeReg_read_unchanged state
            minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    decode_run
  obtain ⟨retired0, run0⟩ := decodeInputAddiX2Step (fromStep + 14) 0x121a0 state 0xc40
    (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0))
    (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)) 0x13 0x01 0x01 0xc4
    configured0 seg0.atPc
    (seg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0x7f0)) (by simp)) code0
    (decodeInputFinalStackResult args.boundary.stackPointer stackLower stackUpper) decode0
    (base := by rfl)
  obtain ⟨retired1, state1, state1Eq, seg1⟩ := seg0.stepWitness
    (by exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩)
    (by unfold DecodeInlineInitialExecutionPc pcInRanges; native_decide) x2
    (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)) 0x121a4 ⟨retired0, run0⟩
    (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside])
  have saved1 : DecodeCalleeSavedAtStack (args.boundary.stackPointer - 0xbb0)
      args.boundary.returnAddress values { args.origin with machine := state1 } := by
    rw [state1Eq]
    simpa only [afterRegisterWrite_mem] using saved
  have configured1 := access.configured.mono
    (seg1.agree instructionPreserved_disjoint_decodeInputParentWrites) seg1.retired
  have code1 := decodeInputCodeOfSeg access loaded seg1 rfl stackLower
  have inputAt1 : state1.regs.get? x12 = some (BitVec.ofNat 64 args.boundary.inputAddress) :=
    (seg1.get x12 (by simp [decodeInputParentWrites])).trans inputReg
  obtain ⟨retired2, run2⟩ := decodeInputBindS2Step (fromStep + 15) state1
    (BitVec.ofNat 64 args.boundary.inputAddress) configured1 seg1.atPc inputAt1 code1
  obtain ⟨retired2', state2, state2Eq, seg2⟩ := seg1.stepWitness
    (by exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩)
    (by unfold DecodeInlineInitialExecutionPc pcInRanges; native_decide) x18
    (BitVec.ofNat 64 args.boundary.inputAddress) 0x121a8 ⟨retired2, run2⟩
    (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping)
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have saved2 : DecodeCalleeSavedAtStack (args.boundary.stackPointer - 0xbb0)
      args.boundary.returnAddress values { args.origin with machine := state2 } := by
    rw [state2Eq]
    simpa only [afterRegisterWrite_mem] using saved1
  have configured2 := access.configured.mono
    (seg2.agree instructionPreserved_disjoint_decodeInputParentWrites) seg2.retired
  have code2 := decodeInputCodeOfSeg access loaded seg2 rfl stackLower
  have resultAt2 : state2.regs.get? x10 =
      some (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)) :=
    (seg2.get x10 (by simp [decodeInputParentWrites])).trans resultReg
  obtain ⟨retired3, run3⟩ := decodeInputBindS0Step (fromStep + 16) state2
    (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)) configured2 seg2.atPc resultAt2 code2
  obtain ⟨retired3', final, finalEq, finalSeg⟩ := seg2.stepWitness
    (by exact ⟨(0x12168, 0x121ac), by native_decide, by native_decide, by native_decide⟩)
    (by unfold DecodeInlineInitialExecutionPc pcInRanges; native_decide) x8
    (BitVec.ofNat 64 (args.boundary.stackPointer + 0x20)) 0x121ac ⟨retired3, run3⟩
    (by native_decide) (fun _ bookkeeping => Or.inl bookkeeping)
    (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  refine ⟨final, finalSeg, ?_⟩
  rw [finalEq]
  simpa only [afterRegisterWrite_mem] using saved2

/-- The complete parent-owned prologue as an endpoint trace and the exact typed child entry. -/
theorem decodeInputInitialHandoff (fromStep : Nat) (args : DecodeInlineArgs)
    (entry : DecodeBoundaryEntry args.boundary args.origin) :
    ∃ state,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.decodeInputExecutionPcRanges)
        fromStep 17 args.origin { args.origin with machine := state } ∧
      DecodeInlineInitialEntry args { args.origin with machine := state } := by
  have entry' := entry
  rcases entry with ⟨stdin, returnPc, allocator, atPc, loaded, stackLower, stackAligned,
    stackUpper, inputFits, separated, stackRead, link, resultReg, allocatorReg, inputReg, sizeReg,
    inputAddressRep, inputSizeRep, allocatorStateRep, allocatorVtableRep, savedReturnRep,
    inputRep, access, entrySaved⟩
  rcases entrySaved with ⟨values, saved⟩
  obtain ⟨state14, seg14, saved14⟩ := decodeInputSavePrefix fromStep args values entry' saved
  obtain ⟨final, finalSeg, finalSaved⟩ := decodeInputFinishPrologue entry' seg14 saved14
  have pointerFinal := inputAddressRep.of_writesOnlyWithin finalSeg.mem (by
    intro index bound inside
    unfold decodeInputFrameMemory byteRange at inside
    omega)
  have sizeFinal := inputSizeRep.of_writesOnlyWithin finalSeg.mem (by
    intro index bound inside
    unfold decodeInputFrameMemory byteRange at inside
    omega)
  have savedReturnFinal := savedReturnRep.of_writesOnlyWithin finalSeg.mem (by
    intro index bound inside
    unfold decodeInputFrameMemory byteRange at inside
    omega)
  have inputFinal : BytesRep final.mem args.boundary.inputAddress args.boundary.input := by
    refine ⟨inputRep.1, ?_⟩
    intro index inBounds
    rw [finalSeg.mem (args.boundary.inputAddress + index) (by
      intro inside
      unfold decodeInputFrameMemory byteRange at inside
      rcases separated with above | below <;> omega)]
    exact inputRep.2 index inBounds
  have codeFinal := decodeInputCodeOfSeg access loaded finalSeg rfl stackLower
  have configuredFinal := access.configured.mono
    (finalSeg.agree instructionPreserved_disjoint_decodeInputParentWrites) finalSeg.retired
  have endTrace : ScopedTrace decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) (fromStep + 17) 0 final final :=
    .exitAt (fromStep + 17) final 0x121ac finalSeg.atPc (by
      unfold DecodeInlineInitialExecutionPc pcInRanges
      exact ⟨(0x121ac, 0x14ca8), by simp [Elflings.sszDecodeExecutionPcRanges],
        by native_decide, by native_decide⟩)
  have machineTrace : ScopedTrace decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) fromStep 17 args.origin.machine final := by
    simpa using finalSeg.confined 0 final endTrace
  have endpointTrace := liftDecodeInputParentTrace args.origin machineTrace
  refine ⟨final, endpointTrace, entry', values, saved, ?_, finalSeg.atPc, ?_, ?_, ?_, ?_, ?_⟩
  · refine
      { stackFits := stackLower
        atStack := finalSeg.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)) (by simp)
        saved := finalSaved
        inputAddress := pointerFinal
        inputSize := sizeFinal
        savedReturn := savedReturnFinal
        input := inputFinal
        code := codeFinal
        configured := configuredFinal
        stdin := rfl
        stdinCursor := rfl
        stdout := rfl
        exitCode := rfl }
  · exact (finalSeg.get x1 (by simp [decodeInputParentWrites])).trans link
  · exact (finalSeg.get x10 (by simp [decodeInputParentWrites])).trans resultReg
  · exact (finalSeg.get x11 (by simp [decodeInputParentWrites])).trans allocatorReg
  · exact (finalSeg.get x12 (by simp [decodeInputParentWrites])).trans inputReg
  · exact (finalSeg.get x13 (by simp [decodeInputParentWrites])).trans sizeReg

/-- The two parent-owned error instructions connect the initial child exit to its resume entry. -/
theorem decodeInputErrorHandoff (fromStep : Nat) (args : DecodeInlineArgs)
    (values : DecodeCalleeSavedValues) (status : BitVec 64) (before : EndpointState)
    (savedAtOrigin : DecodeCalleeSavedAtRegisters values args.origin)
    (frame : DecodeInlineFrame args values before)
    (atPc : before.machine.regs.get? PC = some 0x14ca8)
    (statusAt : before.machine.regs.get? x10 = some status) :
    ∃ after,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.decodeInputExecutionPcRanges)
        fromStep 2 before after ∧
      DecodeInlineResumeEntry
        { inline := args, saved := values, status := status } after := by
  let seg0 := Seg.nil decodeInputParentPc DecodeInlineInitialExecutionPc
    (fun _ _ _ _ _ => False) decodeInputParentWrites noMemory fromStep
    frame.configured.retiredCounter atPc
  have seg0Regs : RegsHold before.machine
      [⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)⟩, ⟨x10, status⟩] :=
    .cons _ _ frame.atStack (.cons _ _ statusAt (.nil _))
  have seg0' : Seg decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) decodeInputParentWrites noMemory
      [⟨x2, BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)⟩, ⟨x10, status⟩]
      fromStep 0 before.machine before.machine 0x14ca8 := { seg0 with regs := seg0Regs }
  obtain ⟨retired0, run0⟩ := decodeInputBindErrorS6Step fromStep before.machine status
    frame.configured atPc statusAt frame.code
  obtain ⟨middle, seg1⟩ := seg0'.step
    (by unfold decodeInputParentPc pcInRanges; native_decide)
    (by unfold DecodeInlineInitialExecutionPc pcInRanges; native_decide)
    x22 status 0x14cac ⟨retired0, run0⟩ (by decide)
    (fun _ bookkeeping => Or.inl bookkeeping) (by simp [decodeInputParentWrites])
    (by decide) (by decide) (by exact of_decide_eq_true rfl)
  have configured1 := frame.configured.mono
    (seg1.agree instructionPreserved_disjoint_decodeInputParentWrites) seg1.retired
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully middle.mem := by
    rw [seg1.memEq noMemory_empty]
    exact frame.code
  have decode1 : Runs (ext_decode (fetchWord 0x6f#8 0xd0#8 0x0f#8 0xe6#8))
      (tryStepControlFlowAfterIncrement middle) (tryStepControlFlowAfterIncrement middle)
      (.JAL (0x1fd660#21, zreg)) := by
    obtain ⟨seccfgBits, seccfgRead, _⟩ := configured1.seccfgPresent
    have privilegeAfter : (tryStepControlFlowAfterIncrement middle).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = middle.regs.get? cur_privilege := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged middle minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured1.normal.2.1
    have seccfgAfter : (tryStepControlFlowAfterIncrement middle).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = middle.regs.get? mseccfg := by
          simpa [tryStepControlFlowAfterIncrement] using
            writeReg_read_unchanged middle minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    decode_run
  obtain ⟨retired1, run1⟩ := configuredJStep (fromStep + 1) 0x14cac 0x1230c middle
    0x1fd660 0x6f 0xd0 0x0f 0xe6 configured1 seg1.atPc code1 decode1
    (by native_decide) (by native_decide) (by native_decide) (base := by rfl)
  obtain ⟨final, seg2⟩ := seg1.stepJump 0x1230c
    (by unfold decodeInputParentPc pcInRanges; native_decide)
    (by unfold DecodeInlineInitialExecutionPc pcInRanges; native_decide)
    ⟨retired1, run1⟩ (fun _ bookkeeping => Or.inl bookkeeping)
    (by exact of_decide_eq_true rfl)
  have endTrace : ScopedTrace decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) (fromStep + 2) 0 final final :=
    .exitAt (fromStep + 2) final 0x1230c seg2.atPc (by
      unfold DecodeInlineInitialExecutionPc pcInRanges
      exact ⟨(0x121ac, 0x14ca8), by simp [Elflings.sszDecodeExecutionPcRanges],
        by native_decide, by native_decide⟩)
  have machineTrace : ScopedTrace decodeInputParentPc DecodeInlineInitialExecutionPc
      (fun _ _ _ _ _ => False) fromStep 2 before.machine final := by
    simpa using seg2.confined 0 final endTrace
  let after : EndpointState := { before with machine := final }
  refine ⟨after, liftDecodeInputParentTrace before machineTrace, savedAtOrigin, ?_, seg2.atPc, ?_⟩
  · have memEq := seg2.memEq noMemory_empty
    refine
      { stackFits := frame.stackFits
        atStack := seg2.reg x2 (BitVec.ofNat 64 (args.boundary.stackPointer - 0xbb0)) (by simp)
        saved := ?_
        inputAddress := ?_
        inputSize := ?_
        savedReturn := ?_
        input := ?_
        code := ?_
        configured := frame.configured.mono
          (seg2.agree instructionPreserved_disjoint_decodeInputParentWrites) seg2.retired
        stdin := frame.stdin
        stdinCursor := frame.stdinCursor
        stdout := frame.stdout
        exitCode := frame.exitCode }
    · have oldSaved := frame.saved
      unfold DecodeCalleeSavedAtStack at oldSaved ⊢
      simpa only [after, memEq] using oldSaved
    · simpa only [after, memEq] using frame.inputAddress
    · simpa only [after, memEq] using frame.inputSize
    · simpa only [after, memEq] using frame.savedReturn
    · simpa only [after, memEq] using frame.input
    · simpa only [after, memEq] using frame.code
  · exact seg2.reg x22 status (by simp)

private theorem initialRegion_in_decodeRegion {pc : BitVec 64}
    (inside : DecodeInlineInitialExecutionPc pc) : DecodeExecutionPc pc := by
  unfold DecodeInlineInitialExecutionPc at inside
  unfold DecodeExecutionPc
  unfold pcInRanges at inside ⊢
  rcases inside with ⟨range, member, lower, upper⟩
  simp [Elflings.sszDecodeExecutionPcRanges] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact ⟨(0x101d4, 0x14cb0), by simp [Elflings.decodeInputExecutionPcRanges],
      by omega, by omega⟩
  · exact ⟨(0x101d4, 0x14cb0), by simp [Elflings.decodeInputExecutionPcRanges],
      by omega, by omega⟩
  · exact ⟨(0x15d38, 0x15d40), by simp [Elflings.decodeInputExecutionPcRanges], lower, upper⟩
  · exact ⟨(0x15ffc, 0x161c0), by simp [Elflings.decodeInputExecutionPcRanges], lower, upper⟩
  · exact ⟨(0x161d4, 0x171f8), by simp [Elflings.decodeInputExecutionPcRanges], lower, upper⟩

/-- Resolve the Level-1 `decodeInput` contract from the exact Level-2 initial and resume contracts. -/
theorem decodeInstanceContract_of_level2
    (hLevel2 : SszDecodeLevel2InstanceContract) : DecodeInstanceContractModuloKnownBugs := by
  obtain ⟨initialBound, initialImpl⟩ := hLevel2.initial
  obtain ⟨resumeBound, resumeImpl⟩ := hLevel2.resume
  refine ⟨fun inputSize => 19 + initialBound inputSize + resumeBound inputSize, ?_⟩
  intro boundary fromStep origin boundaryEntry
  let inline : DecodeInlineArgs := { boundary, origin }
  obtain ⟨childMachine, prefixTrace, childEntry⟩ :=
    decodeInputInitialHandoff fromStep inline boundaryEntry
  let childBefore : EndpointState := { origin with machine := childMachine }
  obtain ⟨initialCount, initialAfter, initialOutcome, initialPositive, initialBounded,
    initialTrace, initialExitPc, initialMeaning, initialExit⟩ :=
    initialImpl inline (fromStep + 17) childBefore childEntry
  have initialTrace' := initialTrace.weaken
    (fun pc inside => initialRegion_in_decodeRegion inside)
  have prefixAndInitial : ConfinedTrace EndpointStep EndpointPc DecodeExecutionPc fromStep
      (17 + initialCount) origin initialAfter := prefixTrace.append initialTrace'
  rcases initialOutcome with result | status
  · refine ⟨17 + initialCount, initialAfter, result, by omega, ?_, prefixAndInitial, ?_,
      initialMeaning, initialExit⟩
    · change 17 + initialCount ≤ 19 + initialBound boundary.input.size +
        resumeBound boundary.input.size
      change initialCount ≤ initialBound boundary.input.size at initialBounded
      omega
    · have returnEq : boundary.returnAddress = 0x14cfc := by
        have member := boundaryEntry.2.1
        simpa [Elflings.decodeInputExitPcs] using member
      exact ⟨0x14cfc, by
        change DecodeBoundaryExit boundary result origin initialAfter at initialExit
        have pcReturn := initialExit.1
        rw [returnEq] at pcReturn
        exact pcReturn, by
        unfold DecodeExitPc pcInList
        native_decide⟩
  · rcases initialExit with ⟨values, savedAtOrigin, frame, atError, statusAt⟩
    obtain ⟨resumeBefore, errorTrace, resumeEntry⟩ :=
      decodeInputErrorHandoff (fromStep + 17 + initialCount) inline values status initialAfter
        savedAtOrigin frame atError statusAt
    obtain ⟨resumeCount, final, unit, resumePositive, resumeBounded, resumeTrace,
      resumeExitPc, resumeMeaning, resumeExit⟩ :=
      resumeImpl { inline, saved := values, status := status }
        (fromStep + 17 + initialCount + 2) resumeBefore resumeEntry
    have errorTrace' : ConfinedTrace EndpointStep EndpointPc DecodeExecutionPc
        (fromStep + 17 + initialCount) 2 initialAfter resumeBefore := by
      simpa [DecodeExecutionPc] using errorTrace
    have resumeTrace' := resumeTrace.weaken
      (fun pc inside => initialRegion_in_decodeRegion inside)
    have withError := prefixAndInitial.append (by
      simpa [Nat.add_assoc] using errorTrace')
    have fullTrace : ConfinedTrace EndpointStep EndpointPc DecodeExecutionPc fromStep
        ((17 + initialCount + 2) + resumeCount) origin final := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        withError.append (by simpa [Nat.add_assoc] using resumeTrace')
    refine ⟨(17 + initialCount + 2) + resumeCount, final, .failure, by omega, ?_,
      fullTrace, ?_, ?_, resumeExit⟩
    · change 17 + initialCount + 2 + resumeCount ≤
        19 + initialBound boundary.input.size + resumeBound boundary.input.size
      change initialCount ≤ initialBound boundary.input.size at initialBounded
      change resumeCount ≤ resumeBound boundary.input.size at resumeBounded
      omega
    · rcases resumeExitPc with ⟨pc, atPc, exit⟩
      exact ⟨pc, atPc, by
        unfold DecodeInlineResumeExitPc at exit
        have pcEq : pc = (0x14cfc : BitVec 64) := by
          apply BitVec.eq_of_toNat_eq
          simpa using exit
        rw [pcEq]
        unfold DecodeExitPc pcInList
        native_decide⟩
    · exact resumeMeaning.2

end BinaryFv.Zesu.MachineExecution
