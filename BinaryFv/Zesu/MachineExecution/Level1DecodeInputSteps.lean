import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.RiscV.Instruction.DecodeTactic
import BinaryFv.RiscV.Elfling.Seg

/-!
# Parent-owned `decodeInput` steps

These instruction-class adapters cover the optimized `decodeInput` instructions outside the
selected inline `ssz.decode` child. The concrete composition remains in the Level-2 refinement
edge, where the child contract is available.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.Binary BinaryFv.RiscV
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
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
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

end BinaryFv.Zesu.MachineExecution
