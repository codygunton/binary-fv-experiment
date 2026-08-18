import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.RiscV.Instruction.DecodeTactic
import BinaryFv.RiscV.Instruction.Execute.Load
import BinaryFv.RiscV.Elfling.Seg

/-!
# Closed Level 2 runtime leaves

The bare-metal Level 2 inventory contains no host-runtime child: `read_input`, `write_output`, and
`zkvm_exit` are genuine assembly functions outside the inlined decoder/encoder children selected at
this level. This module remains as the stable import point for future unconditional leaf proofs.
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
  constructor
  · unfold is_aligned_vaddr
    simp only
    change ((((BitVec.ofNat 64 address).toNat : Int).tmod 8) == 0) = true
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
    simpa [tmodEight]
  · unfold is_aligned_paddr
    simp only
    change ((((BitVec.ofNat 64 address).toNat : Int).tmod 8) == 0) = true
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
    simpa [tmodEight]

private theorem configuredAuipcX5Step (stepNo pc : Nat) (state : State)
    (immediate : BitVec 20) (result : BitVec 64)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (resultEq : result = BitVec.ofNat 64 pc + sign_extend (m := 64) (immediate ++ 0x000#12))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (immediate, .Regidx 5#5, .AUIPC)))
    (pcFits : pc < 2 ^ 64) (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := by native_decide)
    (pcAligned : pc % 4 = 0 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x5 result) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have pcRead : Runs (readReg PC) premise premise (BitVec.ofNat 64 pc) := by
    apply readReg_run
    simp [premise, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (immediate, .Regidx 5#5, .AUIPC))) premise
      { premise with regs := premise.regs.insert x5 result } (.Retire_Success ()) := by
    change Runs (execute_UTYPE immediate (.Regidx 5#5) .AUIPC) _ _ _
    rw [resultEq]
    exact execute_UTYPE_auipc_run premise _ immediate (.Regidx 5#5)
      (BitVec.ofNat 64 pc) pcRead (wX_x5_run premise _)
  exact configuredRegisterWriteStep stepNo pc state x5 result
    (.UTYPE (immediate, .Regidx 5#5, .AUIPC)) byte0 byte1 byte2 byte3 configured atPc loaded
    decode execute (pcFits := pcFits) (base := base) (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3) (pcAligned := pcAligned)

private theorem configuredAddiX5Step (stepNo pc : Nat) (state : State)
    (immediate : BitVec 12) (source result : BitVec 64)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (sourceRead : state.regs.get? x5 = some source)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (resultEq : result = iTypeResult .ADDI immediate source)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (immediate, .Regidx 5#5, .Regidx 5#5, .ADDI)))
    (pcFits : pc < 2 ^ 64) (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := by native_decide)
    (pcAligned : pc % 4 = 0 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired x5 result) false := by
  let premise := coreControlFlowNextState
    (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have sourceAtPremise : premise.regs.get? x5 = some source :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x5 (by decide) |>.trans sourceRead
  have execute : Runs (execute (.ITYPE (immediate, .Regidx 5#5, .Regidx 5#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x5 result } (.Retire_Success ()) := by
    change Runs (execute_ITYPE immediate (.Regidx 5#5) (.Regidx 5#5) .ADDI) _ _ _
    rw [resultEq]
    exact execute_ITYPE_run premise _ immediate (.Regidx 5#5) (.Regidx 5#5) .ADDI source
      (rX_x5_run premise source sourceAtPremise) (wX_x5_run premise _)
  exact configuredRegisterWriteStep stepNo pc state x5 result
    (.ITYPE (immediate, .Regidx 5#5, .Regidx 5#5, .ADDI)) byte0 byte1 byte2 byte3
    configured atPc loaded decode execute (pcFits := pcFits) (base := base)
    (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3) (pcAligned := pcAligned)

/-- Production `0x10190: auipc t0, 0x2400a`. -/
theorem writeOutputContextBaseHighStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10190))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x10190 retired x5 0x2401a190) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  exact configuredAuipcX5Step stepNo 0x10190 state 0x2400a 0x2401a190
    0x97 0xa2 0x00 0x24 configured atPc loaded (by native_decide) (by decode_run)
    (by native_decide) (by rfl)

/-- Production `0x10194: addi t0, t0, -216`. -/
theorem writeOutputContextBaseLowStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10194))
    (sourceRead : state.regs.get? x5 = some (BitVec.ofNat 64 0x2401a190))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x10194 retired x5
        (BitVec.ofNat 64 Elflings.ioContextAddress)) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  exact configuredAddiX5Step stepNo 0x10194 state 0xf28 0x2401a190
    (BitVec.ofNat 64 Elflings.ioContextAddress) 0x93 0x82 0x82 0xf2 configured atPc sourceRead loaded
    (by native_decide) (by decode_run) (by native_decide) (by rfl)

private theorem writeOutputStoreStep (stepNo pc offset : Nat) (state : State)
    (source : BitVec 64) (sourceIndex : regidx) (byte1 byte2 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (contextRead : state.regs.get? x5 = some (BitVec.ofNat 64 Elflings.ioContextAddress))
    (sourceRun : ∀ premise,
      WritesOnlyRegs stepBookkeeping state premise →
      Runs (rX_bits sourceIndex) premise premise source)
    (pma : StorePmaAllows state (BitVec.ofNat 64 (Elflings.ioContextAddress + offset)) 8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 Elflings.ioContextAddress +
      sign_extend (m := 64) (BitVec.ofNat 12 offset) =
      BitVec.ofNat 64 (Elflings.ioContextAddress + offset))
    (aligned : is_aligned_vaddr
        (virtaddr.Virtaddr (BitVec.ofNat 64 (Elflings.ioContextAddress + offset))) 8 = true ∧
      is_aligned_paddr
        (physaddr.Physaddr (BitVec.ofNat 64 (Elflings.ioContextAddress + offset))) 8 = true)
    (notMMIO : StoreMMIOAddressExcluded
      (BitVec.ofNat 64 (Elflings.ioContextAddress + offset)) 8)
    (addressFits : Elflings.ioContextAddress + offset < 2 ^ 64)
    (pcFits : pc < 2 ^ 64)
    (decode : Runs (ext_decode (fetchWord 0x23 (BitVec.ofNat 8 byte1.toNat)
        (BitVec.ofNat 8 byte2.toNat) 0x00))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (BitVec.ofNat 12 offset, sourceIndex, .Regidx 5#5, 8)))
    (read0 : Artifacts.programImage.readFileByte? pc = some 0x23 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some 0x00 := by native_decide)
    (pcAligned : pc % 4 = 0 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc))
          (Elflings.ioContextAddress + offset) source)
        (BitVec.ofNat 64 pc) retired) false := by
  let premise := coreStoreNextState (tryStepStoreAfterIncrement state) (BitVec.ofNat 64 pc)
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise : premise.regs.get? mstatus = some mstatusBits :=
    (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise : premise.regs.get? cur_privilege = some .Machine :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have mseccfgPremise : premise.regs.get? mseccfg = some mseccfgBits :=
    (agree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have contextPremise : premise.regs.get? x5 =
      some (BitVec.ofNat 64 Elflings.ioContextAddress) :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x5 (by decide) |>.trans contextRead
  have sourcePremise := sourceRun premise (stepPremiseState_writes state (BitVec.ofNat 64 pc))
  have contextRun := rX_x5_run premise (BitVec.ofNat 64 Elflings.ioContextAddress) contextPremise
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 5#5)
        (sign_extend (m := 64) (BitVec.ofNat 12 offset)) (Store Data) 8) premise premise
      (.Ext_DataAddr_OK (virtaddr.Virtaddr
        (BitVec.ofNat 64 (Elflings.ioContextAddress + offset)))) := by
    simpa [addressEq] using get_transformed_data_addr_machine_data_run .store premise
      (.Regidx 5#5) 8 (BitVec.ofNat 64 Elflings.ioContextAddress)
      (sign_extend (m := 64) (BitVec.ofNat 12 offset)) mstatusBits mseccfgBits contextRun
      mstatusPremise privilegePremise mprvZero mseccfgPremise pmmDisabled
  have pmaPremise := storePmaAllows_of_agree agree pma
  have physical := phys_access_check_machine_store_allowed premise
    (BitVec.ofNat 64 (Elflings.ioContextAddress + offset)) 8
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    pmaPremise aligned.2
  have noMMIO := storeMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (Elflings.ioContextAddress + offset)) 8
    notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  let afterWrite := afterWriteBytes (width := 8) premise
    (Elflings.ioContextAddress + offset) source
  have access : ConfiguredDwordStoreAccess state afterWrite (BitVec.ofNat 64 pc)
      (BitVec.ofNat 12 offset) (.Regidx 5#5) sourceIndex :=
    ⟨_, mstatusBits, _, mstatusPremise, privilegePremise, mprvZero, sourcePremise,
      addressRun, aligned.1, physical, noMMIO, by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressFits]
        exact writeBytes_run_exact premise (Elflings.ioContextAddress + offset) source⟩
  simpa [afterWrite] using configuredDwordStoreStep stepNo pc state afterWrite
    (BitVec.ofNat 12 offset) (.Regidx 5#5) sourceIndex 0x23 byte1 byte2 0x00 configured atPc
    loaded decode access (pcFits := pcFits) (base := by rfl) (read0 := read0) (read1 := read1)
    (read2 := read2) (read3 := read3) (pcAligned := pcAligned)

/-- Production `0x10198: sd a0, 8(t0)`. -/
theorem writeOutputStoreBufferStep (stepNo : Nat) (state : State) (buffer : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10198))
    (contextRead : state.regs.get? x5 = some (BitVec.ofNat 64 Elflings.ioContextAddress))
    (bufferRead : state.regs.get? x10 = some (BitVec.ofNat 64 buffer))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (Elflings.ioContextAddress + 8)) 8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x10198)
          (Elflings.ioContextAddress + 8) (BitVec.ofNat 64 buffer)) 0x10198 retired) false := by
  obtain ⟨seccfgBits, _, _, privilegeAfter, seccfgAfter⟩ :=
    configured.storeDecodeContext
  apply writeOutputStoreStep stepNo 0x10198 8 state (BitVec.ofNat 64 buffer) (.Regidx 10#5)
    0xb4 0xa2 configured atPc contextRead _ pma loaded (by native_decide) (by native_decide)
    (by unfold StoreMMIOAddressExcluded DataMMIOAddressExcluded; constructor <;> rfl)
    (by native_decide) (by native_decide) (by decode_run)
  intro premise writes
  exact rX_x10_run premise _ ((writes.get x10 (by decide)).trans bufferRead)

/-- Production `0x1019c: sd a1, 16(t0)`. -/
theorem writeOutputStoreLengthStep (stepNo : Nat) (state : State) (count : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1019c))
    (contextRead : state.regs.get? x5 = some (BitVec.ofNat 64 Elflings.ioContextAddress))
    (countRead : state.regs.get? x11 = some (BitVec.ofNat 64 count))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (Elflings.ioContextAddress + 16)) 8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x1019c)
          (Elflings.ioContextAddress + 16) (BitVec.ofNat 64 count)) 0x1019c retired) false := by
  obtain ⟨seccfgBits, _, _, privilegeAfter, seccfgAfter⟩ :=
    configured.storeDecodeContext
  apply writeOutputStoreStep stepNo 0x1019c 16 state (BitVec.ofNat 64 count) (.Regidx 11#5)
    0xb8 0xb2 configured atPc contextRead _ pma loaded (by native_decide) (by native_decide)
    (by unfold StoreMMIOAddressExcluded DataMMIOAddressExcluded; constructor <;> rfl)
    (by native_decide) (by native_decide) (by decode_run)
  intro premise writes
  exact rX_x11_run premise _ ((writes.get x11 (by decide)).trans countRead)

/-- Production `0x101a0: ret`. -/
theorem writeOutputReturnStep (stepNo : Nat) (state : State) (returnAddress : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x101a0))
    (link : state.regs.get? x1 = some returnAddress)
    (targetAligned : Sail.BitVec.access returnAddress 1 = 0#1)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x101a0
          (Sail.BitVec.update returnAddress 0 0#1))
        (Sail.BitVec.update returnAddress 0 0#1) retired) false :=
  configuredRetStep stepNo 0x101a0 state returnAddress configured atPc link targetAligned loaded

def writeOutputPc (pc : BitVec 64) : Prop :=
  pc = 0x10190 ∨ pc = 0x10194 ∨ pc = 0x10198 ∨ pc = 0x1019c

def writeOutputTracePc (pc : BitVec 64) : Prop := writeOutputPc pc ∨ pc = 0x101a0

private def writeOutputExit (pc : BitVec 64) : Prop := pc = 0x101a0

/-- Exact register write set of the bare-metal `write_output` leaf. -/
def writeOutputWrites : RegSet :=
  RegSet.union stepBookkeeping (RegSet.only x5)

private theorem writeOutputMemory_not_file {address : Nat} (inside : writeOutputMemory address) :
    Artifacts.programImage.readFileByte? address = none := by
  cases read : Artifacts.programImage.readFileByte? address with
  | none => rfl
  | some byte =>
      obtain ⟨segment, member, lower, upper⟩ :=
        Binary.ProgramImage.readFileByte?_mem_segment read
      have segmentBound : segment.initialEndAddress ≤ Elflings.ioContextAddress + 8 := by
        have all : ∀ candidate ∈ Artifacts.programImage.segments.toList,
            candidate.initialEndAddress ≤ Elflings.ioContextAddress + 8 := by native_decide
        exact all segment member
      unfold writeOutputMemory Region.union byteRange at inside
      rcases inside with inside | inside <;> omega

private theorem platformPreserved_disjoint_writeOutputWrites :
    RegSet.Disjoint platformPreserved writeOutputWrites :=
  platformPreserved_disjoint.union
    (RegSet.Disjoint.only (by simp [platformPreserved]))

private theorem instructionPreserved_disjoint_writeOutputWrites :
    RegSet.Disjoint instructionPreserved writeOutputWrites :=
  (platformPreserved_disjoint.weaken (fun _ preserved => preserved.1)).union
    (RegSet.Disjoint.only (by simp [instructionPreserved, platformPreserved]))

private theorem writeOutputPc_in_writer {pc : BitVec 64} (inside : writeOutputPc pc) :
    pcInRanges Elflings.writeSuccessExecutionPcRanges pc := by
  rcases inside with rfl | rfl | rfl | rfl
  all_goals exact ⟨(0x10190, 0x101c4), by simp [Elflings.writeSuccessExecutionPcRanges],
    by native_decide, by native_decide⟩

private theorem writeOutputPc_not_observed {pc : BitVec 64} (inside : writeOutputPc pc) :
    ¬ BareMetalHostTransitionPc pc := by
  rcases inside with rfl | rfl | rfl | rfl <;>
    simp [BareMetalHostTransitionPc, readContextReturnPc, writeContextReturnPc,
      exitContextStorePc] <;> native_decide

private theorem liftWriteOutputPrefix (template : EndpointState) {fromStep count}
    {before after : State}
    (trace : ScopedTrace writeOutputPc writeOutputExit (fun _ _ _ _ _ => False)
      fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc writeOutputTracePc
      fromStep count { template with machine := before } { template with machine := after } := by
  induction trace with
  | exitAt fromStep state pc atPc exitPc => exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step fromStep count pc
        { template with machine := before } { template with machine := middle }
        { template with machine := after } ?_
          (show writeOutputTracePc pc from Or.inl inside) ?_ ?_
      · exact atPc
      · exact endpointStep_sail fromStep { template with machine := before } middle
          (fun observed observedPc => by
            change before.regs.get? PC = some observed at observedPc
            rw [atPc] at observedPc
            cases Option.some.inj observedPc
            exact writeOutputPc_not_observed inside) machineStep
      · simpa using ih
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count call program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

private theorem writeOutputLoadedOfSeg {kv a n base cur pc}
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (seg : Seg writeOutputPc writeOutputExit (fun _ _ _ _ _ => False)
      writeOutputWrites writeOutputMemory kv a n base cur pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  intro address byte file
  have outside : ¬ writeOutputMemory address := by
    intro inside
    rw [writeOutputMemory_not_file inside] at file
    cases file
  exact (seg.mem address outside).trans (loaded address byte file)

set_option genInjectivity false in
/-- The exact bare-metal `write_output` function, including its observable return step. -/
structure WriteOutputHandoff (fromStep : Nat) (buffer : Nat) (bytes : Array UInt8)
    (returnAddress : BitVec 64) (before after : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc
    writeOutputTracePc fromStep 5 before after
  atPc : after.machine.regs.get? PC = some (Sail.BitVec.update returnAddress 0 0#1)
  stdout : after.stdout = before.stdout ++ bytes
  stdin : after.stdin = before.stdin
  cursor : after.stdinCursor = before.stdinCursor
  exitCode : after.exitCode = before.exitCode
  writes : WritesOnlyRegs writeOutputWrites before.machine after.machine
  stackPreserved : after.machine.regs.get? x2 = before.machine.regs.get? x2
  preserved : Agree instructionPreserved before.machine after.machine
  aux : AuxStateAgree before.machine after.machine
  memory : WritesOnlyWithin writeOutputMemory before.machine after.machine
  configured : ConfiguredMachinePre EndpointMachinePc after.machine
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem

/-- Compose the exact five-instruction bare-metal `write_output` leaf with `Seg`. -/
theorem writeOutputHandoff (fromStep buffer : Nat) (bytes : Array UInt8)
    (returnAddress : BitVec 64) (before : EndpointState)
    (atPc : before.machine.regs.get? PC = some 0x10190)
    (link : before.machine.regs.get? x1 = some returnAddress)
    (bufferRead : before.machine.regs.get? x10 = some (BitVec.ofNat 64 buffer))
    (countRead : before.machine.regs.get? x11 = some (BitVec.ofNat 64 bytes.size))
    (bufferFits : buffer < 2 ^ 64) (countFits : bytes.size < 2 ^ 64)
    (bytesRep : BytesRep before.machine.mem buffer bytes)
    (bufferOutside : ∀ index, index < bytes.size → ¬ writeOutputMemory (buffer + index))
    (bufferPma : StorePmaAllows before.machine
      (BitVec.ofNat 64 (Elflings.ioContextAddress + 8)) 8)
    (lengthPma : StorePmaAllows before.machine
      (BitVec.ofNat 64 (Elflings.ioContextAddress + 16)) 8)
    (targetAligned : Sail.BitVec.access returnAddress 1 = 0#1)
    (configured : ConfiguredMachinePre EndpointMachinePc before.machine)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.machine.mem) :
    ∃ after, WriteOutputHandoff fromStep buffer bytes returnAddress before after := by
  obtain ⟨retired0, retiredRead0⟩ := configured.retiredCounter
  have seg0 := Seg.nil writeOutputPc writeOutputExit (fun _ _ _ _ _ => False)
    writeOutputWrites writeOutputMemory fromStep ⟨retired0, retiredRead0⟩ atPc
  have seg0 := (seg0.know x1 returnAddress link).know x10 (BitVec.ofNat 64 buffer) bufferRead
  have seg0 := seg0.know x11 (BitVec.ofNat 64 bytes.size) countRead
  obtain ⟨r1, run1⟩ := writeOutputContextBaseHighStep fromStep before.machine configured atPc loaded
  obtain ⟨s1, seg1⟩ := seg0.step (Or.inl rfl)
    (by unfold writeOutputExit; native_decide) x5 0x2401a190 0x10194 ⟨r1, run1⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr rfl)
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have cfg1 := configured.mono (seg1.agree instructionPreserved_disjoint_writeOutputWrites) seg1.retired
  have loaded1 := writeOutputLoadedOfSeg loaded seg1
  obtain ⟨r2, run2⟩ := writeOutputContextBaseLowStep (fromStep + 1) s1 cfg1 seg1.atPc
    (seg1.reg x5 0x2401a190 (by simp)) loaded1
  have seg1' := seg1.forget (kv' :=
    [⟨x11, BitVec.ofNat 64 bytes.size⟩, ⟨x10, BitVec.ofNat 64 buffer⟩,
      ⟨x1, returnAddress⟩]) (by simp)
  obtain ⟨s2, seg2⟩ := seg1'.step (Or.inr (Or.inl rfl))
    (by unfold writeOutputExit; native_decide) x5
    (BitVec.ofNat 64 Elflings.ioContextAddress) 0x10198 ⟨r2, run2⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr rfl)
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have cfg2 := configured.mono (seg2.agree instructionPreserved_disjoint_writeOutputWrites) seg2.retired
  have loaded2 := writeOutputLoadedOfSeg loaded seg2
  obtain ⟨r3, run3⟩ := writeOutputStoreBufferStep (fromStep + 2) s2 buffer cfg2 seg2.atPc
    (seg2.reg x5 _ (by simp)) (seg2.reg x10 _ (by simp))
    (storePmaAllows_of_agree (seg2.agree platformPreserved_disjoint_writeOutputWrites) bufferPma)
    loaded2
  obtain ⟨s3, seg3⟩ := seg2.stepStore (Elflings.ioContextAddress + 8)
    (BitVec.ofNat 64 buffer) 0x1019c (Or.inr (Or.inr (Or.inl rfl)))
    (by unfold writeOutputExit; native_decide) ⟨r3, run3⟩
    (by decide) (by intro address lo hi; exact Or.inl ⟨lo, hi⟩)
    (by intro r h; exact Or.inl h) (by simp [RegsOutside, stepBookkeeping])
  have cfg3 := configured.mono (seg3.agree instructionPreserved_disjoint_writeOutputWrites) seg3.retired
  have loaded3 := writeOutputLoadedOfSeg loaded seg3
  obtain ⟨r4, run4⟩ := writeOutputStoreLengthStep (fromStep + 3) s3 bytes.size cfg3 seg3.atPc
    (seg3.reg x5 _ (by simp)) (seg3.reg x11 _ (by simp))
    (storePmaAllows_of_agree (seg3.agree platformPreserved_disjoint_writeOutputWrites) lengthPma)
    loaded3
  obtain ⟨s4, seg4⟩ := seg3.stepStore (Elflings.ioContextAddress + 16)
    (BitVec.ofNat 64 bytes.size) 0x101a0 (Or.inr (Or.inr (Or.inr rfl)))
    (by unfold writeOutputExit; native_decide) ⟨r4, run4⟩
    (by decide) (by intro address lo hi; exact Or.inr ⟨lo, hi⟩)
    (by intro r h; exact Or.inl h) (by simp [RegsOutside, stepBookkeeping])
  have cfg4 := configured.mono (seg4.agree instructionPreserved_disjoint_writeOutputWrites) seg4.retired
  have loaded4 := writeOutputLoadedOfSeg loaded seg4
  have bytes4 := bytesRep.of_writesOnlyWithin seg4.mem bufferOutside
  obtain ⟨r5, run5⟩ := writeOutputReturnStep (fromStep + 4) s4 returnAddress cfg4 seg4.atPc
    (seg4.reg x1 returnAddress (by simp)) targetAligned loaded4
  let s5 := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s4) 0x101a0
      (Sail.BitVec.update returnAddress 0 0#1))
    (Sail.BitVec.update returnAddress 0 0#1) r5
  let beforeReturn : EndpointState := { before with machine := s4 }
  let after : EndpointState := { before with machine := s5, stdout := before.stdout ++ bytes }
  have machinePrefix : ScopedTrace writeOutputPc writeOutputExit (fun _ _ _ _ _ => False)
      fromStep 4 before.machine s4 := by
    have endTrace : ScopedTrace writeOutputPc writeOutputExit (fun _ _ _ _ _ => False)
        (fromStep + 4) 0 s4 s4 := .exitAt _ _ 0x101a0 seg4.atPc rfl
    simpa using seg4.confined 0 s4 endTrace
  have prefixTrace := liftWriteOutputPrefix before machinePrefix
  have finalStep : EndpointStep (fromStep + 4) beforeReturn after := .write
    ⟨buffer, bytes.size, bytes, seg4.atPc, seg4.reg x10 _ (by simp), seg4.reg x11 _ (by simp),
      bufferFits, countFits, rfl, bytes4, run5, rfl, rfl, rfl, rfl⟩
  have finalTrace : ConfinedTrace EndpointStep EndpointPc
      writeOutputTracePc (fromStep + 4) 1 beforeReturn after := by
    refine ConfinedTrace.step _ 0 0x101a0 beforeReturn after after seg4.atPc ?_ finalStep (.refl _ _)
    exact Or.inr rfl
  refine ⟨after, prefixTrace.append (by simpa [beforeReturn] using finalTrace), ?_, rfl, rfl, rfl,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [after, s5, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, Std.ExtDHashMap.get?_insert]
  · have writes5 : WritesOnlyRegs writeOutputWrites s4 s5 := by
      exact (jumpRetirement_writes s4 0x101a0
        (Sail.BitVec.update returnAddress 0 0#1) r5).mono (fun _ h => Or.inl h)
    simpa [after, s5] using WritesOnlyRegs.trans_same seg4.writes writes5
  · have writes5 : WritesOnlyRegs writeOutputWrites s4 s5 := by
      exact (jumpRetirement_writes s4 0x101a0
        (Sail.BitVec.update returnAddress 0 0#1) r5).mono (fun _ h => Or.inl h)
    exact (WritesOnlyRegs.trans_same seg4.writes writes5).get x2
      (by simp [writeOutputWrites, stepBookkeeping])
  · have writes5 : WritesOnlyRegs writeOutputWrites s4 s5 := by
      exact (jumpRetirement_writes s4 0x101a0
        (Sail.BitVec.update returnAddress 0 0#1) r5).mono (fun _ h => Or.inl h)
    exact (WritesOnlyRegs.trans_same seg4.writes writes5).agree
      instructionPreserved_disjoint_writeOutputWrites
  · have finalAux : AuxStateAgree s4 s5 := by
      simp [AuxStateAgree, s5, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement]
    simpa [after] using seg4.aux.trans finalAux
  · simpa [after, s5] using seg4.mem
  · have writes5 : WritesOnlyRegs writeOutputWrites s4 s5 := by
      exact (jumpRetirement_writes s4 0x101a0
        (Sail.BitVec.update returnAddress 0 0#1) r5).mono (fun _ h => Or.inl h)
    exact cfg4.mono (writes5.agree instructionPreserved_disjoint_writeOutputWrites)
      (jumpRetirement_retired_present s4 0x101a0
        (Sail.BitVec.update returnAddress 0 0#1) r5)
  · simpa [after, s5] using loaded4

/-- Production `0x14ccc: auipc a0, 0x24005`. -/
theorem allocatorStateBaseHighStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14ccc)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14ccc retired x10 0x24019ccc) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14ccc
  have pcRead : Runs (readReg PC) premise premise 0x14ccc := by
    apply readReg_run
    simp [premise, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (0x24005, .Regidx 10#5, .AUIPC))) premise
      { premise with regs := premise.regs.insert x10 0x24019ccc } (.Retire_Success ()) := by
    change Runs (execute_UTYPE 0x24005 (.Regidx 10#5) .AUIPC) _ _ _
    simpa using execute_UTYPE_auipc_run premise _ 0x24005 (.Regidx 10#5) 0x14ccc pcRead
      (wX_x10_run premise 0x24019ccc)
  exact configuredRegisterWriteStep stepNo 0x14ccc state x10 0x24019ccc
    (.UTYPE (0x24005, .Regidx 10#5, .AUIPC)) 0x17 0x55 0x00 0x24 configured atPc loaded
    (by decode_run) execute (base := by rfl)

/-- Production `0x14cd0: auipc a1, 3`. -/
theorem allocatorVtableBaseHighStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cd0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14cd0 retired x11 0x17cd0) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cd0
  have pcRead : Runs (readReg PC) premise premise 0x14cd0 := by
    apply readReg_run
    simp [premise, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (3, .Regidx 11#5, .AUIPC))) premise
      { premise with regs := premise.regs.insert x11 0x17cd0 } (.Retire_Success ()) := by
    change Runs (execute_UTYPE 3 (.Regidx 11#5) .AUIPC) _ _ _
    simpa using execute_UTYPE_auipc_run premise _ 3 (.Regidx 11#5) 0x14cd0 pcRead
      (wX_x11_run premise 0x17cd0)
  exact configuredRegisterWriteStep stepNo 0x14cd0 state x11 0x17cd0
    (.UTYPE (3, .Regidx 11#5, .AUIPC)) 0x97 0x35 0x00 0x00 configured atPc loaded
    (by decode_run) execute (base := by rfl)

/-- Production `0x14cdc: addi a0, a0, 996`. -/
theorem allocatorStateBaseLowStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cdc)
    (source : state.regs.get? x10 = some 0x24019ccc)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14cdc retired x10
        (BitVec.ofNat 64 0x2401a0b0)) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14cdc
  have source' : premise.regs.get? x10 = some 0x24019ccc :=
    (stepPremiseState_writes state 0x14cdc).get x10 (by decide) |>.trans source
  let result := BitVec.ofNat 64 0x2401a0b0
  have resultEq : iTypeResult .ADDI 0x3e4 0x24019ccc = result := by native_decide
  have execute : Runs (execute (.ITYPE (0x3e4, .Regidx 10#5, .Regidx 10#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x10 result } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x3e4 (.Regidx 10#5) (.Regidx 10#5) .ADDI) _ _ _
    simpa only [resultEq] using
      execute_ITYPE_run premise _ 0x3e4 (.Regidx 10#5) (.Regidx 10#5) .ADDI 0x24019ccc
        (rX_x10_run premise 0x24019ccc source')
        (wX_x10_run premise result)
  exact configuredRegisterWriteStep stepNo 0x14cdc state x10
    (BitVec.ofNat 64 0x2401a0b0)
    (.ITYPE (0x3e4, .Regidx 10#5, .Regidx 10#5, .ADDI)) 0x13 0x05 0x45 0x3e
    configured atPc loaded (by configured_decode configured) execute (base := by rfl)

/-- Production `0x14ce0: addi a1, a1, -1320`. -/
theorem allocatorVtableBaseLowStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14ce0)
    (source : state.regs.get? x11 = some 0x17cd0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14ce0 retired x11
        (BitVec.ofNat 64 Elflings.allocatorVtableAddress)) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x14ce0
  have source' : premise.regs.get? x11 = some 0x17cd0 :=
    (stepPremiseState_writes state 0x14ce0).get x11 (by decide) |>.trans source
  let result := BitVec.ofNat 64 Elflings.allocatorVtableAddress
  have resultEq : iTypeResult .ADDI 0xad8 0x17cd0 = result := by native_decide
  have execute : Runs (execute (.ITYPE (0xad8, .Regidx 11#5, .Regidx 11#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x11 result } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0xad8 (.Regidx 11#5) (.Regidx 11#5) .ADDI) _ _ _
    simpa only [resultEq] using
      execute_ITYPE_run premise _ 0xad8 (.Regidx 11#5) (.Regidx 11#5) .ADDI 0x17cd0
        (rX_x11_run premise 0x17cd0 source')
        (wX_x11_run premise result)
  exact configuredRegisterWriteStep stepNo 0x14ce0 state x11
    (BitVec.ofNat 64 Elflings.allocatorVtableAddress)
    (.ITYPE (0xad8, .Regidx 11#5, .Regidx 11#5, .ADDI)) 0x93 0x85 0x85 0xad
    configured atPc loaded (by configured_decode configured) execute (base := by rfl)

private theorem allocatorLoadAtX2Step (stepNo pc offset : Nat) (state : State)
    (stackPointer value : Nat) (imm : BitVec 12) (rd : regidx) (destination : Register)
    (result : RegisterType destination) (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (rep : UIntRep 8 state.mem (stackPointer + offset) value)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (stackPointer + offset)) 8)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + offset)) 8)
    (aligned : stackPointer % 8 = 0) (fits : stackPointer + 0x20 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (addressEq : BitVec.ofNat 64 stackPointer + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (stackPointer + offset))
    (offsetBound : offset + 8 ≤ 0x20)
    (offsetAligned : (stackPointer + offset) % 8 = 0)
    (pcFits : pc < 2 ^ 64)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (imm, .Regidx 2#5, rd, false, 8)))
    (writeRun : ∀ premise, Runs (wX_bits rd (BitVec.ofNat 64 value)) premise
      { premise with regs := premise.regs.insert destination result } ())
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret)
    (pcAligned : pc % 4 = 0 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination result) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state (BitVec.ofNat 64 pc)).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨seccfgBits, seccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise := (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have stackPremise := (stepPremiseState_writes state (BitVec.ofNat 64 pc)).get x2
    (by decide) |>.trans stackRead
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 2#5) (sign_extend (m := 64) imm) (Load Data) 8)
      premise premise (.Ext_DataAddr_OK
        (virtaddr.Virtaddr (BitVec.ofNat 64 (stackPointer + offset)))) := by
    simpa [addressEq] using get_transformed_data_addr_machine_data_run .load premise
      (.Regidx 2#5) 8 (BitVec.ofNat 64 stackPointer) (sign_extend (m := 64) imm)
      mstatusBits seccfgBits (rX_x2_run premise (BitVec.ofNat 64 stackPointer) stackPremise)
      mstatusPremise privilegePremise mprvZero
      ((agree mseccfg (by simp [platformPreserved])).trans seccfgRead) pmmDisabled
  have physical := phys_access_check_machine_load_allowed premise
    (BitVec.ofNat 64 (stackPointer + offset)) 8
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (loadPmaAllows_of_agree agree pma)
    (ofNatAlignedEight (stackPointer + offset) (by omega) offsetAligned).2
  have noMMIO := loadMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (stackPointer + offset)) 8 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  have bytes : ∀ index (bound : index <
      (BinaryFv.RiscV.Sep.leBytes 8 (BitVec.ofNat 64 value)).length),
      premise.mem.get? ((BitVec.ofNat 64 (stackPointer + offset)).toNat + index) =
        some (BinaryFv.RiscV.Sep.leBytes 8 (BitVec.ofNat 64 value))[index] := by
    intro index bound
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simpa [premise, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using
      rep.leBytes index (by simpa only [BinaryFv.RiscV.Sep.leBytes_length] using bound)
  have execute : Runs (execute (.LOAD (imm, .Regidx 2#5, rd, false, 8))) premise
      { premise with regs := premise.regs.insert destination result }
      (.Retire_Success ()) := by
    change Runs (execute_LOAD imm (.Regidx 2#5) rd false 8) _ _ _
    exact execute_LOAD_ld_run premise _ imm (.Regidx 2#5) rd
      (BitVec.ofNat 64 (stackPointer + offset)) mstatusBits (BitVec.ofNat 64 value)
      mstatusPremise privilegePremise mprvZero addressRun
      (ofNatAlignedEight (stackPointer + offset) (by omega) offsetAligned).1 physical noMMIO bytes
      (writeRun premise)
  exact configuredRegisterWriteStep stepNo pc state destination result
    (.LOAD (imm, .Regidx 2#5, rd, false, 8)) byte0 byte1 byte2 byte3
    configured atPc loaded decode execute (pcFits := pcFits) (base := base)
      (destinationNotNextPc := destinationNotNextPc) (destinationNotHart := destinationNotHart)
      (destinationNotIncrement := destinationNotIncrement)
      (destinationNotRetired := destinationNotRetired)
      (read0 := read0) (read1 := read1) (read2 := read2) (read3 := read3)
      (pcAligned := pcAligned)

/-- Production `0x14cd4: ld a3, 8(sp)`. -/
theorem allocatorLoadInputSizeStep (stepNo : Nat) (state : State)
    (stackPointer inputSize : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cd4)
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (rep : UIntRep 8 state.mem (stackPointer + 8) inputSize)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 (stackPointer + 8)) 8)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + 8)) 8)
    (aligned : stackPointer % 8 = 0) (fits : stackPointer + 0x20 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14cd4 retired x13 (BitVec.ofNat 64 inputSize)) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  exact allocatorLoadAtX2Step stepNo 0x14cd4 8 state stackPointer inputSize 8
    (.Regidx 13#5) x13 (BitVec.ofNat 64 inputSize) 0x83 0x36 0x81 0x00
    configured atPc stackRead rep pma notMMIO aligned fits loaded
    (by
      change BitVec.ofNat 64 stackPointer + (8#64) = BitVec.ofNat 64 (stackPointer + 8)
      rw [← BitVec.ofNat_add])
    (by omega) (by omega) (by native_decide) (by rfl)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by decode_run) (fun premise => wX_x13_run premise (BitVec.ofNat 64 inputSize))
    (by decide) (by decide) (by decide) (by decide)

/-- Production `0x14cd8: ld a2, 0(sp)`. -/
theorem allocatorLoadInputAddressStep (stepNo : Nat) (state : State)
    (stackPointer inputAddress : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14cd8)
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (rep : UIntRep 8 state.mem stackPointer inputAddress)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 stackPointer) 8)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 stackPointer) 8)
    (aligned : stackPointer % 8 = 0) (fits : stackPointer + 0x20 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x14cd8 retired x12 (BitVec.ofNat 64 inputAddress)) false := by
  have rep' : UIntRep 8 state.mem (stackPointer + 0) inputAddress := by simpa using rep
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  exact allocatorLoadAtX2Step stepNo 0x14cd8 0 state stackPointer inputAddress 0
    (.Regidx 12#5) x12 (BitVec.ofNat 64 inputAddress) 0x03 0x36 0x01 0x00
    configured atPc stackRead rep' pma notMMIO aligned fits loaded
    (by
      change BitVec.ofNat 64 stackPointer + (0#64) = BitVec.ofNat 64 (stackPointer + 0)
      simp)
    (by omega) (by simpa using aligned) (by native_decide) (by rfl)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by decode_run) (fun premise => wX_x12_run premise (BitVec.ofNat 64 inputAddress))
    (by decide) (by decide) (by decide) (by decide)

private theorem allocatorStoreAtX2Step (stepNo pc offset : Nat) (state : State)
    (stackPointer : Nat) (value : BitVec 64) (imm : BitVec 12) (rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (stackPointer + offset)) 8)
    (notMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + offset)) 8)
    (aligned : (stackPointer + offset) % 8 = 0) (fits : stackPointer + 0x20 < 2 ^ 64)
    (offsetBound : offset + 8 ≤ 0x20)
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
    (pcFits : pc < 2 ^ 64) (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3)
    (pcAligned : pc % 4 = 0 := by native_decide) :
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
    (read2 := read2) (read3 := read3) (pcAligned := pcAligned)

/-- Production `0x14ce4: sd a0, 16(sp)`. -/
theorem allocatorStoreStateStep (stepNo : Nat) (state : State) (stackPointer : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14ce4)
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (sourceRead : state.regs.get? x10 = some (BitVec.ofNat 64 0x2401a0b0))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (stackPointer + 0x10)) 8)
    (notMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + 0x10)) 8)
    (aligned : stackPointer % 8 = 0) (fits : stackPointer + 0x20 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x14ce4)
          (stackPointer + 0x10) (BitVec.ofNat 64 0x2401a0b0)) 0x14ce4 retired) false := by
  exact allocatorStoreAtX2Step stepNo 0x14ce4 0x10 state stackPointer
    (BitVec.ofNat 64 0x2401a0b0) 0x10 (.Regidx 10#5) 0x23 0x38 0xa1 0x00
    configured atPc stackRead pma notMMIO (by omega) fits (by omega) loaded
    (by change BitVec.ofNat 64 stackPointer + (0x10#64) = _; rw [← BitVec.ofNat_add])
    (by
      obtain ⟨_, _, _, privilegeAfter, seccfgAfter⟩ :=
        configured.storeDecodeContext
      decode_run)
    (fun premise writes => rX_x10_run premise _
      ((writes.get x10 (by decide)).trans sourceRead))
    (by native_decide) (by rfl) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

/-- Production `0x14ce8: sd a1, 24(sp)`. -/
theorem allocatorStoreVtableStep (stepNo : Nat) (state : State) (stackPointer : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x14ce8)
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer))
    (sourceRead : state.regs.get? x11 = some (BitVec.ofNat 64 Elflings.allocatorVtableAddress))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (stackPointer + 0x18)) 8)
    (notMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 (stackPointer + 0x18)) 8)
    (aligned : stackPointer % 8 = 0) (fits : stackPointer + 0x20 < 2 ^ 64)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x14ce8)
          (stackPointer + 0x18) (BitVec.ofNat 64 Elflings.allocatorVtableAddress))
        0x14ce8 retired) false := by
  exact allocatorStoreAtX2Step stepNo 0x14ce8 0x18 state stackPointer
    (BitVec.ofNat 64 Elflings.allocatorVtableAddress) 0x18 (.Regidx 11#5)
    0x23 0x3c 0xb1 0x00 configured atPc stackRead pma notMMIO (by omega) fits (by omega) loaded
    (by change BitVec.ofNat 64 stackPointer + (0x18#64) = _; rw [← BitVec.ofNat_add])
    (by
      obtain ⟨_, _, _, privilegeAfter, seccfgAfter⟩ :=
        configured.storeDecodeContext
      decode_run)
    (fun premise writes => rX_x11_run premise _
      ((writes.get x11 (by decide)).trans sourceRead))
    (by native_decide) (by rfl) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

/-- Production `0x10140: auipc t0, 0x2000a`. -/
theorem readInputBufferBaseHighStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10140))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x10140 retired x5 0x2001a140) false := by
  obtain ⟨seccfgBits, seccfgRead, pmmDisabled, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  exact configuredAuipcX5Step stepNo 0x10140 state 0x2000a 0x2001a140
    0x97 0xa2 0x00 0x20 configured atPc loaded (by native_decide) (by decode_run)
    (by native_decide) (by rfl)

/-- Production `0x10144: addi t0, t0, -320`. -/
theorem readInputBufferBaseLowStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10144))
    (sourceRead : state.regs.get? x5 = some (BitVec.ofNat 64 0x2001a140))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x10144 retired x5 Elflings.inputBufferAddress) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  exact configuredAddiX5Step stepNo 0x10144 state 0xec0 0x2001a140
    Elflings.inputBufferAddress 0x93 0x82 0x02 0xec configured atPc sourceRead loaded
    (by native_decide) (by decode_run) (by native_decide) (by rfl)

/-- Production `0x1014c: auipc t0, 0x2400a`. -/
theorem readInputContextBaseHighStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1014c))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1014c retired x5 0x2401a14c) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  exact configuredAuipcX5Step stepNo 0x1014c state 0x2400a 0x2401a14c
    0x97 0xa2 0x00 0x24 configured atPc loaded (by native_decide) (by decode_run)
    (by native_decide) (by rfl)

/-- Production `0x10150: addi t0, t0, -148`. -/
theorem readInputContextBaseLowStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10150))
    (sourceRead : state.regs.get? x5 = some (BitVec.ofNat 64 0x2401a14c))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x10150 retired x5 Elflings.ioContextAddress) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  exact configuredAddiX5Step stepNo 0x10150 state 0xf6c 0x2401a14c
    Elflings.ioContextAddress 0x93 0x82 0xc2 0xf6 configured atPc sourceRead loaded
    (by native_decide) (by decode_run) (by native_decide) (by rfl)

/-- Production `0x10154: ld t1, 0(t0)`. -/
theorem readInputLoadSizeStep (stepNo : Nat) (state : State) (inputSize : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10154))
    (contextRead : state.regs.get? x5 = some (BitVec.ofNat 64 Elflings.ioContextAddress))
    (sizeRep : UIntRep 8 state.mem Elflings.ioContextAddress inputSize)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 Elflings.ioContextAddress) 8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x10154 retired x6 (BitVec.ofNat 64 inputSize)) false := by
  obtain ⟨seccfgBits, seccfgRead, pmmDisabled, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  have decode : Runs (ext_decode (fetchWord 0x03 0xb3 0x02 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0, .Regidx 5#5, .Regidx 6#5, false, 8)) := by
    decode_run
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10154
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state 0x10154).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  have mstatusPremise : premise.regs.get? mstatus = some mstatusBits :=
    (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise : premise.regs.get? cur_privilege = some .Machine :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have contextPremise : premise.regs.get? x5 =
      some (BitVec.ofNat 64 Elflings.ioContextAddress) :=
    (stepPremiseState_writes state 0x10154).get x5 (by decide) |>.trans contextRead
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 5#5) (sign_extend (m := 64) (0#12))
        (Load Data) 8) premise premise
      (.Ext_DataAddr_OK (virtaddr.Virtaddr (BitVec.ofNat 64 Elflings.ioContextAddress))) := by
    simpa using get_transformed_data_addr_machine_data_run .load premise (.Regidx 5#5) 8
      (BitVec.ofNat 64 Elflings.ioContextAddress) (sign_extend (m := 64) (0#12))
      mstatusBits seccfgBits
      (rX_x5_run premise (BitVec.ofNat 64 Elflings.ioContextAddress) contextPremise)
      mstatusPremise privilegePremise mprvZero
      ((agree mseccfg (by simp [platformPreserved])).trans seccfgRead) pmmDisabled
  have physical := phys_access_check_machine_load_allowed premise
    (BitVec.ofNat 64 Elflings.ioContextAddress) 8
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (loadPmaAllows_of_agree agree pma) (by native_decide)
  have noMMIO := loadMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 Elflings.ioContextAddress) 8
    (by unfold LoadMMIOAddressExcluded DataMMIOAddressExcluded; constructor <;> rfl)
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  have bytes : ∀ (index : Nat) (bound : index <
      (BinaryFv.RiscV.Sep.leBytes 8 (BitVec.ofNat 64 inputSize)).length),
      premise.mem.get? (Elflings.ioContextAddress + index) =
        some (BinaryFv.RiscV.Sep.leBytes 8 (BitVec.ofNat 64 inputSize))[index] := by
    intro index bound
    simpa [premise, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using
      sizeRep.leBytes index (by simpa only [BinaryFv.RiscV.Sep.leBytes_length] using bound)
  have execute : Runs (execute (.LOAD (0, .Regidx 5#5, .Regidx 6#5, false, 8))) premise
      { premise with regs := premise.regs.insert x6 (BitVec.ofNat 64 inputSize) }
      (.Retire_Success ()) := by
    change Runs (execute_LOAD 0 (.Regidx 5#5) (.Regidx 6#5) false 8) _ _ _
    exact execute_LOAD_ld_run premise _ 0 (.Regidx 5#5) (.Regidx 6#5)
      (BitVec.ofNat 64 Elflings.ioContextAddress) mstatusBits (BitVec.ofNat 64 inputSize)
      mstatusPremise privilegePremise mprvZero addressRun (by native_decide) physical noMMIO bytes
      (wX_x6_run premise (BitVec.ofNat 64 inputSize))
  exact configuredRegisterWriteStep stepNo 0x10154 state x6 (BitVec.ofNat 64 inputSize)
    (.LOAD (0, .Regidx 5#5, .Regidx 6#5, false, 8)) 0x03 0xb3 0x02 0x00
    configured atPc loaded decode execute (base := by rfl)

/-- Production `0x10148: sd t0, 0(a0)`. -/
theorem readInputStorePointerStep (stepNo : Nat) (state : State) (bufferSlot : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10148))
    (slotRead : state.regs.get? x10 = some (BitVec.ofNat 64 bufferSlot))
    (pointerRead : state.regs.get? x5 = some (BitVec.ofNat 64 Elflings.inputBufferAddress))
    (aligned : bufferSlot % 8 = 0) (fits : bufferSlot + 16 < 2 ^ 64)
    (pma : StorePmaAllows state (BitVec.ofNat 64 bufferSlot) 8)
    (notMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 bufferSlot) 8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x10148)
          bufferSlot (BitVec.ofNat 64 Elflings.inputBufferAddress))
        0x10148 retired) false := by
  let premise := coreStoreNextState (tryStepStoreAfterIncrement state) 0x10148
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state 0x10148).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise : premise.regs.get? mstatus = some mstatusBits :=
    (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise : premise.regs.get? cur_privilege = some .Machine :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have mseccfgPremise : premise.regs.get? mseccfg = some mseccfgBits :=
    (agree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have slotPremise : premise.regs.get? x10 = some (BitVec.ofNat 64 bufferSlot) :=
    (stepPremiseState_writes state 0x10148).get x10 (by decide) |>.trans slotRead
  have pointerPremise : premise.regs.get? x5 =
      some (BitVec.ofNat 64 Elflings.inputBufferAddress) :=
    (stepPremiseState_writes state 0x10148).get x5 (by decide) |>.trans pointerRead
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 10#5) (sign_extend (m := 64) (0#12))
        (Store Data) 8) premise premise
      (.Ext_DataAddr_OK (virtaddr.Virtaddr (BitVec.ofNat 64 bufferSlot))) := by
    have zero : sign_extend (m := 64) (0#12) = 0#64 := by native_decide
    have zeroOffset : BitVec.ofNat 64 bufferSlot + sign_extend (m := 64) (0#12) =
        BitVec.ofNat 64 bufferSlot := by simp [zero]
    simpa [zeroOffset] using get_transformed_data_addr_machine_data_run .store premise
      (.Regidx 10#5) 8
      (BitVec.ofNat 64 bufferSlot) (sign_extend (m := 64) (0#12))
      mstatusBits mseccfgBits (rX_x10_run premise (BitVec.ofNat 64 bufferSlot) slotPremise)
      mstatusPremise privilegePremise mprvZero mseccfgPremise pmmDisabled
  have physical := phys_access_check_machine_store_allowed premise
    (BitVec.ofNat 64 bufferSlot) 8
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (storePmaAllows_of_agree agree pma)
    (ofNatAlignedEight bufferSlot (by omega) aligned).2
  have noMMIO := storeMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 bufferSlot) 8 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  let afterWrite := afterWriteBytes (width := 8) premise (BitVec.ofNat 64 bufferSlot).toNat
    (BitVec.ofNat 64 Elflings.inputBufferAddress)
  have access : ConfiguredDwordStoreAccess state afterWrite 0x10148 0
      (.Regidx 10#5) (.Regidx 5#5) :=
    ⟨_, mstatusBits, _, mstatusPremise, privilegePremise, mprvZero,
      rX_x5_run premise (BitVec.ofNat 64 Elflings.inputBufferAddress) pointerPremise,
      addressRun, (ofNatAlignedEight bufferSlot (by omega) aligned).1, physical, noMMIO,
      writeBytes_run_exact premise (BitVec.ofNat 64 bufferSlot).toNat
        (BitVec.ofNat 64 Elflings.inputBufferAddress)⟩
  obtain ⟨_, _, _, privilegeAfter, seccfgAfter⟩ :=
    configured.storeDecodeContext
  have decode : Runs (ext_decode (fetchWord 0x23 0x30 0x55 0x00))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (0, .Regidx 5#5, .Regidx 10#5, 8)) := by
    decode_run
  simpa [afterWrite, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bufferSlot < 2 ^ 64)] using
    configuredDwordStoreStep stepNo 0x10148 state afterWrite 0
    (.Regidx 10#5) (.Regidx 5#5) 0x23 0x30 0x55 0x00 configured atPc loaded decode access
    (base := by rfl)

/-- Production `0x10158: sd t1, 0(a1)`. -/
theorem readInputStoreSizeStep (stepNo : Nat) (state : State) (sizeSlot inputSize : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10158))
    (slotRead : state.regs.get? x11 = some (BitVec.ofNat 64 sizeSlot))
    (sizeRead : state.regs.get? x6 = some (BitVec.ofNat 64 inputSize))
    (aligned : sizeSlot % 8 = 0) (fits : sizeSlot + 8 < 2 ^ 64)
    (pma : StorePmaAllows state (BitVec.ofNat 64 sizeSlot) 8)
    (notMMIO : StoreMMIOAddressExcluded (BitVec.ofNat 64 sizeSlot) 8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x10158)
          sizeSlot (BitVec.ofNat 64 inputSize))
        0x10158 retired) false := by
  let premise := coreStoreNextState (tryStepStoreAfterIncrement state) 0x10158
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state 0x10158).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise : premise.regs.get? mstatus = some mstatusBits :=
    (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise : premise.regs.get? cur_privilege = some .Machine :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have mseccfgPremise : premise.regs.get? mseccfg = some mseccfgBits :=
    (agree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have slotPremise : premise.regs.get? x11 = some (BitVec.ofNat 64 sizeSlot) :=
    (stepPremiseState_writes state 0x10158).get x11 (by decide) |>.trans slotRead
  have sizePremise : premise.regs.get? x6 = some (BitVec.ofNat 64 inputSize) :=
    (stepPremiseState_writes state 0x10158).get x6 (by decide) |>.trans sizeRead
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 11#5) (sign_extend (m := 64) (0#12))
        (Store Data) 8) premise premise
      (.Ext_DataAddr_OK (virtaddr.Virtaddr (BitVec.ofNat 64 sizeSlot))) := by
    have zero : sign_extend (m := 64) (0#12) = 0#64 := by native_decide
    have zeroOffset : BitVec.ofNat 64 sizeSlot + sign_extend (m := 64) (0#12) =
        BitVec.ofNat 64 sizeSlot := by simp [zero]
    simpa [zeroOffset] using get_transformed_data_addr_machine_data_run .store premise
      (.Regidx 11#5) 8 (BitVec.ofNat 64 sizeSlot) (sign_extend (m := 64) (0#12))
      mstatusBits mseccfgBits (rX_x11_run premise (BitVec.ofNat 64 sizeSlot) slotPremise)
      mstatusPremise privilegePremise mprvZero mseccfgPremise pmmDisabled
  have physical := phys_access_check_machine_store_allowed premise
    (BitVec.ofNat 64 sizeSlot) 8
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    (storePmaAllows_of_agree agree pma)
    (ofNatAlignedEight sizeSlot (by omega) aligned).2
  have noMMIO := storeMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 sizeSlot) 8 notMMIO
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  let afterWrite := afterWriteBytes (width := 8) premise (BitVec.ofNat 64 sizeSlot).toNat
    (BitVec.ofNat 64 inputSize)
  have access : ConfiguredDwordStoreAccess state afterWrite 0x10158 0
      (.Regidx 11#5) (.Regidx 6#5) :=
    ⟨_, mstatusBits, _, mstatusPremise, privilegePremise, mprvZero,
      rX_x6_run premise (BitVec.ofNat 64 inputSize) sizePremise,
      addressRun, (ofNatAlignedEight sizeSlot (by omega) aligned).1, physical, noMMIO,
      writeBytes_run_exact premise (BitVec.ofNat 64 sizeSlot).toNat
        (BitVec.ofNat 64 inputSize)⟩
  obtain ⟨_, _, _, privilegeAfter, seccfgAfter⟩ :=
    configured.storeDecodeContext
  have decode : Runs (ext_decode (fetchWord 0x23 0xb0 0x65 0x00))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (0, .Regidx 6#5, .Regidx 11#5, 8)) := by
    decode_run
  simpa [afterWrite, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sizeSlot < 2 ^ 64)] using
    configuredDwordStoreStep stepNo 0x10158 state afterWrite 0
      (.Regidx 11#5) (.Regidx 6#5) 0x23 0xb0 0x65 0x00 configured atPc loaded decode access
      (base := by rfl)

private def readInputWrites : RegSet :=
  RegSet.union stepBookkeeping (RegSet.union (RegSet.only x5) (RegSet.only x6))

private def readInputMemory (args : ReadInputArgs) : Region :=
  Region.union (byteRange args.bufferSlot 8) (byteRange args.sizeSlot 8)

private theorem instructionPreserved_disjoint_readInputWrites :
    RegSet.Disjoint instructionPreserved readInputWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem platformPreserved_disjoint_readInputWrites :
    RegSet.Disjoint platformPreserved readInputWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint register preserved bookkeeping
  all_goals simp [platformPreserved] at preserved

private theorem abiCalleePreserved_disjoint_readInputWrites :
    RegSet.Disjoint abiCalleePreserved readInputWrites := by
  intro register preserved written
  simp [abiCalleePreserved, readInputWrites, stepBookkeeping, platformPreserved] at preserved written
  grind

private theorem readInputPcInside (pc : BitVec 64)
    (literal : pc = 0x10140 ∨ pc = 0x10144 ∨ pc = 0x10148 ∨ pc = 0x1014c ∨
      pc = 0x10150 ∨ pc = 0x10154 ∨ pc = 0x10158) :
    pcInRanges Elflings.readInputExecutionPcRanges pc := by
  rcases literal with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨(0x10140, 0x10190), by native_decide, by native_decide, by native_decide⟩

private theorem readInputPcNotExit (pc : BitVec 64)
    (literal : pc = 0x10140 ∨ pc = 0x10144 ∨ pc = 0x10148 ∨ pc = 0x1014c ∨
      pc = 0x10150 ∨ pc = 0x10154 ∨ pc = 0x10158) :
    ¬ pcInList Elflings.readInputExitPcs pc := by
  rcases literal with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold pcInList <;> native_decide

private theorem readInputPcNotObserved (pc : BitVec 64)
    (literal : pc = 0x10140 ∨ pc = 0x10144 ∨ pc = 0x10148 ∨ pc = 0x1014c ∨
      pc = 0x10150 ∨ pc = 0x10154 ∨ pc = 0x10158) :
    ¬ BareMetalHostTransitionPc pc := by
  rcases literal with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [BareMetalHostTransitionPc] <;> native_decide

private theorem readInputConfinedSailStep (stepNo : Nat) (before : EndpointState)
    (after : State) (pc : BitVec 64)
    (literal : pc = 0x10140 ∨ pc = 0x10144 ∨ pc = 0x10148 ∨ pc = 0x1014c ∨
      pc = 0x10150 ∨ pc = 0x10154 ∨ pc = 0x10158)
    (atPc : EndpointPc before = some pc) (step : MachineStep stepNo before.machine after) :
    ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.readInputExecutionPcRanges)
      stepNo 1 before { before with machine := after } := by
  apply ConfinedTrace.step stepNo 0 pc before { before with machine := after }
    { before with machine := after }
  · exact atPc
  · exact readInputPcInside pc literal
  · exact endpointStep_sail stepNo before after (fun target targetPc => by
      rw [atPc] at targetPc
      cases Option.some.inj targetPc
      exact readInputPcNotObserved pc literal) step
  · exact .refl (stepNo + 1) _

private theorem readInput_region_not_file (args : ReadInputArgs) (entry : ReadInputEntry args before)
    {address : Nat} (inside : readInputMemory args address) :
    Artifacts.programImage.readFileByte? address = none := by
  rcases entry with ⟨_returnPc, _inputBound, _stdin, _cursor, _atPc, _returnReg,
    _bufferReg, _sizeReg, sizeEq, _aligned, _fits, _bytes, _context, _saved, _pmaBuffer,
    _pmaSize, _loadPma, _mmioBuffer, _mmioSize, _inputOutside, _contextOutside, _savedOutside,
    notFile, _loaded, _configured⟩
  unfold readInputMemory Region.union byteRange at inside
  rcases inside with inside | inside
  · exact notFile address inside.1 (by omega)
  · exact notFile address (by omega) (by omega)

private theorem readInput_code_of_seg (args : ReadInputArgs) (entry : ReadInputEntry args before)
    {fromStep count : Nat} {after : State} {kv : List RegVal} {pc : BitVec 64}
    (seg : Seg (pcInRanges Elflings.readInputExecutionPcRanges)
      (pcInList Elflings.readInputExitPcs) (fun _ _ _ _ _ => False)
      readInputWrites (readInputMemory args) kv fromStep count before.machine after pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
  have entryCopy := entry
  rcases entry with ⟨_returnPc, _inputBound, _stdin, _cursor, _atPc, _returnReg,
    _bufferReg, _sizeReg, _sizeEq, _aligned, _fits, _bytes, _context, _saved, _pmaBuffer,
    _pmaSize, _loadPma, _mmioBuffer, _mmioSize, _inputOutside, _contextOutside, _savedOutside,
    _notFile, loaded, _configured⟩
  intro address byte file
  rw [seg.mem address]
  · exact loaded address byte file
  · intro inside
    have noFile := readInput_region_not_file args entryCopy inside
    rw [noFile] at file
    cases file

private def NonRegisterFrame (before after : State) : Prop :=
  after.choiceState = before.choiceState ∧ after.tags = before.tags ∧
    after.sailOutput = before.sailOutput

private theorem NonRegisterFrame.trans {first middle last : State}
    (left : NonRegisterFrame first middle) (right : NonRegisterFrame middle last) :
    NonRegisterFrame first last :=
  ⟨right.1.trans left.1, right.2.1.trans left.2.1, right.2.2.trans left.2.2⟩

private theorem nonRegisterFrame_afterRegisterWrite (state : State) (pc retired : BitVec 64)
    (dest : Register) (value : RegisterType dest) :
    NonRegisterFrame state (afterRegisterWrite state pc retired dest value) := by
  exact ⟨rfl, rfl, rfl⟩

private theorem nonRegisterFrame_afterByteWrites (state : State)
    (writes : List (Nat × BitVec 8)) :
    NonRegisterFrame state (afterByteWrites state writes) := by
  unfold afterByteWrites
  induction writes generalizing state with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons write writes ih =>
      simpa only [List.foldl_cons] using
        ih { state with mem := state.mem.insert write.1 write.2 }

private theorem nonRegisterFrame_afterStore {width : Nat} (state : State)
    (pc retired : BitVec 64) (address : Nat) (value : BitVec (8 * width)) :
    NonRegisterFrame state
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
          address value)
        (Sail.BitVec.addInt pc 4) retired) := by
  simpa only [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, afterWriteBytes] using
    nonRegisterFrame_afterByteWrites
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (List.ofFn fun index : Fin width =>
        (address + index.val, value.extractLsb' (8 * index.val) 8))

private theorem nonRegisterFrame_afterJump (state : State) (pc target retired : BitVec 64) :
    NonRegisterFrame state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target) target retired) :=
  ⟨rfl, rfl, rfl⟩

private def allocatorWrites : RegSet :=
  RegSet.union stepBookkeeping
    (RegSet.union (RegSet.only x10)
      (RegSet.union (RegSet.only x11) (RegSet.union (RegSet.only x12) (RegSet.only x13))))

private def allocatorMemory (args : AllocatorGetArgs) : Region :=
  Region.union (byteRange (args.stackPointer + 0x10) 8)
    (byteRange (args.stackPointer + 0x18) 8)

private theorem instructionPreserved_disjoint_allocatorWrites :
  RegSet.Disjoint instructionPreserved allocatorWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem platformPreserved_disjoint_allocatorWrites :
    RegSet.Disjoint platformPreserved allocatorWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved bookkeeping
  all_goals simp [platformPreserved] at preserved

private theorem allocatorPcInside (pc : BitVec 64)
    (literal : pc = 0x14ccc ∨ pc = 0x14cd0 ∨ pc = 0x14cd4 ∨ pc = 0x14cd8 ∨
      pc = 0x14cdc ∨ pc = 0x14ce0 ∨ pc = 0x14ce4 ∨ pc = 0x14ce8) :
    pcInRanges Elflings.allocatorGetExecutionPcRanges pc := by
  rcases literal with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨(0x14ccc, 0x14cec), by native_decide, by native_decide, by native_decide⟩

private theorem allocatorPcNotExit (pc : BitVec 64)
    (literal : pc = 0x14ccc ∨ pc = 0x14cd0 ∨ pc = 0x14cd4 ∨ pc = 0x14cd8 ∨
      pc = 0x14cdc ∨ pc = 0x14ce0 ∨ pc = 0x14ce4 ∨ pc = 0x14ce8) :
    ¬ pcInList Elflings.allocatorGetExitPcs pc := by
  rcases literal with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold pcInList <;> native_decide

private theorem liftAllocatorTrace (template : EndpointState) {fromStep count before after}
    (trace : ScopedTrace (pcInRanges Elflings.allocatorGetExecutionPcRanges)
      (pcInList Elflings.allocatorGetExitPcs) (fun _ _ _ _ _ => False)
      fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.allocatorGetExecutionPcRanges)
      fromStep count { template with machine := before } { template with machine := after } := by
  induction trace with
  | exitAt fromStep state pc atPc exitPc => exact .refl fromStep { template with machine := state }
  | ownStep fromStep count pc before middle after atPc inside notExit machineStep rest ih =>
      refine ConfinedTrace.step fromStep count pc
        { template with machine := before } { template with machine := middle }
        { template with machine := after } atPc inside ?_ ih
      exact endpointStep_sail fromStep { template with machine := before } middle
        (fun observed observedPc => by
          change before.regs.get? PC = some observed at observedPc
          rw [atPc] at observedPc
          cases Option.some.inj observedPc
          rcases inside with ⟨range, member, lower, upper⟩
          simp [Elflings.allocatorGetExecutionPcRanges] at member
          subst range
          simp [BareMetalHostTransitionPc, readContextReturnPc, writeContextReturnPc,
            exitContextStorePc]
          omega) machineStep
  | childBody fromStep used count child before middle after body rest ih => exact body.elim
  | inlineStep fromStep used count boundary program parent child before resume after transfer rest ih =>
      exact transfer.body.elim
  | inlineCallStep fromStep childUsed calleeUsed count boundary program parent child callee before
      resume after transfer rest ih => exact transfer.body.elim
  | callStep fromStep used count call program parent callee before resume after transfer rest ih =>
      exact transfer.body.elim

private theorem allocatorLoadedOfSeg {args : AllocatorGetArgs} {kv a n base cur pc}
    (notFile : ∀ address, args.stackPointer + 0x10 ≤ address →
      address < args.stackPointer + 0x20 → Artifacts.programImage.readFileByte? address = none)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (seg : Seg (pcInRanges Elflings.allocatorGetExecutionPcRanges)
      (pcInList Elflings.allocatorGetExitPcs) (fun _ _ _ _ _ => False)
      allocatorWrites (allocatorMemory args) kv a n base cur pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
  intro address byte fileByte
  have outside : ¬allocatorMemory args address := by
    intro inside
    unfold allocatorMemory Region.union byteRange at inside
    have none := notFile address (by omega) (by omega)
    rw [fileByte] at none
    cases none
  exact (seg.mem address outside).trans (loaded address byte fileByte)

/-- The exact eight parent-owned instructions implement the allocator-get Level 1 contract. -/
theorem allocatorGetInstanceContract : AllocatorGetInstanceContract := by
  refine ⟨fun _ => 8, (by intro _ _; simp [level1ContractFuel]), ?_⟩
  intro args fromStep before entry
  have entryCopy := entry
  rcases entry with ⟨returnPc, atPc, stackRead, aligned, fits, pointerRep, sizeRep, savedRep,
    inputRep, pointerPma, sizePma, pointerMMIO, sizeMMIO, statePma, vtablePma,
    stateMMIO, vtableMMIO, inputOutside, notFile, loaded, configured⟩
  obtain ⟨retired0, retiredRead0⟩ := configured.retiredCounter
  have seg0 := Seg.nil (pcInRanges Elflings.allocatorGetExecutionPcRanges)
    (pcInList Elflings.allocatorGetExitPcs) allocatorWrites (allocatorMemory args) fromStep
    (childSummary := fun _ _ _ _ _ => False) ⟨retired0, retiredRead0⟩ atPc
  have seg0 := seg0.know x2 (BitVec.ofNat 64 args.stackPointer) stackRead
  obtain ⟨r1, run1⟩ := allocatorStateBaseHighStep fromStep before.machine configured atPc loaded
  obtain ⟨s1, seg1⟩ := seg0.step (allocatorPcInside 0x14ccc (Or.inl rfl))
    (allocatorPcNotExit 0x14ccc (Or.inl rfl)) x10 0x24019ccc 0x14cd0 ⟨r1, run1⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have cfg1 := configured.mono (seg1.agree instructionPreserved_disjoint_allocatorWrites) seg1.retired
  have code1 := allocatorLoadedOfSeg notFile loaded seg1
  obtain ⟨r2, run2⟩ := allocatorVtableBaseHighStep (fromStep + 1) s1 cfg1 seg1.atPc code1
  obtain ⟨s2, seg2⟩ := seg1.step (allocatorPcInside 0x14cd0 (Or.inr (Or.inl rfl)))
    (allocatorPcNotExit 0x14cd0 (Or.inr (Or.inl rfl))) x11 0x17cd0 0x14cd4 ⟨r2, run2⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inl rfl)))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have cfg2 := configured.mono (seg2.agree instructionPreserved_disjoint_allocatorWrites) seg2.retired
  have code2 := allocatorLoadedOfSeg notFile loaded seg2
  have sizeRep2 := sizeRep.of_writesOnlyWithin seg2.mem (by
    intro index bound inside
    unfold allocatorMemory Region.union byteRange at inside
    omega)
  obtain ⟨r3, run3⟩ := allocatorLoadInputSizeStep (fromStep + 2) s2 args.stackPointer
    args.input.size cfg2 seg2.atPc (seg2.reg x2 _ (by simp)) sizeRep2
    (loadPmaAllows_of_agree (seg2.agree platformPreserved_disjoint_allocatorWrites) sizePma)
    sizeMMIO aligned fits code2
  obtain ⟨s3, seg3⟩ := seg2.step (allocatorPcInside 0x14cd4 (Or.inr (Or.inr (Or.inl rfl))))
    (allocatorPcNotExit 0x14cd4 (Or.inr (Or.inr (Or.inl rfl)))) x13
    (BitVec.ofNat 64 args.input.size) 0x14cd8 ⟨r3, run3⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have cfg3 := configured.mono (seg3.agree instructionPreserved_disjoint_allocatorWrites) seg3.retired
  have code3 := allocatorLoadedOfSeg notFile loaded seg3
  have pointerRep3 := pointerRep.of_writesOnlyWithin seg3.mem (by
    intro index bound inside
    unfold allocatorMemory Region.union byteRange at inside
    omega)
  obtain ⟨r4, run4⟩ := allocatorLoadInputAddressStep (fromStep + 3) s3 args.stackPointer
    args.inputAddress cfg3 seg3.atPc (seg3.reg x2 _ (by simp)) pointerRep3
    (loadPmaAllows_of_agree (seg3.agree platformPreserved_disjoint_allocatorWrites) pointerPma)
    pointerMMIO aligned fits code3
  obtain ⟨s4, seg4⟩ := seg3.step
    (allocatorPcInside 0x14cd8 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (allocatorPcNotExit 0x14cd8 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) x12
    (BitVec.ofNat 64 args.inputAddress) 0x14cdc ⟨r4, run4⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have seg4' := seg4.forget (kv' :=
    [⟨x12, BitVec.ofNat 64 args.inputAddress⟩, ⟨x13, BitVec.ofNat 64 args.input.size⟩,
      ⟨x11, 0x17cd0⟩, ⟨x2, BitVec.ofNat 64 args.stackPointer⟩]) (by simp)
  have cfg4 := configured.mono (seg4.agree instructionPreserved_disjoint_allocatorWrites) seg4.retired
  have code4 := allocatorLoadedOfSeg notFile loaded seg4
  obtain ⟨r5, run5⟩ := allocatorStateBaseLowStep (fromStep + 4) s4 cfg4 seg4.atPc
    (seg4.reg x10 0x24019ccc (by simp)) code4
  obtain ⟨s5, seg5⟩ := seg4'.step
    (allocatorPcInside 0x14cdc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (allocatorPcNotExit 0x14cdc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    x10 (BitVec.ofNat 64 0x2401a0b0) 0x14ce0 ⟨r5, run5⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have seg5' := seg5.forget (kv' :=
    [⟨x10, BitVec.ofNat 64 0x2401a0b0⟩, ⟨x12, BitVec.ofNat 64 args.inputAddress⟩,
      ⟨x13, BitVec.ofNat 64 args.input.size⟩, ⟨x2, BitVec.ofNat 64 args.stackPointer⟩]) (by simp)
  have cfg5 := configured.mono (seg5.agree instructionPreserved_disjoint_allocatorWrites) seg5.retired
  have code5 := allocatorLoadedOfSeg notFile loaded seg5
  obtain ⟨r6, run6⟩ := allocatorVtableBaseLowStep (fromStep + 5) s5 cfg5 seg5.atPc
    (seg5.reg x11 0x17cd0 (by simp)) code5
  obtain ⟨s6, seg6⟩ := seg5'.step
    (allocatorPcInside 0x14ce0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (allocatorPcNotExit 0x14ce0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    x11 (BitVec.ofNat 64 Elflings.allocatorVtableAddress) 0x14ce4 ⟨r6, run6⟩
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inl rfl)))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have cfg6 := configured.mono (seg6.agree instructionPreserved_disjoint_allocatorWrites) seg6.retired
  have code6 := allocatorLoadedOfSeg notFile loaded seg6
  obtain ⟨r7, run7⟩ := allocatorStoreStateStep (fromStep + 6) s6 args.stackPointer cfg6
    seg6.atPc (seg6.reg x2 _ (by simp)) (seg6.reg x10 _ (by simp))
    (storePmaAllows_of_agree (seg6.agree platformPreserved_disjoint_allocatorWrites) statePma)
    stateMMIO aligned fits code6
  obtain ⟨_, s7, s7Eq, seg7⟩ := seg6.stepStoreWitness
    (args.stackPointer + 0x10) (BitVec.ofNat 64 0x2401a0b0) 0x14ce8
    (allocatorPcInside 0x14ce4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (allocatorPcNotExit 0x14ce4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    ⟨r7, run7⟩ (by decide) (by intro address lower upper; exact Or.inl ⟨lower, upper⟩)
    (by intro r h; exact Or.inl h) (by simp [RegsOutside, stepBookkeeping])
  have cfg7 := configured.mono (seg7.agree instructionPreserved_disjoint_allocatorWrites) seg7.retired
  have code7 := allocatorLoadedOfSeg notFile loaded seg7
  obtain ⟨r8, run8⟩ := allocatorStoreVtableStep (fromStep + 7) s7 args.stackPointer cfg7
    seg7.atPc (seg7.reg x2 _ (by simp)) (seg7.reg x11 _ (by simp))
    (storePmaAllows_of_agree (seg7.agree platformPreserved_disjoint_allocatorWrites) vtablePma)
    vtableMMIO aligned fits code7
  obtain ⟨_, s8, s8Eq, seg8⟩ := seg7.stepStoreWitness (args.stackPointer + 0x18)
    (BitVec.ofNat 64 Elflings.allocatorVtableAddress) 0x14cec
    (allocatorPcInside 0x14ce8 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
    (allocatorPcNotExit 0x14ce8 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
    ⟨r8, run8⟩ (by decide) (by intro address lower upper; exact Or.inr ⟨lower, upper⟩)
    (by intro r h; exact Or.inl h) (by simp [RegsOutside, stepBookkeeping])
  let after : EndpointState := { before with machine := s8 }
  have trace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.allocatorGetExecutionPcRanges) fromStep 8 before after := by
    have machineTrace : ScopedTrace (pcInRanges Elflings.allocatorGetExecutionPcRanges)
        (pcInList Elflings.allocatorGetExitPcs) (fun _ _ _ _ _ => False)
        fromStep 8 before.machine s8 := by
      simpa using seg8.confined 0 s8 (.exitAt _ _ 0x14cec seg8.atPc (by
        unfold pcInList
        native_decide))
    simpa [after] using liftAllocatorTrace before machineTrace
  have returnEq : args.returnAddress = 0x14cec := by
    simpa [Elflings.allocatorGetExitPcs] using returnPc
  have finalPc : s8.regs.get? PC = some (BitVec.ofNat 64 args.returnAddress) := by
    rw [returnEq]
    exact seg8.atPc
  refine ⟨8, after, ⟨0x2401a0b0, Elflings.allocatorVtableAddress⟩, by omega,
    Nat.le_refl 8, trace, ⟨0x14cec, seg8.atPc, by unfold pcInList; native_decide⟩, trivial, ?_⟩
  refine ⟨rfl, finalPc, seg8.reg x2 _ (by simp), seg8.reg x10 _ (by simp),
    seg8.reg x11 _ (by simp), seg8.reg x12 _ (by simp), seg8.reg x13 _ (by simp), ?_⟩
  have pointerAfter : UIntRep 8 s8.mem args.stackPointer args.inputAddress :=
    pointerRep.of_writesOnlyWithin seg8.mem (by
      intro index bound inside
      unfold allocatorMemory Region.union byteRange at inside
      rcases inside with inside | inside <;> omega)
  have sizeAfter : UIntRep 8 s8.mem (args.stackPointer + 8) args.input.size :=
    sizeRep.of_writesOnlyWithin seg8.mem (by
      intro index bound inside
      unfold allocatorMemory Region.union byteRange at inside
      rcases inside with inside | inside <;> omega)
  have stateRep7 : UIntRep 8 s7.mem (args.stackPointer + 0x10) 0x2401a0b0 := by
    rw [s7Eq]
    simpa [tryStepStoreAfterRetired, tryStepStoreAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement s6) 0x14ce4)
        (args.stackPointer + 0x10) 0x2401a0b0 (by native_decide) (by omega)
  have secondWrites : WritesOnlyWithin (byteRange (args.stackPointer + 0x18) 8) s7 s8 := by
    intro address outside
    rw [s8Eq]
    exact storeRetirement_mem_writes s7 0x14ce8 0x14cec r8
      (args.stackPointer + 0x18) (BitVec.ofNat 64 Elflings.allocatorVtableAddress) address outside
  have stateAfter : UIntRep 8 s8.mem (args.stackPointer + 0x10) 0x2401a0b0 :=
    stateRep7.of_writesOnlyWithin secondWrites (by
      intro index bound inside
      unfold byteRange at inside
      omega)
  have vtableAfter : UIntRep 8 s8.mem (args.stackPointer + 0x18)
      Elflings.allocatorVtableAddress := by
    rw [s8Eq]
    simpa [tryStepStoreAfterRetired, tryStepStoreAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement s7) 0x14ce8)
        (args.stackPointer + 0x18) Elflings.allocatorVtableAddress
        (by native_decide) (by omega)
  have savedAfter : UIntRep 8 s8.mem (args.stackPointer + 0x378) args.savedReturnAddress :=
    savedRep.of_writesOnlyWithin seg8.mem (by
      intro index bound inside
      unfold allocatorMemory Region.union byteRange at inside
      rcases inside with inside | inside <;> omega)
  have inputAfter : BytesRep s8.mem args.inputAddress args.input := by
    refine ⟨inputRep.1, ?_⟩
    intro index bound
    exact (seg8.mem (args.inputAddress + index) (by
      intro inside
      unfold allocatorMemory Region.union byteRange at inside
      rcases inside with inside | inside
      · exact inputOutside.elim (fun lower => by omega) (fun upper => by omega)
      · exact inputOutside.elim (fun lower => by omega) (fun upper => by omega))).trans
        (inputRep.2 index bound)
  have code8 := allocatorLoadedOfSeg notFile loaded seg8
  have nonRegister : NonRegisterFrame before.machine s8 := by
    simpa [NonRegisterFrame, AuxStateAgree] using seg8.aux
  exact ⟨pointerAfter, sizeAfter, stateAfter, vtableAfter, savedAfter, inputAfter, seg8.mem,
    rfl, rfl, rfl, rfl,
    ⟨seg8.agree (by
        intro register preserved written
        rcases written with bookkeeping | rfl | rfl | rfl | rfl
        · rcases bookkeeping with rfl | rfl | rfl | rfl <;>
            simp [abiCalleePreserved] at preserved
        all_goals simp [abiCalleePreserved] at preserved),
      seg8.retired, code8, nonRegister.1, nonRegister.2.1, nonRegister.2.2⟩⟩

/-- The seven ordinary instructions plus the observed return implement bare-metal `read_input`. -/
theorem readInputInstanceContract : ReadInputInstanceContract := by
  refine ⟨fun _ => 8, (by intro _ _; simp [level1ContractFuel]), ?_⟩
  intro args fromStep before entry
  have entryCopy := entry
  rcases entry with ⟨returnPc, inputBound, stdin, cursor, atPc, link, bufferReg, sizeReg,
    sizeEq, aligned, fits, inputRep, contextRep, savedRep, bufferPma, sizePma, contextPma,
    bufferMMIO, sizeMMIO, inputOutside, contextOutside, savedOutside, notFile, loaded,
    configured⟩
  obtain ⟨retired0, retiredRead0⟩ := configured.retiredCounter
  have seg0 := Seg.nil (pcInRanges Elflings.readInputExecutionPcRanges)
    (pcInList Elflings.readInputExitPcs) readInputWrites (readInputMemory args) fromStep
    (childSummary := fun _ _ _ _ _ => False) ⟨retired0, retiredRead0⟩ atPc
  have seg0 := seg0.know x1 (BitVec.ofNat 64 args.returnAddress) link
  have seg0 := seg0.know x10 (BitVec.ofNat 64 args.bufferSlot) bufferReg
  have seg0 := seg0.know x11 (BitVec.ofNat 64 args.sizeSlot) sizeReg
  obtain ⟨retired1, run1⟩ :=
    readInputBufferBaseHighStep fromStep before.machine configured atPc loaded
  let state1 := afterRegisterWrite before.machine 0x10140 retired1 x5 0x2001a140
  have seg1 := seg0.stepKnown
    (readInputPcInside 0x10140 (Or.inl rfl))
    (readInputPcNotExit 0x10140 (Or.inl rfl)) x5 0x2001a140 0x10144
    retired1 run1
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping, RegSet.union, RegSet.only])
  have configured1 := configured.mono
    (seg1.agree instructionPreserved_disjoint_readInputWrites) seg1.retired
  have loaded1 := readInput_code_of_seg args entryCopy seg1
  have seg1' := seg1.forget (kv' :=
    [⟨x11, BitVec.ofNat 64 args.sizeSlot⟩, ⟨x10, BitVec.ofNat 64 args.bufferSlot⟩,
      ⟨x1, BitVec.ofNat 64 args.returnAddress⟩]) (by simp)
  obtain ⟨retired2, run2⟩ := readInputBufferBaseLowStep (fromStep + 1) state1 configured1 seg1.atPc
    (seg1.reg x5 0x2001a140 (by simp)) loaded1
  let state2 := afterRegisterWrite state1 0x10144 retired2 x5 Elflings.inputBufferAddress
  have seg2 := seg1'.stepKnown
    (readInputPcInside 0x10144 (Or.inr (Or.inl rfl)))
    (readInputPcNotExit 0x10144 (Or.inr (Or.inl rfl))) x5 Elflings.inputBufferAddress 0x10148
    retired2 run2
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping, RegSet.union, RegSet.only])
  have configured2 := configured.mono
    (seg2.agree instructionPreserved_disjoint_readInputWrites) seg2.retired
  have loaded2 := readInput_code_of_seg args entryCopy seg2
  have bufferPma2 := storePmaAllows_of_agree
    (seg2.agree platformPreserved_disjoint_readInputWrites) bufferPma
  obtain ⟨retired3, run3⟩ := readInputStorePointerStep (fromStep + 2) state2 args.bufferSlot configured2
    seg2.atPc (seg2.reg x10 (BitVec.ofNat 64 args.bufferSlot) (by simp))
    (seg2.reg x5 (BitVec.ofNat 64 Elflings.inputBufferAddress) (by simp)) aligned fits
    bufferPma2 bufferMMIO loaded2
  let state3 := tryStepStoreAfterRetired
    (afterWriteBytes (width := 8)
      (coreStoreNextState (tryStepStoreAfterIncrement state2) 0x10148)
      args.bufferSlot (BitVec.ofNat 64 Elflings.inputBufferAddress)) 0x10148 retired3
  have seg3 := seg2.stepStoreKnown args.bufferSlot
    (BitVec.ofNat 64 Elflings.inputBufferAddress) 0x1014c
    retired3
    (readInputPcInside 0x10148 (Or.inr (Or.inr (Or.inl rfl))))
    (readInputPcNotExit 0x10148 (Or.inr (Or.inr (Or.inl rfl))))
    run3
    (by decide)
    (by intro address lower upper; exact Or.inl ⟨lower, upper⟩)
    (by intro r h; exact Or.inl h)
    (by simp [RegsOutside, stepBookkeeping, RegSet.union, RegSet.only])
  have configured3 := configured.mono
    (seg3.agree instructionPreserved_disjoint_readInputWrites) seg3.retired
  have loaded3 := readInput_code_of_seg args entryCopy seg3
  have seg3' := seg3.forget (kv' :=
    [⟨x11, BitVec.ofNat 64 args.sizeSlot⟩, ⟨x10, BitVec.ofNat 64 args.bufferSlot⟩,
      ⟨x1, BitVec.ofNat 64 args.returnAddress⟩]) (by simp)
  obtain ⟨retired4, run4⟩ :=
    readInputContextBaseHighStep (fromStep + 3) state3 configured3 seg3.atPc loaded3
  let state4 := afterRegisterWrite state3 0x1014c retired4 x5 0x2401a14c
  have seg4 := seg3'.stepKnown
    (readInputPcInside 0x1014c (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (readInputPcNotExit 0x1014c (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    x5 0x2401a14c 0x10150
    retired4 run4
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping, RegSet.union, RegSet.only])
  have configured4 := configured.mono
    (seg4.agree instructionPreserved_disjoint_readInputWrites) seg4.retired
  have loaded4 := readInput_code_of_seg args entryCopy seg4
  have seg4' := seg4.forget (kv' :=
    [⟨x11, BitVec.ofNat 64 args.sizeSlot⟩, ⟨x10, BitVec.ofNat 64 args.bufferSlot⟩,
      ⟨x1, BitVec.ofNat 64 args.returnAddress⟩]) (by simp)
  obtain ⟨retired5, run5⟩ := readInputContextBaseLowStep (fromStep + 4) state4 configured4 seg4.atPc
    (seg4.reg x5 0x2401a14c (by simp)) loaded4
  let state5 := afterRegisterWrite state4 0x10150 retired5 x5 Elflings.ioContextAddress
  have seg5 := seg4'.stepKnown
    (readInputPcInside 0x10150 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (readInputPcNotExit 0x10150 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    x5 Elflings.ioContextAddress 0x10154
    retired5 run5
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping, RegSet.union, RegSet.only])
  have configured5 := configured.mono
    (seg5.agree instructionPreserved_disjoint_readInputWrites) seg5.retired
  have loaded5 := readInput_code_of_seg args entryCopy seg5
  have contextRep5 : UIntRep 8 state5.mem Elflings.ioContextAddress args.input.size :=
    contextRep.of_writesOnlyWithin seg5.mem (by
      intro index bound inside
      unfold readInputMemory Region.union byteRange at inside
      rcases inside with inside | inside
      · exact contextOutside.elim (fun h => by omega) (fun h => by omega)
      · exact contextOutside.elim (fun h => by omega) (fun h => by omega))
  have contextPma5 := loadPmaAllows_of_agree
    (seg5.agree platformPreserved_disjoint_readInputWrites) contextPma
  obtain ⟨retired6, run6⟩ := readInputLoadSizeStep (fromStep + 5) state5 args.input.size configured5
    seg5.atPc (seg5.reg x5 (BitVec.ofNat 64 Elflings.ioContextAddress) (by simp)) contextRep5
    contextPma5 loaded5
  let state6 := afterRegisterWrite state5 0x10154 retired6 x6 (BitVec.ofNat 64 args.input.size)
  have seg6 := seg5.stepKnown
    (readInputPcInside 0x10154 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (readInputPcNotExit 0x10154
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    x6 (BitVec.ofNat 64 args.input.size) 0x10158
    retired6 run6
    (by decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping, RegSet.union, RegSet.only])
  have configured6 := configured.mono
    (seg6.agree instructionPreserved_disjoint_readInputWrites) seg6.retired
  have loaded6 := readInput_code_of_seg args entryCopy seg6
  have sizePma6 := storePmaAllows_of_agree
    (seg6.agree platformPreserved_disjoint_readInputWrites) sizePma
  have sizeAligned : args.sizeSlot % 8 = 0 := by omega
  have sizeFits : args.sizeSlot + 8 < 2 ^ 64 := by omega
  obtain ⟨retired7, run7⟩ := readInputStoreSizeStep (fromStep + 6) state6 args.sizeSlot args.input.size
    configured6 seg6.atPc (seg6.reg x11 (BitVec.ofNat 64 args.sizeSlot) (by simp))
    (seg6.reg x6 (BitVec.ofNat 64 args.input.size) (by simp)) sizeAligned sizeFits sizePma6 sizeMMIO
    loaded6
  let state7 := tryStepStoreAfterRetired
    (afterWriteBytes (width := 8)
      (coreStoreNextState (tryStepStoreAfterIncrement state6) 0x10158)
      args.sizeSlot (BitVec.ofNat 64 args.input.size)) 0x10158 retired7
  have seg7 := seg6.stepStoreKnown args.sizeSlot
    (BitVec.ofNat 64 args.input.size) 0x1015c
    retired7
    (readInputPcInside 0x10158 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
    (readInputPcNotExit 0x10158
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
    run7
    (by decide)
    (by intro address lower upper; exact Or.inr ⟨by omega, by simpa [sizeEq] using upper⟩)
    (by intro r h; exact Or.inl h)
    (by simp [RegsOutside, stepBookkeeping, RegSet.union, RegSet.only])
  have frame7 : NonRegisterFrame before.machine state7 :=
    ((((((nonRegisterFrame_afterRegisterWrite before.machine 0x10140 retired1 x5
      0x2001a140).trans
      (nonRegisterFrame_afterRegisterWrite state1 0x10144 retired2 x5
        (BitVec.ofNat 64 Elflings.inputBufferAddress))).trans
      (nonRegisterFrame_afterStore state2 0x10148 retired3 args.bufferSlot
        (BitVec.ofNat 64 Elflings.inputBufferAddress))).trans
      (nonRegisterFrame_afterRegisterWrite state3 0x1014c retired4 x5 0x2401a14c)).trans
      (nonRegisterFrame_afterRegisterWrite state4 0x10150 retired5 x5
        (BitVec.ofNat 64 Elflings.ioContextAddress))).trans
      (nonRegisterFrame_afterRegisterWrite state5 0x10154 retired6 x6
        (BitVec.ofNat 64 args.input.size))).trans
      (nonRegisterFrame_afterStore state6 0x10158 retired7 args.sizeSlot
        (BitVec.ofNat 64 args.input.size))
  have configured7 := configured.mono
    (seg7.agree instructionPreserved_disjoint_readInputWrites) seg7.retired
  have loaded7 := readInput_code_of_seg args entryCopy seg7
  have returnEq : args.returnAddress = 0x14ccc := by
    simpa [Elflings.readInputExitPcs] using returnPc
  have targetAligned : Sail.BitVec.access (BitVec.ofNat 64 args.returnAddress) 1 = 0#1 := by
    rw [returnEq]
    native_decide
  obtain ⟨retired8, run8⟩ := configuredRetStep (fromStep + 7) 0x1015c state7
    (BitVec.ofNat 64 args.returnAddress) configured7 seg7.atPc
    (seg7.reg x1 (BitVec.ofNat 64 args.returnAddress) (by simp)) targetAligned loaded7
  have targetEq : Sail.BitVec.update (BitVec.ofNat 64 args.returnAddress) 0 0#1 =
      BitVec.ofNat 64 args.returnAddress := by
    rw [returnEq]
    native_decide
  let state8 := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state7) 0x1015c
      (Sail.BitVec.update (BitVec.ofNat 64 args.returnAddress) 0 0#1))
      (Sail.BitVec.update (BitVec.ofNat 64 args.returnAddress) 0 0#1) retired8
  let after : EndpointState :=
    { machine := state8, stdin := before.stdin, stdinCursor := args.input.size,
      stdout := before.stdout, exitCode := before.exitCode }
  have frame8 : NonRegisterFrame before.machine state8 := frame7.trans
    (nonRegisterFrame_afterJump state7 0x1015c
      (Sail.BitVec.update (BitVec.ofNat 64 args.returnAddress) 0 0#1) retired8)
  have finalPc : state8.regs.get? PC = some (BitVec.ofNat 64 args.returnAddress) := by
    simp [state8, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, Std.ExtDHashMap.get?_insert, targetEq]
  have inputRep7 : BytesRep state7.mem Elflings.inputBufferAddress args.input := by
    refine ⟨inputRep.1, ?_⟩
    intro index bound
    exact (seg7.mem (Elflings.inputBufferAddress + index) (by
      intro inside
      unfold readInputMemory Region.union byteRange at inside
      rcases inside with inside | inside
      · exact inputOutside.elim (fun h => by omega) (fun h => by omega)
      · exact inputOutside.elim (fun h => by omega) (fun h => by omega))).trans
        (inputRep.2 index bound)
  have stdinSize : before.stdin.size = args.input.size := congrArg Array.size stdin
  have readStep : BareMetalReadStep (fromStep + 7)
      { before with machine := state7 } after := by
    exact ⟨seg7.atPc, by simpa [stdin] using inputRep7, run8, rfl,
      by simpa [after] using stdinSize.symm, rfl, rfl⟩
  have tracePrefix : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.readInputExecutionPcRanges) fromStep 7 before
      { before with machine := state7 } := by
    have t1 := readInputConfinedSailStep fromStep before state1 0x10140 (Or.inl rfl) atPc
      run1
    have t2 := readInputConfinedSailStep (fromStep + 1) { before with machine := state1 }
      state2 0x10144 (Or.inr (Or.inl rfl)) seg1.atPc run2
    have t3 := readInputConfinedSailStep (fromStep + 2) { before with machine := state2 }
      state3 0x10148 (Or.inr (Or.inr (Or.inl rfl))) seg2.atPc run3
    have t4 := readInputConfinedSailStep (fromStep + 3) { before with machine := state3 }
      state4 0x1014c (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) seg3.atPc
      run4
    have t5 := readInputConfinedSailStep (fromStep + 4) { before with machine := state4 }
      state5 0x10150 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) seg4.atPc
      run5
    have t6 := readInputConfinedSailStep (fromStep + 5) { before with machine := state5 }
      state6 0x10154 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) seg5.atPc
      run6
    have t7 := readInputConfinedSailStep (fromStep + 6) { before with machine := state6 }
      state7 0x10158 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) seg6.atPc
      run7
    simpa only [Nat.reduceAdd, Nat.add_assoc] using
      (((((t1.append t2).append t3).append t4).append t5).append t6).append t7
  have trace8 : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.readInputExecutionPcRanges) (fromStep + 7) 1
      { before with machine := state7 } after := by
    apply ConfinedTrace.step (fromStep + 7) 0 0x1015c _ after after
    · exact seg7.atPc
    · exact ⟨(0x10140, 0x10190), by native_decide, by native_decide, by native_decide⟩
    · exact .read readStep
    · exact .refl (fromStep + 8) after
  have trace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.readInputExecutionPcRanges) fromStep 8 before after := by
    simpa using tracePrefix.append trace8
  refine ⟨8, after, ⟨Elflings.inputBufferAddress⟩, by omega, Nat.le_refl 8, trace, ?_,
    trivial, ?_⟩
  · refine ⟨BitVec.ofNat 64 args.returnAddress, finalPc, ?_⟩
    rw [returnEq]
    unfold pcInList
    native_decide
  · refine ⟨finalPc, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have pointerRep3 : UIntRep 8 state3.mem args.bufferSlot
          Elflings.inputBufferAddress := by
        simpa [state3, tryStepStoreAfterRetired, tryStepStoreAfterTick] using
          uintRep_afterWriteBytes_eight
            (coreStoreNextState (tryStepStoreAfterIncrement state2) 0x10148)
            args.bufferSlot Elflings.inputBufferAddress (by native_decide) (by omega)
      have middleMem : state6.mem = state3.mem := by
        simp [state6, state5, state4, afterRegisterWrite_mem]
      have storeWrites : WritesOnlyWithin (byteRange args.sizeSlot 8) state6 state7 := by
        intro address outside
        exact storeRetirement_mem_writes state6 0x10158 0x1015c retired7 args.sizeSlot
          (BitVec.ofNat 64 args.input.size) address outside
      have suffixWrites : WritesOnlyWithin (byteRange args.sizeSlot 8) state3 state7 :=
        WritesOnlyWithin.trans_same (writesOnlyWithin_of_mem_eq middleMem) storeWrites
      simpa [state8, jumpRetirement_mem] using pointerRep3.of_writesOnlyWithin suffixWrites (by
        intro index bound inside
        unfold byteRange at inside
        omega)
    · simpa [state8, jumpRetirement_mem, state7, tryStepStoreAfterRetired,
        tryStepStoreAfterTick] using
        uintRep_afterWriteBytes_eight
          (coreStoreNextState (tryStepStoreAfterIncrement state6) 0x10158)
          args.sizeSlot args.input.size (by omega) (by omega)
    · simpa [state8, jumpRetirement_mem] using inputRep7
    · simpa [state8, jumpRetirement_mem] using savedRep.of_writesOnlyWithin seg7.mem (by
        intro index bound inside
        unfold readInputMemory Region.union byteRange at inside
        rcases inside with inside | inside
        · exact savedOutside.elim (fun h => by omega) (fun h => by omega)
        · exact savedOutside.elim (fun h => by omega) (fun h => by omega))
    · simpa [state8, jumpRetirement_mem] using seg7.mem
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro register preserved
        exact (jumpRetirement_writes state7 0x1015c
          (Sail.BitVec.update (BitVec.ofNat 64 args.returnAddress) 0 0#1) retired8).get register (by
            intro written
            exact abiCalleePreserved_disjoint_readInputWrites register preserved (Or.inl written)) |>.trans
            ((seg7.agree abiCalleePreserved_disjoint_readInputWrites) register preserved)
      · exact jumpRetirement_retired_present state7 0x1015c
          (Sail.BitVec.update (BitVec.ofNat 64 args.returnAddress) 0 0#1) retired8
      · change Artifacts.programImage.fileBytesLoadedFaithfully state7.mem
        exact loaded7
      · exact frame8.1
      · exact frame8.2.1
      · exact frame8.2.2

/-- Production `0x101c4: auipc t0, 0x2400a`. -/
theorem zkvmExitLoadContextBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x101c4))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x101c4 retired x5 0x2401a1c4) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  have decode : Runs (ext_decode (fetchWord 0x97 0xa2 0x00 0x24))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0x2400a, .Regidx 5#5, .AUIPC)) := by
    decode_run
  have pcRead : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4)
      0x101c4 := by
    apply readReg_run
    simp [coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (0x2400a, .Regidx 5#5, .AUIPC)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4 with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4).regs.insert
          x5 0x2401a1c4 }
      (.Retire_Success ()) := by
    change Runs (execute_UTYPE 0x2400a (.Regidx 5#5) .AUIPC) _ _ _
    simpa using execute_UTYPE_auipc_run _ _ 0x2400a (.Regidx 5#5) 0x101c4 pcRead
      (wX_x5_run _ 0x2401a1c4)
  exact configuredRegisterWriteStep stepNo 0x101c4 state x5 0x2401a1c4
    (.UTYPE (0x2400a, .Regidx 5#5, .AUIPC)) 0x97 0xa2 0x00 0x24
    configured atPc loaded decode execute (base := by rfl)

/-- Production `0x101c8: addi t0, t0, -268`. -/
theorem zkvmExitFinishContextBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x101c8))
    (baseRead : state.regs.get? x5 = some (BitVec.ofNat 64 0x2401a1c4))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x101c8 retired x5 0x2401a0b8) false := by
  obtain ⟨seccfgBits, seccfgRead, _, privilegeAfter, seccfgAfter⟩ :=
    configured.decodeContext
  have decode : Runs (ext_decode (fetchWord 0x93 0x82 0x42 0xef))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0xef4, .Regidx 5#5, .Regidx 5#5, .ADDI)) := by
    decode_run
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c8
  have sourceRead : premise.regs.get? x5 = some (BitVec.ofNat 64 0x2401a1c4) := by
    calc
      premise.regs.get? x5 = state.regs.get? x5 :=
        (stepPremiseState_writes state 0x101c8).get x5 (by decide)
      _ = some (BitVec.ofNat 64 0x2401a1c4) := baseRead
  have execute : Runs (execute (.ITYPE (0xef4, .Regidx 5#5, .Regidx 5#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x5 0x2401a0b8 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0xef4 (.Regidx 5#5) (.Regidx 5#5) .ADDI) _ _ _
    simpa [iTypeResult] using execute_ITYPE_run premise
      { premise with regs := premise.regs.insert x5 0x2401a0b8 }
      0xef4 (.Regidx 5#5) (.Regidx 5#5) .ADDI 0x2401a1c4
      (rX_x5_run premise 0x2401a1c4 sourceRead) (wX_x5_run premise 0x2401a0b8)
  exact configuredRegisterWriteStep stepNo 0x101c8 state x5 0x2401a0b8
    (.ITYPE (0xef4, .Regidx 5#5, .Regidx 5#5, .ADDI)) 0x93 0x82 0x42 0xef
    configured atPc loaded decode execute (base := by rfl)

/-- Production `0x101cc: sd a0, 24(t0)`. -/
theorem zkvmExitStoreCodeStep (stepNo : Nat) (state : State) (code : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x101cc))
    (contextRead : state.regs.get? x5 = some (BitVec.ofNat 64 Elflings.ioContextAddress))
    (codeRead : state.regs.get? x10 = some (BitVec.ofNat 64 code))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)) 8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x101cc)
          (Elflings.ioContextAddress + 24) (BitVec.ofNat 64 code))
        0x101cc retired) false := by
  let premise := coreStoreNextState (tryStepStoreAfterIncrement state) 0x101cc
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state 0x101cc).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise : premise.regs.get? mstatus = some mstatusBits :=
    (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise : premise.regs.get? cur_privilege = some .Machine :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have mseccfgPremise : premise.regs.get? mseccfg = some mseccfgBits :=
    (agree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have contextPremise : premise.regs.get? x5 =
      some (BitVec.ofNat 64 Elflings.ioContextAddress) :=
    (stepPremiseState_writes state 0x101cc).get x5 (by decide) |>.trans contextRead
  have codePremise : premise.regs.get? x10 = some (BitVec.ofNat 64 code) :=
    (stepPremiseState_writes state 0x101cc).get x10 (by decide) |>.trans codeRead
  have contextRun := rX_x5_run premise (BitVec.ofNat 64 Elflings.ioContextAddress) contextPremise
  have codeRun := rX_x10_run premise (BitVec.ofNat 64 code) codePremise
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 5#5) (sign_extend (m := 64) (0x018#12))
        (Store Data) 8) premise premise
      (.Ext_DataAddr_OK (virtaddr.Virtaddr
        (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)))) := by
    simpa using get_transformed_data_addr_machine_data_run .store premise (.Regidx 5#5) 8
      (BitVec.ofNat 64 Elflings.ioContextAddress) (sign_extend (m := 64) (0x018#12))
      mstatusBits mseccfgBits contextRun mstatusPremise privilegePremise mprvZero
      mseccfgPremise pmmDisabled
  have pmaPremise : StorePmaAllows premise
      (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)) 8 :=
    storePmaAllows_of_agree agree pma
  have physical := phys_access_check_machine_store_allowed premise
    (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)) 8
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    pmaPremise (by native_decide)
  have noMMIO := storeMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)) 8
    (by
      unfold StoreMMIOAddressExcluded DataMMIOAddressExcluded
      constructor <;> rfl)
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  let afterWrite := afterWriteBytes (width := 8) premise (Elflings.ioContextAddress + 24)
    (BitVec.ofNat 64 code)
  have access : ConfiguredDwordStoreAccess state afterWrite 0x101cc 0x018
      (.Regidx 5#5) (.Regidx 10#5) :=
    ⟨_, mstatusBits, _, mstatusPremise, privilegePremise, mprvZero, codeRun,
      addressRun, by native_decide, physical, noMMIO,
      writeBytes_run_exact premise (Elflings.ioContextAddress + 24) (BitVec.ofNat 64 code)⟩
  have decode : Runs (ext_decode (fetchWord 0x23 0xbc 0xa2 0x00))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (0x018, .Regidx 10#5, .Regidx 5#5, 8)) := by
    obtain ⟨_, _, _, privilegeAfter, seccfgAfter⟩ :=
      configured.storeDecodeContext
    decode_run
  simpa [afterWrite] using configuredDwordStoreStep stepNo 0x101cc state afterWrite
    0x018 (.Regidx 5#5) (.Regidx 10#5) 0x23 0xbc 0xa2 0x00 configured atPc loaded
    decode access (base := by rfl)

private def zkvmExitWrites : RegSet :=
  RegSet.union stepBookkeeping (RegSet.only x5)

private theorem instructionPreserved_disjoint_zkvmExitWrites :
    RegSet.Disjoint instructionPreserved zkvmExitWrites :=
  (platformPreserved_disjoint.weaken (fun _ preserved => preserved.1)).union
    (RegSet.Disjoint.only (by simp [instructionPreserved, platformPreserved]))

private theorem platformPreserved_disjoint_zkvmExitWrites :
    RegSet.Disjoint platformPreserved zkvmExitWrites :=
  platformPreserved_disjoint.union
    (RegSet.Disjoint.only (by simp [platformPreserved]))

private theorem zkvmExitLoadedOfSeg {fromStep count : Nat} {base after : State}
    {kv : List RegVal} {pc : BitVec 64}
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (seg : Seg ZkvmExitExecutionPc
      (pcInList Elflings.zkvmExitExitPcs) (fun _ _ _ _ _ => False)
      zkvmExitWrites (fun _ => False) kv fromStep count base after pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
  simpa [seg.memEq (by simp)] using loaded

private theorem zkvmExitPcInside (pc : BitVec 64)
    (literal : pc = 0x101c4 ∨ pc = 0x101c8 ∨ pc = 0x101cc) :
    ZkvmExitExecutionPc pc := by
  rcases literal with rfl | rfl | rfl <;>
    exact ⟨⟨(0x101c4, 0x101d4), by native_decide, by native_decide, by native_decide⟩,
      by native_decide⟩

private theorem zkvmExitPcNotExit (pc : BitVec 64)
    (literal : pc = 0x101c4 ∨ pc = 0x101c8 ∨ pc = 0x101cc) :
    ¬ pcInList Elflings.zkvmExitExitPcs pc := by
  rcases literal with rfl | rfl | rfl <;> unfold pcInList <;> native_decide

private theorem zkvmExitPcNotObserved (pc : BitVec 64)
    (literal : pc = 0x101c4 ∨ pc = 0x101c8) :
    ¬ BareMetalHostTransitionPc pc := by
  rcases literal with rfl | rfl <;>
    simp only [BareMetalHostTransitionPc] <;> native_decide

private theorem zkvmExitConfinedSailStep (stepNo : Nat) (before : EndpointState)
    (after : State) (pc : BitVec 64) (literal : pc = 0x101c4 ∨ pc = 0x101c8)
    (atPc : EndpointPc before = some pc) (step : MachineStep stepNo before.machine after) :
    ConfinedTrace EndpointStep EndpointPc ZkvmExitExecutionPc
      stepNo 1 before { before with machine := after } := by
  apply ConfinedTrace.step stepNo 0 pc before { before with machine := after }
    { before with machine := after }
  · exact atPc
  · exact zkvmExitPcInside pc (literal.elim Or.inl (fun h => Or.inr (Or.inl h)))
  · exact endpointStep_sail stepNo before after (fun target targetPc => by
      rw [atPc] at targetPc
      cases Option.some.inj targetPc
      exact zkvmExitPcNotObserved pc literal) step
  · exact .refl (stepNo + 1) _

private theorem zkvmExitConfinedStoreStep (stepNo : Nat) (before after : EndpointState)
    (step : BareMetalExitStep stepNo before after) :
    ConfinedTrace EndpointStep EndpointPc ZkvmExitExecutionPc
      stepNo 1 before after := by
  rcases step with ⟨code, atPc, codeRead, codeFits, machineStep, stdin, cursor, stdout, exitCode,
    terminal⟩
  apply ConfinedTrace.step stepNo 0 0x101cc before after after
  · exact atPc
  · exact zkvmExitPcInside 0x101cc (Or.inr (Or.inr rfl))
  · exact .exit ⟨code, atPc, codeRead, codeFits, machineStep, stdin, cursor, stdout, exitCode,
      terminal⟩
  · exact .refl (stepNo + 1) _

/-- The bare-metal `zkvm_exit` function implements its Level 1 contract unconditionally. -/
theorem zkvmExitInstanceContract : ZkvmExitInstanceContract := by
  refine ⟨3, (by simp [level1ContractFuel]), ?_⟩
  intro args fromStep before entry
  rcases entry with ⟨atPc, codeRead, codeFits, pma, loaded, configured⟩
  obtain ⟨retired0, retiredRead0⟩ := configured.retiredCounter
  have seg0 := Seg.nil ZkvmExitExecutionPc
    (pcInList Elflings.zkvmExitExitPcs) zkvmExitWrites (fun _ => False) fromStep
    (childSummary := fun _ _ _ _ _ => False) ⟨retired0, retiredRead0⟩ atPc
  have seg0 := seg0.know x10 (BitVec.ofNat 64 args.code) codeRead
  obtain ⟨retired1, run1⟩ := zkvmExitLoadContextBaseStep fromStep before.machine
    configured atPc loaded
  let state1 := afterRegisterWrite before.machine 0x101c4 retired1 x5 0x2401a1c4
  have seg1 := seg0.stepKnown (zkvmExitPcInside 0x101c4 (Or.inl rfl))
    (zkvmExitPcNotExit 0x101c4 (Or.inl rfl)) x5 0x2401a1c4 0x101c8 retired1 run1
    (by decide) (by intro r h; exact Or.inl h) (Or.inr rfl)
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have configured1 : ConfiguredMachinePre EndpointMachinePc state1 :=
    configured.mono (seg1.agree instructionPreserved_disjoint_zkvmExitWrites) seg1.retired
  have loaded1 := zkvmExitLoadedOfSeg loaded seg1
  have seg1' := seg1.forget (kv' := [⟨x10, BitVec.ofNat 64 args.code⟩]) (by simp)
  obtain ⟨retired2, run2⟩ := zkvmExitFinishContextBaseStep (fromStep + 1) state1
    configured1 seg1.atPc (seg1.reg x5 0x2401a1c4 (by simp)) loaded1
  let state2 := afterRegisterWrite state1 0x101c8 retired2 x5 0x2401a0b8
  have seg2 := seg1'.stepKnown (zkvmExitPcInside 0x101c8 (Or.inr (Or.inl rfl)))
    (zkvmExitPcNotExit 0x101c8 (Or.inr (Or.inl rfl))) x5 0x2401a0b8 0x101cc retired2 run2
    (by decide) (by intro r h; exact Or.inl h) (Or.inr rfl)
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have configured2 : ConfiguredMachinePre EndpointMachinePc state2 :=
    configured.mono (seg2.agree instructionPreserved_disjoint_zkvmExitWrites) seg2.retired
  have loaded2 := zkvmExitLoadedOfSeg loaded seg2
  have context2 : state2.regs.get? x5 =
      some (BitVec.ofNat 64 Elflings.ioContextAddress) := by
    simpa [Elflings.ioContextAddress] using seg2.reg x5 0x2401a0b8 (by simp)
  have code2 : state2.regs.get? x10 = some (BitVec.ofNat 64 args.code) := by
    exact seg2.reg x10 (BitVec.ofNat 64 args.code) (by simp)
  have pma2 : StorePmaAllows state2
      (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)) 8 :=
    storePmaAllows_of_agree (seg2.agree platformPreserved_disjoint_zkvmExitWrites) pma
  obtain ⟨retired3, run3⟩ := zkvmExitStoreCodeStep (fromStep + 2) state2 args.code
    configured2 seg2.atPc context2 code2 pma2 loaded2
  let state3 := tryStepStoreAfterRetired
    (afterWriteBytes (width := 8)
      (coreStoreNextState (tryStepStoreAfterIncrement state2) 0x101cc)
      (Elflings.ioContextAddress + 24) (BitVec.ofNat 64 args.code))
    0x101cc retired3
  let state1Endpoint : EndpointState := { before with machine := state1 }
  let state2Endpoint : EndpointState := { before with machine := state2 }
  let after : EndpointState := { before with machine := state3, exitCode := some args.code }
  have trace1 := zkvmExitConfinedSailStep fromStep before state1 0x101c4 (Or.inl rfl)
    atPc run1
  have trace2 := zkvmExitConfinedSailStep (fromStep + 1) state1Endpoint state2 0x101c8
    (Or.inr rfl) seg1.atPc run2
  have finalPc : state3.regs.get? PC =
      some (BitVec.ofNat 64 Elflings.zkvmExitTerminalPc) := by
    simp only [state3, tryStepStoreAfterRetired, tryStepStoreAfterTick]
    rw [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert]
    rw [dif_neg (by decide : (minstret == PC) ≠ true)]
    rw [dif_pos (by decide : (PC == PC) = true)]
    rfl
  have exitStep : BareMetalExitStep (fromStep + 2) state2Endpoint after := by
    exact ⟨args.code, seg2.atPc, code2, codeFits, run3, rfl, rfl, rfl, rfl, finalPc⟩
  have trace3 := zkvmExitConfinedStoreStep (fromStep + 2) state2Endpoint after exitStep
  have trace12 : ConfinedTrace EndpointStep EndpointPc
      ZkvmExitExecutionPc fromStep 2 before state2Endpoint := by
    simpa [state1Endpoint, state2Endpoint] using trace1.append trace2
  have trace : ConfinedTrace EndpointStep EndpointPc
      ZkvmExitExecutionPc fromStep 3 before after := by
    simpa [state2Endpoint] using trace12.append trace3
  refine ⟨3, after, (), by decide, ?_, trace, ?_, trivial, ?_⟩
  · exact Nat.le_refl 3
  · exact ⟨0x101d0, finalPc, by unfold pcInList; native_decide⟩
  · refine ⟨finalPc, rfl, rfl, rfl, rfl, ?_⟩
    have prefixMem : state2.mem = before.machine.mem := by
      exact seg2.memEq (by simp)
    have storeMem : WritesOnlyWithin (byteRange (Elflings.ioContextAddress + 24) 8)
        state2 state3 := by
      intro address outside
      exact storeRetirement_mem_writes state2 0x101cc 0x101d0 retired3
        (Elflings.ioContextAddress + 24) (BitVec.ofNat 64 args.code) address outside
    exact WritesOnlyWithin.trans_same (writesOnlyWithin_of_mem_eq prefixMem) storeMem

end BinaryFv.Zesu.MachineExecution
