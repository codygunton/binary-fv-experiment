import BinaryFv.RiscV.Instruction.Execute.Arithmetic
import BinaryFv.RiscV.Instruction.Execute.Load
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.SentinelAssembly
import BinaryFv.Zesu.MachineExecution.DecodeTactic

/-!
# Concrete Sail execution of `zesu_raw_result`

The compiled function reads the stored-result discriminant and returns either the payload address or
zero.  Its seven non-return instructions are straight-line RV64 code; the function-instance trace
stops at the generated `ret` exit.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary BinaryFv.RiscV
open BinaryFv.Binary.Elfling BinaryFv.RiscV.Elfling
open BinaryFv.Binary.ProgramImage
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Exact post-state of a register-writing fall-through instruction. -/
def afterRegisterWrite (state : State) (pc retired : BitVec 64) (destination : Register)
    (value : RegisterType destination) : State :=
  tryStepControlFlowAfterRetired
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
        destination value }
    (Sail.BitVec.addInt pc 4) retired

theorem afterRegisterWrite_agree {state : State} {pc retired : BitVec 64}
    {destination : Register} {value : RegisterType destination}
    (notPreserved : ¬ platformPreserved destination) :
    Agree platformPreserved state (afterRegisterWrite state pc retired destination value) := by
  intro register preserved
  have different : destination ≠ register := by
    intro equal
    exact notPreserved (equal ▸ preserved)
  have notPc : PC ≠ register := by
    intro equal
    subst register
    simpa [platformPreserved] using preserved
  have notNextPc : nextPC ≠ register := by
    intro equal
    subst register
    simpa [platformPreserved] using preserved
  have notIncrement : minstret_increment ≠ register := by
    intro equal
    subst register
    simpa [platformPreserved] using preserved
  have notRetired : minstret ≠ register := by
    intro equal
    subst register
    simpa [platformPreserved] using preserved
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    different, notPc, notNextPc, notIncrement, notRetired]

theorem afterRegisterWrite_mem (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    (afterRegisterWrite state pc retired destination value).mem = state.mem := rfl

theorem afterRegisterWrite_retired_present (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    RetiredCounterPresent (afterRegisterWrite state pc retired destination value) := by
  refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]

theorem afterRegisterWrite_pc (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    (afterRegisterWrite state pc retired destination value).regs.get? PC =
      some (Sail.BitVec.addInt pc 4) := by
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    Std.ExtDHashMap.get?_insert]

theorem afterRegisterWrite_exitPlatform {state : State} {pc retired : BitVec 64}
    {destination : Register} {value : RegisterType destination} {nextPc : Nat}
    (notPreserved : ¬ platformPreserved destination) (platform : ExitPlatform state nextPc) :
    ExitPlatform (afterRegisterWrite state pc retired destination value) nextPc := by
  have code : Artifacts.programImage.fileBytesMatchMemory
      (afterRegisterWrite state pc retired destination value).mem := by
    simpa [afterRegisterWrite_mem] using platform.code
  exact exitPlatform_of_agree (afterRegisterWrite_agree notPreserved)
    (afterRegisterWrite_retired_present state pc retired destination value) code platform

theorem exitPlatform_of_executionState {before after : State} {pc : Nat}
    (agree : Agree platformPreserved before after) (retired : RetiredCounterPresent after)
    (memoryUnchanged : after.mem = before.mem) (platform : ExitPlatform before pc) :
    ExitPlatform after pc := by
  have code : Artifacts.programImage.fileBytesMatchMemory after.mem := by
    simpa [memoryUnchanged] using platform.code
  exact exitPlatform_of_agree agree retired code platform

/-- Derive all common machine premises for one register-writing straight-line instruction. -/
theorem fallThroughRegisterWriteStep (stepNo pcNat : Nat) (state : State)
    (byte0 byte1 byte2 byte3 : BitVec 8) (instruction : instruction)
    (destination : Register) (value : RegisterType destination)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pcNat))
    (platform : ExitPlatform state pcNat)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat)
      byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) instruction)
    (execute : Runs (execute instruction)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pcNat) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 pcNat)).regs.insert destination value }
      (.Retire_Success ()))
    (addressExcluded : FetchMMIOAddressExcluded (BitVec.ofNat 64 pcNat))
    (aligned : (BitVec.ofNat 64 pcNat).toNat % 4 = 0)
    (destinationNotNextPc : destination ≠ nextPC)
    (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pcNat) retired destination value) false := by
  obtain ⟨hartRead, privilege, satpRead, midelegRead, mieRead, mipRead, pmpcfgRead,
    pmpaddrRead, inhibitRead, configRead, elpRead, misaCase⟩ := platform.normal
  obtain ⟨mstatusBits, mstatusRead⟩ := platform.mstatusRead
  obtain ⟨retired, retiredRead⟩ := platform.retired
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have fetchPlatform : FetchBasePlatform (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 pcNat) :=
    fetchBasePlatform_of_offPC
      (pc_afterIncrement state (BitVec.ofNat 64 pcNat) atPc)
      (fetchBasePlatformOffPC_of_normal incrementNormal
        ((platformPreserved_mstatus incrementAgree).trans mstatusRead) aligned
        (fetchPmaAllows_of_agree incrementAgree platform.pmaAllows))
  have noMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 pcNat) :=
    fetchMemoryNoMMIO_of_state_layout_excluded _ _
      ⟨addressExcluded, (platformPreserved_htifBase incrementAgree).trans platform.htifRead⟩
  have interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state) :=
    interruptDisabled_of_normal incrementNormal
      ((platformPreserved_mstatus incrementAgree).trans mstatusRead)
      (platform.meipRead.imp fun _ read => (platformPreserved_sigMeip incrementAgree).trans read)
  have notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state) :=
    landingPadNotExpected_of_normal incrementNormal
  refine ⟨retired, ?_⟩
  exact tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 pcNat) retired 0 0
    byte0 byte1 byte2 byte3 instruction destination value fetchPlatform noMMIO bytes interrupts
    base decode notExpected execute destinationNotNextPc destinationNotHart
    destinationNotIncrement destinationNotRetired
    hartRead inhibitRead configRead (by decide) (by decide) retiredRead

theorem fetchFileInstruction (state : State) (pc : Nat)
    (byte0 byte1 byte2 byte3 : UInt8)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem)
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3)
    (fits : pc < 2 ^ 64) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
      (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
      (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) := by
  have loadedAfter : Artifacts.programImage.fileBytesMatchMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc fits loadedAfter byte0 byte1 byte2 byte3
    read0 read1 read2 read3

theorem raw_result_auipc_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1378c)
      0x17#8 0x25#8 0x20#8 0x04#8 :=
  fetchFileInstruction state 0x1378c 0x17 0x25 0x20 0x04 loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem raw_result_base_add_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13790)
      0x13#8 0x05#8 0x45#8 0x89#8 :=
  fetchFileInstruction state 0x13790 0x13 0x05 0x45 0x89 loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem raw_result_discriminant_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13794)
      0x83#8 0x45#8 0x05#8 0x35#8 :=
  fetchFileInstruction state 0x13794 0x83 0x45 0x05 0x35 loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem raw_result_payload_add_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13798)
      0x13#8 0x05#8 0x05#8 0x01#8 :=
  fetchFileInstruction state 0x13798 0x13 0x05 0x05 0x01 loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem raw_result_seqz_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1379c)
      0x93#8 0xb5#8 0x15#8 0x00#8 :=
  fetchFileInstruction state 0x1379c 0x93 0xb5 0x15 0x00 loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem raw_result_mask_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x137a0)
      0x93#8 0x85#8 0xf5#8 0xff#8 :=
  fetchFileInstruction state 0x137a0 0x93 0x85 0xf5 0xff loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem raw_result_select_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x137a4)
      0x33#8 0xf5#8 0xa5#8 0x00#8 :=
  fetchFileInstruction state 0x137a4 0x33 0xf5 0xa5 0x00 loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem raw_result_auipc_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x17#8 0x25#8 0x20#8 0x04#8)) state state
      (.UTYPE (0x4202#20, .Regidx 10#5, .AUIPC)) := by
  decode_run

theorem raw_result_base_add_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x45#8 0x89#8)) state state
      (.ITYPE (0x894#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) := by
  decode_run

theorem raw_result_discriminant_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x83#8 0x45#8 0x05#8 0x35#8)) state state
      (.LOAD (0x350#12, .Regidx 10#5, .Regidx 11#5, true, 1)) := by
  decode_run

theorem raw_result_payload_add_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x05#8 0x01#8)) state state
      (.ITYPE (0x010#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) := by
  decode_run

theorem raw_result_seqz_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x93#8 0xb5#8 0x15#8 0x00#8)) state state
      (.ITYPE (0x001#12, .Regidx 11#5, .Regidx 11#5, .SLTIU)) := by
  decode_run

theorem raw_result_mask_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x93#8 0x85#8 0xf5#8 0xff#8)) state state
      (.ITYPE (0xfff#12, .Regidx 11#5, .Regidx 11#5, .ADDI)) := by
  decode_run

theorem raw_result_select_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x33#8 0xf5#8 0xa5#8 0x00#8)) state state
      (.RTYPE (.Regidx 10#5, .Regidx 11#5, .Regidx 10#5, .AND)) := by
  decode_run

def rawResultAfterAuipc (state : State) (retired : BitVec 64) : State :=
  afterRegisterWrite state (BitVec.ofNat 64 0x1378c) retired x10
    (BitVec.ofNat 64 0x421578c)

def rawResultAfterBaseAdd (state : State) (retired : BitVec 64) : State :=
  afterRegisterWrite state (BitVec.ofNat 64 0x13790) retired x10
    (BitVec.ofNat 64 0x4215020)

def rawResultTag (model : DecoderGlobalsModel) : BitVec 8 :=
  BitVec.ofNat 8 (if model.stored.isSome then 1 else 0)

def rawResultAfterDiscriminant (state : State) (retired : BitVec 64)
    (model : DecoderGlobalsModel) : State :=
  afterRegisterWrite state (BitVec.ofNat 64 0x13794) retired x11
    (zero_extend (m := 64) (rawResultTag model))

def rawResultAfterPayloadAdd (state : State) (retired : BitVec 64) : State :=
  afterRegisterWrite state (BitVec.ofNat 64 0x13798) retired x10
    (BitVec.ofNat 64 canonicalContractParams.resultBuffer)

def rawResultSeqzValue (model : DecoderGlobalsModel) : BitVec 64 :=
  BitVec.ofNat 64 (if model.stored.isSome then 0 else 1)

def rawResultAfterSeqz (state : State) (retired : BitVec 64)
    (model : DecoderGlobalsModel) : State :=
  afterRegisterWrite state (BitVec.ofNat 64 0x1379c) retired x11
    (rawResultSeqzValue model)

def rawResultMaskValue (model : DecoderGlobalsModel) : BitVec 64 :=
  if model.stored.isSome then BitVec.allOnes 64 else 0

def rawResultAfterMask (state : State) (retired : BitVec 64)
    (model : DecoderGlobalsModel) : State :=
  afterRegisterWrite state (BitVec.ofNat 64 0x137a0) retired x11
    (rawResultMaskValue model)

def rawResultPointerValue (model : DecoderGlobalsModel) : BitVec 64 :=
  BitVec.ofNat 64 (if model.stored.isSome then canonicalContractParams.resultBuffer else 0)

def rawResultAfterSelect (state : State) (retired : BitVec 64)
    (model : DecoderGlobalsModel) : State :=
  afterRegisterWrite state (BitVec.ofNat 64 0x137a4) retired x10
    (rawResultPointerValue model)

theorem raw_result_auipc_step (fromStep : Nat) (state : State)
    (machine : RawResultMachinePre state) :
    ∃ retired, Runs (try_step fromStep false) state (rawResultAfterAuipc state retired) false := by
  have platform := machine.instructions 0x1378c (by simp [rawResultInstructionPcs])
  obtain ⟨seccfgBits, seccfgRead⟩ := platform.seccfgRead
  have atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1378c) := by
    rw [← rawResult_entry_address]
    exact machine.entry
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have privilegeIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := incrementNormal.2.1
  have seccfgIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some seccfgBits :=
    (platformPreserved_mseccfg incrementAgree).trans seccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1378c)
  have corePc : executeState.regs.get? PC = some (BitVec.ofNat 64 0x1378c) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs
      (execute (.UTYPE (0x4202#20, .Regidx 10#5, .AUIPC))) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 0x421578c) }
      (.Retire_Success ()) := by
    apply execute_UTYPE_auipc_run executeState _ 0x4202#20 (.Regidx 10#5)
      (BitVec.ofNat 64 0x1378c)
    · exact readReg_run _ _ _ corePc
    · have value : BitVec.ofNat 64 0x1378c +
          sign_extend (m := 64) (0x4202#20 ++ 0x000#12) = BitVec.ofNat 64 0x421578c := by
        rfl
      rw [value]
      exact wX_bits_run_x10 executeState (BitVec.ofNat 64 0x421578c)
  simpa [rawResultAfterAuipc, executeState] using
    fallThroughRegisterWriteStep fromStep 0x1378c state 0x17#8 0x25#8 0x20#8 0x04#8
      (.UTYPE (0x4202#20, .Regidx 10#5, .AUIPC)) x10 (BitVec.ofNat 64 0x421578c)
      atPc platform (raw_result_auipc_fetch state platform.code) (by rfl)
      (raw_result_auipc_decode _ privilegeIncrement seccfgBits seccfgIncrement) execute
      (fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem raw_result_base_add_step (fromStep : Nat) (state : State)
    (platform : ExitPlatform state 0x13790)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x13790))
    (sourceValue : state.regs.get? x10 = some (BitVec.ofNat 64 0x421578c)) :
    ∃ retired, Runs (try_step fromStep false) state (rawResultAfterBaseAdd state retired) false := by
  obtain ⟨seccfgBits, seccfgRead⟩ := platform.seccfgRead
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have privilegeIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := incrementNormal.2.1
  have seccfgIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some seccfgBits :=
    (platformPreserved_mseccfg incrementAgree).trans seccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x13790)
  have source : executeState.regs.get? x10 = some (BitVec.ofNat 64 0x421578c) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, sourceValue]
  have execute : Runs
      (execute (.ITYPE (0x894#12, .Regidx 10#5, .Regidx 10#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 0x4215020) }
      (.Retire_Success ()) := by
    apply execute_ITYPE_run executeState _ 0x894#12 (.Regidx 10#5) (.Regidx 10#5) .ADDI
      (BitVec.ofNat 64 0x421578c)
    · exact rX_bits_run_x10 executeState _ source
    · have value : iTypeResult .ADDI 0x894#12 (BitVec.ofNat 64 0x421578c) =
          BitVec.ofNat 64 0x4215020 := by rfl
      rw [value]
      exact wX_bits_run_x10 executeState (BitVec.ofNat 64 0x4215020)
  simpa [rawResultAfterBaseAdd, executeState] using
    fallThroughRegisterWriteStep fromStep 0x13790 state 0x13#8 0x05#8 0x45#8 0x89#8
      (.ITYPE (0x894#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) x10
      (BitVec.ofNat 64 0x4215020) atPc platform
      (raw_result_base_add_fetch state platform.code) (by rfl)
      (raw_result_base_add_decode _ privilegeIncrement seccfgBits seccfgIncrement) execute
      (fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem raw_result_discriminant_step (fromStep : Nat) (initial state : State)
    (model : DecoderGlobalsModel)
    (sourcePre : (contractRawResult canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer).pre model initial)
    (machine : RawResultMachinePre initial)
    (initialAgree : Agree platformPreserved initial state)
    (memoryUnchanged : state.mem = initial.mem)
    (platform : ExitPlatform state 0x13794)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x13794))
    (baseStored : state.regs.get? x10 = some (BitVec.ofNat 64 0x4215020)) :
    ∃ retired, Runs (try_step fromStep false) state
      (rawResultAfterDiscriminant state retired model) false := by
  obtain ⟨seccfgBits, seccfgRead, pmmDisabled⟩ := machine.mseccfg
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := machine.mstatus
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have privilegeIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := incrementNormal.2.1
  have seccfgIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some seccfgBits :=
    ((platformPreserved_mseccfg initialAgree).trans seccfgRead) |>
      (platformPreserved_mseccfg incrementAgree).trans
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x13794)
  have executeAgree : Agree platformPreserved initial executeState :=
    initialAgree.trans (agree_stepPremiseState state (BitVec.ofNat 64 0x13794))
  have executeBase : executeState.regs.get? x10 = some (BitVec.ofNat 64 0x4215020) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, baseStored]
  have addressCalculation : Runs
      (get_transformed_data_addr (.Regidx 10#5) (sign_extend (m := 64) 0x350#12)
        (MemoryAccessType.Load mem_payload.Data) 1) executeState executeState
      (.Ext_DataAddr_OK (virtaddr.Virtaddr (BitVec.ofNat 64 0x4215370))) := by
    have address : BitVec.ofNat 64 0x4215020 + sign_extend (m := 64) 0x350#12 =
        BitVec.ofNat 64 0x4215370 := by rfl
    rw [← address]
    exact get_transformed_data_addr_machine_load_run executeState (.Regidx 10#5)
      (BitVec.ofNat 64 0x4215020) (sign_extend (m := 64) 0x350#12) mstatusBits seccfgBits
      (rX_bits_run_x10 executeState _ executeBase)
      ((platformPreserved_mstatus executeAgree).trans mstatusRead)
      ((executeAgree cur_privilege (by simp [platformPreserved])).trans
        ((machine.instructions 0x13794 (by simp [rawResultInstructionPcs])).normal.2.1))
      mprvZero ((platformPreserved_mseccfg executeAgree).trans seccfgRead) pmmDisabled
  have loadAllowed : LoadPmaAllows executeState (BitVec.ofNat 64 0x4215370) 1 := by
    have address : Elflings.canonicalDecoderGlobalsLayout.storedResult +
        Elflings.canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset =
        0x4215370 := by rfl
    simpa [address] using loadPmaAllows_of_agree executeAgree machine.discriminantLoad
  have physicalAccess := phys_access_check_machine_load_allowed executeState
    (BitVec.ofNat 64 0x4215370) 1
    (fetchPmpDisabled_of_agree (agree_stepPremiseState state (BitVec.ofNat 64 0x13794))
      (fetchPmpDisabled_of_normal platform.normal)) loadAllowed (by rfl)
  have htifRead : executeState.regs.get? htif_tohost_base = some none :=
    (platformPreserved_htifBase (agree_stepPremiseState state (BitVec.ofNat 64 0x13794))).trans
      platform.htifRead
  have noMMIO : Runs (within_mmio_readable
      (physaddr.Physaddr (BitVec.ofNat 64 0x4215370)) 1) executeState executeState false := by
    exact loadMemoryNoMMIO_of_state_layout_excluded executeState (BitVec.ofNat 64 0x4215370)
      1 (by simp [LoadMMIOAddressExcluded] <;> native_decide) htifRead
  have memoryByte : ∀ (index : Nat)
      (bound : index < (BinaryFv.RiscV.Sep.leBytes 1 (rawResultTag model)).length),
      executeState.mem.get? ((BitVec.ofNat 64 0x4215370).toNat + index) =
        some (BinaryFv.RiscV.Sep.leBytes 1 (rawResultTag model))[index] := by
    intro index bound
    have indexLt : index < 1 := by
      simpa [BinaryFv.RiscV.Sep.leBytes_length] using bound
    have indexZero : index = 0 := by omega
    subst index
    have represented := sourcePre.2.2
    unfold StoredResultDiscriminantRep MemoryRepresentation.OptionTagRep at represented
    have byteZero : (BinaryFv.RiscV.Sep.leBytes 1 (rawResultTag model))[0] =
        rawResultTag model := by
      simp [BinaryFv.RiscV.Sep.leBytes]
    rw [Nat.add_zero, byteZero]
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      memoryUnchanged, rawResultTag] using represented
  have execute : Runs
      (execute (.LOAD (0x350#12, .Regidx 10#5, .Regidx 11#5, true, 1))) executeState
      { executeState with
        regs := executeState.regs.insert x11 (zero_extend (m := 64) (rawResultTag model)) }
      (.Retire_Success ()) :=
    execute_LOAD_lbu_run executeState _ 0x350#12 (.Regidx 10#5) (.Regidx 11#5)
      (BitVec.ofNat 64 0x4215370) mstatusBits (rawResultTag model)
      ((platformPreserved_mstatus executeAgree).trans mstatusRead)
      ((executeAgree cur_privilege (by simp [platformPreserved])).trans
        ((machine.instructions 0x13794 (by simp [rawResultInstructionPcs])).normal.2.1))
      mprvZero addressCalculation (by simp [is_aligned_vaddr]) physicalAccess noMMIO memoryByte
      (wX_bits_run_x11 executeState _)
  simpa [rawResultAfterDiscriminant, executeState] using
    fallThroughRegisterWriteStep fromStep 0x13794 state 0x83#8 0x45#8 0x05#8 0x35#8
      (.LOAD (0x350#12, .Regidx 10#5, .Regidx 11#5, true, 1)) x11
      (zero_extend (m := 64) (rawResultTag model)) atPc platform
      (raw_result_discriminant_fetch state platform.code) (by rfl)
      (raw_result_discriminant_decode _ privilegeIncrement seccfgBits seccfgIncrement) execute
      (fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem raw_result_payload_add_step (fromStep : Nat) (state : State)
    (platform : ExitPlatform state 0x13798)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x13798))
    (sourceValue : state.regs.get? x10 = some (BitVec.ofNat 64 0x4215020)) :
    ∃ retired, Runs (try_step fromStep false) state
      (rawResultAfterPayloadAdd state retired) false := by
  obtain ⟨seccfgBits, seccfgRead⟩ := platform.seccfgRead
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have privilegeIncrement := incrementNormal.2.1
  have seccfgIncrement := (platformPreserved_mseccfg incrementAgree).trans seccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x13798)
  have source : executeState.regs.get? x10 = some (BitVec.ofNat 64 0x4215020) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, sourceValue]
  have execute : Runs
      (execute (.ITYPE (0x010#12, .Regidx 10#5, .Regidx 10#5, .ADDI))) executeState
      { executeState with
        regs := executeState.regs.insert x10
          (BitVec.ofNat 64 canonicalContractParams.resultBuffer) }
      (.Retire_Success ()) := by
    apply execute_ITYPE_run executeState _ 0x010#12 (.Regidx 10#5) (.Regidx 10#5) .ADDI
      (BitVec.ofNat 64 0x4215020)
    · exact rX_bits_run_x10 executeState _ source
    · have value : iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 0x4215020) =
          BitVec.ofNat 64 canonicalContractParams.resultBuffer := by
        native_decide
      rw [value]
      exact wX_bits_run_x10 executeState _
  simpa [rawResultAfterPayloadAdd, executeState] using
    fallThroughRegisterWriteStep fromStep 0x13798 state 0x13#8 0x05#8 0x05#8 0x01#8
      (.ITYPE (0x010#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) x10
      (BitVec.ofNat 64 canonicalContractParams.resultBuffer) atPc platform
      (raw_result_payload_add_fetch state platform.code) (by rfl)
      (raw_result_payload_add_decode _ privilegeIncrement seccfgBits seccfgIncrement) execute
      (fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem raw_result_seqz_value (model : DecoderGlobalsModel) :
    iTypeResult .SLTIU 0x001#12 (zero_extend (m := 64) (rawResultTag model)) =
      rawResultSeqzValue model := by
  rcases model with ⟨attempted, status, stored⟩
  cases stored <;>
    simp [iTypeResult, rawResultTag, rawResultSeqzValue] <;> native_decide

theorem raw_result_seqz_step (fromStep : Nat) (state : State) (model : DecoderGlobalsModel)
    (platform : ExitPlatform state 0x1379c)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1379c))
    (sourceValue : state.regs.get? x11 =
      some (zero_extend (m := 64) (rawResultTag model))) :
    ∃ retired, Runs (try_step fromStep false) state (rawResultAfterSeqz state retired model) false := by
  obtain ⟨seccfgBits, seccfgRead⟩ := platform.seccfgRead
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have privilegeIncrement := incrementNormal.2.1
  have seccfgIncrement := (platformPreserved_mseccfg incrementAgree).trans seccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1379c)
  have source : executeState.regs.get? x11 =
      some (zero_extend (m := 64) (rawResultTag model)) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, sourceValue]
  have execute : Runs
      (execute (.ITYPE (0x001#12, .Regidx 11#5, .Regidx 11#5, .SLTIU))) executeState
      { executeState with regs := executeState.regs.insert x11 (rawResultSeqzValue model) }
      (.Retire_Success ()) := by
    apply execute_ITYPE_run executeState _ 0x001#12 (.Regidx 11#5) (.Regidx 11#5) .SLTIU
      (zero_extend (m := 64) (rawResultTag model))
    · exact rX_bits_run_x11 executeState _ source
    · rw [raw_result_seqz_value]
      exact wX_bits_run_x11 executeState _
  simpa [rawResultAfterSeqz, executeState] using
    fallThroughRegisterWriteStep fromStep 0x1379c state 0x93#8 0xb5#8 0x15#8 0x00#8
      (.ITYPE (0x001#12, .Regidx 11#5, .Regidx 11#5, .SLTIU)) x11
      (rawResultSeqzValue model) atPc platform (raw_result_seqz_fetch state platform.code) (by rfl)
      (raw_result_seqz_decode _ privilegeIncrement seccfgBits seccfgIncrement) execute
      (fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem raw_result_mask_value (model : DecoderGlobalsModel) :
    iTypeResult .ADDI 0xfff#12 (rawResultSeqzValue model) = rawResultMaskValue model := by
  rcases model with ⟨attempted, status, stored⟩
  cases stored <;>
    simp [iTypeResult, rawResultSeqzValue, rawResultMaskValue] <;> native_decide

theorem raw_result_mask_step (fromStep : Nat) (state : State) (model : DecoderGlobalsModel)
    (platform : ExitPlatform state 0x137a0)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x137a0))
    (sourceValue : state.regs.get? x11 = some (rawResultSeqzValue model)) :
    ∃ retired, Runs (try_step fromStep false) state (rawResultAfterMask state retired model) false := by
  obtain ⟨seccfgBits, seccfgRead⟩ := platform.seccfgRead
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have privilegeIncrement := incrementNormal.2.1
  have seccfgIncrement := (platformPreserved_mseccfg incrementAgree).trans seccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x137a0)
  have source : executeState.regs.get? x11 = some (rawResultSeqzValue model) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, sourceValue]
  have execute : Runs
      (execute (.ITYPE (0xfff#12, .Regidx 11#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (rawResultMaskValue model) }
      (.Retire_Success ()) := by
    apply execute_ITYPE_run executeState _ 0xfff#12 (.Regidx 11#5) (.Regidx 11#5) .ADDI
      (rawResultSeqzValue model)
    · exact rX_bits_run_x11 executeState _ source
    · rw [raw_result_mask_value]
      exact wX_bits_run_x11 executeState _
  simpa [rawResultAfterMask, executeState] using
    fallThroughRegisterWriteStep fromStep 0x137a0 state 0x93#8 0x85#8 0xf5#8 0xff#8
      (.ITYPE (0xfff#12, .Regidx 11#5, .Regidx 11#5, .ADDI)) x11
      (rawResultMaskValue model) atPc platform (raw_result_mask_fetch state platform.code) (by rfl)
      (raw_result_mask_decode _ privilegeIncrement seccfgBits seccfgIncrement) execute
      (fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide)

theorem raw_result_select_value (model : DecoderGlobalsModel) :
    rTypeResult .AND (rawResultMaskValue model)
      (BitVec.ofNat 64 canonicalContractParams.resultBuffer) = rawResultPointerValue model := by
  rcases model with ⟨attempted, status, stored⟩
  cases stored <;>
    simp [rTypeResult, rawResultMaskValue, rawResultPointerValue] <;> native_decide

theorem raw_result_select_step (fromStep : Nat) (state : State) (model : DecoderGlobalsModel)
    (platform : ExitPlatform state 0x137a4)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x137a4))
    (payloadValue : state.regs.get? x10 =
      some (BitVec.ofNat 64 canonicalContractParams.resultBuffer))
    (maskValue : state.regs.get? x11 = some (rawResultMaskValue model)) :
    ∃ retired, Runs (try_step fromStep false) state (rawResultAfterSelect state retired model) false := by
  obtain ⟨seccfgBits, seccfgRead⟩ := platform.seccfgRead
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have privilegeIncrement := incrementNormal.2.1
  have seccfgIncrement := (platformPreserved_mseccfg incrementAgree).trans seccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x137a4)
  have payload : executeState.regs.get? x10 =
      some (BitVec.ofNat 64 canonicalContractParams.resultBuffer) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, payloadValue]
  have mask : executeState.regs.get? x11 = some (rawResultMaskValue model) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, maskValue]
  have execute : Runs
      (execute (.RTYPE (.Regidx 10#5, .Regidx 11#5, .Regidx 10#5, .AND))) executeState
      { executeState with regs := executeState.regs.insert x10 (rawResultPointerValue model) }
      (.Retire_Success ()) := by
    apply execute_RTYPE_run executeState _ (.Regidx 10#5) (.Regidx 11#5) (.Regidx 10#5) .AND
      (rawResultMaskValue model) (BitVec.ofNat 64 canonicalContractParams.resultBuffer)
    · exact rX_bits_run_x11 executeState _ mask
    · exact rX_bits_run_x10 executeState _ payload
    · rw [raw_result_select_value]
      exact wX_bits_run_x10 executeState _
  simpa [rawResultAfterSelect, executeState] using
    fallThroughRegisterWriteStep fromStep 0x137a4 state 0x33#8 0xf5#8 0xa5#8 0x00#8
      (.RTYPE (.Regidx 10#5, .Regidx 11#5, .Regidx 10#5, .AND)) x10
      (rawResultPointerValue model) atPc platform (raw_result_select_fetch state platform.code)
      (by rfl) (raw_result_select_decode _ privilegeIncrement seccfgBits seccfgIncrement) execute
      (fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide)

/-- The selected compiled `zesu_raw_result` instance satisfies its source contract by executing all
seven non-return instructions in Sail. -/
theorem rawResultInstanceObligation_proved
    {functionInstance : BinaryFv.Binary.Elfling.FunctionInstance}
    (member : functionInstance ∈ generatedProgram.functionInstances)
    (entry : functionInstance.entryPc = resolvedSymbols.rawResult) :
    RawResultInstanceObligation functionInstance := by
  intro model fromStep state sourcePre machine
  obtain ⟨r1, step1⟩ := raw_result_auipc_step fromStep state machine
  let s1 := rawResultAfterAuipc state r1
  have agree1 : Agree platformPreserved state s1 :=
    afterRegisterWrite_agree (destination := x10) (by simp [platformPreserved])
  have mem1 : s1.mem = state.mem := afterRegisterWrite_mem _ _ _ _ _
  have platform2 : ExitPlatform s1 0x13790 :=
    exitPlatform_of_executionState agree1 (afterRegisterWrite_retired_present _ _ _ _ _) mem1
      (machine.instructions 0x13790 (by simp [rawResultInstructionPcs]))
  have x10s1 : s1.regs.get? x10 = some (BitVec.ofNat 64 0x421578c) := by
    simp [s1, rawResultAfterAuipc, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have at2 : s1.regs.get? PC = some (BitVec.ofNat 64 0x13790) := by
    simpa [s1, rawResultAfterAuipc] using
      afterRegisterWrite_pc state (BitVec.ofNat 64 0x1378c) r1 x10
        (BitVec.ofNat 64 0x421578c)
  obtain ⟨r2, step2⟩ := raw_result_base_add_step (fromStep + 1) s1 platform2 at2 x10s1
  let s2 := rawResultAfterBaseAdd s1 r2
  have agree2 : Agree platformPreserved state s2 := agree1.trans
    (afterRegisterWrite_agree (destination := x10) (by simp [platformPreserved]))
  have mem2 : s2.mem = state.mem :=
    (afterRegisterWrite_mem _ _ _ _ _).trans mem1
  have platform3 : ExitPlatform s2 0x13794 :=
    exitPlatform_of_executionState agree2 (afterRegisterWrite_retired_present _ _ _ _ _) mem2
      (machine.instructions 0x13794 (by simp [rawResultInstructionPcs]))
  have x10s2 : s2.regs.get? x10 = some (BitVec.ofNat 64 0x4215020) := by
    simp [s2, rawResultAfterBaseAdd, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have at3 : s2.regs.get? PC = some (BitVec.ofNat 64 0x13794) := by
    simpa [s2, rawResultAfterBaseAdd] using
      afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x13790) r2 x10
        (BitVec.ofNat 64 0x4215020)
  obtain ⟨r3, step3⟩ := raw_result_discriminant_step (fromStep + 2) state s2 model
    sourcePre machine agree2 mem2 platform3 at3 x10s2
  let s3 := rawResultAfterDiscriminant s2 r3 model
  have agree3 : Agree platformPreserved state s3 := agree2.trans
    (afterRegisterWrite_agree (destination := x11) (by simp [platformPreserved]))
  have mem3 : s3.mem = state.mem :=
    (afterRegisterWrite_mem _ _ _ _ _).trans mem2
  have platform4 : ExitPlatform s3 0x13798 :=
    exitPlatform_of_executionState agree3 (afterRegisterWrite_retired_present _ _ _ _ _) mem3
      (machine.instructions 0x13798 (by simp [rawResultInstructionPcs]))
  have x10s3 : s3.regs.get? x10 = some (BitVec.ofNat 64 0x4215020) := by
    simp [s3, rawResultAfterDiscriminant, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, x10s2]
  have at4 : s3.regs.get? PC = some (BitVec.ofNat 64 0x13798) := by
    simpa [s3, rawResultAfterDiscriminant] using
      afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x13794) r3 x11
        (zero_extend (m := 64) (rawResultTag model))
  obtain ⟨r4, step4⟩ := raw_result_payload_add_step (fromStep + 3) s3 platform4 at4 x10s3
  let s4 := rawResultAfterPayloadAdd s3 r4
  have agree4 : Agree platformPreserved state s4 := agree3.trans
    (afterRegisterWrite_agree (destination := x10) (by simp [platformPreserved]))
  have mem4 : s4.mem = state.mem :=
    (afterRegisterWrite_mem _ _ _ _ _).trans mem3
  have platform5 : ExitPlatform s4 0x1379c :=
    exitPlatform_of_executionState agree4 (afterRegisterWrite_retired_present _ _ _ _ _) mem4
      (machine.instructions 0x1379c (by simp [rawResultInstructionPcs]))
  have x11s4 : s4.regs.get? x11 = some (zero_extend (m := 64) (rawResultTag model)) := by
    simp [s4, rawResultAfterPayloadAdd, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, s3, rawResultAfterDiscriminant]
  have at5 : s4.regs.get? PC = some (BitVec.ofNat 64 0x1379c) := by
    simpa [s4, rawResultAfterPayloadAdd] using
      afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x13798) r4 x10
        (BitVec.ofNat 64 canonicalContractParams.resultBuffer)
  obtain ⟨r5, step5⟩ := raw_result_seqz_step (fromStep + 4) s4 model platform5 at5 x11s4
  let s5 := rawResultAfterSeqz s4 r5 model
  have agree5 : Agree platformPreserved state s5 := agree4.trans
    (afterRegisterWrite_agree (destination := x11) (by simp [platformPreserved]))
  have mem5 : s5.mem = state.mem :=
    (afterRegisterWrite_mem _ _ _ _ _).trans mem4
  have platform6 : ExitPlatform s5 0x137a0 :=
    exitPlatform_of_executionState agree5 (afterRegisterWrite_retired_present _ _ _ _ _) mem5
      (machine.instructions 0x137a0 (by simp [rawResultInstructionPcs]))
  have x11s5 : s5.regs.get? x11 = some (rawResultSeqzValue model) := by
    simp [s5, rawResultAfterSeqz, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have at6 : s5.regs.get? PC = some (BitVec.ofNat 64 0x137a0) := by
    simpa [s5, rawResultAfterSeqz] using
      afterRegisterWrite_pc s4 (BitVec.ofNat 64 0x1379c) r5 x11 (rawResultSeqzValue model)
  obtain ⟨r6, step6⟩ := raw_result_mask_step (fromStep + 5) s5 model platform6 at6 x11s5
  let s6 := rawResultAfterMask s5 r6 model
  have agree6 : Agree platformPreserved state s6 := agree5.trans
    (afterRegisterWrite_agree (destination := x11) (by simp [platformPreserved]))
  have mem6 : s6.mem = state.mem :=
    (afterRegisterWrite_mem _ _ _ _ _).trans mem5
  have platform7 : ExitPlatform s6 0x137a4 :=
    exitPlatform_of_executionState agree6 (afterRegisterWrite_retired_present _ _ _ _ _) mem6
      (machine.instructions 0x137a4 (by simp [rawResultInstructionPcs]))
  have x10s6 : s6.regs.get? x10 =
      some (BitVec.ofNat 64 canonicalContractParams.resultBuffer) := by
    simp [s6, rawResultAfterMask, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, s5, rawResultAfterSeqz, s4, rawResultAfterPayloadAdd]
  have x11s6 : s6.regs.get? x11 = some (rawResultMaskValue model) := by
    simp [s6, rawResultAfterMask, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have at7 : s6.regs.get? PC = some (BitVec.ofNat 64 0x137a4) := by
    simpa [s6, rawResultAfterMask] using
      afterRegisterWrite_pc s5 (BitVec.ofNat 64 0x137a0) r6 x11 (rawResultMaskValue model)
  obtain ⟨r7, step7⟩ :=
    raw_result_select_step (fromStep + 6) s6 model platform7 at7 x10s6 x11s6
  let final := rawResultAfterSelect s6 r7 model
  have finalAgree : Agree platformPreserved state final := agree6.trans
    (afterRegisterWrite_agree (destination := x10) (by simp [platformPreserved]))
  have finalMem : final.mem = state.mem :=
    (afterRegisterWrite_mem _ _ _ _ _).trans mem6
  have finalRetired : RetiredCounterPresent final :=
    afterRegisterWrite_retired_present _ _ _ _ _
  obtain ⟨region1, region2, region3, region4, region5, region6, region7, regionExit⟩ :=
    rawResult_function_instance_execution_pc_membership member entry
  have exits := rawResult_function_instance_exits member entry
  have entryWord : functionInstanceEntryWord functionInstance = BitVec.ofNat 64 0x1378c := by
    simp [functionInstanceEntryWord, entry, rawResult_entry_address]
  have statePc : state.regs.get? PC = some (functionInstanceEntryWord functionInstance) := by
    rw [entryWord, ← rawResult_entry_address]
    exact machine.entry
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x13790) := by
    simpa [s1, rawResultAfterAuipc] using
      afterRegisterWrite_pc state (BitVec.ofNat 64 0x1378c) r1 x10
        (BitVec.ofNat 64 0x421578c)
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x13794) := by
    simpa [s2, rawResultAfterBaseAdd] using
      afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x13790) r2 x10
        (BitVec.ofNat 64 0x4215020)
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x13798) := by
    simpa [s3, rawResultAfterDiscriminant] using
      afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x13794) r3 x11
        (zero_extend (m := 64) (rawResultTag model))
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x1379c) := by
    simpa [s4, rawResultAfterPayloadAdd] using
      afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x13798) r4 x10
        (BitVec.ofNat 64 canonicalContractParams.resultBuffer)
  have pc5 : s5.regs.get? PC = some (BitVec.ofNat 64 0x137a0) := by
    simpa [s5, rawResultAfterSeqz] using
      afterRegisterWrite_pc s4 (BitVec.ofNat 64 0x1379c) r5 x11 (rawResultSeqzValue model)
  have pc6 : s6.regs.get? PC = some (BitVec.ofNat 64 0x137a4) := by
    simpa [s6, rawResultAfterMask] using
      afterRegisterWrite_pc s5 (BitVec.ofNat 64 0x137a0) r6 x11 (rawResultMaskValue model)
  have finalPc : final.regs.get? PC = some (BitVec.ofNat 64 0x137a8) := by
    simpa [final, rawResultAfterSelect] using
      afterRegisterWrite_pc s6 (BitVec.ofNat 64 0x137a4) r7 x10 (rawResultPointerValue model)
  have entryNotExit :
      ¬ functionInstanceExitPred functionInstance (functionInstanceEntryWord functionInstance) := by
    rw [entryWord]
    simp [functionInstanceExitPred, FunctionInstance.isExit, exits]
  have pc1NotExit :
      ¬ functionInstanceExitPred functionInstance (BitVec.ofNat 64 0x13790) := by
    simp [functionInstanceExitPred, FunctionInstance.isExit, exits]
  have pc2NotExit :
      ¬ functionInstanceExitPred functionInstance (BitVec.ofNat 64 0x13794) := by
    simp [functionInstanceExitPred, FunctionInstance.isExit, exits]
  have pc3NotExit :
      ¬ functionInstanceExitPred functionInstance (BitVec.ofNat 64 0x13798) := by
    simp [functionInstanceExitPred, FunctionInstance.isExit, exits]
  have pc4NotExit :
      ¬ functionInstanceExitPred functionInstance (BitVec.ofNat 64 0x1379c) := by
    simp [functionInstanceExitPred, FunctionInstance.isExit, exits]
  have pc5NotExit :
      ¬ functionInstanceExitPred functionInstance (BitVec.ofNat 64 0x137a0) := by
    simp [functionInstanceExitPred, FunctionInstance.isExit, exits]
  have pc6NotExit :
      ¬ functionInstanceExitPred functionInstance (BitVec.ofNat 64 0x137a4) := by
    simp [functionInstanceExitPred, FunctionInstance.isExit, exits]
  have atExit : functionInstanceExitPred functionInstance (BitVec.ofNat 64 0x137a8) := by
    simp [functionInstanceExitPred, FunctionInstance.isExit, exits]
  have trace : BinaryFv.RiscV.Elfling.EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance)
      (functionInstanceExitPred functionInstance) (functionInstanceEntryWord functionInstance)
      fromStep 7 state final := by
    refine ⟨statePc, entryWord.symm ▸ region1, ?_, ?_⟩
    · exact entryNotExit
    refine .step fromStep 6 _ state s1 final statePc (entryWord.symm ▸ region1)
      entryNotExit step1 ?_
    refine .step (fromStep + 1) 5 _ s1 s2 final pc1 region2 pc1NotExit step2 ?_
    refine .step (fromStep + 2) 4 _ s2 s3 final pc2 region3 pc2NotExit step3 ?_
    refine .step (fromStep + 3) 3 _ s3 s4 final pc3 region4 pc3NotExit step4 ?_
    refine .step (fromStep + 4) 2 _ s4 s5 final pc4 region5 pc4NotExit step5 ?_
    refine .step (fromStep + 5) 1 _ s5 s6 final pc5 region6 pc5NotExit step6 ?_
    refine .step (fromStep + 6) 0 _ s6 final final pc6 region7 pc6NotExit step7 ?_
    exact .exitAt (fromStep + 7) final _ finalPc atExit
  have finalX10 : final.regs.get? x10 = some (rawResultPointerValue model) := by
    simp [final, rawResultAfterSelect, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have post : (contractRawResult canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer).post model
      ((contractRawResult canonicalContractParams.env canonicalContractParams.globals
        canonicalContractParams.resultBuffer).meaning model) state final := by
    refine ⟨?_, ?_, ?_, finalAgree, finalRetired, ?_⟩
    · show canonicalContractParams.env.image.fileBytesMatchMemory final.mem
      rw [finalMem]
      exact sourcePre.2.1
    · intro address _
      exact congrArg (fun memory => memory.get? address) finalMem
    · intro address _
      exact congrArg (fun memory => memory.get? address) finalMem
    · refine ⟨rfl, ?_⟩
      simpa [rawResultPointerValue] using finalX10
  exact ⟨⟨7, final, by simp [contractRawResult], trace, post⟩⟩

end BinaryFv.Zesu.MachineExecution
