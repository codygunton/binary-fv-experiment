import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.ReturnToSentinel
import BinaryFv.Zesu.MachineExecution.AccessorBlocks
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.Zesu.MachineExecution.Seg

/-!
# Concrete Sail execution of `zesu_raw_error`

The compiled accessor obligation supplies the current entry PC, fetch conditions at all three owned
instructions, and readable PMA permission for the status word.  This module spends those facts one
instruction at a time.  The function-instance trace stops when it reaches the `ret` at `0x13788`;
`ReturnToSentinel.lean` proves the runner-facing retirement of that `ret`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary BinaryFv.RiscV
open BinaryFv.Binary.Elfling BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def rawErrorAfterAuipc (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x13780) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x13780)).regs.insert x10 (BitVec.ofNat 64 0x4215780) }
    (BitVec.ofNat 64 0x13784) retired

def rawErrorAfterLoad (state : State) (retired : BitVec 64) (value : Nat) : State :=
  tryStepControlFlowAfterRetired
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x13784) with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x13784)).regs.insert x10 (BitVec.ofNat 64 value) }
    (BitVec.ofNat 64 0x13788) retired

theorem rawErrorAfterAuipc_agree (state : State) (retired : BitVec 64) :
    Agree platformPreserved state (rawErrorAfterAuipc state retired) :=
  afterRegisterWrite_agree (state := state) (pc := BitVec.ofNat 64 0x13780) (retired := retired)
    (destination := x10) (value := BitVec.ofNat 64 0x4215780) (by simp [platformPreserved])

theorem rawErrorAfterAuipc_mem (state : State) (retired : BitVec 64) :
    (rawErrorAfterAuipc state retired).mem = state.mem := rfl

theorem rawErrorAfterAuipc_retired_present (state : State) (retired : BitVec 64) :
    RetiredCounterPresent (rawErrorAfterAuipc state retired) :=
  afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x13780) retired x10
    (BitVec.ofNat 64 0x4215780)

theorem rawErrorAfterLoad_agree (state : State) (retired : BitVec 64) (value : Nat) :
    Agree platformPreserved state (rawErrorAfterLoad state retired value) :=
  afterRegisterWrite_agree (state := state) (pc := BitVec.ofNat 64 0x13784) (retired := retired)
    (destination := x10) (value := BitVec.ofNat 64 value) (by simp [platformPreserved])

theorem rawErrorAfterLoad_mem (state : State) (retired : BitVec 64) (value : Nat) :
    (rawErrorAfterLoad state retired value).mem = state.mem := rfl

theorem rawErrorAfterLoad_retired_present (state : State) (retired : BitVec 64) (value : Nat) :
    RetiredCounterPresent (rawErrorAfterLoad state retired value) :=
  afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x13784) retired x10
    (BitVec.ofNat 64 value)

-- Register the two frame equations above with `grind`, so the memory transports fire on these
-- wrappers without the caller naming either the transport or the frame lemma.
attribute [grind =] rawErrorAfterAuipc_mem rawErrorAfterLoad_mem

theorem rawErrorAfterLoad_pc (state : State) (retired : BitVec 64) (value : Nat) :
    (rawErrorAfterLoad state retired value).regs.get? PC = some (BitVec.ofNat 64 0x13788) :=
  afterRegisterWrite_pc state (BitVec.ofNat 64 0x13784) retired x10 (BitVec.ofNat 64 value)

theorem rawErrorAfterLoad_x10 (state : State) (retired : BitVec 64) (value : Nat) :
    (rawErrorAfterLoad state retired value).regs.get? x10 = some (BitVec.ofNat 64 value) :=
  afterRegisterWrite_destination state (BitVec.ofNat 64 0x13784) retired x10
    (BitVec.ofNat 64 value) (by decide) (by decide)

theorem decodeStatus_extend_value (status : DecodeStatus) :
    extend_value false (BitVec.ofNat 32 status.code) = BitVec.ofNat 64 status.code := by
  cases status <;> native_decide

/-- The AUIPC at `0x13780` retires to `0x13784` and writes its exact linked address to `a0`. -/
theorem raw_error_auipc_step (fromStep : Nat) (state : State)
    (machine : RawErrorMachinePre state) :
    ∃ retired, Runs (try_step fromStep false) state (rawErrorAfterAuipc state retired) false := by
  have platform := machine.instructions 0x13780 (by decide)
  obtain ⟨hartRead, privilege, satpRead, midelegRead, mieRead, mipRead, pmpcfgRead,
    pmpaddrRead, inhibitRead, configRead, elpRead, misaCase⟩ := platform.normal
  obtain ⟨mstatusBits, mstatusRead⟩ := platform.mstatusRead
  obtain ⟨seccfgBits, seccfgRead⟩ := platform.seccfgRead
  obtain ⟨retired, retiredRead⟩ := platform.retired
  have atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x13780) := by
    rw [← rawError_entry_address]
    exact machine.entry
  have agreeIncrement : Agree platformPreserved state
      (tryStepControlFlowAfterIncrement state) := agree_afterIncrement state
  have normalIncrement : NormalExecutionState (tryStepControlFlowAfterIncrement state) :=
    normalExecutionState_of_platformPreserved agreeIncrement platform.normal
  have fetchPlatform : FetchBasePlatform (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13780) :=
    fetchBasePlatform_of_offPC
      (pc_afterIncrement state (BitVec.ofNat 64 0x13780) atPc)
      (fetchBasePlatformOffPC_of_normal normalIncrement
        ((platformPreserved_mstatus agreeIncrement).trans mstatusRead) (by decide)
        (fetchPmaAllows_of_agree agreeIncrement platform.pmaAllows))
  have fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13780) :=
    fetchMemoryNoMMIO_of_state_layout_excluded _ _
      ⟨fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide),
        (platformPreserved_htifBase agreeIncrement).trans platform.htifRead⟩
  have interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state) :=
    interruptDisabled_of_normal normalIncrement
      ((platformPreserved_mstatus agreeIncrement).trans mstatusRead)
      (platform.meipRead.imp fun _ read => (platformPreserved_sigMeip agreeIncrement).trans read)
  have notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state) :=
    landingPadNotExpected_of_normal normalIncrement
  have privilegeIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := normalIncrement.2.1
  have seccfgIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some seccfgBits :=
    (platformPreserved_mseccfg agreeIncrement).trans seccfgRead
  have corePc :
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x13780)).regs.get? PC = some (BitVec.ofNat 64 0x13780) :=
    ((coreControlFlowNextState_writes (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13780)).get PC (by decide)).trans
      (pc_afterIncrement state (BitVec.ofNat 64 0x13780) atPc)
  have execute := raw_error_auipc_execute_exact
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13780)) corePc
  refine ⟨retired, ?_⟩
  exact raw_error_auipc_try_step fromStep state (BitVec.ofNat 64 0x13780) retired 0 0
    (BitVec.ofNat 64 0x4215780) fetchPlatform fetchNoMMIO
    (raw_error_auipc_fetch state platform.code) interrupts (by rfl)
    (raw_error_auipc_decode (tryStepControlFlowAfterIncrement state)
      privilegeIncrement seccfgBits seccfgIncrement)
    notExpected execute hartRead inhibitRead configRead (by decide) (by decide) retiredRead

/-- The signed word load at `0x13784` reads the represented decoder status and reaches the `ret`. -/
theorem raw_error_load_step (fromStep : Nat) (state : State) (status : DecodeStatus)
    (represented : Word32LERep state Elflings.canonicalDecoderGlobalsLayout.status status.code)
    (machine : RawErrorMachinePre state) (firstRetired : BitVec 64) :
    ∃ retired, Runs (try_step (fromStep + 1) false) (rawErrorAfterAuipc state firstRetired)
      (rawErrorAfterLoad (rawErrorAfterAuipc state firstRetired) retired status.code) false := by
  let afterAuipc := rawErrorAfterAuipc state firstRetired
  let pc := BitVec.ofNat 64 0x13784
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement afterAuipc) pc
  have firstAgree : Agree platformPreserved state afterAuipc :=
    rawErrorAfterAuipc_agree state firstRetired
  have firstCode : Artifacts.programImage.fileBytesLoadedFaithfully afterAuipc.mem := by
    simpa [afterAuipc, rawErrorAfterAuipc_mem] using machine.instructions 0x13784 (by decide) |>.code
  have firstPlatform : ExitPlatform afterAuipc 0x13784 :=
    exitPlatform_of_agree firstAgree (rawErrorAfterAuipc_retired_present state firstRetired)
      firstCode (machine.instructions 0x13784 (by decide))
  obtain ⟨hartRead, privilege, satpRead, midelegRead, mieRead, mipRead, pmpcfgRead,
    pmpaddrRead, inhibitRead, configRead, elpRead, misaCase⟩ := firstPlatform.normal
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := machine.mstatus
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := machine.mseccfg
  obtain ⟨retired, retiredRead⟩ := firstPlatform.retired
  have atPc : afterAuipc.regs.get? PC = some pc :=
    afterRegisterWrite_pc state (BitVec.ofNat 64 0x13780) firstRetired x10
      (BitVec.ofNat 64 0x4215780)
  have agreeIncrement : Agree platformPreserved afterAuipc
      (tryStepControlFlowAfterIncrement afterAuipc) := agree_afterIncrement afterAuipc
  have normalIncrement : NormalExecutionState (tryStepControlFlowAfterIncrement afterAuipc) :=
    normalExecutionState_of_platformPreserved agreeIncrement firstPlatform.normal
  have fetchPlatform : FetchBasePlatform (tryStepControlFlowAfterIncrement afterAuipc) pc :=
    fetchBasePlatform_of_offPC (pc_afterIncrement afterAuipc pc atPc)
      (fetchBasePlatformOffPC_of_normal normalIncrement
        ((platformPreserved_mstatus agreeIncrement).trans firstPlatform.mstatusRead.choose_spec)
        (by decide) (fetchPmaAllows_of_agree agreeIncrement firstPlatform.pmaAllows))
  have fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement afterAuipc) pc :=
    fetchMemoryNoMMIO_of_state_layout_excluded _ _
      ⟨fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide),
        (platformPreserved_htifBase agreeIncrement).trans firstPlatform.htifRead⟩
  have interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement afterAuipc) :=
    interruptDisabled_of_normal normalIncrement
      ((platformPreserved_mstatus agreeIncrement).trans firstPlatform.mstatusRead.choose_spec)
      (firstPlatform.meipRead.imp fun _ read =>
        (platformPreserved_sigMeip agreeIncrement).trans read)
  have notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement afterAuipc) :=
    landingPadNotExpected_of_normal normalIncrement
  have privilegeIncrement :
      (tryStepControlFlowAfterIncrement afterAuipc).regs.get? cur_privilege =
        some Privilege.Machine := normalIncrement.2.1
  have seccfgIncrement :
      (tryStepControlFlowAfterIncrement afterAuipc).regs.get? mseccfg = some mseccfgBits :=
    (platformPreserved_mseccfg firstAgree).trans mseccfgRead |>
      (platformPreserved_mseccfg agreeIncrement).trans
  have executeAgree : Agree platformPreserved state executeState :=
    firstAgree.trans (agree_stepPremiseState afterAuipc pc)
  have baseStored : executeState.regs.get? x10 = some (BitVec.ofNat 64 0x4215780) :=
    ((stepPremiseState_writes afterAuipc pc).get x10 (by decide)).trans
      (afterRegisterWrite_destination state (BitVec.ofNat 64 0x13780) firstRetired x10
        (BitVec.ofNat 64 0x4215780) (by decide) (by decide))
  have addressCalculation : Runs
      (get_transformed_data_addr (.Regidx 10#5) (sign_extend (m := 64) 0x8a4#12)
        (MemoryAccessType.Load mem_payload.Data) 4) executeState executeState
      (.Ext_DataAddr_OK (virtaddr.Virtaddr
        (BitVec.ofNat 64 Elflings.canonicalDecoderGlobalsLayout.status))) := by
    have address : BitVec.ofNat 64 0x4215780 + sign_extend (m := 64) 0x8a4#12 =
        BitVec.ofNat 64 Elflings.canonicalDecoderGlobalsLayout.status := by native_decide
    rw [← address]
    exact get_transformed_data_addr_machine_load_run executeState (.Regidx 10#5)
      (BitVec.ofNat 64 0x4215780) (sign_extend (m := 64) 0x8a4#12) mstatusBits mseccfgBits
      (rX_bits_run_x10 executeState _ baseStored)
      ((platformPreserved_mstatus executeAgree).trans mstatusRead)
      ((executeAgree cur_privilege (by simp [platformPreserved])).trans
        (machine.instructions 0x13784 (by decide)).normal.2.1)
      mprvZero
      ((platformPreserved_mseccfg executeAgree).trans mseccfgRead) pmmDisabled
  have loadAllowed : LoadPmaAllows executeState
      (BitVec.ofNat 64 Elflings.canonicalDecoderGlobalsLayout.status) 4 :=
    loadPmaAllows_of_agree executeAgree machine.statusLoad
  have physicalAccess := phys_access_check_machine_load_allowed executeState
    (BitVec.ofNat 64 Elflings.canonicalDecoderGlobalsLayout.status) 4
    (fetchPmpDisabled_of_agree (agree_stepPremiseState afterAuipc pc)
      (fetchPmpDisabled_of_normal firstPlatform.normal))
    loadAllowed (by native_decide)
  have noMMIO : Runs (within_mmio_readable
      (physaddr.Physaddr (BitVec.ofNat 64 Elflings.canonicalDecoderGlobalsLayout.status)) 4)
      executeState executeState false :=
    loadMemoryNoMMIO_of_state_layout_excluded executeState
      (BitVec.ofNat 64 Elflings.canonicalDecoderGlobalsLayout.status) 4
      (by simp [LoadMMIOAddressExcluded] <;> native_decide)
      ((platformPreserved_htifBase executeAgree).trans
        (machine.instructions 0x13784 (by decide)).htifRead)
  have memoryBytes : ∀ (index : Nat) (bound : index <
      (BinaryFv.RiscV.Sep.leBytes 4 (BitVec.ofNat 32 status.code)).length),
      executeState.mem.get?
          ((BitVec.ofNat 64 Elflings.canonicalDecoderGlobalsLayout.status).toNat + index) =
        some (BinaryFv.RiscV.Sep.leBytes 4 (BitVec.ofNat 32 status.code))[index] := by
    intro index bound
    have executeMemory : executeState.mem = state.mem := rfl
    rw [executeMemory]
    have indexBound : index < 4 := by
      simpa [BinaryFv.RiscV.Sep.leBytes_length] using bound
    have sourceByte := represented index indexBound
    have indexCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases indexCases with rfl | rfl | rfl | rfl <;> cases status <;>
    simpa [BinaryFv.RiscV.Sep.leBytes, DecodeStatus.code] using sourceByte
  have memoryRead := vmem_read_word_from_bytes_run executeState (.Regidx 10#5)
    (sign_extend (m := 64) 0x8a4#12)
    (BitVec.ofNat 64 Elflings.canonicalDecoderGlobalsLayout.status) mstatusBits
    (BitVec.ofNat 32 status.code)
    ((platformPreserved_mstatus executeAgree).trans mstatusRead)
    ((executeAgree cur_privilege (by simp [platformPreserved])).trans
      (machine.instructions 0x13784 (by decide)).normal.2.1)
    mprvZero addressCalculation (by native_decide) physicalAccess noMMIO
    memoryBytes
  have execute : Runs
      (execute (.LOAD (0x8a4#12, .Regidx 10#5, .Regidx 10#5, false, 4))) executeState
      { executeState with
        regs := executeState.regs.insert x10 (BitVec.ofNat 64 status.code) }
      (.Retire_Success ()) := by
    rw [← decodeStatus_extend_value status]
    exact raw_error_load_execute executeState _ (BitVec.ofNat 32 status.code) memoryRead
      (wX_bits_run_x10 executeState _)
  refine ⟨retired, ?_⟩
  exact raw_error_load_try_step (fromStep + 1) afterAuipc pc retired 0 0
    (BitVec.ofNat 64 status.code) fetchPlatform fetchNoMMIO
    (raw_error_load_fetch afterAuipc firstCode) interrupts (by rfl)
    (raw_error_load_decode (tryStepControlFlowAfterIncrement afterAuipc)
      privilegeIncrement mseccfgBits seccfgIncrement)
    notExpected execute hartRead inhibitRead configRead (by decide) (by decide) retiredRead

/-- The selected compiled `zesu_raw_error` instance satisfies its source contract by executing its
two non-return instructions in Sail. -/
theorem rawErrorInstanceObligation_proved
    {functionInstance : BinaryFv.Binary.Elfling.FunctionInstance}
    (member : functionInstance ∈
      BinaryFv.Zesu.Elflings.Generated.generatedProgram.functionInstances)
    (entry : functionInstance.entryPc = resolvedSymbols.rawError) :
    RawErrorInstanceObligation functionInstance := by
  intro model fromStep state sourcePre machine
  obtain ⟨firstRetired, firstStep⟩ := raw_error_auipc_step fromStep state machine
  obtain ⟨secondRetired, secondStep⟩ :=
    raw_error_load_step fromStep state model.status sourcePre.2.2.2 machine firstRetired
  let afterAuipc := rawErrorAfterAuipc state firstRetired
  let final := rawErrorAfterLoad afterAuipc secondRetired model.status.code
  obtain ⟨entryRegion, loadRegion, exitRegion⟩ :=
    rawError_function_instance_execution_pc_membership member entry
  have exits := rawError_function_instance_exits member entry
  have entryWord : functionInstanceEntryWord functionInstance = BitVec.ofNat 64 0x13780 := by
    simp [functionInstanceEntryWord, entry, rawError_entry_address]
  have stateAtEntry : state.regs.get? PC = some (functionInstanceEntryWord functionInstance) := by
    rw [entryWord]
    rw [← rawError_entry_address]
    exact machine.entry
  have entryNotExit : ¬ functionInstanceExitPred functionInstance (BitVec.ofNat 64 0x13780) := by
    simp [functionInstanceExitPred, FunctionInstance.isExit, exits]
  have afterAuipcPc : afterAuipc.regs.get? PC = some (BitVec.ofNat 64 0x13784) :=
    afterRegisterWrite_pc state (BitVec.ofNat 64 0x13780) firstRetired x10
      (BitVec.ofNat 64 0x4215780)
  have loadNotExit : ¬ functionInstanceExitPred functionInstance (BitVec.ofNat 64 0x13784) := by
    simp [functionInstanceExitPred, FunctionInstance.isExit, exits]
  have finalPc : final.regs.get? PC = some (BitVec.ofNat 64 0x13788) := by
    exact rawErrorAfterLoad_pc afterAuipc secondRetired model.status.code
  have finalExit : functionInstanceExitPred functionInstance (BitVec.ofNat 64 0x13788) := by
    simp [functionInstanceExitPred, FunctionInstance.isExit, exits]
  have trace := raw_error_entered_function_trace_of_two_steps
    (region := functionInstanceExecutionPcs generatedProgram functionInstance)
    (exit := functionInstanceExitPred functionInstance)
    stateAtEntry (entryWord.symm ▸ entryRegion) (entryWord.symm ▸ entryNotExit)
    afterAuipcPc loadRegion loadNotExit firstStep secondStep finalPc finalExit
  have finalMem : final.mem = state.mem := by
    exact (rawErrorAfterLoad_mem afterAuipc secondRetired model.status.code).trans
      (rawErrorAfterAuipc_mem state firstRetired)
  have finalAgree : Agree platformPreserved state final :=
    (rawErrorAfterAuipc_agree state firstRetired).trans
      (rawErrorAfterLoad_agree afterAuipc secondRetired model.status.code)
  have post : (contractRawError canonicalContractParams.env canonicalContractParams.globals).post
      model ((contractRawError canonicalContractParams.env
        canonicalContractParams.globals).meaning model) state final := by
    refine ⟨?_, ?_, ?_, finalAgree,
      rawErrorAfterLoad_retired_present afterAuipc secondRetired model.status.code, rfl, ?_⟩
    · show canonicalContractParams.env.image.fileBytesLoadedFaithfully final.mem
      rw [finalMem]
      exact sourcePre.2.1
    · intro address _
      exact congrArg (fun memory => memory.get? address) finalMem
    · intro address _
      exact congrArg (fun memory => memory.get? address) finalMem
    · exact rawErrorAfterLoad_x10 afterAuipc secondRetired model.status.code
  exact ⟨⟨2, final, by simp [contractRawError], trace, post⟩⟩

end BinaryFv.Zesu.MachineExecution
