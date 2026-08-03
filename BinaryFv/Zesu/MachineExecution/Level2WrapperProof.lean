import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof

/-!
# Sail execution of the `zesu_decode_raw` wrapper

This file executes instructions owned by the emitted wrapper. Selected allocator, inlined `decode`,
and `memcpy` regions are composed through `Level2ChildSummary`; they are not re-proved here.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.ProgramImage BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem readStackPointer (state : State) (value : BitVec 64)
    (stored : state.regs.get? x2 = some value) :
    Runs (rX_bits (.Regidx 2#5)) state state value := by
  have index : (Sail.BitVec.toNatInt (2#5 : BitVec 5)).toNat = 2 := rfl
  unfold Runs
  simp [rX_bits, rX, index, regval_from_reg, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable,
    getThe, MonadState.get, MonadStateOf.get, stored]

private theorem writeStackPointer (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 2#5) value) state
      { state with regs := state.regs.insert x2 value } () := by
  have index : (Sail.BitVec.toNatInt (2#5 : BitVec 5)).toNat = 2 := rfl
  unfold Runs
  simp only [wX_bits, wX, index, regval_into_reg, PreSail.writeReg, EStateM.run,
    EStateM.bind, EStateM.modifyGet, EStateM.instMonad, MonadState.modifyGet,
    MonadStateOf.modifyGet, modify]
  rw [if_pos (by decide)]
  exact xreg_write_callback_run _ _ _

/-- Exact post-state of an emitted aligned eight-byte stack store. -/
def wrapperAfterDwordStore (state : State) (pc retired target data : BitVec 64) : State :=
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc
  tryStepControlFlowAfterRetired
    (afterWriteBytes (width := 8) executeState target.toNat data)
    (Sail.BitVec.addInt pc 4) retired

/-- Shared Sail execution for the wrapper's stack stores. The concrete caller fixes the ELF word,
decoded source register, immediate, live register values, and exact writable stack address. -/
theorem wrapper_dword_store_step {instructionPcs : BitVec 64 → Prop}
    {machineArgs : DecoderMachineArgs} {baseState state : State}
    (machine : DecoderMachinePre instructionPcs machineArgs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc : BitVec 64) (pcIn : instructionPcs pc)
    (atPc : state.regs.get? PC = some pc)
    (byte0 byte1 byte2 byte3 : BitVec 8) (immediate : BitVec 12)
    (source : regidx) (stackBits data target : BitVec 64)
    (stackValue : state.regs.get? x2 = some stackBits)
    (dataAtExecute : Runs (rX_bits source)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) data)
    (targetEq : stackBits + sign_extend immediate = target)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr target) 8 = true)
    (allowed : DecoderAccessRange DecoderWritableByte target 8)
    (fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      byte0 byte1 byte2 byte3)
    (baseEncoding : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (immediate, source, .Regidx 2#5, 8))) :
    ∃ retired, Runs (try_step stepNo false) state
      (wrapperAfterDwordStore state pc retired target data) false := by
  obtain ⟨mstatusBits, mstatusRead, mprvDisabled⟩ := machine.mstatus
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := machine.mseccfg
  obtain ⟨_stepMseccfgBits, platform⟩ := decoderStepPlatform_of_decoderAgree machine agree pc atPc pcIn
    byte0 byte1 byte2 byte3 fetchBytes
  obtain ⟨fetch, fetchNoMMIO, fetched, interrupts, notExpected, -, -⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal agree retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ :=
    counters
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc
  let afterExec := afterWriteBytes (width := 8) executeState target.toNat data
  have stepAgree : Agree decoderPreserved state executeState :=
    Agree.weaken (fun _ preserved => preserved.2) (agree_stepPremiseState state pc)
  have executeAgree : Agree decoderPreserved baseState executeState := agree.trans stepAgree
  have stackAtExecute : executeState.regs.get? x2 = some stackBits := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using stackValue
  have addressRun := get_transformed_data_addr_machine_store_run executeState
    (.Regidx 2#5) 8 stackBits (sign_extend immediate) mstatusBits mseccfgBits
    (readStackPointer executeState stackBits stackAtExecute)
    ((executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead)
    ((executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      machine.normal.2.1)
    mprvDisabled
    ((executeAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead)
    pmmDisabled
  obtain ⟨physical, storeNoMMIO⟩ :=
    machine.dataAccess.store executeState target 8 executeAgree allowed
  have memoryWrite : Runs (PreSail.writeBytes (n := 8) target.toNat data)
      executeState afterExec true := by
    simpa [afterExec] using writeBytes_run_exact (width := 8) executeState target.toNat data
  have execute : Runs (execute (.STORE (immediate, source, .Regidx 2#5, 8)))
      executeState afterExec (.Retire_Success ()) :=
    execute_STORE_dword_run executeState afterExec source (.Regidx 2#5) immediate target
      mstatusBits data
      ((executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead)
      ((executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
        machine.normal.2.1)
      mprvDisabled dataAtExecute (by simpa [targetEq] using addressRun) aligned physical
      storeNoMMIO memoryWrite
  have afterExecRegs : afterExec.regs = executeState.regs := by
    simpa [afterExec] using afterWriteBytes_regs executeState target.toNat data
  refine ⟨retired, ?_⟩
  simpa [wrapperAfterDwordStore, executeState, afterExec] using
    tryStepFallThroughRetires stepNo state afterExec pc retired inhibit config
      byte0 byte1 byte2 byte3 (.STORE (immediate, source, .Regidx 2#5, 8))
      fetch fetchNoMMIO fetched interrupts baseEncoding decode
      notExpected execute
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- Exact state after the first emitted frame decrement, `addi sp, sp, -0x7f0`. -/
def wrapperAfterFirstFrameDecrement (state : State) (retired stackAtEntry : BitVec 64) : State :=
  afterRegisterWrite state (BitVec.ofNat 64 0x102b0) retired x2
    (iTypeResult .ADDI 0x810#12 stackAtEntry)

theorem wrapper_first_frame_decrement_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102b0)
      0x13#8 0x01#8 0x01#8 0x81#8 :=
  fetchFileInstruction state 0x102b0 0x13 0x01 0x01 0x81
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_first_frame_decrement_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x13#8 0x01#8 0x01#8 0x81#8)) state state
      (.ITYPE (0x810#12, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
  decode_run

theorem wrapper_first_frame_decrement_value (stackBase : Nat)
    (_fits : stackBase + 0xa20 ≤ 2 ^ 64) :
    iTypeResult .ADDI 0x810#12 (BitVec.ofNat 64 (stackBase + 0xa20)) =
      BitVec.ofNat 64 (stackBase + 0x230) := by
  rw [show BitVec.ofNat 64 (stackBase + 0xa20) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0xa20 by rw [← BitVec.ofNat_add]]
  rw [show BitVec.ofNat 64 (stackBase + 0x230) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x230 by rw [← BitVec.ofNat_add]]
  unfold iTypeResult
  rw [show sign_extend (0x810#12) = (0xfffffffffffff810#64) by decide]
  bv_decide

/-- The wrapper's first owned instruction executes through Sail from the compiled Level 2 entry.
The result is stated using Sail's `iTypeResult`; the prologue composition later reduces it to the
intermediate stack pointer `stackBase + 0x230`. -/
theorem wrapper_first_frame_decrement_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (state : State) (source : preZesuDecodeRaw canonicalContractParams.env
      canonicalContractParams.globals canonicalContractParams.resultBuffer
      canonicalContractParams.repRawV4 DecoderGlobalsModel.fresh args state)
    (machine : ZesuDecodeRawMachinePre args stackBase state) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (wrapperAfterFirstFrameDecrement state retired
          (BitVec.ofNat 64 (stackBase + 0xa20))) false ∧
      (wrapperAfterFirstFrameDecrement state retired
          (BitVec.ofNat 64 (stackBase + 0xa20))).regs.get? x2 =
        some (BitVec.ofNat 64 (stackBase + 0x230)) := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102b0) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetch := wrapper_first_frame_decrement_fetch state source.2.1
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x01#8 0x01#8 0x81#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x810#12, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
    obtain ⟨mseccfgBits, mseccfgRead, -⟩ := machine.machine.mseccfg
    have privilegeRead : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      exact (agree_afterIncrement state cur_privilege (by simp [platformPreserved])).trans
        machine.machine.normal.2.1
    have mseccfgRead' : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
        some mseccfgBits := by
      exact (platformPreserved_mseccfg (agree_afterIncrement state)).trans mseccfgRead
    exact wrapper_first_frame_decrement_decode _
      privilegeRead mseccfgBits mseccfgRead'
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102b0)
  let stackAtEntry := BitVec.ofNat 64 (stackBase + 0xa20)
  let result := iTypeResult .ADDI 0x810#12 stackAtEntry
  have stackRead : executeState.regs.get? x2 = some stackAtEntry := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement, stackAtEntry,
      Std.ExtDHashMap.get?_insert, machine.stackAtEntry]
  have execute : Runs (execute (.ITYPE (0x810#12, .Regidx 2#5, .Regidx 2#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x2 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x810#12 (.Regidx 2#5) (.Regidx 2#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x810#12 (.Regidx 2#5) (.Regidx 2#5) .ADDI
      stackAtEntry (readStackPointer executeState stackAtEntry stackRead)
      (writeStackPointer executeState result)
  obtain ⟨retired, run⟩ :=
    decoderRegisterWriteStep machine.machine (Agree.refl state) machine.machine.retiredCounter
      stepNo (BitVec.ofNat 64 0x102b0) pcIn machine.atEntry
      0x13#8 0x01#8 0x01#8 0x81#8
      (.ITYPE (0x810#12, .Regidx 2#5, .Regidx 2#5, .ADDI)) x2 result fetch
      (by unfold BaseInstructionEncoding; decide) decode
      (by decide) (by decide) (by decide) (by decide) execute
  refine ⟨retired, by simpa [wrapperAfterFirstFrameDecrement, stackAtEntry, result] using run, ?_⟩
  simp [wrapperAfterFirstFrameDecrement, afterRegisterWrite, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
    Std.ExtDHashMap.get?_insert, wrapper_first_frame_decrement_value stackBase
      machine.stackFrameFits]

/-! ## Saved return address -/

theorem wrapper_save_link_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102b4)
      0x23#8 0x34#8 0x11#8 0x7e#8 :=
  fetchFileInstruction state 0x102b4 0x23 0x34 0x11 0x7e
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_save_link_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x23#8 0x34#8 0x11#8 0x7e#8)) state state
      (.STORE (0x7e8#12, .Regidx 1#5, .Regidx 2#5, 8)) := by
  decode_run

theorem wrapper_saved_link_target (stackBase : Nat) :
    BitVec.ofNat 64 (stackBase + 0x230) + sign_extend (0x7e8#12) =
      BitVec.ofNat 64 (stackBase + 0xa18) := by
  rw [show BitVec.ofNat 64 (stackBase + 0x230) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x230 by rw [← BitVec.ofNat_add]]
  rw [show BitVec.ofNat 64 (stackBase + 0xa18) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0xa18 by rw [← BitVec.ofNat_add]]
  rw [show sign_extend (0x7e8#12) = (0x7e8#64) by decide]
  bv_decide

/-- Execute `sd ra, 0x7e8(sp)` and retain the exact saved return-address bytes. -/
theorem wrapper_save_link_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) (frameRetired : BitVec 64) :
    ∃ link storeRetired,
      Runs (try_step stepNo false)
        (wrapperAfterFirstFrameDecrement entry frameRetired
          (BitVec.ofNat 64 (stackBase + 0xa20)))
        (wrapperAfterDwordStore
          (wrapperAfterFirstFrameDecrement entry frameRetired
            (BitVec.ofNat 64 (stackBase + 0xa20)))
          (BitVec.ofNat 64 0x102b4) storeRetired
          (BitVec.ofNat 64 (stackBase + 0xa18)) link) false := by
  let state := wrapperAfterFirstFrameDecrement entry frameRetired
    (BitVec.ofNat 64 (stackBase + 0xa20))
  obtain ⟨link, linkAtEntry⟩ := machine.linkAtEntry
  have statePc : state.regs.get? PC = some (BitVec.ofNat 64 0x102b4) := by
    simp [state, wrapperAfterFirstFrameDecrement, afterRegisterWrite_pc]
    decide
  have stateStack : state.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)) := by
    simp [state, wrapperAfterFirstFrameDecrement, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      wrapper_first_frame_decrement_value stackBase machine.stackFrameFits]
  have stateLink : state.regs.get? x1 = some link := by
    simp [state, wrapperAfterFirstFrameDecrement, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, linkAtEntry]
  have stateAgree : Agree decoderPreserved entry state := by
    exact afterRegisterWrite_agree_of
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
  have stateRetired : RetiredCounterPresent state := by
    exact afterRegisterWrite_retired_present entry (BitVec.ofNat 64 0x102b0) frameRetired x2
      (iTypeResult .ADDI 0x810#12 (BitVec.ofNat 64 (stackBase + 0xa20)))
  have code : canonicalContractParams.env.CodeIntact state := by
    simpa [state, wrapperAfterFirstFrameDecrement, afterRegisterWrite_mem] using source.2.1
  have fetch := wrapper_save_link_fetch state code
  have decode : Runs (ext_decode (fetchWord 0x23#8 0x34#8 0x11#8 0x7e#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (0x7e8#12, .Regidx 1#5, .Regidx 2#5, 8)) := by
    obtain ⟨mseccfgBits, mseccfgRead, -⟩ := machine.machine.mseccfg
    exact wrapper_save_link_decode _
      ((Agree.trans stateAgree (Agree.weaken (fun _ preserved => preserved.2)
          (agree_afterIncrement state))) cur_privilege
        (by simp [decoderPreserved, platformPreserved]) |>.trans machine.machine.normal.2.1)
      mseccfgBits
      ((Agree.trans stateAgree (Agree.weaken (fun _ preserved => preserved.2)
          (agree_afterIncrement state))) mseccfg
        (by simp [decoderPreserved, platformPreserved]) |>.trans mseccfgRead)
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102b4)
  have linkAtExecute : executeState.regs.get? x1 = some link := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using stateLink
  have dataRun : Runs (rX_bits (.Regidx 1#5)) executeState executeState link :=
    rX_bits_run_x1 executeState link linkAtExecute
  have targetToNat : (BitVec.ofNat 64 (stackBase + 0xa18)).toNat = stackBase + 0xa18 := by
    have wordSize : 2 ^ 64 = 18446744073709551616 := by native_decide
    have frameFits := machine.stackFrameFits
    rw [wordSize] at frameFits
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have allowed : DecoderAccessRange DecoderWritableByte
      (BitVec.ofNat 64 (stackBase + 0xa18)) 8 := by
    rw [DecoderAccessRange, targetToNat]
    refine ⟨by simpa [Nat.add_assoc] using machine.stackFrameFits, ?_⟩
    intro index bound
    exact Or.inl (by simpa [Nat.add_assoc] using
      machine.stackFrameWritable (0xa18 + index) (by omega))
  have aligned : is_aligned_vaddr
      (virtaddr.Virtaddr (BitVec.ofNat 64 (stackBase + 0xa18))) 8 = true := by
    simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by
      have wordSize : 2 ^ 64 = 18446744073709551616 := by native_decide
      have frameFits := machine.stackFrameFits
      rw [wordSize] at frameFits
      omega)]
    have natAligned : (stackBase + 0xa18) % 8 = 0 := by
      have stackAligned := machine.stackAligned
      omega
    simp [Int.tmod, natAligned]
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102b4) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  obtain ⟨storeRetired, run⟩ := wrapper_dword_store_step machine.machine stateAgree stateRetired
    stepNo (BitVec.ofNat 64 0x102b4) pcIn statePc 0x23#8 0x34#8 0x11#8 0x7e#8
    0x7e8#12 (.Regidx 1#5) (BitVec.ofNat 64 (stackBase + 0x230)) link
    (BitVec.ofNat 64 (stackBase + 0xa18)) stateStack dataRun
    (wrapper_saved_link_target stackBase) aligned allowed fetch
    (by unfold BaseInstructionEncoding; decide) decode
  exact ⟨link, storeRetired, by simpa [state] using run⟩

end BinaryFv.Zesu.MachineExecution
