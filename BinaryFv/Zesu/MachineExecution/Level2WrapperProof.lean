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

theorem wrapperAfterDwordStore_agree (state : State) (pc retired target data : BitVec 64) :
    Agree decoderPreserved state (wrapperAfterDwordStore state pc retired target data) := by
  intro register preserved
  have notPc : PC ≠ register := by
    intro equal; subst register
    simpa [decoderPreserved, platformPreserved] using preserved
  have notNextPc : nextPC ≠ register := by
    intro equal; subst register
    simpa [decoderPreserved, platformPreserved] using preserved
  have notIncrement : minstret_increment ≠ register := by
    intro equal; subst register
    simpa [decoderPreserved, platformPreserved] using preserved
  have notRetired : minstret ≠ register := by
    intro equal; subst register
    simpa [decoderPreserved, platformPreserved] using preserved
  simp [wrapperAfterDwordStore, afterWriteBytes_regs, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
    Std.ExtDHashMap.get?_insert, notPc, notNextPc, notIncrement, notRetired]

theorem wrapperAfterDwordStore_retired (state : State) (pc retired target data : BitVec 64) :
    RetiredCounterPresent (wrapperAfterDwordStore state pc retired target data) := by
  refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
  simp [wrapperAfterDwordStore, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    afterWriteBytes_regs]

theorem wrapperAfterDwordStore_register (state : State) (pc retired target data : BitVec 64)
    (register : Register) (notPc : PC ≠ register) (notNextPc : nextPC ≠ register)
    (notIncrement : minstret_increment ≠ register) (notRetired : minstret ≠ register) :
    (wrapperAfterDwordStore state pc retired target data).regs.get? register =
      state.regs.get? register := by
  simp [wrapperAfterDwordStore, afterWriteBytes_regs, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
    Std.ExtDHashMap.get?_insert, notPc, notNextPc, notIncrement, notRetired]

theorem wrapperAfterDwordStore_pc (state : State) (pc retired target data : BitVec 64) :
    (wrapperAfterDwordStore state pc retired target data).regs.get? PC =
      some (Sail.BitVec.addInt pc 4) := by
  simp [wrapperAfterDwordStore, afterWriteBytes_regs, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
    Std.ExtDHashMap.get?_insert]

theorem canonicalStack_not_fileByte {address : Nat}
    (stack : canonicalContractParams.env.stack address) :
    canonicalContractParams.env.image.readFileByte? address = none := by
  simp only [canonicalContractParams, canonicalEnvironment] at stack ⊢
  cases read : Artifacts.programImage.readFileByte? address with
  | none => rfl
  | some byte =>
      exact False.elim (canonicalStack_above_loaded address
        (Nat.lt_trans (file_addr_lt read) (by decide)) stack)

theorem wrapperAfterDwordStore_code (state : State) (pc retired target data : BitVec 64)
    (stack : ∀ index, index < 8 →
      canonicalContractParams.env.stack (target.toNat + index))
    (code : canonicalContractParams.env.CodeIntact state) :
    canonicalContractParams.env.CodeIntact
      (wrapperAfterDwordStore state pc retired target data) := by
  have notFile : ∀ index : Fin 8,
      canonicalContractParams.env.image.readFileByte? (target.toNat + index.val) = none :=
    fun index => canonicalStack_not_fileByte (stack index.val index.isLt)
  have written := fileBytesMatchMemory_afterWriteBytes canonicalContractParams.env.image
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    target.toNat data notFile
    (by simpa [coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code)
  simpa [wrapperAfterDwordStore, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]
    using written

/-- Instantiate the shared store theorem at an aligned offset in the declared wrapper stack frame. -/
theorem wrapper_stack_store_step (args : ZesuDecodeRawArgs) (stackBase : Nat)
    (entry state : State) (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree decoderPreserved entry state) (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc : BitVec 64)
    (pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw pc)
    (atPc : state.regs.get? PC = some pc)
    (byte0 byte1 byte2 byte3 : BitVec 8) (immediate : BitVec 12) (source : regidx)
    (data : BitVec 64) (offset : Nat) (offsetEnd : offset + 8 ≤ 0xa20)
    (offsetAligned : offset % 8 = 0)
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)))
    (dataAtExecute : Runs (rX_bits source)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) data)
    (targetEq : BitVec.ofNat 64 (stackBase + 0x230) + sign_extend immediate =
      BitVec.ofNat 64 (stackBase + offset))
    (fetch : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      byte0 byte1 byte2 byte3)
    (baseEncoding : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (immediate, source, .Regidx 2#5, 8))) :
    ∃ retired, Runs (try_step stepNo false) state
      (wrapperAfterDwordStore state pc retired (BitVec.ofNat 64 (stackBase + offset)) data) false := by
  have wordSize : 2 ^ 64 = 18446744073709551616 := by native_decide
  have frameFits := machine.stackFrameFits
  rw [wordSize] at frameFits
  have targetToNat : (BitVec.ofNat 64 (stackBase + offset)).toNat = stackBase + offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have allowed : DecoderAccessRange DecoderWritableByte
      (BitVec.ofNat 64 (stackBase + offset)) 8 := by
    rw [DecoderAccessRange, targetToNat]
    refine ⟨by omega, ?_⟩
    intro index bound
    exact Or.inl (by simpa [Nat.add_assoc] using
      machine.stackFrameWritable (offset + index) (by omega))
  have aligned : is_aligned_vaddr
      (virtaddr.Virtaddr (BitVec.ofNat 64 (stackBase + offset))) 8 = true := by
    simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    have stackAligned := machine.stackAligned
    have targetAligned : (stackBase + offset) % 8 = 0 := by omega
    simp [Int.tmod, targetAligned]
  exact wrapper_dword_store_step machine.machine agree retiredPresent stepNo pc pcIn atPc
    byte0 byte1 byte2 byte3 immediate source (BitVec.ofNat 64 (stackBase + 0x230)) data
    (BitVec.ofNat 64 (stackBase + offset)) stackValue dataAtExecute targetEq aligned allowed fetch
    baseEncoding decode

theorem wrapperAfterStackStore_code (args : ZesuDecodeRawArgs) (stackBase offset : Nat)
    (entry state : State) (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (offsetEnd : offset + 8 ≤ 0xa20) (pc retired data : BitVec 64)
    (code : canonicalContractParams.env.CodeIntact state) :
    canonicalContractParams.env.CodeIntact
      (wrapperAfterDwordStore state pc retired (BitVec.ofNat 64 (stackBase + offset)) data) := by
  have wordSize : 2 ^ 64 = 18446744073709551616 := by native_decide
  have frameFits := machine.stackFrameFits
  rw [wordSize] at frameFits
  have targetToNat : (BitVec.ofNat 64 (stackBase + offset)).toNat = stackBase + offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine wrapperAfterDwordStore_code state pc retired _ data ?_ code
  intro index bound
  rw [targetToNat]
  simpa [Nat.add_assoc] using machine.stackFrameWritable (offset + index) (by omega)

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

theorem wrapper_save_s0_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102b8)
      0x23#8 0x30#8 0x81#8 0x7e#8 :=
  fetchFileInstruction state 0x102b8 0x23 0x30 0x81 0x7e
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_save_s1_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102bc)
      0x23#8 0x3c#8 0x91#8 0x7c#8 :=
  fetchFileInstruction state 0x102bc 0x23 0x3c 0x91 0x7c
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_save_s2_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102c0)
      0x23#8 0x38#8 0x21#8 0x7d#8 :=
  fetchFileInstruction state 0x102c0 0x23 0x38 0x21 0x7d
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_save_s0_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x23#8 0x30#8 0x81#8 0x7e#8)) state state
      (.STORE (0x7e0#12, .Regidx 8#5, .Regidx 2#5, 8)) := by
  decode_run

theorem wrapper_save_s1_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x23#8 0x3c#8 0x91#8 0x7c#8)) state state
      (.STORE (0x7d8#12, .Regidx 9#5, .Regidx 2#5, 8)) := by
  decode_run

theorem wrapper_save_s2_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x23#8 0x38#8 0x21#8 0x7d#8)) state state
      (.STORE (0x7d0#12, .Regidx 18#5, .Regidx 2#5, 8)) := by
  decode_run

theorem wrapper_saved_s0_target (stackBase : Nat) :
    BitVec.ofNat 64 (stackBase + 0x230) + sign_extend (0x7e0#12) =
      BitVec.ofNat 64 (stackBase + 0xa10) := by
  rw [show BitVec.ofNat 64 (stackBase + 0x230) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x230 by rw [← BitVec.ofNat_add]]
  rw [show BitVec.ofNat 64 (stackBase + 0xa10) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0xa10 by rw [← BitVec.ofNat_add]]
  rw [show sign_extend (0x7e0#12) = (0x7e0#64) by decide]
  bv_decide

theorem wrapper_saved_s1_target (stackBase : Nat) :
    BitVec.ofNat 64 (stackBase + 0x230) + sign_extend (0x7d8#12) =
      BitVec.ofNat 64 (stackBase + 0xa08) := by
  rw [show BitVec.ofNat 64 (stackBase + 0x230) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x230 by rw [← BitVec.ofNat_add]]
  rw [show BitVec.ofNat 64 (stackBase + 0xa08) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0xa08 by rw [← BitVec.ofNat_add]]
  rw [show sign_extend (0x7d8#12) = (0x7d8#64) by decide]
  bv_decide

theorem wrapper_saved_s2_target (stackBase : Nat) :
    BitVec.ofNat 64 (stackBase + 0x230) + sign_extend (0x7d0#12) =
      BitVec.ofNat 64 (stackBase + 0xa00) := by
  rw [show BitVec.ofNat 64 (stackBase + 0x230) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x230 by rw [← BitVec.ofNat_add]]
  rw [show BitVec.ofNat 64 (stackBase + 0xa00) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0xa00 by rw [← BitVec.ofNat_add]]
  rw [show sign_extend (0x7d0#12) = (0x7d0#64) by decide]
  bv_decide

private theorem wrapper_decode_machine_state (entry state : State)
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (zesuDecodeRawMachineArgs args) entry)
    (agree : Agree decoderPreserved entry state) :
    ∃ mseccfgBits,
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine ∧
      (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits := by
  obtain ⟨mseccfgBits, mseccfgRead, -⟩ := machine.mseccfg
  have currentAgree := Agree.trans agree
    (Agree.weaken (fun _ preserved => preserved.2) (agree_afterIncrement state))
  exact ⟨mseccfgBits,
    (currentAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      machine.normal.2.1,
    (currentAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead⟩

/-- Execute the emitted save of the incoming `s0` value. -/
theorem wrapper_save_s0_step (stepNo : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat)
    (entry state : State) (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree decoderPreserved entry state) (retired : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102b8))
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)))
    (value : BitVec 64) (stored : state.regs.get? x8 = some value) :
    ∃ nextRetired, Runs (try_step stepNo false) state
      (wrapperAfterDwordStore state (BitVec.ofNat 64 0x102b8) nextRetired
        (BitVec.ofNat 64 (stackBase + 0xa10)) value) false := by
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102b8)
  have storedAtExecute : executeState.regs.get? x8 = some value := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using stored
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ :=
    wrapper_decode_machine_state entry state machine.machine agree
  apply wrapper_stack_store_step args stackBase entry state machine agree retired stepNo
    (BitVec.ofNat 64 0x102b8)
    (by apply functionInstanceExecutionPcs_iff_ranges.mpr
        apply RegionPcs.iff_inRanges.mpr
        native_decide)
    atPc 0x23#8 0x30#8 0x81#8 0x7e#8 0x7e0#12 (.Regidx 8#5) value 0xa10
    (by decide) (by decide) stack
    (rX_x8_run executeState value storedAtExecute) (wrapper_saved_s0_target stackBase)
    (wrapper_save_s0_fetch state code) (by unfold BaseInstructionEncoding; decide)
    (wrapper_save_s0_decode _ privilege mseccfgBits mseccfgRead)

/-- Execute the emitted save of the incoming `s1` value. -/
theorem wrapper_save_s1_step (stepNo : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat)
    (entry state : State) (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree decoderPreserved entry state) (retired : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102bc))
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)))
    (value : BitVec 64) (stored : state.regs.get? x9 = some value) :
    ∃ nextRetired, Runs (try_step stepNo false) state
      (wrapperAfterDwordStore state (BitVec.ofNat 64 0x102bc) nextRetired
        (BitVec.ofNat 64 (stackBase + 0xa08)) value) false := by
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102bc)
  have storedAtExecute : executeState.regs.get? x9 = some value := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using stored
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ :=
    wrapper_decode_machine_state entry state machine.machine agree
  apply wrapper_stack_store_step args stackBase entry state machine agree retired stepNo
    (BitVec.ofNat 64 0x102bc)
    (by apply functionInstanceExecutionPcs_iff_ranges.mpr
        apply RegionPcs.iff_inRanges.mpr
        native_decide)
    atPc 0x23#8 0x3c#8 0x91#8 0x7c#8 0x7d8#12 (.Regidx 9#5) value 0xa08
    (by decide) (by decide) stack
    (rX_x9_run executeState value storedAtExecute) (wrapper_saved_s1_target stackBase)
    (wrapper_save_s1_fetch state code) (by unfold BaseInstructionEncoding; decide)
    (wrapper_save_s1_decode _ privilege mseccfgBits mseccfgRead)

/-- Execute the emitted save of the incoming `s2` value. -/
theorem wrapper_save_s2_step (stepNo : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat)
    (entry state : State) (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree decoderPreserved entry state) (retired : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102c0))
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)))
    (value : BitVec 64) (stored : state.regs.get? x18 = some value) :
    ∃ nextRetired, Runs (try_step stepNo false) state
      (wrapperAfterDwordStore state (BitVec.ofNat 64 0x102c0) nextRetired
        (BitVec.ofNat 64 (stackBase + 0xa00)) value) false := by
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102c0)
  have storedAtExecute : executeState.regs.get? x18 = some value := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using stored
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ :=
    wrapper_decode_machine_state entry state machine.machine agree
  apply wrapper_stack_store_step args stackBase entry state machine agree retired stepNo
    (BitVec.ofNat 64 0x102c0)
    (by apply functionInstanceExecutionPcs_iff_ranges.mpr
        apply RegionPcs.iff_inRanges.mpr
        native_decide)
    atPc 0x23#8 0x38#8 0x21#8 0x7d#8 0x7d0#12 (.Regidx 18#5) value 0xa00
    (by decide) (by decide) stack
    (rX_bits_run_x18 executeState value storedAtExecute) (wrapper_saved_s2_target stackBase)
    (wrapper_save_s2_fetch state code) (by unfold BaseInstructionEncoding; decide)
    (wrapper_save_s2_decode _ privilege mseccfgBits mseccfgRead)

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

/-- Sail executes the wrapper's frame decrement and all four saved-register stores. -/
theorem wrapper_entry_save_prefix (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    ∃ final, Trace fromStep 5 entry final ∧
      final.regs.get? PC = some (BitVec.ofNat 64 0x102c4) ∧
      final.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)) ∧
      Agree decoderPreserved entry final ∧ RetiredCounterPresent final ∧
      canonicalContractParams.env.CodeIntact final := by
  obtain ⟨frameRetired, frameRun, frameStack⟩ :=
    wrapper_first_frame_decrement_step fromStep args stackBase entry source machine
  let frame := wrapperAfterFirstFrameDecrement entry frameRetired
    (BitVec.ofNat 64 (stackBase + 0xa20))
  obtain ⟨link, linkRetired, linkRun⟩ :=
    wrapper_save_link_step (fromStep + 1) args stackBase entry source machine frameRetired
  let afterLink := wrapperAfterDwordStore frame (BitVec.ofNat 64 0x102b4) linkRetired
    (BitVec.ofNat 64 (stackBase + 0xa18)) link
  have frameAgree : Agree decoderPreserved entry frame := by
    exact afterRegisterWrite_agree_of
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
  have linkAgree : Agree decoderPreserved entry afterLink :=
    frameAgree.trans (wrapperAfterDwordStore_agree frame _ _ _ _)
  have linkStack : afterLink.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)) :=
    (wrapperAfterDwordStore_register frame _ _ _ _ x2 (by decide) (by decide) (by decide)
      (by decide)).trans (by simpa [frame] using frameStack)
  have linkPc : afterLink.regs.get? PC = some (BitVec.ofNat 64 0x102b8) := by
    simpa [afterLink] using wrapperAfterDwordStore_pc frame (BitVec.ofNat 64 0x102b4)
      linkRetired (BitVec.ofNat 64 (stackBase + 0xa18)) link
  have linkCode : canonicalContractParams.env.CodeIntact afterLink := by
    apply wrapperAfterStackStore_code args stackBase 0xa18 entry frame machine (by decide)
    simpa [frame, wrapperAfterFirstFrameDecrement, afterRegisterWrite_mem] using source.2.1
  have linkRetiredPresent := wrapperAfterDwordStore_retired frame
    (BitVec.ofNat 64 0x102b4) linkRetired (BitVec.ofNat 64 (stackBase + 0xa18)) link
  obtain ⟨s0, savedS0⟩ := machine.savedS0AtEntry
  have s0AtFrame : frame.regs.get? x8 = some s0 := by
    simpa [frame, wrapperAfterFirstFrameDecrement, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert] using savedS0
  have s0AtLink : afterLink.regs.get? x8 = some s0 :=
    (wrapperAfterDwordStore_register frame _ _ _ _ x8 (by decide) (by decide) (by decide)
      (by decide)).trans s0AtFrame
  obtain ⟨s0Retired, s0Run⟩ := wrapper_save_s0_step (fromStep + 2) args stackBase entry
    afterLink machine linkAgree linkRetiredPresent linkCode linkPc linkStack s0 s0AtLink
  let afterS0 := wrapperAfterDwordStore afterLink (BitVec.ofNat 64 0x102b8) s0Retired
    (BitVec.ofNat 64 (stackBase + 0xa10)) s0
  have s0Agree : Agree decoderPreserved entry afterS0 :=
    linkAgree.trans (wrapperAfterDwordStore_agree afterLink _ _ _ _)
  have s0Stack : afterS0.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)) :=
    (wrapperAfterDwordStore_register afterLink _ _ _ _ x2 (by decide) (by decide) (by decide)
      (by decide)).trans linkStack
  have s0Pc : afterS0.regs.get? PC = some (BitVec.ofNat 64 0x102bc) := by
    simpa [afterS0] using wrapperAfterDwordStore_pc afterLink (BitVec.ofNat 64 0x102b8)
      s0Retired (BitVec.ofNat 64 (stackBase + 0xa10)) s0
  have s0Code : canonicalContractParams.env.CodeIntact afterS0 :=
    wrapperAfterStackStore_code args stackBase 0xa10 entry afterLink machine (by decide) _ _ _ linkCode
  have s0RetiredPresent := wrapperAfterDwordStore_retired afterLink
    (BitVec.ofNat 64 0x102b8) s0Retired (BitVec.ofNat 64 (stackBase + 0xa10)) s0
  obtain ⟨s1, savedS1⟩ := machine.savedS1AtEntry
  have s1AtFrame : frame.regs.get? x9 = some s1 := by
    simpa [frame, wrapperAfterFirstFrameDecrement, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert] using savedS1
  have s1AtLink : afterLink.regs.get? x9 = some s1 :=
    (wrapperAfterDwordStore_register frame _ _ _ _ x9 (by decide) (by decide) (by decide)
      (by decide)).trans s1AtFrame
  have s1AtS0 : afterS0.regs.get? x9 = some s1 :=
    (wrapperAfterDwordStore_register afterLink _ _ _ _ x9 (by decide) (by decide) (by decide)
      (by decide)).trans s1AtLink
  obtain ⟨s1Retired, s1Run⟩ := wrapper_save_s1_step (fromStep + 3) args stackBase entry
    afterS0 machine s0Agree s0RetiredPresent s0Code s0Pc s0Stack s1 s1AtS0
  let afterS1 := wrapperAfterDwordStore afterS0 (BitVec.ofNat 64 0x102bc) s1Retired
    (BitVec.ofNat 64 (stackBase + 0xa08)) s1
  have s1Agree : Agree decoderPreserved entry afterS1 :=
    s0Agree.trans (wrapperAfterDwordStore_agree afterS0 _ _ _ _)
  have s1Stack : afterS1.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)) :=
    (wrapperAfterDwordStore_register afterS0 _ _ _ _ x2 (by decide) (by decide) (by decide)
      (by decide)).trans s0Stack
  have s1Pc : afterS1.regs.get? PC = some (BitVec.ofNat 64 0x102c0) := by
    simpa [afterS1] using wrapperAfterDwordStore_pc afterS0 (BitVec.ofNat 64 0x102bc)
      s1Retired (BitVec.ofNat 64 (stackBase + 0xa08)) s1
  have s1Code : canonicalContractParams.env.CodeIntact afterS1 :=
    wrapperAfterStackStore_code args stackBase 0xa08 entry afterS0 machine (by decide) _ _ _ s0Code
  have s1RetiredPresent := wrapperAfterDwordStore_retired afterS0
    (BitVec.ofNat 64 0x102bc) s1Retired (BitVec.ofNat 64 (stackBase + 0xa08)) s1
  obtain ⟨s2, savedS2⟩ := machine.savedS2AtEntry
  have s2AtFrame : frame.regs.get? x18 = some s2 := by
    simpa [frame, wrapperAfterFirstFrameDecrement, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert] using savedS2
  have s2AtLink : afterLink.regs.get? x18 = some s2 :=
    (wrapperAfterDwordStore_register frame _ _ _ _ x18 (by decide) (by decide) (by decide)
      (by decide)).trans s2AtFrame
  have s2AtS0 : afterS0.regs.get? x18 = some s2 :=
    (wrapperAfterDwordStore_register afterLink _ _ _ _ x18 (by decide) (by decide) (by decide)
      (by decide)).trans s2AtLink
  have s2AtS1 : afterS1.regs.get? x18 = some s2 :=
    (wrapperAfterDwordStore_register afterS0 _ _ _ _ x18 (by decide) (by decide) (by decide)
      (by decide)).trans s2AtS0
  obtain ⟨s2Retired, s2Run⟩ := wrapper_save_s2_step (fromStep + 4) args stackBase entry
    afterS1 machine s1Agree s1RetiredPresent s1Code s1Pc s1Stack s2 s2AtS1
  let final := wrapperAfterDwordStore afterS1 (BitVec.ofNat 64 0x102c0) s2Retired
    (BitVec.ofNat 64 (stackBase + 0xa00)) s2
  have finalAgree : Agree decoderPreserved entry final :=
    s1Agree.trans (wrapperAfterDwordStore_agree afterS1 _ _ _ _)
  have finalStack : final.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)) :=
    (wrapperAfterDwordStore_register afterS1 _ _ _ _ x2 (by decide) (by decide) (by decide)
      (by decide)).trans s1Stack
  have finalPc : final.regs.get? PC = some (BitVec.ofNat 64 0x102c4) := by
    simpa [final] using wrapperAfterDwordStore_pc afterS1 (BitVec.ofNat 64 0x102c0)
      s2Retired (BitVec.ofNat 64 (stackBase + 0xa00)) s2
  have finalCode : canonicalContractParams.env.CodeIntact final :=
    wrapperAfterStackStore_code args stackBase 0xa00 entry afterS1 machine (by decide) _ _ _ s1Code
  have finalRetired := wrapperAfterDwordStore_retired afterS1
    (BitVec.ofNat 64 0x102c0) s2Retired (BitVec.ofNat 64 (stackBase + 0xa00)) s2
  refine ⟨final, ?_, finalPc, finalStack, finalAgree, finalRetired, finalCode⟩
  refine Trace.step fromStep 4 entry frame final (by simpa [frame] using frameRun) ?_
  refine Trace.step (fromStep + 1) 3 frame afterLink final
    (by simpa [frame, afterLink] using linkRun) ?_
  refine Trace.step (fromStep + 2) 2 afterLink afterS0 final
    (by simpa [afterS0] using s0Run) ?_
  refine Trace.step (fromStep + 3) 1 afterS0 afterS1 final
    (by simpa [afterS1] using s1Run) ?_
  exact Trace.one (fromStep + 4) afterS1 final (by simpa [final] using s2Run)

end BinaryFv.Zesu.MachineExecution
