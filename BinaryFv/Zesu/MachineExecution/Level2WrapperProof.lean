import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof

/-!
# Sail execution of the `zesu_decode_raw` wrapper

This file executes instructions owned by the emitted wrapper. Selected allocator, inlined `decode`,
and `memcpy` regions are composed through `Level2ChildSummary`; they are not re-proved here.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.ProgramImage BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.RiscV.Sep
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

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

private theorem writeSavedS1 (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 9#5) value) state
      { state with regs := state.regs.insert x9 value } () := by
  have index : (Sail.BitVec.toNatInt (9#5 : BitVec 5)).toNat = 9 := rfl
  unfold Runs
  simp only [wX_bits, wX, index, regval_into_reg, PreSail.writeReg, EStateM.run,
    EStateM.bind, EStateM.modifyGet, EStateM.instMonad, MonadState.modifyGet,
    MonadStateOf.modifyGet, modify]
  rw [if_pos (by decide)]
  exact xreg_write_callback_run _ _ _

private theorem writeSavedS0 (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 8#5) value) state
      { state with regs := state.regs.insert x8 value } () := by
  have index : (Sail.BitVec.toNatInt (8#5 : BitVec 5)).toNat = 8 := rfl
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

/-- A wrapper stack store preserves the borrowed input because the compiled entry premise keeps the
entire input interval outside the writable frame. -/
private theorem wrapperAfterDwordStore_inputMemory (args : ZesuDecodeRawArgs) (stackBase : Nat)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (state : State) (pc retired target data : BitVec 64) (targetAddress : Nat)
    (targetValue : target.toNat = targetAddress) (targetInFrame : stackBase ≤ targetAddress)
    (targetEnd : targetAddress + 8 ≤ stackBase + 0xa20)
    (inputMemory : MemoryRepresentation.MemoryBytes state args.inputBase args.bytes) :
    MemoryRepresentation.MemoryBytes
      (wrapperAfterDwordStore state pc retired target data) args.inputBase args.bytes := by
  apply inputMemory.of_mem_eq
  intro inputIndex inputBound
  have outside : ∀ storeIndex : Fin 8,
      target.toNat + storeIndex.val ≠ args.inputBase + inputIndex := by
    intro storeIndex equal
    rw [targetValue] at equal
    rcases machine.inputAvoidsStack with inputBefore | stackBeforeInput
    · omega
    · omega
  have preserved := afterWriteBytes_mem_get?_of_outside
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    target.toNat data (args.inputBase + inputIndex) outside
  simpa [wrapperAfterDwordStore, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using
    preserved

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

/-- Execute the wrapper-owned allocator-tag byte store from the configured decoder machine. The
store permission comes from `DecoderDataAccess`, not from a runner-specific return bundle. -/
theorem wrapper_allocator_tag_step_configured {instructionPcs : BitVec 64 → Prop}
    {machineArgs : DecoderMachineArgs} {baseState state : State}
    (machine : DecoderMachinePre instructionPcs machineArgs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state) (code : canonicalContractParams.env.CodeIntact state)
    (stepNo : Nat) (pcIn : instructionPcs (BitVec.ofNat 64 0x102f4))
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102f4))
    (target data : BitVec 64) (targetValue : state.regs.get? x18 = some target)
    (dataValue : state.regs.get? x10 = some data)
    (allowed : DecoderAccessRange DecoderWritableByte target 1) :
    ∃ retired, Runs (try_step stepNo false) state
      (wrapperAfterAllocatorTag state retired target data) false := by
  obtain ⟨mstatusBits, mstatusRead, mprvDisabled⟩ := machine.mstatus
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := machine.mseccfg
  have fetchBytes := wrapper_allocator_tag_fetch state
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
  obtain ⟨stepMseccfgBits, platform⟩ := decoderStepPlatform_of_decoderAgree machine agree
    (BitVec.ofNat 64 0x102f4) atPc pcIn 0x23#8 0x00#8 0xa9#8 0x00#8 fetchBytes
  obtain ⟨fetch, fetchNoMMIO, fetched, interrupts, notExpected, privilegeIncrement,
    seccfgIncrement⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal agree retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ :=
    counters
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102f4)
  let afterExec : State :=
    { executeState with
      mem := executeState.mem.insert target.toNat (Sail.BitVec.extractLsb data 7 0) }
  have stepAgree : Agree decoderPreserved state executeState :=
    Agree.weaken (fun _ preserved => preserved.2)
      (agree_stepPremiseState state (BitVec.ofNat 64 0x102f4))
  have executeAgree : Agree decoderPreserved baseState executeState := agree.trans stepAgree
  have targetAtExecute : executeState.regs.get? x18 = some target := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using targetValue
  have dataAtExecute : executeState.regs.get? x10 = some data := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using dataValue
  have addressCalculation := get_transformed_data_addr_machine_store_run executeState
    (.Regidx 18#5) 1 target 0 mstatusBits mseccfgBits
    (rX_bits_run_x18 executeState target targetAtExecute)
    ((executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead)
    ((executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      machine.normal.2.1)
    mprvDisabled
    ((executeAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead)
    pmmDisabled
  obtain ⟨physical, storeNoMMIO⟩ :=
    machine.dataAccess.store executeState target 1 executeAgree allowed
  have memoryWrite : Runs (PreSail.writeBytes (n := 1) target.toNat
      (Sail.BitVec.extractLsb data 7 0)) executeState afterExec true := by
    simpa [afterExec] using
      writeBytes_byte_run executeState target.toNat (Sail.BitVec.extractLsb data 7 0)
  have execute : Runs (execute (.STORE (0#12, .Regidx 10#5, .Regidx 18#5, 1)))
      executeState afterExec (.Retire_Success ()) :=
    execute_STORE_byte_run executeState afterExec (.Regidx 10#5) (.Regidx 18#5) 0#12
      target mstatusBits data
      ((executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead)
      ((executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
        machine.normal.2.1)
      mprvDisabled (rX_bits_run_x10 executeState data dataAtExecute)
      (by simpa using addressCalculation) physical storeNoMMIO memoryWrite
  refine ⟨retired, ?_⟩
  simpa [wrapperAfterAllocatorTag, executeState, afterExec] using
    tryStepFallThroughRetires stepNo state afterExec (BitVec.ofNat 64 0x102f4) retired
      inhibit config 0x23#8 0x00#8 0xa9#8 0x00#8
      (.STORE (0#12, .Regidx 10#5, .Regidx 18#5, 1)) fetch fetchNoMMIO fetched interrupts
      (by rfl) (wrapper_allocator_tag_decode _ privilegeIncrement stepMseccfgBits seccfgIncrement)
      notExpected execute (by simp [afterExec, executeState, coreControlFlowNextState])
      (by simp [afterExec, executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by simp [afterExec, executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by simp [afterExec, executeState, coreControlFlowNextState,
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

theorem wrapperAfterDwordStore_platformAgree (state : State)
    (pc retired target data : BitVec 64) :
    Agree platformPreserved state (wrapperAfterDwordStore state pc retired target data) := by
  intro register preserved
  rcases preserved with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wrapperAfterDwordStore, afterWriteBytes_regs, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]

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
    refine ⟨by decide, ?_, ?_⟩
    · omega
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

theorem wrapperAfterStackStore_attempted (args : ZesuDecodeRawArgs) (stackBase offset : Nat)
    (entry state : State) (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (offsetEnd : offset + 8 ≤ 0xa20) (pc retired data : BitVec 64) :
    (wrapperAfterDwordStore state pc retired (BitVec.ofNat 64 (stackBase + offset)) data).mem.get?
        0x4215020 = state.mem.get? 0x4215020 := by
  have wordSize : 2 ^ 64 = 18446744073709551616 := by native_decide
  have frameFits := machine.stackFrameFits
  rw [wordSize] at frameFits
  have targetToNat : (BitVec.ofNat 64 (stackBase + offset)).toNat = stackBase + offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have attemptedNotStack : ¬ canonicalContractParams.env.stack 0x4215020 := by
    simp only [canonicalContractParams, canonicalEnvironment, canonicalStack, range]
    native_decide
  simp only [wrapperAfterDwordStore, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick]
  apply afterWriteBytes_mem_get?_of_outside
  intro index equal
  have stack := machine.stackFrameWritable (offset + index.val) (by omega)
  apply attemptedNotStack
  rw [targetToNat] at equal
  have stackAtWritten : canonicalContractParams.env.stack
      ((stackBase + offset) + index.val) := by
    simpa [Nat.add_assoc] using stack
  exact equal ▸ stackAtWritten

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
    refine ⟨by decide, ?_, ?_⟩
    · simpa [Nat.add_assoc] using machine.stackFrameFits
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
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary fromStep 5 entry final ∧
      final.regs.get? PC = some (BitVec.ofNat 64 0x102c4) ∧
      final.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)) ∧
      final.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) ∧
      final.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size) ∧
      final.mem.get? 0x4215020 = entry.mem.get? 0x4215020 ∧
      MemoryRepresentation.MemoryBytes final args.inputBase args.bytes ∧
      Agree platformPreserved entry final ∧ RetiredCounterPresent final ∧
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
  have framePlatformAgree : Agree platformPreserved entry frame := by
    exact afterRegisterWrite_agree_of
      (by simp [platformPreserved]) (by simp [platformPreserved])
      (by simp [platformPreserved]) (by simp [platformPreserved])
      (by simp [platformPreserved])
  have linkAgree : Agree decoderPreserved entry afterLink :=
    frameAgree.trans (wrapperAfterDwordStore_agree frame _ _ _ _)
  have linkPlatformAgree : Agree platformPreserved entry afterLink :=
    framePlatformAgree.trans (wrapperAfterDwordStore_platformAgree frame _ _ _ _)
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
  have s0PlatformAgree : Agree platformPreserved entry afterS0 :=
    linkPlatformAgree.trans (wrapperAfterDwordStore_platformAgree afterLink _ _ _ _)
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
  have s1PlatformAgree : Agree platformPreserved entry afterS1 :=
    s0PlatformAgree.trans (wrapperAfterDwordStore_platformAgree afterS0 _ _ _ _)
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
  have finalPlatformAgree : Agree platformPreserved entry final :=
    s1PlatformAgree.trans (wrapperAfterDwordStore_platformAgree afterS1 _ _ _ _)
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
  have preserveFourStores (register : Register) (notPc : PC ≠ register)
      (notNextPc : nextPC ≠ register) (notIncrement : minstret_increment ≠ register)
      (notRetired : minstret ≠ register) {value : RegisterType register}
      (atFrame : frame.regs.get? register = some value) :
      final.regs.get? register = some value := by
    exact (wrapperAfterDwordStore_register afterS1 _ _ _ _ register notPc notNextPc
      notIncrement notRetired).trans
      ((wrapperAfterDwordStore_register afterS0 _ _ _ _ register notPc notNextPc
        notIncrement notRetired).trans
      ((wrapperAfterDwordStore_register afterLink _ _ _ _ register notPc notNextPc
        notIncrement notRetired).trans
      ((wrapperAfterDwordStore_register frame _ _ _ _ register notPc notNextPc
        notIncrement notRetired).trans atFrame)))
  have inputAtFrame : frame.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) := by
    simpa [frame, wrapperAfterFirstFrameDecrement, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert] using source.2.2.1
  have lengthAtFrame : frame.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size) := by
    simpa [frame, wrapperAfterFirstFrameDecrement, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert] using source.2.2.2.1
  have finalInput := preserveFourStores x10 (by decide) (by decide) (by decide) (by decide)
    inputAtFrame
  have finalLength := preserveFourStores x11 (by decide) (by decide) (by decide) (by decide)
    lengthAtFrame
  have frameAttempted : frame.mem.get? 0x4215020 = entry.mem.get? 0x4215020 := by
    simpa [frame, wrapperAfterFirstFrameDecrement, afterRegisterWrite_mem]
  have linkAttempted : afterLink.mem.get? 0x4215020 = frame.mem.get? 0x4215020 :=
    wrapperAfterStackStore_attempted args stackBase 0xa18 entry frame machine (by decide) _ _ _
  have s0Attempted : afterS0.mem.get? 0x4215020 = afterLink.mem.get? 0x4215020 :=
    wrapperAfterStackStore_attempted args stackBase 0xa10 entry afterLink machine (by decide) _ _ _
  have s1Attempted : afterS1.mem.get? 0x4215020 = afterS0.mem.get? 0x4215020 :=
    wrapperAfterStackStore_attempted args stackBase 0xa08 entry afterS0 machine (by decide) _ _ _
  have finalAttemptedStep : final.mem.get? 0x4215020 = afterS1.mem.get? 0x4215020 :=
    wrapperAfterStackStore_attempted args stackBase 0xa00 entry afterS1 machine (by decide) _ _ _
  have finalAttempted := finalAttemptedStep.trans
    (s1Attempted.trans (s0Attempted.trans (linkAttempted.trans frameAttempted)))
  have frameInput : MemoryRepresentation.MemoryBytes frame args.inputBase args.bytes := by
    simpa [frame, wrapperAfterFirstFrameDecrement, afterRegisterWrite_mem] using source.1
  have linkInput := wrapperAfterDwordStore_inputMemory args stackBase machine frame
    (BitVec.ofNat 64 0x102b4) linkRetired (BitVec.ofNat 64 (stackBase + 0xa18)) link
    (stackBase + 0xa18) (by
      simp only [BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      have frameFits := machine.stackFrameFits
      omega)
    (by omega) (by omega) frameInput
  have s0Input := wrapperAfterDwordStore_inputMemory args stackBase machine afterLink
    (BitVec.ofNat 64 0x102b8) s0Retired (BitVec.ofNat 64 (stackBase + 0xa10)) s0
    (stackBase + 0xa10) (by
      simp only [BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      have frameFits := machine.stackFrameFits
      omega)
    (by omega) (by omega) linkInput
  have s1Input := wrapperAfterDwordStore_inputMemory args stackBase machine afterS0
    (BitVec.ofNat 64 0x102bc) s1Retired (BitVec.ofNat 64 (stackBase + 0xa08)) s1
    (stackBase + 0xa08) (by
      simp only [BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      have frameFits := machine.stackFrameFits
      omega)
    (by omega) (by omega) s0Input
  have finalInputMemory := wrapperAfterDwordStore_inputMemory args stackBase machine afterS1
    (BitVec.ofNat 64 0x102c0) s2Retired (BitVec.ofNat 64 (stackBase + 0xa00)) s2
    (stackBase + 0xa00) (by
      simp only [BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      have frameFits := machine.stackFrameFits
      omega)
    (by omega) (by omega) s1Input
  have ownStep (stepNo pc : Nat) (before after : State)
      (atPc : before.regs.get? PC = some (BitVec.ofNat 64 pc))
      (inRegion : functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 pc))
      (notExit : ¬ functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw
        (BitVec.ofNat 64 pc))
      (run : Runs (try_step stepNo false) before after false) :
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary stepNo 1 before after := by
    exact ConfinedPrefix.ownStep atPc inRegion notExit run
  have framePc : frame.regs.get? PC = some (BitVec.ofNat 64 0x102b4) := by
    change (wrapperAfterFirstFrameDecrement entry frameRetired
      (BitVec.ofNat 64 (stackBase + 0xa20))).regs.get? PC =
        some (BitVec.ofNat 64 0x102b4)
    unfold wrapperAfterFirstFrameDecrement
    exact afterRegisterWrite_pc entry (BitVec.ofNat 64 0x102b0) frameRetired x2
      (iTypeResult .ADDI 0x810#12 (BitVec.ofNat 64 (stackBase + 0xa20)))
  have prefix0 := ownStep fromStep 0x102b0 entry frame machine.atEntry (by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide)
    (by simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw])
    (by simpa [frame] using frameRun)
  have prefix1 := ownStep (fromStep + 1) 0x102b4 frame afterLink framePc (by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide)
    (by simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw])
    (by simpa [frame, afterLink] using linkRun)
  have prefix2 := ownStep (fromStep + 2) 0x102b8 afterLink afterS0 linkPc (by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide)
    (by simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw])
    (by simpa [afterS0] using s0Run)
  have prefix3 := ownStep (fromStep + 3) 0x102bc afterS0 afterS1 s0Pc (by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide)
    (by simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw])
    (by simpa [afterS1] using s1Run)
  have prefix4 := ownStep (fromStep + 4) 0x102c0 afterS1 final s1Pc (by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide)
    (by simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw])
    (by simpa [final] using s2Run)
  have prefix01 := ConfinedPrefix.trans prefix0 (by simpa using prefix1)
  have prefix012 := ConfinedPrefix.trans prefix01 (by simpa [Nat.add_assoc] using prefix2)
  have prefix0123 := ConfinedPrefix.trans prefix012 (by simpa [Nat.add_assoc] using prefix3)
  have confined : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 5 entry final := by
    simpa [Nat.add_assoc] using ConfinedPrefix.trans prefix0123
      (by simpa [Nat.add_assoc] using prefix4)
  refine ⟨final, ?_, confined, finalPc, finalStack, finalInput, finalLength, finalAttempted,
    finalInputMemory, finalPlatformAgree, finalRetired, finalCode⟩
  refine Trace.step fromStep 4 entry frame final (by simpa [frame] using frameRun) ?_
  refine Trace.step (fromStep + 1) 3 frame afterLink final
    (by simpa [frame, afterLink] using linkRun) ?_
  refine Trace.step (fromStep + 2) 2 afterLink afterS0 final
    (by simpa [afterS0] using s0Run) ?_
  refine Trace.step (fromStep + 3) 1 afterS0 afterS1 final
    (by simpa [afterS1] using s1Run) ?_
  exact Trace.one (fromStep + 4) afterS1 final (by simpa [final] using s2Run)

/-! ## Final frame decrement -/

theorem wrapper_final_frame_decrement_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102c4)
      0x13#8 0x01#8 0x01#8 0xdd#8 :=
  fetchFileInstruction state 0x102c4 0x13 0x01 0x01 0xdd
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_final_frame_decrement_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x13#8 0x01#8 0x01#8 0xdd#8)) state state
      (.ITYPE (0xdd0#12, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
  decode_run

theorem wrapper_final_frame_decrement_value (stackBase : Nat) :
    iTypeResult .ADDI 0xdd0#12 (BitVec.ofNat 64 (stackBase + 0x230)) =
      BitVec.ofNat 64 stackBase := by
  rw [show BitVec.ofNat 64 (stackBase + 0x230) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x230 by rw [← BitVec.ofNat_add]]
  unfold iTypeResult
  rw [show sign_extend (0xdd0#12) = (0xfffffffffffffdd0#64) by decide]
  bv_decide

/-- Execute the second frame decrement from the five-instruction entry-save post-state. -/
theorem wrapper_final_frame_decrement_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry state : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree platformPreserved entry state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102c4))
    (stack : state.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230))) :
    ∃ retired, Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x102c4) retired x2
          (BitVec.ofNat 64 stackBase)) false ∧
      (afterRegisterWrite state (BitVec.ofNat 64 0x102c4) retired x2
          (BitVec.ofNat 64 stackBase)).regs.get? x2 = some (BitVec.ofNat 64 stackBase) := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102c4) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetch := wrapper_final_frame_decrement_fetch state code
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ :=
    wrapper_decode_machine_state entry state machine.machine
      (Agree.weaken (fun _ preserved => preserved.2) agree)
  have decode := wrapper_final_frame_decrement_decode
    (tryStepControlFlowAfterIncrement state) privilege mseccfgBits mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102c4)
  have stackAtExecute : executeState.regs.get? x2 =
      some (BitVec.ofNat 64 (stackBase + 0x230)) := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using stack
  have execute : Runs (execute (.ITYPE (0xdd0#12, .Regidx 2#5, .Regidx 2#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x2 (BitVec.ofNat 64 stackBase) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0xdd0#12 (.Regidx 2#5) (.Regidx 2#5) .ADDI) _ _ _
    rw [← wrapper_final_frame_decrement_value stackBase]
    exact execute_ITYPE_run executeState _ 0xdd0#12 (.Regidx 2#5) (.Regidx 2#5) .ADDI
      (BitVec.ofNat 64 (stackBase + 0x230))
      (readStackPointer executeState _ stackAtExecute)
      (writeStackPointer executeState
        (iTypeResult .ADDI 0xdd0#12 (BitVec.ofNat 64 (stackBase + 0x230))))
  obtain ⟨retired, run⟩ := decoderRegisterWriteStep machine.machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x102c4) pcIn atPc 0x13#8 0x01#8 0x01#8 0xdd#8
    (.ITYPE (0xdd0#12, .Regidx 2#5, .Regidx 2#5, .ADDI)) x2 (BitVec.ofNat 64 stackBase)
    fetch (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute
  refine ⟨retired, run, ?_⟩
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- The complete six-instruction frame setup, ending with the exact final stack pointer. -/
theorem wrapper_complete_frame_prefix (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    ∃ final, Trace fromStep 6 entry final ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary fromStep 6 entry final ∧
      final.regs.get? PC = some (BitVec.ofNat 64 0x102c8) ∧
      final.regs.get? x2 = some (BitVec.ofNat 64 stackBase) ∧
      final.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) ∧
      final.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size) ∧
      final.mem.get? 0x4215020 = entry.mem.get? 0x4215020 ∧
      MemoryRepresentation.MemoryBytes final args.inputBase args.bytes ∧
      Agree platformPreserved entry final ∧ RetiredCounterPresent final ∧
      canonicalContractParams.env.CodeIntact final := by
  obtain ⟨saved, savedTrace, savedPrefix, savedPc, savedStack, savedInput, savedLength,
    savedAttempted, savedInputMemory, savedAgree, savedRetired, savedCode⟩ :=
    wrapper_entry_save_prefix fromStep args stackBase entry source machine
  obtain ⟨retired, run, finalStack⟩ := wrapper_final_frame_decrement_step
    (fromStep + 5) args stackBase entry saved machine savedAgree savedRetired savedCode savedPc savedStack
  let final := afterRegisterWrite saved (BitVec.ofNat 64 0x102c4) retired x2
    (BitVec.ofNat 64 stackBase)
  have finalPc : final.regs.get? PC = some (BitVec.ofNat 64 0x102c8) := by
    simpa [final] using afterRegisterWrite_pc saved (BitVec.ofNat 64 0x102c4) retired x2
      (BitVec.ofNat 64 stackBase)
  have finalInput : final.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) := by
    simpa [final, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using savedInput
  have finalLength : final.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size) := by
    simpa [final, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using savedLength
  have finalAttempted : final.mem.get? 0x4215020 = entry.mem.get? 0x4215020 := by
    simpa [final, afterRegisterWrite_mem] using savedAttempted
  have finalInputMemory : MemoryRepresentation.MemoryBytes final args.inputBase args.bytes := by
    simpa [final, afterRegisterWrite_mem] using savedInputMemory
  have finalAgree : Agree platformPreserved entry final :=
    savedAgree.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  have finalCode : canonicalContractParams.env.CodeIntact final := by
    simpa [final, afterRegisterWrite_mem] using savedCode
  have finalRetired := afterRegisterWrite_retired_present saved (BitVec.ofNat 64 0x102c4)
    retired x2 (BitVec.ofNat 64 stackBase)
  have finalStep : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + 5) 1 saved final := by
    apply ConfinedPrefix.ownStep savedPc
    · apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide
    · simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]
    · simpa [final] using run
  have confined : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 6 entry final := by
    simpa [Nat.add_assoc] using ConfinedPrefix.trans savedPrefix finalStep
  refine ⟨final, ?_, confined, finalPc, by simpa [final] using finalStack, finalInput, finalLength,
    finalAttempted, finalInputMemory, finalAgree, finalRetired, finalCode⟩
  exact Trace.snoc savedTrace (by simpa [final] using run)

/-! ## Preserve the input length in `s1` -/

theorem wrapper_preserve_length_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102c8)
      0x93#8 0x84#8 0x05#8 0x00#8 :=
  fetchFileInstruction state 0x102c8 0x93 0x84 0x05 0x00
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_preserve_length_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x93#8 0x84#8 0x05#8 0x00#8)) state state
      (.ITYPE (0#12, .Regidx 11#5, .Regidx 9#5, .ADDI)) := by
  decode_run

/-- Execute the emitted `mv s1, a1` while retaining the exact input length. -/
theorem wrapper_preserve_length_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry state : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree platformPreserved entry state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102c8))
    (length : state.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x102c8) retired x9
        (BitVec.ofNat 64 args.bytes.size)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102c8) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetch := wrapper_preserve_length_fetch state code
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ :=
    wrapper_decode_machine_state entry state machine.machine
      (Agree.weaken (fun _ preserved => preserved.2) agree)
  have decode := wrapper_preserve_length_decode
    (tryStepControlFlowAfterIncrement state) privilege mseccfgBits mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102c8)
  have lengthAtExecute : executeState.regs.get? x11 =
      some (BitVec.ofNat 64 args.bytes.size) := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using length
  have execute : Runs (execute (.ITYPE (0#12, .Regidx 11#5, .Regidx 9#5, .ADDI)))
      executeState
      { executeState with regs := executeState.regs.insert x9 (BitVec.ofNat 64 args.bytes.size) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0#12 (.Regidx 11#5) (.Regidx 9#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 0#12 (BitVec.ofNat 64 args.bytes.size) =
        BitVec.ofNat 64 args.bytes.size := by
      simp [iTypeResult, show sign_extend (0#12) = (0#64) by decide]
    rw [← resultEq]
    exact execute_ITYPE_run executeState _ 0#12 (.Regidx 11#5)
      (.Regidx 9#5) .ADDI (BitVec.ofNat 64 args.bytes.size)
      (rX_x11_run executeState _ lengthAtExecute)
      (writeSavedS1 executeState
        (iTypeResult .ADDI 0#12 (BitVec.ofNat 64 args.bytes.size)))
  exact decoderRegisterWriteStep machine.machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x102c8) pcIn atPc 0x93#8 0x84#8 0x05#8 0x00#8
    (.ITYPE (0#12, .Regidx 11#5, .Regidx 9#5, .ADDI)) x9
    (BitVec.ofNat 64 args.bytes.size) fetch (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-! ## Materialize the decoder-globals base -/

theorem wrapper_globals_page_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102cc)
      0x97#8 0x55#8 0x20#8 0x04#8 :=
  fetchFileInstruction state 0x102cc 0x97 0x55 0x20 0x04
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_globals_page_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x97#8 0x55#8 0x20#8 0x04#8)) state state
      (.UTYPE (0x04205#20, .Regidx 11#5, .AUIPC)) := by
  decode_run

theorem wrapper_globals_page_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry state : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree platformPreserved entry state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102cc)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x102cc) retired x11
        (BitVec.ofNat 64 0x42152cc)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102cc) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetch := wrapper_globals_page_fetch state code
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ :=
    wrapper_decode_machine_state entry state machine.machine
      (Agree.weaken (fun _ preserved => preserved.2) agree)
  have decode := wrapper_globals_page_decode
    (tryStepControlFlowAfterIncrement state) privilege mseccfgBits mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102cc)
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x102cc) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have resultValue : BitVec.ofNat 64 0x102cc + sign_extend (0x04205#20 ++ 0#12) =
      BitVec.ofNat 64 0x42152cc := by native_decide
  have execute : Runs (execute (.UTYPE (0x04205#20, .Regidx 11#5, .AUIPC))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 0x42152cc) }
      (.Retire_Success ()) := by
    apply execute_UTYPE_auipc_run executeState _ 0x04205#20 (.Regidx 11#5)
      (BitVec.ofNat 64 0x102cc)
    · exact readReg_run _ _ _ pcAtExecute
    · simpa [resultValue] using wX_bits_run_x11 executeState (BitVec.ofNat 64 0x42152cc)
  exact decoderRegisterWriteStep machine.machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x102cc) pcIn atPc 0x97#8 0x55#8 0x20#8 0x04#8
    (.UTYPE (0x04205#20, .Regidx 11#5, .AUIPC)) x11 (BitVec.ofNat 64 0x42152cc)
    fetch (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

theorem wrapper_globals_address_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102d0)
      0x13#8 0x89#8 0x45#8 0xd5#8 :=
  fetchFileInstruction state 0x102d0 0x13 0x89 0x45 0xd5
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_globals_address_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x13#8 0x89#8 0x45#8 0xd5#8)) state state
      (.ITYPE (0xd54#12, .Regidx 11#5, .Regidx 18#5, .ADDI)) := by
  decode_run

theorem wrapper_globals_address_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry state : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree platformPreserved entry state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102d0))
    (page : state.regs.get? x11 = some (BitVec.ofNat 64 0x42152cc)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x102d0) retired x18
        (BitVec.ofNat 64 0x4215020)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102d0) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetch := wrapper_globals_address_fetch state code
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ :=
    wrapper_decode_machine_state entry state machine.machine
      (Agree.weaken (fun _ preserved => preserved.2) agree)
  have decode := wrapper_globals_address_decode
    (tryStepControlFlowAfterIncrement state) privilege mseccfgBits mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102d0)
  have pageAtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 0x42152cc) := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using page
  have resultValue : iTypeResult .ADDI 0xd54#12 (BitVec.ofNat 64 0x42152cc) =
      BitVec.ofNat 64 0x4215020 := by native_decide
  have execute : Runs (execute (.ITYPE (0xd54#12, .Regidx 11#5, .Regidx 18#5, .ADDI)))
      executeState
      { executeState with regs := executeState.regs.insert x18 (BitVec.ofNat 64 0x4215020) }
      (.Retire_Success ()) := by
    apply execute_ITYPE_run executeState _ 0xd54#12 (.Regidx 11#5) (.Regidx 18#5) .ADDI
      (BitVec.ofNat 64 0x42152cc)
    · exact rX_x11_run executeState _ pageAtExecute
    · simpa [resultValue] using wX_x18_run executeState (BitVec.ofNat 64 0x4215020)
  exact decoderRegisterWriteStep machine.machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x102d0) pcIn atPc 0x13#8 0x89#8 0x45#8 0xd5#8
    (.ITYPE (0xd54#12, .Regidx 11#5, .Regidx 18#5, .ADDI)) x18
    (BitVec.ofNat 64 0x4215020) fetch (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-! ## Read the fresh-call flag -/

theorem wrapper_attempted_load_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102d4)
      0x83#8 0x45#8 0x09#8 0x00#8 :=
  fetchFileInstruction state 0x102d4 0x83 0x45 0x09 0x00
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_attempted_load_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x83#8 0x45#8 0x09#8 0x00#8)) state state
      (.LOAD (0#12, .Regidx 18#5, .Regidx 11#5, true, 1)) := by
  decode_run

/-- Execute `lbu a1, 0(s2)` against the represented fresh `attempted` byte. -/
theorem wrapper_attempted_load_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry state : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree platformPreserved entry state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102d4))
    (globals : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
    (fresh : state.mem.get? 0x4215020 = some (0#8)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x102d4) retired x11 (0#64)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102d4) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchBytes := wrapper_attempted_load_fetch state code
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine.machine agree
    (BitVec.ofNat 64 0x102d4) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.machine.normal agree retiredPresent
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have decode := wrapper_attempted_load_decode
    (tryStepControlFlowAfterIncrement state) privilege mseccfgBits mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102d4)
  let address := BitVec.ofNat 64 0x4215020
  have executeAgree : Agree platformPreserved entry executeState :=
    agree.trans (agree_decoderExecuteState state (BitVec.ofNat 64 0x102d4))
  have globalsAtExecute : executeState.regs.get? x18 = some address := by
    simpa [executeState, address, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using globals
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := machine.machine.mstatus
  obtain ⟨machineMseccfgBits, machineMseccfgRead, pmmDisabled⟩ := machine.machine.mseccfg
  have mstatusAtExecute := (executeAgree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegeAtExecute :=
    (executeAgree cur_privilege (by simp [platformPreserved])).trans machine.machine.normal.2.1
  have mseccfgAtExecute :=
    (executeAgree mseccfg (by simp [platformPreserved])).trans machineMseccfgRead
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 18#5) (sign_extend (m := 64) 0#12)
        (MemoryAccessType.Load mem_payload.Data) 1)
      executeState executeState (.Ext_DataAddr_OK (virtaddr.Virtaddr address)) := by
    have zero : sign_extend (m := 64) 0#12 = (0#64) := by decide
    rw [zero]
    simpa using get_transformed_data_addr_machine_load_run executeState (.Regidx 18#5) address
      (0#64) mstatusBits machineMseccfgBits
      (rX_bits_run_x18 executeState address globalsAtExecute) mstatusAtExecute privilegeAtExecute
      mprvZero mseccfgAtExecute pmmDisabled
  have allowed : DecoderAccessRange (DecoderReadableByte (zesuDecodeRawMachineArgs args))
      address 1 := by
    refine ⟨by decide, ?_, ?_⟩
    · native_decide
    intro index bound
    have indexZero : index = 0 := by omega
    subst index
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    simp [address, DecoderGlobalsByte]
    native_decide
  obtain ⟨physAccess, loadNoMMIO⟩ := machine.machine.dataAccess.load executeState address 1
    (Agree.weaken (fun _ preserved => preserved.2) executeAgree) allowed
  have memoryByte : ∀ (index : Nat) (bound : index < (leBytes 1 (0#8)).length),
      executeState.mem.get? (address.toNat + index) =
        some ((leBytes 1 (0#8))[index]'bound) := by
    intro index bound
    have indexZero : index = 0 := by
      rw [leBytes_length] at bound
      omega
    subst index
    simpa [executeState, address, leBytes] using fresh
  have execute : Runs (execute (.LOAD (0#12, .Regidx 18#5, .Regidx 11#5, true, 1)))
      executeState { executeState with regs := executeState.regs.insert x11 (0#64) }
      (.Retire_Success ()) := by
    change Runs (execute_LOAD 0#12 (.Regidx 18#5) (.Regidx 11#5) true 1) _ _ _
    have run := execute_LOAD_lbu_run executeState _ 0#12 (.Regidx 18#5) (.Regidx 11#5)
      address mstatusBits (0#8) mstatusAtExecute privilegeAtExecute mprvZero addressRun
      (is_aligned_vaddr_one _) physAccess loadNoMMIO memoryByte (wX_bits_run_x11 executeState (0#64))
    simpa [zero_extend, Sail.BitVec.zeroExtend] using run
  refine ⟨retired, ?_⟩
  simpa [executeState, afterRegisterWrite] using
    tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x102d4) retired inhibit config
      0x83#8 0x45#8 0x09#8 0x00#8
      (.LOAD (0#12, .Regidx 18#5, .Regidx 11#5, true, 1)) x11 (0#64)
      fetch noMMIO fetched interrupts (by unfold BaseInstructionEncoding; decide) decode
      notExpected execute (by decide) (by decide) (by decide) (by decide)
      hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

def wrapperAfterFreshBranch (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x102d8) (BitVec.ofNat 64 0x102e8))
    (BitVec.ofNat 64 0x102e8) retired

theorem wrapperAfterFreshBranch_register (state : State) (retired : BitVec 64)
    (register : Register) (notPc : PC ≠ register) (notNextPc : nextPC ≠ register)
    (notIncrement : minstret_increment ≠ register) (notRetired : minstret ≠ register) :
    (wrapperAfterFreshBranch state retired).regs.get? register = state.regs.get? register := by
  simp [wrapperAfterFreshBranch, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
    Std.ExtDHashMap.get?_insert, notPc, notNextPc, notIncrement, notRetired]

theorem wrapperAfterFreshBranch_platformAgree (state : State) (retired : BitVec 64) :
    Agree platformPreserved state (wrapperAfterFreshBranch state retired) := by
  intro register preserved
  exact wrapperAfterFreshBranch_register state retired register
    (by intro equal; subst register; simpa [platformPreserved] using preserved)
    (by intro equal; subst register; simpa [platformPreserved] using preserved)
    (by intro equal; subst register; simpa [platformPreserved] using preserved)
    (by intro equal; subst register; simpa [platformPreserved] using preserved)

theorem wrapperAfterFreshBranch_retired (state : State) (retired : BitVec 64) :
    RetiredCounterPresent (wrapperAfterFreshBranch state retired) := by
  refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
  simp [wrapperAfterFreshBranch, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    controlFlowJumpState]

theorem wrapper_fresh_branch_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102d8)
      0x63#8 0x88#8 0x05#8 0x00#8 :=
  fetchFileInstruction state 0x102d8 0x63 0x88 0x05 0x00
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_fresh_branch_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x63#8 0x88#8 0x05#8 0x00#8)) state state
      (.BTYPE (0x10#13, .Regidx 0#5, .Regidx 11#5, .BEQ)) := by
  decode_run

/-- The represented fresh flag forces `beqz a1, 0x102e8` to take its fresh-call edge. -/
theorem wrapper_fresh_branch_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry state : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree platformPreserved entry state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102d8))
    (fresh : state.regs.get? x11 = some (0#64)) :
    ∃ retired, Runs (try_step stepNo false) state (wrapperAfterFreshBranch state retired) false ∧
      (wrapperAfterFreshBranch state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x102e8) := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102d8) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchBytes := wrapper_fresh_branch_fetch state code
  have currentMachine := machine.machine.mono
    (Agree.weaken (fun _ preserved => preserved.2) agree) retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform currentMachine (Agree.refl state)
    (BitVec.ofNat 64 0x102d8) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters currentMachine.normal (Agree.refl state) retiredPresent
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have decode := wrapper_fresh_branch_decode
    (tryStepControlFlowAfterIncrement state) privilege mseccfgBits mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102d8)
  have freshAtExecute : executeState.regs.get? x11 = some (0#64) := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using fresh
  have condition : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 11#5) .BEQ)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_x11_run executeState (0#64) freshAtExecute) ?_
    refine Runs.bind (rX_x0_run executeState) ?_
    rfl
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x102d8) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have targetEq : BitVec.ofNat 64 0x102d8 + sign_extend (m := 64) (0x10#13) =
      BitVec.ofNat 64 0x102e8 := by decide
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      state.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := currentMachine.normal.2.2.2.2.2.2.2.2.2.2.2
    match read : state.regs.get? misa with
    | none => simp [read] at normalMisa
    | some bits => exact ⟨bits, rfl, by simpa [read] using normalMisa⟩
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x102d8)
    misaBits misaRead
  have run := tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x102d8)
    (BitVec.ofNat 64 0x102d8) retired (0x10#13) (.Regidx 0#5) (.Regidx 11#5) .BEQ
    inhibit config 0x63#8 0x88#8 0x05#8 0x00#8 (_get_Misa_C misaBits == 1#1)
    fetch noMMIO fetched interrupts (by unfold BaseInstructionEncoding; decide) decode
    notExpected condition (readReg_run executeState PC _ pcAtExecute)
    (by decide) (by decide) zca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead
  refine ⟨retired, ?_, ?_⟩
  · simpa [wrapperAfterFreshBranch, targetEq] using run
  · simp [wrapperAfterFreshBranch, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- Eleven wrapper-owned Sail steps reach the selected allocator setup on the fresh-call path. -/
theorem wrapper_fresh_prologue_prefix (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    ∃ final, Trace fromStep 11 entry final ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary fromStep 11 entry final ∧
      final.regs.get? PC = some (BitVec.ofNat 64 0x102e8) ∧
      final.regs.get? x2 = some (BitVec.ofNat 64 stackBase) ∧
      final.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) ∧
      final.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      final.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      final.mem.get? 0x4215020 = some (0#8) ∧
      MemoryRepresentation.MemoryBytes final args.inputBase args.bytes ∧
      Agree platformPreserved entry final ∧ RetiredCounterPresent final ∧
      canonicalContractParams.env.CodeIntact final := by
  obtain ⟨s6, trace6, prefix6, pc6, stack6, input6, length6, attempted6, inputMemory6,
    agree6, retired6, code6⟩ :=
    wrapper_complete_frame_prefix fromStep args stackBase entry source machine
  obtain ⟨r7, run7⟩ := wrapper_preserve_length_step (fromStep + 6) args stackBase entry s6
    machine agree6 retired6 code6 pc6 length6
  let s7 := afterRegisterWrite s6 (BitVec.ofNat 64 0x102c8) r7 x9
    (BitVec.ofNat 64 args.bytes.size)
  have pc7 : s7.regs.get? PC = some (BitVec.ofNat 64 0x102cc) := by
    simpa [s7] using afterRegisterWrite_pc s6 (BitVec.ofNat 64 0x102c8) r7 x9
      (BitVec.ofNat 64 args.bytes.size)
  have agree7 : Agree platformPreserved entry s7 :=
    agree6.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired7 := afterRegisterWrite_retired_present s6 (BitVec.ofNat 64 0x102c8) r7 x9
    (BitVec.ofNat 64 args.bytes.size)
  have code7 : canonicalContractParams.env.CodeIntact s7 := by
    simpa [s7, afterRegisterWrite_mem] using code6
  obtain ⟨r8, run8⟩ := wrapper_globals_page_step (fromStep + 7) args stackBase entry s7
    machine agree7 retired7 code7 pc7
  let s8 := afterRegisterWrite s7 (BitVec.ofNat 64 0x102cc) r8 x11
    (BitVec.ofNat 64 0x42152cc)
  have pc8 : s8.regs.get? PC = some (BitVec.ofNat 64 0x102d0) := by
    simpa [s8] using afterRegisterWrite_pc s7 (BitVec.ofNat 64 0x102cc) r8 x11
      (BitVec.ofNat 64 0x42152cc)
  have page8 : s8.regs.get? x11 = some (BitVec.ofNat 64 0x42152cc) := by
    simp [s8, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have agree8 : Agree platformPreserved entry s8 :=
    agree7.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired8 := afterRegisterWrite_retired_present s7 (BitVec.ofNat 64 0x102cc) r8 x11
    (BitVec.ofNat 64 0x42152cc)
  have code8 : canonicalContractParams.env.CodeIntact s8 := by
    simpa [s8, afterRegisterWrite_mem] using code7
  obtain ⟨r9, run9⟩ := wrapper_globals_address_step (fromStep + 8) args stackBase entry s8
    machine agree8 retired8 code8 pc8 page8
  let s9 := afterRegisterWrite s8 (BitVec.ofNat 64 0x102d0) r9 x18
    (BitVec.ofNat 64 0x4215020)
  have pc9 : s9.regs.get? PC = some (BitVec.ofNat 64 0x102d4) := by
    simpa [s9] using afterRegisterWrite_pc s8 (BitVec.ofNat 64 0x102d0) r9 x18
      (BitVec.ofNat 64 0x4215020)
  have globals9 : s9.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [s9, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have agree9 : Agree platformPreserved entry s9 :=
    agree8.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired9 := afterRegisterWrite_retired_present s8 (BitVec.ofNat 64 0x102d0) r9 x18
    (BitVec.ofNat 64 0x4215020)
  have code9 : canonicalContractParams.env.CodeIntact s9 := by
    simpa [s9, afterRegisterWrite_mem] using code8
  have entryFresh : entry.mem.get? 0x4215020 = some (0#8) := by
    have represented := source.2.2.2.2.1.1
    have address : canonicalContractParams.globals.attempted = 0x4215020 := by native_decide
    rw [← address]
    simpa [FlagRep, DecoderGlobalsModel.fresh] using represented
  have fresh9 : s9.mem.get? 0x4215020 = some (0#8) := by
    simpa [s9, s8, s7, afterRegisterWrite_mem] using attempted6.trans entryFresh
  obtain ⟨r10, run10⟩ := wrapper_attempted_load_step (fromStep + 9) args stackBase entry s9
    machine agree9 retired9 code9 pc9 globals9 fresh9
  let s10 := afterRegisterWrite s9 (BitVec.ofNat 64 0x102d4) r10 x11 (0#64)
  have pc10 : s10.regs.get? PC = some (BitVec.ofNat 64 0x102d8) := by
    simpa [s10] using afterRegisterWrite_pc s9 (BitVec.ofNat 64 0x102d4) r10 x11 (0#64)
  have fresh10 : s10.regs.get? x11 = some (0#64) := by
    simp [s10, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have agree10 : Agree platformPreserved entry s10 :=
    agree9.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired10 := afterRegisterWrite_retired_present s9 (BitVec.ofNat 64 0x102d4) r10 x11
    (0#64)
  have code10 : canonicalContractParams.env.CodeIntact s10 := by
    simpa [s10, afterRegisterWrite_mem] using code9
  obtain ⟨r11, run11, pc11⟩ := wrapper_fresh_branch_step (fromStep + 10) args stackBase
    entry s10 machine agree10 retired10 code10 pc10 fresh10
  let final := wrapperAfterFreshBranch s10 r11
  have preserveWrite {before : State} {pc retired : BitVec 64} {destination register : Register}
      {value : RegisterType destination} (different : destination ≠ register) :
      PC ≠ register → nextPC ≠ register → minstret_increment ≠ register → minstret ≠ register →
      (afterRegisterWrite before pc retired destination value).regs.get? register =
        before.regs.get? register := by
    intro notPc notNextPc notIncrement notRetired
    exact afterRegisterWrite_register before pc retired destination register value different
      notPc notNextPc notIncrement notRetired
  have stack7 : s7.regs.get? x2 = some (BitVec.ofNat 64 stackBase) :=
    (preserveWrite (destination := x9) (register := x2) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans stack6
  have stack8 : s8.regs.get? x2 = some (BitVec.ofNat 64 stackBase) :=
    (preserveWrite (destination := x11) (register := x2) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans stack7
  have stack9 : s9.regs.get? x2 = some (BitVec.ofNat 64 stackBase) :=
    (preserveWrite (destination := x18) (register := x2) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans stack8
  have stack10 : s10.regs.get? x2 = some (BitVec.ofNat 64 stackBase) :=
    (preserveWrite (destination := x11) (register := x2) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans stack9
  have finalStack := (wrapperAfterFreshBranch_register s10 r11 x2 (by decide) (by decide)
    (by decide) (by decide)).trans stack10
  have input7 : s7.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) :=
    (preserveWrite (destination := x9) (register := x10) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans input6
  have input8 : s8.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) :=
    (preserveWrite (destination := x11) (register := x10) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans input7
  have input9 : s9.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) :=
    (preserveWrite (destination := x18) (register := x10) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans input8
  have input10 : s10.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) :=
    (preserveWrite (destination := x11) (register := x10) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans input9
  have finalInput := (wrapperAfterFreshBranch_register s10 r11 x10 (by decide) (by decide)
    (by decide) (by decide)).trans input10
  have length7 : s7.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by
    simp [s7, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have length8 : s8.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by
    exact (afterRegisterWrite_register s7 (BitVec.ofNat 64 0x102cc) r8 x11 x9
      (BitVec.ofNat 64 0x42152cc) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans length7
  have length9 : s9.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by
    exact (afterRegisterWrite_register s8 (BitVec.ofNat 64 0x102d0) r9 x18 x9
      (BitVec.ofNat 64 0x4215020) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans length8
  have length10 : s10.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by
    exact (afterRegisterWrite_register s9 (BitVec.ofNat 64 0x102d4) r10 x11 x9 (0#64)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans length9
  have finalLength := (wrapperAfterFreshBranch_register s10 r11 x9 (by decide) (by decide)
    (by decide) (by decide)).trans length10
  have globals10 : s10.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    exact (afterRegisterWrite_register s9 (BitVec.ofNat 64 0x102d4) r10 x11 x18 (0#64)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans globals9
  have finalGlobals := (wrapperAfterFreshBranch_register s10 r11 x18 (by decide) (by decide)
    (by decide) (by decide)).trans globals10
  have finalFresh : final.mem.get? 0x4215020 = some (0#8) := by
    change s9.mem.get? 0x4215020 = some (0#8)
    exact fresh9
  have finalInputMemory : MemoryRepresentation.MemoryBytes final args.inputBase args.bytes := by
    simpa [final, s10, s9, s8, s7, wrapperAfterFreshBranch, wrapperAfterFreshBranch,
      afterRegisterWrite_mem] using inputMemory6
  have finalAgree := agree10.trans (wrapperAfterFreshBranch_platformAgree s10 r11)
  have finalRetired := wrapperAfterFreshBranch_retired s10 r11
  have finalCode : canonicalContractParams.env.CodeIntact final := by
    change canonicalContractParams.env.CodeIntact s10
    exact code10
  have ownStep (stepNo pc : Nat) (before after : State)
      (atPc : before.regs.get? PC = some (BitVec.ofNat 64 pc))
      (inRegion : functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 pc))
      (notExit : ¬ functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw
        (BitVec.ofNat 64 pc))
      (run : Runs (try_step stepNo false) before after false) :
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary stepNo 1 before after := by
    exact ConfinedPrefix.ownStep atPc inRegion notExit run
  have prefix7 := ownStep (fromStep + 6) 0x102c8 s6 s7 pc6 (by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide)
    (by simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s7] using run7)
  have prefix8 := ownStep (fromStep + 7) 0x102cc s7 s8 pc7 (by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide)
    (by simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s8] using run8)
  have prefix9 := ownStep (fromStep + 8) 0x102d0 s8 s9 pc8 (by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide)
    (by simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s9] using run9)
  have prefix10 := ownStep (fromStep + 9) 0x102d4 s9 s10 pc9 (by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide)
    (by simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s10] using run10)
  have prefix11 := ownStep (fromStep + 10) 0x102d8 s10 final pc10
    (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide)
    (by simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw])
    (by simpa [final] using run11)
  have prefix7' := ConfinedPrefix.trans prefix6 (by simpa [Nat.add_assoc] using prefix7)
  have prefix8' := ConfinedPrefix.trans prefix7' (by simpa [Nat.add_assoc] using prefix8)
  have prefix9' := ConfinedPrefix.trans prefix8' (by simpa [Nat.add_assoc] using prefix9)
  have prefix10' := ConfinedPrefix.trans prefix9' (by simpa [Nat.add_assoc] using prefix10)
  have confined : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 11 entry final := by
    simpa [Nat.add_assoc] using ConfinedPrefix.trans prefix10'
      (by simpa [Nat.add_assoc] using prefix11)
  refine ⟨final, ?_, confined, by simpa [final] using pc11, finalStack, finalInput, finalLength,
    finalGlobals, finalFresh, finalInputMemory, finalAgree, finalRetired, finalCode⟩
  have trace7 := Trace.snoc trace6 (by simpa [s7] using run7)
  have trace8 := Trace.snoc trace7 (by simpa [s8] using run8)
  have trace9 := Trace.snoc trace8 (by simpa [s9] using run9)
  have trace10 := Trace.snoc trace9 (by simpa [s10] using run10)
  simpa [final] using Trace.snoc trace10 run11

/-! ## Enter the selected allocator segment -/

theorem wrapper_save_input_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102e8)
      0x13#8 0x04#8 0x05#8 0x00#8 :=
  fetchFileInstruction state 0x102e8 0x13 0x04 0x05 0x00
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_save_input_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x13#8 0x04#8 0x05#8 0x00#8)) state state
      (.ITYPE (0#12, .Regidx 10#5, .Regidx 8#5, .ADDI)) := by
  decode_run

theorem wrapper_save_input_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry state : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree platformPreserved entry state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102e8))
    (input : state.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x102e8) retired x8
        (BitVec.ofNat 64 args.inputBase)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102e8) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetch := wrapper_save_input_fetch state code
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ :=
    wrapper_decode_machine_state entry state machine.machine
      (Agree.weaken (fun _ preserved => preserved.2) agree)
  have decode := wrapper_save_input_decode
    (tryStepControlFlowAfterIncrement state) privilege mseccfgBits mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102e8)
  have inputAtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using input
  have execute : Runs (execute (.ITYPE (0#12, .Regidx 10#5, .Regidx 8#5, .ADDI)))
      executeState
      { executeState with regs := executeState.regs.insert x8 (BitVec.ofNat 64 args.inputBase) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0#12 (.Regidx 10#5) (.Regidx 8#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 0#12 (BitVec.ofNat 64 args.inputBase) =
        BitVec.ofNat 64 args.inputBase := by
      simp [iTypeResult, show sign_extend (0#12) = (0#64) by decide]
    rw [← resultEq]
    exact execute_ITYPE_run executeState _ 0#12 (.Regidx 10#5) (.Regidx 8#5) .ADDI
      (BitVec.ofNat 64 args.inputBase) (rX_x10_run executeState _ inputAtExecute)
      (writeSavedS0 executeState (iTypeResult .ADDI 0#12 (BitVec.ofNat 64 args.inputBase)))
  exact decoderRegisterWriteStep machine.machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x102e8) pcIn atPc 0x13#8 0x04#8 0x05#8 0x00#8
    (.ITYPE (0#12, .Regidx 10#5, .Regidx 8#5, .ADDI)) x8
    (BitVec.ofNat 64 args.inputBase) fetch (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

theorem wrapper_attempted_value_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102ec)
      0x13#8 0x05#8 0x10#8 0x00#8 :=
  fetchFileInstruction state 0x102ec 0x13 0x05 0x10 0x00
    (by simpa [canonicalContractParams, canonicalEnvironment] using code)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_attempted_value_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x10#8 0x00#8)) state state
      (.ITYPE (1#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) := by
  decode_run

theorem wrapper_attempted_value_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry state : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree platformPreserved entry state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102ec)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x102ec) retired x10 (1#64)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102ec) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetch := wrapper_attempted_value_fetch state code
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ :=
    wrapper_decode_machine_state entry state machine.machine
      (Agree.weaken (fun _ preserved => preserved.2) agree)
  have decode := wrapper_attempted_value_decode
    (tryStepControlFlowAfterIncrement state) privilege mseccfgBits mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102ec)
  have execute : Runs (execute (.ITYPE (1#12, .Regidx 0#5, .Regidx 10#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x10 (1#64) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 1#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 1#12 (0#64) = (1#64) := by native_decide
    rw [← resultEq]
    exact execute_ITYPE_run executeState _ 1#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI (0#64)
      (rX_x0_run executeState) (wX_x10_run executeState (iTypeResult .ADDI 1#12 (0#64)))
  exact decoderRegisterWriteStep machine.machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x102ec) pcIn atPc 0x13#8 0x05#8 0x10#8 0x00#8
    (.ITYPE (1#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) x10 (1#64)
    fetch (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Thirteen wrapper-owned Sail steps reach the first selected allocator instruction. The live
registers are exactly the values consumed by that inline segment; no callable ABI is imposed. -/
theorem wrapper_to_allocator_entry_prefix (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    ∃ final, Trace fromStep 13 entry final ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary fromStep 13 entry final ∧
      final.regs.get? PC = some (BitVec.ofNat 64 0x102f0) ∧
      final.regs.get? x2 = some (BitVec.ofNat 64 stackBase) ∧
      final.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      final.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      final.regs.get? x10 = some (1#64) ∧
      final.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      final.mem.get? 0x4215020 = some (0#8) ∧
      MemoryRepresentation.MemoryBytes final args.inputBase args.bytes ∧
      Agree platformPreserved entry final ∧ RetiredCounterPresent final ∧
      canonicalContractParams.env.CodeIntact final := by
  obtain ⟨s11, trace11, prefix11, pc11, stack11, input11, length11, globals11, fresh11,
    inputMemory11, agree11, retired11, code11⟩ :=
    wrapper_fresh_prologue_prefix fromStep args stackBase entry source machine
  obtain ⟨r12, run12⟩ := wrapper_save_input_step (fromStep + 11) args stackBase entry s11
    machine agree11 retired11 code11 pc11 input11
  let s12 := afterRegisterWrite s11 (BitVec.ofNat 64 0x102e8) r12 x8
    (BitVec.ofNat 64 args.inputBase)
  have pc12 : s12.regs.get? PC = some (BitVec.ofNat 64 0x102ec) := by
    simpa [s12] using afterRegisterWrite_pc s11 (BitVec.ofNat 64 0x102e8) r12 x8
      (BitVec.ofNat 64 args.inputBase)
  have agree12 : Agree platformPreserved entry s12 :=
    agree11.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired12 := afterRegisterWrite_retired_present s11 (BitVec.ofNat 64 0x102e8) r12 x8
    (BitVec.ofNat 64 args.inputBase)
  have code12 : canonicalContractParams.env.CodeIntact s12 := by
    simpa [s12, afterRegisterWrite_mem] using code11
  obtain ⟨r13, run13⟩ := wrapper_attempted_value_step (fromStep + 12) args stackBase entry s12
    machine agree12 retired12 code12 pc12
  let final := afterRegisterWrite s12 (BitVec.ofNat 64 0x102ec) r13 x10 (1#64)
  have savedInput12 : s12.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [s12, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have keep {register : Register} {value : RegisterType register}
      (different : x10 ≠ register) (notPc : PC ≠ register)
      (notNextPc : nextPC ≠ register) (notIncrement : minstret_increment ≠ register)
      (notRetired : minstret ≠ register) (read : s12.regs.get? register = some value) :
      final.regs.get? register = some value := by
    exact (afterRegisterWrite_register s12 (BitVec.ofNat 64 0x102ec) r13 x10 register (1#64)
      different notPc notNextPc notIncrement notRetired).trans read
  have stack12 : s12.regs.get? x2 = some (BitVec.ofNat 64 stackBase) :=
    (afterRegisterWrite_register s11 (BitVec.ofNat 64 0x102e8) r12 x8 x2
      (BitVec.ofNat 64 args.inputBase) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans stack11
  have length12 : s12.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) :=
    (afterRegisterWrite_register s11 (BitVec.ofNat 64 0x102e8) r12 x8 x9
      (BitVec.ofNat 64 args.inputBase) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans length11
  have globals12 : s12.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (afterRegisterWrite_register s11 (BitVec.ofNat 64 0x102e8) r12 x8 x18
      (BitVec.ofNat 64 args.inputBase) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans globals11
  have finalPc : final.regs.get? PC = some (BitVec.ofNat 64 0x102f0) := by
    simpa [final] using afterRegisterWrite_pc s12 (BitVec.ofNat 64 0x102ec) r13 x10 (1#64)
  have finalValue : final.regs.get? x10 = some (1#64) := by
    simp [final, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have finalFresh : final.mem.get? 0x4215020 = some (0#8) := by
    simpa [final, s12, afterRegisterWrite_mem] using fresh11
  have finalInputMemory : MemoryRepresentation.MemoryBytes final args.inputBase args.bytes := by
    simpa [final, s12, afterRegisterWrite_mem] using inputMemory11
  have finalAgree : Agree platformPreserved entry final :=
    agree12.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  have finalRetired := afterRegisterWrite_retired_present s12 (BitVec.ofNat 64 0x102ec) r13 x10
    (1#64)
  have finalCode : canonicalContractParams.env.CodeIntact final := by
    simpa [final, afterRegisterWrite_mem] using code12
  have prefix12 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + 11) 1 s11 s12 := by
    apply ConfinedPrefix.ownStep pc11
    · apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide
    · simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]
    · simpa [s12] using run12
  have prefix13 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + 12) 1 s12 final := by
    apply ConfinedPrefix.ownStep pc12
    · apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide
    · simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]
    · simpa [final] using run13
  have prefix12' := ConfinedPrefix.trans prefix11 (by simpa [Nat.add_assoc] using prefix12)
  have confined : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 13 entry final := by
    simpa [Nat.add_assoc] using ConfinedPrefix.trans prefix12'
      (by simpa [Nat.add_assoc] using prefix13)
  refine ⟨final, ?_, confined, finalPc,
    keep (by decide) (by decide) (by decide) (by decide) (by decide)
    stack12, keep (by decide) (by decide) (by decide) (by decide) (by decide) savedInput12,
    keep (by decide) (by decide) (by decide) (by decide) (by decide) length12, finalValue,
    keep (by decide) (by decide) (by decide) (by decide) (by decide) globals12, finalFresh,
    finalInputMemory, finalAgree, finalRetired, finalCode⟩
  have trace12 := Trace.snoc trace11 (by simpa [s12] using run12)
  simpa [final] using Trace.snoc trace12 run13

/-- The configured decoder machine supplies exactly the ordinary-step premises needed at a wrapper
or inline instruction. In particular, this adapter does not manufacture a return-sentinel fact. -/
theorem decoderInstructionStepPlatform {instructionPcs : BitVec 64 → Prop}
    {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre instructionPcs machineArgs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (pc : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (pcIn : instructionPcs (BitVec.ofNat 64 pc)) : InstructionStepPlatform state pc := by
  have current := machine.mono agree retired
  obtain ⟨fetch, noMMIO, interrupts, notExpected⟩ :=
    current.platform state (BitVec.ofNat 64 pc) (Agree.refl state) atPc pcIn
  obtain ⟨seccfgBits, seccfgRead, -⟩ := current.mseccfg
  exact
    { normal := current.normal
      fetch := fetch
      fetchNoMMIO := noMMIO
      interrupts := interrupts
      notExpected := notExpected
      seccfgRead := ⟨seccfgBits, seccfgRead⟩
      retired := retired
      code := by simpa [canonicalContractParams, canonicalEnvironment] using code }

/-- The wrapper's concrete thirteen-step prefix supplies the real entry state for the allocator's
first selected segment, then consumes that segment through its Level 2 contract. -/
theorem wrapper_reaches_allocator_first_segment
    (allocator : AllocatorInlineContract) (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    ∃ atAllocator retired,
      Trace fromStep 13 entry atAllocator ∧
      Nonempty (AllocatorInlineTransfer (fromStep + 13) 0 atAllocator
        (allocatorAfterDataPointer atAllocator retired (BitVec.ofNat 64 0x4215020))) := by
  obtain ⟨atAllocator, trace, -, pc, -, -, -, -, globals, -, -, agree, retired, code⟩ :=
    wrapper_to_allocator_entry_prefix fromStep args stackBase entry source machine
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102f0) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have platform := decoderInstructionStepPlatform machine.machine
    (Agree.weaken (fun _ preserved => preserved.2) agree) retired code 0x102f0 pc pcIn
  obtain ⟨nextRetired, transfer⟩ := allocator.1 (fromStep + 13) atAllocator
    (BitVec.ofNat 64 0x4215020) ⟨platform, pc, globals⟩
  exact ⟨atAllocator, nextRetired, trace, transfer⟩

/-- The first allocator segment and the wrapper-owned tag store are now part of one concrete trace.
The only condition consumed here is the selected allocator contract itself. -/
theorem wrapper_through_allocator_tag
    (allocator : AllocatorInlineContract) (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    ∃ final, Trace fromStep 15 entry final ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary fromStep 15 entry final ∧
      final.regs.get? PC = some (BitVec.ofNat 64 0x102f8) ∧
      final.regs.get? x2 = some (BitVec.ofNat 64 stackBase) ∧
      final.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      final.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      final.regs.get? x11 = some (BitVec.ofNat 64 0x4215021) ∧
      MemoryRepresentation.MemoryBytes final args.inputBase args.bytes ∧
      Agree decoderPreserved entry final ∧ RetiredCounterPresent final ∧
      canonicalContractParams.env.CodeIntact final := by
  obtain ⟨atAllocator, trace13, prefix13, pc13, stack13, savedInput13, length13, data13,
    globals13, -, inputMemory13, agree13, retired13, code13⟩ :=
    wrapper_to_allocator_entry_prefix fromStep args stackBase entry source machine
  have pc13In : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102f0) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have platform13 := decoderInstructionStepPlatform machine.machine
    (Agree.weaken (fun _ preserved => preserved.2) agree13) retired13 code13 0x102f0 pc13 pc13In
  obtain ⟨r14, firstTransfer⟩ := allocator.1 (fromStep + 13) atAllocator
    (BitVec.ofNat 64 0x4215020) ⟨platform13, pc13, globals13⟩
  rcases firstTransfer with ⟨firstTransfer⟩
  let afterFirst := allocatorAfterDataPointer atAllocator r14 (BitVec.ofNat 64 0x4215020)
  have firstStep : Runs (try_step (fromStep + 13) false) atAllocator afterFirst false := by
    exact allocator_data_pointer_step_of_inlineTransfer (fromStep + 13) atAllocator afterFirst
      firstTransfer
  have firstPc : afterFirst.regs.get? PC = some (BitVec.ofNat 64 0x102f4) := by
    simpa [afterFirst, allocatorAfterDataPointer] using
      afterRegisterWrite_pc atAllocator (BitVec.ofNat 64 0x102f0) r14 x11
        (Sail.BitVec.addInt (BitVec.ofNat 64 0x4215020) 1)
  have firstAgreePlatform : Agree platformPreserved atAllocator afterFirst := by
    exact afterRegisterWrite_agree (by simp [platformPreserved])
  have firstAgree : Agree decoderPreserved entry afterFirst :=
    (Agree.weaken (fun _ preserved => preserved.2) agree13).trans
      (Agree.weaken (fun _ preserved => preserved.2) firstAgreePlatform)
  have firstRetired : RetiredCounterPresent afterFirst := by
    exact afterRegisterWrite_retired_present atAllocator (BitVec.ofNat 64 0x102f0) r14 x11
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x4215020) 1)
  have firstCode : canonicalContractParams.env.CodeIntact afterFirst := by
    simpa [afterFirst, allocatorAfterDataPointer, afterRegisterWrite_mem] using code13
  have firstStack : afterFirst.regs.get? x2 = some (BitVec.ofNat 64 stackBase) :=
    (afterRegisterWrite_register atAllocator (BitVec.ofNat 64 0x102f0) r14 x11 x2
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x4215020) 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans stack13
  have firstTarget : afterFirst.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
    (afterRegisterWrite_register atAllocator (BitVec.ofNat 64 0x102f0) r14 x11 x18
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x4215020) 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans globals13
  have firstSavedInput : afterFirst.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) :=
    (afterRegisterWrite_register atAllocator (BitVec.ofNat 64 0x102f0) r14 x11 x8
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x4215020) 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans savedInput13
  have firstLength : afterFirst.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) :=
    (afterRegisterWrite_register atAllocator (BitVec.ofNat 64 0x102f0) r14 x11 x9
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x4215020) 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans length13
  have firstData : afterFirst.regs.get? x10 = some (1#64) :=
    (afterRegisterWrite_register atAllocator (BitVec.ofNat 64 0x102f0) r14 x11 x10
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x4215020) 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans data13
  have writable : DecoderAccessRange DecoderWritableByte (BitVec.ofNat 64 0x4215020) 1 := by
    refine ⟨by decide, ?_, ?_⟩
    · simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]
    · intro index bound
      have indexZero : index = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)
      subst index
      right
      left
      unfold DecoderGlobalsByte
      constructor <;> native_decide
  have pc14In : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102f4) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  obtain ⟨r15, tagStep⟩ := wrapper_allocator_tag_step_configured machine.machine firstAgree
    firstRetired firstCode (fromStep + 14) pc14In firstPc (BitVec.ofNat 64 0x4215020)
    (1#64) firstTarget firstData writable
  let final := wrapperAfterAllocatorTag afterFirst r15 (BitVec.ofNat 64 0x4215020) (1#64)
  have finalStack := (wrapperAfterAllocatorTag_register afterFirst r15
    (BitVec.ofNat 64 0x4215020) (1#64) x2 (by decide) (by decide) (by decide)
    (by decide)).trans firstStack
  have finalSavedInput := (wrapperAfterAllocatorTag_register afterFirst r15
    (BitVec.ofNat 64 0x4215020) (1#64) x8 (by decide) (by decide) (by decide)
    (by decide)).trans firstSavedInput
  have finalLength := (wrapperAfterAllocatorTag_register afterFirst r15
    (BitVec.ofNat 64 0x4215020) (1#64) x9 (by decide) (by decide) (by decide)
    (by decide)).trans firstLength
  have firstContext : afterFirst.regs.get? x11 = some (BitVec.ofNat 64 0x4215021) := by
    have valueEq : Sail.BitVec.addInt (BitVec.ofNat 64 0x4215020) 1 =
        BitVec.ofNat 64 0x4215021 := by native_decide
    simp [afterFirst, allocatorAfterDataPointer, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, valueEq]
  have finalContext := (wrapperAfterAllocatorTag_register afterFirst r15
    (BitVec.ofNat 64 0x4215020) (1#64) x11 (by decide) (by decide) (by decide)
    (by decide)).trans firstContext
  have firstInputMemory : MemoryRepresentation.MemoryBytes afterFirst args.inputBase args.bytes := by
    simpa [afterFirst, allocatorAfterDataPointer, afterRegisterWrite_mem] using inputMemory13
  have finalInputMemory : MemoryRepresentation.MemoryBytes final args.inputBase args.bytes := by
    apply firstInputMemory.of_mem_eq
    intro inputIndex inputBound
    have different : 0x4215020 ≠ args.inputBase + inputIndex := by
      rcases machine.inputAvoidsAttempted with inputBefore | attemptedBefore
      · omega
      · omega
    change (afterFirst.mem.insert 0x4215020
        (Sail.BitVec.extractLsb (1#64) 7 0)).get? (args.inputBase + inputIndex) =
      afterFirst.mem.get? (args.inputBase + inputIndex)
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg different]
  have finalAgree := firstAgree.trans
    (wrapperAfterAllocatorTag_agree afterFirst r15 (BitVec.ofNat 64 0x4215020) (1#64))
  have finalRetired := wrapperAfterAllocatorTag_retired afterFirst r15
    (BitVec.ofNat 64 0x4215020) (1#64)
  have targetNotFile : Artifacts.programImage.readFileByte? 0x4215020 = none := by native_decide
  have finalCode : canonicalContractParams.env.CodeIntact final := by
    have code := wrapperAfterAllocatorTag_code afterFirst r15 (BitVec.ofNat 64 0x4215020)
      (1#64) targetNotFile
      (by simpa [canonicalContractParams, canonicalEnvironment] using firstCode)
    simpa [canonicalContractParams, canonicalEnvironment, final] using code
  have finalPc : final.regs.get? PC = some (BitVec.ofNat 64 0x102f8) := by
    simpa [final] using wrapperAfterAllocatorTag_pc afterFirst r15
      (BitVec.ofNat 64 0x4215020) (1#64)
  have firstLevel2 := firstTransfer.mapSummary
    (fun child stepNo used before after run => allocatorChildSummary_to_level2 run)
  have firstPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + 13) 1 atAllocator afterFirst := by
    intro count tail rest
    simpa [Nat.add_assoc] using ScopedTrace.inlineStep (fromStep + 13) 0 count
      allocatorInlineBoundary generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
      atAllocator afterFirst tail firstLevel2 (by simpa [Nat.add_assoc] using rest)
  have tagPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + 14) 1 afterFirst final := by
    apply ConfinedPrefix.ownStep firstPc
    · apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide
    · simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]
    · simpa [final] using tagStep
  have prefix14 := ConfinedPrefix.trans prefix13 (by simpa [Nat.add_assoc] using firstPrefix)
  have confined : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 15 entry final := by
    simpa [Nat.add_assoc] using ConfinedPrefix.trans prefix14
      (by simpa [Nat.add_assoc] using tagPrefix)
  refine ⟨final, ?_, confined, finalPc, finalStack, finalSavedInput, finalLength, finalContext,
    finalInputMemory, finalAgree, finalRetired, finalCode⟩
  have trace14 := Trace.snoc trace13 firstStep
  simpa [final, Nat.add_assoc] using Trace.snoc trace14 tagStep

private theorem wrapperAllocatorStackAccess (args : ZesuDecodeRawArgs) (stackBase offset : Nat)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) (offsetEnd : offset + 8 ≤ 0xa20)
    (offsetAligned : offset % 8 = 0) :
    DecoderAccessRange DecoderWritableByte
        (BitVec.ofNat 64 stackBase + BitVec.ofNat 64 offset) 8 ∧
      is_aligned_vaddr
        (virtaddr.Virtaddr (BitVec.ofNat 64 stackBase + BitVec.ofNat 64 offset)) 8 = true ∧
      (∀ index : Fin 8, Artifacts.programImage.readFileByte?
        ((BitVec.ofNat 64 stackBase + BitVec.ofNat 64 offset).toNat + index.val) = none) := by
  have wordSize : 2 ^ 64 = 18446744073709551616 := by native_decide
  have frameFits := machine.stackFrameFits
  rw [wordSize] at frameFits
  have targetToNat :
      (BitVec.ofNat 64 stackBase + BitVec.ofNat 64 offset).toNat = stackBase + offset := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have allowed : DecoderAccessRange DecoderWritableByte
      (BitVec.ofNat 64 stackBase + BitVec.ofNat 64 offset) 8 := by
    rw [DecoderAccessRange, targetToNat]
    refine ⟨by decide, ?_, ?_⟩
    · omega
    intro index bound
    exact Or.inl (by simpa [Nat.add_assoc] using
      machine.stackFrameWritable (offset + index) (by omega))
  have aligned : is_aligned_vaddr
      (virtaddr.Virtaddr (BitVec.ofNat 64 stackBase + BitVec.ofNat 64 offset)) 8 = true := by
    simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, targetToNat]
    have targetAligned : (stackBase + offset) % 8 = 0 := by
      have stackAligned := machine.stackAligned
      omega
    simp [Int.tmod, targetAligned]
  have notFile : ∀ index : Fin 8, Artifacts.programImage.readFileByte?
      ((BitVec.ofNat 64 stackBase + BitVec.ofNat 64 offset).toNat + index.val) = none := by
    intro index
    apply canonicalStack_not_fileByte
    rw [targetToNat]
    simpa [Nat.add_assoc] using
      machine.stackFrameWritable (offset + index.val) (by omega)
  exact ⟨allowed, aligned, notFile⟩

private theorem wrapper_second_allocator_inputMemory
    (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry atSecond : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (inputMemory : MemoryRepresentation.MemoryBytes atSecond args.inputBase args.bytes)
    (pageRetired addressRetired contextRetired functionRetired : BitVec 64) :
    MemoryRepresentation.MemoryBytes
      (allocatorAfterFunctionStore
        (allocatorAfterContextStore
          (allocatorAfterFunctionAddress
            (allocatorAfterFunctionPage atSecond pageRetired) addressRetired)
          contextRetired (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x4215021))
        functionRetired (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x13f70))
      args.inputBase args.bytes := by
  let afterPage := allocatorAfterFunctionPage atSecond pageRetired
  let afterAddress := allocatorAfterFunctionAddress afterPage addressRetired
  let afterContext := allocatorAfterContextStore afterAddress contextRetired
    (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x4215021)
  let final := allocatorAfterFunctionStore afterContext functionRetired
    (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x13f70)
  have pageInput : MemoryRepresentation.MemoryBytes afterPage args.inputBase args.bytes := by
    simpa [afterPage, allocatorAfterFunctionPage, afterRegisterWrite_mem] using inputMemory
  have addressInput : MemoryRepresentation.MemoryBytes afterAddress args.inputBase args.bytes := by
    simpa [afterAddress, allocatorAfterFunctionAddress, afterRegisterWrite_mem] using pageInput
  have contextInput : MemoryRepresentation.MemoryBytes afterContext args.inputBase args.bytes := by
    apply addressInput.of_mem_eq
    intro inputIndex inputBound
    have outside : ∀ storeIndex : Fin 8,
        stackBase + 0x10 + storeIndex.val ≠ args.inputBase + inputIndex := by
      intro storeIndex equal
      rcases machine.inputAvoidsStack with inputBefore | stackBeforeInput <;> omega
    have preserved := afterWriteBytes_mem_get?_of_outside
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement afterAddress)
        (BitVec.ofNat 64 0x10300))
      (stackBase + 0x10) (BitVec.ofNat 64 0x4215021)
      (args.inputBase + inputIndex) outside
    simpa [afterContext, allocatorAfterContextStore, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      show (BitVec.ofNat 64 stackBase + sign_extend (0x010#12)).toNat = stackBase + 0x10 by
        rw [show sign_extend (m := 64) (0x010#12) = BitVec.ofNat 64 0x10 by decide,
          ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        have frameFits := machine.stackFrameFits
        omega] using preserved
  apply contextInput.of_mem_eq
  intro inputIndex inputBound
  have outside : ∀ storeIndex : Fin 8,
      stackBase + 0x18 + storeIndex.val ≠ args.inputBase + inputIndex := by
    intro storeIndex equal
    rcases machine.inputAvoidsStack with inputBefore | stackBeforeInput <;> omega
  have preserved := afterWriteBytes_mem_get?_of_outside
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement afterContext)
      (BitVec.ofNat 64 0x10304))
    (stackBase + 0x18) (BitVec.ofNat 64 0x13f70)
    (args.inputBase + inputIndex) outside
  simpa [final, afterContext, afterAddress, afterPage, allocatorAfterFunctionStore,
    tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
    tryStepControlFlowAfterIncrement,
    show (BitVec.ofNat 64 stackBase + sign_extend (0x018#12)).toNat = stackBase + 0x18 by
      rw [show sign_extend (m := 64) (0x018#12) = BitVec.ofNat 64 0x18 by decide,
        ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have frameFits := machine.stackFrameFits
      omega] using preserved

private theorem wrapper_second_allocator_contextCode
    (stackBase : Nat) (atSecond : State) (pageRetired addressRetired contextRetired : BitVec 64)
    (contextNotFile : ∀ index : Fin 8, Artifacts.programImage.readFileByte?
      ((BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x10).toNat + index.val) = none)
    (code : Artifacts.programImage.fileBytesMatchMemory atSecond.mem) :
    Artifacts.programImage.fileBytesMatchMemory
      (allocatorAfterContextStore
        (allocatorAfterFunctionAddress
          (allocatorAfterFunctionPage atSecond pageRetired) addressRetired)
        contextRetired (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x4215021)).mem := by
  let afterPage := allocatorAfterFunctionPage atSecond pageRetired
  let afterAddress := allocatorAfterFunctionAddress afterPage addressRetired
  exact allocatorAfterContextStore_code afterAddress contextRetired
    (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x4215021) contextNotFile
    (by simpa [afterAddress, afterPage, allocatorAfterFunctionAddress,
      allocatorAfterFunctionPage, afterRegisterWrite_mem] using code)

private theorem wrapper_second_allocator_code
    (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry atSecond : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (pageRetired addressRetired contextRetired functionRetired : BitVec 64)
    (contextNotFile : ∀ index : Fin 8, Artifacts.programImage.readFileByte?
      ((BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x10).toNat + index.val) = none)
    (functionNotFile : ∀ index : Fin 8, Artifacts.programImage.readFileByte?
      ((BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x18).toNat + index.val) = none)
    (code : Artifacts.programImage.fileBytesMatchMemory atSecond.mem) :
    canonicalContractParams.env.CodeIntact
      (allocatorAfterFunctionStore
        (allocatorAfterContextStore
          (allocatorAfterFunctionAddress
            (allocatorAfterFunctionPage atSecond pageRetired) addressRetired)
          contextRetired (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x4215021))
        functionRetired (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x13f70)) := by
  let afterPage := allocatorAfterFunctionPage atSecond pageRetired
  let afterAddress := allocatorAfterFunctionAddress afterPage addressRetired
  let afterContext := allocatorAfterContextStore afterAddress contextRetired
    (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x4215021)
  let final := allocatorAfterFunctionStore afterContext functionRetired
    (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x13f70)
  have contextCode := wrapper_second_allocator_contextCode stackBase atSecond pageRetired
    addressRetired contextRetired contextNotFile code
  have finalFileCode := allocatorAfterFunctionStore_code afterContext functionRetired
    (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x13f70)
    (by simpa using functionNotFile)
    (by simpa [afterContext, afterAddress, afterPage] using contextCode)
  simpa [canonicalContractParams, canonicalEnvironment, final] using finalFileCode

private structure WrapperSecondAllocatorPost (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry atSecond : State) where
  final : State
  transfer : AllocatorInlineTransfer (fromStep + 15) 3 atSecond final
  pc : final.regs.get? PC = some (BitVec.ofNat 64 0x10308)
  stack : final.regs.get? x2 = some (BitVec.ofNat 64 stackBase)
  savedInput : final.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase)
  length : final.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size)
  inputMemory : MemoryRepresentation.MemoryBytes final args.inputBase args.bytes
  agree : Agree decoderPreserved entry final
  retired : RetiredCounterPresent final
  code : canonicalContractParams.env.CodeIntact final

/-- Semantic handoff for the allocator's second inline segment. Keeping its state transport
separate from the enclosing trace splice bounds elaboration cost for the wrapper capstone. -/
private theorem wrapper_second_allocator_semantics
    (allocator : AllocatorInlineContract) (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry atSecond : State)
    (pc15 : atSecond.regs.get? PC = some (BitVec.ofNat 64 0x102f8))
    (stack15 : atSecond.regs.get? x2 = some (BitVec.ofNat 64 stackBase))
    (savedInput15 : atSecond.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase))
    (length15 : atSecond.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size))
    (context15 : atSecond.regs.get? x11 = some (BitVec.ofNat 64 0x4215021))
    (inputMemory15 : MemoryRepresentation.MemoryBytes atSecond args.inputBase args.bytes)
    (agree15 : Agree decoderPreserved entry atSecond)
    (retired15 : RetiredCounterPresent atSecond)
    (code15 : canonicalContractParams.env.CodeIntact atSecond)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    Nonempty (WrapperSecondAllocatorPost fromStep args stackBase entry atSecond) := by
  have contextTarget : BitVec.ofNat 64 stackBase + sign_extend (0x010#12) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x10 := by
    rw [show sign_extend (m := 64) (0x010#12) = BitVec.ofNat 64 0x10 by decide]
  have functionTarget : BitVec.ofNat 64 stackBase + sign_extend (0x018#12) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x18 := by
    rw [show sign_extend (m := 64) (0x018#12) = BitVec.ofNat 64 0x18 by decide]
  obtain ⟨contextWritable, contextAligned, contextNotFile⟩ :=
    wrapperAllocatorStackAccess args stackBase 0x10 machine (by decide) (by decide)
  obtain ⟨functionWritable, functionAligned, functionNotFile⟩ :=
    wrapperAllocatorStackAccess args stackBase 0x18 machine (by decide) (by decide)
  have code : Artifacts.programImage.fileBytesMatchMemory atSecond.mem := by
    simpa [canonicalContractParams, canonicalEnvironment] using code15
  let secondPre : AllocatorSecondSegmentPreconditions atSecond
      (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x4215021) :=
    { atEntry := pc15
      machineArgs := zesuDecodeRawMachineArgs args
      machine := machine.machine.mono agree15 retired15
      code := code
      stackValue := stack15
      contextValue := context15
      contextWritable := by simpa [contextTarget] using contextWritable
      functionWritable := by simpa [functionTarget] using functionWritable
      contextAligned := by simpa [contextTarget] using contextAligned
      functionAligned := by simpa [functionTarget] using functionAligned
      contextStoreNotFileBacked := by simpa [contextTarget] using contextNotFile
      functionStoreNotFileBacked := by simpa [functionTarget] using functionNotFile }
  obtain ⟨pageRetired, addressRetired, contextRetired, functionRetired, transfer⟩ :=
    allocator.2 (fromStep + 15) atSecond (BitVec.ofNat 64 stackBase)
      (BitVec.ofNat 64 0x4215021) secondPre
  rcases transfer with ⟨transfer⟩
  let final := allocatorAfterFunctionStore
    (allocatorAfterContextStore
      (allocatorAfterFunctionAddress
        (allocatorAfterFunctionPage atSecond pageRetired) addressRetired)
      contextRetired (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x4215021))
    functionRetired (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x13f70)
  let afterPage := allocatorAfterFunctionPage atSecond pageRetired
  let afterAddress := allocatorAfterFunctionAddress afterPage addressRetired
  let afterContext := allocatorAfterContextStore afterAddress contextRetired
    (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x4215021)
  have finalInputMemory : MemoryRepresentation.MemoryBytes final args.inputBase args.bytes := by
    simpa [final, afterContext, afterAddress, afterPage] using
      wrapper_second_allocator_inputMemory args stackBase entry atSecond machine inputMemory15
        pageRetired addressRetired contextRetired functionRetired
  have pageAgree : Agree platformPreserved atSecond afterPage :=
    afterRegisterWrite_agree (by simp [platformPreserved])
  have addressAgree : Agree platformPreserved afterPage afterAddress :=
    afterRegisterWrite_agree (by simp [platformPreserved])
  have contextAgree : Agree platformPreserved afterAddress afterContext :=
    allocatorAfterContextStore_agree afterAddress contextRetired
      (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x4215021)
  have functionAgree : Agree platformPreserved afterContext final :=
    allocatorAfterFunctionStore_agree afterContext functionRetired
      (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x13f70)
  have segmentAgree : Agree decoderPreserved atSecond final :=
    Agree.weaken (fun _ preserved => preserved.2)
      (((pageAgree.trans addressAgree).trans contextAgree).trans functionAgree)
  have finalAgree : Agree decoderPreserved entry final := agree15.trans segmentAgree
  have finalRetired : RetiredCounterPresent final := by
    refine ⟨Sail.BitVec.addInt functionRetired 1, ?_⟩
    simp [final, allocatorAfterFunctionStore, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]
  have segmentRegister (register : Register) (notX10 : x10 ≠ register)
      (notPc : register ≠ PC) (notNextPc : register ≠ nextPC)
      (notIncrement : register ≠ minstret_increment) (notRetired : register ≠ minstret) :
      final.regs.get? register = atSecond.regs.get? register := by
    have functionPreserved := allocatorAfterFunctionStore_get?_of_ne afterContext functionRetired
      (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x13f70) register notPc notNextPc
      notIncrement notRetired
    have contextPreserved := allocatorAfterContextStore_get?_of_ne afterAddress contextRetired
      (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x4215021) register notPc notNextPc
      notIncrement notRetired
    have addressPreserved := afterRegisterWrite_register afterPage
      (BitVec.ofNat 64 0x102fc) addressRetired x10
      register (BitVec.ofNat 64 0x13f70) notX10 (Ne.symm notPc) (Ne.symm notNextPc)
      (Ne.symm notIncrement) (Ne.symm notRetired)
    have pagePreserved := afterRegisterWrite_register atSecond
      (BitVec.ofNat 64 0x102f8) pageRetired x10 register
      (BitVec.ofNat 64 0x142f8) notX10 (Ne.symm notPc) (Ne.symm notNextPc)
      (Ne.symm notIncrement) (Ne.symm notRetired)
    exact ((functionPreserved.trans contextPreserved).trans addressPreserved).trans pagePreserved
  have finalStack : final.regs.get? x2 = some (BitVec.ofNat 64 stackBase) :=
    (segmentRegister x2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans stack15
  have finalSavedInput : final.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) :=
    (segmentRegister x8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      savedInput15
  have finalLength : final.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) :=
    (segmentRegister x9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans length15
  have finalCode : canonicalContractParams.env.CodeIntact final := by
    simpa [final, afterContext, afterAddress, afterPage] using
      wrapper_second_allocator_code args stackBase entry atSecond machine pageRetired
        addressRetired contextRetired functionRetired contextNotFile functionNotFile code
  refine ⟨
    { final := final
      transfer := transfer
      pc := ?_
      stack := finalStack
      savedInput := finalSavedInput
      length := finalLength
      inputMemory := finalInputMemory
      agree := finalAgree
      retired := finalRetired
      code := finalCode }⟩
  simpa [final] using allocatorAfterFunctionStore_pc _ functionRetired
    (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x13f70)

/-- Nineteen concrete steps now cover the wrapper prologue, both allocator segments, and the
wrapper-owned tag store, ending at the selected `decode` entry. -/
theorem wrapper_through_allocator_setup
    (allocator : AllocatorInlineContract) (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    ∃ final, Trace fromStep 19 entry final ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary fromStep 19 entry final ∧
      final.regs.get? PC = some (BitVec.ofNat 64 0x10308) ∧
      final.regs.get? x2 = some (BitVec.ofNat 64 stackBase) ∧
      final.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      final.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      MemoryRepresentation.MemoryBytes final args.inputBase args.bytes ∧
      Agree decoderPreserved entry final ∧ RetiredCounterPresent final ∧
      canonicalContractParams.env.CodeIntact final := by
  obtain ⟨atSecond, trace15, prefix15, pc15, stack15, savedInput15, length15, context15,
    inputMemory15, agree15, retired15, code15⟩ :=
    wrapper_through_allocator_tag allocator fromStep args stackBase entry source machine
  obtain ⟨post⟩ :=
    wrapper_second_allocator_semantics allocator fromStep args stackBase entry atSecond pc15
      stack15 savedInput15 length15 context15 inputMemory15 agree15 retired15 code15 machine
  let final := post.final
  have transfer := post.transfer
  have trace4 := allocator_second_trace_of_inlineTransfer (fromStep + 15) atSecond final transfer
  have complete := Trace.append trace15 (by simpa [Nat.add_assoc] using trace4)
  have secondLevel2 := transfer.mapSummary
    (fun child stepNo used before after run => allocatorChildSummary_to_level2 run)
  have secondPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + 15) 4 atSecond final := by
    intro count tail rest
    simpa [Nat.add_assoc] using ScopedTrace.inlineStep (fromStep + 15) 3 count
      allocatorInlineBoundary generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
      atSecond final tail secondLevel2 (by simpa [Nat.add_assoc] using rest)
  have confined : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 19 entry final := by
    simpa [Nat.add_assoc] using ConfinedPrefix.trans prefix15
      (by simpa [Nat.add_assoc] using secondPrefix)
  exact ⟨final, by simpa [Nat.add_assoc] using complete, confined, post.pc, post.stack,
    post.savedInput, post.length, post.inputMemory, post.agree, post.retired, post.code⟩

/-- The selected inlined `decode` region is contained in its enclosing wrapper's generated
execution region. This is checked from the generated call relation, not handwritten address bounds. -/
private theorem decodeInline_executionPcs_subset_wrapper (pc : BitVec 64)
    (inside : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 pc) :
    functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw pc := by
  have parentMember : functionInstance_raw_decoder_root_zesu_decode_raw ∈
      generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨1, by native_decide, rfl⟩
  have childMember :
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
        generatedProgram.functionInstances := by
    apply Array.mem_iff_getElem.mpr
    exact ⟨3, by native_decide, rfl⟩
  have childIsCallee :
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
        BinaryFv.RiscV.Elfling.calleeFunctionInstances generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw := by
    apply Array.mem_filter.mpr
    exact ⟨childMember, by native_decide⟩
  exact BinaryFv.Zesu.Elflings.Validation.generated_program_geometry.calleeWithinExecution
    functionInstance_raw_decoder_root_zesu_decode_raw parentMember
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 childIsCallee
    pc inside

/-- The nineteen-step wrapper prefix establishes the complete first-phase `decode` entry and then
visibly consumes the Level 3 conditional theorem. It retains that theorem's bound, scoped trace,
and semantic postcondition alongside the Level 2 child summary, so the wrapper proof can dispatch
the actual result without recovering facts from an opaque existential. -/
theorem wrapper_reaches_decode_first_contract
    (allocator : AllocatorInlineContract) (decodeRaw : CompiledDecodeRawInstanceContract)
    (fromStep : Nat) (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    ∃ atDecode, Trace fromStep 19 entry atDecode ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary fromStep 19 entry atDecode ∧
      ∃ decodeArgs : DecodeInlineArgs,
        DecodeInlinePre decodeArgs atDecode ∧
          ∃ used after,
            Level2ChildSummary
              functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
              (fromStep + 19) used atDecode after ∧
            used ≤ decodeInlineStepBound decodeArgs ∧
            ScopedTrace
              (functionInstanceExecutionPcs generatedProgram
                functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
              (DecodeInlineExit decodeArgs) Level3ChildSummary
              (fromStep + 19) used atDecode after ∧
            DecodeInlinePost decodeArgs atDecode after ∧
            DecodeInlineMachinePost atDecode after := by
  obtain ⟨atDecode, trace, confined, pc, stack, savedInput, length, inputMemory, agree, retired,
    code⟩ :=
    wrapper_through_allocator_setup allocator fromStep args stackBase entry source machine
  let decodeArgs : DecodeInlineArgs :=
    { phase := .first
      stackBase := stackBase
      inputBase := args.inputBase
      bytes := args.bytes }
  have parentMachine := machine.machine.mono agree retired
  have decodeMachine : DecodeInlineMachinePre decodeArgs atDecode := by
    simpa [DecodeInlineArgs.machineArgs, decodeArgs, zesuDecodeRawMachineArgs] using
      parentMachine.restrict decodeInline_executionPcs_subset_wrapper
  let pre : DecodeInlinePre decodeArgs atDecode :=
    { atEntry := by simpa [decodeArgs, DecodeInlineArgs.entryPc] using pc
      stackValue := by simpa [decodeArgs] using stack
      inputValue := by simpa [decodeArgs] using savedInput
      lengthValue := by simpa [decodeArgs] using length
      inputMemory := by simpa [decodeArgs] using inputMemory
      code := code
      inputFits := machine.inputFits
      rootInputBound := machine.inputBound
      stackAligned := machine.stackAligned
      stackObjectsFit := machine.stackObjectsFit
      stackObjectsReadable := machine.stackObjectsReadable
      machine := decodeMachine
      retryReason := by simp [decodeArgs]
      propagateReason := by
        intro error phase
        simp [decodeArgs] at phase }
  obtain ⟨used, after, bound, childTrace, post, machinePost⟩ :=
    level3DecodeInlineContract decodeRaw decodeArgs (fromStep + 19) atDecode pre
  have level3 : level3DecodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      (fromStep + 19) used atDecode after :=
    ⟨rfl, decodeArgs, pre, bound, childTrace, post, machinePost⟩
  exact ⟨atDecode, trace, confined, decodeArgs, pre, used, after, .decode level3,
    bound, childTrace, post, machinePost⟩

def wrapperAfterDecodeFirstErrorBranch (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10324) (BitVec.ofNat 64 0x1037c))
    (BitVec.ofNat 64 0x1037c) retired

/-- Retire the first `decode` segment's real outgoing `bne a0, x0, 0x1037c`. Every internal error
tag is nonzero, so the checked edge must enter the wrapper's retry dispatch. -/
theorem wrapper_decode_first_error_branch_step (stepNo : Nat) (args : DecodeInlineArgs)
    (before state : State) (pre : DecodeInlinePre args before)
    (frame : DecodeInlineMachinePost before state) (error : Contracts.DecodeError)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10324))
    (tagRead : state.regs.get? x10 = some
      (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) :
    ∃ retired,
      Runs (try_step stepNo false) state (wrapperAfterDecodeFirstErrorBranch state retired) false ∧
      (wrapperAfterDecodeFirstErrorBranch state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x1037c) := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      (BitVec.ofNat 64 0x10324) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact frame.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10324) 0x63#8 0x1c#8 0x05#8 0x04#8 :=
    fetchFileInstruction state 0x10324 0x63 0x1c 0x05 0x04 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have machine := pre.machine.mono frame.agree frame.retiredCounter
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x10324) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal (Agree.refl state) frame.retiredCounter
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ :=
    counters
  have wordEq : fetchWord 0x63#8 0x1c#8 0x05#8 0x04#8 =
      (0x04051c63 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x1c#8 0x05#8 0x04#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x58#13, .Regidx 0#5, .Regidx 10#5, .BNE)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10324)
  have tagAtExecute : executeState.regs.get? x10 = some
      (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tagRead]
  have tagNonzero : BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)) ≠ 0#64 := by
    cases error <;> simp [Contracts.decodeInternalResultTag]
  have condition : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 10#5) .BNE)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState _ tagAtExecute) ?_
    refine Runs.bind (rX_x0_run executeState) ?_
    rw [bne_iff_ne.mpr tagNonzero]
    rfl
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x10324) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have targetEq : BitVec.ofNat 64 0x10324 + sign_extend (m := 64) (0x58#13) =
      BitVec.ofNat 64 0x1037c := by decide
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      state.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match read : state.regs.get? misa with
    | none => simp [read] at normalMisa
    | some bits => exact ⟨bits, rfl, by simpa [read] using normalMisa⟩
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x10324)
    misaBits misaRead
  have run := tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x10324)
    (BitVec.ofNat 64 0x10324) retired (0x58#13) (.Regidx 0#5) (.Regidx 10#5) .BNE
    inhibit config 0x63#8 0x1c#8 0x05#8 0x04#8 (_get_Misa_C misaBits == 1#1)
    fetch noMMIO fetched interrupts (by unfold BaseInstructionEncoding; decide) decode
    notExpected condition (readReg_run executeState PC _ pcAtExecute)
    (by decide) (by decide) zca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead
  refine ⟨retired, ?_, ?_⟩
  · simpa [wrapperAfterDecodeFirstErrorBranch, targetEq] using run
  · simp [wrapperAfterDecodeFirstErrorBranch, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- Package a failed first `decode` segment with its real checked outgoing edge. -/
theorem wrapper_decode_first_error_inlineTransfer (fromStep used : Nat) (args : DecodeInlineArgs)
    (before state : State) (pre : DecodeInlinePre args before)
    (body : level3DecodeChildSummary
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
      fromStep used before state)
    (frame : DecodeInlineMachinePost before state) (error : Contracts.DecodeError)
    (phase : args.phase = .first)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10324))
    (tagRead : state.regs.get? x10 = some
      (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) :
    ∃ retired, Nonempty (InlineTransfer
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary decodeInlineBoundary generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      fromStep used before (wrapperAfterDecodeFirstErrorBranch state retired)) := by
  obtain ⟨retired, branch, atResume⟩ :=
    wrapper_decode_first_error_branch_step (fromStep + used) args before state pre frame error atPc
      tagRead
  refine ⟨retired, ⟨{
    valid := decodeInlineBoundary_valid
    entryPc := BitVec.ofNat 64 0x10308
    atEntry := by simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry
    entryAccepted := by simpa [DecodeInlineArgs.entryPc, phase] using decodeInline_entry_accepted args
    entryInRegion := ?_
    entryNotExit := ?_
    sExit := state
    body := .decode body
    exitEdge := ⟨0x10324, 0x1037c⟩
    exitEdgeMem := ?_
    childExitPc := BitVec.ofNat 64 0x10324
    atExit := atPc
    exitIsEdgeSource := by decide
    exitInRegion := ?_
    exitNotExit := ?_
    doExit := branch
    resumePc := BitVec.ofNat 64 0x1037c
    atResume := atResume
    resumeIsEdgeTarget := by decide
    resumeInRegion := ?_}⟩⟩
  · apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  · simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]
  · simp [decodeInlineBoundary]
  · apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  · simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]
  · apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide

theorem wrapperAfterDecodeFirstErrorBranch_register (state : State) (retired : BitVec 64)
    (register : Register) (notPc : PC ≠ register) (notNextPc : nextPC ≠ register)
    (notIncrement : minstret_increment ≠ register) (notRetired : minstret ≠ register) :
    (wrapperAfterDecodeFirstErrorBranch state retired).regs.get? register = state.regs.get? register := by
  simp [wrapperAfterDecodeFirstErrorBranch, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
    tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    notPc, notNextPc, notIncrement, notRetired]

theorem wrapperAfterDecodeFirstErrorBranch_agree (state : State) (retired : BitVec 64) :
    Agree decoderPreserved state (wrapperAfterDecodeFirstErrorBranch state retired) := by
  intro register preserved
  have platform := preserved.2
  exact wrapperAfterDecodeFirstErrorBranch_register state retired register
    (by intro equal; subst register; simpa [platformPreserved] using platform)
    (by intro equal; subst register; simpa [platformPreserved] using platform)
    (by intro equal; subst register; simpa [platformPreserved] using platform)
    (by intro equal; subst register; simpa [platformPreserved] using platform)

theorem wrapperAfterDecodeFirstErrorBranch_retired (state : State) (retired : BitVec 64) :
    RetiredCounterPresent (wrapperAfterDecodeFirstErrorBranch state retired) := by
  refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
  simp [wrapperAfterDecodeFirstErrorBranch, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick]

theorem wrapperAfterDecodeFirstErrorBranch_code (state : State) (retired : BitVec 64)
    (code : canonicalContractParams.env.CodeIntact state) :
    canonicalContractParams.env.CodeIntact (wrapperAfterDecodeFirstErrorBranch state retired) := by
  simpa [wrapperAfterDecodeFirstErrorBranch, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
    tryStepControlFlowAfterIncrement] using code

/-- Execute the wrapper-owned `li a1, 2` between the two selected `decode` segments. -/
theorem wrapper_retry_reason_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1037c)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1037c) retired x11 (BitVec.ofNat 64 2)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x1037c) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1037c) 0x93#8 0x05#8 0x20#8 0x00#8 :=
    fetchFileInstruction state 0x1037c 0x93 0x05 0x20 0x00
      (hasExactErePrefix_programImage_of_codeIntact code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have afterIncrementAgree : Agree platformPreserved base (tryStepControlFlowAfterIncrement state) :=
    agree.trans (agree_afterIncrement state)
  have privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine :=
    (afterIncrementAgree cur_privilege (by simp [platformPreserved])).trans machine.normal.2.1
  obtain ⟨mseccfgBits, mseccfgRead, -⟩ := machine.mseccfg
  have mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits :=
    (afterIncrementAgree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x20#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
    have wordEq : fetchWord 0x93#8 0x05#8 0x20#8 0x00#8 = (0x00200593 : BitVec 32) := by decide
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1037c)
  have resultEq : iTypeResult .ADDI 0x002#12 (0#64) = BitVec.ofNat 64 2 := by decide
  have execute : Runs (execute (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 2) }
      (.Retire_Success ()) := by
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x002#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 2))
  exact decoderRegisterWriteStep machine agree retiredPresent stepNo (BitVec.ofNat 64 0x1037c)
    pcIn atPc 0x93#8 0x05#8 0x20#8 0x00#8
    (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) x11 (BitVec.ofNat 64 2)
    fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

end BinaryFv.Zesu.MachineExecution
