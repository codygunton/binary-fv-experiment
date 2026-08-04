import BinaryFv.Zesu.MachineExecution.Level2Tag0Success
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.Zesu.MachineExecution.Level2WrapperProof
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.Zesu.MachineExecution.RegisterRuns

/-!
# Tag-zero post-copy wrapper instructions

The emitted `memcpy` returns to `0x10350`.  The three instructions here set the success status,
store it immediately after the 832-byte payload, and set the wrapper result before `0x1035c`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The exact post-`memcpy` facts consumed by the three tag-zero wrapper instructions. -/
structure Tag0PostMemcpyPre (base state : State) (machineArgs : DecoderMachineArgs) where
  machine : DecoderMachinePre
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    machineArgs base
  platform : Agree platformPreserved base state
  retired : RetiredCounterPresent state
  code : canonicalContractParams.env.CodeIntact state
  atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10350)
  stack : BitVec 64
  stackValue : state.regs.get? x2 = some stack
  globalsValue : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  statusSlot : DecoderAccessRange DecoderWritableByte (BitVec.ofNat 64 0x4215370) 1
  contents : ByteArray
  payload : MemoryRepresentation.MemoryBytes state 0x4215030 contents
  payloadLength : contents.size = 832
  link : BitVec 64
  savedS0 : BitVec 64
  savedS1 : BitVec 64
  savedS2 : BitVec 64
  savedFrame : WrapperSavedRegisterFrame stack.toNat link savedS0 savedS1 savedS2 state
  payloadBeforeStack : 0x4215370 ≤ stack.toNat

/-- Execute `addi a1, x0, 1` at `0x10350`. -/
theorem tag0_postcopy_status_register_step {machineArgs : DecoderMachineArgs} {base state : State}
    (pre : Tag0PostMemcpyPre base state machineArgs) (stepNo : Nat) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10350) retired x11
        (iTypeResult .ADDI 0x001#12 (BitVec.ofNat 64 0))) false := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10350) := by
    refine ⟨?_, by native_decide⟩
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have image := hasExactErePrefix_programImage_of_codeIntact pre.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10350) 0x93#8 0x05#8 0x10#8 0x00#8 :=
    fetchFileInstruction state 0x10350 0x93 0x05 0x10 0x00 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform pre.machine pre.platform
    (BitVec.ofNat 64 0x10350) pre.atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x93#8 0x05#8 0x10#8 0x00#8 = (0x00100593 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x10#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x001#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10350)
  let result := iTypeResult .ADDI 0x001#12 (BitVec.ofNat 64 0)
  have execute : Runs (execute (.ITYPE (0x001#12, .Regidx 0#5, .Regidx 11#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x11 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x001#12 (.Regidx 0#5) (.Regidx 11#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x001#12 (.Regidx 0#5) (.Regidx 11#5) .ADDI
      (BitVec.ofNat 64 0) (rX_x0_run executeState) (wX_x11_run executeState result)
  exact decoderRegisterWriteStep pre.machine pre.platform pre.retired stepNo
    (BitVec.ofNat 64 0x10350) pcIn pre.atPc 0x93#8 0x05#8 0x10#8 0x00#8
    (.ITYPE (0x001#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) x11 result fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Exact state after the tag-zero `sb a1, 848(s2)` at `0x10354`. -/
def tag0PostcopyStatusStoreAfter (state : State) (retired : BitVec 64) : State :=
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10354)
  tryStepControlFlowAfterRetired
    (afterWriteBytes (width := 1) executeState 0x4215370 (BitVec.ofNat 64 1))
    (BitVec.ofNat 64 0x10358) retired

/-- Execute the pinned `sb a1, 848(s2)` at `0x10354`; its target is immediately after the payload. -/
theorem tag0_postcopy_status_store_step {machineArgs : DecoderMachineArgs} {base state : State}
    (pre : Tag0PostMemcpyPre base state machineArgs) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10354))
    (status : state.regs.get? x11 = some (BitVec.ofNat 64 1)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tag0PostcopyStatusStoreAfter state retired) false := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10354) := by
    refine ⟨?_, by native_decide⟩
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10354) 0x23#8 0x08#8 0xb9#8 0x34#8 :=
    fetchFileInstruction state 0x10354 0x23 0x08 0xb9 0x34
      (hasExactErePrefix_programImage_of_codeIntact pre.code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mstatusBits, mstatusRead, mprvDisabled⟩ := pre.machine.mstatus
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := pre.machine.mseccfg
  have decoderAgree : Agree decoderPreserved base state :=
    Agree.weaken (fun _ preserved => preserved.2) pre.platform
  obtain ⟨_, platform⟩ := decoderStepPlatform_of_decoderAgree pre.machine decoderAgree
    (BitVec.ofNat 64 0x10354) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, fetchNoMMIO, fetched, interrupts, notExpected, privilege, mseccfgAtIncrement⟩ :=
    platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters_of_decoderAgree pre.machine.normal decoderAgree pre.retired
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10354)
  let afterExec := afterWriteBytes (width := 1) executeState 0x4215370 (BitVec.ofNat 64 1)
  have stepAgree : Agree decoderPreserved state executeState :=
    Agree.weaken (fun _ preserved => preserved.2)
      (agree_stepPremiseState state (BitVec.ofNat 64 0x10354))
  have executeAgree : Agree decoderPreserved base executeState := decoderAgree.trans stepAgree
  have globalsAtExecute : executeState.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using pre.globalsValue
  have statusAtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 1) := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using status
  have targetEq : (BitVec.ofNat 64 0x4215020) + sign_extend (m := 64) 0x350#12 =
      BitVec.ofNat 64 0x4215370 := by decide
  have addressRun := get_transformed_data_addr_machine_store_run executeState
    (.Regidx 18#5) 8 (BitVec.ofNat 64 0x4215020) (sign_extend (m := 64) 0x350#12)
    mstatusBits mseccfgBits (rX_bits_run_x18 executeState _ globalsAtExecute)
    ((executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead)
    ((executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      pre.machine.normal.2.1)
    mprvDisabled
    ((executeAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead)
    pmmDisabled
  obtain ⟨physical, storeNoMMIO⟩ :=
    pre.machine.dataAccess.store executeState (BitVec.ofNat 64 0x4215370) 1 executeAgree pre.statusSlot
      (by decide)
  have memoryWrite : Runs (PreSail.writeBytes (n := 1) 0x4215370 (BitVec.ofNat 64 1))
      executeState afterExec true := by
    simpa [afterExec] using writeBytes_run_exact (width := 1) executeState 0x4215370
      (BitVec.ofNat 64 1)
  have execute : Runs (execute (.STORE (0x350#12, .Regidx 11#5, .Regidx 18#5, 1)))
      executeState afterExec (.Retire_Success ()) :=
    execute_STORE_byte_run executeState afterExec (.Regidx 11#5) (.Regidx 18#5) 0x350#12
      (BitVec.ofNat 64 0x4215370) mstatusBits (BitVec.ofNat 64 1)
      ((executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead)
      ((executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
        pre.machine.normal.2.1)
      mprvDisabled (rX_bits_run_x11 executeState _ statusAtExecute)
      (by simpa [targetEq] using addressRun) physical storeNoMMIO memoryWrite
  have afterExecRegs : afterExec.regs = executeState.regs := by
    simpa [afterExec] using afterWriteBytes_regs executeState 0x4215370 (BitVec.ofNat 64 1)
  refine ⟨retired, ?_⟩
  simpa [tag0PostcopyStatusStoreAfter, executeState, afterExec] using
    tryStepFallThroughRetires stepNo state afterExec (BitVec.ofNat 64 0x10354) retired
      inhibit config 0x23#8 0x08#8 0xb9#8 0x34#8
      (.STORE (0x350#12, .Regidx 11#5, .Regidx 18#5, 1)) fetch fetchNoMMIO fetched interrupts
      (by unfold BaseInstructionEncoding; decide) (by decode_run) notExpected execute
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- The one-byte status store starts exactly at the first byte after the 832-byte payload. -/
theorem tag0PostcopyStatusStoreAfter_preserves_payload {state : State} (retired : BitVec 64)
    (contents : ByteArray) (payload : MemoryRepresentation.MemoryBytes state 0x4215030 contents)
    (length : contents.size = 832) :
    MemoryRepresentation.MemoryBytes (tag0PostcopyStatusStoreAfter state retired) 0x4215030 contents := by
  apply payload.of_mem_eq
  intro index indexBound
  have outside : ∀ storeIndex : Fin 1, 0x4215370 + storeIndex.val ≠ 0x4215030 + index := by
    intro storeIndex equal
    rw [length] at indexBound
    omega
  have preserved := afterWriteBytes_mem_get?_of_outside
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10354))
    0x4215370 (BitVec.ofNat 64 1) (0x4215030 + index) outside
  simpa [tag0PostcopyStatusStoreAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement] using preserved

/-- The concrete global byte store cannot overlap the four wrapper save words. -/
theorem tag0PostcopyStatusStoreAfter_preserves_saved_frame {state : State} (retired : BitVec 64)
    (stack link s0 s1 s2 : BitVec 64)
    (frame : WrapperSavedRegisterFrame stack.toNat link s0 s1 s2 state)
    (payloadBeforeStack : 0x4215370 ≤ stack.toNat) :
    WrapperSavedRegisterFrame stack.toNat link s0 s1 s2 (tag0PostcopyStatusStoreAfter state retired) := by
  have preserve (offset : Nat) (bound : offset + 8 ≤ 0xa20) (value : BitVec 64)
      (saved : SavedWordBytes state (stack.toNat + offset) value) :
      SavedWordBytes (tag0PostcopyStatusStoreAfter state retired) (stack.toNat + offset) value := by
    intro index indexBound
    have indexLt : index < 8 := by
      rw [BinaryFv.RiscV.Sep.leBytes_length] at indexBound
      exact indexBound
    have outside : ∀ storeIndex : Fin 1,
        0x4215370 + storeIndex.val ≠ stack.toNat + offset + index := by
      intro storeIndex equal
      omega
    have preserved := afterWriteBytes_mem_get?_of_outside
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10354))
      0x4215370 (BitVec.ofNat 64 1) (stack.toNat + offset + index) outside
    simpa [tag0PostcopyStatusStoreAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using
      preserved.trans (saved index indexBound)
  rcases frame with ⟨linkFrame, s0Frame, s1Frame, s2Frame⟩
  exact ⟨preserve 0xa18 (by omega) link linkFrame, preserve 0xa10 (by omega) s0 s0Frame,
    preserve 0xa08 (by omega) s1 s1Frame, preserve 0xa00 (by omega) s2 s2Frame⟩

/-- Execute `addi a0, x0, 1` at `0x10358`. -/
theorem tag0_postcopy_result_register_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10358)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10358) retired x10
        (iTypeResult .ADDI 0x001#12 (BitVec.ofNat 64 0))) false := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10358) := by
    refine ⟨?_, by native_decide⟩
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10358) 0x13#8 0x05#8 0x10#8 0x00#8 :=
    fetchFileInstruction state 0x10358 0x13 0x05 0x10 0x00 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine agree
    (BitVec.ofNat 64 0x10358) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x13#8 0x05#8 0x10#8 0x00#8 = (0x00100513 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x10#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x001#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10358)
  let result := iTypeResult .ADDI 0x001#12 (BitVec.ofNat 64 0)
  have execute : Runs (execute (.ITYPE (0x001#12, .Regidx 0#5, .Regidx 10#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x10 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x001#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x001#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI
      (BitVec.ofNat 64 0) (rX_x0_run executeState) (wX_x10_run executeState result)
  exact decoderRegisterWriteStep machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10358) pcIn atPc 0x13#8 0x05#8 0x10#8 0x00#8
    (.ITYPE (0x001#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) x10 result fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- The complete tag-zero suffix reaches the common status-store entry with result and status one. -/
structure Tag0PostcopyResult (base before after : State) (fromStep : Nat) : Prop where
  trace : Trace fromStep 3 before after
  atTerminal : after.regs.get? PC = some (BitVec.ofNat 64 0x1035c)
  resultValue : after.regs.get? x10 = some (BitVec.ofNat 64 1)
  statusValue : after.regs.get? x11 = some (BitVec.ofNat 64 1)
  payload : ∃ contents : ByteArray, contents.size = 832 ∧
    MemoryRepresentation.MemoryBytes after 0x4215030 contents
  savedFrame : ∃ stack link s0 s1 s2 : BitVec 64,
    WrapperSavedRegisterFrame stack.toNat link s0 s1 s2 after
  platform : Agree platformPreserved base after
  code : canonicalContractParams.env.CodeIntact after
  retired : RetiredCounterPresent after
  globalsValue : after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  stackValue : ∃ stack : BitVec 64, after.regs.get? x2 = some stack

theorem tag0_postcopy_complete {machineArgs : DecoderMachineArgs} {base before : State}
    (pre : Tag0PostMemcpyPre base before machineArgs) (fromStep : Nat) :
    ∃ after, Tag0PostcopyResult base before after fromStep := by
  obtain ⟨r1, h1⟩ := tag0_postcopy_status_register_step pre fromStep
  let s1 := afterRegisterWrite before (BitVec.ofNat 64 0x10350) r1 x11
    (iTypeResult .ADDI 0x001#12 (BitVec.ofNat 64 0))
  have a1 : Agree platformPreserved base s1 := pre.platform.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have c1 : RetiredCounterPresent s1 := afterRegisterWrite_retired_present _ _ _ _ _
  have code1 : canonicalContractParams.env.CodeIntact s1 := by
    rw [DecoderEnvironment.CodeIntact, afterRegisterWrite_mem]
    exact pre.code
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x10354) := by
    simpa [s1] using afterRegisterWrite_pc before (BitVec.ofNat 64 0x10350) r1 x11
      (iTypeResult .ADDI 0x001#12 (BitVec.ofNat 64 0))
  have status1 : s1.regs.get? x11 = some (BitVec.ofNat 64 1) := by
    simp [s1, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have globals1 : s1.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simpa [s1] using afterRegisterWrite_register before (BitVec.ofNat 64 0x10350) r1 x11 x18
      (iTypeResult .ADDI 0x001#12 (BitVec.ofNat 64 0)) (by decide) (by decide) (by decide)
      (by decide) (by decide) |>.trans pre.globalsValue
  have stack1 : s1.regs.get? x2 = some pre.stack := by
    simpa [s1] using afterRegisterWrite_register before (BitVec.ofNat 64 0x10350) r1 x11 x2
      (iTypeResult .ADDI 0x001#12 (BitVec.ofNat 64 0)) (by decide) (by decide) (by decide)
      (by decide) (by decide) |>.trans pre.stackValue
  have payload1 : MemoryRepresentation.MemoryBytes s1 0x4215030 pre.contents := by
    apply pre.payload.of_mem_eq
    intro index bound
    simp [s1, afterRegisterWrite_mem]
  have frame1 : WrapperSavedRegisterFrame pre.stack.toNat pre.link pre.savedS0 pre.savedS1 pre.savedS2 s1 :=
    WrapperSavedRegisterFrame.of_mem_eq pre.savedFrame (afterRegisterWrite_mem _ _ _ _ _)
  let pre1 : Tag0PostMemcpyPre base s1 machineArgs := {
    machine := pre.machine, platform := a1, retired := c1, code := code1, atPc := pc1,
    stack := pre.stack, stackValue := stack1, globalsValue := globals1, statusSlot := pre.statusSlot,
    contents := pre.contents, payload := payload1, payloadLength := pre.payloadLength,
    link := pre.link, savedS0 := pre.savedS0, savedS1 := pre.savedS1, savedS2 := pre.savedS2,
    savedFrame := frame1, payloadBeforeStack := pre.payloadBeforeStack }
  obtain ⟨r2, h2⟩ := tag0_postcopy_status_store_step pre1 (fromStep + 1) pc1 status1
  let s2 := tag0PostcopyStatusStoreAfter s1 r2
  have a2 : Agree platformPreserved base s2 := by
    intro register preserved
    have notPc : PC ≠ register := by intro h; subst register; simp [platformPreserved] at preserved
    have notNextPc : nextPC ≠ register := by intro h; subst register; simp [platformPreserved] at preserved
    have notIncrement : minstret_increment ≠ register := by intro h; subst register; simp [platformPreserved] at preserved
    have notRetired : minstret ≠ register := by intro h; subst register; simp [platformPreserved] at preserved
    simpa [s2, tag0PostcopyStatusStoreAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, afterWriteBytes_regs, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, notPc, notNextPc,
      notIncrement, notRetired] using a1 register preserved
  have c2 : RetiredCounterPresent s2 := by
    refine ⟨Sail.BitVec.addInt r2 1, ?_⟩
    simp [s2, tag0PostcopyStatusStoreAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]
  have code2 : canonicalContractParams.env.CodeIntact s2 := by
    have unbacked : ∀ index : Fin 1, Artifacts.programImage.readFileByte? (0x4215370 + index.val) = none := by native_decide
    apply fileBytesMatchMemory_afterWriteBytes Artifacts.programImage
    · exact unbacked
    simpa [s2, tag0PostcopyStatusStoreAfter, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement] using code1
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10358) := by
    simp [s2, tag0PostcopyStatusStoreAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r3, h3⟩ := tag0_postcopy_result_register_step pre.machine a2 c2 code2 (fromStep + 2) pc2
  let after := afterRegisterWrite s2 (BitVec.ofNat 64 0x10358) r3 x10
    (iTypeResult .ADDI 0x001#12 (BitVec.ofNat 64 0))
  refine ⟨after, ?_⟩
  refine { trace := ?_, atTerminal := ?_, resultValue := ?_, statusValue := ?_, payload := ?_,
    savedFrame := ?_, platform := ?_, code := ?_, retired := ?_, globalsValue := ?_, stackValue := ?_ }
  · simpa [s1, s2, after, Nat.add_assoc] using
      Trace.append (Trace.one fromStep before s1 (by simpa [s1] using h1))
        (Trace.append (Trace.one (fromStep + 1) s1 s2 (by simpa [s2] using h2))
          (Trace.one (fromStep + 2) s2 after (by simpa [after] using h3)))
  · simpa [after] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10358) r3 x10
      (iTypeResult .ADDI 0x001#12 (BitVec.ofNat 64 0))
  · simp [after, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · simp [after, s2, tag0PostcopyStatusStoreAfter, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, afterWriteBytes_regs, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · exact ⟨pre.contents, pre.payloadLength,
      tag0PostcopyStatusStoreAfter_preserves_payload r2 pre.contents payload1 pre.payloadLength |>.of_mem_eq
        (afterRegisterWrite_mem _ _ _ _ _)⟩
  · exact ⟨pre.stack, pre.link, pre.savedS0, pre.savedS1, pre.savedS2,
      WrapperSavedRegisterFrame.of_mem_eq
        (tag0PostcopyStatusStoreAfter_preserves_saved_frame r2 pre.stack pre.link pre.savedS0 pre.savedS1
          pre.savedS2 frame1 pre.payloadBeforeStack) (afterRegisterWrite_mem _ _ _ _ _)⟩
  · exact a2.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  · rw [DecoderEnvironment.CodeIntact, afterRegisterWrite_mem]; exact code2
  · exact afterRegisterWrite_retired_present _ _ _ _ _
  · simp [after, s2, tag0PostcopyStatusStoreAfter, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, afterWriteBytes_regs, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, globals1]
  · exact ⟨pre.stack, by simp [after, s2, tag0PostcopyStatusStoreAfter, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, afterWriteBytes_regs,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, stack1]⟩

end BinaryFv.Zesu.MachineExecution
