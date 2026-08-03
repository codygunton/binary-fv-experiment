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

end BinaryFv.Zesu.MachineExecution
