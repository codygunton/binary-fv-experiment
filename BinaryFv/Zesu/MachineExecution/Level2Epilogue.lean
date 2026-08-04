import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep

/-!
# Shared `zesu_decode_raw` epilogue

The wrapper paths meet at `0x1035c`.  This module proves that common instruction sequence; callers
supply the value already selected for `a0`, the normalized status in `a1`, and the ordinary
machine frame carried from their own path.  No source-function ABI is assigned to an inline child.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Exact state after the shared `sw a1, 4(s2)` at `0x1035c`. -/
def wrapperAfterStatusStore (state : State) (retired target status : BitVec 64) : State :=
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1035c)
  tryStepControlFlowAfterRetired
    (afterWriteBytes (width := 4) executeState target.toNat (Sail.BitVec.extractLsb status 31 0))
    (BitVec.ofNat 64 0x10360) retired

/-- Decode the exact `sw a1, 4(s2)` encoding after the wrapper's increment step. -/
theorem wrapper_epilogue_status_store_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x23#8 0x22#8 0xb9#8 0x00#8)) state state
      (.STORE (0x4#12, .Regidx 11#5, .Regidx 18#5, 4)) := by
  decode_run

/-- Execute the common status store.  The target is explicit because `s2` is a live wrapper value,
not a callee argument convention. -/
theorem wrapper_epilogue_status_store_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1035c))
    (statusBase target status : BitVec 64) (targetValue : state.regs.get? x18 = some statusBase)
    (statusValue : state.regs.get? x11 = some status)
    (targetEq : statusBase + sign_extend (m := 64) 0x4#12 = target)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr target) 4 = true)
    (allowed : DecoderAccessRange DecoderWritableByte target 4) :
    ∃ retired, Runs (try_step stepNo false) state
      (wrapperAfterStatusStore state retired target status) false := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x1035c) := by
    refine ⟨?_, by native_decide⟩
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1035c) 0x23#8 0x22#8 0xb9#8 0x00#8 :=
    fetchFileInstruction state 0x1035c 0x23 0x22 0xb9 0x00
      (hasExactErePrefix_programImage_of_codeIntact code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mstatusBits, mstatusRead, mprvDisabled⟩ := machine.mstatus
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := machine.mseccfg
  obtain ⟨_, platform⟩ := decoderStepPlatform_of_decoderAgree machine agree
    (BitVec.ofNat 64 0x1035c) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, fetchNoMMIO, fetched, interrupts, notExpected, privilege, mseccfgAtIncrement⟩ :=
    platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal agree retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1035c)
  let afterExec := afterWriteBytes (width := 4) executeState target.toNat
    (Sail.BitVec.extractLsb status 31 0)
  have stepAgree : Agree decoderPreserved state executeState :=
    Agree.weaken (fun _ preserved => preserved.2)
      (agree_stepPremiseState state (BitVec.ofNat 64 0x1035c))
  have executeAgree : Agree decoderPreserved base executeState := agree.trans stepAgree
  have targetAtExecute : executeState.regs.get? x18 = some statusBase := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using targetValue
  have statusAtExecute : executeState.regs.get? x11 = some status := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using statusValue
  have addressRun := get_transformed_data_addr_machine_store_run executeState
    (.Regidx 18#5) 4 statusBase (sign_extend (m := 64) 0x4#12) mstatusBits mseccfgBits
    (rX_bits_run_x18 executeState statusBase targetAtExecute)
    ((executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead)
    ((executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      machine.normal.2.1)
    mprvDisabled
    ((executeAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead)
    pmmDisabled
  obtain ⟨physical, storeNoMMIO⟩ :=
    machine.dataAccess.store executeState target 4 executeAgree allowed
      (by simpa [is_aligned_paddr, is_aligned_vaddr] using aligned)
  have memoryWrite : Runs (PreSail.writeBytes (n := 4) target.toNat
      (Sail.BitVec.extractLsb status 31 0)) executeState afterExec true := by
    simpa [afterExec] using writeBytes_run_exact (width := 4) executeState target.toNat
      (Sail.BitVec.extractLsb status 31 0)
  have execute : Runs (execute (.STORE (0x4#12, .Regidx 11#5, .Regidx 18#5, 4)))
      executeState afterExec (.Retire_Success ()) :=
    execute_STORE_word_aligned_run executeState afterExec (.Regidx 11#5) (.Regidx 18#5) 0x4#12
      target mstatusBits status
      ((executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead)
      ((executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
        machine.normal.2.1)
      mprvDisabled (rX_bits_run_x11 executeState status statusAtExecute)
      (by simpa [targetEq] using addressRun) aligned physical storeNoMMIO memoryWrite
  have afterExecRegs : afterExec.regs = executeState.regs := by
    simpa [afterExec] using afterWriteBytes_regs executeState target.toNat
      (Sail.BitVec.extractLsb status 31 0)
  refine ⟨retired, ?_⟩
  simpa [wrapperAfterStatusStore, executeState, afterExec] using
    tryStepFallThroughRetires stepNo state afterExec (BitVec.ofNat 64 0x1035c) retired
      inhibit config 0x23#8 0x22#8 0xb9#8 0x00#8
      (.STORE (0x4#12, .Regidx 11#5, .Regidx 18#5, 4)) fetch fetchNoMMIO fetched interrupts
      (by unfold BaseInstructionEncoding; decide)
      (wrapper_epilogue_status_store_decode _ privilege _ mseccfgAtIncrement) notExpected execute
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
