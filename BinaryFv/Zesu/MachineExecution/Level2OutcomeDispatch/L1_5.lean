import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.Level2TerminalRouteFrame
import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps

/-!
# Level 2 result-tag dispatch

The wrapper owns the instructions after either inlined `decode` segment reaches `0x103fc`.
These Sail proofs distinguish the internal result tags before entering the shared wrapper tail.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The first dispatch instruction writes the tag-three comparison constant. -/
theorem wrapper_dispatch_tag3_constant_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x103fc) retired x11 (BitVec.ofNat 64 3)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x103fc) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x103fc) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103fc) 0x93#8 0x05#8 0x30#8 0x00#8 :=
    fetchFileInstruction state 0x103fc 0x93 0x05 0x30 0x00
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
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x30#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x003#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
    change Runs (ext_decode (0x00300593 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103fc)
  have execute : Runs (execute (.ITYPE (0x003#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 3) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x003#12 (0#64) = BitVec.ofNat 64 3 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x003#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 3))
  exact decoderRegisterWriteStep machine agree retiredPresent stepNo (BitVec.ofNat 64 0x103fc)
    fetchPc atPc 0x93#8 0x05#8 0x30#8 0x00#8
    (.ITYPE (0x003#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) x11 (BitVec.ofNat 64 3)
    fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Exact post-state of the tag-three branch at `0x10400`. -/
def wrapperDispatchTag3BranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10400) (BitVec.ofNat 64 0x10434))
    (BitVec.ofNat 64 0x10434) retired

end BinaryFv.Zesu.MachineExecution
