import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.RiscV.Instruction.DecodeTactic
import BinaryFv.RiscV.Instruction.Execute.Arithmetic

/-! Exact Sail steps for the production `read_input` function at `0x10140`. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

private theorem readInputDecodeReads (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    ∃ seccfgBits,
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine ∧
      (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some seccfgBits := by
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  refine ⟨seccfgBits, ?_, ?_⟩
  · calc
      _ = state.regs.get? cur_privilege := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := configured.normal.2.1
  · calc
      _ = state.regs.get? mseccfg := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
      _ = some seccfgBits := seccfgRead

private theorem coreRegisterRead {register : Register} {value : RegisterType register}
    (state : State) (pc : BitVec 64) (read : state.regs.get? register = some value)
    (notIncrement : register ≠ minstret_increment := by decide)
    (notNextPc : register ≠ nextPC := by decide) :
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.get? register =
      some value := by
  calc
    _ = (tryStepControlFlowAfterIncrement state).regs.get? register := by
      simpa [coreControlFlowNextState] using
        writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC register
          (Sail.BitVec.addInt pc 4) notNextPc
    _ = state.regs.get? register := by
      simpa [tryStepControlFlowAfterIncrement] using
        writeReg_read_unchanged state minstret_increment register true notIncrement
    _ = some value := read

/-- Production `0x10140: mv t1, a0`. -/
theorem readInputMoveBufferSlotStep (stepNo : Nat) (state : State) (value : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x10140)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (source : state.regs.get? x10 = some value) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x10140 retired x6 (iTypeResult .ADDI 0 value)) false := by
  obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := readInputDecodeReads state configured
  have decode : Runs (ext_decode (fetchWord 0x13 0x03 0x05 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0, .Regidx 10#5, .Regidx 6#5, .ADDI)) := by
    decode_run
  have execute : Runs (execute (.ITYPE (0, .Regidx 10#5, .Regidx 6#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10140)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10140 with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10140).regs.insert
          x6 (iTypeResult .ADDI 0 value) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 10#5) (.Regidx 6#5) .ADDI) _ _ _
    exact execute_ITYPE_run _ _ 0 (.Regidx 10#5) (.Regidx 6#5) .ADDI value
      (rX_x10_run _ _ (coreRegisterRead state 0x10140 source)) (wX_x6_run _ _)
  exact configuredRegisterWriteStep stepNo 0x10140 state x6 (iTypeResult .ADDI 0 value)
    (.ITYPE (0, .Regidx 10#5, .Regidx 6#5, .ADDI)) 0x13 0x03 0x05 0x00 configured atPc loaded
    decode execute (base := by rfl)

/-- Production `0x10144: mv a6, a1`. -/
theorem readInputMoveSizeSlotStep (stepNo : Nat) (state : State) (value : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x10144)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (source : state.regs.get? x11 = some value) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x10144 retired x16 (iTypeResult .ADDI 0 value)) false := by
  obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := readInputDecodeReads state configured
  have decode : Runs (ext_decode (fetchWord 0x13 0x88 0x05 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0, .Regidx 11#5, .Regidx 16#5, .ADDI)) := by
    decode_run
  have execute : Runs (execute (.ITYPE (0, .Regidx 11#5, .Regidx 16#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10144)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10144 with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10144).regs.insert
          x16 (iTypeResult .ADDI 0 value) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 11#5) (.Regidx 16#5) .ADDI) _ _ _
    exact execute_ITYPE_run _ _ 0 (.Regidx 11#5) (.Regidx 16#5) .ADDI value
      (rX_x11_run _ _ (coreRegisterRead state 0x10144 source)) (wX_x16_run _ _)
  exact configuredRegisterWriteStep stepNo 0x10144 state x16 (iTypeResult .ADDI 0 value)
    (.ITYPE (0, .Regidx 11#5, .Regidx 16#5, .ADDI)) 0x13 0x88 0x05 0x00 configured atPc loaded
    decode execute (base := by rfl)

/-- Production `0x10148: li a5, 0`. -/
theorem readInputZeroOffsetStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x10148)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x10148 retired x15 (iTypeResult .ADDI 0 0)) false := by
  obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := readInputDecodeReads state configured
  have decode : Runs (ext_decode (fetchWord 0x93 0x07 0x00 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0, .Regidx 0#5, .Regidx 15#5, .ADDI)) := by
    decode_run
  have execute : Runs (execute (.ITYPE (0, .Regidx 0#5, .Regidx 15#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10148)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10148 with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10148).regs.insert
          x15 (iTypeResult .ADDI 0 0) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 0#5) (.Regidx 15#5) .ADDI) _ _ _
    exact execute_ITYPE_run _ _ 0 (.Regidx 0#5) (.Regidx 15#5) .ADDI 0
      (rX_x0_run _) (wX_x15_run _ _)
  exact configuredRegisterWriteStep stepNo 0x10148 state x15 (iTypeResult .ADDI 0 0)
    (.ITYPE (0, .Regidx 0#5, .Regidx 15#5, .ADDI)) 0x93 0x07 0x00 0x00 configured atPc loaded
    decode execute (base := by rfl)

/-- Production `0x1014c: auipc a4, 0x2000a`. -/
theorem readInputBufferBaseHighStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x1014c)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1014c retired x14
        (0x1014c + sign_extend (m := 64) (0x2000a#20 ++ 0x000#12))) false := by
  obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := readInputDecodeReads state configured
  have decode : Runs (ext_decode (fetchWord 0x17 0xa7 0x00 0x20))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0x2000a#20, .Regidx 14#5, .AUIPC)) := by
    decode_run
  have pcRead : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x1014c)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x1014c) 0x1014c := by
    apply readReg_run
    exact coreRegisterRead state 0x1014c atPc
  have execute : Runs (execute (.UTYPE (0x2000a#20, .Regidx 14#5, .AUIPC)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x1014c)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x1014c with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x1014c).regs.insert
          x14 (0x1014c + sign_extend (m := 64) (0x2000a#20 ++ 0x000#12)) }
      (.Retire_Success ()) := by
    change Runs (execute_UTYPE 0x2000a#20 (.Regidx 14#5) .AUIPC) _ _ _
    exact execute_UTYPE_auipc_run _ _ 0x2000a#20 (.Regidx 14#5) 0x1014c pcRead
      (wX_x14_run _ _)
  exact configuredRegisterWriteStep stepNo 0x1014c state x14
    (0x1014c + sign_extend (m := 64) (0x2000a#20 ++ 0x000#12))
    (.UTYPE (0x2000a#20, .Regidx 14#5, .AUIPC)) 0x17 0xa7 0x00 0x20 configured atPc loaded
    decode execute (base := by rfl)

/-- Production `0x10150: addi a4, a4, -332`. -/
theorem readInputBufferBaseLowStep (stepNo : Nat) (state : State) (value : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x10150)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (source : state.regs.get? x14 = some value) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x10150 retired x14 (iTypeResult .ADDI 0xeb4 value)) false := by
  obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := readInputDecodeReads state configured
  have decode : Runs (ext_decode (fetchWord 0x13 0x07 0x47 0xeb))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0xeb4, .Regidx 14#5, .Regidx 14#5, .ADDI)) := by
    decode_run
  have execute : Runs (execute (.ITYPE (0xeb4, .Regidx 14#5, .Regidx 14#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10150)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10150 with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10150).regs.insert
          x14 (iTypeResult .ADDI 0xeb4 value) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0xeb4 (.Regidx 14#5) (.Regidx 14#5) .ADDI) _ _ _
    exact execute_ITYPE_run _ _ 0xeb4 (.Regidx 14#5) (.Regidx 14#5) .ADDI value
      (rX_x14_run _ _ (coreRegisterRead state 0x10150 source)) (wX_x14_run _ _)
  exact configuredRegisterWriteStep stepNo 0x10150 state x14 (iTypeResult .ADDI 0xeb4 value)
    (.ITYPE (0xeb4, .Regidx 14#5, .Regidx 14#5, .ADDI)) 0x13 0x07 0x47 0xeb configured atPc loaded
    decode execute (base := by rfl)

/-- Production `0x10154: lui a3, 0x4000`. -/
theorem readInputBufferCapacityStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x10154)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x10154 retired x13
        (sign_extend (m := 64) (0x04000#20 ++ 0x000#12))) false := by
  obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ := readInputDecodeReads state configured
  have decode : Runs (ext_decode (fetchWord 0xb7 0x06 0x00 0x04))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0x04000#20, .Regidx 13#5, .LUI)) := by
    decode_run
  have execute : Runs (execute (.UTYPE (0x04000#20, .Regidx 13#5, .LUI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10154)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10154 with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x10154).regs.insert
          x13 (sign_extend (m := 64) (0x04000#20 ++ 0x000#12)) }
      (.Retire_Success ()) := by
    change Runs (execute_UTYPE 0x04000#20 (.Regidx 13#5) .LUI) _ _ _
    exact execute_UTYPE_lui_run _ _ 0x04000#20 (.Regidx 13#5) (wX_x13_run _ _)
  exact configuredRegisterWriteStep stepNo 0x10154 state x13
    (sign_extend (m := 64) (0x04000#20 ++ 0x000#12))
    (.UTYPE (0x04000#20, .Regidx 13#5, .LUI)) 0xb7 0x06 0x00 0x04 configured atPc loaded
    decode execute (base := by rfl)

end BinaryFv.Zesu.MachineExecution
