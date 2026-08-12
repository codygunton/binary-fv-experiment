import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.RiscV.Instruction.Execute.Arithmetic
import BinaryFv.RiscV.Instruction.RegisterRuns
import BinaryFv.RiscV.Step.FallThrough
import BinaryFv.RiscV.Step.RegisterWrite
import BinaryFv.RiscV.Proof.ImageFetch

/-! Exact closed runtime leaves selected at Level 2. -/

namespace BinaryFv.Zesu

open BinaryFv.Binary BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

private theorem endpointLiStep (stepNo pc : Nat) (state : MachineState)
    (afterExec : MachineState) (decoded : instruction)
    (byte0 byte1 byte2 byte3 : UInt8)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (pcFits : pc < 2 ^ 64)
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      decoded)
    (execute : Runs (execute decoded)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      afterExec (.Retire_Success ()))
    (nextPc : afterExec.regs.get? nextPC =
      some (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4))
    (hart : afterExec.regs.get? hart_state =
      (tryStepControlFlowAfterIncrement state).regs.get? hart_state)
    (increment : afterExec.regs.get? minstret_increment =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment)
    (retiredCounter : afterExec.regs.get? minstret =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret)
    (base : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat))
    (read0 : Artifacts.programImage.readFileByte? pc = some byte0 := by native_decide)
    (read1 : Artifacts.programImage.readFileByte? (pc + 1) = some byte1 := by native_decide)
    (read2 : Artifacts.programImage.readFileByte? (pc + 2) = some byte2 := by native_decide)
    (read3 : Artifacts.programImage.readFileByte? (pc + 3) = some byte3 := by native_decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired afterExec
        (Sail.BitVec.addInt (BitVec.ofNat 64 pc) 4) retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 pc) atPc trivial
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) pc pcFits loadedAfter
    byte0 byte1 byte2 byte3 read0 read1 read2 read3
  exact ⟨retired, tryStepFallThroughRetires stepNo state afterExec (BitVec.ofNat 64 pc) retired
    0 0 (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
    (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat)
    decoded platform noMMIO bytes interrupts base decode notExpected execute nextPc hart increment
    retiredCounter counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1
    counters.2.2.2.2.1 counters.2.2.2.2.2⟩

private theorem zkvmExitA1ZeroDecode (state : MachineState)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    Runs (ext_decode (fetchWord 0x93 0x05 0x00 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine := by
    calc
      _ = state.regs.get? cur_privilege := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := configured.normal.2.1
  have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
      some seccfgBits := by
    calc
      _ = state.regs.get? mseccfg := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
      _ = some seccfgBits := seccfgRead
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
    instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
    MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
  rfl

/-- Production `0x101c4: li a1, 0` in the closed Linux-exit leaf. -/
theorem zkvmExitA1ZeroStep (stepNo : Nat) (state : MachineState)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x101c4)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4 with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4).regs.insert
            x11 0 }
        0x101c8 retired) false := by
  let afterExec :=
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4 with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4).regs.insert
        x11 0 }
  have execute : Runs (execute (.ITYPE (0, .Regidx 0#5, .Regidx 11#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4)
      afterExec (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 0#5) (.Regidx 11#5) .ADDI) _ _ _
    simpa [afterExec] using execute_ITYPE_run _ _ 0 (.Regidx 0#5) (.Regidx 11#5) .ADDI 0
      (rX_x0_run _) (wX_x11_run _ 0)
  apply endpointLiStep stepNo 0x101c4 state afterExec
    (.ITYPE (0, .Regidx 0#5, .Regidx 11#5, .ADDI)) 0x93 0x05 0x00 0x00 configured atPc loaded
    (by native_decide) (zkvmExitA1ZeroDecode state configured) execute
    (by simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]) (by rfl)
  all_goals first
    | native_decide
    | simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert]

private theorem zkvmExitA2ZeroDecode (state : MachineState)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    Runs (ext_decode (fetchWord 0x13 0x06 0x00 0x00))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0, .Regidx 0#5, .Regidx 12#5, .ADDI)) := by
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine := by
    calc
      _ = state.regs.get? cur_privilege := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := configured.normal.2.1
  have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
      some seccfgBits := by
    calc
      _ = state.regs.get? mseccfg := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
      _ = some seccfgBits := seccfgRead
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
    instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
    MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
  rfl

/-- Production `0x101c8: li a2, 0` in the closed Linux-exit leaf. -/
theorem zkvmExitA2ZeroStep (stepNo : Nat) (state : MachineState)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x101c8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c8 with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c8).regs.insert
            x12 0 }
        0x101cc retired) false := by
  let afterExec :=
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c8 with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c8).regs.insert
        x12 0 }
  have execute : Runs (execute (.ITYPE (0, .Regidx 0#5, .Regidx 12#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c8)
      afterExec (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    simpa [afterExec] using execute_ITYPE_run _ _ 0 (.Regidx 0#5) (.Regidx 12#5) .ADDI 0
      (rX_x0_run _) (wX_x12_run _ 0)
  apply endpointLiStep stepNo 0x101c8 state afterExec
    (.ITYPE (0, .Regidx 0#5, .Regidx 12#5, .ADDI)) 0x13 0x06 0x00 0x00 configured atPc loaded
    (by native_decide) (zkvmExitA2ZeroDecode state configured) execute
    (by simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]) (by rfl)
  all_goals first
    | native_decide
    | simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert]

private theorem zkvmExitA7Decode (state : MachineState)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    Runs (ext_decode (fetchWord 0x93 0x08 0xd0 0x05))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x5d, .Regidx 0#5, .Regidx 17#5, .ADDI)) := by
  obtain ⟨seccfgBits, seccfgRead, _⟩ := configured.seccfgPresent
  have privilegeAfter : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine := by
    calc
      _ = state.regs.get? cur_privilege := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := configured.normal.2.1
  have seccfgAfter : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
      some seccfgBits := by
    calc
      _ = state.regs.get? mseccfg := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
      _ = some seccfgBits := seccfgRead
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
    instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
    MonadState.get, MonadStateOf.get, privilegeAfter, seccfgAfter, *]
  rfl

/-- Production `0x101cc: li a7, 93` in the closed Linux-exit leaf. -/
theorem zkvmExitA7Step (stepNo : Nat) (state : MachineState)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some 0x101cc)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101cc with
          regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101cc).regs.insert
            x17 93 }
        0x101d0 retired) false := by
  let afterExec :=
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101cc with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101cc).regs.insert
        x17 93 }
  have execute : Runs (execute (.ITYPE (0x5d, .Regidx 0#5, .Regidx 17#5, .ADDI)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101cc)
      afterExec (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x5d (.Regidx 0#5) (.Regidx 17#5) .ADDI) _ _ _
    simpa [afterExec] using execute_ITYPE_run _ _ 0x5d (.Regidx 0#5) (.Regidx 17#5) .ADDI 0
      (rX_x0_run _) (wX_x17_run _ 93)
  apply endpointLiStep stepNo 0x101cc state afterExec
    (.ITYPE (0x5d, .Regidx 0#5, .Regidx 17#5, .ADDI)) 0x93 0x08 0xd0 0x05 configured atPc loaded
    (by native_decide) (zkvmExitA7Decode state configured) execute
    (by simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]) (by rfl)
  all_goals first
    | native_decide
    | simp [afterExec, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert]

private theorem runtimeConfinedSailStep (stepNo : Nat) (before : EndpointState)
    (after : MachineState) (pc : BitVec 64) (atPc : EndpointPc before = some pc)
    (inside : pcInRanges Elflings.zkvmExitExecutionPcRanges pc)
    (notSyscall : ¬LinuxSyscallPc pc) (step : MachineStep stepNo before.machine after) :
    ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.zkvmExitExecutionPcRanges)
      stepNo 1 before { before with machine := after } := by
  apply ConfinedTrace.step stepNo 0 pc before { before with machine := after }
    { before with machine := after } atPc inside
  · exact endpointStep_sail stepNo before after (fun target targetPc => by
      rw [atPc] at targetPc
      cases Option.some.inj targetPc
      exact notSyscall) step
  · exact .refl (stepNo + 1) _

private theorem runtimeConfinedExitStep (stepNo : Nat) (before after : EndpointState)
    (atPc : EndpointPc before = some 0x101d0) (step : LinuxExitStep before after) :
    ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.zkvmExitExecutionPcRanges)
      stepNo 1 before after := by
  apply ConfinedTrace.step stepNo 0 0x101d0 before after after atPc
  · unfold pcInRanges
    refine ⟨(0x101c4, 0x101d4), by native_decide, by native_decide, by native_decide⟩
  · exact .exit step
  · exact .refl (stepNo + 1) _

/-- The selected `zkvm_exit` Level 2 leaf is discharged by three exact Sail instructions followed
by the linked Linux `exit` transition. -/
theorem zkvmExitInstanceContract : ZkvmExitInstanceContract := by
  refine ⟨4, ?_⟩
  intro args fromStep before entry
  rcases entry with ⟨pc0, code0, loaded0, configured0⟩
  obtain ⟨retired0, run0⟩ :=
    zkvmExitA1ZeroStep fromStep before.machine configured0 pc0 loaded0
  let machine1 := afterRegisterWrite before.machine 0x101c4 retired0 x11 0
  let state1 : EndpointState := { before with machine := machine1 }
  have run0' : MachineStep fromStep before.machine machine1 := by
    simpa [MachineStep, machine1, afterRegisterWrite] using run0
  have trace0 := runtimeConfinedSailStep fromStep before machine1 0x101c4
    (by simpa [EndpointPc] using pc0)
    (by unfold pcInRanges; refine ⟨(0x101c4, 0x101d4), ?_, ?_, ?_⟩ <;> native_decide)
    (by unfold LinuxSyscallPc; native_decide) run0'
  have configured1 : ConfiguredMachinePre EndpointMachinePc machine1 :=
    ConfiguredMachinePre.afterRegisterWrite 0x101c4 retired0 x11 0 configured0 (by
      simp [instructionPreserved, platformPreserved])
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully machine1.mem :=
    fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage before.machine
      0x101c4 retired0 x11 0 loaded0
  have pc1 : machine1.regs.get? PC = some 0x101c8 := by
    simpa [machine1] using afterRegisterWrite_pc before.machine 0x101c4 retired0 x11 0
  have code1 : machine1.regs.get? x10 = some (BitVec.ofNat 64 args.code) :=
    (afterRegisterWrite_writes before.machine 0x101c4 retired0 x11 0).get x10 (by decide) |>.trans code0
  obtain ⟨retired1, run1⟩ :=
    zkvmExitA2ZeroStep (fromStep + 1) machine1 configured1 pc1 loaded1
  let machine2 := afterRegisterWrite machine1 0x101c8 retired1 x12 0
  let state2 : EndpointState := { state1 with machine := machine2 }
  have run1' : MachineStep (fromStep + 1) machine1 machine2 := by
    simpa [MachineStep, machine2, afterRegisterWrite] using run1
  have trace1 := runtimeConfinedSailStep (fromStep + 1) state1 machine2 0x101c8
    (by simpa [state1, EndpointPc] using pc1)
    (by unfold pcInRanges; refine ⟨(0x101c4, 0x101d4), ?_, ?_, ?_⟩ <;> native_decide)
    (by unfold LinuxSyscallPc; native_decide) run1'
  have configured2 : ConfiguredMachinePre EndpointMachinePc machine2 :=
    ConfiguredMachinePre.afterRegisterWrite 0x101c8 retired1 x12 0 configured1 (by
      simp [instructionPreserved, platformPreserved])
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully machine2.mem :=
    fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage machine1
      0x101c8 retired1 x12 0 loaded1
  have pc2 : machine2.regs.get? PC = some 0x101cc := by
    simpa [machine2] using afterRegisterWrite_pc machine1 0x101c8 retired1 x12 0
  have code2 : machine2.regs.get? x10 = some (BitVec.ofNat 64 args.code) :=
    (afterRegisterWrite_writes machine1 0x101c8 retired1 x12 0).get x10 (by decide) |>.trans code1
  obtain ⟨retired2, run2⟩ :=
    zkvmExitA7Step (fromStep + 2) machine2 configured2 pc2 loaded2
  let machine3 := afterRegisterWrite machine2 0x101cc retired2 x17 93
  let state3 : EndpointState := { state2 with machine := machine3 }
  have run2' : MachineStep (fromStep + 2) machine2 machine3 := by
    simpa [MachineStep, machine3, afterRegisterWrite] using run2
  have trace2 := runtimeConfinedSailStep (fromStep + 2) state2 machine3 0x101cc
    (by simpa [state2, EndpointPc] using pc2)
    (by unfold pcInRanges; refine ⟨(0x101c4, 0x101d4), ?_, ?_, ?_⟩ <;> native_decide)
    (by unfold LinuxSyscallPc; native_decide) run2'
  have pc3 : machine3.regs.get? PC = some 0x101d0 := by
    simpa [machine3] using afterRegisterWrite_pc machine2 0x101cc retired2 x17 93
  have code3 : machine3.regs.get? x10 = some (BitVec.ofNat 64 args.code) :=
    (afterRegisterWrite_writes machine2 0x101cc retired2 x17 93).get x10 (by decide) |>.trans code2
  have syscall3 : machine3.regs.get? x17 = some (BitVec.ofNat 64 93) := by
    simpa using afterRegisterWrite_destination machine2 0x101cc retired2 x17 93
      (by decide) (by decide)
  let terminalMachine : MachineState := { machine3 with cycleCount := machine3.cycleCount + 1 }
  let terminal : EndpointState := { state3 with machine := terminalMachine, exitCode := some args.code }
  have exitStep : LinuxExitStep state3 terminal := by
    refine ⟨args.code, ?_, syscall3, code3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [state3, EndpointPc, exitEcallPc] using pc3
    · rfl
    · rfl
    · rfl
    · rfl
    · refine ⟨?_, rfl, rfl, rfl, rfl⟩
      intro register outside
      rfl
    · rfl
    · simpa [terminal, terminalMachine, exitEcallPc] using pc3
  have trace3 := runtimeConfinedExitStep (fromStep + 3) state3 terminal
    (by simpa [state3, EndpointPc] using pc3) exitStep
  have trace01 := trace0.append trace1
  have trace012 := trace01.append (by
    simpa [Nat.add_assoc, state1, state2] using trace2)
  have trace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.zkvmExitExecutionPcRanges) fromStep 4 before terminal := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, state1, state2] using
      trace012.append (by simpa [Nat.add_assoc] using trace3)
  refine ⟨4, terminal, (), by decide, by simp [zkvmExitContract], trace, ?_, trivial, ?_⟩
  · exact ⟨0x101d0, by simpa [terminal, state3, EndpointPc] using pc3, by
      unfold pcInList
      native_decide⟩
  · refine ⟨?_, rfl, rfl, rfl, rfl, ?_⟩
    · simpa [terminal, state3, EndpointPc] using pc3
    · calc
        terminal.machine.mem = machine3.mem := rfl
        _ = machine2.mem := afterRegisterWrite_mem machine2 0x101cc retired2 x17 93
        _ = machine1.mem := afterRegisterWrite_mem machine1 0x101c8 retired1 x12 0
        _ = before.machine.mem := afterRegisterWrite_mem before.machine 0x101c4 retired0 x11 0

end BinaryFv.Zesu
