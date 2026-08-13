import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.RiscV.Instruction.DecodeTactic
import BinaryFv.RiscV.Elfling.Seg

/-!
# Closed Level 2 runtime leaves

The bare-metal Level 2 inventory contains no host-runtime child: `read_input`, `write_output`, and
`zkvm_exit` are genuine assembly functions outside the inlined decoder/encoder children selected at
this level. This module remains as the stable import point for future unconditional leaf proofs.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.Binary BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register
open MemoryAccessType mem_payload page_based_mem_type

/-- Production `0x101c4: auipc t0, 0x2400a`. -/
theorem zkvmExitLoadContextBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x101c4))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x101c4 retired x5 0x2401a1c4) false := by
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
  have decode : Runs (ext_decode (fetchWord 0x97 0xa2 0x00 0x24))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0x2400a, .Regidx 5#5, .AUIPC)) := by
    decode_run
  have pcRead : Runs (readReg PC)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4)
      0x101c4 := by
    apply readReg_run
    simp [coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (0x2400a, .Regidx 5#5, .AUIPC)))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4 with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c4).regs.insert
          x5 0x2401a1c4 }
      (.Retire_Success ()) := by
    change Runs (execute_UTYPE 0x2400a (.Regidx 5#5) .AUIPC) _ _ _
    simpa using execute_UTYPE_auipc_run _ _ 0x2400a (.Regidx 5#5) 0x101c4 pcRead
      (wX_x5_run _ 0x2401a1c4)
  exact configuredRegisterWriteStep stepNo 0x101c4 state x5 0x2401a1c4
    (.UTYPE (0x2400a, .Regidx 5#5, .AUIPC)) 0x97 0xa2 0x00 0x24
    configured atPc loaded decode execute (base := by rfl)

/-- Production `0x101c8: addi t0, t0, -268`. -/
theorem zkvmExitFinishContextBaseStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x101c8))
    (baseRead : state.regs.get? x5 = some (BitVec.ofNat 64 0x2401a1c4))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x101c8 retired x5 0x2401a0b8) false := by
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
  have decode : Runs (ext_decode (fetchWord 0x93 0x82 0x42 0xef))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0xef4, .Regidx 5#5, .Regidx 5#5, .ADDI)) := by
    decode_run
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x101c8
  have sourceRead : premise.regs.get? x5 = some (BitVec.ofNat 64 0x2401a1c4) := by
    calc
      premise.regs.get? x5 = state.regs.get? x5 :=
        (stepPremiseState_writes state 0x101c8).get x5 (by decide)
      _ = some (BitVec.ofNat 64 0x2401a1c4) := baseRead
  have execute : Runs (execute (.ITYPE (0xef4, .Regidx 5#5, .Regidx 5#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x5 0x2401a0b8 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0xef4 (.Regidx 5#5) (.Regidx 5#5) .ADDI) _ _ _
    simpa [iTypeResult] using execute_ITYPE_run premise
      { premise with regs := premise.regs.insert x5 0x2401a0b8 }
      0xef4 (.Regidx 5#5) (.Regidx 5#5) .ADDI 0x2401a1c4
      (rX_x5_run premise 0x2401a1c4 sourceRead) (wX_x5_run premise 0x2401a0b8)
  exact configuredRegisterWriteStep stepNo 0x101c8 state x5 0x2401a0b8
    (.ITYPE (0xef4, .Regidx 5#5, .Regidx 5#5, .ADDI)) 0x93 0x82 0x42 0xef
    configured atPc loaded decode execute (base := by rfl)

/-- Production `0x101cc: sd a0, 24(t0)`. -/
theorem zkvmExitStoreCodeStep (stepNo : Nat) (state : State) (code : Nat)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x101cc))
    (contextRead : state.regs.get? x5 = some (BitVec.ofNat 64 Elflings.ioContextAddress))
    (codeRead : state.regs.get? x10 = some (BitVec.ofNat 64 code))
    (pma : StorePmaAllows state (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)) 8)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStoreAfterRetired
        (afterWriteBytes (width := 8)
          (coreStoreNextState (tryStepStoreAfterIncrement state) 0x101cc)
          (Elflings.ioContextAddress + 24) (BitVec.ofNat 64 code))
        0x101cc retired) false := by
  let premise := coreStoreNextState (tryStepStoreAfterIncrement state) 0x101cc
  have agree : Agree platformPreserved state premise :=
    (stepPremiseState_writes state 0x101cc).agree platformPreserved_disjoint
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := configured.mstatusStoreMode
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := configured.seccfgPresent
  have mstatusPremise : premise.regs.get? mstatus = some mstatusBits :=
    (agree mstatus (by simp [platformPreserved])).trans mstatusRead
  have privilegePremise : premise.regs.get? cur_privilege = some .Machine :=
    (agree cur_privilege (by simp [platformPreserved])).trans configured.normal.2.1
  have mseccfgPremise : premise.regs.get? mseccfg = some mseccfgBits :=
    (agree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have contextPremise : premise.regs.get? x5 =
      some (BitVec.ofNat 64 Elflings.ioContextAddress) :=
    (stepPremiseState_writes state 0x101cc).get x5 (by decide) |>.trans contextRead
  have codePremise : premise.regs.get? x10 = some (BitVec.ofNat 64 code) :=
    (stepPremiseState_writes state 0x101cc).get x10 (by decide) |>.trans codeRead
  have contextRun := rX_x5_run premise (BitVec.ofNat 64 Elflings.ioContextAddress) contextPremise
  have codeRun := rX_x10_run premise (BitVec.ofNat 64 code) codePremise
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 5#5) (sign_extend (m := 64) (0x018#12))
        (Store Data) 8) premise premise
      (.Ext_DataAddr_OK (virtaddr.Virtaddr
        (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)))) := by
    simpa using get_transformed_data_addr_machine_data_run .store premise (.Regidx 5#5) 8
      (BitVec.ofNat 64 Elflings.ioContextAddress) (sign_extend (m := 64) (0x018#12))
      mstatusBits mseccfgBits contextRun mstatusPremise privilegePremise mprvZero
      mseccfgPremise pmmDisabled
  have pmaPremise : StorePmaAllows premise
      (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)) 8 :=
    storePmaAllows_of_agree agree pma
  have physical := phys_access_check_machine_store_allowed premise
    (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)) 8
    (fetchPmpDisabled_of_normal (normalExecutionState_of_platformPreserved agree configured.normal))
    pmaPremise (by native_decide)
  have noMMIO := storeMemoryNoMMIO_of_state_layout_excluded premise
    (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)) 8
    (by
      unfold StoreMMIOAddressExcluded DataMMIOAddressExcluded
      constructor <;> rfl)
    ((agree htif_tohost_base (by simp [platformPreserved])).trans configured.htifDisabled)
  let afterWrite := afterWriteBytes (width := 8) premise (Elflings.ioContextAddress + 24)
    (BitVec.ofNat 64 code)
  have access : ConfiguredDwordStoreAccess state afterWrite 0x101cc 0x018
      (.Regidx 5#5) (.Regidx 10#5) :=
    ⟨_, mstatusBits, _, mstatusPremise, privilegePremise, mprvZero, codeRun,
      addressRun, by native_decide, physical, noMMIO,
      writeBytes_run_exact premise (Elflings.ioContextAddress + 24) (BitVec.ofNat 64 code)⟩
  have decode : Runs (ext_decode (fetchWord 0x23 0xbc 0xa2 0x00))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (0x018, .Regidx 10#5, .Regidx 5#5, 8)) := by
    have privilegeAfter : (tryStepStoreAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepStoreAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepStoreAfterIncrement state).regs.get? mseccfg =
        some mseccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepStoreAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some mseccfgBits := mseccfgRead
    decode_run
  simpa [afterWrite] using configuredDwordStoreStep stepNo 0x101cc state afterWrite
    0x018 (.Regidx 5#5) (.Regidx 10#5) 0x23 0xbc 0xa2 0x00 configured atPc loaded
    decode access (base := by rfl)

private def zkvmExitWrites : RegSet :=
  RegSet.union stepBookkeeping (RegSet.only x5)

private theorem instructionPreserved_disjoint_zkvmExitWrites :
    RegSet.Disjoint instructionPreserved zkvmExitWrites :=
  (platformPreserved_disjoint.weaken (fun _ preserved => preserved.1)).union
    (RegSet.Disjoint.only (by simp [instructionPreserved, platformPreserved]))

private theorem platformPreserved_disjoint_zkvmExitWrites :
    RegSet.Disjoint platformPreserved zkvmExitWrites :=
  platformPreserved_disjoint.union
    (RegSet.Disjoint.only (by simp [platformPreserved]))

private theorem zkvmExitPcInside (pc : BitVec 64)
    (literal : pc = 0x101c4 ∨ pc = 0x101c8 ∨ pc = 0x101cc) :
    pcInRanges Elflings.zkvmExitExecutionPcRanges pc := by
  rcases literal with rfl | rfl | rfl <;>
    exact ⟨(0x101c4, 0x101d4), by native_decide, by native_decide, by native_decide⟩

private theorem zkvmExitPcNotExit (pc : BitVec 64)
    (literal : pc = 0x101c4 ∨ pc = 0x101c8 ∨ pc = 0x101cc) :
    ¬ pcInList Elflings.zkvmExitExitPcs pc := by
  rcases literal with rfl | rfl | rfl <;> unfold pcInList <;> native_decide

private theorem zkvmExitPcNotObserved (pc : BitVec 64)
    (literal : pc = 0x101c4 ∨ pc = 0x101c8) :
    ¬ BareMetalHostTransitionPc pc := by
  rcases literal with rfl | rfl <;>
    simp only [BareMetalHostTransitionPc] <;> native_decide

private theorem zkvmExitConfinedSailStep (stepNo : Nat) (before : EndpointState)
    (after : State) (pc : BitVec 64) (literal : pc = 0x101c4 ∨ pc = 0x101c8)
    (atPc : EndpointPc before = some pc) (step : MachineStep stepNo before.machine after) :
    ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.zkvmExitExecutionPcRanges)
      stepNo 1 before { before with machine := after } := by
  apply ConfinedTrace.step stepNo 0 pc before { before with machine := after }
    { before with machine := after }
  · exact atPc
  · exact zkvmExitPcInside pc (literal.elim Or.inl (fun h => Or.inr (Or.inl h)))
  · exact endpointStep_sail stepNo before after (fun target targetPc => by
      rw [atPc] at targetPc
      cases Option.some.inj targetPc
      exact zkvmExitPcNotObserved pc literal) step
  · exact .refl (stepNo + 1) _

private theorem zkvmExitConfinedStoreStep (stepNo : Nat) (before after : EndpointState)
    (step : BareMetalExitStep stepNo before after) :
    ConfinedTrace EndpointStep EndpointPc (pcInRanges Elflings.zkvmExitExecutionPcRanges)
      stepNo 1 before after := by
  rcases step with ⟨code, atPc, codeRead, machineStep, stdin, cursor, stdout, exitCode, terminal⟩
  apply ConfinedTrace.step stepNo 0 0x101cc before after after
  · exact atPc
  · exact zkvmExitPcInside 0x101cc (Or.inr (Or.inr rfl))
  · exact .exit ⟨code, atPc, codeRead, machineStep, stdin, cursor, stdout, exitCode, terminal⟩
  · exact .refl (stepNo + 1) _

/-- The bare-metal `zkvm_exit` function implements its Level 1 contract unconditionally. -/
theorem zkvmExitInstanceContract : ZkvmExitInstanceContract := by
  refine ⟨3, ?_⟩
  intro args fromStep before entry
  rcases entry with ⟨atPc, codeRead, pma, loaded, configured⟩
  obtain ⟨retired1, run1⟩ := zkvmExitLoadContextBaseStep fromStep before.machine
    configured atPc loaded
  let state1 := afterRegisterWrite before.machine 0x101c4 retired1 x5 0x2401a1c4
  have writes1 : WritesOnlyRegs zkvmExitWrites before.machine state1 :=
    (afterRegisterWrite_writes before.machine 0x101c4 retired1 x5 0x2401a1c4).mono
      (fun _ written => written.elim Or.inl (fun h => h ▸ Or.inr rfl))
  have configured1 : ConfiguredMachinePre EndpointMachinePc state1 :=
    configured.mono (writes1.agree instructionPreserved_disjoint_zkvmExitWrites)
      (afterRegisterWrite_retired_present before.machine 0x101c4 retired1 x5 0x2401a1c4)
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully state1.mem := by
    rw [afterRegisterWrite_mem]
    exact loaded
  have base1 : state1.regs.get? x5 = some (BitVec.ofNat 64 0x2401a1c4) :=
    afterRegisterWrite_destination before.machine 0x101c4 retired1 x5 0x2401a1c4
      (by decide) (by decide)
  have atPc1 : state1.regs.get? PC = some (BitVec.ofNat 64 0x101c8) := by
    simpa using afterRegisterWrite_pc before.machine 0x101c4 retired1 x5 0x2401a1c4
  obtain ⟨retired2, run2⟩ := zkvmExitFinishContextBaseStep (fromStep + 1) state1
    configured1 atPc1 base1 loaded1
  let state2 := afterRegisterWrite state1 0x101c8 retired2 x5 0x2401a0b8
  have writes2 : WritesOnlyRegs zkvmExitWrites state1 state2 :=
    (afterRegisterWrite_writes state1 0x101c8 retired2 x5 0x2401a0b8).mono
      (fun _ written => written.elim Or.inl (fun h => h ▸ Or.inr rfl))
  have configured2 : ConfiguredMachinePre EndpointMachinePc state2 :=
    configured1.mono (writes2.agree instructionPreserved_disjoint_zkvmExitWrites)
      (afterRegisterWrite_retired_present state1 0x101c8 retired2 x5 0x2401a0b8)
  have loaded2 : Artifacts.programImage.fileBytesLoadedFaithfully state2.mem := by
    rw [afterRegisterWrite_mem]
    exact loaded1
  have context2 : state2.regs.get? x5 =
      some (BitVec.ofNat 64 Elflings.ioContextAddress) := by
    simpa [Elflings.ioContextAddress] using
      afterRegisterWrite_destination state1 0x101c8 retired2 x5 0x2401a0b8
        (by decide) (by decide)
  have atPc2 : state2.regs.get? PC = some (BitVec.ofNat 64 0x101cc) := by
    simpa using afterRegisterWrite_pc state1 0x101c8 retired2 x5 0x2401a0b8
  have code2 : state2.regs.get? x10 = some (BitVec.ofNat 64 args.code) := by
    exact (writes2.get x10 (by simp [zkvmExitWrites])).trans
      ((writes1.get x10 (by simp [zkvmExitWrites])).trans codeRead)
  have pma2 : StorePmaAllows state2
      (BitVec.ofNat 64 (Elflings.ioContextAddress + 24)) 8 :=
    storePmaAllows_of_agree
      ((writes1.trans_same writes2).agree platformPreserved_disjoint_zkvmExitWrites) pma
  obtain ⟨retired3, run3⟩ := zkvmExitStoreCodeStep (fromStep + 2) state2 args.code
    configured2 atPc2 context2 code2 pma2 loaded2
  let state3 := tryStepStoreAfterRetired
    (afterWriteBytes (width := 8)
      (coreStoreNextState (tryStepStoreAfterIncrement state2) 0x101cc)
      (Elflings.ioContextAddress + 24) (BitVec.ofNat 64 args.code))
    0x101cc retired3
  let state1Endpoint : EndpointState := { before with machine := state1 }
  let state2Endpoint : EndpointState := { before with machine := state2 }
  let after : EndpointState := { before with machine := state3, exitCode := some args.code }
  have trace1 := zkvmExitConfinedSailStep fromStep before state1 0x101c4 (Or.inl rfl)
    atPc run1
  have trace2 := zkvmExitConfinedSailStep (fromStep + 1) state1Endpoint state2 0x101c8
    (Or.inr rfl) atPc1 run2
  have finalPc : state3.regs.get? PC =
      some (BitVec.ofNat 64 Elflings.zkvmExitTerminalPc) := by
    simp only [state3, tryStepStoreAfterRetired, tryStepStoreAfterTick]
    rw [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert]
    rw [dif_neg (by decide : (minstret == PC) ≠ true)]
    rw [dif_pos (by decide : (PC == PC) = true)]
    rfl
  have exitStep : BareMetalExitStep (fromStep + 2) state2Endpoint after := by
    exact ⟨args.code, atPc2, code2, run3, rfl, rfl, rfl, rfl, finalPc⟩
  have trace3 := zkvmExitConfinedStoreStep (fromStep + 2) state2Endpoint after exitStep
  have trace12 : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.zkvmExitExecutionPcRanges) fromStep 2 before state2Endpoint := by
    simpa [state1Endpoint, state2Endpoint] using trace1.append trace2
  have trace : ConfinedTrace EndpointStep EndpointPc
      (pcInRanges Elflings.zkvmExitExecutionPcRanges) fromStep 3 before after := by
    simpa [state2Endpoint] using trace12.append trace3
  refine ⟨3, after, (), by decide, ?_, trace, ?_, trivial, ?_⟩
  · exact Nat.le_refl 3
  · exact ⟨0x101d0, finalPc, by unfold pcInList; native_decide⟩
  · refine ⟨finalPc, rfl, rfl, rfl, rfl, ?_⟩
    have prefixMem : state2.mem = before.machine.mem := by
      simp [state2, state1, afterRegisterWrite_mem]
    have storeMem : WritesOnlyWithin (byteRange (Elflings.ioContextAddress + 24) 8)
        state2 state3 := by
      intro address outside
      exact storeRetirement_mem_writes state2 0x101cc 0x101d0 retired3
        (Elflings.ioContextAddress + 24) (BitVec.ofNat 64 args.code) address outside
    exact WritesOnlyWithin.trans_same (writesOnlyWithin_of_mem_eq prefixMem) storeMem

end BinaryFv.Zesu.MachineExecution
