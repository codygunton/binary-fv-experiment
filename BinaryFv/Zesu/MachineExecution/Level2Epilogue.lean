import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.Zesu.MachineExecution.RegisterRuns
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.RiscV.Step.TryStepStackAddi
import BinaryFv.RiscV.Step.TryStepStackAddiMemory

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

/--
The wrapper's own confined-prefix scope, named once for the whole module: `zesu_decode_raw`'s
execution addresses, its generated exit pcs, and the Level 2 child summaries.

This is an `abbrev`, so it is the same proposition as the spelled-out `ConfinedPrefix` application
and unifies with it in either direction; callers outside this module need not know the name. The
retired step count stays an explicit argument, because it is what the child-summary interface
consumes.
-/
abbrev WrapperPrefix (fromStep len : Nat) (before after : State) : Prop :=
  ConfinedPrefix
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary fromStep len before after

/-- Discharge a `DecoderFetchPc` premise for a literal pc: `owned_pc` decides that the address lies
in the function instance's execution ranges, and the alignment conjunct is a closed computation.
Like `owned_pc` this fails, rather than closing the goal, on an address the generator did not
attribute to the function instance. -/
macro "fetch_pc" : tactic =>
  `(tactic| exact ⟨by owned_pc, by first | decide | native_decide⟩)

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
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContextOfDecoderAgree machine agree
  obtain ⟨retired, run⟩ := decoderStoreWordStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x1035c 0x23 0x22 0xb9 0x00 0x4#12 11#5 18#5 statusBase status target atPc
    (rX_bits_run_x18 _ statusBase (decoderExecuteState_get? targetValue))
    (rX_bits_run_x11 _ status (decoderExecuteState_get? statusValue))
    targetEq allowed
  exact ⟨retired, by
    simpa [wrapperAfterStatusStore, afterMemoryWrite,
      show Sail.BitVec.addInt (BitVec.ofNat 64 0x1035c) 4 = BitVec.ofNat 64 0x10360 from by decide]
      using run⟩

/-- Exact state after the first epilogue stack restoration at `0x10360`. -/
def wrapperAfterFirstStackRestore (state : State) (retired stack : BitVec 64) : State :=
  tryStepStackAddiAfterRetired state (BitVec.ofNat 64 0x10360) 0x230#12 stack retired

/-- Decode the `addi sp, sp, 560` immediately following the status store. -/
theorem wrapper_epilogue_first_stack_restore_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x13#8 0x01#8 0x01#8 0x23#8)) state state
      (.ITYPE (0x230#12, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
  decode_run

/-- Execute the first of the wrapper's two epilogue stack restorations. -/
theorem wrapper_epilogue_first_stack_restore_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10360))
    (stack : BitVec 64) (stackValue : state.regs.get? x2 = some stack) :
    ∃ retired, Runs (try_step stepNo false) state
      (wrapperAfterFirstStackRestore state retired stack) false := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10360) := by
    fetch_pc
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10360) 0x13#8 0x01#8 0x01#8 0x23#8 :=
    fetchInstruction state 0x10360 0x13 0x01 0x01 0x23
      (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨_, platform⟩ := decoderStepPlatform_of_decoderAgree machine agree
    (BitVec.ofNat 64 0x10360) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, fetchNoMMIO, fetched, interrupts, notExpected, privilege, mseccfgAtIncrement⟩ :=
    platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal agree retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  refine ⟨retired, ?_⟩
  simpa [wrapperAfterFirstStackRestore, tryStepStackAddiAfterIncrement,
    tryStepControlFlowAfterIncrement] using
    tryStepStackAddiRetiresWithFetchMemory stepNo state (BitVec.ofNat 64 0x10360) 0x230#12 stack
      retired inhibit config 0x13#8 0x01#8 0x01#8 0x23#8 fetch
      (by simpa [tryStepStackAddiAfterIncrement, tryStepControlFlowAfterIncrement] using fetchNoMMIO)
      (by simpa [tryStepStackAddiAfterIncrement, tryStepControlFlowAfterIncrement] using fetched)
      interrupts (by unfold BaseInstructionEncoding; decide)
      (wrapper_epilogue_first_stack_restore_decode _ privilege _ mseccfgAtIncrement) notExpected
      (by simpa [stackAddiNextState, tryStepStackAddiAfterIncrement,
        tryStepControlFlowAfterIncrement, coreControlFlowNextState, Std.ExtDHashMap.get?_insert]
        using stackValue)
      hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- Retire one of the four real `ld` instructions in the wrapper epilogue.  Its only memory
content premise is the corresponding `SavedWordBytes` conjunct of the saved wrapper frame. -/
theorem wrapper_epilogue_saved_load_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8) (imm : BitVec 12)
    (rs1 rd : regidx) (value stack address : BitVec 64) (afterExec : State)
    (atPc : state.regs.get? PC = some pc)
    (pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw) pc)
    (stackRead : Runs (rX_bits rs1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) stack)
    (targetEq : stack + sign_extend (m := 64) imm = address)
    (savedBase : Nat) (savedBaseEq : savedBase = address.toNat)
    (saved : SavedWordBytes state savedBase value)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (allowed : DecoderAccessRange (DecoderReadableByte machineArgs) address 8)
    (fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (imm, rs1, rd, false, 8)))
    (baseEncoding : BaseInstructionEncoding byte0)
    (write : Runs (wX_bits rd value) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      afterExec ())
    (nextPcAfterExec : afterExec.regs.get? nextPC = some (Sail.BitVec.addInt pc 4))
    (hartAgree : afterExec.regs.get? hart_state =
      (tryStepControlFlowAfterIncrement state).regs.get? hart_state)
    (incrementAgree : afterExec.regs.get? minstret_increment =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret_increment)
    (retiredAgree : afterExec.regs.get? minstret =
      (tryStepControlFlowAfterIncrement state).regs.get? minstret) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired afterExec (Sail.BitVec.addInt pc 4) retired) false := by
  obtain ⟨_, platform⟩ := decoderStepPlatform_of_decoderAgree machine agree pc atPc pcIn
    _ _ _ _ fetchBytes
  obtain ⟨fetch, fetchNoMMIO, fetched, interrupts, notExpected, privilege, mseccfgAtIncrement⟩ :=
    platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal agree retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc
  have stepAgree : Agree decoderPreserved state executeState :=
    Agree.weaken (fun _ preserved => preserved.2) (agree_stepPremiseState state pc)
  have executeAgree : Agree decoderPreserved base executeState := agree.trans stepAgree
  obtain ⟨mstatusBits, mstatusRead, mprvDisabled⟩ := machine.mstatus
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := machine.mseccfg
  have addressRun := get_transformed_data_addr_machine_load_run executeState rs1 stack
    (sign_extend (m := 64) imm) mstatusBits mseccfgBits (by simpa [executeState] using stackRead)
    ((executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead)
    ((executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans machine.normal.2.1)
    mprvDisabled ((executeAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead)
    pmmDisabled
  obtain ⟨physical, loadNoMMIO⟩ := machine.dataAccess.load executeState address 8 executeAgree allowed
    (by simpa [is_aligned_paddr, is_aligned_vaddr] using aligned)
  have memoryBytes : ∀ index (bound : index < (BinaryFv.RiscV.Sep.leBytes 8 value).length),
      executeState.mem.get? (address.toNat + index) =
        some (getElem (BinaryFv.RiscV.Sep.leBytes 8 value) index bound) := by
    intro index bound
    rw [← savedBaseEq]
    simpa [SavedWordBytes, executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using saved index bound
  have execute : Runs (execute (.LOAD (imm, rs1, rd, false, 8))) executeState afterExec
      (.Retire_Success ()) := by
    change Runs (execute_LOAD imm rs1 rd false 8) _ _ _
    exact execute_LOAD_ld_run executeState _ imm rs1 rd address mstatusBits value
      ((executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead)
      ((executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans machine.normal.2.1)
      mprvDisabled (by simpa [targetEq] using addressRun) aligned physical loadNoMMIO memoryBytes
      (by simpa [executeState] using write)
  refine ⟨retired, ?_⟩
  simpa [executeState] using
    tryStepFallThroughRetires stepNo state afterExec pc retired inhibit config byte0 byte1 byte2 byte3
      (.LOAD (imm, rs1, rd, false, 8)) fetch fetchNoMMIO fetched interrupts baseEncoding decode
      notExpected execute nextPcAfterExec hartAgree incrementAgree retiredAgree hartRead inhibitRead
      configRead notInhibited machineEnabled retiredRead

/-- Execute the actual `ld ra, 2024(sp)` at `0x10364`. -/
theorem wrapper_epilogue_load_ra_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10364))
    (stack link address : BitVec 64) (stackValue : state.regs.get? x2 = some stack)
    (addressEq : stack + sign_extend (m := 64) (0x7e8#12) = address)
    (savedBase : Nat) (addressNat : savedBase = address.toNat)
    (frame : SavedWordBytes state savedBase link)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (allowed : DecoderAccessRange (DecoderReadableByte machineArgs) address 8) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10364) retired x1 link) false := by
  let pc := BitVec.ofNat 64 0x10364
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc
  have stackAtExecute : executeState.regs.get? x2 = some stack :=
    decoderExecuteState_get? stackValue
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      0x83#8 0x30#8 0x81#8 0x7e#8 :=
    fetchInstruction state 0x10364 0x83 0x30 0x81 0x7e
      (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, mseccfgRead, _⟩ := machine.mseccfg
  have incrementAgree : Agree decoderPreserved base (tryStepControlFlowAfterIncrement state) :=
    agree.trans (Agree.weaken (fun _ preserved => preserved.2) (agree_afterIncrement state))
  have privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine :=
    (incrementAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans machine.normal.2.1
  have mseccfgAtIncrement : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
      some mseccfgBits :=
    (incrementAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead
  have decode : Runs (ext_decode (fetchWord 0x83#8 0x30#8 0x81#8 0x7e#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0x7e8#12, .Regidx 2#5, .Regidx 1#5, false, 8)) := by
    decode_run
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw) pc := by
    fetch_pc
  obtain ⟨retired, run⟩ := wrapper_epilogue_saved_load_step machine agree retiredPresent stepNo pc
    0x83#8 0x30#8 0x81#8 0x7e#8 0x7e8#12 (.Regidx 2#5) (.Regidx 1#5) link stack address
    { executeState with regs := executeState.regs.insert x1 link } atPc pcIn
    (rX_x2_run executeState stack stackAtExecute) addressEq savedBase addressNat frame aligned allowed
    fetchBytes decode (by unfold BaseInstructionEncoding; decide) (wX_x1_run executeState link)
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
  exact ⟨retired, by simpa [afterRegisterWrite, pc, executeState] using run⟩

/-- Execute the actual `ld s0, 2016(sp)` at `0x10368`. -/
theorem wrapper_epilogue_load_s0_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10368))
    (stack s0 address : BitVec 64) (stackValue : state.regs.get? x2 = some stack)
    (addressEq : stack + sign_extend (m := 64) (0x7e0#12) = address)
    (savedBase : Nat) (addressNat : savedBase = address.toNat)
    (frame : SavedWordBytes state savedBase s0)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (allowed : DecoderAccessRange (DecoderReadableByte machineArgs) address 8) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10368) retired x8 s0) false := by
  let pc := BitVec.ofNat 64 0x10368
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc
  have stackAtExecute : executeState.regs.get? x2 = some stack :=
    decoderExecuteState_get? stackValue
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      0x03#8 0x34#8 0x01#8 0x7e#8 :=
    fetchInstruction state 0x10368 0x03 0x34 0x01 0x7e
      (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, mseccfgRead, _⟩ := machine.mseccfg
  have incrementAgree : Agree decoderPreserved base (tryStepControlFlowAfterIncrement state) :=
    agree.trans (Agree.weaken (fun _ preserved => preserved.2) (agree_afterIncrement state))
  have privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine :=
    (incrementAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans machine.normal.2.1
  have mseccfgAtIncrement : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
      some mseccfgBits :=
    (incrementAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead
  have decode : Runs (ext_decode (fetchWord 0x03#8 0x34#8 0x01#8 0x7e#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0x7e0#12, .Regidx 2#5, .Regidx 8#5, false, 8)) := by
    decode_run
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw) pc := by
    fetch_pc
  obtain ⟨retired, run⟩ := wrapper_epilogue_saved_load_step machine agree retiredPresent stepNo pc
    0x03#8 0x34#8 0x01#8 0x7e#8 0x7e0#12 (.Regidx 2#5) (.Regidx 8#5) s0 stack address
    { executeState with regs := executeState.regs.insert x8 s0 } atPc pcIn
    (rX_x2_run executeState stack stackAtExecute) addressEq savedBase addressNat frame aligned allowed
    fetchBytes decode (by unfold BaseInstructionEncoding; decide) (wX_x8_run executeState s0)
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
  exact ⟨retired, by simpa [afterRegisterWrite, pc, executeState] using run⟩

/-- Execute the actual `ld s1, 2008(sp)` at `0x1036c`. -/
theorem wrapper_epilogue_load_s1_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1036c))
    (stack s1 address : BitVec 64) (stackValue : state.regs.get? x2 = some stack)
    (addressEq : stack + sign_extend (m := 64) (0x7d8#12) = address)
    (savedBase : Nat) (addressNat : savedBase = address.toNat)
    (frame : SavedWordBytes state savedBase s1)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (allowed : DecoderAccessRange (DecoderReadableByte machineArgs) address 8) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1036c) retired x9 s1) false := by
  let pc := BitVec.ofNat 64 0x1036c
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc
  have stackAtExecute : executeState.regs.get? x2 = some stack :=
    decoderExecuteState_get? stackValue
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      0x83#8 0x34#8 0x81#8 0x7d#8 :=
    fetchInstruction state 0x1036c 0x83 0x34 0x81 0x7d
      (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, mseccfgRead, _⟩ := machine.mseccfg
  have incrementAgree : Agree decoderPreserved base (tryStepControlFlowAfterIncrement state) :=
    agree.trans (Agree.weaken (fun _ preserved => preserved.2) (agree_afterIncrement state))
  have privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine :=
    (incrementAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans machine.normal.2.1
  have mseccfgAtIncrement : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
      some mseccfgBits :=
    (incrementAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead
  have decode : Runs (ext_decode (fetchWord 0x83#8 0x34#8 0x81#8 0x7d#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0x7d8#12, .Regidx 2#5, .Regidx 9#5, false, 8)) := by
    decode_run
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw) pc := by
    fetch_pc
  obtain ⟨retired, run⟩ := wrapper_epilogue_saved_load_step machine agree retiredPresent stepNo pc
    0x83#8 0x34#8 0x81#8 0x7d#8 0x7d8#12 (.Regidx 2#5) (.Regidx 9#5) s1 stack address
    { executeState with regs := executeState.regs.insert x9 s1 } atPc pcIn
    (rX_x2_run executeState stack stackAtExecute) addressEq savedBase addressNat frame aligned allowed
    fetchBytes decode (by unfold BaseInstructionEncoding; decide) (wX_x9_run executeState s1)
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
  exact ⟨retired, by simpa [afterRegisterWrite, pc, executeState] using run⟩

/-- Execute the actual `ld s2, 2000(sp)` at `0x10370`. -/
theorem wrapper_epilogue_load_s2_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10370))
    (stack s2 address : BitVec 64) (stackValue : state.regs.get? x2 = some stack)
    (addressEq : stack + sign_extend (m := 64) (0x7d0#12) = address)
    (savedBase : Nat) (addressNat : savedBase = address.toNat)
    (frame : SavedWordBytes state savedBase s2)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (allowed : DecoderAccessRange (DecoderReadableByte machineArgs) address 8) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10370) retired x18 s2) false := by
  let pc := BitVec.ofNat 64 0x10370
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc
  have stackAtExecute : executeState.regs.get? x2 = some stack :=
    decoderExecuteState_get? stackValue
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      0x03#8 0x39#8 0x01#8 0x7d#8 :=
    fetchInstruction state 0x10370 0x03 0x39 0x01 0x7d
      (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, mseccfgRead, _⟩ := machine.mseccfg
  have incrementAgree : Agree decoderPreserved base (tryStepControlFlowAfterIncrement state) :=
    agree.trans (Agree.weaken (fun _ preserved => preserved.2) (agree_afterIncrement state))
  have privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine :=
    (incrementAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans machine.normal.2.1
  have mseccfgAtIncrement : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg =
      some mseccfgBits :=
    (incrementAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead
  have decode : Runs (ext_decode (fetchWord 0x03#8 0x39#8 0x01#8 0x7d#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.LOAD (0x7d0#12, .Regidx 2#5, .Regidx 18#5, false, 8)) := by
    decode_run
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw) pc := by
    fetch_pc
  obtain ⟨retired, run⟩ := wrapper_epilogue_saved_load_step machine agree retiredPresent stepNo pc
    0x03#8 0x39#8 0x01#8 0x7d#8 0x7d0#12 (.Regidx 2#5) (.Regidx 18#5) s2 stack address
    { executeState with regs := executeState.regs.insert x18 s2 } atPc pcIn
    (rX_x2_run executeState stack stackAtExecute) addressEq savedBase addressNat frame aligned allowed
    fetchBytes decode (by unfold BaseInstructionEncoding; decide) (wX_x18_run executeState s2)
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
    (by simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert])
  exact ⟨retired, by simpa [afterRegisterWrite, pc, executeState] using run⟩

/-- Exact state after the final `addi sp, sp, 2032` at `0x10374`. -/
def wrapperAfterFinalStackRestore (state : State) (retired stack : BitVec 64) : State :=
  tryStepStackAddiAfterRetired state (BitVec.ofNat 64 0x10374) 0x7f0#12 stack retired

/-- Decode the final stack restoration's production ELF word. -/
theorem wrapper_epilogue_final_stack_restore_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x13#8 0x01#8 0x01#8 0x7f#8)) state state
      (.ITYPE (0x7f0#12, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
  decode_run

/-- Execute the final wrapper stack restoration; with the preceding `+560`, it exactly reverses
the prologue's `0xa20`-byte allocation. -/
theorem wrapper_epilogue_final_stack_restore_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10374))
    (stack : BitVec 64) (stackValue : state.regs.get? x2 = some stack) :
    ∃ retired, Runs (try_step stepNo false) state
      (wrapperAfterFinalStackRestore state retired stack) false := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10374) := by
    fetch_pc
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10374) 0x13#8 0x01#8 0x01#8 0x7f#8 :=
    fetchInstruction state 0x10374 0x13 0x01 0x01 0x7f
      (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨_, platform⟩ := decoderStepPlatform_of_decoderAgree machine agree
    (BitVec.ofNat 64 0x10374) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, fetchNoMMIO, fetched, interrupts, notExpected, privilege, mseccfgAtIncrement⟩ :=
    platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal agree retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  refine ⟨retired, ?_⟩
  simpa [wrapperAfterFinalStackRestore, tryStepStackAddiAfterIncrement,
    tryStepControlFlowAfterIncrement] using
    tryStepStackAddiRetiresWithFetchMemory stepNo state (BitVec.ofNat 64 0x10374) 0x7f0#12 stack
      retired inhibit config 0x13#8 0x01#8 0x01#8 0x7f#8 fetch
      (by simpa [tryStepStackAddiAfterIncrement, tryStepControlFlowAfterIncrement] using fetchNoMMIO)
      (by simpa [tryStepStackAddiAfterIncrement, tryStepControlFlowAfterIncrement] using fetched)
      interrupts (by unfold BaseInstructionEncoding; decide)
      (wrapper_epilogue_final_stack_restore_decode _ privilege _ mseccfgAtIncrement) notExpected
      (by simpa [stackAddiNextState, tryStepStackAddiAfterIncrement,
        tryStepControlFlowAfterIncrement, coreControlFlowNextState, Std.ExtDHashMap.get?_insert]
        using stackValue)
      hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- Exact state after the wrapper's final `ret` at `0x10378`. -/
def wrapperAfterReturn (state : State) (retired link : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10378) link)
    link retired

/-- Retire the actual final `ret`, jumping to the explicitly restored return address. -/
theorem wrapper_epilogue_return_step {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10378))
    (link : BitVec 64) (linkValue : state.regs.get? x1 = some link)
    (linkEven : Sail.BitVec.update link 0 0#1 = link) (linkBit1 : Sail.BitVec.access link 1 = 0#1) :
    ∃ retired, Runs (try_step stepNo false) state (wrapperAfterReturn state retired link) false ∧
      (wrapperAfterReturn state retired link).regs.get? PC = some link := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContextOfDecoderAgree machine agree
  obtain ⟨retired, run⟩ := decoderRetStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10378 0x67 0x80 0x00 0x00 1#5 link link atPc
    (rX_bits_run_x1 _ _ (decoderExecuteState_get? linkValue))
  refine ⟨retired, ?_, ?_⟩
  · simpa [wrapperAfterReturn] using run
  · simp [wrapperAfterReturn, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]

/-- Compact public composition rule for the eight concrete instructions from the status store
through the restored-link return.  The caller supplies the typed intermediate frame facts to the
individual step theorems; this rule merely records their real machine sequencing. -/
theorem wrapper_epilogue_trace (fromStep : Nat) (before afterStore afterFirst afterRa afterS0 afterS1
    afterS2 afterStack after : State)
    (statusStore : Runs (try_step fromStep false) before afterStore false)
    (firstRestore : Runs (try_step (fromStep + 1) false) afterStore afterFirst false)
    (restoreRa : Runs (try_step (fromStep + 2) false) afterFirst afterRa false)
    (restoreS0 : Runs (try_step (fromStep + 3) false) afterRa afterS0 false)
    (restoreS1 : Runs (try_step (fromStep + 4) false) afterS0 afterS1 false)
    (restoreS2 : Runs (try_step (fromStep + 5) false) afterS1 afterS2 false)
    (finalRestore : Runs (try_step (fromStep + 6) false) afterS2 afterStack false)
    (returnRun : Runs (try_step (fromStep + 7) false) afterStack after false) :
    Trace fromStep 8 before after := by
  trace_steps [statusStore, firstRestore, restoreRa, restoreS0, restoreS1, restoreS2, finalRestore,
    returnRun]

/-- The public post-status tail boundary.  The capstone establishes this frame after the status
store; this module consumes it only from `0x10360` onward. -/
structure WrapperEpilogueTailInput (state : State) : Prop where
  frame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 state
  stack : state.regs.get? x2 = some stackValue
  result : state.regs.get? x10 = some resultValue
  status : state.regs.get? x11 = some statusValue

/-- A compact tail result exposes the actual return target and restored callee-visible registers. -/
structure WrapperEpilogueTailResult (fromStep : Nat) (before after : State) (link savedS0 savedS1
    savedS2 stack result status : BitVec 64) : Prop where
  trace : Trace fromStep 7 before after
  pc : after.regs.get? PC = some link
  ra : after.regs.get? x1 = some link
  s0 : after.regs.get? x8 = some savedS0
  s1 : after.regs.get? x9 = some savedS1
  s2 : after.regs.get? x18 = some savedS2
  sp : after.regs.get? x2 = some stack
  a0 : after.regs.get? x10 = some result
  a1 : after.regs.get? x11 = some status
  code : canonicalContractParams.env.CodeIntact after
  retired : RetiredCounterPresent after

/-- The first typed tail phase restores the stack window and then the saved return address. -/
theorem wrapper_epilogue_first_restore_and_ra {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (fromStep : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10360))
    (stackBase link savedS0 savedS1 savedS2 stack address : BitVec 64)
    (frame : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 state)
    (stackValue : state.regs.get? x2 = some stack)
    (addressEq : (stack + sign_extend (m := 64) (0x230#12)) +
      sign_extend (m := 64) (0x7e8#12) = address)
    (addressNat : stackBase.toNat + 0xa18 = address.toNat)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (allowed : DecoderAccessRange (DecoderReadableByte machineArgs) address 8) :
    ∃ retired1 retired2,
      let afterFirst := wrapperAfterFirstStackRestore state retired1 stack
      let afterRa := afterRegisterWrite afterFirst (BitVec.ofNat 64 0x10364) retired2 x1 link
      Runs (try_step fromStep false) state afterFirst false ∧
      Runs (try_step (fromStep + 1) false) afterFirst afterRa false ∧
      Trace fromStep 2 state afterRa ∧ afterRa.regs.get? x1 = some link ∧
      WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 afterRa ∧
      RetiredCounterPresent afterRa := by
  obtain ⟨retired1, firstRun⟩ := wrapper_epilogue_first_stack_restore_step machine agree retiredPresent
    code fromStep atPc stack stackValue
  let afterFirst := wrapperAfterFirstStackRestore state retired1 stack
  have stepAgree : Agree decoderPreserved state afterFirst := by
    intro register preserved
    cases register <;>
      simp only [afterFirst, wrapperAfterFirstStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState,
      stackAddiNextState, tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert] at preserved ⊢ <;>
      simp_all [decoderPreserved, platformPreserved]
  have agreeFirst : Agree decoderPreserved base afterFirst := agree.trans stepAgree
  have counterFirst : RetiredCounterPresent afterFirst := by
    refine ⟨Sail.BitVec.addInt retired1 1, ?_⟩
    simp [afterFirst, wrapperAfterFirstStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick]
  have machineFirst := machine.mono agreeFirst counterFirst
  have stackFirst : afterFirst.regs.get? x2 = some (stack + sign_extend (m := 64) (0x230#12)) := by
    simpa [afterFirst] using tryStepStackAddiAfterRetired_stackPointer state
      (BitVec.ofNat 64 0x10360) 0x230#12 stack retired1
  have frameFirst : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 afterFirst :=
    WrapperSavedRegisterFrame.of_mem_eq frame (by rfl)
  have atRa : afterFirst.regs.get? PC = some (BitVec.ofNat 64 0x10364) := by
    simp [afterFirst, wrapperAfterFirstStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState,
      stackAddiNextState, tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert]
    decide
  obtain ⟨retired2, raRun⟩ := wrapper_epilogue_load_ra_step machineFirst (Agree.refl afterFirst) counterFirst code
    (fromStep + 1) atRa (stack + sign_extend (m := 64) (0x230#12)) link address stackFirst addressEq
    (stackBase.toNat + 0xa18) addressNat frameFirst.1 aligned allowed
  let afterRa := afterRegisterWrite afterFirst (BitVec.ofNat 64 0x10364) retired2 x1 link
  refine ⟨retired1, retired2, firstRun, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [afterFirst, afterRa] using raRun
  · trace_steps [(by simpa [afterFirst] using firstRun), (by simpa [afterFirst, afterRa] using raRun)]
  · simp [afterRa, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · exact WrapperSavedRegisterFrame.of_mem_eq frameFirst (afterRegisterWrite_mem _ _ _ _ _)
  · exact afterRegisterWrite_retired_present _ _ _ _ _

/-- Restore the three saved callee registers in the wrapper's real epilogue.  This begins at
`0x10368`, immediately after `wrapper_epilogue_first_restore_and_ra`; the saved values are
arbitrary frame contents, not ABI defaults. -/
structure WrapperEpilogueSavedRegistersResult (fromStep : Nat) (base before after : State)
    (stackBase link savedS0 savedS1 savedS2 stack result status : BitVec 64) : Prop where
  trace : Trace fromStep 3 before after
  confined : WrapperPrefix fromStep 3 before after
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x10374)
  memory : after.mem = before.mem
  ra : after.regs.get? x1 = some link
  s0 : after.regs.get? x8 = some savedS0
  s1 : after.regs.get? x9 = some savedS1
  s2 : after.regs.get? x18 = some savedS2
  sp : after.regs.get? x2 = some stack
  a0 : after.regs.get? x10 = some result
  a1 : after.regs.get? x11 = some status
  frame : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 after
  code : canonicalContractParams.env.CodeIntact after
  agree : Agree decoderPreserved base after
  retired : RetiredCounterPresent after

/-- The common wrapper epilogue stopped at the generated function-instance exit instruction.
This retires the six instructions from `0x10360` through `0x10374`, but leaves `ret` at
`0x10378` unexecuted. -/
structure WrapperEpilogueExitResult (fromStep : Nat) (base before after : State)
    (link savedS0 savedS1 savedS2 restoredStack result status : BitVec 64) : Prop where
  trace : Trace fromStep 6 before after
  confined : WrapperPrefix fromStep 6 before after
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x10378)
  ra : after.regs.get? x1 = some link
  s0 : after.regs.get? x8 = some savedS0
  s1 : after.regs.get? x9 = some savedS1
  s2 : after.regs.get? x18 = some savedS2
  sp : after.regs.get? x2 = some restoredStack
  a0 : after.regs.get? x10 = some result
  a1 : after.regs.get? x11 = some status
  memory : after.mem = before.mem
  code : canonicalContractParams.env.CodeIntact after
  agree : Agree decoderPreserved base after
  retired : RetiredCounterPresent after

theorem wrapper_epilogue_restore_saved_registers {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (fromStep : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10368))
    (stackBase link savedS0 savedS1 savedS2 stack result status s0Address s1Address s2Address : BitVec 64)
    (frame : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 state)
    (raValue : state.regs.get? x1 = some link)
    (stackValue : state.regs.get? x2 = some stack)
    (resultValue : state.regs.get? x10 = some result)
    (statusValue : state.regs.get? x11 = some status)
    (s0AddressEq : stack + sign_extend (m := 64) (0x7e0#12) = s0Address)
    (s1AddressEq : stack + sign_extend (m := 64) (0x7d8#12) = s1Address)
    (s2AddressEq : stack + sign_extend (m := 64) (0x7d0#12) = s2Address)
    (s0AddressNat : stackBase.toNat + 0xa10 = s0Address.toNat)
    (s1AddressNat : stackBase.toNat + 0xa08 = s1Address.toNat)
    (s2AddressNat : stackBase.toNat + 0xa00 = s2Address.toNat)
    (s0Aligned : is_aligned_vaddr (virtaddr.Virtaddr s0Address) 8 = true)
    (s1Aligned : is_aligned_vaddr (virtaddr.Virtaddr s1Address) 8 = true)
    (s2Aligned : is_aligned_vaddr (virtaddr.Virtaddr s2Address) 8 = true)
    (s0Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s0Address 8)
    (s1Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s1Address 8)
    (s2Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s2Address 8) :
    ∃ after, WrapperEpilogueSavedRegistersResult fromStep base state after stackBase link savedS0 savedS1
      savedS2 stack result status := by
  obtain ⟨retiredS0, s0Run⟩ := wrapper_epilogue_load_s0_step machine agree retiredPresent code
    fromStep atPc stack savedS0 s0Address stackValue s0AddressEq (stackBase.toNat + 0xa10)
    s0AddressNat frame.2.1 s0Aligned s0Allowed
  let afterS0 := afterRegisterWrite state (BitVec.ofNat 64 0x10368) retiredS0 x8 savedS0
  have agreeS0 : Agree decoderPreserved base afterS0 :=
    agree.trans (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved]))
  have retiredS0Present : RetiredCounterPresent afterS0 :=
    afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10368) retiredS0 x8 savedS0
  have atS1 : afterS0.regs.get? PC = some (BitVec.ofNat 64 0x1036c) := by
    simpa [afterS0] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10368) retiredS0 x8 savedS0
  have stackS0 : afterS0.regs.get? x2 = some stack :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans stackValue
  have frameS0 : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 afterS0 :=
    WrapperSavedRegisterFrame.of_mem_eq frame (afterRegisterWrite_mem _ _ _ _ _)
  have codeS0 : canonicalContractParams.env.CodeIntact afterS0 := by
    simpa [afterS0, afterRegisterWrite_mem] using code
  have machineS0 := machine.mono agreeS0 retiredS0Present
  obtain ⟨retiredS1, s1Run⟩ := wrapper_epilogue_load_s1_step machineS0 (Agree.refl afterS0)
    retiredS0Present codeS0 (fromStep + 1) atS1 stack savedS1 s1Address stackS0 s1AddressEq
    (stackBase.toNat + 0xa08) s1AddressNat frameS0.2.2.1 s1Aligned s1Allowed
  let afterS1 := afterRegisterWrite afterS0 (BitVec.ofNat 64 0x1036c) retiredS1 x9 savedS1
  have agreeS1 : Agree decoderPreserved base afterS1 :=
    agreeS0.trans (afterRegisterWrite_agree_of (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved]))
  have retiredS1Present : RetiredCounterPresent afterS1 :=
    afterRegisterWrite_retired_present afterS0 (BitVec.ofNat 64 0x1036c) retiredS1 x9 savedS1
  have atS2 : afterS1.regs.get? PC = some (BitVec.ofNat 64 0x10370) := by
    simpa [afterS1] using afterRegisterWrite_pc afterS0 (BitVec.ofNat 64 0x1036c) retiredS1 x9 savedS1
  have stackS1 : afterS1.regs.get? x2 = some stack :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans stackS0
  have frameS1 : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 afterS1 :=
    WrapperSavedRegisterFrame.of_mem_eq frameS0 (afterRegisterWrite_mem _ _ _ _ _)
  have codeS1 : canonicalContractParams.env.CodeIntact afterS1 := by
    simpa [afterS1, afterRegisterWrite_mem] using codeS0
  have machineS1 := machine.mono agreeS1 retiredS1Present
  obtain ⟨retiredS2, s2Run⟩ := wrapper_epilogue_load_s2_step machineS1 (Agree.refl afterS1)
    retiredS1Present codeS1 (fromStep + 2) atS2 stack savedS2 s2Address stackS1 s2AddressEq
    (stackBase.toNat + 0xa00) s2AddressNat frameS1.2.2.2 s2Aligned s2Allowed
  let afterS2 := afterRegisterWrite afterS1 (BitVec.ofNat 64 0x10370) retiredS2 x18 savedS2
  have agreeS2 : Agree decoderPreserved base afterS2 :=
    agreeS1.trans (afterRegisterWrite_agree_of (P := decoderPreserved)
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have prefixS0 : WrapperPrefix fromStep 1 state afterS0 :=
    ConfinedPrefix.ownStep' atPc (by simpa [afterS0] using s0Run)
  have prefixS1 : WrapperPrefix (fromStep + 1) 1 afterS0 afterS1 :=
    ConfinedPrefix.ownStep' atS1 (by simpa [afterS0, afterS1] using s1Run)
  have prefixS2 : WrapperPrefix (fromStep + 2) 1 afterS1 afterS2 :=
    ConfinedPrefix.ownStep' atS2 (by simpa [afterS1, afterS2] using s2Run)
  have savedPrefix : WrapperPrefix fromStep 3 state afterS2 := by
    confined_steps [prefixS0, prefixS1, prefixS2]
  refine ⟨afterS2, ⟨?_, savedPrefix, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · trace_steps [(by simpa [afterS0] using s0Run), (by simpa [afterS0, afterS1] using s1Run),
      (by simpa [afterS1, afterS2] using s2Run)]
  · simpa [afterS2] using
      afterRegisterWrite_pc afterS1 (BitVec.ofNat 64 0x10370) retiredS2 x18 savedS2
  · rfl
  · exact ((afterRegisterWrite_writes _ _ _ _ _).get x1 (by decide)).trans
      (((afterRegisterWrite_writes _ _ _ _ _).get x1 (by decide)).trans
        (((afterRegisterWrite_writes _ _ _ _ _).get x1 (by decide)).trans raValue))
  · simp [afterS2, afterS1, afterS0, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [afterS2, afterS1, afterS0, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [afterS2, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · exact ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans
      (((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans
        (((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans stackValue))
  · exact ((afterRegisterWrite_writes _ _ _ _ _).get x10 (by decide)).trans
      (((afterRegisterWrite_writes _ _ _ _ _).get x10 (by decide)).trans
        (((afterRegisterWrite_writes _ _ _ _ _).get x10 (by decide)).trans resultValue))
  · exact ((afterRegisterWrite_writes _ _ _ _ _).get x11 (by decide)).trans
      (((afterRegisterWrite_writes _ _ _ _ _).get x11 (by decide)).trans
        (((afterRegisterWrite_writes _ _ _ _ _).get x11 (by decide)).trans statusValue))
  · exact WrapperSavedRegisterFrame.of_mem_eq frameS1 (afterRegisterWrite_mem _ _ _ _ _)
  · simpa [afterS2, afterRegisterWrite_mem] using codeS1
  · exact agreeS2
  · exact afterRegisterWrite_retired_present afterS1 (BitVec.ofNat 64 0x10370) retiredS2 x18 savedS2

/-- Compose the six real wrapper epilogue instructions through the final stack deallocation,
stopping at the function-instance exit instruction rather than retiring `ret`. -/
theorem wrapper_epilogue_to_exit {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (fromStep : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10360))
    (stackBase link savedS0 savedS1 savedS2 stack restoredStack result status raAddress s0Address s1Address
      s2Address : BitVec 64)
    (frame : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 state)
    (stackValue : state.regs.get? x2 = some stack)
    (resultValue : state.regs.get? x10 = some result) (statusValue : state.regs.get? x11 = some status)
    (raAddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7e8#12) = raAddress)
    (s0AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7e0#12) = s0Address)
    (s1AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7d8#12) = s1Address)
    (s2AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7d0#12) = s2Address)
    (raAddressNat : stackBase.toNat + 0xa18 = raAddress.toNat)
    (s0AddressNat : stackBase.toNat + 0xa10 = s0Address.toNat)
    (s1AddressNat : stackBase.toNat + 0xa08 = s1Address.toNat)
    (s2AddressNat : stackBase.toNat + 0xa00 = s2Address.toNat)
    (raAligned : is_aligned_vaddr (virtaddr.Virtaddr raAddress) 8 = true)
    (s0Aligned : is_aligned_vaddr (virtaddr.Virtaddr s0Address) 8 = true)
    (s1Aligned : is_aligned_vaddr (virtaddr.Virtaddr s1Address) 8 = true)
    (s2Aligned : is_aligned_vaddr (virtaddr.Virtaddr s2Address) 8 = true)
    (raAllowed : DecoderAccessRange (DecoderReadableByte machineArgs) raAddress 8)
    (s0Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s0Address 8)
    (s1Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s1Address 8)
    (s2Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s2Address 8)
    (restoredStackEq : (stack + sign_extend (m := 64) (0x230#12)) +
      sign_extend (m := 64) (0x7f0#12) = restoredStack) :
    ∃ after, WrapperEpilogueExitResult fromStep base state after link savedS0 savedS1 savedS2 restoredStack
      result status := by
  obtain ⟨retiredFirst, retiredRa, firstRun, raRun, firstTrace, raAtRa, frameRa, retiredRaPresent⟩ :=
    wrapper_epilogue_first_restore_and_ra machine agree retiredPresent code fromStep atPc stackBase link
      savedS0 savedS1 savedS2 stack raAddress frame stackValue raAddressEq raAddressNat raAligned raAllowed
  let afterFirst := wrapperAfterFirstStackRestore state retiredFirst stack
  let afterRa := afterRegisterWrite afterFirst (BitVec.ofNat 64 0x10364) retiredRa x1 link
  have agreeFirst : Agree decoderPreserved base afterFirst := by
    apply agree.trans
    intro register preserved
    cases register <;>
      simp only [afterFirst, wrapperAfterFirstStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert] at preserved ⊢ <;>
      simp_all [decoderPreserved, platformPreserved]
  have agreeRa : Agree decoderPreserved base afterRa := agreeFirst.trans
    (afterRegisterWrite_agree_of (P := decoderPreserved) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved]))
  have codeRa : canonicalContractParams.env.CodeIntact afterRa := by
    simpa [afterRa, afterFirst, wrapperAfterFirstStackRestore, afterRegisterWrite_mem] using code
  have memoryRa : afterRa.mem = state.mem := by rfl
  have stackRa : afterRa.regs.get? x2 = some (stack + sign_extend (m := 64) (0x230#12)) :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans
      (tryStepStackAddiAfterRetired_stackPointer state (BitVec.ofNat 64 0x10360) 0x230#12 stack
        retiredFirst)
  have resultRa : afterRa.regs.get? x10 = some result := by
    simp [afterRa, afterFirst, afterRegisterWrite, wrapperAfterFirstStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, resultValue]
  have statusRa : afterRa.regs.get? x11 = some status := by
    simp [afterRa, afterFirst, afterRegisterWrite, wrapperAfterFirstStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, statusValue]
  have atS0 : afterRa.regs.get? PC = some (BitVec.ofNat 64 0x10368) := by
    simpa [afterRa] using afterRegisterWrite_pc afterFirst (BitVec.ofNat 64 0x10364) retiredRa x1 link
  obtain ⟨afterS2, saved⟩ := wrapper_epilogue_restore_saved_registers machine agreeRa retiredRaPresent
    codeRa (fromStep + 2) atS0 stackBase link savedS0 savedS1 savedS2
    (stack + sign_extend (m := 64) (0x230#12)) result status s0Address s1Address s2Address frameRa raAtRa
    stackRa resultRa statusRa s0AddressEq s1AddressEq s2AddressEq s0AddressNat s1AddressNat s2AddressNat
    s0Aligned s1Aligned s2Aligned s0Allowed s1Allowed s2Allowed
  obtain ⟨retiredStack, stackRun⟩ := wrapper_epilogue_final_stack_restore_step machine saved.agree
    saved.retired saved.code (fromStep + 5) saved.pc
    (stack + sign_extend (m := 64) (0x230#12)) saved.sp
  let afterStack := wrapperAfterFinalStackRestore afterS2 retiredStack
    (stack + sign_extend (m := 64) (0x230#12))
  have stackAgree : Agree decoderPreserved afterS2 afterStack := by
    intro register preserved
    cases register <;>
      simp only [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert] at preserved ⊢ <;>
      simp_all [decoderPreserved, platformPreserved]
  have retiredStackPresent : RetiredCounterPresent afterStack := by
    refine ⟨Sail.BitVec.addInt retiredStack 1, ?_⟩
    simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick]
  have atRa : afterFirst.regs.get? PC = some (BitVec.ofNat 64 0x10364) := by
    simp [afterFirst, wrapperAfterFirstStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState,
      stackAddiNextState, tryStepStackAddiAfterIncrement, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
    decide
  have prefixFirst : WrapperPrefix fromStep 1 state afterFirst :=
    ConfinedPrefix.ownStep' atPc (by simpa [afterFirst] using firstRun)
  have prefixRa : WrapperPrefix (fromStep + 1) 1 afterFirst afterRa :=
    ConfinedPrefix.ownStep' atRa (by simpa [afterFirst, afterRa] using raRun)
  have prefixStack : WrapperPrefix (fromStep + 5) 1 afterS2 afterStack :=
    ConfinedPrefix.ownStep' saved.pc (by simpa [afterStack] using stackRun)
  have confined : WrapperPrefix fromStep 6 state afterStack := by
    confined_steps [prefixFirst, prefixRa, saved.confined, prefixStack]
  refine ⟨afterStack, ⟨?_, confined, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [Nat.add_assoc] using Trace.append firstTrace (Trace.append saved.trace
      (Trace.one (fromStep + 5) afterS2 afterStack (by simpa [afterStack] using stackRun)))
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert]
    decide
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.ra]
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.s0]
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.s1]
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.s2]
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, restoredStackEq]
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.a0]
  · simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.a1]
  · calc afterStack.mem = afterS2.mem := by rfl
      _ = afterRa.mem := saved.memory
      _ = state.mem := memoryRa
  · simpa [afterStack, wrapperAfterFinalStackRestore] using saved.code
  · exact saved.agree.trans stackAgree
  · exact retiredStackPresent

/-- The final two instructions of the wrapper epilogue return through the restored link without
changing its saved-register result. -/
structure WrapperEpilogueReturnResult (fromStep : Nat) (base before after : State)
    (link savedS0 savedS1 savedS2 stack restoredStack result status : BitVec 64) : Prop where
  trace : Trace fromStep 2 before after
  pc : after.regs.get? PC = some link
  ra : after.regs.get? x1 = some link
  s0 : after.regs.get? x8 = some savedS0
  s1 : after.regs.get? x9 = some savedS1
  s2 : after.regs.get? x18 = some savedS2
  sp : after.regs.get? x2 = some restoredStack
  a0 : after.regs.get? x10 = some result
  a1 : after.regs.get? x11 = some status
  memory : after.mem = before.mem
  code : canonicalContractParams.env.CodeIntact after
  agree : Agree decoderPreserved base after
  retired : RetiredCounterPresent after

/-- The complete post-status epilogue result, from the first stack adjustment through `ret`. -/
structure WrapperEpilogueCompleteResult (fromStep : Nat) (base before after : State)
    (link savedS0 savedS1 savedS2 restoredStack result status : BitVec 64) : Prop where
  trace : Trace fromStep 7 before after
  pc : after.regs.get? PC = some link
  ra : after.regs.get? x1 = some link
  s0 : after.regs.get? x8 = some savedS0
  s1 : after.regs.get? x9 = some savedS1
  s2 : after.regs.get? x18 = some savedS2
  sp : after.regs.get? x2 = some restoredStack
  a0 : after.regs.get? x10 = some result
  a1 : after.regs.get? x11 = some status
  memory : after.mem = before.mem
  code : canonicalContractParams.env.CodeIntact after
  agree : Agree decoderPreserved base after
  retired : RetiredCounterPresent after

/-- Execute `addi sp, sp, 2032` and the production `ret` after the typed saved-register phase. -/
theorem wrapper_epilogue_final_restore_and_return {base before state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (fromStep : Nat) (stackBase link savedS0 savedS1 savedS2 stack restoredStack result status : BitVec 64)
    (saved : WrapperEpilogueSavedRegistersResult fromStep base before state stackBase link savedS0 savedS1
      savedS2 stack result status)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10374))
    (restoredStackEq : stack + sign_extend (m := 64) (0x7f0#12) = restoredStack)
    (linkEven : Sail.BitVec.update link 0 0#1 = link) (linkBit1 : Sail.BitVec.access link 1 = 0#1) :
    ∃ after, WrapperEpilogueReturnResult (fromStep + 3) base state after link savedS0 savedS1 savedS2
      stack restoredStack result status := by
  obtain ⟨retiredStack, stackRun⟩ := wrapper_epilogue_final_stack_restore_step machine saved.agree
    saved.retired saved.code (fromStep + 3) atPc stack saved.sp
  let afterStack := wrapperAfterFinalStackRestore state retiredStack stack
  have stackAgree : Agree decoderPreserved state afterStack := by
    intro register preserved
    cases register <;>
      simp only [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState,
      stackAddiNextState, tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert] at preserved ⊢ <;>
      simp_all [decoderPreserved, platformPreserved]
  have agreeStack : Agree decoderPreserved base afterStack := saved.agree.trans stackAgree
  have retiredStackPresent : RetiredCounterPresent afterStack := by
    refine ⟨Sail.BitVec.addInt retiredStack 1, ?_⟩
    simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick]
  have codeStack : canonicalContractParams.env.CodeIntact afterStack := by
    simpa [afterStack, wrapperAfterFinalStackRestore] using saved.code
  have machineStack := machine.mono agreeStack retiredStackPresent
  have atReturn : afterStack.regs.get? PC = some (BitVec.ofNat 64 0x10378) := by
    simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState,
      stackAddiNextState, tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert]
    decide
  have linkStack : afterStack.regs.get? x1 = some link := by
    simp [afterStack, wrapperAfterFinalStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState,
      stackAddiNextState, tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert, saved.ra]
  obtain ⟨retiredReturn, returnRun, pcReturn⟩ := wrapper_epilogue_return_step machineStack
    (Agree.refl afterStack) retiredStackPresent codeStack (fromStep + 4) atReturn link linkStack
    linkEven linkBit1
  let afterReturn := wrapperAfterReturn afterStack retiredReturn link
  refine ⟨afterReturn, ⟨?_, pcReturn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · trace_steps [(by simpa [afterStack] using stackRun), (by simpa [afterReturn] using returnRun)]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, saved.ra]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, saved.s0]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, saved.s1]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, saved.s2]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, restoredStackEq]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, saved.a0]
  · simp [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, saved.a1]
  · rfl
  · simpa [afterReturn, wrapperAfterReturn, afterStack, wrapperAfterFinalStackRestore] using saved.code
  · have returnAgree : Agree decoderPreserved afterStack afterReturn :=
      Agree.weaken (fun _ preserved => preserved.2)
        ((jumpRetirement_writes _ _ _ _).agree platformPreserved_disjoint)
    exact agreeStack.trans returnAgree
  · unfold RetiredCounterPresent
    simp [afterReturn, wrapperAfterReturn, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]

/-- Compose the real seven-instruction epilogue after the status store. -/
theorem wrapper_epilogue_complete {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (fromStep : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10360))
    (stackBase link savedS0 savedS1 savedS2 stack restoredStack result status raAddress s0Address s1Address
      s2Address : BitVec 64)
    (frame : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 state)
    (stackValue : state.regs.get? x2 = some stack)
    (resultValue : state.regs.get? x10 = some result) (statusValue : state.regs.get? x11 = some status)
    (raAddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7e8#12) = raAddress)
    (s0AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7e0#12) = s0Address)
    (s1AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7d8#12) = s1Address)
    (s2AddressEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7d0#12) = s2Address)
    (raAddressNat : stackBase.toNat + 0xa18 = raAddress.toNat)
    (s0AddressNat : stackBase.toNat + 0xa10 = s0Address.toNat)
    (s1AddressNat : stackBase.toNat + 0xa08 = s1Address.toNat)
    (s2AddressNat : stackBase.toNat + 0xa00 = s2Address.toNat)
    (raAligned : is_aligned_vaddr (virtaddr.Virtaddr raAddress) 8 = true)
    (s0Aligned : is_aligned_vaddr (virtaddr.Virtaddr s0Address) 8 = true)
    (s1Aligned : is_aligned_vaddr (virtaddr.Virtaddr s1Address) 8 = true)
    (s2Aligned : is_aligned_vaddr (virtaddr.Virtaddr s2Address) 8 = true)
    (raAllowed : DecoderAccessRange (DecoderReadableByte machineArgs) raAddress 8)
    (s0Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s0Address 8)
    (s1Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s1Address 8)
    (s2Allowed : DecoderAccessRange (DecoderReadableByte machineArgs) s2Address 8)
    (restoredStackEq : (stack + sign_extend (m := 64) (0x230#12)) + sign_extend (m := 64) (0x7f0#12) = restoredStack)
    (linkEven : Sail.BitVec.update link 0 0#1 = link) (linkBit1 : Sail.BitVec.access link 1 = 0#1) :
    ∃ after, WrapperEpilogueCompleteResult fromStep base state after link savedS0 savedS1 savedS2 restoredStack
      result status := by
  obtain ⟨retiredFirst, retiredRa, firstRun, raRun, firstTrace, raAtRa, frameRa, retiredRaPresent⟩ :=
    wrapper_epilogue_first_restore_and_ra machine agree retiredPresent code fromStep atPc stackBase link
      savedS0 savedS1 savedS2 stack raAddress frame stackValue raAddressEq raAddressNat raAligned raAllowed
  let afterFirst := wrapperAfterFirstStackRestore state retiredFirst stack
  let afterRa := afterRegisterWrite afterFirst (BitVec.ofNat 64 0x10364) retiredRa x1 link
  have agreeFirst : Agree decoderPreserved base afterFirst := by
    apply agree.trans
    intro register preserved
    cases register <;>
      simp only [afterFirst, wrapperAfterFirstStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert] at preserved ⊢ <;>
      simp_all [decoderPreserved, platformPreserved]
  have agreeRa : Agree decoderPreserved base afterRa := agreeFirst.trans
    (afterRegisterWrite_agree_of (P := decoderPreserved) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved]))
  have codeRa : canonicalContractParams.env.CodeIntact afterRa := by
    simpa [afterRa, afterFirst, wrapperAfterFirstStackRestore, afterRegisterWrite_mem] using code
  have memoryRa : afterRa.mem = state.mem := by rfl
  have stackRa : afterRa.regs.get? x2 = some (stack + sign_extend (m := 64) (0x230#12)) :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans
      (tryStepStackAddiAfterRetired_stackPointer state (BitVec.ofNat 64 0x10360) 0x230#12 stack
        retiredFirst)
  have resultRa : afterRa.regs.get? x10 = some result := by
    simp [afterRa, afterFirst, afterRegisterWrite, wrapperAfterFirstStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, resultValue]
  have statusRa : afterRa.regs.get? x11 = some status := by
    simp [afterRa, afterFirst, afterRegisterWrite, wrapperAfterFirstStackRestore,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
      tryStepStackAddiAfterIncrement, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, statusValue]
  have atS0 : afterRa.regs.get? PC = some (BitVec.ofNat 64 0x10368) := by
    simpa [afterRa] using afterRegisterWrite_pc afterFirst (BitVec.ofNat 64 0x10364) retiredRa x1 link
  obtain ⟨afterS2, saved⟩ := wrapper_epilogue_restore_saved_registers machine agreeRa retiredRaPresent
    codeRa (fromStep + 2) atS0 stackBase link savedS0 savedS1 savedS2
    (stack + sign_extend (m := 64) (0x230#12)) result status s0Address s1Address s2Address frameRa raAtRa
    stackRa resultRa statusRa s0AddressEq s1AddressEq s2AddressEq s0AddressNat s1AddressNat s2AddressNat
    s0Aligned s1Aligned s2Aligned s0Allowed s1Allowed s2Allowed
  obtain ⟨afterReturn, final⟩ := wrapper_epilogue_final_restore_and_return machine (fromStep + 2)
    stackBase link savedS0 savedS1 savedS2 (stack + sign_extend (m := 64) (0x230#12)) restoredStack result
    status saved saved.pc restoredStackEq linkEven linkBit1
  refine ⟨afterReturn, ⟨?_, final.pc, final.ra, final.s0, final.s1, final.s2, final.sp, final.a0,
    final.a1, ?_, final.code, final.agree, final.retired⟩⟩
  · simpa only [Nat.add_assoc] using Trace.append firstTrace (Trace.append saved.trace final.trace)
  · calc afterReturn.mem = afterS2.mem := final.memory
      _ = afterRa.mem := saved.memory
      _ = state.mem := memoryRa

end BinaryFv.Zesu.MachineExecution
