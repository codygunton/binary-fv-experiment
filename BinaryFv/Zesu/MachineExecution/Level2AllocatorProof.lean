import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Boundaries
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.RiscV.Elfling.SequentialSplice
import BinaryFv.RiscV.Instruction.Execute.StoreByte
import BinaryFv.RiscV.Instruction.Execute.RegisterOp

/-!
# Sail execution of the inlined Level 2 allocator construction

The inlined `allocator` is not a callable function and has no RISC-V ABI obligation. Its five
instructions occupy two regions separated by the wrapper's store at `0x102f4`. This module executes
those instructions at their real machine boundaries. It begins with the first one-instruction
segment; the remaining four-instruction segment follows after the wrapper store is connected.
-/

namespace BinaryFv.Zesu.MachineExecution

open RegisterWriteStep

open BinaryFv BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

/-- Exact state after `addi a1, s2, 1` at the allocator's first inline segment. -/
def allocatorAfterDataPointer (state : State) (retired source : BitVec 64) : State :=
  afterRegisterWrite state (BitVec.ofNat 64 0x102f0) retired x11 (Sail.BitVec.addInt source 1)

theorem allocator_data_pointer_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102f0)
      0x93#8 0x05#8 0x19#8 0x00#8 :=
  fetchFileInstruction state 0x102f0 0x93 0x05 0x19 0x00 loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem allocator_data_pointer_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x19#8 0x00#8)) state state
      (.ITYPE (0x001#12, .Regidx 18#5, .Regidx 11#5, .ADDI)) := by
  decode_run

/-- Exact state after the wrapper stores the allocator tag byte at `0x102f4`. -/
def wrapperAfterAllocatorTag (state : State) (retired target data : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x102f4) with
      mem := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x102f4)).mem.insert target.toNat
          (Sail.BitVec.extractLsb data 7 0) }
    (BitVec.ofNat 64 0x102f8) retired

/-- Exact state after `auipc a0, 4` begins the allocator's second inline segment. -/
def allocatorAfterFunctionPage (state : State) (retired : BitVec 64) : State :=
  afterRegisterWrite state (BitVec.ofNat 64 0x102f8) retired x10
    (BitVec.ofNat 64 0x142f8)

/-- Exact state after resolving the `allocatorAlloc` function address. -/
def allocatorAfterFunctionAddress (state : State) (retired : BitVec 64) : State :=
  afterRegisterWrite state (BitVec.ofNat 64 0x102fc) retired x10
    (BitVec.ofNat 64 0x13f70)

/-- Exact state after storing the allocator context pointer in the stack allocator object. -/
def allocatorAfterContextStore (state : State) (retired stackBase context : BitVec 64) : State :=
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10300)
  let target := stackBase + sign_extend (0x010#12)
  tryStepControlFlowAfterRetired (afterWriteBytes (width := 8) executeState target.toNat context)
    (BitVec.ofNat 64 0x10304) retired

theorem allocatorAfterContextStore_get?_of_ne (state : State)
    (retired stackBase context : BitVec 64) (register : Register)
    (notPc : register ≠ PC) (notNextPc : register ≠ nextPC)
    (notIncrement : register ≠ minstret_increment) (notRetired : register ≠ minstret) :
    (allocatorAfterContextStore state retired stackBase context).regs.get? register =
      state.regs.get? register := by
  have pcNot : PC ≠ register := Ne.symm notPc
  have nextPcNot : nextPC ≠ register := Ne.symm notNextPc
  have incrementNot : minstret_increment ≠ register := Ne.symm notIncrement
  have retiredNot : minstret ≠ register := Ne.symm notRetired
  simp [allocatorAfterContextStore, afterWriteBytes_regs, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
    Std.ExtDHashMap.get?_insert, pcNot, nextPcNot, incrementNot, retiredNot]

theorem allocatorAfterContextStore_agree (state : State) (retired stackBase context : BitVec 64) :
    Agree platformPreserved state
      (allocatorAfterContextStore state retired stackBase context) := by
  intro register preserved
  have notPc : PC ≠ register := by
    intro equal
    subst register
    simpa [platformPreserved] using preserved
  have notNextPc : nextPC ≠ register := by
    intro equal
    subst register
    simpa [platformPreserved] using preserved
  have notIncrement : minstret_increment ≠ register := by
    intro equal
    subst register
    simpa [platformPreserved] using preserved
  have notRetired : minstret ≠ register := by
    intro equal
    subst register
    simpa [platformPreserved] using preserved
  simp [allocatorAfterContextStore, afterWriteBytes_regs, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
    Std.ExtDHashMap.get?_insert, notPc, notNextPc, notIncrement, notRetired]

theorem allocatorAfterContextStore_retired (state : State)
    (retired stackBase context : BitVec 64) :
    RetiredCounterPresent (allocatorAfterContextStore state retired stackBase context) := by
  refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
  simp [allocatorAfterContextStore, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]

theorem allocatorAfterContextStore_pc (state : State)
    (retired stackBase context : BitVec 64) :
    (allocatorAfterContextStore state retired stackBase context).regs.get? PC =
      some (BitVec.ofNat 64 0x10304) := by
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10300)
  have storedRegs :
      (afterWriteBytes (width := 8) executeState
        (stackBase + sign_extend (0x010#12)).toNat context).regs = executeState.regs :=
    afterWriteBytes_regs executeState _ context
  simp [allocatorAfterContextStore, executeState, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, storedRegs, Std.ExtDHashMap.get?_insert]

theorem allocatorAfterContextStore_code (state : State)
    (retired stackBase context : BitVec 64)
    (notFileBacked : ∀ index : Fin 8,
      Artifacts.programImage.readFileByte?
        ((stackBase + sign_extend (0x010#12)).toNat + index.val) = none)
    (code : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    Artifacts.programImage.fileBytesMatchMemory
      (allocatorAfterContextStore state retired stackBase context).mem := by
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10300)
  have executeCode : Artifacts.programImage.fileBytesMatchMemory executeState.mem := by
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code
  have stored := fileBytesMatchMemory_afterWriteBytes Artifacts.programImage executeState
    (stackBase + sign_extend (0x010#12)).toNat context notFileBacked executeCode
  simpa [allocatorAfterContextStore, executeState, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick] using stored

theorem allocatorAfterContextStore_exitPlatform {state : State}
    {retired stackBase context : BitVec 64} {pc : Nat}
    (notFileBacked : ∀ index : Fin 8,
      Artifacts.programImage.readFileByte?
        ((stackBase + sign_extend (0x010#12)).toNat + index.val) = none)
    (platform : ExitPlatform state pc) :
    ExitPlatform (allocatorAfterContextStore state retired stackBase context) pc :=
  exitPlatform_of_agree (allocatorAfterContextStore_agree state retired stackBase context)
    (allocatorAfterContextStore_retired state retired stackBase context)
    (allocatorAfterContextStore_code state retired stackBase context notFileBacked platform.code)
    platform

/-- Exact state after the allocator's outgoing edge stores its function pointer. -/
def allocatorAfterFunctionStore (state : State) (retired stackBase functionAddress : BitVec 64) :
    State :=
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10304)
  let target := stackBase + sign_extend (0x018#12)
  tryStepControlFlowAfterRetired
    (afterWriteBytes (width := 8) executeState target.toNat functionAddress)
    (BitVec.ofNat 64 0x10308) retired

theorem allocatorAfterFunctionStore_pc (state : State)
    (retired stackBase functionAddress : BitVec 64) :
    (allocatorAfterFunctionStore state retired stackBase functionAddress).regs.get? PC =
      some (BitVec.ofNat 64 0x10308) := by
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10304)
  have storedRegs :
      (afterWriteBytes (width := 8) executeState
        (stackBase + sign_extend (0x018#12)).toNat functionAddress).regs = executeState.regs :=
    afterWriteBytes_regs executeState _ functionAddress
  simp [allocatorAfterFunctionStore, executeState, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, storedRegs, Std.ExtDHashMap.get?_insert]

/-! ## Boundary-facing allocator summary

The allocator has two entries, so its Level 2 summary is a relation over one machine-code segment,
not a callable-function contract. The first segment has no body steps: its only instruction is the
checked outgoing edge at `0x102f0`, which `InlineTransfer` retires. The second segment contains the
three instructions at `0x102f8`, `0x102fc`, and `0x10300`; its outgoing store at `0x10304` is again
retired by `InlineTransfer`.
-/

/-- The machine execution owned by one allocator segment before its checked outgoing edge. -/
inductive AllocatorSegmentExecution : Nat → Nat → State → State → Prop where
  /-- The first allocator segment stops immediately on its outgoing instruction at `0x102f0`. -/
  | dataPointer (fromStep : Nat) (state : State) :
      AllocatorSegmentExecution fromStep 0 state state
  /-- The second allocator segment retires its three body instructions and stops at `0x10304`. -/
  | functionAndContext (fromStep : Nat) (entry afterPage afterAddress atOutgoingEdge : State)
      (pageStep : Runs (try_step fromStep false) entry afterPage false)
      (addressStep : Runs (try_step (fromStep + 1) false) afterPage afterAddress false)
      (contextStep : Runs (try_step (fromStep + 2) false) afterAddress atOutgoingEdge false) :
      AllocatorSegmentExecution fromStep 3 entry atOutgoingEdge

/-- The child-summary relation consumed by the wrapper's allocator `InlineTransfer`s. It recognizes
only the selected generated allocator instance and exposes the exact Sail execution of either legal
machine-code segment. -/
def allocatorChildSummary (child : Binary.Elfling.FunctionInstanceId)
    (fromStep used : Nat) (before after : State) : Prop :=
  child =
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41Id ∧
    AllocatorSegmentExecution fromStep used before after

theorem allocatorChildSummary_dataPointer (fromStep : Nat) (state : State) :
    allocatorChildSummary
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41Id
      fromStep 0 state state := by
  exact ⟨rfl, .dataPointer fromStep state⟩

theorem allocatorChildSummary_functionAndContext (fromStep : Nat)
    (entry afterPage afterAddress atOutgoingEdge : State)
    (pageStep : Runs (try_step fromStep false) entry afterPage false)
    (addressStep : Runs (try_step (fromStep + 1) false) afterPage afterAddress false)
    (contextStep : Runs (try_step (fromStep + 2) false) afterAddress atOutgoingEdge false) :
    allocatorChildSummary
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41Id
      fromStep 3 entry atOutgoingEdge := by
  exact ⟨rfl, .functionAndContext fromStep entry afterPage afterAddress atOutgoingEdge
    pageStep addressStep contextStep⟩

/-- Fetch addresses whose platform premises are needed to execute the second allocator segment and
its outgoing edge. They are stated at the segment entry and transported across each proved step. -/
def allocatorSecondSegmentFetchPcs : List Nat := [0x102f8, 0x102fc, 0x10300, 0x10304]

/-- The non-control-flow facts at the second allocator entry. These are properties of the wrapper's
live stack object and machine environment, not a function-call ABI. -/
structure AllocatorSecondSegmentPreconditions (entry : State)
    (stackBase context : BitVec 64) where
  atEntry : entry.regs.get? PC = some (BitVec.ofNat 64 0x102f8)
  platform : ∀ pc ∈ allocatorSecondSegmentFetchPcs, ExitPlatform entry pc
  stackValue : entry.regs.get? x2 = some stackBase
  contextValue : entry.regs.get? x11 = some context
  mstatusBits : BitVec 64
  mstatusRead : entry.regs.get? mstatus = some mstatusBits
  mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1
  mseccfgBits : BitVec 64
  mseccfgRead : entry.regs.get? mseccfg = some mseccfgBits
  pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled
  contextStoreAllowed : StorePmaAllows entry (stackBase + sign_extend (0x010#12)) 8
  functionStoreAllowed : StorePmaAllows entry (stackBase + sign_extend (0x018#12)) 8
  contextAligned : is_aligned_vaddr
    (virtaddr.Virtaddr (stackBase + sign_extend (0x010#12))) 8 = true
  functionAligned : is_aligned_vaddr
    (virtaddr.Virtaddr (stackBase + sign_extend (0x018#12))) 8 = true
  contextBeforeClint : (stackBase + sign_extend (0x010#12)).toNat + 8 ≤
    BitVec.toNat plat_clint_base
  contextBeforeSig : (stackBase + sign_extend (0x010#12)).toNat + 8 ≤
    BitVec.toNat plat_sig_base
  functionBeforeClint : (stackBase + sign_extend (0x018#12)).toNat + 8 ≤
    BitVec.toNat plat_clint_base
  functionBeforeSig : (stackBase + sign_extend (0x018#12)).toNat + 8 ≤
    BitVec.toNat plat_sig_base
  contextStoreNotFileBacked : ∀ index : Fin 8,
    Artifacts.programImage.readFileByte?
      ((stackBase + sign_extend (0x010#12)).toNat + index.val) = none

theorem wrapper_allocator_tag_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102f4)
      0x23#8 0x00#8 0xa9#8 0x00#8 :=
  fetchFileInstruction state 0x102f4 0x23 0x00 0xa9 0x00 loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem wrapper_allocator_tag_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x23#8 0x00#8 0xa9#8 0x00#8)) state state
      (.STORE (0#12, .Regidx 10#5, .Regidx 18#5, 1)) := by
  decode_run

theorem allocator_function_page_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102f8)
      0x17#8 0x45#8 0x00#8 0x00#8 :=
  fetchFileInstruction state 0x102f8 0x17 0x45 0x00 0x00 loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem allocator_function_page_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x17#8 0x45#8 0x00#8 0x00#8)) state state
      (.UTYPE (0x00004#20, .Regidx 10#5, .AUIPC)) := by
  decode_run

theorem allocator_function_address_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102fc)
      0x13#8 0x05#8 0x85#8 0xc7#8 :=
  fetchFileInstruction state 0x102fc 0x13 0x05 0x85 0xc7 loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem allocator_function_address_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x85#8 0xc7#8)) state state
      (.ITYPE (0xc78#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) := by
  decode_run

theorem allocator_context_store_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10300)
      0x23#8 0x38#8 0xb1#8 0x00#8 :=
  fetchFileInstruction state 0x10300 0x23 0x38 0xb1 0x00 loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem allocator_context_store_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x23#8 0x38#8 0xb1#8 0x00#8)) state state
      (.STORE (0x010#12, .Regidx 11#5, .Regidx 2#5, 8)) := by
  decode_run

theorem allocator_function_store_fetch (state : State)
    (loaded : Artifacts.programImage.fileBytesMatchMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10304)
      0x23#8 0x3c#8 0xa1#8 0x00#8 :=
  fetchFileInstruction state 0x10304 0x23 0x3c 0xa1 0x00 loaded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)

theorem allocator_function_store_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x23#8 0x3c#8 0xa1#8 0x00#8)) state state
      (.STORE (0x018#12, .Regidx 10#5, .Regidx 2#5, 8)) := by
  decode_run

/-- The first allocator-attributed instruction executes through the generated Sail `try_step` and
lands on the wrapper-owned store at `0x102f4`. -/
theorem allocator_data_pointer_step (fromStep : Nat) (state : State)
    (platform : ExitPlatform state 0x102f0) (source : BitVec 64)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102f0))
    (sourceValue : state.regs.get? x18 = some source) :
    ∃ retired, Runs (try_step fromStep false) state
      (allocatorAfterDataPointer state retired source) false := by
  obtain ⟨seccfgBits, seccfgRead⟩ := platform.seccfgRead
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have privilegeIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := incrementNormal.2.1
  have seccfgIncrement :
      (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some seccfgBits :=
    (platformPreserved_mseccfg incrementAgree).trans seccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102f0)
  have sourceAtExecute : executeState.regs.get? x18 = some source := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, sourceValue]
  have execute : Runs
      (execute (.ITYPE (0x001#12, .Regidx 18#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (Sail.BitVec.addInt source 1) }
      (.Retire_Success ()) := by
    apply execute_ITYPE_run executeState _ 0x001#12 (.Regidx 18#5) (.Regidx 11#5) .ADDI source
    · exact rX_bits_run_x18 executeState source sourceAtExecute
    · simpa [iTypeResult] using
        (wX_bits_run_x11 executeState (Sail.BitVec.addInt source 1))
  simpa [allocatorAfterDataPointer, executeState] using
    fallThroughRegisterWriteStep fromStep 0x102f0 state 0x93#8 0x05#8 0x19#8 0x00#8
      (.ITYPE (0x001#12, .Regidx 18#5, .Regidx 11#5, .ADDI)) x11
      (Sail.BitVec.addInt source 1) atPc platform
      (allocator_data_pointer_fetch state platform.code) (by rfl)
      (allocator_data_pointer_decode _ privilegeIncrement seccfgBits seccfgIncrement) execute
      (fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide)

/-- The first allocator segment is discharged by Sail execution and packaged at the exact checked
inline boundary consumed by the wrapper's Level 2 scoped trace. -/
theorem allocator_data_pointer_inlineTransfer (fromStep : Nat) (state : State)
    (platform : ExitPlatform state 0x102f0) (source : BitVec 64)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102f0))
    (sourceValue : state.regs.get? x18 = some source) :
    ∃ retired,
      Nonempty (InlineTransfer
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        allocatorChildSummary allocatorInlineBoundary generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw
        functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
        fromStep 0 state (allocatorAfterDataPointer state retired source)) := by
  obtain ⟨retired, step⟩ := allocator_data_pointer_step fromStep state platform source atPc sourceValue
  refine ⟨retired, ⟨
    { valid := allocatorInlineBoundary_valid
      entryPc := BitVec.ofNat 64 0x102f0
      atEntry := atPc
      entryAccepted := ?_
      entryInRegion := ?_
      entryNotExit := ?_
      sExit := state
      body := allocatorChildSummary_dataPointer fromStep state
      exitEdge := ⟨0x102f0, 0x102f4⟩
      exitEdgeMem := ?_
      childExitPc := BitVec.ofNat 64 0x102f0
      atExit := atPc
      exitIsEdgeSource := by decide
      exitInRegion := ?_
      exitNotExit := ?_
      doExit := step
      resumePc := BitVec.ofNat 64 0x102f4
      atResume := ?_
      resumeIsEdgeTarget := by decide
      resumeInRegion := ?_ }⟩⟩
  · simp [allocatorInlineBoundary, InlineBoundary.acceptsEntry]
  · apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  · simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]
  · simp [allocatorInlineBoundary]
  · apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  · simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]
  · exact afterRegisterWrite_pc state (BitVec.ofNat 64 0x102f0) retired x11
      (Sail.BitVec.addInt source 1)
  · apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide

/-- The wrapper-owned `sb a0, 0(s2)` executes through generated Sail semantics and stores exactly
the low byte of `a0` at the address in `s2`. -/
theorem wrapper_allocator_tag_step (fromStep : Nat) (state : State)
    (platform : ExitPlatform state 0x102f4)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102f4))
    (target data mstatusBits mseccfgBits : BitVec 64)
    (targetValue : state.regs.get? x18 = some target)
    (dataValue : state.regs.get? x10 = some data)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (storeAllowed : StorePmaAllows state target 1)
    (beforeClint : target.toNat + 1 ≤ BitVec.toNat plat_clint_base)
    (beforeSig : target.toNat + 1 ≤ BitVec.toNat plat_sig_base) :
    ∃ retired, Runs (try_step fromStep false) state
      (wrapperAfterAllocatorTag state retired target data) false := by
  obtain ⟨hartRead, privilege, satpRead, midelegRead, mieRead, mipRead, pmpcfgRead,
    pmpaddrRead, inhibitRead, configRead, elpRead, misaCase⟩ := platform.normal
  obtain ⟨retired, retiredRead⟩ := platform.retired
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have fetchPlatform : FetchBasePlatform (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x102f4) :=
    fetchBasePlatform_of_offPC
      (pc_afterIncrement state (BitVec.ofNat 64 0x102f4) atPc)
      (fetchBasePlatformOffPC_of_normal incrementNormal
        ((platformPreserved_mstatus incrementAgree).trans mstatusRead) (by decide)
        (fetchPmaAllows_of_agree incrementAgree platform.pmaAllows))
  have fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x102f4) :=
    fetchMemoryNoMMIO_of_state_layout_excluded _ _
      ⟨fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide),
        (platformPreserved_htifBase incrementAgree).trans platform.htifRead⟩
  have interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state) :=
    interruptDisabled_of_normal incrementNormal
      ((platformPreserved_mstatus incrementAgree).trans mstatusRead)
      (platform.meipRead.imp fun _ read => (platformPreserved_sigMeip incrementAgree).trans read)
  have notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state) :=
    landingPadNotExpected_of_normal incrementNormal
  have privilegeIncrement := incrementNormal.2.1
  have seccfgIncrement := (platformPreserved_mseccfg incrementAgree).trans mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102f4)
  let afterExec : State :=
    { executeState with
      mem := executeState.mem.insert target.toNat (Sail.BitVec.extractLsb data 7 0) }
  have executeAgree : Agree platformPreserved state executeState :=
    agree_stepPremiseState state (BitVec.ofNat 64 0x102f4)
  have targetAtExecute : executeState.regs.get? x18 = some target := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, targetValue]
  have dataAtExecute : executeState.regs.get? x10 = some data := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, dataValue]
  have addressCalculation := get_transformed_data_addr_machine_store_run executeState
    (.Regidx 18#5) 1 target 0 mstatusBits mseccfgBits
    (rX_bits_run_x18 executeState target targetAtExecute)
    ((platformPreserved_mstatus executeAgree).trans mstatusRead)
    ((executeAgree cur_privilege (by simp [platformPreserved])).trans privilege)
    mprvZero ((platformPreserved_mseccfg executeAgree).trans mseccfgRead) pmmDisabled
  have physicalAccess := phys_access_check_machine_store_allowed executeState target 1
    (fetchPmpDisabled_of_agree executeAgree (fetchPmpDisabled_of_normal platform.normal))
    (storePmaAllows_of_agree executeAgree storeAllowed) (by simp [is_aligned_paddr])
  have storeNoMMIO := storeMemoryNoMMIO_of_state_layout_excluded executeState target 1
    (store_mmio_address_excluded_of_before_layout target 1 (by decide) beforeClint beforeSig)
    ((platformPreserved_htifBase executeAgree).trans platform.htifRead)
  have memoryWrite : Runs (PreSail.writeBytes (n := 1) target.toNat
      (Sail.BitVec.extractLsb data 7 0)) executeState afterExec true := by
    simpa [afterExec] using
      writeBytes_byte_run executeState target.toNat (Sail.BitVec.extractLsb data 7 0)
  have execute : Runs (execute (.STORE (0#12, .Regidx 10#5, .Regidx 18#5, 1)))
      executeState afterExec (.Retire_Success ()) :=
    execute_STORE_byte_run executeState afterExec (.Regidx 10#5) (.Regidx 18#5) 0#12
      target mstatusBits data ((platformPreserved_mstatus executeAgree).trans mstatusRead)
      ((executeAgree cur_privilege (by simp [platformPreserved])).trans privilege) mprvZero
      (rX_bits_run_x10 executeState data dataAtExecute) (by simpa using addressCalculation)
      physicalAccess storeNoMMIO memoryWrite
  refine ⟨retired, ?_⟩
  simpa [wrapperAfterAllocatorTag, executeState, afterExec] using
    tryStepFallThroughRetires fromStep state afterExec (BitVec.ofNat 64 0x102f4) retired 0 0
      0x23#8 0x00#8 0xa9#8 0x00#8 (.STORE (0#12, .Regidx 10#5, .Regidx 18#5, 1))
      fetchPlatform fetchNoMMIO (wrapper_allocator_tag_fetch state platform.code) interrupts
      (by rfl) (wrapper_allocator_tag_decode _ privilegeIncrement mseccfgBits seccfgIncrement)
      notExpected execute (by simp [afterExec, executeState, coreControlFlowNextState])
      (by simp [afterExec, executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by simp [afterExec, executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by simp [afterExec, executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert]) hartRead inhibitRead configRead
      (by decide) (by decide) retiredRead

/-- The allocator's second segment begins by materializing the page containing `allocatorAlloc`. -/
theorem allocator_function_page_step (fromStep : Nat) (state : State)
    (platform : ExitPlatform state 0x102f8)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102f8)) :
    ∃ retired, Runs (try_step fromStep false) state
      (allocatorAfterFunctionPage state retired) false := by
  obtain ⟨seccfgBits, seccfgRead⟩ := platform.seccfgRead
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have privilegeIncrement := incrementNormal.2.1
  have seccfgIncrement := (platformPreserved_mseccfg incrementAgree).trans seccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102f8)
  have corePc : executeState.regs.get? PC = some (BitVec.ofNat 64 0x102f8) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have auipcValue :
      BitVec.ofNat 64 0x102f8 + sign_extend (0x00004#20 ++ 0#12) =
        BitVec.ofNat 64 0x142f8 := by
    native_decide
  have execute : Runs (execute (.UTYPE (0x00004#20, .Regidx 10#5, .AUIPC))) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 0x142f8) }
      (.Retire_Success ()) := by
    apply execute_UTYPE_auipc_run executeState _ 0x00004#20 (.Regidx 10#5)
      (BitVec.ofNat 64 0x102f8)
    · exact readReg_run _ _ _ corePc
    · simpa [auipcValue] using wX_bits_run_x10 executeState (BitVec.ofNat 64 0x142f8)
  simpa [allocatorAfterFunctionPage, executeState] using
    fallThroughRegisterWriteStep fromStep 0x102f8 state 0x17#8 0x45#8 0x00#8 0x00#8
      (.UTYPE (0x00004#20, .Regidx 10#5, .AUIPC)) x10 (BitVec.ofNat 64 0x142f8)
      atPc platform (allocator_function_page_fetch state platform.code) (by rfl)
      (allocator_function_page_decode _ privilegeIncrement seccfgBits seccfgIncrement) execute
      (fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide)

/-- The second allocator body instruction resolves the exact vtable function pointer. -/
theorem allocator_function_address_step (fromStep : Nat) (state : State)
    (platform : ExitPlatform state 0x102fc)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102fc))
    (pageValue : state.regs.get? x10 = some (BitVec.ofNat 64 0x142f8)) :
    ∃ retired, Runs (try_step fromStep false) state
      (allocatorAfterFunctionAddress state retired) false := by
  obtain ⟨seccfgBits, seccfgRead⟩ := platform.seccfgRead
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have privilegeIncrement := incrementNormal.2.1
  have seccfgIncrement := (platformPreserved_mseccfg incrementAgree).trans seccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102fc)
  have sourceAtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 0x142f8) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pageValue]
  have resultValue :
      iTypeResult .ADDI 0xc78#12 (BitVec.ofNat 64 0x142f8) =
        BitVec.ofNat 64 0x13f70 := by
    native_decide
  have execute : Runs
      (execute (.ITYPE (0xc78#12, .Regidx 10#5, .Regidx 10#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 0x13f70) }
      (.Retire_Success ()) := by
    apply execute_ITYPE_run executeState _ 0xc78#12 (.Regidx 10#5) (.Regidx 10#5) .ADDI
      (BitVec.ofNat 64 0x142f8)
    · exact rX_bits_run_x10 executeState _ sourceAtExecute
    · simpa [resultValue] using wX_bits_run_x10 executeState (BitVec.ofNat 64 0x13f70)
  simpa [allocatorAfterFunctionAddress, executeState] using
    fallThroughRegisterWriteStep fromStep 0x102fc state 0x13#8 0x05#8 0x85#8 0xc7#8
      (.ITYPE (0xc78#12, .Regidx 10#5, .Regidx 10#5, .ADDI)) x10
      (BitVec.ofNat 64 0x13f70) atPc platform
      (allocator_function_address_fetch state platform.code) (by rfl)
      (allocator_function_address_decode _ privilegeIncrement seccfgBits seccfgIncrement) execute
      (fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide)) (by decide)
      (by decide) (by decide) (by decide) (by decide)

/-- The last instruction inside the allocator's second child-summary body stores its context
pointer at offset 16 of the stack allocator object and stops on the outgoing edge at `0x10304`. -/
theorem allocator_context_store_step (fromStep : Nat) (state : State)
    (platform : ExitPlatform state 0x10300)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10300))
    (stackBase context mstatusBits mseccfgBits : BitVec 64)
    (stackValue : state.regs.get? x2 = some stackBase)
    (contextValue : state.regs.get? x11 = some context)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (storeAllowed : StorePmaAllows state (stackBase + sign_extend (0x010#12)) 8)
    (aligned : is_aligned_vaddr
      (virtaddr.Virtaddr (stackBase + sign_extend (0x010#12))) 8 = true)
    (beforeClint : (stackBase + sign_extend (0x010#12)).toNat + 8 ≤
      BitVec.toNat plat_clint_base)
    (beforeSig : (stackBase + sign_extend (0x010#12)).toNat + 8 ≤
      BitVec.toNat plat_sig_base) :
    ∃ retired, Runs (try_step fromStep false) state
      (allocatorAfterContextStore state retired stackBase context) false := by
  let target := stackBase + sign_extend (0x010#12)
  obtain ⟨hartRead, privilege, satpRead, midelegRead, mieRead, mipRead, pmpcfgRead,
    pmpaddrRead, inhibitRead, configRead, elpRead, misaCase⟩ := platform.normal
  obtain ⟨retired, retiredRead⟩ := platform.retired
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have fetchPlatform : FetchBasePlatform (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10300) :=
    fetchBasePlatform_of_offPC
      (pc_afterIncrement state (BitVec.ofNat 64 0x10300) atPc)
      (fetchBasePlatformOffPC_of_normal incrementNormal
        ((platformPreserved_mstatus incrementAgree).trans mstatusRead) (by decide)
        (fetchPmaAllows_of_agree incrementAgree platform.pmaAllows))
  have fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10300) :=
    fetchMemoryNoMMIO_of_state_layout_excluded _ _
      ⟨fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide),
        (platformPreserved_htifBase incrementAgree).trans platform.htifRead⟩
  have interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state) :=
    interruptDisabled_of_normal incrementNormal
      ((platformPreserved_mstatus incrementAgree).trans mstatusRead)
      (platform.meipRead.imp fun _ read => (platformPreserved_sigMeip incrementAgree).trans read)
  have notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state) :=
    landingPadNotExpected_of_normal incrementNormal
  have privilegeIncrement := incrementNormal.2.1
  have seccfgIncrement := (platformPreserved_mseccfg incrementAgree).trans mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10300)
  let afterExec := afterWriteBytes (width := 8) executeState target.toNat context
  have executeAgree : Agree platformPreserved state executeState :=
    agree_stepPremiseState state (BitVec.ofNat 64 0x10300)
  have stackAtExecute : executeState.regs.get? x2 = some stackBase := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackValue]
  have contextAtExecute : executeState.regs.get? x11 = some context := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, contextValue]
  have addressCalculation := get_transformed_data_addr_machine_store_run executeState
    (.Regidx 2#5) 8 stackBase (sign_extend (0x010#12)) mstatusBits mseccfgBits
    (rX_bits_run_x2 executeState stackBase stackAtExecute)
    ((platformPreserved_mstatus executeAgree).trans mstatusRead)
    ((executeAgree cur_privilege (by simp [platformPreserved])).trans privilege)
    mprvZero ((platformPreserved_mseccfg executeAgree).trans mseccfgRead) pmmDisabled
  have physicalAccess := phys_access_check_machine_store_allowed executeState target 8
    (fetchPmpDisabled_of_agree executeAgree (fetchPmpDisabled_of_normal platform.normal))
    (storePmaAllows_of_agree executeAgree (by simpa [target] using storeAllowed))
    (by simpa [is_aligned_paddr, is_aligned_vaddr, target] using aligned)
  have storeNoMMIO := storeMemoryNoMMIO_of_state_layout_excluded executeState target 8
    (store_mmio_address_excluded_of_before_layout target 8 (by decide)
      (by simpa [target] using beforeClint) (by simpa [target] using beforeSig))
    ((platformPreserved_htifBase executeAgree).trans platform.htifRead)
  have memoryWrite : Runs (PreSail.writeBytes (n := 8) target.toNat context)
      executeState afterExec true := by
    simpa [afterExec] using
      writeBytes_run_exact (width := 8) executeState target.toNat context
  have execute : Runs
      (execute (.STORE (0x010#12, .Regidx 11#5, .Regidx 2#5, 8))) executeState afterExec
      (.Retire_Success ()) :=
    execute_STORE_dword_run executeState afterExec (.Regidx 11#5) (.Regidx 2#5) 0x010#12
      target mstatusBits context ((platformPreserved_mstatus executeAgree).trans mstatusRead)
      ((executeAgree cur_privilege (by simp [platformPreserved])).trans privilege) mprvZero
      (rX_bits_run_x11 executeState context contextAtExecute) (by simpa [target] using addressCalculation)
      (by simpa [target] using aligned) physicalAccess storeNoMMIO memoryWrite
  have afterExecRegs : afterExec.regs = executeState.regs := by
    simpa [afterExec] using afterWriteBytes_regs executeState target.toNat context
  refine ⟨retired, ?_⟩
  simpa [allocatorAfterContextStore, target, executeState, afterExec] using
    tryStepFallThroughRetires fromStep state afterExec (BitVec.ofNat 64 0x10300) retired 0 0
      0x23#8 0x38#8 0xb1#8 0x00#8 (.STORE (0x010#12, .Regidx 11#5, .Regidx 2#5, 8))
      fetchPlatform fetchNoMMIO (allocator_context_store_fetch state platform.code) interrupts
      (by rfl) (allocator_context_store_decode _ privilegeIncrement mseccfgBits seccfgIncrement)
      notExpected execute
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert]) hartRead inhibitRead configRead (by decide) (by decide)
      retiredRead

/-- The allocator's checked outgoing edge stores its function pointer at offset 24 and retires
directly into the selected `decode` region at `0x10308`. -/
theorem allocator_function_store_transfer (fromStep : Nat) (state : State)
    (platform : ExitPlatform state 0x10304)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10304))
    (stackBase functionAddress mstatusBits mseccfgBits : BitVec 64)
    (stackValue : state.regs.get? x2 = some stackBase)
    (functionValue : state.regs.get? x10 = some functionAddress)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (storeAllowed : StorePmaAllows state (stackBase + sign_extend (0x018#12)) 8)
    (aligned : is_aligned_vaddr
      (virtaddr.Virtaddr (stackBase + sign_extend (0x018#12))) 8 = true)
    (beforeClint : (stackBase + sign_extend (0x018#12)).toNat + 8 ≤
      BitVec.toNat plat_clint_base)
    (beforeSig : (stackBase + sign_extend (0x018#12)).toNat + 8 ≤
      BitVec.toNat plat_sig_base) :
    ∃ retired, Runs (try_step fromStep false) state
      (allocatorAfterFunctionStore state retired stackBase functionAddress) false := by
  let target := stackBase + sign_extend (0x018#12)
  obtain ⟨hartRead, privilege, satpRead, midelegRead, mieRead, mipRead, pmpcfgRead,
    pmpaddrRead, inhibitRead, configRead, elpRead, misaCase⟩ := platform.normal
  obtain ⟨retired, retiredRead⟩ := platform.retired
  have incrementAgree := agree_afterIncrement state
  have incrementNormal := normalExecutionState_of_platformPreserved incrementAgree platform.normal
  have fetchPlatform : FetchBasePlatform (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10304) :=
    fetchBasePlatform_of_offPC
      (pc_afterIncrement state (BitVec.ofNat 64 0x10304) atPc)
      (fetchBasePlatformOffPC_of_normal incrementNormal
        ((platformPreserved_mstatus incrementAgree).trans mstatusRead) (by decide)
        (fetchPmaAllows_of_agree incrementAgree platform.pmaAllows))
  have fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10304) :=
    fetchMemoryNoMMIO_of_state_layout_excluded _ _
      ⟨fetch_mmio_address_excluded_of_before_layout _ (by decide) (by decide),
        (platformPreserved_htifBase incrementAgree).trans platform.htifRead⟩
  have interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state) :=
    interruptDisabled_of_normal incrementNormal
      ((platformPreserved_mstatus incrementAgree).trans mstatusRead)
      (platform.meipRead.imp fun _ read => (platformPreserved_sigMeip incrementAgree).trans read)
  have notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state) :=
    landingPadNotExpected_of_normal incrementNormal
  have privilegeIncrement := incrementNormal.2.1
  have seccfgIncrement := (platformPreserved_mseccfg incrementAgree).trans mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10304)
  let afterExec := afterWriteBytes (width := 8) executeState target.toNat functionAddress
  have executeAgree : Agree platformPreserved state executeState :=
    agree_stepPremiseState state (BitVec.ofNat 64 0x10304)
  have stackAtExecute : executeState.regs.get? x2 = some stackBase := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackValue]
  have functionAtExecute : executeState.regs.get? x10 = some functionAddress := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, functionValue]
  have addressCalculation := get_transformed_data_addr_machine_store_run executeState
    (.Regidx 2#5) 8 stackBase (sign_extend (0x018#12)) mstatusBits mseccfgBits
    (rX_bits_run_x2 executeState stackBase stackAtExecute)
    ((platformPreserved_mstatus executeAgree).trans mstatusRead)
    ((executeAgree cur_privilege (by simp [platformPreserved])).trans privilege)
    mprvZero ((platformPreserved_mseccfg executeAgree).trans mseccfgRead) pmmDisabled
  have physicalAccess := phys_access_check_machine_store_allowed executeState target 8
    (fetchPmpDisabled_of_agree executeAgree (fetchPmpDisabled_of_normal platform.normal))
    (storePmaAllows_of_agree executeAgree (by simpa [target] using storeAllowed))
    (by simpa [is_aligned_paddr, is_aligned_vaddr, target] using aligned)
  have storeNoMMIO := storeMemoryNoMMIO_of_state_layout_excluded executeState target 8
    (store_mmio_address_excluded_of_before_layout target 8 (by decide)
      (by simpa [target] using beforeClint) (by simpa [target] using beforeSig))
    ((platformPreserved_htifBase executeAgree).trans platform.htifRead)
  have memoryWrite : Runs (PreSail.writeBytes (n := 8) target.toNat functionAddress)
      executeState afterExec true := by
    simpa [afterExec] using
      writeBytes_run_exact (width := 8) executeState target.toNat functionAddress
  have execute : Runs
      (execute (.STORE (0x018#12, .Regidx 10#5, .Regidx 2#5, 8))) executeState afterExec
      (.Retire_Success ()) :=
    execute_STORE_dword_run executeState afterExec (.Regidx 10#5) (.Regidx 2#5) 0x018#12
      target mstatusBits functionAddress
      ((platformPreserved_mstatus executeAgree).trans mstatusRead)
      ((executeAgree cur_privilege (by simp [platformPreserved])).trans privilege) mprvZero
      (rX_bits_run_x10 executeState functionAddress functionAtExecute)
      (by simpa [target] using addressCalculation) (by simpa [target] using aligned)
      physicalAccess storeNoMMIO memoryWrite
  have afterExecRegs : afterExec.regs = executeState.regs := by
    simpa [afterExec] using afterWriteBytes_regs executeState target.toNat functionAddress
  refine ⟨retired, ?_⟩
  simpa [allocatorAfterFunctionStore, target, executeState, afterExec] using
    tryStepFallThroughRetires fromStep state afterExec (BitVec.ofNat 64 0x10304) retired 0 0
      0x23#8 0x3c#8 0xa1#8 0x00#8 (.STORE (0x018#12, .Regidx 10#5, .Regidx 2#5, 8))
      fetchPlatform fetchNoMMIO (allocator_function_store_fetch state platform.code) interrupts
      (by rfl) (allocator_function_store_decode _ privilegeIncrement mseccfgBits seccfgIncrement)
      notExpected execute
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert])
      (by rw [afterExecRegs]; simp [executeState, coreControlFlowNextState,
        Std.ExtDHashMap.get?_insert]) hartRead inhibitRead configRead (by decide) (by decide)
      retiredRead

/-- Three Sail body steps plus the Sail outgoing store form the second checked allocator transfer.
This is the boundary-facing composition used by the Level 2 wrapper proof; the outgoing store is
not hidden in the child summary and is therefore counted exactly once. -/
theorem allocator_functionAndContext_inlineTransfer (fromStep : Nat)
    (entry afterPage afterAddress atOutgoingEdge afterTransfer : State)
    (atEntry : entry.regs.get? PC = some (BitVec.ofNat 64 0x102f8))
    (pageStep : Runs (try_step fromStep false) entry afterPage false)
    (addressStep : Runs (try_step (fromStep + 1) false) afterPage afterAddress false)
    (contextStep : Runs (try_step (fromStep + 2) false) afterAddress atOutgoingEdge false)
    (atOutgoingPc : atOutgoingEdge.regs.get? PC = some (BitVec.ofNat 64 0x10304))
    (outgoingStep : Runs (try_step (fromStep + 3) false) atOutgoingEdge afterTransfer false)
    (atDecode : afterTransfer.regs.get? PC = some (BitVec.ofNat 64 0x10308)) :
    Nonempty (InlineTransfer
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      allocatorChildSummary allocatorInlineBoundary generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
      fromStep 3 entry afterTransfer) := by
  refine ⟨
    { valid := allocatorInlineBoundary_valid
      entryPc := BitVec.ofNat 64 0x102f8
      atEntry := atEntry
      entryAccepted := ?_
      entryInRegion := ?_
      entryNotExit := ?_
      sExit := atOutgoingEdge
      body := allocatorChildSummary_functionAndContext fromStep entry afterPage afterAddress
        atOutgoingEdge pageStep addressStep contextStep
      exitEdge := ⟨0x10304, 0x10308⟩
      exitEdgeMem := ?_
      childExitPc := BitVec.ofNat 64 0x10304
      atExit := atOutgoingPc
      exitIsEdgeSource := by decide
      exitInRegion := ?_
      exitNotExit := ?_
      doExit := outgoingStep
      resumePc := BitVec.ofNat 64 0x10308
      atResume := atDecode
      resumeIsEdgeTarget := by decide
      resumeInRegion := ?_ }⟩
  · simp [allocatorInlineBoundary, InlineBoundary.acceptsEntry]
  · apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  · simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]
  · simp [allocatorInlineBoundary]
  · apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  · simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]
  · apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide

/-- The complete allocator setup as it appears in the wrapper trace: the first allocator splice,
the wrapper-owned tag store, and the second allocator splice. The result is a six-instruction
confined prefix ending at the checked `decode` entry. -/
theorem allocator_setup_prefix
    {childSummary : Binary.Elfling.FunctionInstanceId → Nat → Nat → State → State → Prop}
    (fromStep : Nat)
    (entry afterFirst afterTag afterDecode : State)
    (first : InlineTransfer
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      childSummary allocatorInlineBoundary generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
      fromStep 0 entry afterFirst)
    (atTag : afterFirst.regs.get? PC = some (BitVec.ofNat 64 0x102f4))
    (tagStep : Runs (try_step (fromStep + 1) false) afterFirst afterTag false)
    (second : InlineTransfer
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      childSummary allocatorInlineBoundary generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
      (fromStep + 2) 3 afterTag afterDecode) :
    ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      childSummary fromStep 6 entry afterDecode := by
  intro count final rest
  have restAtSecondExit : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      childSummary ((fromStep + 2) + 3 + 1) count afterDecode final := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest
  have afterSecond : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      childSummary (fromStep + 2) (3 + 1 + count) afterTag final :=
    ScopedTrace.inlineStep (fromStep + 2) 3 count allocatorInlineBoundary generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
      afterTag afterDecode final second restAtSecondExit
  have tagInRegion : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102f4) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have tagNotExit : ¬ functionInstanceExitPred
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x102f4) := by
    simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]
  have afterTagStep : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      childSummary (fromStep + 1) ((3 + 1 + count) + 1) afterFirst final := by
    apply ScopedTrace.ownStep (fromStep + 1) (3 + 1 + count)
      (BitVec.ofNat 64 0x102f4) afterFirst afterTag final atTag tagInRegion tagNotExit tagStep
    simpa only [Nat.add_assoc] using afterSecond
  have complete : ScopedTrace
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      childSummary fromStep (0 + 1 + ((3 + 1 + count) + 1)) entry final :=
    ScopedTrace.inlineStep fromStep 0 ((3 + 1 + count) + 1) allocatorInlineBoundary
      generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
      entry afterFirst final first (by simpa using afterTagStep)
  simpa only [Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using complete

/-- The second allocator condition is eliminated from its entry-state premises: all three body
instructions and the outgoing instruction execute through Sail and produce the checked Level 2
inline transfer. Intermediate platform and store-permission facts are transported from `entry`;
they are not assumed independently at invented states. -/
theorem allocator_second_segment_proved (fromStep : Nat) (entry : State)
    (stackBase context : BitVec 64)
    (pre : AllocatorSecondSegmentPreconditions entry stackBase context) :
    ∃ pageRetired addressRetired contextRetired functionRetired,
      Nonempty (InlineTransfer
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        allocatorChildSummary allocatorInlineBoundary generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw
        functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
        fromStep 3 entry
        (allocatorAfterFunctionStore
          (allocatorAfterContextStore
            (allocatorAfterFunctionAddress
              (allocatorAfterFunctionPage entry pageRetired) addressRetired)
            contextRetired stackBase context)
          functionRetired stackBase (BitVec.ofNat 64 0x13f70))) := by
  obtain ⟨pageRetired, pageStep⟩ := allocator_function_page_step fromStep entry
    (pre.platform 0x102f8 (by simp [allocatorSecondSegmentFetchPcs])) pre.atEntry
  let afterPage := allocatorAfterFunctionPage entry pageRetired
  have pageAgree : Agree platformPreserved entry afterPage :=
    afterRegisterWrite_agree (destination := x10) (by simp [platformPreserved])
  have pagePlatform (pc : Nat) (member : pc ∈ allocatorSecondSegmentFetchPcs) :
      ExitPlatform afterPage pc := by
    exact exitPlatform_of_agree pageAgree
      (afterRegisterWrite_retired_present entry (BitVec.ofNat 64 0x102f8) pageRetired x10
        (BitVec.ofNat 64 0x142f8))
      (by simpa [afterPage, allocatorAfterFunctionPage, afterRegisterWrite_mem] using
        (pre.platform pc member).code)
      (pre.platform pc member)
  have pagePc : afterPage.regs.get? PC = some (BitVec.ofNat 64 0x102fc) := by
    simpa [afterPage, allocatorAfterFunctionPage] using
      afterRegisterWrite_pc entry (BitVec.ofNat 64 0x102f8) pageRetired x10
        (BitVec.ofNat 64 0x142f8)
  have pageValue : afterPage.regs.get? x10 = some (BitVec.ofNat 64 0x142f8) := by
    simp [afterPage, allocatorAfterFunctionPage, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨addressRetired, addressStep⟩ := allocator_function_address_step (fromStep + 1)
    afterPage (pagePlatform 0x102fc (by simp [allocatorSecondSegmentFetchPcs])) pagePc pageValue
  let afterAddress := allocatorAfterFunctionAddress afterPage addressRetired
  have addressAgree : Agree platformPreserved entry afterAddress := pageAgree.trans
    (afterRegisterWrite_agree (destination := x10) (by simp [platformPreserved]))
  have addressPlatform (pc : Nat) (member : pc ∈ allocatorSecondSegmentFetchPcs) :
      ExitPlatform afterAddress pc := by
    exact exitPlatform_of_agree addressAgree
      (afterRegisterWrite_retired_present afterPage (BitVec.ofNat 64 0x102fc) addressRetired x10
        (BitVec.ofNat 64 0x13f70))
      (by simpa [afterAddress, allocatorAfterFunctionAddress, afterPage,
          allocatorAfterFunctionPage, afterRegisterWrite_mem] using
        (pre.platform pc member).code)
      (pre.platform pc member)
  have addressPc : afterAddress.regs.get? PC = some (BitVec.ofNat 64 0x10300) := by
    simpa [afterAddress, allocatorAfterFunctionAddress] using
      afterRegisterWrite_pc afterPage (BitVec.ofNat 64 0x102fc) addressRetired x10
        (BitVec.ofNat 64 0x13f70)
  have addressFunction : afterAddress.regs.get? x10 = some (BitVec.ofNat 64 0x13f70) := by
    simp [afterAddress, allocatorAfterFunctionAddress, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have addressStack : afterAddress.regs.get? x2 = some stackBase := by
    simp [afterAddress, allocatorAfterFunctionAddress, afterPage, allocatorAfterFunctionPage,
      afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      pre.stackValue]
  have addressContext : afterAddress.regs.get? x11 = some context := by
    simp [afterAddress, allocatorAfterFunctionAddress, afterPage, allocatorAfterFunctionPage,
      afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      pre.contextValue]
  obtain ⟨contextRetired, contextStep⟩ := allocator_context_store_step (fromStep + 2)
    afterAddress (addressPlatform 0x10300 (by simp [allocatorSecondSegmentFetchPcs])) addressPc
    stackBase context pre.mstatusBits pre.mseccfgBits addressStack addressContext
    ((platformPreserved_mstatus addressAgree).trans pre.mstatusRead) pre.mprvZero
    ((platformPreserved_mseccfg addressAgree).trans pre.mseccfgRead) pre.pmmDisabled
    (storePmaAllows_of_agree addressAgree pre.contextStoreAllowed) pre.contextAligned
    pre.contextBeforeClint pre.contextBeforeSig
  let atOutgoingEdge := allocatorAfterContextStore afterAddress contextRetired stackBase context
  have contextAgree : Agree platformPreserved entry atOutgoingEdge := addressAgree.trans
    (allocatorAfterContextStore_agree afterAddress contextRetired stackBase context)
  have outgoingPlatform : ExitPlatform atOutgoingEdge 0x10304 :=
    allocatorAfterContextStore_exitPlatform pre.contextStoreNotFileBacked
      (addressPlatform 0x10304 (by simp [allocatorSecondSegmentFetchPcs]))
  have outgoingPc : atOutgoingEdge.regs.get? PC = some (BitVec.ofNat 64 0x10304) := by
    exact allocatorAfterContextStore_pc afterAddress contextRetired stackBase context
  have outgoingStack : atOutgoingEdge.regs.get? x2 = some stackBase := by
    exact (allocatorAfterContextStore_get?_of_ne afterAddress contextRetired stackBase context x2
      (by decide) (by decide) (by decide) (by decide)).trans addressStack
  have outgoingFunction : atOutgoingEdge.regs.get? x10 =
      some (BitVec.ofNat 64 0x13f70) := by
    exact (allocatorAfterContextStore_get?_of_ne afterAddress contextRetired stackBase context x10
      (by decide) (by decide) (by decide) (by decide)).trans addressFunction
  obtain ⟨functionRetired, outgoingStep⟩ := allocator_function_store_transfer (fromStep + 3)
    atOutgoingEdge outgoingPlatform outgoingPc stackBase (BitVec.ofNat 64 0x13f70)
    pre.mstatusBits pre.mseccfgBits outgoingStack outgoingFunction
    ((platformPreserved_mstatus contextAgree).trans pre.mstatusRead) pre.mprvZero
    ((platformPreserved_mseccfg contextAgree).trans pre.mseccfgRead) pre.pmmDisabled
    (storePmaAllows_of_agree contextAgree pre.functionStoreAllowed) pre.functionAligned
    pre.functionBeforeClint pre.functionBeforeSig
  let afterTransfer := allocatorAfterFunctionStore atOutgoingEdge functionRetired stackBase
    (BitVec.ofNat 64 0x13f70)
  have decodePc : afterTransfer.regs.get? PC = some (BitVec.ofNat 64 0x10308) := by
    exact allocatorAfterFunctionStore_pc atOutgoingEdge functionRetired stackBase
      (BitVec.ofNat 64 0x13f70)
  refine ⟨pageRetired, addressRetired, contextRetired, functionRetired, ?_⟩
  simpa [afterPage, afterAddress, atOutgoingEdge, afterTransfer] using
    allocator_functionAndContext_inlineTransfer fromStep entry afterPage afterAddress
      atOutgoingEdge afterTransfer pre.atEntry pageStep addressStep contextStep outgoingPc
      outgoingStep decodePc

end BinaryFv.Zesu.MachineExecution
