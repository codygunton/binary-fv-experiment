import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.GeneratedWordStep
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.Zesu.MachineExecution.Level2WrapperSteps
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.MachineExecution.OwnedPc

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
open RegisterWriteStep GeneratedWordStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The concrete eight-byte store writes precisely the little-endian representation used by the
saved-frame interface. -/
private theorem wrapperAfterDwordStore_savedWord (state : State) (pc retired target data : BitVec 64)
    (base : Nat) (targetValue : target.toNat = base) :
    SavedWordBytes (wrapperAfterDwordStore state pc retired target data) base data := by
  intro index bound
  rw [BinaryFv.RiscV.Sep.leBytes_length] at bound
  have indexCases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 := by omega
  rcases indexCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [wrapperAfterDwordStore, afterWriteBytes, afterByteWrites, targetValue,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem_insert,
      BinaryFv.RiscV.Sep.leBytes, BinaryFv.RiscV.Sep.leBytes_length] <;> omega

private theorem wrapperAfterDwordStore_preserves_savedWord (state : State)
    (pc retired target data : BitVec 64) (targetBase savedBase : Nat) (value : BitVec 64)
    (targetValue : target.toNat = targetBase)
    (disjoint : targetBase + 8 ≤ savedBase ∨ savedBase + 8 ≤ targetBase)
    (saved : SavedWordBytes state savedBase value) :
    SavedWordBytes (wrapperAfterDwordStore state pc retired target data) savedBase value := by
  intro index bound
  rw [BinaryFv.RiscV.Sep.leBytes_length] at bound
  refine (storeRetirement_mem_writes state pc (Sail.BitVec.addInt pc 4) retired target.toNat data
    (savedBase + index) ?_).trans (saved index bound)
  rintro ⟨lower, upper⟩
  rw [targetValue] at lower upper
  rcases disjoint with left | right <;> omega

/-- An eight-byte allocator-object store below the wrapper save area leaves all four saved words
unchanged. The separation is the actual emitted object layout. -/
private theorem wrapperAfterDwordStore_preserves_savedFrame (state : State)
    (pc retired target data : BitVec 64) (stackBase targetBase : Nat)
    (targetValue : target.toNat = targetBase) (targetBeforeSaveArea : targetBase + 8 ≤ stackBase + 0xa00)
    {link s0 s1 s2 : BitVec 64}
    (frame : WrapperSavedRegisterFrame stackBase link s0 s1 s2 state) :
    WrapperSavedRegisterFrame stackBase link s0 s1 s2
      (wrapperAfterDwordStore state pc retired target data) := by
  rw [WrapperSavedRegisterFrame] at frame ⊢
  rcases frame with ⟨linkFrame, s0Frame, s1Frame, s2Frame⟩
  exact ⟨
    wrapperAfterDwordStore_preserves_savedWord state pc retired target data targetBase
      (stackBase + 0xa18) link targetValue (Or.inl (by omega)) linkFrame,
    wrapperAfterDwordStore_preserves_savedWord state pc retired target data targetBase
      (stackBase + 0xa10) s0 targetValue (Or.inl (by omega)) s0Frame,
    wrapperAfterDwordStore_preserves_savedWord state pc retired target data targetBase
      (stackBase + 0xa08) s1 targetValue (Or.inl (by omega)) s1Frame,
    wrapperAfterDwordStore_preserves_savedWord state pc retired target data targetBase
      (stackBase + 0xa00) s2 targetValue (Or.inl targetBeforeSaveArea) s2Frame⟩

/-- The one-byte attempted-tag store is below the canonical wrapper stack and cannot overwrite a
saved register word. -/
private theorem wrapperAfterAllocatorTag_preserves_savedFrame (state : State)
    (retired target data : BitVec 64) (stackBase : Nat)
    (targetBeforeSaveArea : target.toNat + 1 ≤ stackBase + 0xa00)
    {link s0 s1 s2 : BitVec 64}
    (frame : WrapperSavedRegisterFrame stackBase link s0 s1 s2 state) :
    WrapperSavedRegisterFrame stackBase link s0 s1 s2
      (wrapperAfterAllocatorTag state retired target data) := by
  rw [WrapperSavedRegisterFrame] at frame ⊢
  rcases frame with ⟨linkFrame, s0Frame, s1Frame, s2Frame⟩
  have preserve (base : Nat) (baseInSaveArea : stackBase + 0xa00 ≤ base)
      (value : BitVec 64) (saved : SavedWordBytes state base value) :
      SavedWordBytes (wrapperAfterAllocatorTag state retired target data) base value := by
    intro index bound
    have indexLt : index < 8 := by
      simpa [BinaryFv.RiscV.Sep.leBytes_length] using bound
    have outside : target.toNat ≠ base + index := by omega
    change (state.mem.insert target.toNat (Sail.BitVec.extractLsb data 7 0)).get? (base + index) =
      some (getElem (BinaryFv.RiscV.Sep.leBytes 8 value) index bound)
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg outside]
    exact saved index bound
  exact ⟨preserve (stackBase + 0xa18) (by omega) link linkFrame,
    preserve (stackBase + 0xa10) (by omega) s0 s0Frame,
    preserve (stackBase + 0xa08) (by omega) s1 s1Frame,
    preserve (stackBase + 0xa00) (by omega) s2 s2Frame⟩

/-- A wrapper stack store preserves the borrowed input because the compiled entry premise keeps the
entire input interval outside the writable frame. -/
private theorem wrapperAfterDwordStore_inputMemory (args : ZesuDecodeRawArgs) (stackBase : Nat)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (state : State) (pc retired target data : BitVec 64) (targetAddress : Nat)
    (targetValue : target.toNat = targetAddress) (targetInFrame : stackBase ≤ targetAddress)
    (targetEnd : targetAddress + 8 ≤ stackBase + 0xa20)
    (inputMemory : DecodedValue.MemoryBytes state args.inputBase args.bytes) :
    DecodedValue.MemoryBytes
      (wrapperAfterDwordStore state pc retired target data) args.inputBase args.bytes := by
  apply inputMemory.of_mem_eq
  intro inputIndex inputBound
  refine storeRetirement_mem_writes state pc (Sail.BitVec.addInt pc 4) retired target.toNat data
    (args.inputBase + inputIndex) ?_
  rintro ⟨lower, upper⟩
  rw [targetValue] at lower upper
  rcases machine.inputAvoidsStack with inputBefore | stackBeforeInput <;> omega

/-- Execute the wrapper-owned allocator-tag byte store from the configured decoder machine. The
store permission comes from `DecoderDataAccess`, not from a runner-specific return bundle. -/
theorem wrapper_allocator_tag_step_configured {instructionPcs : BitVec 64 → Prop}
    {machineArgs : DecoderMachineArgs} {baseState state : State}
    (machine : DecoderMachinePre instructionPcs machineArgs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state) (code : canonicalContractParams.env.CodeIntact state)
    (stepNo : Nat) (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 0x102f4))
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102f4))
    (target data : BitVec 64) (targetValue : state.regs.get? x18 = some target)
    (dataValue : state.regs.get? x10 = some data)
    (allowed : DecoderAccessRange DecoderWritableByte target 1) :
    ∃ retired, Runs (try_step stepNo false) state
      (wrapperAfterAllocatorTag state retired target data) false := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContextOfDecoderAgree machine agree
  obtain ⟨retired, run⟩ := decoderStoreByteStep machine agree retiredPresent
    (by exact Contracts.canonicalCodeIntact_image code)
    stepNo 0x102f4 0x23 0x00 0xa9 0x00 (0#12) 10#5 18#5 target data target atPc
    (rX_bits_run_x18 _ target (decoderExecuteState_get? targetValue))
    (rX_bits_run_x10 _ data (decoderExecuteState_get? dataValue))
    (by simp [show sign_extend (m := 64) (0#12) = (0#64) from by decide]) allowed
  exact ⟨retired, by
    simpa [wrapperAfterAllocatorTag, afterMemoryWrite, afterWriteBytes, afterByteWrites,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      show Sail.BitVec.addInt (BitVec.ofNat 64 0x102f4) 4 = BitVec.ofNat 64 0x102f8 from by decide]
      using run⟩

/-- Instantiate the shared store theorem at an aligned offset in the declared wrapper stack frame. -/
theorem wrapper_stack_store_step (args : ZesuDecodeRawArgs) (stackBase : Nat)
    (entry state : State) (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree decoderPreserved entry state) (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc : BitVec 64)
    (pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw) pc)
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
  refine storeRetirement_mem_writes state pc (Sail.BitVec.addInt pc 4) retired
    (BitVec.ofNat 64 (stackBase + offset)).toNat data 0x4215020 ?_
  rintro ⟨lower, upper⟩
  rw [targetToNat] at lower upper
  refine attemptedNotStack ?_
  have stack := machine.stackFrameWritable (offset + (0x4215020 - (stackBase + offset))) (by omega)
  have address : stackBase + (offset + (0x4215020 - (stackBase + offset))) = 0x4215020 := by omega
  exact address ▸ stack

/-- A stack-frame store preserves a decoder-global byte once that byte is known to be outside the
canonical stack. -/
private theorem wrapperAfterStackStore_preserves_byte (args : ZesuDecodeRawArgs) (stackBase offset : Nat)
    (entry state : State) (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (offsetEnd : offset + 8 ≤ 0xa20) (pc retired data : BitVec 64) (address : Nat)
    (outsideStack : ¬ canonicalContractParams.env.stack address) :
    (wrapperAfterDwordStore state pc retired (BitVec.ofNat 64 (stackBase + offset)) data).mem.get?
        address = state.mem.get? address := by
  have wordSize : 2 ^ 64 = 18446744073709551616 := by native_decide
  have frameFits := machine.stackFrameFits
  rw [wordSize] at frameFits
  have targetToNat : (BitVec.ofNat 64 (stackBase + offset)).toNat = stackBase + offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine storeRetirement_mem_writes state pc (Sail.BitVec.addInt pc 4) retired
    (BitVec.ofNat 64 (stackBase + offset)).toNat data address ?_
  rintro ⟨lower, upper⟩
  rw [targetToNat] at lower upper
  refine outsideStack ?_
  have stack := machine.stackFrameWritable (offset + (address - (stackBase + offset))) (by omega)
  have addressEq : stackBase + (offset + (address - (stackBase + offset))) = address := by omega
  exact addressEq ▸ stack

/-- The wrapper's first owned instruction executes through Sail from the compiled Level 2 entry.
The result is stated using Sail's `iTypeResult`; the prologue composition later reduces it to the
intermediate stack pointer `stackBase + 0x230`. -/
theorem wrapper_first_frame_decrement_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (state : State) (source : preZesuDecodeRaw canonicalContractParams.env
      canonicalContractParams.globals canonicalContractParams.resultBuffer
      canonicalContractParams.repStatelessInput DecoderGlobalsModel.fresh args state)
    (machine : ZesuDecodeRawMachinePre args stackBase state) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (wrapperAfterFirstFrameDecrement state retired
          (BitVec.ofNat 64 (stackBase + 0xa20))) false ∧
      (wrapperAfterFirstFrameDecrement state retired
          (BitVec.ofNat 64 (stackBase + 0xa20))).regs.get? x2 =
        some (BitVec.ofNat 64 (stackBase + 0x230)) := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContext machine.machine (Agree.refl state)
  obtain ⟨retired, run⟩ := decoderITypeStep machine.machine (Agree.refl state)
    machine.machine.retiredCounter
    (by simpa [canonicalContractParams, canonicalEnvironment] using source.2.1)
    stepNo 0x102b0 0x13 0x01 0x01 0x81 0x810#12 2#5 2#5 .ADDI machine.atEntry
    (rX_x2_run _ _ (decoderExecuteState_get? machine.stackAtEntry)) (wX_x2_run _ _)
  refine ⟨retired, run, ?_⟩
  rw [← wrapper_first_frame_decrement_value stackBase machine.stackFrameFits]
  exact afterRegisterWrite_destination state (BitVec.ofNat 64 0x102b0) retired x2
    (iTypeResult .ADDI 0x810#12 (BitVec.ofNat 64 (stackBase + 0xa20))) (by decide) (by decide)

/-! ## Saved return address -/

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
  have storedAtExecute : executeState.regs.get? x8 = some value :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x102b8)).get x8 (by decide)).trans stored
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ :=
    wrapper_decode_machine_state entry state machine.machine agree
  apply wrapper_stack_store_step args stackBase entry state machine agree retired stepNo
    (BitVec.ofNat 64 0x102b8)
    (fetchPc _)
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
  have storedAtExecute : executeState.regs.get? x9 = some value :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x102bc)).get x9 (by decide)).trans stored
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ :=
    wrapper_decode_machine_state entry state machine.machine agree
  apply wrapper_stack_store_step args stackBase entry state machine agree retired stepNo
    (BitVec.ofNat 64 0x102bc)
    (fetchPc _)
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
  have storedAtExecute : executeState.regs.get? x18 = some value :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x102c0)).get x18 (by decide)).trans stored
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ :=
    wrapper_decode_machine_state entry state machine.machine agree
  apply wrapper_stack_store_step args stackBase entry state machine agree retired stepNo
    (BitVec.ofNat 64 0x102c0)
    (fetchPc _)
    atPc 0x23#8 0x38#8 0x21#8 0x7d#8 0x7d0#12 (.Regidx 18#5) value 0xa00
    (by decide) (by decide) stack
    (rX_bits_run_x18 executeState value storedAtExecute) (wrapper_saved_s2_target stackBase)
    (wrapper_save_s2_fetch state code) (by unfold BaseInstructionEncoding; decide)
    (wrapper_save_s2_decode _ privilege mseccfgBits mseccfgRead)

/-- Execute `sd ra, 0x7e8(sp)` and retain the exact saved return-address bytes. -/
theorem wrapper_save_link_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) (frameRetired : BitVec 64) :
    ∃ link storeRetired,
      entry.regs.get? x1 = some link ∧
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
    rw [← wrapper_first_frame_decrement_value stackBase machine.stackFrameFits]
    exact afterRegisterWrite_destination entry (BitVec.ofNat 64 0x102b0) frameRetired x2
      (iTypeResult .ADDI 0x810#12 (BitVec.ofNat 64 (stackBase + 0xa20))) (by decide) (by decide)
  have stateLink : state.regs.get? x1 = some link :=
    ((afterRegisterWrite_writes entry (BitVec.ofNat 64 0x102b0) frameRetired x2
      (iTypeResult .ADDI 0x810#12 (BitVec.ofNat 64 (stackBase + 0xa20)))).get x1
        (by decide)).trans linkAtEntry
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
  have linkAtExecute : executeState.regs.get? x1 = some link :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x102b4)).get x1 (by decide)).trans stateLink
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
  obtain ⟨storeRetired, run⟩ := wrapper_dword_store_step machine.machine stateAgree stateRetired
    stepNo (BitVec.ofNat 64 0x102b4) (fetchPc _) statePc
    0x23#8 0x34#8 0x11#8 0x7e#8
    0x7e8#12 (.Regidx 1#5) (BitVec.ofNat 64 (stackBase + 0x230)) link
    (BitVec.ofNat 64 (stackBase + 0xa18)) stateStack dataRun
    (wrapper_saved_link_target stackBase) aligned allowed fetch
    (by unfold BaseInstructionEncoding; decide) decode
  exact ⟨link, storeRetired, linkAtEntry, by simpa [state] using run⟩

/-- The wrapper's own confined-prefix shape, named once so each step composition states it in a
line. As an `abbrev` it is reducible, so it *is* the spelled-out application. -/
private abbrev WrapperConfinedPrefix (fromStep used : Nat) (before after : State) : Prop :=
  ConfinedPrefix
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary fromStep used before after

/-- One wrapper-owned Sail step, packaged at the numeric-pc spelling every prefix proof in this
file uses. -/
private theorem wrapperOwnStep (stepNo pc : Nat) (before after : State)
    (atPc : before.regs.get? PC = some (BitVec.ofNat 64 pc))
    (inRegion : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 pc))
    (notExit : ¬ functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw
      (BitVec.ofNat 64 pc))
    (run : Runs (try_step stepNo false) before after false) :
    WrapperConfinedPrefix stepNo 1 before after :=
  ConfinedPrefix.ownStep atPc inRegion notExit run

/-- Sail executes the wrapper's frame decrement and all four saved-register stores. -/
theorem wrapper_entry_save_prefix (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
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
      final.mem.get? (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) =
        entry.mem.get? (canonicalContractParams.globals.storedResult +
          canonicalContractParams.globals.storedResultObject.discriminantOffset) ∧
      DecodedValue.MemoryBytes final args.inputBase args.bytes ∧
      Agree platformPreserved entry final ∧ Agree decodeRawCalleeSaved entry final ∧
      RetiredCounterPresent final ∧
      canonicalContractParams.env.CodeIntact final ∧
      ∃ link s0 s1 s2, entry.regs.get? x1 = some link ∧ entry.regs.get? x8 = some s0 ∧
        entry.regs.get? x9 = some s1 ∧ entry.regs.get? x18 = some s2 ∧
        WrapperSavedRegisterFrame stackBase link s0 s1 s2 final := by
  obtain ⟨frameRetired, frameRun, frameStackRaw⟩ :=
    wrapper_first_frame_decrement_step fromStep args stackBase entry source machine
  let frame := wrapperAfterFirstFrameDecrement entry frameRetired
    (BitVec.ofNat 64 (stackBase + 0xa20))
  obtain ⟨link, linkRetired, linkAtEntry, linkRun⟩ :=
    wrapper_save_link_step (fromStep + 1) args stackBase entry source machine frameRetired
  let afterLink := wrapperAfterDwordStore frame (BitVec.ofNat 64 0x102b4) linkRetired
    (BitVec.ofNat 64 (stackBase + 0xa18)) link
  -- The write set of each step, stated once. Every register carried forward below -- through one
  -- store or through all five -- is then a single `grind` against these facts and the value the
  -- register held at the last state that wrote it, whatever the register is.
  have wFrame : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x2)) entry frame :=
    afterRegisterWrite_writes entry (BitVec.ofNat 64 0x102b0) frameRetired x2
      (iTypeResult .ADDI 0x810#12 (BitVec.ofNat 64 (stackBase + 0xa20)))
  have wLink : WritesOnlyRegs stepBookkeeping frame afterLink :=
    wrapperAfterDwordStore_writes frame _ _ _ _
  have frameStack : frame.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)) := frameStackRaw
  have inputAtEntry : entry.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) := source.2.2.1
  have lengthAtEntry : entry.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size) :=
    source.2.2.2.1
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
  have frameCalleeSavedAgree : Agree decodeRawCalleeSaved entry frame := by
    exact afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved])
  have linkAgree : Agree decoderPreserved entry afterLink :=
    frameAgree.trans (wrapperAfterDwordStore_agree frame _ _ _ _)
  have linkPlatformAgree : Agree platformPreserved entry afterLink :=
    framePlatformAgree.trans (wrapperAfterDwordStore_platformAgree frame _ _ _ _)
  have linkCalleeSavedAgree : Agree decodeRawCalleeSaved entry afterLink :=
    frameCalleeSavedAgree.trans
      ((wrapperAfterDwordStore_writes frame _ _ _ _).agree decodeRawCalleeSaved_disjoint)
  have linkStack : afterLink.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)) := by grind
  have linkPc : afterLink.regs.get? PC = some (BitVec.ofNat 64 0x102b8) := by
    simpa [afterLink] using wrapperAfterDwordStore_pc frame (BitVec.ofNat 64 0x102b4)
      linkRetired (BitVec.ofNat 64 (stackBase + 0xa18)) link
  have linkCode : canonicalContractParams.env.CodeIntact afterLink := by
    apply wrapperAfterStackStore_code args stackBase 0xa18 entry frame machine (by decide)
    simpa [frame, wrapperAfterFirstFrameDecrement, afterRegisterWrite_mem] using source.2.1
  have linkRetiredPresent := wrapperAfterDwordStore_retired frame
    (BitVec.ofNat 64 0x102b4) linkRetired (BitVec.ofNat 64 (stackBase + 0xa18)) link
  obtain ⟨s0, savedS0⟩ := machine.savedS0AtEntry
  have s0AtLink : afterLink.regs.get? x8 = some s0 := by grind
  obtain ⟨s0Retired, s0Run⟩ := wrapper_save_s0_step (fromStep + 2) args stackBase entry
    afterLink machine linkAgree linkRetiredPresent linkCode linkPc linkStack s0 s0AtLink
  let afterS0 := wrapperAfterDwordStore afterLink (BitVec.ofNat 64 0x102b8) s0Retired
    (BitVec.ofNat 64 (stackBase + 0xa10)) s0
  have wS0 : WritesOnlyRegs stepBookkeeping afterLink afterS0 :=
    wrapperAfterDwordStore_writes afterLink _ _ _ _
  have s0Agree : Agree decoderPreserved entry afterS0 :=
    linkAgree.trans (wrapperAfterDwordStore_agree afterLink _ _ _ _)
  have s0PlatformAgree : Agree platformPreserved entry afterS0 :=
    linkPlatformAgree.trans (wrapperAfterDwordStore_platformAgree afterLink _ _ _ _)
  have s0CalleeSavedAgree : Agree decodeRawCalleeSaved entry afterS0 :=
    linkCalleeSavedAgree.trans
      ((wrapperAfterDwordStore_writes afterLink _ _ _ _).agree decodeRawCalleeSaved_disjoint)
  have s0Stack : afterS0.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)) := by grind
  have s0Pc : afterS0.regs.get? PC = some (BitVec.ofNat 64 0x102bc) := by
    simpa [afterS0] using wrapperAfterDwordStore_pc afterLink (BitVec.ofNat 64 0x102b8)
      s0Retired (BitVec.ofNat 64 (stackBase + 0xa10)) s0
  have s0Code : canonicalContractParams.env.CodeIntact afterS0 :=
    wrapperAfterStackStore_code args stackBase 0xa10 entry afterLink machine (by decide) _ _ _ linkCode
  have s0RetiredPresent := wrapperAfterDwordStore_retired afterLink
    (BitVec.ofNat 64 0x102b8) s0Retired (BitVec.ofNat 64 (stackBase + 0xa10)) s0
  obtain ⟨s1, savedS1⟩ := machine.savedS1AtEntry
  have s1AtS0 : afterS0.regs.get? x9 = some s1 := by grind
  obtain ⟨s1Retired, s1Run⟩ := wrapper_save_s1_step (fromStep + 3) args stackBase entry
    afterS0 machine s0Agree s0RetiredPresent s0Code s0Pc s0Stack s1 s1AtS0
  let afterS1 := wrapperAfterDwordStore afterS0 (BitVec.ofNat 64 0x102bc) s1Retired
    (BitVec.ofNat 64 (stackBase + 0xa08)) s1
  have wS1 : WritesOnlyRegs stepBookkeeping afterS0 afterS1 :=
    wrapperAfterDwordStore_writes afterS0 _ _ _ _
  have s1Agree : Agree decoderPreserved entry afterS1 :=
    s0Agree.trans (wrapperAfterDwordStore_agree afterS0 _ _ _ _)
  have s1PlatformAgree : Agree platformPreserved entry afterS1 :=
    s0PlatformAgree.trans (wrapperAfterDwordStore_platformAgree afterS0 _ _ _ _)
  have s1CalleeSavedAgree : Agree decodeRawCalleeSaved entry afterS1 :=
    s0CalleeSavedAgree.trans
      ((wrapperAfterDwordStore_writes afterS0 _ _ _ _).agree decodeRawCalleeSaved_disjoint)
  have s1Stack : afterS1.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)) := by grind
  have s1Pc : afterS1.regs.get? PC = some (BitVec.ofNat 64 0x102c0) := by
    simpa [afterS1] using wrapperAfterDwordStore_pc afterS0 (BitVec.ofNat 64 0x102bc)
      s1Retired (BitVec.ofNat 64 (stackBase + 0xa08)) s1
  have s1Code : canonicalContractParams.env.CodeIntact afterS1 :=
    wrapperAfterStackStore_code args stackBase 0xa08 entry afterS0 machine (by decide) _ _ _ s0Code
  have s1RetiredPresent := wrapperAfterDwordStore_retired afterS0
    (BitVec.ofNat 64 0x102bc) s1Retired (BitVec.ofNat 64 (stackBase + 0xa08)) s1
  obtain ⟨s2, savedS2⟩ := machine.savedS2AtEntry
  have s2AtS1 : afterS1.regs.get? x18 = some s2 := by grind
  obtain ⟨s2Retired, s2Run⟩ := wrapper_save_s2_step (fromStep + 4) args stackBase entry
    afterS1 machine s1Agree s1RetiredPresent s1Code s1Pc s1Stack s2 s2AtS1
  let final := wrapperAfterDwordStore afterS1 (BitVec.ofNat 64 0x102c0) s2Retired
    (BitVec.ofNat 64 (stackBase + 0xa00)) s2
  have wFinal : WritesOnlyRegs stepBookkeeping afterS1 final :=
    wrapperAfterDwordStore_writes afterS1 _ _ _ _
  have finalAgree : Agree decoderPreserved entry final :=
    s1Agree.trans (wrapperAfterDwordStore_agree afterS1 _ _ _ _)
  have finalPlatformAgree : Agree platformPreserved entry final :=
    s1PlatformAgree.trans (wrapperAfterDwordStore_platformAgree afterS1 _ _ _ _)
  have finalCalleeSavedAgree : Agree decodeRawCalleeSaved entry final :=
    s1CalleeSavedAgree.trans
      ((wrapperAfterDwordStore_writes afterS1 _ _ _ _).agree decodeRawCalleeSaved_disjoint)
  -- Three registers, across up to five steps, in one `grind`: `x2` back to the frame decrement
  -- that set it, `x10` and `x11` all the way back to `entry`.
  obtain ⟨finalStack, finalInput, finalLength⟩ :
      final.regs.get? x2 = some (BitVec.ofNat 64 (stackBase + 0x230)) ∧
      final.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) ∧
      final.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size) := by grind
  have finalPc : final.regs.get? PC = some (BitVec.ofNat 64 0x102c4) := by
    simpa [final] using wrapperAfterDwordStore_pc afterS1 (BitVec.ofNat 64 0x102c0)
      s2Retired (BitVec.ofNat 64 (stackBase + 0xa00)) s2
  have finalCode : canonicalContractParams.env.CodeIntact final :=
    wrapperAfterStackStore_code args stackBase 0xa00 entry afterS1 machine (by decide) _ _ _ s1Code
  have finalRetired := wrapperAfterDwordStore_retired afterS1
    (BitVec.ofNat 64 0x102c0) s2Retired (BitVec.ofNat 64 (stackBase + 0xa00)) s2
  have frameFits := machine.stackFrameFits
  -- Every slot this proof stores to lies inside the wrapper's own frame, so its address literal
  -- reads back as the plain sum. Stated once, it discharges all fourteen `targetValue` premises.
  have offsetToNat : ∀ offset : Nat, offset + 8 ≤ 0xa20 →
      (BitVec.ofNat 64 (stackBase + offset)).toNat = stackBase + offset := by
    intro offset bound
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have linkBytes : SavedWordBytes afterLink (stackBase + 0xa18) link :=
    wrapperAfterDwordStore_savedWord frame _ _ _ _ (stackBase + 0xa18) (offsetToNat 0xa18 (by omega))
  have s0Bytes : SavedWordBytes afterS0 (stackBase + 0xa10) s0 :=
    wrapperAfterDwordStore_savedWord afterLink _ _ _ _ (stackBase + 0xa10)
      (offsetToNat 0xa10 (by omega))
  have s1Bytes : SavedWordBytes afterS1 (stackBase + 0xa08) s1 :=
    wrapperAfterDwordStore_savedWord afterS0 _ _ _ _ (stackBase + 0xa08)
      (offsetToNat 0xa08 (by omega))
  have s2Bytes : SavedWordBytes final (stackBase + 0xa00) s2 :=
    wrapperAfterDwordStore_savedWord afterS1 _ _ _ _ (stackBase + 0xa00)
      (offsetToNat 0xa00 (by omega))
  have linkAfterS0 := wrapperAfterDwordStore_preserves_savedWord afterLink
    (BitVec.ofNat 64 0x102b8) s0Retired (BitVec.ofNat 64 (stackBase + 0xa10)) s0
    (stackBase + 0xa10) (stackBase + 0xa18) link
    (offsetToNat 0xa10 (by omega)) (by omega) linkBytes
  have linkAfterS1 := wrapperAfterDwordStore_preserves_savedWord afterS0
    (BitVec.ofNat 64 0x102bc) s1Retired (BitVec.ofNat 64 (stackBase + 0xa08)) s1
    (stackBase + 0xa08) (stackBase + 0xa18) link
    (offsetToNat 0xa08 (by omega)) (by omega) linkAfterS0
  have linkFinal := wrapperAfterDwordStore_preserves_savedWord afterS1
    (BitVec.ofNat 64 0x102c0) s2Retired (BitVec.ofNat 64 (stackBase + 0xa00)) s2
    (stackBase + 0xa00) (stackBase + 0xa18) link
    (offsetToNat 0xa00 (by omega)) (by omega) linkAfterS1
  have s0AfterS1 := wrapperAfterDwordStore_preserves_savedWord afterS0
    (BitVec.ofNat 64 0x102bc) s1Retired (BitVec.ofNat 64 (stackBase + 0xa08)) s1
    (stackBase + 0xa08) (stackBase + 0xa10) s0
    (offsetToNat 0xa08 (by omega)) (by omega) s0Bytes
  have s0Final := wrapperAfterDwordStore_preserves_savedWord afterS1
    (BitVec.ofNat 64 0x102c0) s2Retired (BitVec.ofNat 64 (stackBase + 0xa00)) s2
    (stackBase + 0xa00) (stackBase + 0xa10) s0
    (offsetToNat 0xa00 (by omega)) (by omega) s0AfterS1
  have s1Final := wrapperAfterDwordStore_preserves_savedWord afterS1
    (BitVec.ofNat 64 0x102c0) s2Retired (BitVec.ofNat 64 (stackBase + 0xa00)) s2
    (stackBase + 0xa00) (stackBase + 0xa08) s1
    (offsetToNat 0xa00 (by omega)) (by omega) s1Bytes
  have finalSavedFrame : WrapperSavedRegisterFrame stackBase link s0 s1 s2 final :=
    ⟨linkFinal, s0Final, s1Final, s2Bytes⟩
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
  have storedTagOutsideStack : ¬ canonicalContractParams.env.stack
      (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) := by
    simp [canonicalContractParams, canonicalEnvironment, canonicalStack, range]
    native_decide
  have frameStored : frame.mem.get? (canonicalContractParams.globals.storedResult +
      canonicalContractParams.globals.storedResultObject.discriminantOffset) =
      entry.mem.get? (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) := by
    simp [frame, wrapperAfterFirstFrameDecrement, afterRegisterWrite_mem]
  have linkStored := wrapperAfterStackStore_preserves_byte args stackBase 0xa18 entry frame machine
    (by decide) (BitVec.ofNat 64 0x102b4) linkRetired link _ storedTagOutsideStack
  have s0Stored := wrapperAfterStackStore_preserves_byte args stackBase 0xa10 entry afterLink machine
    (by decide) (BitVec.ofNat 64 0x102b8) s0Retired s0 _ storedTagOutsideStack
  have s1Stored := wrapperAfterStackStore_preserves_byte args stackBase 0xa08 entry afterS0 machine
    (by decide) (BitVec.ofNat 64 0x102bc) s1Retired s1 _ storedTagOutsideStack
  have finalStoredStep := wrapperAfterStackStore_preserves_byte args stackBase 0xa00 entry afterS1
    machine (by decide) (BitVec.ofNat 64 0x102c0) s2Retired s2 _ storedTagOutsideStack
  have finalStored := finalStoredStep.trans
    (s1Stored.trans (s0Stored.trans (linkStored.trans frameStored)))
  have frameInput : DecodedValue.MemoryBytes frame args.inputBase args.bytes := by
    simpa [frame, wrapperAfterFirstFrameDecrement, afterRegisterWrite_mem] using source.1
  have linkInput := wrapperAfterDwordStore_inputMemory args stackBase machine frame
    (BitVec.ofNat 64 0x102b4) linkRetired (BitVec.ofNat 64 (stackBase + 0xa18)) link
    (stackBase + 0xa18) (offsetToNat 0xa18 (by omega))
    (by omega) (by omega) frameInput
  have s0Input := wrapperAfterDwordStore_inputMemory args stackBase machine afterLink
    (BitVec.ofNat 64 0x102b8) s0Retired (BitVec.ofNat 64 (stackBase + 0xa10)) s0
    (stackBase + 0xa10) (offsetToNat 0xa10 (by omega))
    (by omega) (by omega) linkInput
  have s1Input := wrapperAfterDwordStore_inputMemory args stackBase machine afterS0
    (BitVec.ofNat 64 0x102bc) s1Retired (BitVec.ofNat 64 (stackBase + 0xa08)) s1
    (stackBase + 0xa08) (offsetToNat 0xa08 (by omega))
    (by omega) (by omega) s0Input
  have finalInputMemory := wrapperAfterDwordStore_inputMemory args stackBase machine afterS1
    (BitVec.ofNat 64 0x102c0) s2Retired (BitVec.ofNat 64 (stackBase + 0xa00)) s2
    (stackBase + 0xa00) (offsetToNat 0xa00 (by omega))
    (by omega) (by omega) s1Input
  have framePc : frame.regs.get? PC = some (BitVec.ofNat 64 0x102b4) := by
    change (wrapperAfterFirstFrameDecrement entry frameRetired
      (BitVec.ofNat 64 (stackBase + 0xa20))).regs.get? PC =
        some (BitVec.ofNat 64 0x102b4)
    unfold wrapperAfterFirstFrameDecrement
    exact afterRegisterWrite_pc entry (BitVec.ofNat 64 0x102b0) frameRetired x2
      (iTypeResult .ADDI 0x810#12 (BitVec.ofNat 64 (stackBase + 0xa20)))
  have prefix0 := wrapperOwnStep fromStep 0x102b0 entry frame machine.atEntry (regionPc _)
    (notExitPc _)
    (by simpa [frame] using frameRun)
  have prefix1 := wrapperOwnStep (fromStep + 1) 0x102b4 frame afterLink framePc (regionPc _)
    (notExitPc _)
    (by simpa [frame, afterLink] using linkRun)
  have prefix2 := wrapperOwnStep (fromStep + 2) 0x102b8 afterLink afterS0 linkPc (regionPc _)
    (notExitPc _)
    (by simpa [afterS0] using s0Run)
  have prefix3 := wrapperOwnStep (fromStep + 3) 0x102bc afterS0 afterS1 s0Pc (regionPc _)
    (notExitPc _)
    (by simpa [afterS1] using s1Run)
  have prefix4 := wrapperOwnStep (fromStep + 4) 0x102c0 afterS1 final s1Pc (regionPc _)
    (notExitPc _)
    (by simpa [final] using s2Run)
  have confined : WrapperConfinedPrefix fromStep 5 entry final := by
    confined_steps [prefix0, prefix1, prefix2, prefix3, prefix4]
  refine ⟨final, ?_, confined, finalPc, finalStack, finalInput, finalLength, finalAttempted,
    finalStored, finalInputMemory, finalPlatformAgree, finalCalleeSavedAgree, finalRetired, finalCode,
    ⟨link, s0, s1, s2, linkAtEntry, savedS0, savedS1, savedS2, finalSavedFrame⟩⟩
  refine Trace.step fromStep 4 entry frame final (by simpa [frame] using frameRun) ?_
  refine Trace.step (fromStep + 1) 3 frame afterLink final
    (by simpa [frame, afterLink] using linkRun) ?_
  refine Trace.step (fromStep + 2) 2 afterLink afterS0 final
    (by simpa [afterS0] using s0Run) ?_
  refine Trace.step (fromStep + 3) 1 afterS0 afterS1 final
    (by simpa [afterS1] using s1Run) ?_
  exact Trace.one (fromStep + 4) afterS1 final (by simpa [final] using s2Run)

/-! ## Final frame decrement -/

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
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine.machine agree
  obtain ⟨retired, run⟩ := decoderITypeStep machine.machine agree retiredPresent
    (by exact Contracts.canonicalCodeIntact_image code)
    stepNo 0x102c4 0x13 0x01 0x01 0xdd 0xdd0#12 2#5 2#5 .ADDI atPc
    (rX_x2_run _ _ (decoderExecuteState_get? stack))
    (by rw [wrapper_final_frame_decrement_value]; exact wX_x2_run _ _)
  exact ⟨retired, run, afterRegisterWrite_destination state (BitVec.ofNat 64 0x102c4) retired x2
    (BitVec.ofNat 64 stackBase) (by decide) (by decide)⟩

/-- The complete six-instruction frame setup, ending with the exact final stack pointer. -/
theorem wrapper_complete_frame_prefix (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
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
      final.mem.get? (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) =
        entry.mem.get? (canonicalContractParams.globals.storedResult +
          canonicalContractParams.globals.storedResultObject.discriminantOffset) ∧
      DecodedValue.MemoryBytes final args.inputBase args.bytes ∧
      Agree platformPreserved entry final ∧ Agree decodeRawCalleeSaved entry final ∧
      RetiredCounterPresent final ∧
      canonicalContractParams.env.CodeIntact final ∧
      ∃ link s0 s1 s2, entry.regs.get? x1 = some link ∧ entry.regs.get? x8 = some s0 ∧
        entry.regs.get? x9 = some s1 ∧ entry.regs.get? x18 = some s2 ∧
        WrapperSavedRegisterFrame stackBase link s0 s1 s2 final := by
  obtain ⟨saved, savedTrace, savedPrefix, savedPc, savedStack, savedInput, savedLength,
    savedAttempted, savedStored, savedInputMemory, savedAgree, savedCalleeSavedAgree, savedRetired,
    savedCode, savedFrame⟩ :=
    wrapper_entry_save_prefix fromStep args stackBase entry source machine
  obtain ⟨retired, run, finalStack⟩ := wrapper_final_frame_decrement_step
    (fromStep + 5) args stackBase entry saved machine savedAgree savedRetired savedCode savedPc savedStack
  let final := afterRegisterWrite saved (BitVec.ofNat 64 0x102c4) retired x2
    (BitVec.ofNat 64 stackBase)
  have finalPc : final.regs.get? PC = some (BitVec.ofNat 64 0x102c8) := by
    simpa [final] using afterRegisterWrite_pc saved (BitVec.ofNat 64 0x102c4) retired x2
      (BitVec.ofNat 64 stackBase)
  have finalInput : final.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) :=
    ((afterRegisterWrite_writes saved (BitVec.ofNat 64 0x102c4) retired x2
      (BitVec.ofNat 64 stackBase)).get x10 (by decide)).trans savedInput
  have finalLength : final.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size) :=
    ((afterRegisterWrite_writes saved (BitVec.ofNat 64 0x102c4) retired x2
      (BitVec.ofNat 64 stackBase)).get x11 (by decide)).trans savedLength
  have finalAttempted : final.mem.get? 0x4215020 = entry.mem.get? 0x4215020 := by
    simpa [final, afterRegisterWrite_mem] using savedAttempted
  have finalStored : final.mem.get? (canonicalContractParams.globals.storedResult +
      canonicalContractParams.globals.storedResultObject.discriminantOffset) =
      entry.mem.get? (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) := by
    simpa [final, afterRegisterWrite_mem] using savedStored
  have finalInputMemory : DecodedValue.MemoryBytes final args.inputBase args.bytes := by
    simpa [final, afterRegisterWrite_mem] using savedInputMemory
  have finalAgree : Agree platformPreserved entry final :=
    savedAgree.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  have finalCalleeSavedAgree : Agree decodeRawCalleeSaved entry final :=
    savedCalleeSavedAgree.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have finalCode : canonicalContractParams.env.CodeIntact final := by
    simpa [final, afterRegisterWrite_mem] using savedCode
  have finalRetired := afterRegisterWrite_retired_present saved (BitVec.ofNat 64 0x102c4)
    retired x2 (BitVec.ofNat 64 stackBase)
  obtain ⟨link, s0, s1, s2, linkAtEntry, s0AtEntry, s1AtEntry, s2AtEntry, savedFrame⟩ := savedFrame
  have finalFrame : WrapperSavedRegisterFrame stackBase link s0 s1 s2 final :=
    WrapperSavedRegisterFrame.of_mem_eq savedFrame (by simp [final, afterRegisterWrite_mem])
  have finalStep : WrapperConfinedPrefix (fromStep + 5) 1 saved final :=
    ConfinedPrefix.ownStep' savedPc (by simpa [final] using run)
  have confined : WrapperConfinedPrefix fromStep 6 entry final := by
    confined_steps [savedPrefix, finalStep]
  refine ⟨final, ?_, confined, finalPc, by simpa [final] using finalStack, finalInput, finalLength,
    finalAttempted, finalStored, finalInputMemory, finalAgree, finalCalleeSavedAgree, finalRetired,
    finalCode,
    ⟨link, s0, s1, s2, linkAtEntry, s0AtEntry, s1AtEntry, s2AtEntry, finalFrame⟩⟩
  exact Trace.snoc savedTrace (by simpa [final] using run)

/-! ## Preserve the input length in `s1` -/

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
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine.machine agree
  have resultEq : iTypeResult .ADDI 0#12 (BitVec.ofNat 64 args.bytes.size) =
      BitVec.ofNat 64 args.bytes.size := by
    simp [iTypeResult, show sign_extend (0#12) = (0#64) by decide]
  exact decoderITypeStep machine.machine agree retiredPresent
    (by exact Contracts.canonicalCodeIntact_image code)
    stepNo 0x102c8 0x93 0x84 0x05 0x00 0#12 11#5 9#5 .ADDI atPc
    (rX_x11_run _ _ (decoderExecuteState_get? length))
    (by rw [resultEq]; exact wX_x9_run _ _)

/-! ## Materialize the decoder-globals base -/

theorem wrapper_globals_page_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry state : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree platformPreserved entry state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102cc)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x102cc) retired x11
        (BitVec.ofNat 64 0x42152cc)) false := by
  obtain ⟨mseccfgBits, privilege, mseccfgRead⟩ := decodeReads machine.machine agree
  have decode := wrapper_globals_page_decode
    (tryStepControlFlowAfterIncrement state) privilege mseccfgBits mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102cc)
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x102cc) :=
    ((coreControlFlowNextState_writes (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x102cc)).get PC (by decide)).trans
        (pc_afterIncrement state (BitVec.ofNat 64 0x102cc) atPc)
  have resultValue : BitVec.ofNat 64 0x102cc + sign_extend (0x04205#20 ++ 0#12) =
      BitVec.ofNat 64 0x42152cc := by native_decide
  have execute : Runs (execute (.UTYPE (0x04205#20, .Regidx 11#5, .AUIPC))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 0x42152cc) }
      (.Retire_Success ()) := by
    apply execute_UTYPE_auipc_run executeState _ 0x04205#20 (.Regidx 11#5)
      (BitVec.ofNat 64 0x102cc)
    · exact readReg_run _ _ _ pcAtExecute
    · simpa [resultValue] using wX_bits_run_x11 executeState (BitVec.ofNat 64 0x42152cc)
  exact generatedRegisterWriteStep machine.machine agree retiredPresent
    (by exact Contracts.canonicalCodeIntact_image code)
    stepNo 0x102cc 0x04205597 atPc decode execute

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
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine.machine agree
  have resultValue : iTypeResult .ADDI 0xd54#12 (BitVec.ofNat 64 0x42152cc) =
      BitVec.ofNat 64 0x4215020 := by native_decide
  exact decoderITypeStep machine.machine agree retiredPresent
    (by exact Contracts.canonicalCodeIntact_image code)
    stepNo 0x102d0 0x13 0x89 0x45 0xd5 0xd54#12 11#5 18#5 .ADDI atPc
    (rX_x11_run _ _ (decoderExecuteState_get? page))
    (by rw [resultValue]; exact wX_x18_run _ _)

/-! ## Read the fresh-call flag -/

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
  have fetchBytes := wrapper_attempted_load_fetch state code
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine.machine agree
    (BitVec.ofNat 64 0x102d4) atPc (fetchPc _) _ _ _ _ fetchBytes
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
  have globalsAtExecute : executeState.regs.get? x18 = some address :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x102d4)).get x18 (by decide)).trans globals
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
    (Agree.weaken (fun _ preserved => preserved.2) executeAgree) allowed (by
      simp [is_aligned_paddr])
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
  have fetchBytes := wrapper_fresh_branch_fetch state code
  have currentMachine := machine.machine.mono
    (Agree.weaken (fun _ preserved => preserved.2) agree) retiredPresent
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform currentMachine (Agree.refl state)
    (BitVec.ofNat 64 0x102d8) atPc (fetchPc _) _ _ _ _ fetchBytes
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters currentMachine.normal (Agree.refl state) retiredPresent
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have decode := wrapper_fresh_branch_decode
    (tryStepControlFlowAfterIncrement state) privilege mseccfgBits mseccfgRead
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x102d8)
  have freshAtExecute : executeState.regs.get? x11 = some (0#64) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x102d8)).get x11 (by decide)).trans fresh
  have condition : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 11#5) .BEQ)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_x11_run executeState (0#64) freshAtExecute) ?_
    refine Runs.bind (rX_x0_run executeState) ?_
    rfl
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x102d8) :=
    ((coreControlFlowNextState_writes (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x102d8)).get PC (by decide)).trans
        (pc_afterIncrement state (BitVec.ofNat 64 0x102d8) atPc)
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
  · exact Elfling.tryStepControlFlowAfterRetired_pc _ _ _

/-- The fixed write set of the five prologue instructions that follow the frame setup: the
`try_step` bookkeeping plus the three architectural registers they target. Chosen once for the whole
segment rather than accumulated one `Or` per step -- see `Seg`'s module docstring. -/
@[reducible] private def wrapperFreshPrologueWrites : RegSet :=
  RegSet.union stepBookkeeping
    (RegSet.union (RegSet.only x9) (RegSet.union (RegSet.only x11) (RegSet.only x18)))

/-- Eleven wrapper-owned Sail steps reach the selected allocator setup on the fresh-call path.

The five instructions after the frame setup are composed through `Seg`, so no post-state of any of
them is ever named: each combinator hands back an opaque successor and every clause of the
conclusion is a field read or a one-line membership check. -/
theorem wrapper_fresh_prologue_prefix (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
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
      final.mem.get? (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) =
        entry.mem.get? (canonicalContractParams.globals.storedResult +
          canonicalContractParams.globals.storedResultObject.discriminantOffset) ∧
      DecodedValue.MemoryBytes final args.inputBase args.bytes ∧
      Agree platformPreserved entry final ∧ Agree decodeRawCalleeSaved entry final ∧
      RetiredCounterPresent final ∧
      canonicalContractParams.env.CodeIntact final ∧
      ∃ link s0 s1 s2, entry.regs.get? x1 = some link ∧ entry.regs.get? x8 = some s0 ∧
        entry.regs.get? x9 = some s1 ∧ entry.regs.get? x18 = some s2 ∧
        WrapperSavedRegisterFrame stackBase link s0 s1 s2 final := by
  obtain ⟨s6, trace6, prefix6, pc6, stack6, input6, length6, attempted6, stored6, inputMemory6,
    agree6, calleeSaved6, retired6, code6, frame6⟩ :=
    wrapper_complete_frame_prefix fromStep args stackBase entry source machine
  obtain ⟨link, savedS0, savedS1, savedS2, linkAtEntry, s0AtEntry, s1AtEntry, s2AtEntry,
    frame6⟩ := frame6
  have entryFresh : entry.mem.get? 0x4215020 = some (0#8) := by
    have represented := source.2.2.2.2.1.1
    have address : canonicalContractParams.globals.attempted = 0x4215020 := by native_decide
    rw [← address]
    simpa [FlagRep, DecoderGlobalsModel.fresh] using represented
  have fresh6 : s6.mem.get? 0x4215020 = some (0#8) := attempted6.trans entryFresh
  have bookkeeping : ∀ r, stepBookkeeping r → wrapperFreshPrologueWrites r := fun _ h => Or.inl h
  have disjoint : RegSet.Disjoint platformPreserved wrapperFreshPrologueWrites :=
    platformPreserved_disjoint.union
      ((RegSet.Disjoint.only (by simp [platformPreserved])).union
        ((RegSet.Disjoint.only (by simp [platformPreserved])).union
          (RegSet.Disjoint.only (by simp [platformPreserved]))))
  have calleeSavedDisjoint : RegSet.Disjoint decodeRawCalleeSaved wrapperFreshPrologueWrites :=
    decodeRawCalleeSaved_disjoint.union
      ((RegSet.Disjoint.only (by simp [decodeRawCalleeSaved])).union
        ((RegSet.Disjoint.only (by simp [decodeRawCalleeSaved])).union
          (RegSet.Disjoint.only (by simp [decodeRawCalleeSaved]))))
  -- `mv s1, a1` at `0x102c8`.
  obtain ⟨_, seg⟩ :=
    (Seg.nil
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary wrapperFreshPrologueWrites noMemory (fromStep + 6) retired6 pc6).step
      (regionPc _) (notExitPc _)
      x9 (BitVec.ofNat 64 args.bytes.size) (BitVec.ofNat 64 0x102cc)
      (wrapper_preserve_length_step _ args stackBase entry _ machine agree6 retired6 code6 pc6
        length6)
      (by decide) bookkeeping (Or.inr (Or.inl rfl)) (by decide) (by decide) (by decide)
  -- `auipc a1, 0x4205` at `0x102cc`.
  obtain ⟨_, seg⟩ :=
    seg.step (regionPc _) (notExitPc _)
      x11 (BitVec.ofNat 64 0x42152cc) (BitVec.ofNat 64 0x102d0)
      (wrapper_globals_page_step _ args stackBase entry _ machine
        (agree6.trans (seg.agree disjoint)) seg.retired
        (codeIntact_of_mem_eq (seg.memEq noMemory_empty) code6) seg.atPc)
      (by decide) bookkeeping (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
      (of_decide_eq_true rfl)
  -- `addi s2, a1, 0xd54` at `0x102d0`.
  obtain ⟨_, seg⟩ :=
    seg.step (regionPc _) (notExitPc _)
      x18 (BitVec.ofNat 64 0x4215020) (BitVec.ofNat 64 0x102d4)
      (wrapper_globals_address_step _ args stackBase entry _ machine
        (agree6.trans (seg.agree disjoint)) seg.retired
        (codeIntact_of_mem_eq (seg.memEq noMemory_empty) code6) seg.atPc
        (seg.reg x11 (BitVec.ofNat 64 0x42152cc) (by simp)))
      (by decide) bookkeeping (Or.inr (Or.inr (Or.inr rfl))) (by decide) (by decide)
      (of_decide_eq_true rfl)
  -- `lbu a1, 0(s2)` at `0x102d4` overwrites the `auipc` page value, which the `addi` above already
  -- consumed, so it is forgotten before the write that would invalidate it.
  obtain ⟨_, seg⟩ :=
    (seg.forget
        (kv' := [⟨x18, BitVec.ofNat 64 0x4215020⟩, ⟨x9, BitVec.ofNat 64 args.bytes.size⟩])
        (by simp)).step
      (regionPc _) (notExitPc _) x11 (0#64) (BitVec.ofNat 64 0x102d8)
      (wrapper_attempted_load_step _ args stackBase entry _ machine
        (agree6.trans (seg.agree disjoint)) seg.retired
        (codeIntact_of_mem_eq (seg.memEq noMemory_empty) code6) seg.atPc
        (seg.reg x18 (BitVec.ofNat 64 0x4215020) (by simp))
        (by rw [seg.memEq noMemory_empty]; exact fresh6))
      (by decide) bookkeeping (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
      (of_decide_eq_true rfl)
  -- `beqz a1, 0x102e8` at `0x102d8`, taken.
  obtain ⟨final, seg⟩ :=
    seg.stepJump (BitVec.ofNat 64 0x102e8) (regionPc _) (notExitPc _)
      (by
        obtain ⟨branchRetired, run, -⟩ := wrapper_fresh_branch_step _ args stackBase entry _
          machine (agree6.trans (seg.agree disjoint)) seg.retired
          (codeIntact_of_mem_eq (seg.memEq noMemory_empty) code6) seg.atPc
          (seg.reg x11 (0#64) (by simp))
        exact ⟨branchRetired, run⟩)
      bookkeeping (of_decide_eq_true rfl)
  have memory : final.mem = s6.mem := seg.memEq noMemory_empty
  exact ⟨final, Trace.append trace6 seg.trace, by confined_steps [prefix6, seg.confined],
    seg.atPc, (seg.get x2 (by decide)).trans stack6, (seg.get x10 (by decide)).trans input6,
    seg.reg x9 (BitVec.ofNat 64 args.bytes.size) (by simp),
    seg.reg x18 (BitVec.ofNat 64 0x4215020) (by simp),
    by rw [memory]; exact fresh6,
    by rw [memory]; exact stored6,
    inputMemory6.of_mem_eq (fun _ _ => by rw [memory]),
    agree6.trans (seg.agree disjoint), calleeSaved6.trans (seg.agree calleeSavedDisjoint), seg.retired,
    codeIntact_of_mem_eq memory code6,
    ⟨link, savedS0, savedS1, savedS2, linkAtEntry, s0AtEntry, s1AtEntry, s2AtEntry,
      WrapperSavedRegisterFrame.of_mem_eq frame6 memory⟩⟩

/-! ## Enter the selected allocator segment -/

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
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine.machine agree
  have resultEq : iTypeResult .ADDI 0#12 (BitVec.ofNat 64 args.inputBase) =
      BitVec.ofNat 64 args.inputBase := by
    simp [iTypeResult, show sign_extend (0#12) = (0#64) by decide]
  exact decoderITypeStep machine.machine agree retiredPresent
    (by exact Contracts.canonicalCodeIntact_image code)
    stepNo 0x102e8 0x13 0x04 0x05 0x00 0#12 10#5 8#5 .ADDI atPc
    (rX_x10_run _ _ (decoderExecuteState_get? input))
    (by rw [resultEq]; exact wX_x8_run _ _)

theorem wrapper_attempted_value_step (stepNo : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry state : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (agree : Agree platformPreserved entry state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x102ec)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x102ec) retired x10 (1#64)) false := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine.machine agree
  have resultEq : iTypeResult .ADDI 1#12 (0#64) = (1#64) := by native_decide
  exact decoderITypeStep machine.machine agree retiredPresent
    (by exact Contracts.canonicalCodeIntact_image code)
    stepNo 0x102ec 0x13 0x05 0x10 0x00 1#12 0#5 10#5 .ADDI atPc
    (rX_x0_run _) (by rw [resultEq]; exact wX_x10_run _ _)

/-- Thirteen wrapper-owned Sail steps reach the first selected allocator instruction. The live
registers are exactly the values consumed by that inline segment; no callable ABI is imposed. -/
theorem wrapper_to_allocator_entry_prefix (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
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
      final.mem.get? (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) =
        entry.mem.get? (canonicalContractParams.globals.storedResult +
          canonicalContractParams.globals.storedResultObject.discriminantOffset) ∧
      DecodedValue.MemoryBytes final args.inputBase args.bytes ∧
      Agree platformPreserved entry final ∧ Agree decodeRawCalleeSaved entry final ∧
      RetiredCounterPresent final ∧
      canonicalContractParams.env.CodeIntact final ∧
      ∃ link s0 s1 s2, entry.regs.get? x1 = some link ∧ entry.regs.get? x8 = some s0 ∧
        entry.regs.get? x9 = some s1 ∧ entry.regs.get? x18 = some s2 ∧
        WrapperSavedRegisterFrame stackBase link s0 s1 s2 final := by
  obtain ⟨s11, trace11, prefix11, pc11, stack11, input11, length11, globals11, fresh11, stored11,
    inputMemory11, agree11, calleeSaved11, retired11, code11, frame11⟩ :=
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
  have code12 : canonicalContractParams.env.CodeIntact s12 :=
    codeIntact_of_mem_eq (afterRegisterWrite_mem s11 (BitVec.ofNat 64 0x102e8) r12 x8 (BitVec.ofNat 64 args.inputBase)) code11
  obtain ⟨r13, run13⟩ := wrapper_attempted_value_step (fromStep + 12) args stackBase entry s12
    machine agree12 retired12 code12 pc12
  let final := afterRegisterWrite s12 (BitVec.ofNat 64 0x102ec) r13 x10 (1#64)
  have savedInput12 : s12.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) :=
    afterRegisterWrite_destination s11 (BitVec.ofNat 64 0x102e8) r12 x8 (BitVec.ofNat 64 args.inputBase) (by decide) (by decide)
  have w12 : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x8)) s11 s12 :=
    afterRegisterWrite_writes s11 (BitVec.ofNat 64 0x102e8) r12 x8 (BitVec.ofNat 64 args.inputBase)
  have wFinal : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x10)) s12 final :=
    afterRegisterWrite_writes s12 (BitVec.ofNat 64 0x102ec) r13 x10 (1#64)
  obtain ⟨finalStack, finalSavedInput, finalLength, finalGlobals⟩ :
      final.regs.get? x2 = some (BitVec.ofNat 64 stackBase) ∧
      final.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      final.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      final.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have finalPc : final.regs.get? PC = some (BitVec.ofNat 64 0x102f0) := by
    simpa [final] using afterRegisterWrite_pc s12 (BitVec.ofNat 64 0x102ec) r13 x10 (1#64)
  have finalValue : final.regs.get? x10 = some (1#64) :=
    afterRegisterWrite_destination s12 (BitVec.ofNat 64 0x102ec) r13 x10 (1#64) (by decide) (by decide)
  have finalFresh : final.mem.get? 0x4215020 = some (0#8) := by
    simpa [final, s12, afterRegisterWrite_mem] using fresh11
  have finalStored : final.mem.get? (canonicalContractParams.globals.storedResult +
      canonicalContractParams.globals.storedResultObject.discriminantOffset) =
      entry.mem.get? (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) := by
    simpa [final, s12, afterRegisterWrite_mem] using stored11
  have finalInputMemory : DecodedValue.MemoryBytes final args.inputBase args.bytes := by
    simpa [final, s12, afterRegisterWrite_mem] using inputMemory11
  have finalAgree : Agree platformPreserved entry final :=
    agree12.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  have agree12CalleeSaved : Agree decodeRawCalleeSaved entry s12 :=
    calleeSaved11.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have finalCalleeSavedAgree : Agree decodeRawCalleeSaved entry final :=
    agree12CalleeSaved.trans (afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]))
  have finalRetired := afterRegisterWrite_retired_present s12 (BitVec.ofNat 64 0x102ec) r13 x10
    (1#64)
  have finalCode : canonicalContractParams.env.CodeIntact final := by
    simpa [final, afterRegisterWrite_mem] using code12
  obtain ⟨link, savedS0, savedS1, savedS2, linkAtEntry, s0AtEntry, s1AtEntry, s2AtEntry,
    frame11⟩ := frame11
  have finalFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 final := by
    apply WrapperSavedRegisterFrame.of_mem_eq frame11
    simp [final, s12, afterRegisterWrite_mem]
  have prefix12 : WrapperConfinedPrefix (fromStep + 11) 1 s11 s12 :=
    ConfinedPrefix.ownStep' pc11 (by simpa [s12] using run12)
  have prefix13 : WrapperConfinedPrefix (fromStep + 12) 1 s12 final :=
    ConfinedPrefix.ownStep' pc12 (by simpa [final] using run13)
  have confined : WrapperConfinedPrefix fromStep 13 entry final := by
    confined_steps [prefix11, prefix12, prefix13]
  refine ⟨final, ?_, confined, finalPc, finalStack, finalSavedInput, finalLength, finalValue,
    finalGlobals, finalFresh, finalStored,
    finalInputMemory, finalAgree, finalCalleeSavedAgree, finalRetired, finalCode,
    ⟨link, savedS0, savedS1, savedS2, linkAtEntry, s0AtEntry, s1AtEntry, s2AtEntry, finalFrame⟩⟩
  have trace12 := Trace.snoc trace11 (by simpa [s12] using run12)
  simpa [final] using Trace.snoc trace12 run13

/-- The wrapper's concrete thirteen-step prefix supplies the real entry state for the allocator's
first selected segment, then consumes that segment through its Level 2 contract. -/
theorem wrapper_reaches_allocator_first_segment
    (allocator : AllocatorInlineContract) (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
      DecoderGlobalsModel.fresh args entry)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    ∃ atAllocator retired,
      Trace fromStep 13 entry atAllocator ∧
      Nonempty (AllocatorInlineTransfer (fromStep + 13) 0 atAllocator
        (allocatorAfterDataPointer atAllocator retired (BitVec.ofNat 64 0x4215020))) := by
  obtain ⟨atAllocator, trace, -, pc, -, -, -, -, globals, -, -, -, agree, -, retired, code, -⟩ :=
    wrapper_to_allocator_entry_prefix fromStep args stackBase entry source machine
  have platform := decoderInstructionStepPlatform machine.machine
    (Agree.weaken (fun _ preserved => preserved.2) agree) retired code 0x102f0 pc
      (fetchPc _)
  obtain ⟨nextRetired, transfer⟩ := allocator.1 (fromStep + 13) atAllocator
    (BitVec.ofNat 64 0x4215020) ⟨platform, pc, globals⟩
  exact ⟨atAllocator, nextRetired, trace, transfer⟩

/-- The first allocator segment and the wrapper-owned tag store are now part of one concrete trace.
The only condition consumed here is the selected allocator contract itself. -/
theorem wrapper_through_allocator_tag
    (allocator : AllocatorInlineContract) (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
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
      final.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      final.mem.get? 0x4215020 = some (1#8) ∧
      final.mem.get? (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) =
        entry.mem.get? (canonicalContractParams.globals.storedResult +
          canonicalContractParams.globals.storedResultObject.discriminantOffset) ∧
      DecodedValue.MemoryBytes final args.inputBase args.bytes ∧
      Agree platformPreserved entry final ∧ Agree decoderPreserved entry final ∧
      Agree decodeRawCalleeSaved entry final ∧
      RetiredCounterPresent final ∧
      canonicalContractParams.env.CodeIntact final ∧
      ∃ link s0 s1 s2, entry.regs.get? x1 = some link ∧ entry.regs.get? x8 = some s0 ∧
        entry.regs.get? x9 = some s1 ∧ entry.regs.get? x18 = some s2 ∧
        WrapperSavedRegisterFrame stackBase link s0 s1 s2 final := by
  obtain ⟨atAllocator, trace13, prefix13, pc13, stack13, savedInput13, length13, data13,
    globals13, -, stored13, inputMemory13, agree13, calleeSaved13, retired13, code13, frame13⟩ :=
    wrapper_to_allocator_entry_prefix fromStep args stackBase entry source machine
  have platform13 := decoderInstructionStepPlatform machine.machine
    (Agree.weaken (fun _ preserved => preserved.2) agree13) retired13 code13 0x102f0 pc13
      (fetchPc _)
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
  -- The data-pointer step writes `x11` and the bookkeeping, and nothing else; every register the
  -- allocator entry carries forward is one `grind` against that.
  have wFirst : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x11)) atAllocator
      afterFirst :=
    afterRegisterWrite_writes atAllocator (BitVec.ofNat 64 0x102f0) r14 x11
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x4215020) 1)
  have firstCalleeSavedAgree : Agree decodeRawCalleeSaved entry afterFirst :=
    calleeSaved13.trans (wFirst.agree
      (decodeRawCalleeSaved_disjoint.union
        (RegSet.Disjoint.only (by simp [decodeRawCalleeSaved]))))
  obtain ⟨firstTarget, firstData⟩ :
      afterFirst.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      afterFirst.regs.get? x10 = some (1#64) := by grind
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
  obtain ⟨r15, tagStep⟩ := wrapper_allocator_tag_step_configured machine.machine firstAgree
    firstRetired firstCode (fromStep + 14) (fetchPc _) firstPc
    (BitVec.ofNat 64 0x4215020)
    (1#64) firstTarget firstData writable
  let final := wrapperAfterAllocatorTag afterFirst r15 (BitVec.ofNat 64 0x4215020) (1#64)
  have wTag : WritesOnlyRegs stepBookkeeping afterFirst final :=
    wrapperAfterAllocatorTag_writes afterFirst r15 (BitVec.ofNat 64 0x4215020) (1#64)
  have firstContext : afterFirst.regs.get? x11 = some (BitVec.ofNat 64 0x4215021) := by
    have valueEq : Sail.BitVec.addInt (BitVec.ofNat 64 0x4215020) 1 =
        BitVec.ofNat 64 0x4215021 := by native_decide
    rw [← valueEq]
    exact afterRegisterWrite_destination atAllocator (BitVec.ofNat 64 0x102f0) r14 x11
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x4215020) 1) (by decide) (by decide)
  -- Five registers across both steps in one `grind`: `x11` from the state that wrote it, the rest
  -- straight back through the allocator entry.
  obtain ⟨finalStack, finalSavedInput, finalLength, finalContext, finalGlobals⟩ :
      final.regs.get? x2 = some (BitVec.ofNat 64 stackBase) ∧
      final.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      final.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      final.regs.get? x11 = some (BitVec.ofNat 64 0x4215021) ∧
      final.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have firstInputMemory : DecodedValue.MemoryBytes afterFirst args.inputBase args.bytes := by
    simpa [afterFirst, allocatorAfterDataPointer, afterRegisterWrite_mem] using inputMemory13
  have finalInputMemory : DecodedValue.MemoryBytes final args.inputBase args.bytes := by
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
  have finalPlatformAgree : Agree platformPreserved entry final :=
    agree13.trans (firstAgreePlatform.trans (wTag.agree platformPreserved_disjoint))
  have finalAgree := firstAgree.trans
    (wrapperAfterAllocatorTag_agree afterFirst r15 (BitVec.ofNat 64 0x4215020) (1#64))
  have finalCalleeSavedAgree : Agree decodeRawCalleeSaved entry final :=
    firstCalleeSavedAgree.trans (wTag.agree decodeRawCalleeSaved_disjoint)
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
  have finalAttempted : final.mem.get? 0x4215020 = some (1#8) := by
    simp [final, wrapperAfterAllocatorTag, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem_insert]
    decide
  have firstStored : afterFirst.mem.get?
      (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) =
      atAllocator.mem.get? (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) := by
    simp [afterFirst, allocatorAfterDataPointer, afterRegisterWrite_mem]
  have tagNotAttempted : 0x4215020 ≠
      canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset := by native_decide
  have finalStored : final.mem.get? (canonicalContractParams.globals.storedResult +
      canonicalContractParams.globals.storedResultObject.discriminantOffset) =
      entry.mem.get? (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) := by
    change (afterFirst.mem.insert 0x4215020 (Sail.BitVec.extractLsb (1#64) 7 0)).get? _ = _
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg tagNotAttempted]
    exact firstStored.trans stored13
  obtain ⟨link, savedS0, savedS1, savedS2, linkAtEntry, s0AtEntry, s1AtEntry, s2AtEntry,
    frame13⟩ := frame13
  have firstFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 afterFirst := by
    apply WrapperSavedRegisterFrame.of_mem_eq frame13
    simp [afterFirst, allocatorAfterDataPointer, afterRegisterWrite_mem]
  have tagBeforeSaveArea : (BitVec.ofNat 64 0x4215020).toNat + 1 ≤ stackBase + 0xa00 := by
    have stackAfterResult := wrapper_stack_after_stored_result machine
    change 0x4215021 ≤ stackBase + 0xa00
    omega
  have finalFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 final := by
    simpa [final] using wrapperAfterAllocatorTag_preserves_savedFrame afterFirst r15
      (BitVec.ofNat 64 0x4215020) (1#64) stackBase tagBeforeSaveArea firstFrame
  have firstLevel2 := firstTransfer.mapSummary
    (fun child stepNo used before after run => allocatorChildSummary_to_level2 run)
  have firstPrefix : WrapperConfinedPrefix (fromStep + 13) 1 atAllocator afterFirst := by
    intro count tail rest
    simpa [Nat.add_assoc] using ScopedTrace.inlineStep (fromStep + 13) 0 count
      allocatorInlineBoundary generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
      atAllocator afterFirst tail firstLevel2 (by simpa [Nat.add_assoc] using rest)
  have tagPrefix : WrapperConfinedPrefix (fromStep + 14) 1 afterFirst final :=
    ConfinedPrefix.ownStep' firstPc (by simpa [final] using tagStep)
  have confined : WrapperConfinedPrefix fromStep 15 entry final := by
    confined_steps [prefix13, firstPrefix, tagPrefix]
  refine ⟨final, ?_, confined, finalPc, finalStack, finalSavedInput, finalLength, finalContext,
    finalGlobals, finalAttempted, finalStored, finalInputMemory, finalPlatformAgree, finalAgree,
    finalCalleeSavedAgree, finalRetired, finalCode,
    ⟨link, savedS0, savedS1, savedS2, linkAtEntry, s0AtEntry, s1AtEntry, s2AtEntry, finalFrame⟩⟩
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

private theorem memoryBytes_afterWriteBytes_retired {state : State} {base : Nat}
    {bytes : ByteArray} (pc nextPc retired target data : BitVec 64)
    (inputMemory : DecodedValue.MemoryBytes state base bytes)
    (outside : ∀ inputIndex, inputIndex < bytes.size → ∀ storeIndex : Fin 8,
      target.toNat + storeIndex.val ≠ base + inputIndex) :
    DecodedValue.MemoryBytes
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (width := 8)
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
          target.toNat data)
        nextPc retired)
      base bytes := by
  apply inputMemory.of_mem_eq
  intro inputIndex inputBound
  exact afterWriteBytes_mem_get?_of_outside _ target.toNat data (base + inputIndex)
    (outside inputIndex inputBound)

private theorem wrapper_second_allocator_inputMemory
    (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry atSecond : State)
    (machine : ZesuDecodeRawMachinePre args stackBase entry)
    (inputMemory : DecodedValue.MemoryBytes atSecond args.inputBase args.bytes)
    (pageRetired addressRetired contextRetired functionRetired : BitVec 64) :
    DecodedValue.MemoryBytes
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
  have pageInput : DecodedValue.MemoryBytes afterPage args.inputBase args.bytes :=
    inputMemory.of_mem_eq (fun _ _ => by rw [allocatorAfterFunctionPage_mem])
  have addressInput : DecodedValue.MemoryBytes afterAddress args.inputBase args.bytes :=
    pageInput.of_mem_eq (fun _ _ => by rw [allocatorAfterFunctionAddress_mem])
  have contextInput : DecodedValue.MemoryBytes afterContext args.inputBase args.bytes := by
    apply memoryBytes_afterWriteBytes_retired _ _ _ _ _ addressInput
    intro inputIndex inputBound storeIndex equal
    rw [show (BitVec.ofNat 64 stackBase + sign_extend (0x010#12)).toNat = stackBase + 0x10 by
      rw [show sign_extend (m := 64) (0x010#12) = BitVec.ofNat 64 0x10 by decide,
        ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have frameFits := machine.stackFrameFits
      omega] at equal
    rcases machine.inputAvoidsStack with inputBefore | stackBeforeInput <;> omega
  apply memoryBytes_afterWriteBytes_retired _ _ _ _ _ contextInput
  intro inputIndex inputBound storeIndex equal
  rw [show (BitVec.ofNat 64 stackBase + sign_extend (0x018#12)).toNat = stackBase + 0x18 by
    rw [show sign_extend (m := 64) (0x018#12) = BitVec.ofNat 64 0x18 by decide,
      ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have frameFits := machine.stackFrameFits
    omega] at equal
  rcases machine.inputAvoidsStack with inputBefore | stackBeforeInput <;> omega

private theorem wrapper_second_allocator_contextCode
    (stackBase : Nat) (atSecond : State) (pageRetired addressRetired contextRetired : BitVec 64)
    (contextNotFile : ∀ index : Fin 8, Artifacts.programImage.readFileByte?
      ((BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x10).toNat + index.val) = none)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully atSecond.mem) :
    Artifacts.programImage.fileBytesLoadedFaithfully
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
    (code : Artifacts.programImage.fileBytesLoadedFaithfully atSecond.mem) :
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
  globals : final.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  attempted : final.mem.get? 0x4215020 = atSecond.mem.get? 0x4215020
  stored : final.mem.get? (canonicalContractParams.globals.storedResult +
    canonicalContractParams.globals.storedResultObject.discriminantOffset) =
    atSecond.mem.get? (canonicalContractParams.globals.storedResult +
      canonicalContractParams.globals.storedResultObject.discriminantOffset)
  inputMemory : DecodedValue.MemoryBytes final args.inputBase args.bytes
  platform : Agree platformPreserved entry final
  agree : Agree decoderPreserved entry final
  calleeSaved : Agree decodeRawCalleeSaved entry final
  retired : RetiredCounterPresent final
  code : canonicalContractParams.env.CodeIntact final
  savedFrame : ∃ link s0 s1 s2, entry.regs.get? x1 = some link ∧ entry.regs.get? x8 = some s0 ∧
    entry.regs.get? x9 = some s1 ∧ entry.regs.get? x18 = some s2 ∧
    WrapperSavedRegisterFrame stackBase link s0 s1 s2 final

/-- Semantic handoff for the allocator's second inline segment. Keeping its state transport
separate from the enclosing trace splice bounds elaboration cost for the wrapper capstone. -/
private theorem wrapper_second_allocator_semantics
    (allocator : AllocatorInlineContract) (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry atSecond : State)
    (pc15 : atSecond.regs.get? PC = some (BitVec.ofNat 64 0x102f8))
    (stack15 : atSecond.regs.get? x2 = some (BitVec.ofNat 64 stackBase))
    (savedInput15 : atSecond.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase))
    (length15 : atSecond.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size))
    (globals15 : atSecond.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
    (context15 : atSecond.regs.get? x11 = some (BitVec.ofNat 64 0x4215021))
    (inputMemory15 : DecodedValue.MemoryBytes atSecond args.inputBase args.bytes)
    (platform15 : Agree platformPreserved entry atSecond)
    (agree15 : Agree decoderPreserved entry atSecond)
    (calleeSaved15 : Agree decodeRawCalleeSaved entry atSecond)
    (retired15 : RetiredCounterPresent atSecond)
    (code15 : canonicalContractParams.env.CodeIntact atSecond)
    (frame15 : ∃ link s0 s1 s2, entry.regs.get? x1 = some link ∧ entry.regs.get? x8 = some s0 ∧
      entry.regs.get? x9 = some s1 ∧ entry.regs.get? x18 = some s2 ∧
      WrapperSavedRegisterFrame stackBase link s0 s1 s2 atSecond)
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
  have code : Artifacts.programImage.fileBytesLoadedFaithfully atSecond.mem := by
    exact Contracts.canonicalCodeIntact_image code15
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
  have contextTargetNat :
      (BitVec.ofNat 64 stackBase + sign_extend (0x010#12)).toNat = stackBase + 0x10 := by
    rw [contextTarget, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have frameFits := machine.stackFrameFits
    omega
  have functionTargetNat :
      (BitVec.ofNat 64 stackBase + sign_extend (0x018#12)).toNat = stackBase + 0x18 := by
    rw [functionTarget, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have frameFits := machine.stackFrameFits
    omega
  have finalInputMemory : DecodedValue.MemoryBytes final args.inputBase args.bytes := by
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
  have finalPlatform : Agree platformPreserved entry final :=
    platform15.trans (((pageAgree.trans addressAgree).trans contextAgree).trans functionAgree)
  have pageCalleeSavedAgree : Agree decodeRawCalleeSaved atSecond afterPage :=
    afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved])
  have addressCalleeSavedAgree : Agree decodeRawCalleeSaved afterPage afterAddress :=
    afterRegisterWrite_agree_of
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved]) (by simp [decodeRawCalleeSaved])
      (by simp [decodeRawCalleeSaved])
  have contextCalleeSavedAgree : Agree decodeRawCalleeSaved afterAddress afterContext :=
    (allocatorAfterContextStore_writes afterAddress contextRetired (BitVec.ofNat 64 stackBase)
      (BitVec.ofNat 64 0x4215021)).agree decodeRawCalleeSaved_disjoint
  have functionCalleeSavedAgree : Agree decodeRawCalleeSaved afterContext final :=
    (allocatorAfterFunctionStore_writes afterContext functionRetired (BitVec.ofNat 64 stackBase)
      (BitVec.ofNat 64 0x13f70)).agree decodeRawCalleeSaved_disjoint
  have finalCalleeSaved : Agree decodeRawCalleeSaved entry final :=
    calleeSaved15.trans
      (((pageCalleeSavedAgree.trans addressCalleeSavedAgree).trans contextCalleeSavedAgree).trans
        functionCalleeSavedAgree)
  have finalRetired : RetiredCounterPresent final :=
    tryStepControlFlowAfterRetired_retired_present _ _ functionRetired
  have pageAttempted : afterPage.mem.get? 0x4215020 = atSecond.mem.get? 0x4215020 := by
    simp [afterPage, allocatorAfterFunctionPage, afterRegisterWrite_mem]
  have addressAttempted : afterAddress.mem.get? 0x4215020 = afterPage.mem.get? 0x4215020 := by
    simp [afterAddress, allocatorAfterFunctionAddress, afterRegisterWrite_mem]
  have contextAttempted : afterContext.mem.get? 0x4215020 = afterAddress.mem.get? 0x4215020 := by
    refine storeRetirement_mem_writes afterAddress (BitVec.ofNat 64 0x10300)
      (BitVec.ofNat 64 0x10304) contextRetired
      (BitVec.ofNat 64 stackBase + sign_extend (0x010#12)).toNat
      (BitVec.ofNat 64 0x4215021) 0x4215020 ?_
    rintro ⟨lower, _⟩
    rw [contextTargetNat] at lower
    have stackAfterResult := wrapper_stack_after_stored_result machine
    omega
  have functionAttempted : final.mem.get? 0x4215020 = afterContext.mem.get? 0x4215020 := by
    refine storeRetirement_mem_writes afterContext (BitVec.ofNat 64 0x10304)
      (BitVec.ofNat 64 0x10308) functionRetired
      (BitVec.ofNat 64 stackBase + sign_extend (0x018#12)).toNat
      (BitVec.ofNat 64 0x13f70) 0x4215020 ?_
    rintro ⟨lower, _⟩
    rw [functionTargetNat] at lower
    have stackAfterResult := wrapper_stack_after_stored_result machine
    omega
  have finalAttempted : final.mem.get? 0x4215020 = atSecond.mem.get? 0x4215020 :=
    functionAttempted.trans (contextAttempted.trans (addressAttempted.trans pageAttempted))
  have storedTagAddress : canonicalContractParams.globals.storedResult +
      canonicalContractParams.globals.storedResultObject.discriminantOffset = 0x4215370 := by native_decide
  have pageStored : afterPage.mem.get?
      (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) = atSecond.mem.get?
      (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) := by
    simp [afterPage, allocatorAfterFunctionPage, afterRegisterWrite_mem]
  have addressStored : afterAddress.mem.get?
      (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) = afterPage.mem.get?
      (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) := by
    simp [afterAddress, allocatorAfterFunctionAddress, afterRegisterWrite_mem]
  have contextStored : afterContext.mem.get?
      (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) = afterAddress.mem.get?
      (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) := by
    refine storeRetirement_mem_writes afterAddress (BitVec.ofNat 64 0x10300)
      (BitVec.ofNat 64 0x10304) contextRetired
      (BitVec.ofNat 64 stackBase + sign_extend (0x010#12)).toNat
      (BitVec.ofNat 64 0x4215021) _ ?_
    rintro ⟨lower, _⟩
    rw [contextTargetNat, storedTagAddress] at lower
    have stackAfterResult := wrapper_stack_after_stored_result machine
    omega
  have functionStored : final.mem.get?
      (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) = afterContext.mem.get?
      (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) := by
    refine storeRetirement_mem_writes afterContext (BitVec.ofNat 64 0x10304)
      (BitVec.ofNat 64 0x10308) functionRetired
      (BitVec.ofNat 64 stackBase + sign_extend (0x018#12)).toNat
      (BitVec.ofNat 64 0x13f70) _ ?_
    rintro ⟨lower, _⟩
    rw [functionTargetNat, storedTagAddress] at lower
    have stackAfterResult := wrapper_stack_after_stored_result machine
    omega
  have finalStored := functionStored.trans (contextStored.trans (addressStored.trans pageStored))
  -- The write set of each of the segment's four steps; the two register writes both target `x10`,
  -- the two stores write only the bookkeeping.
  have wPage : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x10)) atSecond afterPage :=
    afterRegisterWrite_writes atSecond (BitVec.ofNat 64 0x102f8) pageRetired x10
      (BitVec.ofNat 64 0x142f8)
  have wAddress : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x10)) afterPage
      afterAddress :=
    afterRegisterWrite_writes afterPage (BitVec.ofNat 64 0x102fc) addressRetired x10
      (BitVec.ofNat 64 0x13f70)
  have wContext : WritesOnlyRegs stepBookkeeping afterAddress afterContext :=
    allocatorAfterContextStore_writes afterAddress contextRetired (BitVec.ofNat 64 stackBase)
      (BitVec.ofNat 64 0x4215021)
  have wFunction : WritesOnlyRegs stepBookkeeping afterContext final :=
    allocatorAfterFunctionStore_writes afterContext functionRetired (BitVec.ofNat 64 stackBase)
      (BitVec.ofNat 64 0x13f70)
  obtain ⟨finalStack, finalSavedInput, finalLength, finalGlobals⟩ :
      final.regs.get? x2 = some (BitVec.ofNat 64 stackBase) ∧
      final.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      final.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      final.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have finalCode : canonicalContractParams.env.CodeIntact final := by
    simpa [final, afterContext, afterAddress, afterPage] using
      wrapper_second_allocator_code args stackBase entry atSecond machine pageRetired
        addressRetired contextRetired functionRetired contextNotFile functionNotFile code
  obtain ⟨link, savedS0, savedS1, savedS2, linkAtEntry, s0AtEntry, s1AtEntry, s2AtEntry,
    frame15⟩ := frame15
  have pageFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 afterPage := by
    apply WrapperSavedRegisterFrame.of_mem_eq frame15
    simp [afterPage, allocatorAfterFunctionPage, afterRegisterWrite_mem]
  have addressFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 afterAddress := by
    apply WrapperSavedRegisterFrame.of_mem_eq pageFrame
    simp [afterAddress, allocatorAfterFunctionAddress, afterRegisterWrite_mem]
  have contextTargetValue :
      (BitVec.ofNat 64 stackBase + sign_extend (0x010#12)).toNat = stackBase + 0x10 := by
    rw [contextTarget, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have frameFits := machine.stackFrameFits
    omega
  have contextFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 afterContext := by
    change WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2
      (wrapperAfterDwordStore afterAddress (BitVec.ofNat 64 0x10300) contextRetired
        (BitVec.ofNat 64 stackBase + sign_extend (0x010#12)) (BitVec.ofNat 64 0x4215021))
    exact wrapperAfterDwordStore_preserves_savedFrame afterAddress (BitVec.ofNat 64 0x10300)
      contextRetired (BitVec.ofNat 64 stackBase + sign_extend (0x010#12))
      (BitVec.ofNat 64 0x4215021) stackBase (stackBase + 0x10) contextTargetValue (by omega)
      addressFrame
  have functionTargetValue :
      (BitVec.ofNat 64 stackBase + sign_extend (0x018#12)).toNat = stackBase + 0x18 := by
    rw [functionTarget, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have frameFits := machine.stackFrameFits
    omega
  have finalFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 final := by
    change WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2
      (wrapperAfterDwordStore afterContext (BitVec.ofNat 64 0x10304) functionRetired
        (BitVec.ofNat 64 stackBase + sign_extend (0x018#12)) (BitVec.ofNat 64 0x13f70))
    exact wrapperAfterDwordStore_preserves_savedFrame afterContext (BitVec.ofNat 64 0x10304)
      functionRetired (BitVec.ofNat 64 stackBase + sign_extend (0x018#12))
      (BitVec.ofNat 64 0x13f70) stackBase (stackBase + 0x18) functionTargetValue (by omega)
      contextFrame
  refine ⟨
    { final := final
      transfer := transfer
      pc := ?_
      stack := finalStack
      savedInput := finalSavedInput
      length := finalLength
      globals := finalGlobals
      attempted := finalAttempted
      stored := finalStored
      inputMemory := finalInputMemory
      platform := finalPlatform
      agree := finalAgree
      calleeSaved := finalCalleeSaved
      retired := finalRetired
      code := finalCode
      savedFrame := ⟨link, savedS0, savedS1, savedS2, linkAtEntry, s0AtEntry, s1AtEntry,
        s2AtEntry, finalFrame⟩ }⟩
  simpa [final] using allocatorAfterFunctionStore_pc _ functionRetired
    (BitVec.ofNat 64 stackBase) (BitVec.ofNat 64 0x13f70)

/-- Nineteen concrete steps now cover the wrapper prologue, both allocator segments, and the
wrapper-owned tag store, ending at the selected `decode` entry. -/
theorem wrapper_through_allocator_setup
    (allocator : AllocatorInlineContract) (fromStep : Nat) (args : ZesuDecodeRawArgs)
    (stackBase : Nat) (entry : State)
    (source : preZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
      canonicalContractParams.resultBuffer canonicalContractParams.repStatelessInput
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
      final.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      final.mem.get? 0x4215020 = some (1#8) ∧
      final.mem.get? (canonicalContractParams.globals.storedResult +
        canonicalContractParams.globals.storedResultObject.discriminantOffset) =
        entry.mem.get? (canonicalContractParams.globals.storedResult +
          canonicalContractParams.globals.storedResultObject.discriminantOffset) ∧
      DecodedValue.MemoryBytes final args.inputBase args.bytes ∧
      Agree platformPreserved entry final ∧ Agree decoderPreserved entry final ∧
      Agree decodeRawCalleeSaved entry final ∧
      RetiredCounterPresent final ∧
      canonicalContractParams.env.CodeIntact final ∧
      ∃ link s0 s1 s2, entry.regs.get? x1 = some link ∧ entry.regs.get? x8 = some s0 ∧
        entry.regs.get? x9 = some s1 ∧ entry.regs.get? x18 = some s2 ∧
        WrapperSavedRegisterFrame stackBase link s0 s1 s2 final := by
  obtain ⟨atSecond, trace15, prefix15, pc15, stack15, savedInput15, length15, context15, globals15,
    attempted15, _stored15, inputMemory15, platform15, agree15, calleeSaved15, retired15, code15,
    frame15⟩ :=
    wrapper_through_allocator_tag allocator fromStep args stackBase entry source machine
  obtain ⟨post⟩ :=
    wrapper_second_allocator_semantics allocator fromStep args stackBase entry atSecond pc15
      stack15 savedInput15 length15 globals15 context15 inputMemory15 platform15 agree15 calleeSaved15
        retired15 code15 frame15 machine
  let final := post.final
  have transfer := post.transfer
  have trace4 := allocator_second_trace_of_inlineTransfer (fromStep + 15) atSecond final transfer
  have complete := Trace.append trace15 (by simpa [Nat.add_assoc] using trace4)
  have secondLevel2 := transfer.mapSummary
    (fun child stepNo used before after run => allocatorChildSummary_to_level2 run)
  have secondPrefix : WrapperConfinedPrefix (fromStep + 15) 4 atSecond final := by
    intro count tail rest
    simpa [Nat.add_assoc] using ScopedTrace.inlineStep (fromStep + 15) 3 count
      allocatorInlineBoundary generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
      atSecond final tail secondLevel2 (by simpa [Nat.add_assoc] using rest)
  have confined : WrapperConfinedPrefix fromStep 19 entry final := by
    confined_steps [prefix15, secondPrefix]
  exact ⟨final, by simpa [Nat.add_assoc] using complete, confined, post.pc, post.stack,
    post.savedInput, post.length, post.globals, post.attempted.trans attempted15,
    post.stored.trans _stored15, post.inputMemory, post.platform, post.agree, post.calleeSaved,
    post.retired, post.code,
    post.savedFrame⟩

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
  · exact regionPc _
  · exact notExitPc _
  · simp [decodeInlineBoundary]
  · exact regionPc _
  · exact notExitPc _
  · exact regionPc _

end BinaryFv.Zesu.MachineExecution
