import BinaryFv.Zesu.MachineExecution.GeneratedWordStep
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.MachineExecution.OwnedPc

/-!
# Wrapper single-instruction steps

Step lemmas and register/memory helpers for the instructions owned by the emitted
`zesu_decode_raw` wrapper. Everything here is stated purely over the RiscV execution layer, so this
module deliberately avoids `Level2Contracts` and `Level2SavedFrame`; it therefore elaborates in
parallel with the inlined `decode` proof rather than after it. The compositions that consume these
steps live in `Level2WrapperProof`.
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

private theorem writeSavedS1 (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 9#5) value) state
      { state with regs := state.regs.insert x9 value } () := by
  have index : (Sail.BitVec.toNatInt (9#5 : BitVec 5)).toNat = 9 := rfl
  unfold Runs
  simp only [wX_bits, wX, index, regval_into_reg, PreSail.writeReg, EStateM.run,
    EStateM.bind, EStateM.modifyGet, EStateM.instMonad, MonadState.modifyGet,
    MonadStateOf.modifyGet, modify]
  rw [if_pos (by decide)]
  exact xreg_write_callback_run _ _ _

private theorem writeSavedS0 (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 8#5) value) state
      { state with regs := state.regs.insert x8 value } () := by
  have index : (Sail.BitVec.toNatInt (8#5 : BitVec 5)).toNat = 8 := rfl
  unfold Runs
  simp only [wX_bits, wX, index, regval_into_reg, PreSail.writeReg, EStateM.run,
    EStateM.bind, EStateM.modifyGet, EStateM.instMonad, MonadState.modifyGet,
    MonadStateOf.modifyGet, modify]
  rw [if_pos (by decide)]
  exact xreg_write_callback_run _ _ _

/-- Exact post-state of an emitted aligned eight-byte stack store. -/
def wrapperAfterDwordStore (state : State) (pc retired target data : BitVec 64) : State :=
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc
  tryStepControlFlowAfterRetired
    (afterWriteBytes (width := 8) executeState target.toNat data)
    (Sail.BitVec.addInt pc 4) retired

/-- Shared Sail execution for the wrapper's stack stores. The concrete caller fixes the ELF word,
decoded source register, immediate, live register values, and exact writable stack address.

This is now only the wrapper-specific *shape* of a width-eight store — base register pinned to `sp`,
conclusion in `wrapperAfterDwordStore` — over the shared store class: `decoderStoreAccess` supplies
the machine side and `decoderStoreStepOfExecute` the retirement, exactly as they do for
`decoderStoreDwordStep`. It keeps its signature because the four wrapper stores below reach it
through `wrapper_stack_store_step`; a site that needs neither `sp` pinned nor a
`wrapperAfterDwordStore` conclusion should call `decoderStoreDwordStep` directly. -/
theorem wrapper_dword_store_step {instructionPcs : BitVec 64 → Prop}
    {machineArgs : DecoderMachineArgs} {baseState state : State}
    (machine : DecoderMachinePre instructionPcs machineArgs baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc : BitVec 64) (pcIn : DecoderFetchPc instructionPcs pc)
    (atPc : state.regs.get? PC = some pc)
    (byte0 byte1 byte2 byte3 : BitVec 8) (immediate : BitVec 12)
    (source : regidx) (stackBits data target : BitVec 64)
    (stackValue : state.regs.get? x2 = some stackBits)
    (dataAtExecute : Runs (rX_bits source)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) data)
    (targetEq : stackBits + sign_extend immediate = target)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr target) 8 = true)
    (allowed : DecoderAccessRange DecoderWritableByte target 8)
    (fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      byte0 byte1 byte2 byte3)
    (baseEncoding : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.STORE (immediate, source, .Regidx 2#5, 8))) :
    ∃ retired, Runs (try_step stepNo false) state
      (wrapperAfterDwordStore state pc retired target data) false := by
  obtain ⟨mstatusBits, mstatusRead, privilege, mprvDisabled, addressRun, physical, storeNoMMIO⟩ :=
    decoderStoreAccess machine agree pc 2#5 immediate 8 stackBits target
      (readStackPointer _ stackBits
        (((stepPremiseState_writes state pc).get x2 (by decide)).trans stackValue))
      targetEq allowed aligned
  exact decoderStoreStepOfExecute machine agree retiredPresent stepNo pc pcIn atPc
    byte0 byte1 byte2 byte3 (.STORE (immediate, source, .Regidx 2#5, 8)) target.toNat 8 data
    fetchBytes baseEncoding decode
    (execute_STORE_dword_run _ _ source (.Regidx 2#5) immediate target mstatusBits data
      mstatusRead privilege mprvDisabled dataAtExecute addressRun aligned physical storeNoMMIO
      (writeBytes_run_exact _ target.toNat data))

/-- The write set of an emitted stack store: exactly the `try_step` bookkeeping, by
`storeRetirement_writes`. The five observations below are all readings of this one fact -- at one
register, at either preserved predicate, at `PC`, at `minstret`. -/
theorem wrapperAfterDwordStore_writes (state : State) (pc retired target data : BitVec 64) :
    WritesOnlyRegs stepBookkeeping state (wrapperAfterDwordStore state pc retired target data) :=
  storeRetirement_writes state pc (Sail.BitVec.addInt pc 4) retired target.toNat (width := 8) data

theorem wrapperAfterDwordStore_agree (state : State) (pc retired target data : BitVec 64) :
    Agree decoderPreserved state (wrapperAfterDwordStore state pc retired target data) :=
  (wrapperAfterDwordStore_writes state pc retired target data).agree
    (platformPreserved_disjoint.weaken (fun _ preserved => preserved.2))

theorem wrapperAfterDwordStore_platformAgree (state : State)
    (pc retired target data : BitVec 64) :
    Agree platformPreserved state (wrapperAfterDwordStore state pc retired target data) :=
  (wrapperAfterDwordStore_writes state pc retired target data).agree platformPreserved_disjoint

theorem wrapperAfterDwordStore_retired (state : State) (pc retired target data : BitVec 64) :
    RetiredCounterPresent (wrapperAfterDwordStore state pc retired target data) :=
  tryStepControlFlowAfterRetired_retired_present _ _ retired

theorem wrapperAfterDwordStore_register (state : State) (pc retired target data : BitVec 64)
    (register : Register) (notPc : PC ≠ register) (notNextPc : nextPC ≠ register)
    (notIncrement : minstret_increment ≠ register) (notRetired : minstret ≠ register) :
    (wrapperAfterDwordStore state pc retired target data).regs.get? register =
      state.regs.get? register :=
  (wrapperAfterDwordStore_writes state pc retired target data).get register
    (fun written => written.elim (fun h => notPc h.symm) (fun written => written.elim
      (fun h => notNextPc h.symm) (fun written => written.elim (fun h => notRetired h.symm)
        (fun h => notIncrement h.symm))))

theorem wrapperAfterDwordStore_pc (state : State) (pc retired target data : BitVec 64) :
    (wrapperAfterDwordStore state pc retired target data).regs.get? PC =
      some (Sail.BitVec.addInt pc 4) :=
  Elfling.tryStepControlFlowAfterRetired_pc _ _ retired

theorem canonicalStack_not_fileByte {address : Nat}
    (stack : canonicalContractParams.env.stack address) :
    canonicalContractParams.env.image.readFileByte? address = none := by
  simp only [canonicalContractParams, canonicalEnvironment] at stack ⊢
  cases read : Artifacts.programImage.readFileByte? address with
  | none => rfl
  | some byte =>
      exact False.elim (canonicalStack_above_loaded address
        (Nat.lt_trans (file_addr_lt read) (by decide)) stack)

theorem wrapperAfterDwordStore_code (state : State) (pc retired target data : BitVec 64)
    (stack : ∀ index, index < 8 →
      canonicalContractParams.env.stack (target.toNat + index))
    (code : canonicalContractParams.env.CodeIntact state) :
    canonicalContractParams.env.CodeIntact
      (wrapperAfterDwordStore state pc retired target data) := by
  have notFile : ∀ index : Fin 8,
      canonicalContractParams.env.image.readFileByte? (target.toNat + index.val) = none :=
    fun index => canonicalStack_not_fileByte (stack index.val index.isLt)
  have written := fileBytesMatchMemory_afterWriteBytes canonicalContractParams.env.image
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
    target.toNat data notFile
    (by simpa [coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code)
  simpa [wrapperAfterDwordStore, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]
    using written

/-- Exact state after the first emitted frame decrement, `addi sp, sp, -0x7f0`. -/
def wrapperAfterFirstFrameDecrement (state : State) (retired stackAtEntry : BitVec 64) : State :=
  afterRegisterWrite state (BitVec.ofNat 64 0x102b0) retired x2
    (iTypeResult .ADDI 0x810#12 stackAtEntry)

/-- The first frame decrement writes `x2`, so memory is the memory it was handed. -/
@[grind =] theorem wrapperAfterFirstFrameDecrement_mem (state : State)
    (retired stackAtEntry : BitVec 64) :
    (wrapperAfterFirstFrameDecrement state retired stackAtEntry).mem = state.mem := rfl

theorem wrapper_first_frame_decrement_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x81010113 : BitVec 32)) state state
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

theorem wrapper_save_link_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102b4)
      0x23#8 0x34#8 0x11#8 0x7e#8 :=
  fetchInstruction state 0x102b4 0x23 0x34 0x11 0x7e
    (by exact Contracts.canonicalCodeIntact_image code)

theorem wrapper_save_link_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x23#8 0x34#8 0x11#8 0x7e#8)) state state
      (.STORE (0x7e8#12, .Regidx 1#5, .Regidx 2#5, 8)) := by
  decode_run

theorem wrapper_saved_link_target (stackBase : Nat) :
    BitVec.ofNat 64 (stackBase + 0x230) + sign_extend (0x7e8#12) =
      BitVec.ofNat 64 (stackBase + 0xa18) := by
  rw [show BitVec.ofNat 64 (stackBase + 0x230) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x230 by rw [← BitVec.ofNat_add]]
  rw [show BitVec.ofNat 64 (stackBase + 0xa18) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0xa18 by rw [← BitVec.ofNat_add]]
  rw [show sign_extend (0x7e8#12) = (0x7e8#64) by decide]
  bv_decide

theorem wrapper_save_s0_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102b8)
      0x23#8 0x30#8 0x81#8 0x7e#8 :=
  fetchInstruction state 0x102b8 0x23 0x30 0x81 0x7e
    (by exact Contracts.canonicalCodeIntact_image code)

theorem wrapper_save_s1_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102bc)
      0x23#8 0x3c#8 0x91#8 0x7c#8 :=
  fetchInstruction state 0x102bc 0x23 0x3c 0x91 0x7c
    (by exact Contracts.canonicalCodeIntact_image code)

theorem wrapper_save_s2_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102c0)
      0x23#8 0x38#8 0x21#8 0x7d#8 :=
  fetchInstruction state 0x102c0 0x23 0x38 0x21 0x7d
    (by exact Contracts.canonicalCodeIntact_image code)

theorem wrapper_save_s0_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x23#8 0x30#8 0x81#8 0x7e#8)) state state
      (.STORE (0x7e0#12, .Regidx 8#5, .Regidx 2#5, 8)) := by
  decode_run

theorem wrapper_save_s1_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x23#8 0x3c#8 0x91#8 0x7c#8)) state state
      (.STORE (0x7d8#12, .Regidx 9#5, .Regidx 2#5, 8)) := by
  decode_run

theorem wrapper_save_s2_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x23#8 0x38#8 0x21#8 0x7d#8)) state state
      (.STORE (0x7d0#12, .Regidx 18#5, .Regidx 2#5, 8)) := by
  decode_run

theorem wrapper_saved_s0_target (stackBase : Nat) :
    BitVec.ofNat 64 (stackBase + 0x230) + sign_extend (0x7e0#12) =
      BitVec.ofNat 64 (stackBase + 0xa10) := by
  rw [show BitVec.ofNat 64 (stackBase + 0x230) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x230 by rw [← BitVec.ofNat_add]]
  rw [show BitVec.ofNat 64 (stackBase + 0xa10) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0xa10 by rw [← BitVec.ofNat_add]]
  rw [show sign_extend (0x7e0#12) = (0x7e0#64) by decide]
  bv_decide

theorem wrapper_saved_s1_target (stackBase : Nat) :
    BitVec.ofNat 64 (stackBase + 0x230) + sign_extend (0x7d8#12) =
      BitVec.ofNat 64 (stackBase + 0xa08) := by
  rw [show BitVec.ofNat 64 (stackBase + 0x230) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x230 by rw [← BitVec.ofNat_add]]
  rw [show BitVec.ofNat 64 (stackBase + 0xa08) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0xa08 by rw [← BitVec.ofNat_add]]
  rw [show sign_extend (0x7d8#12) = (0x7d8#64) by decide]
  bv_decide

theorem wrapper_saved_s2_target (stackBase : Nat) :
    BitVec.ofNat 64 (stackBase + 0x230) + sign_extend (0x7d0#12) =
      BitVec.ofNat 64 (stackBase + 0xa00) := by
  rw [show BitVec.ofNat 64 (stackBase + 0x230) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x230 by rw [← BitVec.ofNat_add]]
  rw [show BitVec.ofNat 64 (stackBase + 0xa00) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0xa00 by rw [← BitVec.ofNat_add]]
  rw [show sign_extend (0x7d0#12) = (0x7d0#64) by decide]
  bv_decide

theorem wrapper_final_frame_decrement_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0xdd010113 : BitVec 32)) state state
      (.ITYPE (0xdd0#12, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
  decode_run

theorem wrapper_final_frame_decrement_value (stackBase : Nat) :
    iTypeResult .ADDI 0xdd0#12 (BitVec.ofNat 64 (stackBase + 0x230)) =
      BitVec.ofNat 64 stackBase := by
  rw [show BitVec.ofNat 64 (stackBase + 0x230) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 0x230 by rw [← BitVec.ofNat_add]]
  unfold iTypeResult
  rw [show sign_extend (0xdd0#12) = (0xfffffffffffffdd0#64) by decide]
  bv_decide

theorem wrapper_preserve_length_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x00058493 : BitVec 32)) state state
      (.ITYPE (0#12, .Regidx 11#5, .Regidx 9#5, .ADDI)) := by
  decode_run

theorem wrapper_globals_page_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x04205597 : BitVec 32)) state state
      (.UTYPE (0x04205#20, .Regidx 11#5, .AUIPC)) := by
  decode_run

theorem wrapper_globals_address_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0xd5458913 : BitVec 32)) state state
      (.ITYPE (0xd54#12, .Regidx 11#5, .Regidx 18#5, .ADDI)) := by
  decode_run

theorem wrapper_attempted_load_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102d4)
      0x83#8 0x45#8 0x09#8 0x00#8 :=
  fetchInstruction state 0x102d4 0x83 0x45 0x09 0x00
    (by exact Contracts.canonicalCodeIntact_image code)

theorem wrapper_attempted_load_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x83#8 0x45#8 0x09#8 0x00#8)) state state
      (.LOAD (0#12, .Regidx 18#5, .Regidx 11#5, true, 1)) := by
  decode_run

def wrapperAfterFreshBranch (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x102d8) (BitVec.ofNat 64 0x102e8))
    (BitVec.ofNat 64 0x102e8) retired

/-- The taken fresh-flag branch touches no memory. -/
@[grind =] theorem wrapperAfterFreshBranch_mem (state : State) (retired : BitVec 64) :
    (wrapperAfterFreshBranch state retired).mem = state.mem := rfl

/-- The taken fresh-flag branch is a jump, so it writes exactly the bookkeeping. -/
theorem wrapperAfterFreshBranch_writes (state : State) (retired : BitVec 64) :
    WritesOnlyRegs stepBookkeeping state (wrapperAfterFreshBranch state retired) :=
  jumpRetirement_writes state (BitVec.ofNat 64 0x102d8) (BitVec.ofNat 64 0x102e8) retired

theorem wrapperAfterFreshBranch_register (state : State) (retired : BitVec 64)
    (register : Register) (notPc : PC ≠ register) (notNextPc : nextPC ≠ register)
    (notIncrement : minstret_increment ≠ register) (notRetired : minstret ≠ register) :
    (wrapperAfterFreshBranch state retired).regs.get? register = state.regs.get? register :=
  (wrapperAfterFreshBranch_writes state retired).get register
    (fun written => written.elim (fun h => notPc h.symm) (fun written => written.elim
      (fun h => notNextPc h.symm) (fun written => written.elim (fun h => notRetired h.symm)
        (fun h => notIncrement h.symm))))

theorem wrapperAfterFreshBranch_platformAgree (state : State) (retired : BitVec 64) :
    Agree platformPreserved state (wrapperAfterFreshBranch state retired) :=
  (wrapperAfterFreshBranch_writes state retired).agree platformPreserved_disjoint

theorem wrapperAfterFreshBranch_retired (state : State) (retired : BitVec 64) :
    RetiredCounterPresent (wrapperAfterFreshBranch state retired) :=
  tryStepControlFlowAfterRetired_retired_present _ _ retired

theorem wrapper_fresh_branch_fetch (state : State)
    (code : canonicalContractParams.env.CodeIntact state) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x102d8)
      0x63#8 0x88#8 0x05#8 0x00#8 :=
  fetchInstruction state 0x102d8 0x63 0x88 0x05 0x00
    (by exact Contracts.canonicalCodeIntact_image code)

theorem wrapper_fresh_branch_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x63#8 0x88#8 0x05#8 0x00#8)) state state
      (.BTYPE (0x10#13, .Regidx 0#5, .Regidx 11#5, .BEQ)) := by
  decode_run

theorem wrapper_save_input_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x00050413 : BitVec 32)) state state
      (.ITYPE (0#12, .Regidx 10#5, .Regidx 8#5, .ADDI)) := by
  decode_run

theorem wrapper_attempted_value_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x00100513 : BitVec 32)) state state
      (.ITYPE (1#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) := by
  decode_run

/-- The configured decoder machine supplies exactly the ordinary-step premises needed at a wrapper
or inline instruction. In particular, this adapter does not manufacture a return-sentinel fact. -/
theorem decoderInstructionStepPlatform {instructionPcs : BitVec 64 → Prop}
    {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre instructionPcs machineArgs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (pc : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    (pcIn : DecoderFetchPc instructionPcs (BitVec.ofNat 64 pc)) : InstructionStepPlatform state pc := by
  have current := machine.mono agree retired
  obtain ⟨fetch, noMMIO, interrupts, notExpected⟩ :=
    current.platform state (BitVec.ofNat 64 pc) (Agree.refl state) atPc pcIn
  obtain ⟨seccfgBits, seccfgRead, -⟩ := current.mseccfg
  exact
    { normal := current.normal
      fetch := fetch
      fetchNoMMIO := noMMIO
      interrupts := interrupts
      notExpected := notExpected
      seccfgRead := ⟨seccfgBits, seccfgRead⟩
      retired := retired
      code := by exact Contracts.canonicalCodeIntact_image code }

def wrapperAfterDecodeFirstErrorBranch (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10324) (BitVec.ofNat 64 0x1037c))
    (BitVec.ofNat 64 0x1037c) retired

/-- The taken decode-error branch touches no memory. -/
@[grind =] theorem wrapperAfterDecodeFirstErrorBranch_mem (state : State) (retired : BitVec 64) :
    (wrapperAfterDecodeFirstErrorBranch state retired).mem = state.mem := rfl

/-- Retire the first `decode` segment's real outgoing `bne a0, x0, 0x1037c`. Every internal error
tag is nonzero, so the checked edge must enter the wrapper's retry dispatch. -/
theorem wrapper_decode_first_error_branch_step (stepNo : Nat) (args : DecodeInlineArgs)
    (before state : State) (pre : DecodeInlinePre args before)
    (frame : DecodeInlineMachinePost before state) (error : Contracts.DecodeError)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10324))
    (tagRead : state.regs.get? x10 = some
      (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)))) :
    ∃ retired,
      Runs (try_step stepNo false) state (wrapperAfterDecodeFirstErrorBranch state retired) false ∧
      (wrapperAfterDecodeFirstErrorBranch state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x1037c) := by
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact frame.code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10324) 0x63#8 0x1c#8 0x05#8 0x04#8 :=
    fetchInstruction state 0x10324 0x63 0x1c 0x05 0x04 image
  have machine := pre.machine.mono frame.agree frame.retiredCounter
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x10324) atPc (fetchPc _) _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal (Agree.refl state) frame.retiredCounter
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ :=
    counters
  have wordEq : fetchWord 0x63#8 0x1c#8 0x05#8 0x04#8 =
      (0x04051c63 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x1c#8 0x05#8 0x04#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x58#13, .Regidx 0#5, .Regidx 10#5, .BNE)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10324)
  have tagAtExecute : executeState.regs.get? x10 = some
      (BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error))) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10324)).get x10 (by decide)).trans tagRead
  have tagNonzero : BitVec.ofNat 64 (Contracts.decodeInternalResultTag (.error error)) ≠ 0#64 := by
    cases error <;> simp [Contracts.decodeInternalResultTag]
  have condition : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 10#5) .BNE)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState _ tagAtExecute) ?_
    refine Runs.bind (rX_x0_run executeState) ?_
    rw [bne_iff_ne.mpr tagNonzero]
    rfl
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x10324) :=
    ((coreControlFlowNextState_writes (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10324)).get PC (by decide)).trans
        (pc_afterIncrement state (BitVec.ofNat 64 0x10324) atPc)
  have targetEq : BitVec.ofNat 64 0x10324 + sign_extend (m := 64) (0x58#13) =
      BitVec.ofNat 64 0x1037c := by decide
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      state.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match read : state.regs.get? misa with
    | none => simp [read] at normalMisa
    | some bits => exact ⟨bits, rfl, by simpa [read] using normalMisa⟩
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x10324)
    misaBits misaRead
  have run := tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x10324)
    (BitVec.ofNat 64 0x10324) retired (0x58#13) (.Regidx 0#5) (.Regidx 10#5) .BNE
    inhibit config 0x63#8 0x1c#8 0x05#8 0x04#8 (_get_Misa_C misaBits == 1#1)
    fetch noMMIO fetched interrupts (by unfold BaseInstructionEncoding; decide) decode
    notExpected condition (readReg_run executeState PC _ pcAtExecute)
    (by decide) (by decide) zca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead
  refine ⟨retired, ?_, ?_⟩
  · simpa [wrapperAfterDecodeFirstErrorBranch, targetEq] using run
  · exact Elfling.tryStepControlFlowAfterRetired_pc _ _ _

/-- The taken error branch out of the first `decode` segment is a jump: bookkeeping only. -/
theorem wrapperAfterDecodeFirstErrorBranch_writes (state : State) (retired : BitVec 64) :
    WritesOnlyRegs stepBookkeeping state (wrapperAfterDecodeFirstErrorBranch state retired) :=
  jumpRetirement_writes state (BitVec.ofNat 64 0x10324) (BitVec.ofNat 64 0x1037c) retired

theorem wrapperAfterDecodeFirstErrorBranch_register (state : State) (retired : BitVec 64)
    (register : Register) (notPc : PC ≠ register) (notNextPc : nextPC ≠ register)
    (notIncrement : minstret_increment ≠ register) (notRetired : minstret ≠ register) :
    (wrapperAfterDecodeFirstErrorBranch state retired).regs.get? register =
      state.regs.get? register :=
  (wrapperAfterDecodeFirstErrorBranch_writes state retired).get register
    (fun written => written.elim (fun h => notPc h.symm) (fun written => written.elim
      (fun h => notNextPc h.symm) (fun written => written.elim (fun h => notRetired h.symm)
        (fun h => notIncrement h.symm))))

theorem wrapperAfterDecodeFirstErrorBranch_agree (state : State) (retired : BitVec 64) :
    Agree decoderPreserved state (wrapperAfterDecodeFirstErrorBranch state retired) :=
  (wrapperAfterDecodeFirstErrorBranch_writes state retired).agree
    (platformPreserved_disjoint.weaken (fun _ preserved => preserved.2))

theorem wrapperAfterDecodeFirstErrorBranch_retired (state : State) (retired : BitVec 64) :
    RetiredCounterPresent (wrapperAfterDecodeFirstErrorBranch state retired) :=
  tryStepControlFlowAfterRetired_retired_present _ _ retired

theorem wrapperAfterDecodeFirstErrorBranch_code (state : State) (retired : BitVec 64)
    (code : canonicalContractParams.env.CodeIntact state) :
    canonicalContractParams.env.CodeIntact (wrapperAfterDecodeFirstErrorBranch state retired) := by
  simpa [wrapperAfterDecodeFirstErrorBranch, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
    tryStepControlFlowAfterIncrement] using code

/-- Execute the wrapper-owned `li a1, 2` between the two selected `decode` segments. -/
theorem wrapper_retry_reason_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1037c)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1037c) retired x11 (BitVec.ofNat 64 2)) false := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine agree
  have resultEq : iTypeResult .ADDI 0x002#12 (0#64) = BitVec.ofNat 64 2 := by decide
  exact decoderITypeStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x1037c 0x93 0x05 0x20 0x00 0x002#12 0#5 11#5 .ADDI atPc
    (rX_x0_run _) (by rw [resultEq]; exact wX_x11_run _ _)

end BinaryFv.Zesu.MachineExecution
