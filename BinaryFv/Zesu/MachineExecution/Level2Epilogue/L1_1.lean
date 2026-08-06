import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.Zesu.MachineExecution.RegisterRuns
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.RiscV.Step.TryStepStackAddi
import BinaryFv.RiscV.Step.TryStepStackAddiMemory
import BinaryFv.Zesu.MachineExecution.OwnedPc

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

/-- Exact state after the first epilogue stack restoration at `0x10360`. -/
def wrapperAfterFirstStackRestore (state : State) (retired stack : BitVec 64) : State :=
  tryStepStackAddiAfterRetired state (BitVec.ofNat 64 0x10360) 0x230#12 stack retired

/-- The first stack restoration writes `x2`, so memory is the memory it was handed. -/
@[grind =] theorem wrapperAfterFirstStackRestore_mem (state : State) (retired stack : BitVec 64) :
    (wrapperAfterFirstStackRestore state retired stack).mem = state.mem := rfl

/-- An `addi sp, sp, imm` post-state *is* the generic register-write post-state at `x2`: both
insert `minstret_increment`, `nextPC`, `x2`, `PC` and `minstret`, in that order and with the same
values, so the two definitions are literally the same state.

Naming the identity is what lets the two epilogue stack restorations retire through the `ITYPE`
class lemma while keeping the `tryStepStackAddi…` post-state their consumers already destructure. -/
theorem tryStepStackAddiAfterRetired_eq_afterRegisterWrite (state : State) (pc : BitVec 64)
    (immediate : BitVec 12) (stackValue retired : BitVec 64) :
    tryStepStackAddiAfterRetired state pc immediate stackValue retired =
      afterRegisterWrite state pc retired x2 (stackValue + sign_extend (m := 64) immediate) :=
  rfl

/-- A `ld` writes its data unchanged: sign-extending a double word to 64 bits is the identity.
`Load.lean` proves the same fact, but privately, so the four `ld` sites below need their own copy to
match the `LOAD` class lemma's `extend_value` premise. -/
theorem extend_value_dword (v : BitVec (8 * 8)) : extend_value false v = v := by
  unfold extend_value
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

/-- The `vmem_read` one of the four real `ld` instructions in the wrapper epilogue performs: the
saved frame word at the load's effective address, read back through the machine's data-access
permission. Its only memory content premise is the corresponding `SavedWordBytes` conjunct of the
saved wrapper frame.

This is all that is left of the retirement lemma this module used to carry. That lemma had to
restate the entire `try_step` postlude — platform reads, counter reads, `tryStepFallThroughRetires`
and four framing facts about an abstract post-execute state — purely because `decoderLoadStep`
demanded `Agree platformPreserved`, which no wrapper-epilogue state can supply once the prologue's
`jalr` has clobbered `x1`. With `decoderLoadStepOfDecoderAgree` owning the retirement, only the
address translation and the memory content are still this module's business. -/
theorem wrapper_epilogue_saved_load_read {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state)
    (pc : BitVec 64) (imm : BitVec 12) (rs1 : regidx) (value stack address : BitVec 64)
    (stackRead : Runs (rX_bits rs1) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) stack)
    (targetEq : stack + sign_extend (m := 64) imm = address)
    (savedBase : Nat) (savedBaseEq : savedBase = address.toNat)
    (saved : SavedWordBytes state savedBase value)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (allowed : DecoderAccessRange (DecoderReadableByte machineArgs) address 8) :
    Runs (vmem_read rs1 (sign_extend (m := 64) imm) 8
        (MemoryAccessType.Load mem_payload.Data) false false false)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) (.Ok value) := by
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc
  have executeAgree : Agree decoderPreserved base executeState :=
    agree.trans (Agree.weaken (fun _ preserved => preserved.2) (agree_stepPremiseState state pc))
  obtain ⟨mstatusBits, mstatusRead, mprvDisabled⟩ := machine.mstatus
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := machine.mseccfg
  have mstatusAtExecute :=
    (executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead
  have privilege :=
    (executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      machine.normal.2.1
  have addressRun := get_transformed_data_addr_machine_load_run executeState rs1 stack
    (sign_extend (m := 64) imm) mstatusBits mseccfgBits (by simpa [executeState] using stackRead)
    mstatusAtExecute privilege mprvDisabled
    ((executeAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead)
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
  have hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data)
      page_based_mem_type.PBMT_PMA (physaddr.Physaddr address) 8 false false false)
      executeState executeState (Sail.Ok value) := by
    have read := mem_read_load_run executeState address mstatusBits
      (BinaryFv.RiscV.Sep.leBytes 8 value) mstatusAtExecute privilege mprvDisabled memoryBytes
      physical loadNoMMIO
    rwa [show BinaryFv.RiscV.Sep.leWord (BinaryFv.RiscV.Sep.leBytes 8 value) = value from by
      simpa using BinaryFv.RiscV.Sep.leWord_leBytes 8 value] at read
  exact vmem_read_dword_run executeState rs1 (sign_extend (m := 64) imm) address mstatusBits value
    mstatusAtExecute privilege mprvDisabled (by simpa [targetEq] using addressRun) aligned hread

end BinaryFv.Zesu.MachineExecution
