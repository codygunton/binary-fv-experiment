import BinaryFv.Zesu.DecodedValue.StatelessInput
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps

/-! # Decoder loads backed by little-endian bit-vector representations -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.DecodedValue BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open PreSail LeanRV64DExecutable.Functions Register

/-- An aligned Machine-mode double-word read from a `BitVectorLERep` memory value.

The representation supplies the exact bytes, while `DecoderMachinePre.dataAccess` supplies the
configured PMA and no-MMIO facts for the explicit readable range.  This is the data premise of
`decoderLoadStepOfDecoderAgree`; that instruction-class theorem owns fetch, decode, and retirement. -/
theorem decoderDwordReadOfBitVectorLERep {instructionPcs : BitVec 64 → Prop}
    {margs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre instructionPcs margs base)
    (agree : Agree decoderPreserved base state)
    (pc : BitVec 64) (imm : BitVec 12) (rs : regidx) (value stack address : BitVec 64)
    (stackRead : Runs (rX_bits rs)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) stack)
    (targetEq : stack + sign_extend (m := 64) imm = address)
    (representationBase : Nat) (baseEq : representationBase = address.toNat)
    (representation : BitVectorLERep state representationBase value)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (readable : DecoderAccessRange (DecoderReadableByte margs) address 8) :
    Runs (vmem_read rs (sign_extend (m := 64) imm) 8
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
  have addressRun := get_transformed_data_addr_machine_data_run .load executeState rs 8 stack
    (sign_extend (m := 64) imm) mstatusBits mseccfgBits (by simpa [executeState] using stackRead)
    mstatusAtExecute privilege mprvDisabled
    ((executeAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead)
    pmmDisabled
  obtain ⟨physical, loadNoMMIO⟩ := machine.dataAccess.load executeState address 8 executeAgree
    readable (by simpa [is_aligned_paddr, is_aligned_vaddr] using aligned)
  have memoryBytes : ∀ index (bound : index < (BinaryFv.RiscV.Sep.leBytes 8 value).length),
      executeState.mem.get? (address.toNat + index) =
        some (getElem (BinaryFv.RiscV.Sep.leBytes 8 value) index bound) := by
    intro index bound
    rw [← baseEq]
    simpa [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert] using representation.leBytes index (by
        simpa only [BinaryFv.RiscV.Sep.leBytes_length] using bound)
  have hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data)
      page_based_mem_type.PBMT_PMA (physaddr.Physaddr address) 8 false false false)
      executeState executeState (Sail.Ok value) := by
    have read := mem_read_load_run executeState address mstatusBits
      (BinaryFv.RiscV.Sep.leBytes 8 value) mstatusAtExecute privilege mprvDisabled memoryBytes
      physical loadNoMMIO
    rwa [show BinaryFv.RiscV.Sep.leWord (BinaryFv.RiscV.Sep.leBytes 8 value) = value from by
      simpa using BinaryFv.RiscV.Sep.leWord_leBytes 8 value] at read
  exact vmem_read_dword_run executeState rs (sign_extend (m := 64) imm) address mstatusBits value
    mstatusAtExecute privilege mprvDisabled (by simpa [targetEq] using addressRun) aligned hread

end BinaryFv.Zesu.MachineExecution
