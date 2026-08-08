import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.DecodeInlineContract
import BinaryFv.Zesu.MachineExecution.MemcpyInstance

/-!
# Supplying the emitted `memcpy` from decoder machine premises

The inlined decoder and the emitted `memcpy` use different register frames, but they run on the
same configured machine. This file converts the decoder's platform and data-access premises into
the narrower premises required by the proved `memcpy` body. The caller still proves the concrete
source and destination intervals; no copy result or execution trace is assumed here.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.RiscV BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open PreSail LeanRV64DExecutable.Functions Register

private theorem rX_bits_x14_run (state : State) (value : BitVec 64)
    (read : state.regs.get? x14 = some value) :
    Runs (rX_bits (.Regidx 14#5)) state state value := by
  have index : (Sail.BitVec.toNatInt (14#5)).toNat = 14 := by decide
  unfold Runs
  simp [rX_bits, rX, index, read, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
    regval_from_reg]

private theorem decoderAgree_of_memcpyStable {before after : State}
    (stable : StableAgree before after) : Agree decoderPreserved before after := by
  intro register preserved
  apply stable register
  rcases preserved with ⟨notLink, platform⟩
  simp only [NonW]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro equal; subst register; simp [platformPreserved] at platform
  · intro equal; subst register; simp [platformPreserved] at platform
  · intro equal; subst register; simp [platformPreserved] at platform
  · intro equal; subst register; simp [platformPreserved] at platform
  · intro equal; subst register; simp [platformPreserved] at platform
  · intro equal; subst register; simp [platformPreserved] at platform
  · intro equal; subst register; simp [platformPreserved] at platform

/-- Convert the enclosing decoder machine premise to the exact machine interface used by the
proved emitted `memcpy`. The range hypotheses are ordinary, non-wrapping byte intervals. -/
theorem memcpyMachinePre_of_decoder
    {parentPcs : BitVec 64 → Prop} {decoderArgs : DecoderMachineArgs}
    (args : CopyArgs) (state : State)
    (machine : DecoderMachinePre parentPcs decoderArgs state)
    (bodyWithinParent : ∀ pc, IsBodyPc pc → parentPcs pc)
    (entry : state.regs.get? PC = some (BitVec.ofNat 64 0x13eb8))
    (returnAddress : ∃ address : BitVec 64,
      state.regs.get? x1 = some address ∧ Sail.BitVec.access address 1 = 0#1)
    (imageIsZesu : canonicalContractParams.env.image = Artifacts.programImage)
    (lengthFits : args.length < 2 ^ 64)
    (sourceAddressFits : args.source < 2 ^ 64)
    (destinationAddressFits : args.destination < 2 ^ 64)
    (sourceFits : args.source + args.length ≤ 2 ^ 64)
    (destinationFits : args.destination + args.length ≤ 2 ^ 64)
    (destinationNotFile : ∀ index, index < args.length →
      canonicalContractParams.env.image.readFileByte? (args.destination + index) = none)
    (destinationNotAllocatorState : ∀ address, canonicalContractParams.env.allocatorState address →
      address < args.destination ∨ args.destination + args.length ≤ address)
    (sourceReadable : ∀ index, index < args.length →
      DecoderReadableByte decoderArgs (args.source + index))
    (destinationWritable : ∀ index, index < args.length →
      DecoderWritableByte (args.destination + index)) :
    MemcpyMachinePre canonicalContractParams.env args state := by
  obtain ⟨mstatusBits, mstatusRead, mprvDisabled⟩ := machine.mstatus
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := machine.mseccfg
  have platform : AbstractPlatform state := by
    intro next pc stable atPc bodyPc
    have aligned : pc.toNat % 4 = 0 := by
      simp only [IsBodyPc] at bodyPc
      rcases bodyPc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact machine.platform next pc (decoderAgree_of_memcpyStable stable) atPc
      ⟨bodyWithinParent pc bodyPc, aligned⟩
  have landingPad : AbstractElp state := by
    intro next register valid stable
    exact machine.landingPad next register trivial (decoderAgree_of_memcpyStable stable)
  have dataAccess : AbstractDataAccess (BitVec.ofNat 64 args.length)
      (BitVec.ofNat 64 args.destination) (BitVec.ofNat 64 args.source) state := by
    intro index next indexBound stable
    have indexLt : index < args.length := by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthFits] using indexBound
    have sourceIndexFits : args.source + index < 2 ^ 64 := by omega
    have destinationIndexFits : args.destination + index < 2 ^ 64 := by omega
    have sourceAddress :
        (BitVec.ofNat 64 args.source + BitVec.ofNat 64 index).toNat = args.source + index := by
      rw [windowAddr_toNat (BitVec.ofNat 64 args.source) index]
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sourceAddressFits]
      · simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sourceAddressFits] using sourceIndexFits
    have destinationAddress :
        (BitVec.ofNat 64 args.destination + BitVec.ofNat 64 index).toNat =
          args.destination + index := by
      rw [windowAddr_toNat (BitVec.ofNat 64 args.destination) index]
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt destinationAddressFits]
      · simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt destinationAddressFits] using
          destinationIndexFits
    have decoderAgree := decoderAgree_of_memcpyStable stable
    have currentPrivilege : next.regs.get? cur_privilege = some Privilege.Machine :=
      (decoderAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
        machine.normal.2.1
    have nextMstatus : next.regs.get? mstatus = some mstatusBits :=
      (decoderAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead
    have nextMseccfg : next.regs.get? mseccfg = some mseccfgBits :=
      (decoderAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead
    constructor
    · intro sourceRegister
      have transformed := get_transformed_data_addr_machine_load_run next (.Regidx 13#5)
        (BitVec.ofNat 64 args.source + BitVec.ofNat 64 index) 0 mstatusBits mseccfgBits
        (rX_bits_x13_run next _ sourceRegister) nextMstatus currentPrivilege mprvDisabled
        nextMseccfg pmmDisabled
      have allowed : DecoderAccessRange (DecoderReadableByte decoderArgs)
          (BitVec.ofNat 64 args.source + BitVec.ofNat 64 index) 1 := by
        refine ⟨by decide, ?_, ?_⟩
        · rw [sourceAddress]
          omega
        intro offset offsetBound
        have offsetZero : offset = 0 := by omega
        subst offset
        simpa [sourceAddress] using sourceReadable index indexLt
      obtain ⟨physical, noMMIO⟩ := machine.dataAccess.load next
        (BitVec.ofNat 64 args.source + BitVec.ofNat 64 index) 1 decoderAgree allowed
        (by simp [is_aligned_paddr])
      exact ⟨by simpa using transformed, physical, noMMIO⟩
    · intro destinationRegister
      have transformed := get_transformed_data_addr_machine_store_run next (.Regidx 14#5) 1
        (BitVec.ofNat 64 args.destination + BitVec.ofNat 64 index) 0 mstatusBits mseccfgBits
        (rX_bits_x14_run next _ destinationRegister) nextMstatus currentPrivilege mprvDisabled
        nextMseccfg pmmDisabled
      have allowed : DecoderAccessRange DecoderWritableByte
          (BitVec.ofNat 64 args.destination + BitVec.ofNat 64 index) 1 := by
        refine ⟨by decide, ?_, ?_⟩
        · rw [destinationAddress]
          omega
        intro offset offsetBound
        have offsetZero : offset = 0 := by omega
        subst offset
        simpa [destinationAddress] using destinationWritable index indexLt
      obtain ⟨physical, noMMIO⟩ := machine.dataAccess.store next
        (BitVec.ofNat 64 args.destination + BitVec.ofNat 64 index) 1 decoderAgree allowed
        (by simp [is_aligned_paddr])
      exact ⟨by simpa using transformed, physical, noMMIO⟩
  exact
    { normal := machine.normal
      entry
      returnAddress
      currentPrivilege := machine.normal.2.1
      mstatus := ⟨mstatusBits, mstatusRead, mprvDisabled⟩
      mseccfg := ⟨mseccfgBits, mseccfgRead⟩
      inhibit := ⟨0, machine.normal.2.2.2.2.2.2.2.2.1, by decide⟩
      counterConfig := ⟨0, machine.normal.2.2.2.2.2.2.2.2.2.1, by decide⟩
      hartActive := machine.normal.1
      retiredCounter := machine.retiredCounter
      imageIsZesu
      lengthFits
      sourceAddressFits
      destinationAddressFits
      sourceFits
      destinationFits
      destinationNotFile
      destinationNotAllocatorState
      platform
      dataAccess
      landingPad }

end BinaryFv.Zesu.MachineExecution
