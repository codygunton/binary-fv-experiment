import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.Instruction.Decode
import BinaryFv.RiscV.Step.ConfiguredMachine
import BinaryFv.RiscV.Step.TryStepStackAddiMemory
import BinaryFv.Ssz.Generated.ProgramImage
import BinaryFv.Ssz.MachineContract

/-!
# Concrete Level 0 instructions of the SSZ endpoint

Each theorem below instantiates a target-independent instruction-class lemma with a word named by
the generated production-ELF artifact. No `try_step` execution fact is assumed.
-/

namespace BinaryFv.Ssz

open BinaryFv.Binary
open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

/-- The exact generated Level 0 instruction addresses. -/
def mainGluePcs (pc : BitVec 64) : Prop := pcInRanges Generated.mainGluePcRanges pc

/-- Production `0x14cb0: addi sp, sp, -896`, including generated fetch and retirement. -/
theorem main_stack_allocate_step (stepNo : Nat) (state : State) (stackValue : BitVec 64)
    (configured : ConfiguredMachinePre mainGluePcs state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 Generated.mainEntry))
    (stackRead : state.regs.get? x2 = some stackValue)
    (loaded : Generated.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepStackAddiAfterRetired state (BitVec.ofNat 64 Generated.mainEntry)
        (BitVec.ofNat 12 0xc80) stackValue retired) false := by
  obtain ⟨retired, counters⟩ := configured.counters
  obtain ⟨platform, noMMIO, interrupts, notExpected⟩ :=
    configured.stepContext (BitVec.ofNat 64 Generated.mainEntry) atPc (by
      refine ⟨(0x14cb0, 0x14ccc), ?_, ?_, ?_⟩ <;> native_decide)
  have loadedAfter : Generated.programImage.fileBytesLoadedFaithfully
      (tryStepStackAddiAfterIncrement state).mem := by
    simpa [tryStepStackAddiAfterIncrement] using loaded
  have bytes := BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Generated.programImage
    (tryStepStackAddiAfterIncrement state) Generated.mainEntry (by native_decide) loadedAfter
    0x13 0x01 0x01 0xc8 (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have decode : Runs
      (ext_decode (fetchWord (0x13 : BitVec 8) (0x01 : BitVec 8) (0x01 : BitVec 8)
        (0xc8 : BitVec 8)))
      (tryStepStackAddiAfterIncrement state) (tryStepStackAddiAfterIncrement state)
      (.ITYPE (BitVec.ofNat 12 0xc80, stackPointer, stackPointer, .ADDI)) := by
    obtain ⟨seccfgBits, seccfgRead⟩ := configured.seccfgPresent
    have privilegeAfter : (tryStepStackAddiAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine := by
      calc
        _ = state.regs.get? cur_privilege := by
          simpa [tryStepStackAddiAfterIncrement] using
            writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
        _ = some Privilege.Machine := configured.normal.2.1
    have seccfgAfter : (tryStepStackAddiAfterIncrement state).regs.get? mseccfg =
        some seccfgBits := by
      calc
        _ = state.regs.get? mseccfg := by
          simpa [tryStepStackAddiAfterIncrement] using
            writeReg_read_unchanged state minstret_increment mseccfg true (by decide)
        _ = some seccfgBits := seccfgRead
    unfold Runs
    rw [extDecode_eq]
    simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports,
      bool_bit_backwards, PreSail.readReg, EStateM.run, Bind.bind, Pure.pure,
      Functor.map, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
      EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
      EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get,
      MonadStateOf.get, privilegeAfter, seccfgAfter, *]
    rfl
  have wordEq : fetchWord (0x13 : BitVec 8) (0x01 : BitVec 8) (0x01 : BitVec 8)
      (0xc8 : BitVec 8) = BitVec.ofNat 32 Generated.mainGlueWordAt14cb0 := by
    native_decide
  have stackAfterNext :
      (stackAddiNextState (tryStepStackAddiAfterIncrement state)
        (BitVec.ofNat 64 Generated.mainEntry)).regs.get? x2 = some stackValue := by
    calc
      _ = (tryStepStackAddiAfterIncrement state).regs.get? x2 := by
        simpa [stackAddiNextState] using
          writeReg_read_unchanged (tryStepStackAddiAfterIncrement state) nextPC x2
            (Sail.BitVec.addInt (BitVec.ofNat 64 Generated.mainEntry) 4) (by decide)
      _ = state.regs.get? x2 := by
        simpa [tryStepStackAddiAfterIncrement] using
          writeReg_read_unchanged state minstret_increment x2 true (by decide)
      _ = some stackValue := stackRead
  refine ⟨retired, tryStepStackAddiRetiresWithFetchMemory stepNo state
    (BitVec.ofNat 64 Generated.mainEntry) (BitVec.ofNat 12 0xc80) stackValue retired 0 0
    0x13 0x01 0x01 0xc8 platform noMMIO bytes interrupts ?_ decode notExpected stackAfterNext
    counters.1 counters.2.1 counters.2.2.1 counters.2.2.2.1 counters.2.2.2.2.1
    counters.2.2.2.2.2⟩
  rfl

end BinaryFv.Ssz
