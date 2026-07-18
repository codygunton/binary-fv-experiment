import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.SSZ.Zesu.Analysis.Primitives

namespace BinaryFv.SSZ.Zesu.Proof

open BinaryFv BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open PreSail LeanRV64DExecutable.Functions Register

private macro "decode_run" : tactic =>
  `(tactic|
    (unfold Runs
     rw [extDecode_eq]
     simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
       PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
       EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable, getThe,
       MonadState.get, MonadStateOf.get, *]
     rfl))

/-- The first raw-header `lbu` is encoded at `0x104bc` in the immutable decoder image. -/
theorem raw_header_first_lbu_image_bytes :
    Artifact.programImage.readByte? 0x104bc = some 0x03 ∧
      Artifact.programImage.readByte? 0x104bd = some 0x45 ∧
        Artifact.programImage.readByte? 0x104be = some 0x0a ∧
          Artifact.programImage.readByte? 0x104bf = some 0x00 := by
  native_decide

/-- Register-only retirement bookkeeping preserves the loaded immutable code image. -/
theorem image_loaded_after_increment (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    Artifact.programImage.matchesMemory (tryStepControlFlowAfterIncrement state).mem := by
  simpa [tryStepControlFlowAfterIncrement] using loaded

/-- The generated Sail fetch at the first raw-header read sees its exact ELF instruction bytes. -/
theorem raw_header_first_lbu_fetch (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104bc)
      (BitVec.ofNat 8 0x03) (BitVec.ofNat 8 0x45) (BitVec.ofNat 8 0x0a) (BitVec.ofNat 8 0x00) := by
  rcases raw_header_first_lbu_image_bytes with ⟨read0, read1, read2, read3⟩
  exact fetchBytesAt_of_image_bytes Artifact.programImage
    (tryStepControlFlowAfterIncrement state) 0x104bc (by omega)
    (image_loaded_after_increment state loaded) 0x03 0x45 0x0a 0x00 read0 read1 read2 read3

/-- Generated Sail decodes the fetched word at `0x104bc` as `lbu a0, 0(s4)`. -/
theorem raw_header_first_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x03#8 0x45#8 0x0a#8 0x00#8)) state state
      (.LOAD (0#12, .Regidx 20#5, .Regidx 10#5, true, 1)) := by
  decode_run

end BinaryFv.SSZ.Zesu.Proof
