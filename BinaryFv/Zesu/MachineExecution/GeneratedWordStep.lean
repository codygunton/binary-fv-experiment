import BinaryFv.Zesu.ControlFlow.MachineRegions
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof

/-!
# Instruction steps driven by the generated word table

`GeneratedMachineRegions.words` records the `(address, word)` pair of every instruction in the pinned
binary, and `BinaryFv.Zesu.MachineRegions.words_are_file_image_words` checks all of those rows against
the file-backed bytes of `Artifacts.programImage`. This module spends that check: a step proof names
an address and its instruction word, and the fetch bytes, the assembled word, and the base-encoding
side condition all come from the table instead of from four hand-written byte literals per address.

Region membership is *not* in the word table -- it is a fact about `generatedProgram`'s ranges -- so
`regionPc`, `notExitPc` and `fetchPc` collapse the decidable range and exit checks instead, under the
same `autoParam` discipline. They are here because every call site that wants a table-driven fetch
wants them in the same breath.
-/

namespace BinaryFv.Zesu.MachineExecution

namespace GeneratedWordStep

open BinaryFv BinaryFv.Binary BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-! ## Address geometry of the generated program -/

/-- A literal pc lies in a function instance's execution scope. The decidable range check on the
generated program is the whole content; the `autoParam` removes the two `apply`s that precede it. -/
theorem regionPc {program : Program} {functionInstance : FunctionInstance} (pc : BitVec 64)
    (member : Program.inRanges (functionInstanceExecutionRanges program functionInstance)
      pc.toNat = true := by native_decide) :
    functionInstanceExecutionPcs program functionInstance pc :=
  functionInstanceExecutionPcs_iff_ranges.mpr (RegionPcs.iff_inRanges.mpr member)

/-- A literal pc is not one of a function instance's exits. -/
theorem notExitPc {functionInstance : FunctionInstance} (pc : BitVec 64)
    (member : functionInstance.exitPcs.contains pc.toNat = false := by native_decide) :
    ¬ functionInstanceExitPred functionInstance pc := by
  intro isExit
  rw [Array.contains_eq_true_of_mem (a := pc.toNat) isExit] at member
  exact Bool.noConfusion member

/-- A literal pc is an aligned fetchable start inside a function instance's execution scope. -/
theorem fetchPc {program : Program} {functionInstance : FunctionInstance} (pc : BitVec 64)
    (member : Program.inRanges (functionInstanceExecutionRanges program functionInstance)
      pc.toNat = true := by native_decide)
    (aligned : pc.toNat % 4 = 0 := by native_decide) :
    DecoderFetchPc (functionInstanceExecutionPcs program functionInstance) pc :=
  ⟨regionPc pc member, aligned⟩

/-! ## The register reads `decode_run` performs -/

/-- The two register reads the generated `ext_decode` makes before it reaches the encoding tables:
the current privilege and `mseccfg`. `decode_run` closes its goal by `simp only [..., *]`, so these
have to be in context; they follow from the machine premise alone, which is why a decode proof does
not have to route through `decoderStepPlatform` (that additionally wants the fetch). -/
theorem decodeReads {instructionPcs : BitVec 64 → Prop} {args : DecoderMachineArgs}
    {base state : State} (machine : DecoderMachinePre instructionPcs args base)
    (agree : Agree platformPreserved base state) :
    ∃ seccfgBits,
      (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
        some Privilege.Machine ∧
      (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some seccfgBits := by
  have afterIncrement : Agree decoderPreserved base (tryStepControlFlowAfterIncrement state) :=
    Agree.trans (Agree.weaken (fun _ preserved => preserved.2) agree)
      (Agree.weaken (fun _ preserved => preserved.2) (agree_afterIncrement state))
  obtain ⟨seccfgBits, seccfgRead, -⟩ := machine.mseccfg
  exact ⟨seccfgBits,
    (afterIncrement cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      machine.normal.2.1,
    (afterIncrement Register.mseccfg
      (by simp [decoderPreserved, platformPreserved])).trans seccfgRead⟩

/-! ## Fetch from the generated word table -/

/-- The low two bits of an assembled fetch word are the low two bits of its first byte. -/
private theorem baseInstructionEncoding_of_fetchWord {byte0 byte1 byte2 byte3 : BitVec 8}
    {bits : BitVec 32} (wordEq : fetchWord byte0 byte1 byte2 byte3 = bits)
    (low : Sail.BitVec.extractLsb bits 1 0 = 0b11#2) : BaseInstructionEncoding byte0 := by
  subst wordEq
  simp only [BaseInstructionEncoding, fetchWord, Sail.BitVec.extractLsb] at low ⊢
  bv_decide

/-- The fetch at `pc`, taken from the generated word table.

The four bytes stay existential deliberately: the table row, not a byte quadruple, is the pinned
fact, and everything a step proof needs about the bytes -- that they are what memory holds, that they
assemble to `bits`, and that `bits` is a base encoding -- is returned alongside them.

`row` is discharged against the ELF by `MachineRegions.words_are_file_image_words`, which checks
every row of the table against `Artifacts.programImage`'s file-backed bytes. -/
theorem generatedFetch (state : State) (pc : Nat) (bits : BitVec 32)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (row : MachineRegions.wordAt? pc = some bits.toNat := by native_decide)
    (base : Sail.BitVec.extractLsb bits 1 0 = 0b11#2 := by decide) :
    ∃ byte0 byte1 byte2 byte3 : BitVec 8,
      FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc)
        byte0 byte1 byte2 byte3 ∧
      fetchWord byte0 byte1 byte2 byte3 = bits ∧
      BaseInstructionEncoding byte0 := by
  obtain ⟨fits, owned⟩ := MachineRegions.readFileU32LE_of_wordAt row
  have loadedAfter : Artifacts.programImage.fileBytesLoadedFaithfully
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  obtain ⟨byte0, byte1, byte2, byte3, fetchBytes, wordEq⟩ :=
    ProgramImage.fetchBytesAt_of_ownedFileEncodedWord Artifacts.programImage
      (tryStepControlFlowAfterIncrement state) { address := pc, bits := bits } fits loadedAfter owned
  exact ⟨_, _, _, _, fetchBytes, wordEq, baseInstructionEncoding_of_fetchWord wordEq base⟩

/-! ## A whole register-writing step from an address and a word -/

/-- One register-writing fall-through instruction at a literal address, with its region membership,
its fetch, its instruction word and its base encoding all discharged from the generated tables.

Against `decoderRegisterWriteStep` this drops, per call site, the `DecoderFetchPc` block, the
`FetchBytesAt` block, the `fetchWord = ...` normalisation, the four byte literals and the four
`(by decide)` destination disequalities. The caller supplies exactly what is instruction-specific:
where it is, what word it is, what it decodes to, and what it executes to. -/
theorem generatedRegisterWriteStep {program : Program} {functionInstance : FunctionInstance}
    {args : DecoderMachineArgs} {baseState state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs program functionInstance) args baseState)
    (agree : Agree platformPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (stepNo : Nat) (pc : Nat) (bits : BitVec 32)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 pc))
    {decoded : _root_.instruction} {destination : Register} {value : RegisterType destination}
    (decode : Runs (ext_decode bits) (tryStepControlFlowAfterIncrement state)
      (tryStepControlFlowAfterIncrement state) decoded)
    (execute : Runs (execute decoded)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 pc) with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 pc)).regs.insert destination value }
      (.Retire_Success ()))
    (row : MachineRegions.wordAt? pc = some bits.toNat := by native_decide)
    (base : Sail.BitVec.extractLsb bits 1 0 = 0b11#2 := by decide)
    (member : Program.inRanges (functionInstanceExecutionRanges program functionInstance)
      (BitVec.ofNat 64 pc).toNat = true := by native_decide)
    (aligned : (BitVec.ofNat 64 pc).toNat % 4 = 0 := by native_decide)
    (destinationNotNextPc : destination ≠ nextPC := by decide)
    (destinationNotHart : destination ≠ hart_state := by decide)
    (destinationNotIncrement : destination ≠ minstret_increment := by decide)
    (destinationNotRetired : destination ≠ minstret := by decide) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 pc) retired destination value) false := by
  obtain ⟨byte0, byte1, byte2, byte3, fetchBytes, wordEq, baseEncoding⟩ :=
    generatedFetch state pc bits loaded row base
  exact decoderRegisterWriteStep machine agree retiredPresent stepNo (BitVec.ofNat 64 pc)
    (fetchPc (BitVec.ofNat 64 pc) member aligned) atPc byte0 byte1 byte2 byte3 decoded
    destination value fetchBytes baseEncoding (by rw [wordEq]; exact decode)
    destinationNotNextPc destinationNotHart destinationNotIncrement destinationNotRetired execute

end GeneratedWordStep

end BinaryFv.Zesu.MachineExecution
