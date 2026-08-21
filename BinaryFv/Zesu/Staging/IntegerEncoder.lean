import BinaryFv.Zesu.MachineExecution.HLevel3RawEncoderSteps
import BinaryFv.Zesu.DecodedValue.Encoder

/-!
# The fixed-width integer encoder hLevel3 boundary

The two standalone integer encoders have the same semantics. One encodes two 64-bit register
pieces. The other encodes four pieces. Their contracts differ only in word count, frame size,
and exact machine-code sites.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV
open BinaryFv.Zesu
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register

structure IntegerEncoderArgs where
  stackPointer : Nat
  returnPc : Nat
  word0 : Nat
  word1 : Nat
  word2 : Nat
  word3 : Nat
  stackFits : stackPointer < 2 ^ 64
  returnFits : returnPc < 2 ^ 64
  word0Fits : word0 < 2 ^ 64
  word1Fits : word1 < 2 ^ 64
  word2Fits : word2 < 2 ^ 64
  word3Fits : word3 < 2 ^ 64

def integerEncoderBytes (wordCount : Nat) (args : IntegerEncoderArgs) : Array UInt8 :=
  if wordCount = 2 then
    encodeNatLE 8 args.word0 ++ encodeNatLE 8 args.word1
  else
    encodeNatLE 8 args.word0 ++ encodeNatLE 8 args.word1 ++
      encodeNatLE 8 args.word2 ++ encodeNatLE 8 args.word3

private theorem encodeNatLE_size (width value : Nat) : (encodeNatLE width value).size = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [encodeNatLE, ih, Nat.add_comm]

private theorem encodeNatLE_get_toNat (width value index : Nat) (bound : index < width) :
    ((encodeNatLE width value)[index]'(by simpa [encodeNatLE_size] using bound)).toNat =
      (value / 2 ^ (8 * index)) % 256 := by
  induction width generalizing value index with
  | zero => omega
  | succ width ih =>
      by_cases indexZero : index = 0
      · subst index
        simp [encodeNatLE]
      · obtain ⟨nextIndex, rfl⟩ := Nat.exists_eq_succ_of_ne_zero indexZero
        have exponent : 2 ^ (8 * (nextIndex + 1)) = 256 * 2 ^ (8 * nextIndex) := by
          rw [show 8 * (nextIndex + 1) = 8 * nextIndex + 8 by omega, Nat.pow_add]
          simp [show 2 ^ 8 = 256 by decide, Nat.mul_comm]
        have exponent' : 2 ^ ((nextIndex + 1) * 8) = 2 ^ (nextIndex * 8) * 256 := by
          calc
            _ = 2 ^ (8 * (nextIndex + 1)) :=
              congrArg (fun exponent : Nat => 2 ^ exponent) (by omega)
            _ = 256 * 2 ^ (8 * nextIndex) := exponent
            _ = 2 ^ (nextIndex * 8) * 256 := by
              rw [show 8 * nextIndex = nextIndex * 8 by omega, Nat.mul_comm]
        simp [encodeNatLE, ih (value / 256) nextIndex (by omega), Nat.div_div_eq_div_mul,
          Nat.succ_eq_add_one, Nat.mul_comm, exponent']

private theorem UIntRep.bytesRepEncodeNatLE {width address value : Nat}
    {mem : Std.ExtHashMap Nat (BitVec 8)} (rep : UIntRep width mem address value) :
    BytesRep mem address (encodeNatLE width value) := by
  refine ⟨by simpa [encodeNatLE_size] using rep.2.1, ?_⟩
  intro index bound
  rw [rep.leBytes index (by simpa [encodeNatLE_size] using bound)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [encodeNatLE_get_toNat width value index (by simpa [encodeNatLE_size] using bound)]
  simp [BinaryFv.RiscV.Sep.leBytes, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt rep.1]

private theorem BytesRep.appendAdjacent {address : Nat} {left right : Array UInt8}
    {mem : Std.ExtHashMap Nat (BitVec 8)} (leftRep : BytesRep mem address left)
    (rightRep : BytesRep mem (address + left.size) right) :
    BytesRep mem address (left ++ right) := by
  refine ⟨by simpa [Array.size_append, Nat.add_assoc] using rightRep.1, ?_⟩
  intro index bound
  by_cases inLeft : index < left.size
  · simpa [Array.getElem_append_left inLeft] using leftRep.2 index inLeft
  · have leftLe : left.size ≤ index := by omega
    have inRight : index - left.size < right.size := by
      rw [Array.size_append] at bound
      omega
    have represented := rightRep.2 (index - left.size) inRight
    rw [show address + index = address + left.size + (index - left.size) by omega]
    rw [Array.getElem_append_right leftLe]
    exact represented

def IntegerEncoderWordBindings (wordCount : Nat) (args : IntegerEncoderArgs)
    (state : EndpointState) : Prop :=
  state.machine.regs.get? x10 = some (BitVec.ofNat 64 args.word0) ∧
  state.machine.regs.get? x11 = some (BitVec.ofNat 64 args.word1) ∧
  (wordCount = 2 ∨
    (wordCount = 4 ∧
      state.machine.regs.get? x12 = some (BitVec.ofNat 64 args.word2) ∧
      state.machine.regs.get? x13 = some (BitVec.ofNat 64 args.word3)))

def integerEncoderFrame (frameBase frameSize : Nat) : Region :=
  byteRange frameBase frameSize

def integerEncoderMemory (frameBase frameSize : Nat) : Region :=
  Region.union (integerEncoderFrame frameBase frameSize) writeOutputMemory

def integerEncoderPrefixWrites (register : Register) : Prop :=
  stepBookkeeping register ∨ register = x1 ∨ register = x10 ∨ register = x11

private theorem instructionPreserved_disjoint_integerEncoderPrefixWrites :
    RegSet.Disjoint instructionPreserved integerEncoderPrefixWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

structure IntegerEncoderMachineAccess (frameBase frameSize : Nat) (state : State) : Prop where
  output : EncoderOutputMachineAccess state
  frameFits : frameBase + frameSize ≤ 2 ^ 64
  frameAligned : frameBase % 16 = 0
  storePma : ∀ offset, offset + 8 ≤ frameSize → offset % 8 = 0 →
    StorePmaAllows state (BitVec.ofNat 64 (frameBase + offset)) 8
  storeNoMMIO : ∀ offset, offset + 8 ≤ frameSize → offset % 8 = 0 →
    StoreMMIOAddressExcluded (BitVec.ofNat 64 (frameBase + offset)) 8
  loadPma : ∀ offset, offset + 8 ≤ frameSize → offset % 8 = 0 →
    LoadPmaAllows state (BitVec.ofNat 64 (frameBase + offset)) 8
  loadNoMMIO : ∀ offset, offset + 8 ≤ frameSize → offset % 8 = 0 →
    LoadMMIOAddressExcluded (BitVec.ofNat 64 (frameBase + offset)) 8
  codeDisjoint : ∀ offset, offset < frameSize →
    Artifacts.programImage.readFileByte? (frameBase + offset) = none
  outputDisjoint : ∀ offset, offset < frameSize → ¬writeOutputMemory (frameBase + offset)

private theorem IntegerEncoderMachineAccess.ofWrites {frameBase frameSize : Nat}
    {before after : State} {writes : RegSet}
    (access : IntegerEncoderMachineAccess frameBase frameSize before)
    (frame : WritesOnlyRegs writes before after) (pmaOutside : ¬writes pma_regions)
    (configured : ConfiguredMachinePre EndpointMachinePc after) :
    IntegerEncoderMachineAccess frameBase frameSize after := by
  have pmaEq := frame.get pma_regions pmaOutside
  exact
    { output :=
        { configured
          outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq
            access.output.outputBufferStore
          outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq
            access.output.outputLengthStore
          outputBufferNoMMIO := access.output.outputBufferNoMMIO
          outputLengthNoMMIO := access.output.outputLengthNoMMIO }
      frameFits := access.frameFits
      frameAligned := access.frameAligned
      storePma := fun offset bound aligned =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.storePma offset bound aligned)
      storeNoMMIO := access.storeNoMMIO
      loadPma := fun offset bound aligned =>
        dataPmaAllows_of_pma_regions_eq pmaEq (access.loadPma offset bound aligned)
      loadNoMMIO := access.loadNoMMIO
      codeDisjoint := access.codeDisjoint
      outputDisjoint := access.outputDisjoint }

private theorem IntegerEncoderMachineAccess.ofSeg {frameBase frameSize : Nat}
    {owned exit M kv fromStep count before after pc}
    (access : IntegerEncoderMachineAccess frameBase frameSize before)
    (seg : Seg owned exit (fun _ _ _ _ _ => False) integerEncoderPrefixWrites M kv
      fromStep count before after pc) :
    IntegerEncoderMachineAccess frameBase frameSize after := by
  exact access.ofWrites seg.writes (by
      simp [integerEncoderPrefixWrites, stepBookkeeping])
    (access.output.configured.mono
      (seg.agree instructionPreserved_disjoint_integerEncoderPrefixWrites) seg.retired)

private theorem integerEncoderCodeOfSeg {frameBase frameSize : Nat}
    {owned exit kv fromStep count before after pc}
    (access : IntegerEncoderMachineAccess frameBase frameSize before)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully before.mem)
    (seg : Seg owned exit (fun _ _ _ _ _ => False) integerEncoderPrefixWrites
      (integerEncoderFrame frameBase frameSize) kv fromStep count before after pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
  intro address byte fileByte
  have unchanged := seg.mem address (by
    intro inside
    unfold integerEncoderFrame byteRange at inside
    have none := access.codeDisjoint (address - frameBase) (by omega)
    rw [show frameBase + (address - frameBase) = address by omega, fileByte] at none
    cases none)
  exact unchanged.trans (loaded address byte fileByte)

def integerEncoderPreserved (register : Register) : Prop :=
  encoderInlinePreserved register ∨ register = x1

def IntegerEncoderEntry (entry frameSize wordCount : Nat) (args : IntegerEncoderArgs)
    (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnPc) ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  IntegerEncoderWordBindings wordCount args state ∧
  frameSize ≤ args.stackPointer ∧
  IntegerEncoderMachineAccess (args.stackPointer - frameSize) frameSize state.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully state.machine.mem

def IntegerEncoderExit (frameSize wordCount : Nat) (args : IntegerEncoderArgs)
    (_outcome : Unit) (before after : EndpointState) : Prop :=
  after.machine.regs.get? PC = some (BitVec.ofNat 64 args.returnPc) ∧
  after.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnPc) ∧
  after.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  after.stdout = before.stdout ++ integerEncoderBytes wordCount args ∧
  after.stdin = before.stdin ∧ after.stdinCursor = before.stdinCursor ∧
  after.exitCode = before.exitCode ∧
  WritesOnlyWithin
    (integerEncoderMemory (args.stackPointer - frameSize) frameSize)
    before.machine after.machine ∧
  Agree integerEncoderPreserved before.machine after.machine ∧
  RetiredCounterPresent after.machine ∧
  Artifacts.programImage.fileBytesLoadedFaithfully after.machine.mem ∧
  EndpointMachineAuxAgree before.machine after.machine

def integerEncoderContract (entry frameSize wordCount : Nat)
    (stepBound : IntegerEncoderArgs → Nat) :
    RelationalMachineContract EndpointState IntegerEncoderArgs Unit :=
  { allows := fun _ _ => True
    entry := IntegerEncoderEntry entry frameSize wordCount
    exit := IntegerEncoderExit frameSize wordCount
    stepBound }

def IntegerEncoderInstanceContract (entry frameSize wordCount : Nat)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat) : Prop :=
  ∃ stepBound : Nat,
    stepBound < level2ContractFuel ∧
    (integerEncoderContract entry frameSize wordCount (fun _ => stepBound)).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs)

set_option genInjectivity false in
/-- The shared boundary after an integer encoder writes its words and prepares `write_output`. -/
structure IntegerEncoderPreparedHandoff (executionPcs : List Elflings.PcRange)
    (outputEntry frameSize wordCount fromStep prefixCount : Nat)
    (args : IntegerEncoderArgs) (before prepared : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
    fromStep prefixCount before prepared
  atPc : prepared.machine.regs.get? PC = some (BitVec.ofNat 64 (outputEntry + 4))
  source : prepared.machine.regs.get? x10 =
    some (BitVec.ofNat 64 (args.stackPointer - frameSize))
  stack : prepared.machine.regs.get? x2 =
    some (BitVec.ofNat 64 (args.stackPointer - frameSize))
  length : prepared.machine.regs.get? x11 = some (BitVec.ofNat 64 (8 * wordCount))
  savedReturn : UIntRep 8 prepared.machine.mem
    (args.stackPointer - frameSize + (frameSize - 8)) args.returnPc
  bytes : BytesRep prepared.machine.mem (args.stackPointer - frameSize)
    (integerEncoderBytes wordCount args)
  bytesSize : (integerEncoderBytes wordCount args).size = 8 * wordCount
  outsideOutput : ∀ index, index < (integerEncoderBytes wordCount args).size →
    ¬writeOutputMemory (args.stackPointer - frameSize + index)
  loaded : Artifacts.programImage.fileBytesLoadedFaithfully prepared.machine.mem
  access : EncoderOutputMachineAccess prepared.machine
  writes : WritesOnlyRegs
    (RegSet.union (RegSet.only x2) integerEncoderPrefixWrites)
    before.machine prepared.machine
  mem : WritesOnlyWithin (integerEncoderFrame (args.stackPointer - frameSize) frameSize)
    before.machine prepared.machine
  aux : EndpointMachineAuxAgree before.machine prepared.machine

/-- Exact site data for one width of the shared fixed-width integer encoder. -/
structure IntegerEncoderSite (entry frameSize wordCount outputEntry callReturn prefixCount
    suffixCount : Nat) (executionPcs : List Elflings.PcRange) (exitPcs : List Nat) where
  totalCount : prefixCount + 7 + suffixCount < level2ContractFuel
  output : RawWriteOutputPreparedSite outputEntry (8 * wordCount) callReturn
    executionPcs [callReturn]
  prepare : ∀ fromStep args before,
    IntegerEncoderEntry entry frameSize wordCount args before →
      ∃ prepared, IntegerEncoderPreparedHandoff executionPcs outputEntry frameSize wordCount
        fromStep prefixCount args before prepared
  finish : ∀ fromStep args before prepared outputState,
    IntegerEncoderPreparedHandoff executionPcs outputEntry frameSize wordCount
      fromStep prefixCount args before prepared →
    RawEncoderExit callReturn
      { sourceAddress := args.stackPointer - frameSize
        bytes := integerEncoderBytes wordCount args }
      () prepared outputState →
    ∃ after,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
        (fromStep + prefixCount + 7) suffixCount outputState after ∧
      (∃ pc, EndpointPc after = some pc ∧ pcInList exitPcs pc) ∧
      IntegerEncoderExit frameSize wordCount args () before after

/-- Prove every compatible integer encoder from one prepare/output/finish composition. -/
theorem integerEncoderInstanceContract_of_site
    (site : IntegerEncoderSite entry frameSize wordCount outputEntry callReturn
      prefixCount suffixCount executionPcs exitPcs) :
    IntegerEncoderInstanceContract entry frameSize wordCount executionPcs exitPcs := by
  refine ⟨prefixCount + 7 + suffixCount, site.totalCount, ?_⟩
  intro args fromStep before entryPre
  obtain ⟨prepared, preparedHandoff⟩ := site.prepare fromStep args before entryPre
  let rawArgs : RawEncoderArgs :=
    { sourceAddress := args.stackPointer - frameSize
      bytes := integerEncoderBytes wordCount args }
  obtain ⟨outputState, outputTrace, outputExit⟩ := rawWriteOutputPreparedHandoff
    site.output (fromStep + prefixCount) rawArgs prepared preparedHandoff.atPc
      preparedHandoff.source preparedHandoff.length preparedHandoff.bytesSize
      preparedHandoff.bytes preparedHandoff.outsideOutput preparedHandoff.loaded
      preparedHandoff.access
  obtain ⟨after, suffixTrace, exitAt, exitState⟩ :=
    site.finish fromStep args before prepared outputState preparedHandoff outputExit
  have prefixOutput : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep (prefixCount + 7) before outputState := by
    simpa [Nat.add_assoc] using preparedHandoff.trace.append outputTrace
  have wholeTrace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      fromStep (prefixCount + 7 + suffixCount) before after := by
    simpa [Nat.add_assoc] using prefixOutput.append suffixTrace
  refine ⟨prefixCount + 7 + suffixCount, after, (), by omega, Nat.le_refl _, wholeTrace,
    exitAt, trivial, exitState⟩

def integerEncoderU256ExecutionPcs : List Elflings.PcRange :=
  [(0x10190, 0x101c4), (0x15cb0, 0x15ccc), (0x15ccc, 0x15cd8),
    (0x15cd8, 0x15ce4)]

def integerEncoderU256ExitPcs : List Nat :=
  [0x151b4, 0x155bc, 0x155fc, 0x15614, 0x15644, 0x1565c]

def integerEncoderU128ExecutionPcs : List Elflings.PcRange :=
  [(0x10190, 0x101c4), (0x15ce4, 0x15cf8), (0x15cf8, 0x15d04),
    (0x15d04, 0x15d10)]

def integerEncoderU128ExitPcs : List Nat := [0x15118, 0x15138, 0x15564]

private def integerEncoderU256OutputSite :
    RawWriteOutputPreparedSite 0x15ccc 32 0x15cd8
      integerEncoderU256ExecutionPcs [0x15cd8] :=
  rawWriteOutputPreparedSiteOfLiterals 0x15ccc 32 0x15cd8
    0xfcd0 0xffffa 0x4c0
    0x97 0xa0 0xff 0xff
    0xe7 0x80 0x00 0x4c
    integerEncoderU256ExecutionPcs [0x15cd8]

private def integerEncoderU128OutputSite :
    RawWriteOutputPreparedSite 0x15cf8 16 0x15d04
      integerEncoderU128ExecutionPcs [0x15d04] :=
  rawWriteOutputPreparedSiteOfLiterals 0x15cf8 16 0x15d04
    0xfcfc 0xffffa 0x494
    0x97 0xa0 0xff 0xff
    0xe7 0x80 0x40 0x49
    integerEncoderU128ExecutionPcs [0x15d04]

abbrev Proposed_ssz_decode_observation_Encoder_int_fi_1_43a9_Contract : Prop :=
  IntegerEncoderInstanceContract 0x15cb0 48 4
    integerEncoderU256ExecutionPcs integerEncoderU256ExitPcs

abbrev Proposed_ssz_decode_observation_Encoder_int_fi_1_4494_Contract : Prop :=
  IntegerEncoderInstanceContract 0x15ce4 32 2
    integerEncoderU128ExecutionPcs integerEncoderU128ExitPcs

end BinaryFv.Zesu.Staging
