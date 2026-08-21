import BinaryFv.Zesu.MachineExecution.EncoderCallFinish
import BinaryFv.Zesu.DecodedValue.Encoder

/-!
# The fixed-width integer encoder hLevel3 boundary

The two standalone integer encoders have the same semantics. One encodes two 64-bit register
pieces. The other encodes four pieces. Their contracts differ only in word count, frame size,
and exact machine-code sites.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
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

theorem encodeNatLE_size (width value : Nat) : (encodeNatLE width value).size = width := by
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

theorem UIntRep.bytesRepEncodeNatLE {width address value : Nat}
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

theorem UIntRep.bytesRepEncodeNatLEEight {address value : Nat}
    {mem : Std.ExtHashMap Nat (BitVec 8)} (rep : UIntRep 8 mem address value) :
    BytesRep mem address (encodeNatLE 8 value) :=
  UIntRep.bytesRepEncodeNatLE rep

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

private theorem UIntRep.twoWordsBytesRep {address word0 word1 : Nat}
    {mem : Std.ExtHashMap Nat (BitVec 8)} (first : UIntRep 8 mem address word0)
    (second : UIntRep 8 mem (address + 8) word1) :
    BytesRep mem address (encodeNatLE 8 word0 ++ encodeNatLE 8 word1) := by
  have firstBytes := UIntRep.bytesRepEncodeNatLEEight first
  have secondBytes : BytesRep mem (address + (encodeNatLE 8 word0).size)
      (encodeNatLE 8 word1) := by
    simpa only [encodeNatLE_size] using UIntRep.bytesRepEncodeNatLEEight second
  exact BytesRep.appendAdjacent firstBytes secondBytes

private theorem integerEncoderStackSubtractResult (stackPointer frameSize : Nat)
    (immediate : BitVec 12) (lower : frameSize ≤ stackPointer)
    (upper : stackPointer < 2 ^ 64)
    (sign : sign_extend (m := 64) immediate = BitVec.ofNat 64 (2 ^ 64 - frameSize)) :
    BitVec.ofNat 64 (stackPointer - frameSize) =
      iTypeResult .ADDI immediate (BitVec.ofNat 64 stackPointer) :=
  stackSubtractResult stackPointer frameSize immediate lower upper sign

private theorem integerEncoderStackRestoreResult (stackPointer frameSize : Nat)
    (immediate : BitVec 12) (lower : frameSize ≤ stackPointer)
    (upper : stackPointer < 2 ^ 64)
    (sign : sign_extend (m := 64) immediate = BitVec.ofNat 64 frameSize) :
    BitVec.ofNat 64 stackPointer =
      iTypeResult .ADDI immediate (BitVec.ofNat 64 (stackPointer - frameSize)) :=
  stackRestoreResult stackPointer frameSize immediate lower upper sign

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

private theorem IntegerEncoderMachineAccess.ofEncoderFrame {frameBase frameSize : Nat}
    {before after : State} (access : IntegerEncoderMachineAccess frameBase frameSize before)
    (agree : Agree encoderInlinePreserved before after) (retired : RetiredCounterPresent after) :
    IntegerEncoderMachineAccess frameBase frameSize after := by
  have instructionAgree : Agree instructionPreserved before after :=
    agree.weaken (fun _ preserved => Or.inl preserved)
  have pmaEq := instructionAgree pma_regions
    (by simp [instructionPreserved, platformPreserved])
  exact
    { output :=
        { configured := access.output.configured.mono instructionAgree retired
          outputBufferStore := dataPmaAllows_of_pma_regions_eq pmaEq
            access.output.outputBufferStore
          outputLengthStore := dataPmaAllows_of_pma_regions_eq pmaEq
            access.output.outputLengthStore
          outputBufferNoMMIO := access.output.outputBufferNoMMIO
          outputLengthNoMMIO := access.output.outputLengthNoMMIO }
      frameFits := access.frameFits
      frameAligned := access.frameAligned
      storePma := fun offset bound aligned => dataPmaAllows_of_pma_regions_eq pmaEq
        (access.storePma offset bound aligned)
      storeNoMMIO := access.storeNoMMIO
      loadPma := fun offset bound aligned => dataPmaAllows_of_pma_regions_eq pmaEq
        (access.loadPma offset bound aligned)
      loadNoMMIO := access.loadNoMMIO
      codeDisjoint := access.codeDisjoint
      outputDisjoint := access.outputDisjoint }

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

def IntegerEncoderEntry (entry frameSize wordCount : Nat) (exitPcs : List Nat)
    (args : IntegerEncoderArgs)
    (state : EndpointState) : Prop :=
  state.machine.regs.get? PC = some (BitVec.ofNat 64 entry) ∧
  state.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnPc) ∧
  state.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
  IntegerEncoderWordBindings wordCount args state ∧
  pcInList exitPcs (BitVec.ofNat 64 args.returnPc) ∧
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

def integerEncoderContract (entry frameSize wordCount : Nat) (exitPcs : List Nat)
    (stepBound : IntegerEncoderArgs → Nat) :
    RelationalMachineContract EndpointState IntegerEncoderArgs Unit :=
  { allows := fun _ _ => True
    entry := IntegerEncoderEntry entry frameSize wordCount exitPcs
    exit := IntegerEncoderExit frameSize wordCount
    stepBound }

def IntegerEncoderInstanceContract (entry frameSize wordCount : Nat)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat) : Prop :=
  ∃ stepBound : Nat,
    stepBound < level2ContractFuel ∧
    (integerEncoderContract entry frameSize wordCount exitPcs (fun _ => stepBound)).Implements
      EndpointStep EndpointPc (pcInRanges executionPcs) (pcInList exitPcs)

set_option genInjectivity false in
/-- The shared boundary after an integer encoder writes its words and prepares `write_output`. -/
structure IntegerEncoderPreparedHandoff (executionPcs : List Elflings.PcRange)
    (exitPcs : List Nat)
    (outputEntry frameSize wordCount fromStep prefixCount : Nat)
    (args : IntegerEncoderArgs) (before prepared : EndpointState) : Prop where
  trace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
    fromStep prefixCount before prepared
  atPc : prepared.machine.regs.get? PC = some (BitVec.ofNat 64 (outputEntry + 4))
  returnInside : pcInList exitPcs (BitVec.ofNat 64 args.returnPc)
  frameLower : frameSize ≤ args.stackPointer
  entryLink : before.machine.regs.get? x1 = some (BitVec.ofNat 64 args.returnPc)
  entryStack : before.machine.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer)
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
  access : IntegerEncoderMachineAccess (args.stackPointer - frameSize) frameSize prepared.machine
  writes : WritesOnlyRegs
    (RegSet.union (RegSet.only x2) integerEncoderPrefixWrites)
    before.machine prepared.machine
  mem : WritesOnlyWithin (integerEncoderFrame (args.stackPointer - frameSize) frameSize)
    before.machine prepared.machine
  aux : EndpointMachineAuxAgree before.machine prepared.machine
  stdout : prepared.stdout = before.stdout
  stdin : prepared.stdin = before.stdin
  stdinCursor : prepared.stdinCursor = before.stdinCursor
  exitCode : prepared.exitCode = before.exitCode

/-- Exact site data for one width of the shared fixed-width integer encoder. -/
structure IntegerEncoderSite (entry frameSize wordCount outputEntry callReturn prefixCount
    suffixCount : Nat) (executionPcs : List Elflings.PcRange) (exitPcs : List Nat) where
  totalCount : prefixCount + 7 + suffixCount < level2ContractFuel
  output : RawWriteOutputPreparedSite outputEntry (8 * wordCount) callReturn
    executionPcs [callReturn]
  prepare : ∀ fromStep args before,
    IntegerEncoderEntry entry frameSize wordCount exitPcs args before →
      ∃ prepared, IntegerEncoderPreparedHandoff executionPcs exitPcs outputEntry frameSize wordCount
        fromStep prefixCount args before prepared
  finish : ∀ fromStep args before prepared outputState,
    IntegerEncoderPreparedHandoff executionPcs exitPcs outputEntry frameSize wordCount
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
      preparedHandoff.access.output
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

private def integerEncoderU128PreparePcs : List Elflings.PcRange := [(0x15ce4, 0x15cfc)]

private def integerEncoderU256PreparePcs : List Elflings.PcRange := [(0x15cb0, 0x15cd0)]

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

private theorem integerEncoderPcNotObserved {executionPcs : List Elflings.PcRange}
    {pc : BitVec 64} (afterHost : ∀ range ∈ executionPcs, 0x101d4 ≤ range.1)
    (inside : pcInRanges executionPcs pc) : ¬BareMetalHostTransitionPc pc := by
  intro observed
  unfold pcInRanges at inside
  rcases inside with ⟨range, member, lower, upper⟩
  have after := afterHost range member
  unfold BareMetalHostTransitionPc readContextReturnPc writeContextReturnPc
    exitContextStorePc at observed
  rcases observed with observed | observed | observed <;> omega

private theorem liftIntegerEncoderTrace (template : EndpointState)
    {executionPcs : List Elflings.PcRange} {exit : BitVec 64 → Prop}
    {fromStep count : Nat} {before after : State}
    (afterHost : ∀ range ∈ executionPcs, 0x101d4 ≤ range.1)
    (trace : ScopedTrace (pcInRanges executionPcs) exit (fun _ _ _ _ _ => False)
      fromStep count before after) :
    ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs) fromStep count
      { template with machine := before } { template with machine := after } := by
  exact liftSailSegToEndpointTrace template afterHost trace

private theorem integerEncoderSaveWord0Decode (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    Runs (ext_decode (fetchWord 0x23#8 0x30#8 0xa1#8 0x00#8))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (0, .Regidx 10#5, .Regidx 2#5, 8)) := by
  configured_store_decode configured

private theorem integerEncoderSaveWord1Decode (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    Runs (ext_decode (fetchWord 0x23#8 0x34#8 0xb1#8 0x00#8))
      (tryStepStoreAfterIncrement state) (tryStepStoreAfterIncrement state)
      (.STORE (8, .Regidx 11#5, .Regidx 2#5, 8)) := by
  configured_store_decode configured

private theorem integerEncoderStackSourceDecode (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x01#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0, .Regidx 2#5, .Regidx 10#5, .ADDI)) := by
  configured_decode configured

private theorem integerEncoderU128LengthDecode (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x00#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x10, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
  configured_decode configured

private theorem integerEncoderU256LengthDecode (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state) :
    Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x00#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x20, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
  configured_decode configured

/-- Append one exact stack word to the shared integer-encoder save schedule. -/
private theorem integerEncoderSaveWordStep
    {executionPcs : List Elflings.PcRange} {exit : BitVec 64 → Prop}
    {frameBase frameSize : Nat} {base cur : State} {kv : List RegVal}
    {fromStep count : Nat} {pc : BitVec 64}
    (seg : Seg (pcInRanges executionPcs) exit (fun _ _ _ _ _ => False)
      integerEncoderPrefixWrites (integerEncoderFrame frameBase frameSize)
      kv fromStep count base cur pc)
    (originAccess : IntegerEncoderMachineAccess frameBase frameSize base)
    (originLoaded : Artifacts.programImage.fileBytesLoadedFaithfully base.mem)
    (currentAccess : IntegerEncoderMachineAccess frameBase frameSize cur)
    (currentLoaded : Artifacts.programImage.fileBytesLoadedFaithfully cur.mem)
    (words : List (Nat × Nat)) (wordsRep : SavedWordReps cur words)
    (storePc offset : Nat) (source : BitVec 64) (imm : BitVec 12) (rs2 : regidx)
    (byte0 byte1 byte2 byte3 : UInt8)
    (stackRead : cur.regs.get? x2 = some (BitVec.ofNat 64 frameBase))
    (dataRun : ∀ premise, WritesOnlyRegs stepBookkeeping cur premise →
      Runs (rX_bits rs2) premise premise source)
    (wordsDisjoint : ∀ word ∈ words, ∀ index, index < 8 →
      ¬byteRange (frameBase + offset) 8 (word.1 + index))
    (frameBound : offset + 8 ≤ frameSize)
    (offsetAligned : offset % 8 = 0)
    (aligned : (frameBase + offset) % 8 = 0)
    (pcEq : pc = BitVec.ofNat 64 storePc)
    (inRegion : pcInRanges executionPcs (BitVec.ofNat 64 storePc))
    (notExit : ¬exit (BitVec.ofNat 64 storePc))
    (decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 byte0.toNat)
      (BitVec.ofNat 8 byte1.toNat) (BitVec.ofNat 8 byte2.toNat)
      (BitVec.ofNat 8 byte3.toNat)))
      (tryStepStoreAfterIncrement cur) (tryStepStoreAfterIncrement cur)
      (.STORE (imm, rs2, .Regidx 2#5, 8)))
    (addressEq : BitVec.ofNat 64 frameBase + sign_extend (m := 64) imm =
      BitVec.ofNat 64 (frameBase + offset))
    (keep : RegsOutside stepBookkeeping kv)
    (site : ExactInstructionSite storePc byte0 byte1 byte2 byte3)
    (baseEncoding : BaseInstructionEncoding (BitVec.ofNat 8 byte0.toNat)) :
    ∃ next,
      Seg (pcInRanges executionPcs) exit (fun _ _ _ _ _ => False)
        integerEncoderPrefixWrites (integerEncoderFrame frameBase frameSize)
        kv fromStep (count + 1) base next (BitVec.ofNat 64 (storePc + 4)) ∧
      SavedWordReps next ((frameBase + offset, source.toNat) :: words) ∧
      IntegerEncoderMachineAccess frameBase frameSize next ∧
      Artifacts.programImage.fileBytesLoadedFaithfully next.mem := by
  subst pc
  obtain ⟨retired, run⟩ := configuredStackDwordStoreStep (fromStep + count) storePc
    frameBase offset cur source imm rs2 byte0 byte1 byte2 byte3
    currentAccess.output.configured seg.atPc stackRead
    (currentAccess.storePma offset frameBound offsetAligned)
    (currentAccess.storeNoMMIO offset frameBound offsetAligned) aligned
    (by have fits := currentAccess.frameFits; omega) currentLoaded addressEq decode dataRun
    (site := site) (base := baseEncoding)
  obtain ⟨retired', next, nextEq, nextSeg⟩ := seg.stepStoreWitness
    (width := 8) (frameBase + offset) source (BitVec.ofNat 64 (storePc + 4))
    inRegion notExit ⟨retired, run⟩ site.advance
    (by intro address lower upper; unfold integerEncoderFrame byteRange; omega)
    (by intro register bookkeeping; exact Or.inl bookkeeping) keep
  have stepWrites : WritesOnlyWithin (byteRange (frameBase + offset) 8) cur next := by
    intro address outside
    rw [nextEq]
    exact storeRetirement_mem_writes cur (BitVec.ofNat 64 storePc)
      (Sail.BitVec.addInt (BitVec.ofNat 64 storePc) 4) retired'
      (frameBase + offset) source address outside
  have oldReps : SavedWordReps next words := by
    intro word member
    exact (wordsRep word member).of_writesOnlyWithin stepWrites (by
      intro index indexBound
      exact wordsDisjoint word member index indexBound)
  have currentRep : UIntRep 8 next.mem (frameBase + offset) source.toNat := by
    rw [nextEq]
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using
      uintRep_afterWriteBytes_eight
        (coreStoreNextState (tryStepStoreAfterIncrement cur) (BitVec.ofNat 64 storePc))
        (frameBase + offset) source.toNat source.isLt (by
          have fits := currentAccess.frameFits
          omega)
  refine ⟨next, nextSeg, ?_, originAccess.ofSeg nextSeg,
    integerEncoderCodeOfSeg originAccess originLoaded nextSeg⟩
  intro word member
  simp only [List.mem_cons] at member
  rcases member with rfl | tail
  · simpa using currentRep
  · exact oldReps word tail

private theorem integerEncoderPrepare (entryPc frameSize wordCount outputEntry prefixCount : Nat)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat)
    (fromStep : Nat) (args : IntegerEncoderArgs)
    (before : EndpointState)
    (entry : IntegerEncoderEntry entryPc frameSize wordCount exitPcs args before)
    (site :
      (entryPc = 0x15cb0 ∧ frameSize = 48 ∧ wordCount = 4 ∧ outputEntry = 0x15ccc ∧
        prefixCount = 8 ∧ executionPcs = integerEncoderU256ExecutionPcs ∧
        exitPcs = integerEncoderU256ExitPcs) ∨
      (entryPc = 0x15ce4 ∧ frameSize = 32 ∧ wordCount = 2 ∧ outputEntry = 0x15cf8 ∧
        prefixCount = 6 ∧ executionPcs = integerEncoderU128ExecutionPcs ∧
        exitPcs = integerEncoderU128ExitPcs)) :
    ∃ prepared, IntegerEncoderPreparedHandoff executionPcs exitPcs outputEntry frameSize wordCount
      fromStep prefixCount args before prepared := by
  rcases site with u256 | u128
  · rcases u256 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rcases entry with ⟨atPc, link, stack, words, returnInside, frameLower, access, loaded⟩
    rcases words with ⟨word0, word1, words⟩
    rcases words with impossible | ⟨_, word2, word3⟩
    · omega
    let frameBase := args.stackPointer - 48
    have stackResult : BitVec.ofNat 64 frameBase =
        iTypeResult .ADDI 0xfd0 (BitVec.ofNat 64 args.stackPointer) :=
      integerEncoderStackSubtractResult args.stackPointer 48 0xfd0 frameLower
        args.stackFits (by native_decide)
    have decode0 : Runs
        (ext_decode (fetchWord 0x13#8 0x01#8 0x01#8 0xfd#8))
        (tryStepControlFlowAfterIncrement before.machine)
        (tryStepControlFlowAfterIncrement before.machine)
        (.ITYPE (0xfd0, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
      configured_decode access.output.configured
    obtain ⟨r0, run0⟩ := configuredAddiX2Step fromStep 0x15cb0 before.machine 0xfd0
      (BitVec.ofNat 64 args.stackPointer) (BitVec.ofNat 64 frameBase)
      0x13 0x01 0x01 0xfd access.output.configured atPc stack loaded stackResult decode0
      (base := by rfl)
    let machine1 := afterRegisterWrite before.machine 0x15cb0 r0 x2
      (BitVec.ofNat 64 frameBase)
    have atPc1 : machine1.regs.get? PC = some 0x15cb4 := by
      simpa [machine1] using afterRegisterWrite_pc before.machine 0x15cb0 r0 x2
        (BitVec.ofNat 64 frameBase)
    have stack1 : machine1.regs.get? x2 = some (BitVec.ofNat 64 frameBase) := by
      simpa [machine1] using afterRegisterWrite_destination before.machine 0x15cb0 r0 x2
        (BitVec.ofNat 64 frameBase) (by decide) (by decide)
    have firstWrites := afterRegisterWrite_writes before.machine 0x15cb0 r0 x2
      (BitVec.ofNat 64 frameBase)
    have link1 : machine1.regs.get? x1 = some (BitVec.ofNat 64 args.returnPc) :=
      (firstWrites.get x1 (by simp [stepBookkeeping])).trans link
    have word01 : machine1.regs.get? x10 = some (BitVec.ofNat 64 args.word0) :=
      (firstWrites.get x10 (by simp [stepBookkeeping])).trans word0
    have word11 : machine1.regs.get? x11 = some (BitVec.ofNat 64 args.word1) :=
      (firstWrites.get x11 (by simp [stepBookkeeping])).trans word1
    have word21 : machine1.regs.get? x12 = some (BitVec.ofNat 64 args.word2) :=
      (firstWrites.get x12 (by simp [stepBookkeeping])).trans word2
    have word31 : machine1.regs.get? x13 = some (BitVec.ofNat 64 args.word3) :=
      (firstWrites.get x13 (by simp [stepBookkeeping])).trans word3
    have configured1 : ConfiguredMachinePre EndpointMachinePc machine1 := by
      exact access.output.configured.afterRegisterWrite 0x15cb0 r0 x2
        (BitVec.ofNat 64 frameBase) (by simp [instructionPreserved, platformPreserved])
    have access1 : IntegerEncoderMachineAccess frameBase 48 machine1 :=
      access.ofWrites firstWrites (by simp [stepBookkeeping]) configured1
    have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully machine1.mem := by
      simpa [machine1] using fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
        before.machine 0x15cb0 r0 x2 (BitVec.ofNat 64 frameBase) loaded
    have seg00 := Seg.nil (pcInRanges integerEncoderU256PreparePcs)
      (fun pc => pc = 0x15cd0) (fun _ _ _ _ _ => False) integerEncoderPrefixWrites
      (integerEncoderFrame frameBase 48) (fromStep + 1) configured1.retiredCounter atPc1
    have seg01 := seg00.know x2 (BitVec.ofNat 64 frameBase) stack1
    have seg02 := seg01.know x1 (BitVec.ofNat 64 args.returnPc) link1
    have seg03 := seg02.know x10 (BitVec.ofNat 64 args.word0) word01
    have seg04 := seg03.know x11 (BitVec.ofNat 64 args.word1) word11
    have seg05 := seg04.know x12 (BitVec.ofNat 64 args.word2) word21
    have seg0 := seg05.know x13 (BitVec.ofNat 64 args.word3) word31
    have reps0 : SavedWordReps machine1 [] := by simp [SavedWordReps]
    obtain ⟨machine2, seg1, reps1, access2, loaded2⟩ := integerEncoderSaveWordStep
      seg0 access1 loaded1 access1 loaded1 [] reps0 0x15cb4 40
      (BitVec.ofNat 64 args.returnPc) 0x28 (.Regidx 1#5) 0x23 0x34 0x11 0x02 stack1
      (by intro premise writes
          exact rX_x1_run premise (BitVec.ofNat 64 args.returnPc)
            ((writes.get x1 (by decide)).trans (seg0.reg x1 _ (by simp))))
      (by simp) (by omega) (by omega) (by have aligned := access1.frameAligned; omega)
      rfl (by owned_pc [pcInRanges, integerEncoderU256PreparePcs]) (by native_decide)
      (by configured_store_decode configured1) (by
        change BitVec.ofNat 64 frameBase + 0x28#64 = _
        rw [← BitVec.ofNat_add])
      (by simp [RegsOutside, integerEncoderPrefixWrites, stepBookkeeping])
      (by native_decide) (by rfl)
    obtain ⟨machine3, seg2, reps2, access3, loaded3⟩ := integerEncoderSaveWordStep
      seg1 access1 loaded1 access2 loaded2
      [(frameBase + 40, (BitVec.ofNat 64 args.returnPc).toNat)] reps1
      0x15cb8 0 (BitVec.ofNat 64 args.word0) 0 (.Regidx 10#5) 0x23 0x30 0xa1 0x00
      (seg1.reg x2 _ (by simp))
      (by intro premise writes
          exact rX_x10_run premise (BitVec.ofNat 64 args.word0)
            ((writes.get x10 (by decide)).trans (seg1.reg x10 _ (by simp))))
      (by intro word member index bound; simp at member; rcases member with rfl
          unfold byteRange; omega)
      (by omega) (by omega) (by have aligned := access2.frameAligned; omega) rfl
      (by owned_pc [pcInRanges, integerEncoderU256PreparePcs]) (by native_decide)
      (by configured_store_decode access2.output.configured) (by
        change BitVec.ofNat 64 frameBase + sign_extend (m := 64) (0#12) = _
        rw [show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
        simp)
      (by simp [RegsOutside, integerEncoderPrefixWrites, stepBookkeeping])
      (by native_decide) (by rfl)
    obtain ⟨machine4, seg3, reps3, access4, loaded4⟩ := integerEncoderSaveWordStep
      seg2 access1 loaded1 access3 loaded3
      [(frameBase, (BitVec.ofNat 64 args.word0).toNat),
        (frameBase + 40, (BitVec.ofNat 64 args.returnPc).toNat)] reps2
      0x15cbc 8 (BitVec.ofNat 64 args.word1) 8 (.Regidx 11#5) 0x23 0x34 0xb1 0x00
      (seg2.reg x2 _ (by simp))
      (by intro premise writes
          exact rX_x11_run premise (BitVec.ofNat 64 args.word1)
            ((writes.get x11 (by decide)).trans (seg2.reg x11 _ (by simp))))
      (by intro word member index bound; simp at member; rcases member with rfl | rfl
          all_goals unfold byteRange
          all_goals omega)
      (by omega) (by omega) (by have aligned := access3.frameAligned; omega) rfl
      (by owned_pc [pcInRanges, integerEncoderU256PreparePcs]) (by native_decide)
      (by configured_store_decode access3.output.configured) (by
        change BitVec.ofNat 64 frameBase + 8#64 = _
        rw [← BitVec.ofNat_add])
      (by simp [RegsOutside, integerEncoderPrefixWrites, stepBookkeeping])
      (by native_decide) (by rfl)
    obtain ⟨machine5, seg4, reps4, access5, loaded5⟩ := integerEncoderSaveWordStep
      seg3 access1 loaded1 access4 loaded4
      [(frameBase + 8, (BitVec.ofNat 64 args.word1).toNat),
        (frameBase, (BitVec.ofNat 64 args.word0).toNat),
        (frameBase + 40, (BitVec.ofNat 64 args.returnPc).toNat)] reps3
      0x15cc0 16 (BitVec.ofNat 64 args.word2) 0x10 (.Regidx 12#5) 0x23 0x38 0xc1 0x00
      (seg3.reg x2 _ (by simp))
      (by intro premise writes
          exact rX_x12_run premise (BitVec.ofNat 64 args.word2)
            ((writes.get x12 (by decide)).trans (seg3.reg x12 _ (by simp))))
      (by intro word member index bound; simp at member
          rcases member with rfl | rfl | rfl
          all_goals unfold byteRange
          all_goals omega)
      (by omega) (by omega) (by have aligned := access4.frameAligned; omega) rfl
      (by owned_pc [pcInRanges, integerEncoderU256PreparePcs]) (by native_decide)
      (by configured_store_decode access4.output.configured) (by
        change BitVec.ofNat 64 frameBase + 0x10#64 = _
        rw [← BitVec.ofNat_add])
      (by simp [RegsOutside, integerEncoderPrefixWrites, stepBookkeeping])
      (by native_decide) (by rfl)
    obtain ⟨machine6, seg5, reps5, access6, loaded6⟩ := integerEncoderSaveWordStep
      seg4 access1 loaded1 access5 loaded5
      [(frameBase + 16, (BitVec.ofNat 64 args.word2).toNat),
        (frameBase + 8, (BitVec.ofNat 64 args.word1).toNat),
        (frameBase, (BitVec.ofNat 64 args.word0).toNat),
        (frameBase + 40, (BitVec.ofNat 64 args.returnPc).toNat)] reps4
      0x15cc4 24 (BitVec.ofNat 64 args.word3) 0x18 (.Regidx 13#5) 0x23 0x3c 0xd1 0x00
      (seg4.reg x2 _ (by simp))
      (by intro premise writes
          exact rX_x13_run premise (BitVec.ofNat 64 args.word3)
            ((writes.get x13 (by decide)).trans (seg4.reg x13 _ (by simp))))
      (by intro word member index bound; simp at member
          rcases member with rfl | rfl | rfl | rfl
          all_goals unfold byteRange
          all_goals omega)
      (by omega) (by omega) (by have aligned := access5.frameAligned; omega) rfl
      (by owned_pc [pcInRanges, integerEncoderU256PreparePcs]) (by native_decide)
      (by configured_store_decode access5.output.configured) (by
        change BitVec.ofNat 64 frameBase + 0x18#64 = _
        rw [← BitVec.ofNat_add])
      (by simp [RegsOutside, integerEncoderPrefixWrites, stepBookkeeping])
      (by native_decide) (by rfl)
    have seg5' := seg5.forget (kv' := [⟨x1, BitVec.ofNat 64 args.returnPc⟩,
      ⟨x2, BitVec.ofNat 64 frameBase⟩]) (by simp)
    obtain ⟨rr6, sourceRun⟩ := configuredRawEncoderStackSourceStep (fromStep + 6) 0x15cc8
      0 0 0x13 0x05 0x01 0x00 machine6 frameBase access6.output.configured seg5'.atPc
      (seg5'.reg x2 _ (by simp)) loaded6 (by native_decide) (by rfl) (by
        change BitVec.ofNat 64 frameBase + sign_extend (m := 64) (0#12) = _
        rw [show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
        simp) (integerEncoderStackSourceDecode machine6 access6.output.configured)
    obtain ⟨rr6', machine7, machine7Eq, seg6⟩ := seg5'.stepWitness
      (by owned_pc [pcInRanges, integerEncoderU256PreparePcs]) (by native_decide)
      x10 (BitVec.ofNat 64 frameBase) 0x15ccc ⟨rr6, sourceRun⟩ (by native_decide)
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [integerEncoderPrefixWrites]) (by decide) (by decide)
      (by simp [RegsOutside, integerEncoderPrefixWrites, stepBookkeeping])
    have seg6' := seg6.forget (kv' := [⟨x10, BitVec.ofNat 64 frameBase⟩,
      ⟨x1, BitVec.ofNat 64 args.returnPc⟩, ⟨x2, BitVec.ofNat 64 frameBase⟩]) (by simp)
    have access7 := access1.ofSeg seg6'
    have loaded7 := integerEncoderCodeOfSeg access1 loaded1 seg6'
    obtain ⟨rr7, lengthRun⟩ := configuredRawWriteOutputLengthStep (fromStep + 7) 0x15ccc 32
      0x20 0x93 0x05 0x00 0x02 machine7 access7.output.configured seg6'.atPc loaded7
      (by native_decide) (by rfl) (by native_decide)
      (integerEncoderU256LengthDecode machine7 access7.output.configured)
    obtain ⟨rr7', machine8, machine8Eq, seg7⟩ := seg6'.stepWitness
      (by owned_pc [pcInRanges, integerEncoderU256PreparePcs]) (by native_decide)
      x11 (BitVec.ofNat 64 32) 0x15cd0 ⟨rr7, lengthRun⟩ (by native_decide)
      (by intro register bookkeeping; exact Or.inl bookkeeping)
      (by simp [integerEncoderPrefixWrites]) (by decide) (by decide)
      (by simp [RegsOutside, integerEncoderPrefixWrites, stepBookkeeping])
    let prepared : EndpointState := { before with machine := machine8 }
    have savedReturn6 : UIntRep 8 machine6.mem (frameBase + 40) args.returnPc := by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt args.returnFits] using
        reps5 (frameBase + 40, (BitVec.ofNat 64 args.returnPc).toNat) (by simp)
    have word0At6 : UIntRep 8 machine6.mem frameBase args.word0 := by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt args.word0Fits] using
        reps5 (frameBase, (BitVec.ofNat 64 args.word0).toNat) (by simp)
    have word1At6 : UIntRep 8 machine6.mem (frameBase + 8) args.word1 := by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt args.word1Fits] using
        reps5 (frameBase + 8, (BitVec.ofNat 64 args.word1).toNat) (by simp)
    have word2At6 : UIntRep 8 machine6.mem (frameBase + 16) args.word2 := by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt args.word2Fits] using
        reps5 (frameBase + 16, (BitVec.ofNat 64 args.word2).toNat) (by simp)
    have word3At6 : UIntRep 8 machine6.mem (frameBase + 24) args.word3 := by
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt args.word3Fits] using
        reps5 (frameBase + 24, (BitVec.ofNat 64 args.word3).toNat) (by simp)
    have savedReturn8 : UIntRep 8 machine8.mem (frameBase + 40) args.returnPc := by
      rw [machine8Eq, machine7Eq]
      simpa using savedReturn6
    have word0At8 : UIntRep 8 machine8.mem frameBase args.word0 := by
      rw [machine8Eq, machine7Eq]
      simpa using word0At6
    have word1At8 : UIntRep 8 machine8.mem (frameBase + 8) args.word1 := by
      rw [machine8Eq, machine7Eq]
      simpa using word1At6
    have word2At8 : UIntRep 8 machine8.mem (frameBase + 16) args.word2 := by
      rw [machine8Eq, machine7Eq]
      simpa using word2At6
    have word3At8 : UIntRep 8 machine8.mem (frameBase + 24) args.word3 := by
      rw [machine8Eq, machine7Eq]
      simpa using word3At6
    have firstPair := UIntRep.twoWordsBytesRep word0At8 word1At8
    have thirdBytes : BytesRep machine8.mem
        (frameBase + (encodeNatLE 8 args.word0 ++ encodeNatLE 8 args.word1).size)
        (encodeNatLE 8 args.word2) := by
      simpa only [Array.size_append, encodeNatLE_size, Nat.add_assoc] using
        UIntRep.bytesRepEncodeNatLEEight word2At8
    have firstThree := BytesRep.appendAdjacent firstPair thirdBytes
    have fourthBytes : BytesRep machine8.mem
        (frameBase +
          ((encodeNatLE 8 args.word0 ++ encodeNatLE 8 args.word1) ++
            encodeNatLE 8 args.word2).size)
        (encodeNatLE 8 args.word3) := by
      simpa only [Array.size_append, encodeNatLE_size, Nat.add_assoc] using
        UIntRep.bytesRepEncodeNatLEEight word3At8
    have encoded : BytesRep machine8.mem frameBase (integerEncoderBytes 4 args) := by
      unfold integerEncoderBytes
      rw [if_neg (show (4 : Nat) ≠ 2 by decide)]
      exact BytesRep.appendAdjacent firstThree fourthBytes
    have machineTrace : ScopedTrace (pcInRanges integerEncoderU256PreparePcs)
        (fun pc => pc = 0x15cd0) (fun _ _ _ _ _ => False) fromStep 8
        before.machine machine8 := by
      have tail : ScopedTrace (pcInRanges integerEncoderU256PreparePcs)
          (fun pc => pc = 0x15cd0) (fun _ _ _ _ _ => False) (fromStep + 1) 7
          machine1 machine8 := by
        simpa using seg7.confined 0 machine8
          (ScopedTrace.exitAt (fromStep + 1 + 7) machine8 0x15cd0 seg7.atPc rfl)
      exact ScopedTrace.ownStep fromStep 7 0x15cb0 before.machine machine1 machine8 atPc
        (by owned_pc [pcInRanges, integerEncoderU256PreparePcs]) (by native_decide) run0 tail
    refine ⟨prepared, ?_⟩
    refine
      { trace := by
          have localTrace := liftIntegerEncoderTrace before (by
            intro range member
            simp [integerEncoderU256PreparePcs] at member
            rcases member with rfl
            omega) machineTrace
          exact localTrace.weaken (by
            intro pc inside
            unfold pcInRanges at inside ⊢
            rcases inside with ⟨range, member, lower, upper⟩
            simp [integerEncoderU256PreparePcs] at member
            rcases member with rfl
            by_cases firstRange : pc.toNat < 0x15ccc
            · exact ⟨(0x15cb0, 0x15ccc), by simp [integerEncoderU256ExecutionPcs], lower,
                firstRange⟩
            · exact ⟨(0x15ccc, 0x15cd8), by simp [integerEncoderU256ExecutionPcs],
                by omega, by omega⟩)
        atPc := by simpa [prepared] using seg7.atPc
        returnInside := returnInside
        frameLower := frameLower
        entryLink := link
        entryStack := stack
        source := by
          change machine8.regs.get? x10 = some (BitVec.ofNat 64 frameBase)
          exact seg7.reg x10 _ (by simp)
        stack := by
          change machine8.regs.get? x2 = some (BitVec.ofNat 64 frameBase)
          exact seg7.reg x2 _ (by simp)
        length := by simpa [prepared] using seg7.reg x11 _ (by simp)
        savedReturn := by simpa [prepared, frameBase] using savedReturn8
        bytes := by simpa [prepared, frameBase] using encoded
        bytesSize := by simp [integerEncoderBytes, encodeNatLE_size]
        outsideOutput := by
          intro index bound
          apply access.outputDisjoint index
          have size : (integerEncoderBytes 4 args).size = 32 := by
            simp [integerEncoderBytes, encodeNatLE_size]
          omega
        loaded := by simpa [prepared] using integerEncoderCodeOfSeg access1 loaded1 seg7
        access := by simpa [prepared, frameBase] using access1.ofSeg seg7
        writes := by
          change WritesOnlyRegs (RegSet.union (RegSet.only x2) integerEncoderPrefixWrites)
            before.machine machine8
          have first : WritesOnlyRegs
              (RegSet.union (RegSet.only x2) integerEncoderPrefixWrites)
              before.machine machine1 := firstWrites.mono (by
            intro register written
            rcases written with bookkeeping | destination
            · exact Or.inr (Or.inl bookkeeping)
            · exact Or.inl destination)
          have rest : WritesOnlyRegs
              (RegSet.union (RegSet.only x2) integerEncoderPrefixWrites) machine1 machine8 :=
            seg7.writes.mono (by intro register written; exact Or.inr written)
          exact first.trans_same rest
        mem := by
          have initial : WritesOnlyWithin (integerEncoderFrame frameBase 48)
              before.machine machine1 := by
            apply writesOnlyWithin_of_mem_eq
            exact afterRegisterWrite_mem before.machine 0x15cb0 r0 x2
              (BitVec.ofNat 64 frameBase)
          simpa [prepared, frameBase] using initial.trans_same seg7.mem
        aux := by simpa [prepared, machine1] using seg7.aux
        stdout := rfl
        stdin := rfl
        stdinCursor := rfl
        exitCode := rfl }
  rcases u128 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases entry with ⟨atPc, link, stack, words, returnInside, frameLower, access, loaded⟩
  rcases words with ⟨word0, word1, _⟩
  let frameBase := args.stackPointer - 32
  have stackResult : BitVec.ofNat 64 frameBase =
      iTypeResult .ADDI 0xfe0 (BitVec.ofNat 64 args.stackPointer) :=
    integerEncoderStackSubtractResult args.stackPointer 32 0xfe0 frameLower
      args.stackFits (by native_decide)
  have decode0 : Runs
      (ext_decode (fetchWord 0x13#8 0x01#8 0x01#8 0xfe#8))
      (tryStepControlFlowAfterIncrement before.machine)
      (tryStepControlFlowAfterIncrement before.machine)
      (.ITYPE (0xfe0, .Regidx 2#5, .Regidx 2#5, .ADDI)) := by
    configured_decode access.output.configured
  obtain ⟨r0, run0⟩ := configuredAddiX2Step fromStep 0x15ce4 before.machine 0xfe0
    (BitVec.ofNat 64 args.stackPointer) (BitVec.ofNat 64 frameBase)
    0x13 0x01 0x01 0xfe access.output.configured atPc stack loaded stackResult decode0
    (base := by rfl)
  let machine1 := afterRegisterWrite before.machine 0x15ce4 r0 x2 (BitVec.ofNat 64 frameBase)
  have atPc1 : machine1.regs.get? PC = some 0x15ce8 := by
    simpa [machine1] using afterRegisterWrite_pc before.machine 0x15ce4 r0 x2
      (BitVec.ofNat 64 frameBase)
  have stack1 : machine1.regs.get? x2 = some (BitVec.ofNat 64 frameBase) := by
    simpa [machine1] using afterRegisterWrite_destination before.machine 0x15ce4 r0 x2
      (BitVec.ofNat 64 frameBase) (by decide) (by decide)
  have link1 : machine1.regs.get? x1 = some (BitVec.ofNat 64 args.returnPc) :=
    (afterRegisterWrite_writes before.machine 0x15ce4 r0 x2
      (BitVec.ofNat 64 frameBase)).get x1 (by simp [stepBookkeeping]) |>.trans link
  have word01 : machine1.regs.get? x10 = some (BitVec.ofNat 64 args.word0) :=
    (afterRegisterWrite_writes before.machine 0x15ce4 r0 x2
      (BitVec.ofNat 64 frameBase)).get x10 (by simp [stepBookkeeping]) |>.trans word0
  have word11 : machine1.regs.get? x11 = some (BitVec.ofNat 64 args.word1) :=
    (afterRegisterWrite_writes before.machine 0x15ce4 r0 x2
      (BitVec.ofNat 64 frameBase)).get x11 (by simp [stepBookkeeping]) |>.trans word1
  have configured1 : ConfiguredMachinePre EndpointMachinePc machine1 := by
    exact access.output.configured.afterRegisterWrite 0x15ce4 r0 x2
      (BitVec.ofNat 64 frameBase) (by simp [instructionPreserved, platformPreserved])
  have access1 : IntegerEncoderMachineAccess frameBase 32 machine1 :=
    access.ofWrites (afterRegisterWrite_writes before.machine 0x15ce4 r0 x2
      (BitVec.ofNat 64 frameBase)) (by simp [stepBookkeeping]) configured1
  have loaded1 : Artifacts.programImage.fileBytesLoadedFaithfully machine1.mem := by
    simpa [machine1] using fileBytesLoadedFaithfully_afterRegisterWrite Artifacts.programImage
      before.machine 0x15ce4 r0 x2 (BitVec.ofNat 64 frameBase) loaded
  have seg0 := (((Seg.nil (pcInRanges integerEncoderU128PreparePcs)
    (fun pc => pc = 0x15cfc) (fun _ _ _ _ _ => False) integerEncoderPrefixWrites
    (integerEncoderFrame frameBase 32) (fromStep + 1) configured1.retiredCounter atPc1).know
      x2 (BitVec.ofNat 64 frameBase) stack1).know
      x1 (BitVec.ofNat 64 args.returnPc) link1).know
      x10 (BitVec.ofNat 64 args.word0) word01 |>.know
      x11 (BitVec.ofNat 64 args.word1) word11
  have reps0 : SavedWordReps machine1 [] := by simp [SavedWordReps]
  obtain ⟨machine2, seg1, reps1, access2, loaded2⟩ := integerEncoderSaveWordStep
    seg0 access1 loaded1 access1 loaded1 [] reps0 0x15ce8 24
    (BitVec.ofNat 64 args.returnPc) 0x18 (.Regidx 1#5) 0x23 0x3c 0x11 0x00 stack1
    (by intro premise writes
        exact rX_x1_run premise (BitVec.ofNat 64 args.returnPc)
          ((writes.get x1 (by decide)).trans (seg0.reg x1 _ (by simp))))
    (by simp) (by omega) (by omega) (by have aligned := access1.frameAligned; omega)
    rfl (by owned_pc [pcInRanges, integerEncoderU128PreparePcs]) (by native_decide)
    (by configured_store_decode configured1) (by
      change BitVec.ofNat 64 frameBase + 0x18#64 = _
      rw [← BitVec.ofNat_add])
    (by simp [RegsOutside, integerEncoderPrefixWrites, stepBookkeeping])
    (by native_decide) (by rfl)
  obtain ⟨machine3, seg2, reps2, access3, loaded3⟩ := integerEncoderSaveWordStep
    seg1 access1 loaded1 access2 loaded2
    [(frameBase + 24, (BitVec.ofNat 64 args.returnPc).toNat)] reps1
    0x15cec 0 (BitVec.ofNat 64 args.word0) 0 (.Regidx 10#5) 0x23 0x30 0xa1 0x00
    (seg1.reg x2 _ (by simp))
    (by intro premise writes
        exact rX_x10_run premise (BitVec.ofNat 64 args.word0)
          ((writes.get x10 (by decide)).trans (seg1.reg x10 _ (by simp))))
    (by
      intro word member index bound
      simp at member
      rcases member with rfl
      unfold byteRange
      omega)
    (by omega) (by omega) (by have aligned := access2.frameAligned; omega) rfl
    (by owned_pc [pcInRanges, integerEncoderU128PreparePcs]) (by native_decide)
    (integerEncoderSaveWord0Decode machine2 access2.output.configured) (by
      change BitVec.ofNat 64 frameBase + 0#64 = _
      simp) (by simp [RegsOutside, integerEncoderPrefixWrites, stepBookkeeping])
    (by native_decide) (by rfl)
  obtain ⟨machine4, seg3, reps3, access3', loaded3'⟩ := integerEncoderSaveWordStep
    seg2 access1 loaded1 access3 loaded3
    [(frameBase, (BitVec.ofNat 64 args.word0).toNat),
      (frameBase + 24, (BitVec.ofNat 64 args.returnPc).toNat)] reps2
    0x15cf0 8 (BitVec.ofNat 64 args.word1) 8 (.Regidx 11#5) 0x23 0x34 0xb1 0x00
    (seg2.reg x2 _ (by simp))
    (by intro premise writes
        exact rX_x11_run premise (BitVec.ofNat 64 args.word1)
          ((writes.get x11 (by decide)).trans (seg2.reg x11 _ (by simp))))
    (by
      intro word member index bound
      simp at member
      rcases member with rfl | rfl
      all_goals unfold byteRange
      all_goals omega)
    (by omega) (by omega) (by have aligned := access3.frameAligned; omega) rfl
    (by owned_pc [pcInRanges, integerEncoderU128PreparePcs]) (by native_decide)
    (integerEncoderSaveWord1Decode machine3 access3.output.configured) (by
      change BitVec.ofNat 64 frameBase + 8#64 = _
      rw [← BitVec.ofNat_add])
    (by simp [RegsOutside, integerEncoderPrefixWrites, stepBookkeeping])
    (by native_decide) (by rfl)
  have seg3' := seg3.forget (kv' := [⟨x11, BitVec.ofNat 64 args.word1⟩,
    ⟨x1, BitVec.ofNat 64 args.returnPc⟩, ⟨x2, BitVec.ofNat 64 frameBase⟩]) (by simp)
  have access4 := access3'
  have loaded4 := loaded3'
  obtain ⟨rr4, sourceRun⟩ := configuredRawEncoderStackSourceStep (fromStep + 4) 0x15cf4
    0 0 0x13 0x05 0x01 0x00 machine4 frameBase access4.output.configured seg3'.atPc
    (seg3'.reg x2 _ (by simp)) loaded4 (by native_decide) (by rfl) (by
      change BitVec.ofNat 64 frameBase + sign_extend (m := 64) (0#12) = _
      rw [show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
      simp) (integerEncoderStackSourceDecode machine4 access4.output.configured)
  obtain ⟨rr4', machine5, machine5Eq, seg4⟩ := seg3'.stepWitness
    (by owned_pc [pcInRanges, integerEncoderU128PreparePcs]) (by native_decide)
    x10 (BitVec.ofNat 64 frameBase) 0x15cf8 ⟨rr4, sourceRun⟩ (by native_decide)
    (by intro register bookkeeping; exact Or.inl bookkeeping) (by simp [integerEncoderPrefixWrites])
    (by decide) (by decide) (by simp [RegsOutside, integerEncoderPrefixWrites, stepBookkeeping])
  have seg4' := seg4.forget (kv' := [⟨x10, BitVec.ofNat 64 frameBase⟩,
    ⟨x1, BitVec.ofNat 64 args.returnPc⟩, ⟨x2, BitVec.ofNat 64 frameBase⟩]) (by simp)
  have access5 := access1.ofSeg seg4'
  have loaded5 := integerEncoderCodeOfSeg access1 loaded1 seg4'
  obtain ⟨rr5, lengthRun⟩ := configuredRawWriteOutputLengthStep (fromStep + 5) 0x15cf8 16
    0x10 0x93 0x05 0x00 0x01 machine5 access5.output.configured seg4'.atPc loaded5
    (by native_decide) (by rfl) (by native_decide)
    (integerEncoderU128LengthDecode machine5 access5.output.configured)
  obtain ⟨rr5', machine6, machine6Eq, seg5⟩ := seg4'.stepWitness
    (by owned_pc [pcInRanges, integerEncoderU128PreparePcs]) (by native_decide)
    x11 (BitVec.ofNat 64 16) 0x15cfc ⟨rr5, lengthRun⟩ (by native_decide)
    (by intro register bookkeeping; exact Or.inl bookkeeping) (by simp [integerEncoderPrefixWrites])
    (by decide) (by decide) (by simp [RegsOutside, integerEncoderPrefixWrites, stepBookkeeping])
  let prepared : EndpointState := { before with machine := machine6 }
  have savedReturn4 : UIntRep 8 machine4.mem (frameBase + 24) args.returnPc := by
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt args.returnFits] using
      reps3 (frameBase + 24, (BitVec.ofNat 64 args.returnPc).toNat) (by simp)
  have word0At4 : UIntRep 8 machine4.mem frameBase args.word0 := by
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt args.word0Fits] using
      reps3 (frameBase, (BitVec.ofNat 64 args.word0).toNat) (by simp)
  have word1At4 : UIntRep 8 machine4.mem (frameBase + 8) args.word1 := by
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt args.word1Fits] using
      reps3 (frameBase + 8, (BitVec.ofNat 64 args.word1).toNat) (by simp)
  have savedReturn6 : UIntRep 8 machine6.mem (frameBase + 24) args.returnPc := by
    rw [machine6Eq, machine5Eq]
    simpa using savedReturn4
  have word0At6 : UIntRep 8 machine6.mem frameBase args.word0 := by
    rw [machine6Eq, machine5Eq]
    simpa using word0At4
  have word1At6 : UIntRep 8 machine6.mem (frameBase + 8) args.word1 := by
    rw [machine6Eq, machine5Eq]
    simpa using word1At4
  have encoded : BytesRep machine6.mem frameBase (integerEncoderBytes 2 args) := by
    unfold integerEncoderBytes
    simp only [if_pos rfl]
    exact UIntRep.twoWordsBytesRep word0At6 word1At6
  have machineTrace : ScopedTrace (pcInRanges integerEncoderU128PreparePcs)
      (fun pc => pc = 0x15cfc) (fun _ _ _ _ _ => False) fromStep 6
      before.machine machine6 := by
    have tail : ScopedTrace (pcInRanges integerEncoderU128PreparePcs)
        (fun pc => pc = 0x15cfc) (fun _ _ _ _ _ => False) (fromStep + 1) 5
        machine1 machine6 := by
      simpa using seg5.confined 0 machine6
        (ScopedTrace.exitAt (fromStep + 1 + 5) machine6 0x15cfc seg5.atPc rfl)
    exact ScopedTrace.ownStep fromStep 5 0x15ce4 before.machine machine1 machine6 atPc
      (by owned_pc [pcInRanges, integerEncoderU128PreparePcs]) (by native_decide) run0
      tail
  refine ⟨prepared, ?_⟩
  refine
    { trace := by
        have localTrace := liftIntegerEncoderTrace before (by
          intro range member
          simp [integerEncoderU128PreparePcs] at member
          rcases member with rfl
          omega) machineTrace
        exact localTrace.weaken (by
          intro pc inside
          unfold pcInRanges at inside ⊢
          rcases inside with ⟨range, member, lower, upper⟩
          simp [integerEncoderU128PreparePcs] at member
          rcases member with rfl
          by_cases firstRange : pc.toNat < 0x15cf8
          · exact ⟨(0x15ce4, 0x15cf8), by simp [integerEncoderU128ExecutionPcs], lower,
              firstRange⟩
          · exact ⟨(0x15cf8, 0x15d04), by simp [integerEncoderU128ExecutionPcs],
              by omega, by omega⟩)
      atPc := by simpa [prepared] using seg5.atPc
      returnInside := returnInside
      frameLower := frameLower
      entryLink := link
      entryStack := stack
      source := by
        change machine6.regs.get? x10 = some (BitVec.ofNat 64 frameBase)
        exact seg5.reg x10 _ (by simp)
      stack := by
        change machine6.regs.get? x2 = some (BitVec.ofNat 64 frameBase)
        exact seg5.reg x2 _ (by simp)
      length := by simpa [prepared] using seg5.reg x11 _ (by simp)
      savedReturn := by simpa [prepared, frameBase] using savedReturn6
      bytes := by simpa [prepared, frameBase] using encoded
      bytesSize := by simp [integerEncoderBytes, encodeNatLE_size]
      outsideOutput := by
        intro index bound
        apply access.outputDisjoint index
        have size : (integerEncoderBytes 2 args).size = 16 := by
          simp [integerEncoderBytes, encodeNatLE_size]
        omega
      loaded := by simpa [prepared] using integerEncoderCodeOfSeg access1 loaded1 seg5
      access := by simpa [prepared, frameBase] using access1.ofSeg seg5
      writes := by
        change WritesOnlyRegs (RegSet.union (RegSet.only x2) integerEncoderPrefixWrites)
          before.machine machine6
        have first : WritesOnlyRegs
            (RegSet.union (RegSet.only x2) integerEncoderPrefixWrites)
            before.machine machine1 :=
          (afterRegisterWrite_writes before.machine 0x15ce4 r0 x2
          (BitVec.ofNat 64 frameBase)).mono (by
            intro register written
            rcases written with bookkeeping | destination
            · exact Or.inr (Or.inl bookkeeping)
            · exact Or.inl destination)
        have rest : WritesOnlyRegs
            (RegSet.union (RegSet.only x2) integerEncoderPrefixWrites) machine1 machine6 :=
          seg5.writes.mono (by
            intro register written
            exact Or.inr written)
        exact first.trans_same rest
      mem := by
        have initial : WritesOnlyWithin (integerEncoderFrame frameBase 32)
            before.machine machine1 := by
          apply writesOnlyWithin_of_mem_eq
          exact afterRegisterWrite_mem before.machine 0x15ce4 r0 x2
            (BitVec.ofNat 64 frameBase)
        simpa [prepared, frameBase] using initial.trans_same seg5.mem
      aux := by simpa [prepared, machine1] using seg5.aux
      stdout := rfl
      stdin := rfl
      stdinCursor := rfl
      exitCode := rfl }

/-- Integer encoders use the shared called-encoder return-site schema. -/
abbrev IntegerEncoderFinishSite := EncoderCallFinishSite

private def integerEncoderU256FinishSite : IntegerEncoderFinishSite 48 0x15cd8
    integerEncoderU256ExecutionPcs integerEncoderU256ExitPcs where
  loadPc := 0x15cd8
  restorePc := 0x15cdc
  retPc := 0x15ce0
  returnOffset := 40
  loadImm := 0x28
  restoreImm := 0x30
  loadByte0 := 0x83
  loadByte1 := 0x30
  loadByte2 := 0x81
  loadByte3 := 0x02
  restoreByte0 := 0x13
  restoreByte1 := 0x01
  restoreByte2 := 0x01
  restoreByte3 := 0x03
  pcs := by decide
  loadStarts := rfl
  frameLarge := by decide
  returnSlot := by decide
  loadSign := by native_decide
  restoreSign := by native_decide
  loadSite := by native_decide
  restoreSite := by native_decide
  retSite := by native_decide
  loadBase := by rfl
  restoreBase := by rfl
  loadDecode := by intro state configured; configured_decode configured
  restoreDecode := by intro state configured; configured_decode configured
  loadInside := by owned_pc [pcInRanges, integerEncoderU256ExecutionPcs]
  restoreInside := by owned_pc [pcInRanges, integerEncoderU256ExecutionPcs]
  retInside := by owned_pc [pcInRanges, integerEncoderU256ExecutionPcs]
  loadLocal := by owned_pc [pcInRanges]
  restoreLocal := by owned_pc [pcInRanges]
  retLocal := by owned_pc [pcInRanges]
  localInside := by
    intro pc inside
    unfold pcInRanges at inside ⊢
    rcases inside with ⟨range, member, lower, upper⟩
    simp at member
    rcases member with rfl
    exact ⟨(0x15cd8, 0x15ce4), by simp [integerEncoderU256ExecutionPcs], lower, upper⟩
  loadNotExit := by simp [pcInList, integerEncoderU256ExitPcs]
  restoreNotExit := by simp [pcInList, integerEncoderU256ExitPcs]
  retNotExit := by simp [pcInList, integerEncoderU256ExitPcs]
  localAfterHost := by native_decide
  returnFacts := by
    intro returnPc fits listed
    simp [pcInList, integerEncoderU256ExitPcs, Nat.mod_eq_of_lt fits] at listed
    rcases listed with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals native_decide

private def integerEncoderU128FinishSite : IntegerEncoderFinishSite 32 0x15d04
    integerEncoderU128ExecutionPcs integerEncoderU128ExitPcs where
  loadPc := 0x15d04
  restorePc := 0x15d08
  retPc := 0x15d0c
  returnOffset := 24
  loadImm := 0x18
  restoreImm := 0x20
  loadByte0 := 0x83
  loadByte1 := 0x30
  loadByte2 := 0x81
  loadByte3 := 0x01
  restoreByte0 := 0x13
  restoreByte1 := 0x01
  restoreByte2 := 0x01
  restoreByte3 := 0x02
  pcs := by decide
  loadStarts := rfl
  frameLarge := by decide
  returnSlot := by decide
  loadSign := by native_decide
  restoreSign := by native_decide
  loadSite := by native_decide
  restoreSite := by native_decide
  retSite := by native_decide
  loadBase := by rfl
  restoreBase := by rfl
  loadDecode := by intro state configured; configured_decode configured
  restoreDecode := by intro state configured; configured_decode configured
  loadInside := by owned_pc [pcInRanges, integerEncoderU128ExecutionPcs]
  restoreInside := by owned_pc [pcInRanges, integerEncoderU128ExecutionPcs]
  retInside := by owned_pc [pcInRanges, integerEncoderU128ExecutionPcs]
  loadLocal := by owned_pc [pcInRanges]
  restoreLocal := by owned_pc [pcInRanges]
  retLocal := by owned_pc [pcInRanges]
  localInside := by
    intro pc inside
    unfold pcInRanges at inside ⊢
    rcases inside with ⟨range, member, lower, upper⟩
    simp at member
    rcases member with rfl
    exact ⟨(0x15d04, 0x15d10), by simp [integerEncoderU128ExecutionPcs], lower, upper⟩
  loadNotExit := by simp [pcInList, integerEncoderU128ExitPcs]
  restoreNotExit := by simp [pcInList, integerEncoderU128ExitPcs]
  retNotExit := by simp [pcInList, integerEncoderU128ExitPcs]
  localAfterHost := by native_decide
  returnFacts := by
    intro returnPc fits listed
    simp [pcInList, integerEncoderU128ExitPcs, Nat.mod_eq_of_lt fits] at listed
    rcases listed with rfl | rfl | rfl
    all_goals native_decide

private def integerEncoderSuffixWrites (register : Register) : Prop :=
  encoderCallFinishWrites register

private theorem encoderInlinePreservedExceptStack_disjoint_integerEncoderPrefixWrites :
    RegSet.Disjoint (fun register => encoderInlinePreserved register ∧ register ≠ x2)
      (RegSet.union (RegSet.only x2) integerEncoderPrefixWrites) := by
  intro register preserved written
  change register = x2 ∨ integerEncoderPrefixWrites register at written
  simp [encoderInlinePreserved, integerEncoderPrefixWrites, instructionPreserved,
    platformPreserved, stepBookkeeping] at preserved written
  grind

private theorem encoderInlinePreservedExceptStack_disjoint_integerEncoderSuffixWrites :
    RegSet.Disjoint (fun register => encoderInlinePreserved register ∧ register ≠ x2)
      integerEncoderSuffixWrites := by
  intro register preserved written
  simp [encoderInlinePreserved, integerEncoderSuffixWrites, encoderCallFinishWrites,
    instructionPreserved,
    platformPreserved, stepBookkeeping] at preserved written
  grind

private theorem instructionPreserved_disjoint_integerEncoderSuffixWrites :
    RegSet.Disjoint instructionPreserved integerEncoderSuffixWrites :=
  instructionPreserved_disjoint_encoderCallFinishWrites

/-- Restore `ra` and `sp`, then return, for both fixed-width integer encoders. -/
private theorem integerEncoderFinish
    (frameSize wordCount outputEntry callReturn fromStep prefixCount : Nat)
    (executionPcs : List Elflings.PcRange) (exitPcs : List Nat)
    (site : IntegerEncoderFinishSite frameSize callReturn executionPcs exitPcs)
    (args : IntegerEncoderArgs) (before prepared outputState : EndpointState)
    (handoff : IntegerEncoderPreparedHandoff executionPcs exitPcs outputEntry frameSize
      wordCount fromStep prefixCount args before prepared)
    (outputExit : RawEncoderExit callReturn
      { sourceAddress := args.stackPointer - frameSize
        bytes := integerEncoderBytes wordCount args }
      () prepared outputState) :
    ∃ after,
      ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
        (fromStep + prefixCount + 7) 3 outputState after ∧
      (∃ pc, EndpointPc after = some pc ∧ pcInList exitPcs pc) ∧
      IntegerEncoderExit frameSize wordCount args () before after := by
  rcases outputExit with ⟨outputPc, outputStdout, outputStdin, outputCursor, outputCode,
    outputMem, outputFrame⟩
  rcases outputFrame with ⟨outputAgree, outputRetired, outputLoaded, outputAux⟩
  let frameBase := args.stackPointer - frameSize
  have outputAccess := handoff.access.ofEncoderFrame outputAgree outputRetired
  have outputStack : outputState.machine.regs.get? x2 =
      some (BitVec.ofNat 64 frameBase) :=
    (outputAgree x2 (by simp [encoderInlinePreserved])).trans handoff.stack
  have savedOutput : UIntRep 8 outputState.machine.mem
      (frameBase + site.returnOffset) args.returnPc := by
    have saved := handoff.savedReturn.of_writesOnlyWithin outputMem (by
      intro index bound
      simpa only [Nat.add_assoc] using
        handoff.access.outputDisjoint (frameSize - 8 + index) (by
          have large := site.frameLarge
          omega))
    simpa [frameBase, site.returnSlot.1] using saved
  obtain ⟨machine3, seg3⟩ := encoderCallFinishSeg site
    (fromStep + prefixCount + 7) args.stackPointer args.returnPc outputState.machine
    handoff.frameLower args.stackFits args.returnFits handoff.returnInside
    outputAccess.output.configured outputPc outputStack savedOutput
    (outputAccess.loadPma site.returnOffset site.returnSlot.2.1 site.returnSlot.2.2)
    (outputAccess.loadNoMMIO site.returnOffset site.returnSlot.2.1 site.returnSlot.2.2)
    outputAccess.frameAligned outputLoaded
  let after : EndpointState := { outputState with machine := machine3 }
  have machineTrace : ScopedTrace (pcInRanges [(site.loadPc, site.retPc + 4)]) (pcInList exitPcs)
      (fun _ _ _ _ _ => False) (fromStep + prefixCount + 7) 3
      outputState.machine machine3 := by
    simpa using seg3.confined 0 machine3
      (ScopedTrace.exitAt (fromStep + prefixCount + 7 + 3) machine3
        (BitVec.ofNat 64 args.returnPc) seg3.atPc handoff.returnInside)
  have endpointTrace : ConfinedTrace EndpointStep EndpointPc (pcInRanges executionPcs)
      (fromStep + prefixCount + 7) 3 outputState after := by
    have localTrace := liftIntegerEncoderTrace outputState (by
      intro range member
      simp at member
      rcases member with rfl
      exact site.localAfterHost) machineTrace
    exact localTrace.weaken site.localInside
  refine ⟨after, endpointTrace, ⟨BitVec.ofNat 64 args.returnPc, by simpa [after] using seg3.atPc,
    handoff.returnInside⟩, ?_⟩
  refine ⟨by simpa [after] using seg3.atPc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, seg3.retired, ?_, ?_⟩
  · simpa [after] using seg3.reg x1 (BitVec.ofNat 64 args.returnPc) (by simp)
  · simpa [after] using seg3.reg x2 (BitVec.ofNat 64 args.stackPointer) (by simp)
  · simpa [after, handoff.stdout] using outputStdout
  · simpa [after, handoff.stdin] using outputStdin
  · simpa [after, handoff.stdinCursor] using outputCursor
  · simpa [after, handoff.exitCode] using outputCode
  · have prefixFrame : WritesOnlyWithin (integerEncoderMemory frameBase frameSize)
        before.machine prepared.machine := WritesOnlyWithin.mono
        (fun address inside => Or.inl inside) handoff.mem
    have outputFrame : WritesOnlyWithin (integerEncoderMemory frameBase frameSize)
        prepared.machine outputState.machine := WritesOnlyWithin.mono
        (fun address inside => Or.inr inside) outputMem
    have suffix : WritesOnlyWithin (integerEncoderMemory frameBase frameSize)
        outputState.machine machine3 := WritesOnlyWithin.mono (by simp) seg3.mem
    simpa [after, frameBase] using prefixFrame.trans_same outputFrame |>.trans_same suffix
  · intro register preserved
    rcases preserved with inline | rfl
    · by_cases stackRegister : register = x2
      · subst stackRegister
        exact (seg3.reg x2 _ (by simp)).trans handoff.entryStack.symm
      · have prefixEq := handoff.writes register
          (encoderInlinePreservedExceptStack_disjoint_integerEncoderPrefixWrites register
            ⟨inline, stackRegister⟩)
        have outputEq := outputAgree register inline
        have suffixEq := seg3.writes register
          (encoderInlinePreservedExceptStack_disjoint_integerEncoderSuffixWrites register
            ⟨inline, stackRegister⟩)
        exact suffixEq.trans (outputEq.trans prefixEq)
    · exact (seg3.reg x1 _ (by simp)).trans handoff.entryLink.symm
  · have memoryEq := seg3.memEq (by simp)
    simpa [after, memoryEq] using outputLoaded
  · exact ⟨seg3.aux.1.trans (outputAux.1.trans handoff.aux.1),
      seg3.aux.2.1.trans (outputAux.2.1.trans handoff.aux.2.1),
      seg3.aux.2.2.trans (outputAux.2.2.trans handoff.aux.2.2)⟩

abbrev Proposed_ssz_decode_observation_Encoder_int_fi_1_43a9_Contract : Prop :=
  IntegerEncoderInstanceContract 0x15cb0 48 4
    integerEncoderU256ExecutionPcs integerEncoderU256ExitPcs

abbrev Proposed_ssz_decode_observation_Encoder_int_fi_1_4494_Contract : Prop :=
  IntegerEncoderInstanceContract 0x15ce4 32 2
    integerEncoderU128ExecutionPcs integerEncoderU128ExitPcs

private def integerEncoderU256Site : IntegerEncoderSite 0x15cb0 48 4 0x15ccc 0x15cd8
    8 3 integerEncoderU256ExecutionPcs integerEncoderU256ExitPcs where
  totalCount := by native_decide
  output := integerEncoderU256OutputSite
  prepare := by
    intro fromStep args before entry
    exact integerEncoderPrepare 0x15cb0 48 4 0x15ccc 8 integerEncoderU256ExecutionPcs
      integerEncoderU256ExitPcs fromStep args before entry (Or.inl ⟨rfl, rfl, rfl, rfl,
        rfl, rfl, rfl⟩)
  finish := by
    intro fromStep args before prepared outputState handoff outputExit
    exact integerEncoderFinish 48 4 0x15ccc 0x15cd8 fromStep 8 integerEncoderU256ExecutionPcs
      integerEncoderU256ExitPcs integerEncoderU256FinishSite args before prepared outputState
      handoff outputExit

private def integerEncoderU128Site : IntegerEncoderSite 0x15ce4 32 2 0x15cf8 0x15d04
    6 3 integerEncoderU128ExecutionPcs integerEncoderU128ExitPcs where
  totalCount := by native_decide
  output := integerEncoderU128OutputSite
  prepare := by
    intro fromStep args before entry
    exact integerEncoderPrepare 0x15ce4 32 2 0x15cf8 6 integerEncoderU128ExecutionPcs
      integerEncoderU128ExitPcs fromStep args before entry (Or.inr ⟨rfl, rfl, rfl, rfl,
        rfl, rfl, rfl⟩)
  finish := by
    intro fromStep args before prepared outputState handoff outputExit
    exact integerEncoderFinish 32 2 0x15cf8 0x15d04 fromStep 6 integerEncoderU128ExecutionPcs
      integerEncoderU128ExitPcs integerEncoderU128FinishSite args before prepared outputState
      handoff outputExit

theorem proposed_integerEncoder_43a9_proved :
    Proposed_ssz_decode_observation_Encoder_int_fi_1_43a9_Contract :=
  integerEncoderInstanceContract_of_site integerEncoderU256Site

theorem proposed_integerEncoder_4494_proved :
    Proposed_ssz_decode_observation_Encoder_int_fi_1_4494_Contract :=
  integerEncoderInstanceContract_of_site integerEncoderU128Site

end BinaryFv.Zesu.Staging
