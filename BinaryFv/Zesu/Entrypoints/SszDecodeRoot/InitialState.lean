import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.ExecutableCorrectness
import BinaryFv.RiscV.Logic.Framing
import BinaryFv.RiscV.Proof.ImageLoadCorrectness

/-! The computable endpoint initializer satisfies the existing Level 0 entry contract. -/

namespace BinaryFv.Zesu

open PreSail LeanRV64DExecutable.Functions Register BinaryFv.RiscV
open BinaryFv.Binary

private local instance : Inhabited LoadSegment := ⟨⟨0, ByteArray.empty, 0, 0⟩⟩
private local instance : DecidableEq LoadSegment := fun a b => by
  exact decidable_of_iff
    (a.virtualAddress = b.virtualAddress ∧ a.initialBytes = b.initialBytes ∧
      a.memorySize = b.memorySize ∧ a.flags = b.flags) (by cases a; cases b; simp)

private theorem writeMemoryBytes_establishes (address : Nat) (bytes : List UInt8) (start : State) :
    ∃ finish, Runs (writeMemoryBytes address bytes) start finish () ∧
      finish.regs = start.regs ∧
      (∀ other, other < address ∨ address + bytes.length ≤ other →
        finish.mem.get? other = start.mem.get? other) ∧
      (∀ index (bound : index < bytes.length),
        finish.mem.get? (address + index) =
          some (BitVec.ofNat 8 (bytes[index]'bound).toNat)) := by
  induction bytes generalizing address start with
  | nil =>
      exact ⟨start, rfl, rfl, fun _ _ => rfl, fun index bound => (Nat.not_lt_zero index bound).elim⟩
  | cons byte bytes ih =>
      let afterHead : State := { start with
        mem := start.mem.insert address (BitVec.ofNat 8 byte.toNat) }
      obtain ⟨finish, tailRun, tailRegs, tailFrame, tailBytes⟩ := ih (address + 1) afterHead
      have headRun : Runs (PreSail.writeByte address (BitVec.ofNat 8 byte.toNat))
          start afterHead () := by
        exact writeByte_run start address (BitVec.ofNat 8 byte.toNat)
      refine ⟨finish, Runs.bind headRun tailRun, ?_, ?_, ?_⟩
      · simpa [afterHead] using tailRegs
      · intro other outside
        rw [tailFrame other (by simp at outside ⊢; omega)]
        simp only [afterHead, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
        have distinct : address ≠ other := by simp at outside; omega
        simp [distinct]
      · intro index bound
        cases index with
        | zero =>
            simpa only [Nat.add_zero, List.getElem_cons_zero] using (show
              finish.mem.get? address = some (BitVec.ofNat 8 byte.toNat) by
                rw [tailFrame address (by simp)]
                simp [afterHead, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert])
        | succ index =>
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              tailBytes index (by simpa using bound)

private abbrev endpointTextSegment := Artifacts.programImage.segments[0]!
private abbrev endpointContextSegment := Artifacts.programImage.segments[1]!

private theorem endpointSegments : Artifacts.programImage.segments =
    #[endpointTextSegment, endpointContextSegment] := by native_decide

private theorem endpointSegments_disjoint :
    endpointTextSegment.initialEndAddress ≤ endpointContextSegment.virtualAddress := by
  native_decide

private theorem endpointBaseLoaded :
    ∃ finish, Runs initializeEndpointBaseMachine endpointConfiguredMachine finish () ∧
      finish.regs = endpointConfiguredMachine.regs ∧
      Artifacts.programImage.fileBytesLoadedFaithfully finish.mem := by
  obtain ⟨afterContext, contextRun, contextRegs, _contextLow, _contextHigh, contextBytes⟩ :=
    loadFileSegment_establishes endpointContextSegment endpointConfiguredMachine
  obtain ⟨finish, textRun, textRegs, _textLow, textHigh, textBytes⟩ :=
    loadFileSegment_establishes endpointTextSegment afterContext
  have contextAfter : ∀ address byte,
      endpointContextSegment.readFileByte? address = some byte →
      finish.mem.get? address = some (BitVec.ofNat 8 byte.toNat) := by
    intro address byte read
    rw [textHigh address (by
      rw [LoadSegment.readFileByte?] at read
      split at read
      next inside =>
        have rangeBoth : endpointContextSegment.virtualAddress ≤ address ∧
            address < endpointContextSegment.initialEndAddress := by
          simpa [LoadSegment.containsInitialByte] using inside
        have range : endpointContextSegment.virtualAddress ≤ address := by
          exact rangeBoth.1
        exact Nat.le_trans endpointSegments_disjoint range
      next outside => simp at read)]
    exact contextBytes address byte read
  refine ⟨finish, ?_, textRegs.trans contextRegs, ?_⟩
  · unfold initializeEndpointBaseMachine loadFileBackedImage
    rw [endpointSegments]
    exact Runs.bind contextRun (Runs.bind textRun rfl)
  · intro address byte read
    unfold ProgramImage.readFileByte? at read
    cases selectedEq : Artifacts.programImage.fileSegmentAt? address with
    | none => rw [selectedEq] at read; simp at read
    | some segment =>
      rw [selectedEq] at read
      have selected : Artifacts.programImage.segments.toList.find?
          (fun item => item.containsInitialByte address) = some segment := selectedEq
      have member := List.mem_of_find?_eq_some selected
      have member' : segment = endpointTextSegment ∨ segment = endpointContextSegment := by
        rw [endpointSegments] at member
        simpa using member
      rcases member' with rfl | rfl
      · exact textBytes address byte read
      · exact contextAfter address byte read

private theorem endpointBaseNormal : NormalExecutionState endpointBaseMachine := by
  simp [NormalExecutionState, endpointBaseMachine, endpointConfiguredMachine, initialState,
    Std.ExtDHashMap.get?_insert, Sail.BitVec.access]

private theorem endpointBaseRegions : endpointBaseMachine.regs.get? pma_regions =
    some [endpointPmaRegion] := by
  simp [endpointBaseMachine, endpointConfiguredMachine, Std.ExtDHashMap.get?_insert]

private theorem endpointBaseRegs : endpointBaseMachine.regs = endpointConfiguredMachine.regs := by
  rfl

private theorem endpointPmaMatches {address : BitVec 64} {width : Nat}
    (fits : address.toNat + width ≤ 0x40000000) :
    matching_pma_region [endpointPmaRegion] (physaddr.Physaddr address) width =
      some endpointPmaRegion := by
    have widthEq : (to_bits width : BitVec 64) = BitVec.ofNat 64 width := by
      apply BitVec.eq_of_toNat_eq
      simp [to_bits, Sail.get_slice_int]
    unfold matching_pma_region
    rw [widthEq]
    unfold matching_pma_region_bits_range range_subset zopz0zIzJ_u bits_of_physaddr
      Sail.BitVec.toNatInt zero_extend Sail.BitVec.zeroExtend
    simp [endpointPmaRegion]
    omega

private theorem endpointPmaAllows {access : DataPmaAccess} {state : State}
    {address : BitVec 64} {width : Nat}
    (regions : state.regs.get? pma_regions = some [endpointPmaRegion])
    (fits : address.toNat + width ≤ 0x40000000) :
    DataPmaAllows access state address width :=
  ⟨[endpointPmaRegion], endpointPmaRegion, regions, endpointPmaMatches fits, by cases access <;> rfl⟩

private theorem endpointPmaAllowsAtNat {access : DataPmaAccess} {state : State}
    (regions : state.regs.get? pma_regions = some [endpointPmaRegion])
    (address width : Nat) (addressFits : address < 2 ^ 64)
    (fits : address + width ≤ 0x40000000) :
    DataPmaAllows access state (BitVec.ofNat 64 address) width := by
  apply endpointPmaAllows regions
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressFits]
  exact fits

private theorem endpointMachinePc_fits {pc : BitVec 64} (owned : EndpointMachinePc pc) :
    pc.toNat + 4 ≤ 0x2000000 := by
  obtain ⟨_, byte, read⟩ := owned
  obtain ⟨segment, member, _, upper⟩ :=
    Artifacts.programImage.readFileByte?_mem_segment read
  have bounds : ∀ segment ∈ Artifacts.programImage.segments.toList,
      segment.initialEndAddress ≤ 0x2000000 ∧ segment.initialEndAddress % 4 = 0 := by
    native_decide
  have bound := bounds segment member
  omega

private theorem endpointBaseConfigured :
    ConfiguredMachinePre EndpointMachinePc endpointBaseMachine where
  normal := endpointBaseNormal
  retiredCounter := by
    simp [RetiredCounterPresent, endpointBaseRegs, endpointConfiguredMachine,
      Std.ExtDHashMap.get?_insert]
  mstatusStoreMode := by
    simp [endpointBaseRegs, endpointConfiguredMachine, Std.ExtDHashMap.get?_insert]
    rfl
  seccfgPresent := by
    simp [endpointBaseRegs, endpointConfiguredMachine, Std.ExtDHashMap.get?_insert]
    rfl
  htifDisabled := by
    change endpointBaseMachine.regs.get? htif_tohost_base = some none
    rw [endpointBaseRegs]
    simp [endpointConfiguredMachine, Std.ExtDHashMap.get?_insert]
    exact rfl
  platform := by
    have mstatus : ∃ bits, endpointBaseMachine.regs.get? mstatus = some bits := by
      simp [endpointBaseRegs, endpointConfiguredMachine, Std.ExtDHashMap.get?_insert]
    obtain ⟨mstatusBits, mstatusRead⟩ := mstatus
    have meip : ∃ bits, endpointBaseMachine.regs.get? sig_meip = some bits := by
      simp [endpointBaseRegs, endpointConfiguredMachine, Std.ExtDHashMap.get?_insert]
    obtain ⟨meipBits, meipRead⟩ := meip
    have htif : endpointBaseMachine.regs.get? htif_tohost_base = some none := by
      change endpointBaseMachine.regs.get? htif_tohost_base = some none
      rw [endpointBaseRegs]
      simp [endpointConfiguredMachine, Std.ExtDHashMap.get?_insert]
      exact rfl
    intro state pc agree atPc owned
    have normal : NormalExecutionState state := normalExecutionState_of_agree
      (agree.weaken (fun register member => by
        constructor
        · exact normalRegisters_platformPreserved register member
        · rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp)) endpointBaseNormal
    have mstatusState := (agree mstatus (by simp [instructionPreserved, platformPreserved])).trans
      mstatusRead
    have regionsState := (agree pma_regions
      (by simp [instructionPreserved, platformPreserved])).trans endpointBaseRegions
    have meipState := (agree sig_meip
      (by simp [instructionPreserved, platformPreserved])).trans meipRead
    have htifState := (agree htif_tohost_base
      (by simp [instructionPreserved, platformPreserved])).trans htif
    refine ⟨fetchBasePlatform_of_offPC atPc
      (fetchBasePlatformOffPC_of_normal normal mstatusState owned.1
        (fetchPmaAllows_of_region regionsState (by
          have fits : pc.toNat + 4 ≤ 0x40000000 :=
            Nat.le_trans (endpointMachinePc_fits owned) (by native_decide)
          exact endpointPmaMatches fits) rfl)), ?_,
      interruptDisabled_of_normal normal mstatusState ⟨meipBits, meipState⟩,
      landingPadNotExpected_of_normal normal⟩
    exact fetchMemoryNoMMIO_of_state_layout_excluded state pc
      ⟨fetch_mmio_address_excluded_of_before_layout pc (by
          have pcFits := endpointMachinePc_fits owned
          have layout : 0x2000000 ≤ BitVec.toNat plat_clint_base := by native_decide
          omega) (by
          have pcFits := endpointMachinePc_fits owned
          have layout : 0x2000000 ≤ BitVec.toNat plat_sig_base := by native_decide
          omega), htifState⟩
  landingPad := by
    have privilege : endpointBaseMachine.regs.get? cur_privilege = some Privilege.Machine :=
      endpointBaseNormal.2.1
    have seccfg : ∃ bits, endpointBaseMachine.regs.get? mseccfg = some bits := by
      simp [endpointBaseRegs, endpointConfiguredMachine, Std.ExtDHashMap.get?_insert]
    obtain ⟨bits, read⟩ := seccfg
    intro state r _ agree
    exact updateElpState_run state r bits
      ((agree cur_privilege (by simp [instructionPreserved, platformPreserved])).trans privilege)
      ((agree mseccfg (by simp [instructionPreserved, platformPreserved])).trans read)

private theorem endpointBaseCode :
    Artifacts.programImage.fileBytesLoadedFaithfully endpointBaseMachine.mem := by
  obtain ⟨finish, run, _, code⟩ := endpointBaseLoaded
  have memEq : endpointProgramMemory = finish.mem := endpointProgramMemory_eq_of_runs run
  rw [endpointBaseMachine, memEq]
  exact code

private theorem endpointFileAddress_before_stack {address : Nat} {byte : UInt8}
    (read : Artifacts.programImage.readFileByte? address = some byte) :
    address < canonicalStackPointer - 0xbb0 := by
  obtain ⟨segment, member, _, upper⟩ :=
    Artifacts.programImage.readFileByte?_mem_segment read
  have bounds : ∀ segment ∈ Artifacts.programImage.segments.toList,
      segment.initialEndAddress ≤ canonicalStackPointer - 0xbb0 := by
    native_decide
  exact Nat.lt_of_lt_of_le upper (bounds segment member)

private theorem endpointDataNoMMIO (address : BitVec 64) (width : Nat)
    (lower : 0x20000000 ≤ address.toNat)
    (_fits : address.toNat + width ≤ 0x40000000) : DataMMIOAddressExcluded address width := by
  unfold DataMMIOAddressExcluded Sail.BitVec.toNatInt
  rw [show plat_clint_base = (33554432 : BitVec 64) by native_decide,
    show plat_clint_size = (786432 : BitVec 64) by native_decide,
    show plat_sig_base = (201326592 : BitVec 64) by native_decide,
    show plat_sig_size = (32 : BitVec 64) by native_decide]
  simp
  constructor <;> intro _ <;> omega

private theorem endpointDataNoMMIOAtNat (address width : Nat)
    (addressFits : address < 2 ^ 64) (lower : 0x20000000 ≤ address)
    (fits : address + width ≤ 0x40000000) :
    DataMMIOAddressExcluded (BitVec.ofNat 64 address) width := by
  apply endpointDataNoMMIO
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressFits]
    exact lower
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressFits]
    exact fits

def canonicalMainArgs (input : Array UInt8) : MainArgs :=
  { input, stackPointer := canonicalStackPointer, returnAddress := 0 }

/-- The computable runner starts the linked endpoint in the exact state required by Level 0. -/
theorem initialEndpointState_mainEntry (input : Array UInt8)
    (inputBound : input.size ≤ 64 * 1024 * 1024) :
    MainEntry (canonicalMainArgs input) (initialEndpointState input) := by
  obtain ⟨inputState, inputRun, inputRegs, inputFrame, inputWindow⟩ :=
    writeMemoryBytes_establishes Elflings.inputBufferAddress input.toList endpointBaseMachine
  let contextState := afterWriteBytes (width := 8) inputState Elflings.ioContextAddress
    (BitVec.ofNat 64 input.size)
  let pcState : State := { contextState with
    regs := contextState.regs.insert PC (BitVec.ofNat 64 Elflings.mainEntry) }
  let returnState : State := { pcState with regs := pcState.regs.insert x1 (0 : BitVec 64) }
  let finalMachine : State := { returnState with
    regs := returnState.regs.insert x2 (BitVec.ofNat 64 (canonicalStackPointer + 0x380)) }
  have contextRun : Runs
      (PreSail.writeBytes (n := 8) Elflings.ioContextAddress (BitVec.ofNat 64 input.size))
      inputState contextState true := by
    exact writeBytes_run_exact inputState Elflings.ioContextAddress (BitVec.ofNat 64 input.size)
  have pcRun : Runs (writeReg PC (BitVec.ofNat 64 Elflings.mainEntry))
      contextState pcState () := by
    exact writeReg_run contextState PC (BitVec.ofNat 64 Elflings.mainEntry)
  have returnRun : Runs (writeReg x1 (0 : BitVec 64)) pcState returnState () := by
    exact writeReg_run pcState x1 (0 : BitVec 64)
  have stackRun : Runs (writeReg x2 (BitVec.ofNat 64 (canonicalStackPointer + 0x380)))
      returnState finalMachine () := by
    exact writeReg_run returnState x2 (BitVec.ofNat 64 (canonicalStackPointer + 0x380))
  have initializeRun : Runs (initializeEndpointInput input) endpointBaseMachine finalMachine () := by
    unfold initializeEndpointInput
    exact Runs.bind inputRun (Runs.bind contextRun (Runs.bind pcRun (Runs.bind returnRun stackRun)))
  have machineEq : (initialEndpointState input).machine = finalMachine := by
    unfold initialEndpointState
    rw [initializeRun]
  have inputRepAtInput : BytesRep inputState.mem Elflings.inputBufferAddress input := by
    refine ⟨?_, ?_⟩
    · have layout : Elflings.inputBufferAddress + maxSszInputSize ≤ 2 ^ 64 := by native_decide
      simp [maxSszInputSize] at inputBound layout
      omega
    · intro index bound
      simpa using inputWindow index (by simpa using bound)
  have inputRep : BytesRep finalMachine.mem Elflings.inputBufferAddress input := by
    refine ⟨inputRepAtInput.1, ?_⟩
    intro index bound
    change (afterWriteBytes inputState Elflings.ioContextAddress
      (BitVec.ofNat 64 input.size)).mem.get? (Elflings.inputBufferAddress + index) = _
    rw [afterWriteBytes_mem_get?_of_outside]
    · exact inputRepAtInput.2 index bound
    · intro contextIndex equal
      have layout : Elflings.inputBufferAddress + maxSszInputSize ≤
          Elflings.ioContextAddress := by native_decide
      simp [maxSszInputSize] at inputBound layout
      omega
  have sizeRep : UIntRep 8 finalMachine.mem Elflings.ioContextAddress input.size := by
    simpa [finalMachine, returnState, pcState, contextState] using
      uintRep_afterWriteBytes_eight inputState Elflings.ioContextAddress input.size
        (by omega) (by native_decide)
  have codeInput : Artifacts.programImage.fileBytesLoadedFaithfully inputState.mem := by
    intro address byte read
    rw [inputFrame address (Or.inl (by
      have beforeStack := endpointFileAddress_before_stack read
      have layout : canonicalStackPointer - 0xbb0 < Elflings.inputBufferAddress := by native_decide
      omega))]
    exact endpointBaseCode address byte read
  have code : Artifacts.programImage.fileBytesLoadedFaithfully finalMachine.mem := by
    simpa [finalMachine, returnState, pcState, contextState] using
      fileBytesLoadedFaithfully_afterWriteBytes Artifacts.programImage inputState
        Elflings.ioContextAddress (BitVec.ofNat 64 input.size) (by
          intro index
          apply Option.eq_none_iff_forall_not_mem.mpr
          intro byte read
          have before := endpointFileAddress_before_stack read
          have layout : canonicalStackPointer - 0xbb0 < Elflings.ioContextAddress := by native_decide
          omega) codeInput
  have agree : Agree instructionPreserved endpointBaseMachine finalMachine := by
    intro register preserved
    obtain ⟨platform, notLink⟩ := preserved
    rcases platform with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · contradiction
    all_goals simp [finalMachine, returnState, pcState, contextState, afterWriteBytes_regs,
      inputRegs, Std.ExtDHashMap.get?_insert]
  have retiredFinal : RetiredCounterPresent finalMachine := by
    obtain ⟨retired, read⟩ := endpointBaseConfigured.retiredCounter
    exact ⟨retired, by
      simpa [finalMachine, returnState, pcState, contextState, afterWriteBytes_regs, inputRegs,
        Std.ExtDHashMap.get?_insert] using read⟩
  have configured : ConfiguredMachinePre EndpointMachinePc finalMachine :=
    endpointBaseConfigured.mono agree retiredFinal
  have regions : finalMachine.regs.get? pma_regions = some [endpointPmaRegion] :=
    (agree pma_regions (by simp [instructionPreserved, platformPreserved])).trans endpointBaseRegions
  have dataAccess : MainDataAccess (canonicalMainArgs input) finalMachine := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro offset width bound
      apply endpointPmaAllowsAtNat regions <;>
        simp [canonicalMainArgs, canonicalStackPointer,
          show Elflings.inputBufferAddress = 536977408 by native_decide] <;> omega
    · intro offset width bound
      apply endpointPmaAllowsAtNat regions <;>
        simp [canonicalMainArgs, canonicalStackPointer,
          show Elflings.inputBufferAddress = 536977408 by native_decide] <;> omega
    · exact endpointPmaAllowsAtNat regions _ _ (by native_decide) (by native_decide)
    · exact endpointPmaAllowsAtNat regions _ _ (by native_decide) (by native_decide)
    · exact endpointPmaAllowsAtNat regions _ _ (by native_decide) (by native_decide)
    · exact endpointPmaAllowsAtNat regions _ _ (by native_decide) (by native_decide)
    · intro offset width bound
      apply endpointPmaAllowsAtNat regions <;>
        simp [canonicalMainArgs, canonicalStackPointer,
          show Elflings.inputBufferAddress = 536977408 by native_decide] <;> omega
    · intro offset width bound
      apply endpointPmaAllowsAtNat regions <;>
        simp [canonicalMainArgs, canonicalStackPointer,
          show Elflings.inputBufferAddress = 536977408 by native_decide] <;> omega
  have endpointEq : initialEndpointState input =
      EndpointState.mk finalMachine input 0 #[] none := by
    apply EndpointState.ext
    · exact machineEq
    all_goals rfl
  rw [endpointEq]
  refine {
    stdin := rfl
    stdinCursor := rfl
    stdout := rfl
    exitCode := rfl
    inputBound := inputBound
    stackLower := by
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide]
    stackFits := by
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide]
    stackAligned := by
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide]
    returnAddressFits := by simp [canonicalMainArgs]
    atPc := by simp [finalMachine, returnState, pcState, Std.ExtDHashMap.get?_insert]
    stackRegister := by simp [canonicalMainArgs, finalMachine, Std.ExtDHashMap.get?_insert]
    returnRegister := by
      simp [canonicalMainArgs, finalMachine, returnState, Std.ExtDHashMap.get?_insert]
    configured := configured
    code := code
    dataAccess := dataAccess
    calleeSaved := by
      refine ⟨DecodeCalleeSavedValues.mk 0 0 0 0 0 0 0 0 0 0 0 0, ?_⟩
      simp [DecodeCalleeSavedAtRegisters, finalMachine, returnState, pcState, contextState,
        afterWriteBytes_regs, inputRegs, endpointBaseRegs, endpointConfiguredMachine,
        Std.ExtDHashMap.get?_insert]
    savedReturnNoMMIO := endpointDataNoMMIOAtNat _ _ (by
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide]) (by
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide]) (by
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide])
    inputSizeNoMMIO := endpointDataNoMMIOAtNat _ _ (by
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide]) (by
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide]) (by
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide])
    stackNoMMIO := by
      intro offset width bound
      apply endpointDataNoMMIOAtNat
      · simp [canonicalMainArgs, canonicalStackPointer,
          show Elflings.inputBufferAddress = 536977408 by native_decide]
        omega
      · simp [canonicalMainArgs, canonicalStackPointer,
          show Elflings.inputBufferAddress = 536977408 by native_decide]
        omega
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide]
      omega
    decodeFrameNoMMIO := by
      intro offset width bound
      apply endpointDataNoMMIOAtNat
      · simp [canonicalMainArgs, canonicalStackPointer,
          show Elflings.inputBufferAddress = 536977408 by native_decide]
        omega
      · simp [canonicalMainArgs, canonicalStackPointer,
          show Elflings.inputBufferAddress = 536977408 by native_decide]
        omega
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide]
      omega
    inputBytes := inputRep
    inputSizeContext := sizeRep
    stackBelowInputBuffer := by
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide]
    inputOutsideStack := by
      intro index bound
      right
      simp [canonicalMainArgs, canonicalStackPointer,
        show Elflings.inputBufferAddress = 536977408 by native_decide]
      omega
    stackNotFileBacked := by
      intro address lower upper
      apply Option.eq_none_iff_forall_not_mem.mpr
      intro byte read
      exact (Nat.not_lt_of_ge lower) (endpointFileAddress_before_stack read) }

end BinaryFv.Zesu
