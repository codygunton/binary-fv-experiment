import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.EntryBinding
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.RiscV.Elfling.ProgramGeometry

/-!
# Canonical decoder-entry machine audit

This module records the checked target facts needed before `buildZesuEntryState` can be adapted to
`compiledZesuDecodeRawContract`: the PMA table, fixed CLINT/signature windows, and the distinction
between file-backed image bytes and zero-filled virtual memory. HTIF has no configured window
because the builder pins `htif_tohost_base` to `none`.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

/-- The wrapper's frame base after its two entry decrements. -/
def canonicalZesuDecodeRawStackBase : Nat := canonicalRunnerLayout.stackStop - 0xa20

/-- A positive access entirely below the configured PMA ceiling selects the runner's sole region. -/
theorem matching_zesuMainMemoryRegion {address : BitVec 64} {width : Nat}
    (positive : 0 < width) (below : address.toNat + width ≤ 2 ^ 63) :
    matching_pma_region [zesuMainMemoryRegion] (physaddr.Physaddr address) width =
      some zesuMainMemoryRegion := by
  simp only [matching_pma_region, matching_pma_region_bits_range]
  unfold range_subset zesuMainMemoryRegion zesuPmaRange
  simp [zero_extend, bits_of_physaddr, to_bits, zopz0zIzJ_u, Sail.BitVec.toNatInt,
    Sail.BitVec.zeroExtend, Sail.get_slice_int]
  omega

/-- The canonical ELF's virtual image contains a zero-filled byte at the CLINT base. This is not
ordinary memory: `within_mmio_readable` selects CLINT there. The permission therefore uses
`readFileByte?`, whose absence at every MMIO window is proved below. -/
theorem canonicalImage_reads_clint :
    ∃ byte, Artifacts.programImage.readByte? (BitVec.toNat plat_clint_base) = some byte := by
  refine ⟨0, ?_⟩
  native_decide

/-- No file-backed canonical image byte occurs at or above its last file byte. -/
theorem canonicalFileImage_none_of_86028_le {address : Nat} (above : 86028 ≤ address) :
    Artifacts.programImage.readFileByte? address = none := by
  cases file : Artifacts.programImage.readFileByte? address with
  | none => rfl
  | some byte =>
      have below := file_addr_lt file
      omega

/-- Every address in the fixed CLINT window is absent from the immutable file image. -/
theorem canonicalFileImage_none_in_clint {address : Nat}
    (inWindow : BitVec.toNat plat_clint_base ≤ address ∧
      address < BitVec.toNat plat_clint_base + BitVec.toNat plat_clint_size) :
    Artifacts.programImage.readFileByte? address = none := by
  rw [clintBase_pinned] at inWindow
  exact canonicalFileImage_none_of_86028_le (by omega)

/-- Every address in the fixed signature window is absent from the immutable file image. -/
theorem canonicalFileImage_none_in_signature {address : Nat}
    (inWindow : BitVec.toNat plat_sig_base ≤ address ∧
      address < BitVec.toNat plat_sig_base + BitVec.toNat plat_sig_size) :
    Artifacts.programImage.readFileByte? address = none := by
  rw [signatureBase_pinned] at inWindow
  exact canonicalFileImage_none_of_86028_le (by omega)

/-- Every readable decoder byte at the canonical runner input placement lies outside the two fixed
MMIO windows and below the configured PMA ceiling. -/
theorem decoderReadableByte_layout (args : DecoderMachineArgs) (address : Nat)
    (inputBase : args.inputBase = canonicalRunnerLayout.inputBase)
    (inputBound : args.bytes.size < 2 * 1024 * 1024)
    (readable : DecoderReadableByte args address) :
    (address < BitVec.toNat plat_clint_base ∨
      BitVec.toNat plat_clint_base + BitVec.toNat plat_clint_size ≤ address) ∧
    (address < BitVec.toNat plat_sig_base ∨
      BitVec.toNat plat_sig_base + BitVec.toNat plat_sig_size ≤ address) ∧
    address < 2 ^ 63 := by
  rw [clintBase_pinned, clintSize_pinned, signatureBase_pinned, signatureSize_pinned]
  rcases readable with image | input | stack | globals | allocator | arena
  · have image' : ∃ byte, Artifacts.programImage.readFileByte? address = some byte := by
      simpa [canonicalContractParams, canonicalEnvironment] using image
    obtain ⟨byte, image'⟩ := image'
    have belowImage := file_addr_lt image'
    exact ⟨Or.inl (by omega), Or.inl (by omega), by omega⟩
  · rw [inputBase] at input
    have afterClint : 33554432 + 786432 ≤ canonicalRunnerLayout.inputBase := by native_decide
    have afterSignature : 201326592 + 32 ≤ canonicalRunnerLayout.inputBase := by native_decide
    refine ⟨Or.inr (by omega), Or.inr (by omega), ?_⟩
    have ceiling : canonicalRunnerLayout.inputBase + 2 * 1024 * 1024 < 2 ^ 63 := by
      native_decide
    omega
  · simp only [canonicalContractParams, canonicalEnvironment, canonicalStack, range] at stack
    have afterClint : 33554432 + 786432 ≤ canonicalRunnerLayout.stackBase := by native_decide
    have afterSignature : 201326592 + 32 ≤ canonicalRunnerLayout.stackBase := by native_decide
    refine ⟨Or.inr (by omega), Or.inr (by omega), ?_⟩
    have ceiling : canonicalRunnerLayout.stackBase + canonicalRunnerLayout.stackSize < 2 ^ 63 := by
      native_decide
    omega
  · unfold DecoderGlobalsByte at globals
    have afterClint : 33554432 + 786432 ≤ Elflings.GeneratedDecoderGlobals.bssBase := by
      native_decide
    have beforeSignature : Elflings.GeneratedDecoderGlobals.bssBase +
        Elflings.GeneratedDecoderGlobals.bssSize ≤ 201326592 := by native_decide
    refine ⟨Or.inr (by omega), Or.inl (by omega), ?_⟩
    have ceiling : Elflings.GeneratedDecoderGlobals.bssBase +
        Elflings.GeneratedDecoderGlobals.bssSize < 2 ^ 63 := by native_decide
    omega
  · simp only [canonicalContractParams, canonicalEnvironment, Elflings.canonicalAllocatorState] at allocator
    rcases allocator with cursor | limit
    · have beforeClint : Elflings.canonicalHeapPosAddr + 8 ≤ 33554432 := by native_decide
      have beforeSignature : Elflings.canonicalHeapPosAddr + 8 ≤ 201326592 := by native_decide
      have belowPma : Elflings.canonicalHeapPosAddr + 8 < 2 ^ 63 := by native_decide
      refine ⟨Or.inl (by omega), Or.inl (by omega), by omega⟩
    · have beforeClint : Elflings.canonicalHeapTopAddr + 8 ≤ 33554432 := by native_decide
      have beforeSignature : Elflings.canonicalHeapTopAddr + 8 ≤ 201326592 := by native_decide
      have belowPma : Elflings.canonicalHeapTopAddr + 8 < 2 ^ 63 := by native_decide
      refine ⟨Or.inl (by omega), Or.inl (by omega), by omega⟩
  · change canonicalContractParams.env.arenaBase ≤ address ∧
      address < Elflings.canonicalHeapLimit ∧ address < BitVec.toNat plat_clint_base at arena
    rw [clintBase_pinned] at arena
    refine ⟨Or.inl arena.2.2, Or.inl (by omega), ?_⟩
    rw [canonicalHeapLimit_pinned] at arena
    omega

/-- Writable decoder bytes are a subset of readable decoder bytes at the same input placement. -/
theorem decoderWritableByte_layout (args : DecoderMachineArgs) (address : Nat)
    (inputBase : args.inputBase = canonicalRunnerLayout.inputBase)
    (inputBound : args.bytes.size < 2 * 1024 * 1024)
    (writable : DecoderWritableByte address) :
    (address < BitVec.toNat plat_clint_base ∨
      BitVec.toNat plat_clint_base + BitVec.toNat plat_clint_size ≤ address) ∧
    (address < BitVec.toNat plat_sig_base ∨
      BitVec.toNat plat_sig_base + BitVec.toNat plat_sig_size ≤ address) ∧
    address < 2 ^ 63 := by
  apply decoderReadableByte_layout args address inputBase inputBound
  rcases writable with stack | globals | allocator | arena
  · exact Or.inr (Or.inr (Or.inl stack))
  · exact Or.inr (Or.inr (Or.inr (Or.inl globals)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl allocator))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr arena))))

/-- A byte-placement exclusion at the first byte is sufficient for Sail's whole-range MMIO test:
both CLINT and signature selectors first require the access address itself to lie in their window. -/
theorem loadMMIOAddressExcluded_of_layout {address : BitVec 64} {width : Nat}
    (positive : 0 < width)
    (clint : address.toNat < BitVec.toNat plat_clint_base ∨
      BitVec.toNat plat_clint_base + BitVec.toNat plat_clint_size ≤ address.toNat)
    (signature : address.toNat < BitVec.toNat plat_sig_base ∨
      BitVec.toNat plat_sig_base + BitVec.toNat plat_sig_size ≤ address.toNat) :
    LoadMMIOAddressExcluded address width := by
  rw [clintBase_pinned, clintSize_pinned] at clint
  rw [signatureBase_pinned, signatureSize_pinned] at signature
  unfold LoadMMIOAddressExcluded DataMMIOAddressExcluded
  simp [Sail.BitVec.toNatInt, clintBase_pinned, clintSize_pinned,
    signatureBase_pinned, signatureSize_pinned]
  constructor
  · intro inClint
    rcases clint with before | after <;> omega
  · intro inSignature
    rcases signature with before | after <;> omega

theorem storeMMIOAddressExcluded_of_layout {address : BitVec 64} {width : Nat}
    (positive : 0 < width)
    (clint : address.toNat < BitVec.toNat plat_clint_base ∨
      BitVec.toNat plat_clint_base + BitVec.toNat plat_clint_size ≤ address.toNat)
    (signature : address.toNat < BitVec.toNat plat_sig_base ∨
      BitVec.toNat plat_sig_base + BitVec.toNat plat_sig_size ≤ address.toNat) :
    StoreMMIOAddressExcluded address width := by
  rw [clintBase_pinned, clintSize_pinned] at clint
  rw [signatureBase_pinned, signatureSize_pinned] at signature
  unfold StoreMMIOAddressExcluded DataMMIOAddressExcluded
  simp [Sail.BitVec.toNatInt, clintBase_pinned, clintSize_pinned,
    signatureBase_pinned, signatureSize_pinned]
  constructor
  · intro inClint
    rcases clint with before | after <;> omega
  · intro inSignature
    rcases signature with before | after <;> omega

theorem readableAccessRange_below_pma (args : DecoderMachineArgs) (address : BitVec 64)
    (width : Nat) (inputBase : args.inputBase = canonicalRunnerLayout.inputBase)
    (inputBound : args.bytes.size < 2 * 1024 * 1024)
    (allowed : DecoderAccessRange (DecoderReadableByte args) address width) :
    address.toNat + width ≤ 2 ^ 63 := by
  have positive := allowed.1
  have lastBound : width - 1 < width := by omega
  have last := decoderReadableByte_layout args (address.toNat + (width - 1)) inputBase inputBound
    (allowed.2.2 _ lastBound)
  omega

theorem writableAccessRange_below_pma (args : DecoderMachineArgs) (address : BitVec 64)
    (width : Nat) (inputBase : args.inputBase = canonicalRunnerLayout.inputBase)
    (inputBound : args.bytes.size < 2 * 1024 * 1024)
    (allowed : DecoderAccessRange DecoderWritableByte address width) :
    address.toNat + width ≤ 2 ^ 63 := by
  have positive := allowed.1
  have lastBound : width - 1 < width := by omega
  have last := decoderWritableByte_layout args (address.toNat + (width - 1)) inputBase inputBound
    (allowed.2.2 _ lastBound)
  omega

/-- The canonical PMA table and placement permissions discharge every aligned data access admitted
by the decoder contract. The alignment premise is explicit because Sail checks it before PMA. -/
theorem canonicalDecoderDataAccess (args : DecoderMachineArgs) (state : State)
    (inputBase : args.inputBase = canonicalRunnerLayout.inputBase)
    (inputBound : args.bytes.size < 2 * 1024 * 1024)
    (normal : NormalExecutionState state)
    (pma : state.regs.get? pma_regions = some [zesuMainMemoryRegion])
    (htif : state.regs.get? htif_tohost_base = some none) : DecoderDataAccess args state where
  load next address width agree allowed aligned := by
    have pmaNext : next.regs.get? pma_regions = some [zesuMainMemoryRegion] :=
      (agree pma_regions (by simp [decoderPreserved, platformPreserved])).trans pma
    have belowPma := readableAccessRange_below_pma args address width inputBase inputBound allowed
    have pmaAllowed : LoadPmaAllows next address width :=
      ⟨[zesuMainMemoryRegion], zesuMainMemoryRegion, pmaNext,
        matching_zesuMainMemoryRegion allowed.1 belowPma, by native_decide⟩
    have pmpDisabled : FetchPmpDisabled next :=
      ⟨(agree pmpcfg_n (by simp [decoderPreserved, platformPreserved])).trans
          (fetchPmpDisabled_of_normal normal).1,
        (agree pmpaddr_n (by simp [decoderPreserved, platformPreserved])).trans
          (fetchPmpDisabled_of_normal normal).2⟩
    have physical : Runs (phys_access_check (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA .Machine (physaddr.Physaddr address) width false) next next none :=
      phys_access_check_machine_load_allowed next address width pmpDisabled pmaAllowed aligned
    have first := decoderReadableByte_layout args address.toNat inputBase inputBound (allowed.2.2 0 allowed.1)
    have htifNext : next.regs.get? htif_tohost_base = some none :=
      (agree htif_tohost_base (by simp [decoderPreserved, platformPreserved])).trans htif
    exact ⟨physical, loadMemoryNoMMIO_of_state_layout_excluded next address width
      (loadMMIOAddressExcluded_of_layout allowed.1 first.1 first.2.1) htifNext⟩
  store next address width agree allowed aligned := by
    have pmaNext : next.regs.get? pma_regions = some [zesuMainMemoryRegion] :=
      (agree pma_regions (by simp [decoderPreserved, platformPreserved])).trans pma
    have belowPma := writableAccessRange_below_pma args address width inputBase inputBound allowed
    have pmaAllowed : StorePmaAllows next address width :=
      ⟨[zesuMainMemoryRegion], zesuMainMemoryRegion, pmaNext,
        matching_zesuMainMemoryRegion allowed.1 belowPma, by native_decide⟩
    have pmpDisabled : FetchPmpDisabled next :=
      ⟨(agree pmpcfg_n (by simp [decoderPreserved, platformPreserved])).trans
          (fetchPmpDisabled_of_normal normal).1,
        (agree pmpaddr_n (by simp [decoderPreserved, platformPreserved])).trans
          (fetchPmpDisabled_of_normal normal).2⟩
    have physical : Runs (phys_access_check (MemoryAccessType.Store mem_payload.Data)
        page_based_mem_type.PBMT_PMA .Machine (physaddr.Physaddr address) width false) next next none :=
      phys_access_check_machine_store_allowed next address width pmpDisabled pmaAllowed aligned
    have first := decoderWritableByte_layout args address.toNat inputBase inputBound (allowed.2.2 0 allowed.1)
    have htifNext : next.regs.get? htif_tohost_base = some none :=
      (agree htif_tohost_base (by simp [decoderPreserved, platformPreserved])).trans htif
    exact ⟨physical, storeMemoryNoMMIO_of_state_layout_excluded next address width
      (storeMMIOAddressExcluded_of_layout allowed.1 first.1 first.2.1) htifNext⟩

/-! ## Builder-to-compiled-entry adapter -/

/-- The linked entry symbol used by the wrapper proof is fixed by the parsed canonical ELF. -/
theorem canonicalZesuDecodeRawEntry_pinned :
    Artifacts.zesuDecodeRaw.toOption.map (fun symbol => symbol.value) = some 0x102b0 := by
  native_decide

/-- Every pc in the root wrapper's generated execution extent is before the first MMIO window.
The check ranges over the actual generated extent, including absorbed inline bodies. -/
def rawDecoderExecutionBeforeClintB : Bool :=
  (functionInstanceExecutionRanges generatedProgram
    functionInstance_raw_decoder_root_zesu_decode_raw).all fun range =>
      decide (range.stop ≤ BitVec.toNat plat_clint_base ∧ range.stop % 4 = 0)

theorem rawDecoderExecutionBeforeClint : rawDecoderExecutionBeforeClintB = true := by
  native_decide

theorem rawDecoderExecution_before_clint {pc : BitVec 64}
    (inExecution : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw pc)
    (aligned : pc.toNat % 4 = 0) :
    pc.toNat + 4 ≤ BitVec.toNat plat_clint_base := by
  obtain ⟨range, member, lower, upper⟩ := functionInstanceExecutionPcs_iff_ranges.mp inExecution
  obtain ⟨index, indexBound, atIndex⟩ := Array.mem_iff_getElem.mp member
  have allChecked := rawDecoderExecutionBeforeClint
  unfold rawDecoderExecutionBeforeClintB at allChecked
  have checked := Array.all_eq_true.mp allChecked index indexBound
  rw [atIndex] at checked
  have rangeFacts : range.stop ≤ BitVec.toNat plat_clint_base ∧ range.stop % 4 = 0 :=
    of_decide_eq_true checked
  omega

/-- The runner-built state meets the compiled wrapper entry predicate for every public-size input. -/
theorem buildZesuEntryState_compiled_entry (input : ByteArray)
    (inputBound : input.size < 2 * 1024 * 1024) :
    ∃ state, Runs (buildZesuEntryState input) initialState state () ∧
      compiledZesuDecodeRawContract.binding.entry
        ⟨canonicalRunnerLayout.inputBase, input⟩ state := by
  obtain ⟨state, built, source, link, stack, normal, fetchPresent, fetchPinned, loadPinned,
    entrySymbol, entrySymbolFound, entryPc, nextPc, pma, savedS0, savedS1, savedS2⟩ :=
    buildZesuEntryState_entry_binding_abi input
  refine ⟨state, built, source, ?_⟩
  refine ⟨canonicalZesuDecodeRawStackBase, ?_⟩
  refine {
    atEntry := ?_
    linkAtEntry := ⟨_, link⟩
    savedS0AtEntry := savedS0
    savedS1AtEntry := savedS1
    savedS2AtEntry := savedS2
    stackAtEntry := ?_
    inputFits := ?_
    inputBound := inputBound
    inputAvoidsStack := ?_
    inputAvoidsAttempted := ?_
    inputAvoidsDecoderGlobals := ?_
    inputAvoidsCanonicalArena := ?_
    inputAvoidsAllocatorState := ?_
    inputAvoidsCanonicalStack := ?_
    stackAligned := ?_
    stackFrameFits := ?_
    stackAvoidsStatusGlobals := ?_
    stackFrameWritable := ?_
    stackObjectsFit := ?_
    stackObjectsReadable := ?_
    machine := ?_ }
  · have entryValue : entrySymbol.value = 0x102b0 := by
      have entryPinned := canonicalZesuDecodeRawEntry_pinned
      rw [entrySymbolFound] at entryPinned
      exact Option.some.inj entryPinned
    simpa [entryValue] using entryPc
  · simpa [canonicalZesuDecodeRawStackBase] using stack
  · have runnerFits : canonicalRunnerLayout.inputBase + 2 * 1024 * 1024 ≤ 2 ^ 64 := by
      native_decide
    change canonicalRunnerLayout.inputBase + input.size ≤ 2 ^ 64
    omega
  · change canonicalRunnerLayout.inputBase + input.size ≤ canonicalZesuDecodeRawStackBase ∨
      canonicalZesuDecodeRawStackBase + 0xa20 ≤ canonicalRunnerLayout.inputBase
    left
    have stackBase : canonicalRunnerLayout.inputBase + 2 * 1024 * 1024 ≤
        canonicalZesuDecodeRawStackBase := by native_decide
    omega
  · change canonicalRunnerLayout.inputBase + input.size ≤ 0x4215020 ∨
      0x4215020 < canonicalRunnerLayout.inputBase
    right
    have afterAttempted : 0x4215020 < canonicalRunnerLayout.inputBase := by
      native_decide
    omega
  · right
    have afterDecoderGlobals : Elflings.GeneratedDecoderGlobals.bssBase +
        Elflings.GeneratedDecoderGlobals.bssSize ≤ canonicalRunnerLayout.inputBase := by
      native_decide
    exact afterDecoderGlobals
  · right
    have afterArena : Elflings.canonicalHeapLimit ≤ canonicalRunnerLayout.inputBase := by
      native_decide
    exact afterArena
  · intro address allocator
    change Elflings.canonicalAllocatorState address at allocator
    change canonicalRunnerLayout.inputBase + input.size ≤ address ∨
      address < canonicalRunnerLayout.inputBase
    rcases allocator with cursor | limit
    · right
      have cursorBeforeInput : Elflings.canonicalHeapPosAddr + 8 ≤
          canonicalRunnerLayout.inputBase := by native_decide
      omega
    · right
      have limitBeforeInput : Elflings.canonicalHeapTopAddr + 8 ≤
          canonicalRunnerLayout.inputBase := by native_decide
      omega
  · intro address stack
    simp only [canonicalContractParams, canonicalEnvironment, canonicalStack, range] at stack
    change canonicalRunnerLayout.inputBase + input.size ≤ address ∨
      address < canonicalRunnerLayout.inputBase
    left
    have inputBeforeStack : canonicalRunnerLayout.inputBase + input.size ≤
        canonicalRunnerLayout.stackBase := by
      have capacityBound : input.size ≤ canonicalRunnerLayout.inputCapacity := by
        simpa [canonicalRunnerLayout, Runtime.maximumInputBytes] using Nat.le_of_lt inputBound
      exact Nat.le_trans (Nat.add_le_add_left capacityBound _) layout_pairwise_disjoint.1
    omega
  · native_decide
  · native_decide
  · right
    native_decide
  · intro index indexBound
    simp only [canonicalContractParams, canonicalEnvironment, canonicalStack, range]
    have stackBasePinned : canonicalZesuDecodeRawStackBase = 0x3000000ff5e0 := by native_decide
    have stackStartPinned : canonicalRunnerLayout.stackBase = 0x300000000000 := by native_decide
    have stackSizePinned : canonicalRunnerLayout.stackSize = 1024 * 1024 := by native_decide
    have lower : canonicalRunnerLayout.stackBase ≤ canonicalZesuDecodeRawStackBase + index := by
      rw [stackBasePinned, stackStartPinned]
      omega
    have upper : canonicalZesuDecodeRawStackBase + index <
        canonicalRunnerLayout.stackBase + canonicalRunnerLayout.stackSize := by
      rw [stackBasePinned, stackStartPinned, stackSizePinned]
      omega
    exact ⟨lower, upper⟩
  · native_decide
  · intro index indexBound
    simp only [canonicalContractParams, canonicalEnvironment, canonicalStack, range]
    have stackBasePinned : canonicalZesuDecodeRawStackBase = 0x3000000ff5e0 := by native_decide
    have stackStartPinned : canonicalRunnerLayout.stackBase = 0x300000000000 := by native_decide
    have stackSizePinned : canonicalRunnerLayout.stackSize = 1024 * 1024 := by native_decide
    have entryResultPinned : canonicalContractParams.env.record.entryResult = 848 := by native_decide
    have lower : canonicalRunnerLayout.stackBase ≤ canonicalZesuDecodeRawStackBase + index := by
      rw [stackBasePinned, stackStartPinned]
      omega
    have upper : canonicalZesuDecodeRawStackBase + index <
        canonicalRunnerLayout.stackBase + canonicalRunnerLayout.stackSize := by
      rw [entryResultPinned] at indexBound
      rw [stackBasePinned, stackStartPinned, stackSizePinned]
      omega
    exact ⟨lower, upper⟩
  · have loadFacts : LoadPlatformPinned state [] := loadPinned [] (by native_decide)
    have fetchFacts : FetchPlatformPinned state [] := fetchPinned [] (by native_decide)
    refine {
      normal := normal
      retiredCounter := fetchPresent.1
      mstatus := loadFacts.mstatus
      mseccfg := loadFacts.mseccfg
      platform := ?_
      dataAccess := canonicalDecoderDataAccess (zesuDecodeRawMachineArgs
        ⟨canonicalRunnerLayout.inputBase, input⟩) state rfl inputBound normal pma fetchFacts.2
      landingPad := ?_ }
    · intro next pc agree atPc pcIn
      have normalNext : NormalExecutionState next := normalExecutionState_of_agree
        (Agree.weaken (fun register preserved => by
          refine ⟨?_, normalRegisters_platformPreserved register preserved⟩
          intro equal
          subst register
          simp [normalRegisters] at preserved) agree) normal
      obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := loadFacts.mstatus
      have mstatusNext : next.regs.get? mstatus = some mstatusBits :=
        (agree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusRead
      have pmaNext : next.regs.get? pma_regions = some [zesuMainMemoryRegion] :=
        (agree pma_regions (by simp [decoderPreserved, platformPreserved])).trans pma
      have beforeClint := rawDecoderExecution_before_clint pcIn.1 pcIn.2
      have clintBelowPma : BitVec.toNat plat_clint_base ≤ 2 ^ 63 := by native_decide
      have pmaAllows : FetchPmaAllows next pc :=
        ⟨[zesuMainMemoryRegion], zesuMainMemoryRegion, pmaNext,
          matching_zesuMainMemoryRegion (by decide) (by omega), by native_decide⟩
      have htifNext : next.regs.get? htif_tohost_base = some none :=
        (agree htif_tohost_base (by simp [decoderPreserved, platformPreserved])).trans fetchFacts.2
      have clintBeforeSignature : BitVec.toNat plat_clint_base ≤ BitVec.toNat plat_sig_base := by
        native_decide
      have meipNext : ∃ bit, next.regs.get? sig_meip = some bit := by
        obtain ⟨bit, meip⟩ := fetchPresent.2.2.1
        exact ⟨bit,
          (agree sig_meip (by simp [decoderPreserved, platformPreserved])).trans meip⟩
      exact ⟨fetchBasePlatform_of_offPC atPc
          (fetchBasePlatformOffPC_of_normal normalNext mstatusNext pcIn.2 pmaAllows),
        fetchMemoryNoMMIO_of_state_layout_excluded next pc
          ⟨fetch_mmio_address_excluded_of_before_layout pc beforeClint (by omega), htifNext⟩,
        interruptDisabled_of_normal normalNext mstatusNext meipNext,
        landingPadNotExpected_of_normal normalNext⟩
    · intro next register _ agree
      obtain ⟨mseccfgBits, mseccfgRead, _⟩ := loadFacts.mseccfg
      exact updateElpState_run next register mseccfgBits
        ((agree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans normal.2.1)
        ((agree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgRead)

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
