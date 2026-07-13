import ShaFv.SHA3.Root
import ShaFv.RISCV.Machine

namespace ShaFv.SHA3.Artifact

open ShaFv.RISCV

def sha3Name : ByteArray :=
  "sha3".toUTF8

def programImage : Except ElfError ProgramImage := do
  let elf ← binary.parsed
  pure (Elf64.programImage elf)

def loadSegmentHasCodePlacement (segment : ProgramHeader) : Bool :=
  decide (segment.virtualAddress + segment.memorySize ≤ addressLimit) &&
    decide (sha3CodeWindow.start ≤ segment.virtualAddress) &&
      decide (segment.virtualAddress + segment.memorySize ≤ sha3CodeWindow.stop)

def loadSegmentsHaveCodePlacement : Bool :=
  match binary.parsed with
  | .ok elf =>
    elf.loadSegments.toList.all loadSegmentHasCodePlacement
  | .error _ => false

theorem load_segments_have_code_placement : loadSegmentsHaveCodePlacement = true := by
  native_decide

def sha3Symbol : Except ElfError StaticSymbol := do
  let elf ← binary.parsed
  Elf64.findUniqueExecutableFunction elf sha3Name

def sha3Address : Except ElfError Nat := do
  let symbol ← sha3Symbol
  pure symbol.value

def imageSha3Word : Except ElfError Nat := do
  let elf ← binary.parsed
  let symbol ← sha3Symbol
  match (Elf64.programImage elf).readU32LE? symbol.value with
  | some word => pure word
  | none => throw (.symbolOutsideExecutableSegment sha3Name)

def sourceSha3Word : Except ElfError Nat := do
  let elf ← binary.parsed
  let symbol ← sha3Symbol
  match Elf64.readSourceU32LE? elf symbol.value with
  | some word => pure word
  | none => throw (.symbolOutsideExecutableSegment sha3Name)

theorem binary_parses : binary.parsed.isOk = true := by
  native_decide

theorem sha3_address : sha3Address.toOption = some 0x10540 := by
  native_decide

/-- The image fetch word comes from the same parsed ELF bytes as its source segment. -/
theorem image_sha3_word_eq_source : imageSha3Word.toOption = sourceSha3Word.toOption := by
  native_decide

def fetchSha3Instruction : Except ElfError FetchResult := do
  let elf ← binary.parsed
  let symbol ← sha3Symbol
  match (fetchLoadedSha3 (Elf64.programImage elf) symbol.value).run initialState with
  | .ok fetched _ => pure fetched
  | .error _ _ => throw (.symbolOutsideExecutableSegment sha3Name)

def fetchedSha3WordMatchesImage : Bool :=
  match fetchSha3Instruction, sha3Symbol, programImage with
  | .ok (.F_Base fetched), .ok symbol, .ok image =>
    match image.readU32LE? symbol.value with
    | some expected => fetched.toNat == expected
    | none => false
  | _, _, _ => false

/-- Sail fetches the code word that the parser derived from the embedded ELF image. -/
theorem fetched_sha3_word_matches_image : fetchedSha3WordMatchesImage = true := by
  native_decide

def mutateByte (offset : Nat) (value : UInt8) : ByteArray :=
  if h : offset < bytes.size then bytes.set offset value h else bytes

def malformedMagic : ByteArray :=
  mutateByte 0 0

def malformedClass : ByteArray :=
  mutateByte 4 1

def malformedEndian : ByteArray :=
  mutateByte 5 2

def malformedMachine : ByteArray :=
  mutateByte 18 0x12

def truncatedProgramHeaderTable : ByteArray :=
  bytes.extract 0 0xe7

def truncatedSectionHeaderTable : ByteArray :=
  bytes.extract 0 0xe9f

def oversizedLoadFileRange : ByteArray :=
  mutateByte 0x99 0xff

def loadMemorySmallerThanFile : ByteArray :=
  mutateByte 0xa0 0

def loadOutsideCodeWindow : ByteArray :=
  mutateByte 0x8a 0

def malformedSymbolTableRange : ByteArray :=
  mutateByte 0xdf9 0xff

def missingSha3Name : ByteArray :=
  mutateByte 0xc31 0x78

def unsupportedProgramHeader : ByteArray :=
  mutateByte 0x78 2

def nonExecutableLoadSegment : ByteArray :=
  mutateByte 0x7c 4

def undefinedSha3Symbol : ByteArray :=
  mutateByte 0xaae 0

theorem rejects_malformed_magic : (Elf64.parse malformedMagic).isOk = false := by
  native_decide

theorem rejects_malformed_class : (Elf64.parse malformedClass).isOk = false := by
  native_decide

theorem rejects_malformed_endian : (Elf64.parse malformedEndian).isOk = false := by
  native_decide

theorem rejects_malformed_machine : (Elf64.parse malformedMachine).isOk = false := by
  native_decide

theorem rejects_truncated_program_header_table :
    (Elf64.parse truncatedProgramHeaderTable).isOk = false := by
  native_decide

theorem rejects_truncated_section_header_table :
    (Elf64.parse truncatedSectionHeaderTable).isOk = false := by
  native_decide

theorem rejects_oversized_load_file_range : (Elf64.parse oversizedLoadFileRange).isOk = false := by
  native_decide

theorem rejects_load_memory_smaller_than_file :
    (Elf64.parse loadMemorySmallerThanFile).isOk = false := by
  native_decide

theorem rejects_load_outside_code_window : (Elf64.parse loadOutsideCodeWindow).isOk = false := by
  native_decide

theorem rejects_malformed_symbol_table_range :
    (Elf64.parse malformedSymbolTableRange).isOk = false := by
  native_decide

theorem rejects_unsupported_program_header :
    (Elf64.parse unsupportedProgramHeader).isOk = false := by
  native_decide

theorem rejects_missing_sha3_symbol :
    (do
      let elf ← Elf64.parse missingSha3Name
      Elf64.findUniqueExecutableFunction elf sha3Name).isOk = false := by
  native_decide

theorem rejects_nonexecutable_sha3_symbol :
    (do
      let elf ← Elf64.parse nonExecutableLoadSegment
      Elf64.findUniqueExecutableFunction elf sha3Name).isOk = false := by
  native_decide

theorem rejects_undefined_sha3_symbol :
    (do
      let elf ← Elf64.parse undefinedSha3Symbol
      Elf64.findUniqueExecutableFunction elf sha3Name).isOk = false := by
  native_decide

end ShaFv.SHA3.Artifact
