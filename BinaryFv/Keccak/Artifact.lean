import BinaryFv.Keccak.ABI
import BinaryFv.RiscV.Elf64
import RethKeccakElf

namespace BinaryFv.Keccak.Artifact

open BinaryFv.RiscV

def parsed : Except ElfError Elf64 :=
  Elf64.parse RethKeccakElf.bytes

def programImage : Except ElfError ProgramImage := do
  let elf ← parsed
  pure (Elf64.programImage elf)

def rethKeccak256Name : ByteArray :=
  "reth_keccak256".toUTF8

/-- The proof-facing entry point is resolved from the generated full ELF symbol table. -/
def rethKeccak256 : Except ElfError StaticSymbol := do
  let elf ← parsed
  Elf64.findUniqueExecutableFunction elf rethKeccak256Name

def entryAddress : Except ElfError Word := do
  let symbol ← rethKeccak256
  pure symbol.value

/-- This target's frozen direct-call ABI uses the sole load image as its code range. -/
def codeRange : Except ElfError AddressRange := do
  let elf ← parsed
  match elf.loadSegments.toList with
  | [segment] => pure ⟨segment.virtualAddress, segment.memorySize⟩
  | segments => throw (.unexpectedLoadSegmentCount segments.length)

def firstLoadHeaderIndex : List ProgramHeader → Nat → Option Nat
  | [], _ => none
  | header :: remaining, index =>
    if header.kind == Elf64.programTypeLoad then some index
    else firstLoadHeaderIndex remaining (index + 1)

def firstLoadHeaderOffset : Except ElfError Nat := do
  let elf ← parsed
  let some index := firstLoadHeaderIndex elf.programHeaders.toList 0 | throw .noLoadSegments
  pure (elf.header.programHeaderOffset + index * elf.header.programHeaderEntrySize)

def layoutIsValid : Bool :=
  match codeRange with
  | .ok code => decide (codePlacement code)
  | .error _ => false

theorem binary_parses : parsed.isOk = true := by
  native_decide

theorem reth_keccak256_resolves : rethKeccak256.isOk = true := by
  native_decide

theorem code_range_resolves : codeRange.isOk = true := by
  native_decide

theorem layout_is_valid : layoutIsValid = true := by
  native_decide

def mutateByte (input : ByteArray) (offset : Nat) (value : UInt8) : ByteArray :=
  if h : offset < input.size then input.set offset value h else input

/-- ELF-format mutations use standard field locations, never target code addresses. -/
def malformedMagic : ByteArray :=
  mutateByte RethKeccakElf.bytes 0 0

def malformedClass : ByteArray :=
  mutateByte RethKeccakElf.bytes 4 1

def truncatedHeaderTable : ByteArray :=
  RethKeccakElf.bytes.extract 0 64

def malformedLoadRange : Except ElfError ByteArray := do
  let offset ← firstLoadHeaderOffset
  pure (mutateByte RethKeccakElf.bytes (offset + 40) 0)

def unsupportedProgramHeader : Except ElfError ByteArray := do
  let offset ← firstLoadHeaderOffset
  pure (mutateByte RethKeccakElf.bytes offset 2)

def malformedLoadRangeRejected : Bool :=
  match malformedLoadRange with
  | .ok bytes => !(Elf64.parse bytes).isOk
  | .error _ => false

def unsupportedProgramHeaderRejected : Bool :=
  match unsupportedProgramHeader with
  | .ok bytes => !(Elf64.parse bytes).isOk
  | .error _ => false

theorem rejects_malformed_magic : (Elf64.parse malformedMagic).isOk = false := by
  native_decide

theorem rejects_malformed_class : (Elf64.parse malformedClass).isOk = false := by
  native_decide

theorem rejects_truncated_header_table : (Elf64.parse truncatedHeaderTable).isOk = false := by
  native_decide

theorem rejects_malformed_load_range : malformedLoadRangeRejected = true := by
  native_decide

theorem rejects_unsupported_program_header : unsupportedProgramHeaderRejected = true := by
  native_decide

def missingRethKeccak256 : Except ElfError StaticSymbol := do
  let elf ← parsed
  let stripped := { elf with
    staticSymbols := elf.staticSymbols.filter fun symbol => symbol.name != rethKeccak256Name }
  Elf64.findUniqueExecutableFunction stripped rethKeccak256Name

def duplicateRethKeccak256 : Except ElfError StaticSymbol := do
  let elf ← parsed
  let symbol ← rethKeccak256
  let duplicated := { elf with staticSymbols := elf.staticSymbols.push symbol }
  Elf64.findUniqueExecutableFunction duplicated rethKeccak256Name

theorem rejects_missing_reth_keccak256 : missingRethKeccak256.isOk = false := by
  native_decide

theorem rejects_duplicate_reth_keccak256 : duplicateRethKeccak256.isOk = false := by
  native_decide

end BinaryFv.Keccak.Artifact
