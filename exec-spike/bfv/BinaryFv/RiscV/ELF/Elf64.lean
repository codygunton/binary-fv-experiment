import BinaryFv.RiscV.Model.Address
import BinaryFv.Binary.ProgramImage

namespace BinaryFv.RiscV

open BinaryFv.Binary

/-- Errors produced by the deliberately bounded ELF64 parser. -/
inductive ElfError where
  | truncated (offset length fileSize : Nat)
  | badMagic
  | unsupportedClass (actual : Nat)
  | unsupportedEndian (actual : Nat)
  | unsupportedIdentVersion (actual : Nat)
  | unsupportedAbi (osAbi abiVersion : Nat)
  | unsupportedType (actual : Nat)
  | unsupportedMachine (actual : Nat)
  | unsupportedVersion (actual : Nat)
  | unsupportedFlags (actual : Nat)
  | invalidHeaderSize (actual : Nat)
  | invalidProgramHeaderSize (actual : Nat)
  | invalidSectionHeaderSize (actual : Nat)
  | unsupportedExtendedNumbering
  | invalidSectionNameTable
  | invalidEntryPoint
  | tableOutOfBounds
  | invalidLoadSegment (index : Nat)
  | unexpectedLoadSegmentCount (actual : Nat)
  | unsupportedProgramHeader (index kind : Nat)
  | noLoadSegments
  | overlappingLoadSegments
  | unsupportedSection (index kind : Nat)
  | invalidSection (index : Nat)
  | missingStaticSymbolTable
  | ambiguousStaticSymbolTable
  | invalidStaticSymbolTable
  | invalidStringTable
  | invalidStringOffset (offset : Nat)
  | unterminatedString (offset : Nat)
  | unsupportedExtendedSymbolIndex (index : Nat)
  | missingStaticSymbol (name : ByteArray)
  | ambiguousStaticSymbol (name : ByteArray)
  | invalidFunctionSymbol (name : ByteArray)
  | symbolOutsideExecutableSegment (name : ByteArray)
deriving DecidableEq

structure Header where
  entry : Nat
  programHeaderOffset : Nat
  sectionHeaderOffset : Nat
  flags : Nat
  programHeaderEntrySize : Nat
  programHeaderCount : Nat
  sectionHeaderEntrySize : Nat
  sectionHeaderCount : Nat
  sectionNameTableIndex : Nat

structure ProgramHeader where
  kind : Nat
  flags : Nat
  fileOffset : Nat
  virtualAddress : Nat
  physicalAddress : Nat
  fileSize : Nat
  memorySize : Nat
  alignment : Nat

structure SectionHeader where
  nameOffset : Nat
  kind : Nat
  flags : Nat
  address : Nat
  fileOffset : Nat
  size : Nat
  link : Nat
  info : Nat
  alignment : Nat
  entrySize : Nat

structure StaticSymbol where
  name : ByteArray
  info : Nat
  other : Nat
  sectionIndex : Nat
  value : Nat
  size : Nat
  deriving DecidableEq

structure ParsedStaticSymbols where
  symbols : Array StaticSymbol
  strings : ByteArray

structure Elf64 where
  bytes : ByteArray
  header : Header
  programHeaders : Array ProgramHeader
  loadSegments : Array ProgramHeader
  sectionHeaders : Array SectionHeader
  staticSymbols : Array StaticSymbol
  staticStrings : ByteArray

namespace ProgramHeader

def containsFileRange (header : ProgramHeader) (address size : Nat) : Bool :=
  decide (header.virtualAddress ≤ address ∧
    address + size ≤ header.virtualAddress + header.fileSize)

def containsMemoryRange (header : ProgramHeader) (address size : Nat) : Bool :=
  decide (header.virtualAddress ≤ address ∧
    address + size ≤ header.virtualAddress + header.memorySize)

def executable (header : ProgramHeader) : Bool :=
  header.flags &&& 1 != 0

def toLoadSegment (bytes : ByteArray) (header : ProgramHeader) : LoadSegment := {
  virtualAddress := header.virtualAddress
  initialBytes := bytes.extract header.fileOffset (header.fileOffset + header.fileSize)
  memorySize := header.memorySize
  flags := header.flags
}

end ProgramHeader

namespace StaticSymbol

def globalFunction (symbol : StaticSymbol) : Bool :=
  symbol.info / 16 == 1 && symbol.info % 16 == 2

end StaticSymbol

namespace SectionHeader

def containsAddressRange (header : SectionHeader) (address size : Nat) : Bool :=
  decide (header.address ≤ address ∧ address + size ≤ header.address + header.size)

def executable (header : SectionHeader) : Bool :=
  header.flags &&& 0x4 != 0

end SectionHeader

namespace Elf64

def elfMagic : Nat := 0x464c457f
def elfClass64 : Nat := 2
def elfDataLittleEndian : Nat := 1
def elfVersionCurrent : Nat := 1
def elfOsAbiSystemV : Nat := 0
def elfTypeExecutable : Nat := 2
def elfMachineRiscV : Nat := 243
def elfHeaderSize : Nat := 64
def programHeaderSize : Nat := 56
def sectionHeaderSize : Nat := 64
def symbolSize : Nat := 24
def extendedProgramHeaderCount : Nat := 0xffff
def extendedSectionNameTableIndex : Nat := 0xffff
def sectionTypeNoBits : Nat := 8
def sectionTypeSymtab : Nat := 2
def sectionTypeStrtab : Nat := 3
def sectionTypeDynamic : Nat := 6
def sectionTypeDynsym : Nat := 11
def programTypeLoad : Nat := 1
def programTypeRiscVAttributes : Nat := 0x70000003
def programTypeGnuStack : Nat := 0x6474e551
def symbolSectionIndexExtended : Nat := 0xffff

def ensure (condition : Bool) (error : ElfError) : Except ElfError Unit :=
  if condition then .ok () else .error error

def checkedSlice (bytes : ByteArray) (offset length : Nat) : Except ElfError ByteArray :=
  if offset ≤ bytes.size ∧ length ≤ bytes.size - offset then
    .ok (bytes.extract offset (offset + length))
  else
    .error (.truncated offset length bytes.size)

def readNatLE? (bytes : ByteArray) (offset : Nat) : Nat → Option Nat
  | 0 => some 0
  | width + 1 => do
    let byte ← bytes[offset]?
    let rest ← readNatLE? bytes (offset + 1) width
    pure (byte.toNat + 256 * rest)

def readNatLE (bytes : ByteArray) (offset width : Nat) : Except ElfError Nat := do
  let _ ← checkedSlice bytes offset width
  match readNatLE? bytes offset width with
  | some value => pure value
  | none => throw (.truncated offset width bytes.size)

def readU8 (bytes : ByteArray) (offset : Nat) : Except ElfError Nat :=
  readNatLE bytes offset 1

def readU16LE (bytes : ByteArray) (offset : Nat) : Except ElfError Nat :=
  readNatLE bytes offset 2

def readU32LE (bytes : ByteArray) (offset : Nat) : Except ElfError Nat :=
  readNatLE bytes offset 4

def readU64LE (bytes : ByteArray) (offset : Nat) : Except ElfError Nat :=
  readNatLE bytes offset 8

def checkedTable (bytes : ByteArray) (offset entrySize count : Nat) : Except ElfError Unit := do
  match checkedSlice bytes offset (entrySize * count) with
  | .ok _ => pure ()
  | .error _ => throw .tableOutOfBounds

def isPowerOfTwo (value : Nat) : Bool :=
  value != 0 && (value &&& (value - 1) == 0)

def parseHeader (bytes : ByteArray) : Except ElfError Header := do
  let magic ← readU32LE bytes 0
  let elfClass ← readU8 bytes 4
  let dataEncoding ← readU8 bytes 5
  let identVersion ← readU8 bytes 6
  let osAbi ← readU8 bytes 7
  let abiVersion ← readU8 bytes 8
  let elfType ← readU16LE bytes 16
  let machine ← readU16LE bytes 18
  let version ← readU32LE bytes 20
  let entry ← readU64LE bytes 24
  let programHeaderOffset ← readU64LE bytes 32
  let sectionHeaderOffset ← readU64LE bytes 40
  let flags ← readU32LE bytes 48
  let headerSize ← readU16LE bytes 52
  let programHeaderEntrySize ← readU16LE bytes 54
  let programHeaderCount ← readU16LE bytes 56
  let sectionHeaderEntrySize ← readU16LE bytes 58
  let sectionHeaderCount ← readU16LE bytes 60
  let sectionNameTableIndex ← readU16LE bytes 62
  let _ ← ensure (magic == elfMagic) .badMagic
  let _ ← ensure (elfClass == elfClass64) (.unsupportedClass elfClass)
  let _ ← ensure (dataEncoding == elfDataLittleEndian) (.unsupportedEndian dataEncoding)
  let _ ← ensure (identVersion == elfVersionCurrent) (.unsupportedIdentVersion identVersion)
  let _ ← ensure (osAbi == elfOsAbiSystemV && abiVersion == 0) (.unsupportedAbi osAbi abiVersion)
  let _ ← ensure (elfType == elfTypeExecutable) (.unsupportedType elfType)
  let _ ← ensure (machine == elfMachineRiscV) (.unsupportedMachine machine)
  let _ ← ensure (version == elfVersionCurrent) (.unsupportedVersion version)
  let _ ← ensure (flags == 0) (.unsupportedFlags flags)
  let _ ← ensure (headerSize == elfHeaderSize) (.invalidHeaderSize headerSize)
  let _ ← ensure (programHeaderEntrySize == programHeaderSize)
    (.invalidProgramHeaderSize programHeaderEntrySize)
  let _ ← ensure (sectionHeaderEntrySize == sectionHeaderSize)
    (.invalidSectionHeaderSize sectionHeaderEntrySize)
  let _ ← ensure
    (programHeaderCount != extendedProgramHeaderCount && sectionHeaderCount != 0 &&
      sectionNameTableIndex != extendedSectionNameTableIndex)
    .unsupportedExtendedNumbering
  let header := {
    entry
    programHeaderOffset
    sectionHeaderOffset
    flags
    programHeaderEntrySize
    programHeaderCount
    sectionHeaderEntrySize
    sectionHeaderCount
    sectionNameTableIndex
  }
  let _ ← checkedTable bytes header.programHeaderOffset header.programHeaderEntrySize
    header.programHeaderCount
  let _ ← checkedTable bytes header.sectionHeaderOffset header.sectionHeaderEntrySize
    header.sectionHeaderCount
  let _ ← ensure (header.sectionNameTableIndex < header.sectionHeaderCount) .invalidSectionNameTable
  pure header

def validLoadAlignment (header : ProgramHeader) : Bool :=
  header.alignment == 0 || header.alignment == 1 ||
    (isPowerOfTwo header.alignment &&
      header.virtualAddress % header.alignment == header.fileOffset % header.alignment)

def parseProgramHeader (bytes : ByteArray) (offset index : Nat) :
    Except ElfError ProgramHeader := do
  let kind ← readU32LE bytes offset
  let flags ← readU32LE bytes (offset + 4)
  let fileOffset ← readU64LE bytes (offset + 8)
  let virtualAddress ← readU64LE bytes (offset + 16)
  let physicalAddress ← readU64LE bytes (offset + 24)
  let fileSize ← readU64LE bytes (offset + 32)
  let memorySize ← readU64LE bytes (offset + 40)
  let alignment ← readU64LE bytes (offset + 48)
  let header := {
    kind
    flags
    fileOffset
    virtualAddress
    physicalAddress
    fileSize
    memorySize
    alignment
  }
  let _ ← checkedSlice bytes header.fileOffset header.fileSize
  if header.kind == programTypeLoad then
    let _ ← ensure (header.fileSize ≤ header.memorySize) (.invalidLoadSegment index)
    let _ ← ensure (header.virtualAddress + header.memorySize ≤ addressLimit)
      (.invalidLoadSegment index)
    let _ ← ensure (validLoadAlignment header) (.invalidLoadSegment index)
    pure header
  else if header.kind == programTypeRiscVAttributes || header.kind == programTypeGnuStack then
    pure header
  else
    throw (.unsupportedProgramHeader index header.kind)

def parseProgramHeaders (bytes : ByteArray) (header : Header) :
    Except ElfError (Array ProgramHeader) :=
  (Array.range header.programHeaderCount).mapM fun index =>
    parseProgramHeader bytes
      (header.programHeaderOffset + index * header.programHeaderEntrySize) index

def loadSegmentsOverlap (left right : ProgramHeader) : Bool :=
  decide (left.virtualAddress < right.virtualAddress + right.memorySize ∧
    right.virtualAddress < left.virtualAddress + left.memorySize)

def loadSegmentsAreDisjoint : List ProgramHeader → Bool
  | [] => true
  | segment :: remaining =>
    !(remaining.any fun other => loadSegmentsOverlap segment other) &&
      loadSegmentsAreDisjoint remaining

def parseSectionHeader (bytes : ByteArray) (offset index : Nat) :
    Except ElfError SectionHeader := do
  let nameOffset ← readU32LE bytes offset
  let kind ← readU32LE bytes (offset + 4)
  let flags ← readU64LE bytes (offset + 8)
  let address ← readU64LE bytes (offset + 16)
  let fileOffset ← readU64LE bytes (offset + 24)
  let size ← readU64LE bytes (offset + 32)
  let link ← readU32LE bytes (offset + 40)
  let info ← readU32LE bytes (offset + 44)
  let alignment ← readU64LE bytes (offset + 48)
  let entrySize ← readU64LE bytes (offset + 56)
  let header := {
    nameOffset
    kind
    flags
    address
    fileOffset
    size
    link
    info
    alignment
    entrySize
  }
  if header.kind == sectionTypeDynamic || header.kind == sectionTypeDynsym then
    throw (.unsupportedSection index header.kind)
  else if header.kind == sectionTypeNoBits then
    pure header
  else
    let _ ← checkedSlice bytes header.fileOffset header.size
    pure header

def parseSectionHeaders (bytes : ByteArray) (header : Header) :
    Except ElfError (Array SectionHeader) :=
  (Array.range header.sectionHeaderCount).mapM fun index =>
    parseSectionHeader bytes
      (header.sectionHeaderOffset + index * header.sectionHeaderEntrySize) index

def findNul? (bytes : ByteArray) (offset : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    match bytes[offset]? with
    | some 0 => some offset
    | some _ => findNul? bytes (offset + 1) fuel
    | none => none

def readString (bytes : ByteArray) (offset : Nat) : Except ElfError ByteArray := do
  let _ ← ensure (offset < bytes.size) (.invalidStringOffset offset)
  match findNul? bytes offset (bytes.size - offset) with
  | some stop => pure (bytes.extract offset stop)
  | none => throw (.unterminatedString offset)

def parseStaticSymbol (bytes strings : ByteArray) (offset index : Nat) :
    Except ElfError StaticSymbol := do
  let nameOffset ← readU32LE bytes offset
  let info ← readU8 bytes (offset + 4)
  let other ← readU8 bytes (offset + 5)
  let sectionIndex ← readU16LE bytes (offset + 6)
  let value ← readU64LE bytes (offset + 8)
  let size ← readU64LE bytes (offset + 16)
  let _ ← ensure (sectionIndex != symbolSectionIndexExtended)
    (.unsupportedExtendedSymbolIndex index)
  let name ← readString strings nameOffset
  pure { name, info, other, sectionIndex, value, size }

def staticSymbolTables (sections : Array SectionHeader) : List SectionHeader :=
  sections.toList.filter fun header => header.kind == sectionTypeSymtab

def parseStaticSymbols (bytes : ByteArray) (sections : Array SectionHeader) :
    Except ElfError ParsedStaticSymbols := do
  let symbolTable ←
    match staticSymbolTables sections with
    | [table] => pure table
    | [] => throw .missingStaticSymbolTable
    | _ => throw .ambiguousStaticSymbolTable
  let _ ← ensure (symbolTable.entrySize == symbolSize && symbolTable.size % symbolSize == 0)
    .invalidStaticSymbolTable
  let some stringTable := sections[symbolTable.link]? | throw .invalidStringTable
  let _ ← ensure (stringTable.kind == sectionTypeStrtab) .invalidStringTable
  let strings ← checkedSlice bytes stringTable.fileOffset stringTable.size
  let symbols ← (Array.range (symbolTable.size / symbolSize)).mapM fun index =>
    parseStaticSymbol bytes strings (symbolTable.fileOffset + index * symbolSize) index
  pure { symbols, strings }

def parse (bytes : ByteArray) : Except ElfError Elf64 := do
  let header ← parseHeader bytes
  let programHeaders ← parseProgramHeaders bytes header
  let loadSegments := programHeaders.filter fun program => program.kind == programTypeLoad
  let _ ← ensure (loadSegments.size != 0) .noLoadSegments
  let _ ← ensure (loadSegmentsAreDisjoint loadSegments.toList) .overlappingLoadSegments
  let sectionHeaders ← parseSectionHeaders bytes header
  let some sectionNameTable := sectionHeaders[header.sectionNameTableIndex]?
    | throw .invalidSectionNameTable
  let _ ← ensure (sectionNameTable.kind == sectionTypeStrtab) .invalidSectionNameTable
  let parsedSymbols ← parseStaticSymbols bytes sectionHeaders
  let _ ← ensure
    (programHeaders.toList.any fun program =>
      program.kind == programTypeLoad && program.executable &&
        program.containsMemoryRange header.entry 1)
    .invalidEntryPoint
  pure {
    bytes
    header
    programHeaders
    loadSegments
    sectionHeaders
    staticSymbols := parsedSymbols.symbols
    staticStrings := parsedSymbols.strings
  }

def programImage (elf : Elf64) : ProgramImage := {
  segments := elf.loadSegments.map fun segment => segment.toLoadSegment elf.bytes
}

def findUniqueStaticSymbol (elf : Elf64) (name : ByteArray) : Except ElfError StaticSymbol :=
  match elf.staticSymbols.toList.filter fun symbol => symbol.name == name with
  | [symbol] => pure symbol
  | [] => throw (.missingStaticSymbol name)
  | _ => throw (.ambiguousStaticSymbol name)

def findUniqueExecutableFunction (elf : Elf64) (name : ByteArray) :
    Except ElfError StaticSymbol := do
  let symbol ← findUniqueStaticSymbol elf name
  let _ ← ensure (symbol.globalFunction) (.invalidFunctionSymbol name)
  let _ ← ensure (symbol.sectionIndex != 0) (.invalidFunctionSymbol name)
  let some symbolSection := elf.sectionHeaders[symbol.sectionIndex]?
    | throw (.invalidFunctionSymbol name)
  let _ ← ensure
    (symbolSection.executable && symbolSection.containsAddressRange symbol.value symbol.size)
    (.invalidFunctionSymbol name)
  let _ ← ensure
    (elf.loadSegments.toList.any fun segment =>
      segment.executable && segment.containsMemoryRange symbol.value symbol.size)
    (.symbolOutsideExecutableSegment name)
  pure symbol

def sourceOffsetFor? (elf : Elf64) (address size : Nat) : Option Nat :=
  match elf.loadSegments.toList.find? fun segment => segment.containsFileRange address size with
  | some segment => some (segment.fileOffset + (address - segment.virtualAddress))
  | none => none

def readSourceU32LE? (elf : Elf64) (address : Nat) : Option Nat :=
  match sourceOffsetFor? elf address 4 with
  | some offset => readNatLE? elf.bytes offset 4
  | none => none

end Elf64

end BinaryFv.RiscV
