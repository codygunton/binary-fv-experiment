import BinaryFv.Zesu.Artifacts.Layout

namespace BinaryFv.Zesu.Artifacts

open BinaryFv.Binary
open BinaryFv.RiscV

def programImage : ProgramImage :=
  match parsed with
  | .ok parsedElf => parsedElf.programImage
  | .error _ => { segments := #[] }

def symbol (name : String) : Except ElfError StaticSymbol :=
  parsed.bind fun parsedElf => parsedElf.findUniqueExecutableFunction name.toUTF8

def zesuRawAlloc : Except ElfError StaticSymbol := symbol "zesu_raw_alloc"
def zesuRawResult : Except ElfError StaticSymbol := symbol "zesu_raw_result"
def zesuRawError : Except ElfError StaticSymbol := symbol "zesu_raw_error"
def memcpy : Except ElfError StaticSymbol := symbol "memcpy"
def memmove : Except ElfError StaticSymbol := symbol "memmove"

def operationalSymbols : List (Except ElfError StaticSymbol) :=
  [zesuDecodeRaw, zesuRawAlloc, zesuRawResult, zesuRawError, memcpy, memmove]

def operationalSymbolsResolve : Bool := operationalSymbols.all Except.isOk

theorem operational_symbols_resolve : operationalSymbolsResolve = true := by
  native_decide

/-- The proof entry's exact executable range, resolved from the canonical ELF symbol table. -/
def zesuDecodeRawCodeRange : Except ElfError AddressRange := do
  let entry ← zesuDecodeRaw
  pure ⟨entry.value, entry.size⟩

theorem zesu_decode_raw_code_range_resolves : zesuDecodeRawCodeRange.isOk = true := by
  native_decide

def memcpyCodeRange : Except ElfError AddressRange := do
  let entry ← memcpy
  pure ⟨entry.value, entry.size⟩

def memmoveCodeRange : Except ElfError AddressRange := do
  let entry ← memmove
  pure ⟨entry.value, entry.size⟩

theorem memcpy_code_range_resolves : memcpyCodeRange.isOk = true := by
  native_decide

theorem memmove_code_range_resolves : memmoveCodeRange.isOk = true := by
  native_decide

end BinaryFv.Zesu.Artifacts
