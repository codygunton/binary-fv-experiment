import BinaryFv.RiscV.Elf64
import BinaryFv.RiscV.Machine

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

inductive DecodeError where
  | incompleteWord (address : Nat)
  | missingWord (address : Nat)
deriving DecidableEq, Repr

structure EncodedWord where
  address : Nat
  bits : BitVec 32
deriving Repr

structure DecodedWord where
  encoded : EncodedWord
  instruction : instruction
deriving Repr

def SectionHeader.executableWordAddresses (header : SectionHeader) :
    Except DecodeError (Array Nat) :=
  if !header.executable then
    pure #[]
  else if header.size % 4 != 0 then
    throw (.incompleteWord (header.address + header.size - header.size % 4))
  else
    pure ((Array.range (header.size / 4)).map fun index => header.address + 4 * index)

/-- Derive every fixed-width executable instruction word from parser-owned ELF sections. -/
def Elf64.executableWords (elf : Elf64) : Except DecodeError (Array EncodedWord) := do
  let addresses ← elf.sectionHeaders.foldl (fun addresses header => do
    let addresses ← addresses
    let sectionAddresses ← header.executableWordAddresses
    pure (addresses ++ sectionAddresses)) (.ok #[])
  let image := elf.programImage
  addresses.mapM fun address => do
    let some value := image.readU32LE? address | throw (.missingWord address)
    pure { address, bits := BitVec.ofNat 32 value }

def decodeWord (encoded : EncodedWord) : SailM DecodedWord := do
  pure { encoded, instruction := ← ext_decode encoded.bits }

def decodeWords (words : Array EncodedWord) : SailM (Array DecodedWord) :=
  words.mapM decodeWord

def DecodedWord.legal (decoded : DecodedWord) : Bool :=
  match decoded.instruction with
  | .ILLEGAL _ | .C_ILLEGAL _ => false
  | _ => true

def StaticSymbol.function (symbol : StaticSymbol) : Bool :=
  symbol.info % 16 == 2

/-- Keep only parser-validated function symbols contained in executable sections. -/
def Elf64.executableFunctions (elf : Elf64) : Array StaticSymbol :=
  elf.staticSymbols.filter fun symbol =>
    symbol.function && (match elf.sectionHeaders[symbol.sectionIndex]? with
      | some header => header.executable && header.containsAddressRange symbol.value symbol.size
      | none => false)

def Elf64.largestExecutableFunctionSize (elf : Elf64) : Nat :=
  elf.executableFunctions.foldl (fun largest symbol => max largest symbol.size) 0

/-- Select a core by an ELF-derived structural property, not by a target address or name. -/
def Elf64.uniqueLargestExecutableFunction? (elf : Elf64) : Option StaticSymbol :=
  match (elf.executableFunctions.filter fun symbol =>
    symbol.size == elf.largestExecutableFunctionSize).toList with
  | [symbol] => some symbol
  | _ => none

end BinaryFv.RiscV
