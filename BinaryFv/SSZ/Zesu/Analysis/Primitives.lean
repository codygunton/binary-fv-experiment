import BinaryFv.SSZ.Zesu.Analysis.Decode

namespace BinaryFv.SSZ.Zesu.Analysis

open BinaryFv.RiscV

/-- ELF-decoded primitive memory-read candidates; source names and debug mappings are not inputs. -/
def primitiveReadAddresses? : Option (Array Nat) :=
  decodedWords?.map fun words =>
    words.foldl (fun addresses word =>
      match word.instruction with
      | .LOAD _ => addresses.push word.encoded.address
      | _ => addresses) #[]

/-- ELF-decoded load candidates of one exact byte width. -/
def primitiveReadAddressesOfWidth? (width : Nat) : Option (Array Nat) :=
  decodedWords?.map fun words =>
    words.foldl (fun addresses word =>
      match word.instruction with
      | .LOAD (_, _, _, _, loadWidth) =>
        if loadWidth == width then addresses.push word.encoded.address else addresses
      | _ => addresses) #[]

/-- Each candidate remains an instruction that the authoritative Sail decoder classified as a load. -/
def primitiveReadInventoryValid : Bool :=
  match decodedWords?, primitiveReadAddresses? with
  | some words, some addresses =>
    addresses.all fun address =>
      match words.toList.find? fun word => word.encoded.address == address with
      | some word => match word.instruction with | .LOAD _ => true | _ => false
      | none => false
  | _, _ => false

theorem primitive_read_inventory_valid : primitiveReadInventoryValid = true := by
  native_decide

def primitiveReadWidthsInventoryValid : Bool :=
  match decodedWords?, primitiveReadAddressesOfWidth? 1, primitiveReadAddressesOfWidth? 2,
      primitiveReadAddressesOfWidth? 4, primitiveReadAddressesOfWidth? 8 with
  | some words, some byteLoads, some halfwordLoads, some wordLoads, some doublewordLoads =>
    (byteLoads ++ halfwordLoads ++ wordLoads ++ doublewordLoads).all fun address =>
      match words.toList.find? fun word => word.encoded.address == address with
      | some word => match word.instruction with
        | .LOAD (_, _, _, _, width) => width == 1 || width == 2 || width == 4 || width == 8
        | _ => false
      | none => false
  | _, _, _, _, _ => false

theorem primitive_read_widths_inventory_valid : primitiveReadWidthsInventoryValid = true := by
  native_decide

/-- The first parser-owned raw-header byte-read run, recorded solely from canonical ELF words. -/
def rawHeaderByteReadSites : Array Nat := #[0x104bc, 0x104c4, 0x10534, 0x10538]

def rawHeaderByteReadWords : Array Nat := #[0x000a4503, 0x001a4503, 0x002a4503, 0x003a4583]

def rawHeaderByteReadBlockValid : Bool :=
  rawHeaderByteReadSites.zip rawHeaderByteReadWords |>.all fun entry =>
    Artifact.programImage.readU32LE? entry.1 == some entry.2

theorem raw_header_byte_read_block_valid : rawHeaderByteReadBlockValid = true := by
  native_decide

end BinaryFv.SSZ.Zesu.Analysis
