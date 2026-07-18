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

end BinaryFv.SSZ.Zesu.Analysis
