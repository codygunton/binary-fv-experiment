import BinaryFv.SSZ.Zesu.Artifact.Symbols

namespace BinaryFv.SSZ.Zesu.Analysis

open BinaryFv.RiscV

/-- The six compiler-emitted allocator-vtable tail-call instructions in the pinned decoder. -/
def allocatorIndirectCallSites : Array Nat := #[0x130c8, 0x13510, 0x135d8, 0x1366c, 0x13690, 0x13718]

def wordAt (address : Nat) : Option Nat := Artifact.programImage.readU32LE? address

/-- Each recorded site is the `jr t1` tail transfer reached after loading vtable slot 24. -/
def allocatorIndirectCallSitesAreJrT1 : Bool :=
  allocatorIndirectCallSites.all fun address => wordAt address == some 0x00030067

theorem allocator_indirect_call_sites_are_jr_t1 : allocatorIndirectCallSitesAreJrT1 = true := by
  native_decide

def allocatorVtableCallSlotOffset : Nat := 24

end BinaryFv.SSZ.Zesu.Analysis
