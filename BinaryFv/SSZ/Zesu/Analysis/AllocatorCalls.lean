import BinaryFv.SSZ.Zesu.Artifact.Symbols

namespace BinaryFv.SSZ.Zesu.Analysis

open BinaryFv.RiscV

private instance : DecidableEq (Except ElfError StaticSymbol) := fun left right =>
  match left, right with
  | .ok left, .ok right =>
    if h : left = right then isTrue (by simp [h])
    else isFalse fun equal => h (by simpa using equal)
  | .error left, .error right =>
    if h : left = right then isTrue (by simp [h])
    else isFalse fun equal => h (by simpa using equal)
  | .ok _, .error _ => isFalse fun equal => by cases equal
  | .error _, .ok _ => isFalse fun equal => by cases equal

/-- The six compiler-emitted allocator-vtable tail-call instructions in the pinned decoder. -/
def allocatorIndirectCallSites : Array Nat := #[0x130c8, 0x13510, 0x135d8, 0x1366c, 0x13690, 0x13718]

def wordAt (address : Nat) : Option Nat := Artifact.programImage.readU32LE? address

def doublewordAt (address : Nat) : Option Nat := Artifact.programImage.readU64LE? address

/-- Each recorded site is the `jr t1` tail transfer reached after loading vtable slot 24. -/
def allocatorIndirectCallSitesAreJrT1 : Bool :=
  allocatorIndirectCallSites.all fun address => wordAt address == some 0x00030067

theorem allocator_indirect_call_sites_are_jr_t1 : allocatorIndirectCallSitesAreJrT1 = true := by
  native_decide

def allocatorVtableCallSlotOffset : Nat := 24

/-- The immutable Zig allocator vtable emitted into the canonical ELF's `.rodata`. -/
def allocatorVtableAddress : Nat := 0x13f70
def allocatorWrapperAddress : Nat := 0x13768

/-- Slot zero is the allocation wrapper in the immutable Zig allocator vtable. -/
def allocatorVtableAllocTarget : Option Nat := doublewordAt allocatorVtableAddress

theorem allocator_vtable_alloc_target : allocatorVtableAllocTarget = some allocatorWrapperAddress := by
  native_decide

/-- The six recorded `jr t1` sites load vtable slot 24, which is Zig's `free` slot. -/
def allocatorVtableFreeTarget : Option Nat :=
  doublewordAt (allocatorVtableAddress + allocatorVtableCallSlotOffset)

theorem allocator_vtable_free_target : allocatorVtableFreeTarget = some 0x10440 := by
  native_decide

/-- The actual target of the six cleanup transfers is a one-instruction `ret` stub. -/
def allocatorFreeStubWord : Option Nat := wordAt 0x10440

theorem allocator_free_stub_word : allocatorFreeStubWord = some 0x00008067 := by
  native_decide

/-- The wrapper ends with an ELF-pinned AUIPC/JALR tail transfer to `zesu_raw_alloc`. -/
def allocatorWrapperTailWords : Bool :=
  wordAt 0x13778 == some 0xffffd317 && wordAt 0x1377c == some 0xad430067

theorem allocator_wrapper_tail_words : allocatorWrapperTailWords = true := by
  native_decide

theorem allocator_wrapper_address_is_raw_alloc_target :
    Artifact.zesuRawAlloc = .ok
      { name := "zesu_raw_alloc".toUTF8, info := 18, other := 0, sectionIndex := 1,
        value := 0x1024c, size := 100 } := by
  native_decide

end BinaryFv.SSZ.Zesu.Analysis
