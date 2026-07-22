import DecoderGlobals
import BinaryFv.SSZ.Zesu.Artifact.Symbols
import BinaryFv.SSZ.Zesu.Contracts.ExportedDecoder

/-!
# Validation of the extracted decoder globals

`DecoderGlobals.lean` is *untrusted* generated data: the canonical linked addresses and sizes of the
decoder's private globals (`attempted`, `allocator_state`, `last_status`, `stored_result`), extracted
by `tools/generate_elfling_program.py` from the sidecar symbol table (offsets) and the pinned linker
map (the `.bss` base), together with the exported accessors' instructions that reference them.

This module *checks* that data against the pinned canonical image and only then defines
`canonicalDecoderGlobalsLayout`. The addresses are never handwritten or existentially chosen: they
flow from the generated artifact, and `decoderGlobalsValidated` is the kernel-checked proof that the
artifact is internally consistent and agrees with the real production ELF.

The checks, all discharged by `native_decide`:

* **identity** — exactly the four expected globals, in declaration order;
* **size/alignment** — each global's size matches its Zig type, and `last_status`/`stored_result`/the
  `.bss` block carry their required alignment;
* **disjoint `.bss` containment** — every global lies inside the decoder `.bss` block and no two
  overlap;
* **production-ELF references** — each recorded accessor instruction is present in the canonical image
  at its pc with the exact 32-bit word, and its resolved operand target is one of the globals.
-/

namespace BinaryFv.SSZ.Zesu.Elfling

open BinaryFv.SSZ.Zesu.Elfling.GeneratedDecoderGlobals
open BinaryFv.SSZ.Zesu.Artifact (programImage)
open BinaryFv.SSZ.Zesu.Contracts (DecoderGlobalsLayout)

/-- The canonical linked address of a generated decoder global, by symbol name. -/
def decoderGlobalAddr? (name : String) : Option Nat :=
  (globals.find? (fun g => g.1 == name)).map (fun g => g.2.1)

/-- The size in bytes of a generated decoder global, by symbol name. -/
def decoderGlobalSize? (name : String) : Option Nat :=
  (globals.find? (fun g => g.1 == name)).map (fun g => g.2.2)

/-- (1) Exactly the four decoder globals, in declaration order. -/
def identityValid : Bool :=
  globals.map (fun g => g.1) ==
    ["raw_decoder_root.attempted", "raw_decoder_root.allocator_state",
     "raw_decoder_root.last_status", "raw_decoder_root.stored_result"]

/-- (2a) Each global's size matches its Zig type. -/
def sizesValid : Bool :=
  decoderGlobalSize? "raw_decoder_root.attempted" == some 1 &&
  decoderGlobalSize? "raw_decoder_root.allocator_state" == some 1 &&
  decoderGlobalSize? "raw_decoder_root.last_status" == some 4 &&
  decoderGlobalSize? "raw_decoder_root.stored_result" == some 848

/-- (2b) The `.bss` block is 16-aligned; the 32-bit status is 4-aligned; the result buffer is
16-aligned. -/
def alignmentValid : Bool :=
  decide (bssBase % 16 = 0) &&
  decide ((decoderGlobalAddr? "raw_decoder_root.last_status").getD 1 % 4 = 0) &&
  decide ((decoderGlobalAddr? "raw_decoder_root.stored_result").getD 1 % 16 = 0)

/-- Every global's byte range lies inside the decoder `.bss` block. -/
def withinBss : Bool :=
  globals.all (fun g => decide (bssBase ≤ g.2.1) && decide (g.2.1 + g.2.2 ≤ bssBase + bssSize))

/-- Consecutive globals (emitted in ascending address order) do not overlap. -/
def disjointAscending : List (Nat × Nat) → Bool
  | [] => true
  | [_] => true
  | (a1, s1) :: (a2, s2) :: rest => decide (a1 + s1 ≤ a2) && disjointAscending ((a2, s2) :: rest)

/-- (3) Disjoint `.bss` containment. -/
def containmentValid : Bool :=
  withinBss && disjointAscending (globals.map (fun g => (g.2.1, g.2.2)))

/-- The set of generated global addresses. -/
def globalAddrs : List Nat := globals.map (fun g => g.2.1)

/-- (4) Each recorded accessor reference is present in the canonical image at its pc with the exact
32-bit word, and its resolved target is one of the decoder globals. -/
def referencesValid : Bool :=
  accessorRefs.all (fun r =>
    (programImage.readU32LE? r.2.1 == some r.2.2.1) && globalAddrs.contains r.2.2.2)

/-! ## Allocator/heap runtime globals

`runtimeGlobals` are the allocator's mutable cursor `ZKVM_HEAP_POS`, its limit `ZKVM_HEAP_TOP`, and the
64 MiB `heap` region, read from the pinned ELF symbol table. The heap runner (Row D) initializes the
cursor and runs allocations inside this region. -/

/-- The canonical linked address of a runtime global by symbol name. -/
def runtimeGlobalAddr? (name : String) : Option Nat :=
  (runtimeGlobals.find? (fun g => g.1 == name)).map (fun g => g.2.1)

/-- The size in bytes of a runtime global by symbol name. -/
def runtimeGlobalSize? (name : String) : Option Nat :=
  (runtimeGlobals.find? (fun g => g.1 == name)).map (fun g => g.2.2)

/-- (5) Exactly the three runtime globals, in declaration order (limit, cursor, heap). -/
def runtimeIdentityValid : Bool :=
  runtimeGlobals.map (fun g => g.1) == ["ZKVM_HEAP_TOP", "ZKVM_HEAP_POS", "heap"]

/-- (6) The cursor/limit are 8-byte words, the heap is the pinned 64 MiB region, and the three sit
consecutively: `ZKVM_HEAP_TOP`, then `ZKVM_HEAP_POS` 8 bytes later, then `heap` 8 bytes after that. -/
def runtimeLayoutValid : Bool :=
  runtimeGlobalSize? "ZKVM_HEAP_TOP" == some 8 &&
  runtimeGlobalSize? "ZKVM_HEAP_POS" == some 8 &&
  runtimeGlobalSize? "heap" == some (64 * 1024 * 1024) &&
  decide ((runtimeGlobalAddr? "ZKVM_HEAP_TOP").getD 0 + 8 = (runtimeGlobalAddr? "ZKVM_HEAP_POS").getD 1) &&
  decide ((runtimeGlobalAddr? "ZKVM_HEAP_POS").getD 0 + 8 = (runtimeGlobalAddr? "heap").getD 1)

/-- The conjunction of every decoder- and runtime-global check. -/
def decoderGlobalsChecksPass : Bool :=
  identityValid && sizesValid && alignmentValid && containmentValid && referencesValid &&
  runtimeIdentityValid && runtimeLayoutValid

/-- **The generated globals are valid.** Kernel-checked against the pinned canonical image; this is
what licenses the canonical layouts below to be read off the generated artifact. -/
theorem decoderGlobalsValidated : decoderGlobalsChecksPass = true := by native_decide

/-! ## The checked layouts -/

/-- The canonical decoder-globals layout, taken **only** from the validated generated artifact — no
address is handwritten. `zesu_raw_error` reads `status`; `zesu_raw_result` returns `storedResult`
(the buffer itself) or null. -/
def canonicalDecoderGlobalsLayout : DecoderGlobalsLayout :=
  { attempted := (decoderGlobalAddr? "raw_decoder_root.attempted").getD 0
    status := (decoderGlobalAddr? "raw_decoder_root.last_status").getD 0
    storedResult := (decoderGlobalAddr? "raw_decoder_root.stored_result").getD 0 }

/-- The canonical result buffer the exported accessor returns on success: the `stored_result` global
itself (not a separate pointer). -/
def canonicalResultBuffer : Nat :=
  (decoderGlobalAddr? "raw_decoder_root.stored_result").getD 0

/-- The canonical heap base and limit, from the validated `heap` region. -/
def canonicalHeapBase : Nat := (runtimeGlobalAddr? "heap").getD 0
def canonicalHeapLimit : Nat := canonicalHeapBase + (runtimeGlobalSize? "heap").getD 0

/-- The canonical addresses of the allocator's mutable cursor and limit words. -/
def canonicalHeapPosAddr : Nat := (runtimeGlobalAddr? "ZKVM_HEAP_POS").getD 0
def canonicalHeapTopAddr : Nat := (runtimeGlobalAddr? "ZKVM_HEAP_TOP").getD 0

/-- The allocator's mutable state: the 8 bytes of the cursor and the 8 bytes of the limit. A
non-allocating routine must leave every one of these unchanged. -/
def canonicalAllocatorState (address : Nat) : Prop :=
  (canonicalHeapPosAddr ≤ address ∧ address < canonicalHeapPosAddr + 8) ∨
  (canonicalHeapTopAddr ≤ address ∧ address < canonicalHeapTopAddr + 8)

end BinaryFv.SSZ.Zesu.Elfling
