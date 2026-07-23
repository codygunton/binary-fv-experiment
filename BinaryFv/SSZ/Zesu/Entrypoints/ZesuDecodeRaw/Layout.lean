import BinaryFv.SSZ.Zesu.Artifact.Symbols
import BinaryFv.SSZ.Zesu.Runtime.AllocationBound
import BinaryFv.SSZ.Zesu.Elfling.GeneratedDecoderGlobals
import DecoderGlobals

/-!
# The runner's memory layout

Everything the executable runner places in memory that the linked image does not: the input buffer,
the machine stack, and the return sentinel. One record fixes all of them, and this module proves the
properties every later step of the runner and its correspondence proof needs — that no range wraps,
that they are pairwise disjoint, that they are correctly aligned, and that none of them collides
with anything the ELF loads or with the decoder's own heap and globals.

Getting this wrong is not a proof inconvenience, it is a silent unsoundness: a stack that overlapped
the heap would let the decoder's own frame corrupt an allocation and the run would still "succeed".
So the layout is one pinned record with concrete addresses, and each property below is a `decide` on
those numbers rather than a side condition carried around.

*The bound the disjointness rests on.* Rather than case over every loaded segment, the module
establishes one number — `loadedCeiling` — above which the image loads nothing, the heap does not
reach, and the decoder's globals do not sit, and then places every runner range above it. That keeps
the disjointness argument a comparison instead of an enumeration, and it is checked against the real
image rather than assumed.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open BinaryFv.Binary
open BinaryFv.SSZ.Zesu

/-! ## What the image already occupies -/

/-- The end of the decoder's 64 MiB arena: the highest address the runtime globals reach. Read from
the generated runtime-global table, not written by hand. -/
def heapCeiling : Nat :=
  (Elfling.GeneratedDecoderGlobals.runtimeGlobals.foldl
    (fun acc g => max acc (g.2.1 + g.2.2)) 0)

/-- The end of the decoder's private BSS: the highest address its globals reach. -/
def globalsCeiling : Nat :=
  Elfling.GeneratedDecoderGlobals.bssBase + Elfling.GeneratedDecoderGlobals.bssSize

/-- One address above everything the linked image occupies, the arena and the decoder globals
included. Every runner range is placed above it. -/
def loadedCeiling : Nat := 0x1000_0000_0000

/-- Nothing the ELF loads reaches `loadedCeiling`. Checked against the real parsed segments. -/
theorem segments_below_ceiling :
    Artifact.programImage.segments.toList.all
      (fun segment => decide (segment.virtualAddress + segment.memorySize ≤ loadedCeiling))
      = true := by
  native_decide

/-- Neither the arena nor the decoder globals reach it either. -/
theorem runtime_below_ceiling : heapCeiling ≤ loadedCeiling ∧ globalsCeiling ≤ loadedCeiling := by
  constructor <;> decide

/-! ## The layout -/

/-- Where the runner puts the things the image does not contain. Sizes are in bytes; `sentinel` is a
program counter, not a range. -/
structure RunnerLayout where
  /-- Base of the input buffer the exported entry receives in `a0`. -/
  inputBase : Nat
  /-- Capacity of the input buffer: the theorem's input bound, so no admissible input overruns it. -/
  inputCapacity : Nat
  /-- Lowest address of the machine stack. -/
  stackBase : Nat
  /-- Stack size in bytes. -/
  stackSize : Nat
  /-- The return address the entry is called with. Reaching it ends the run. -/
  sentinel : Nat
deriving DecidableEq, Repr

namespace RunnerLayout

/-- One past the last input byte. -/
def inputStop (l : RunnerLayout) : Nat := l.inputBase + l.inputCapacity

/-- One past the top of the stack. The RISC-V stack pointer starts here and grows down. -/
def stackStop (l : RunnerLayout) : Nat := l.stackBase + l.stackSize

end RunnerLayout

/--
The pinned runner layout.

The input buffer is exactly the theorem's bound (`maximumInputBytes`), so an input the public
theorem admits always fits and one it does not is rejected before any address arithmetic. The stack
is 1 MiB, ample for a decoder whose deepest inline nesting is four frames, and 16-byte aligned as
the RISC-V C ABI requires. The sentinel is a 4-aligned address in no range at all: control reaching
it cannot be a real instruction fetch, which is exactly what makes "the run returned" observable.
-/
def canonicalRunnerLayout : RunnerLayout where
  inputBase := 0x2000_0000_0000
  inputCapacity := Runtime.maximumInputBytes
  stackBase := 0x3000_0000_0000
  stackSize := 1024 * 1024
  sentinel := 0x4000_0000_0000

/-! ## The properties the runner and its proofs consume -/

/-- No runner range wraps a 64-bit address, so every address computed from the layout is a genuine
machine address and `BitVec.ofNat` loses nothing. -/
theorem layout_no_wrap :
    canonicalRunnerLayout.inputStop < 2 ^ 64 ∧
      canonicalRunnerLayout.stackStop < 2 ^ 64 ∧
      canonicalRunnerLayout.sentinel < 2 ^ 64 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The input buffer, the stack, and the sentinel are pairwise disjoint. -/
theorem layout_pairwise_disjoint :
    canonicalRunnerLayout.inputStop ≤ canonicalRunnerLayout.stackBase ∧
      canonicalRunnerLayout.stackStop ≤ canonicalRunnerLayout.sentinel := by
  constructor <;> decide

/-- The input buffer is 8-byte aligned (its scalar reads are up to 8 bytes wide) and the stack is
16-byte aligned as the RISC-V C ABI requires; the sentinel is instruction-aligned. -/
theorem layout_aligned :
    canonicalRunnerLayout.inputBase % 8 = 0 ∧
      canonicalRunnerLayout.stackBase % 16 = 0 ∧
      canonicalRunnerLayout.stackStop % 16 = 0 ∧
      canonicalRunnerLayout.sentinel % 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Every runner range sits above everything the image loads, so none of them can collide with the
code, the decoder's globals, or the 64 MiB arena. -/
theorem layout_above_loaded :
    loadedCeiling ≤ canonicalRunnerLayout.inputBase ∧
      loadedCeiling ≤ canonicalRunnerLayout.stackBase ∧
      loadedCeiling ≤ canonicalRunnerLayout.sentinel := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Consequently no loaded byte is a runner byte: an address the image can read back is below every
runner range. This is the form the framing proofs consume. -/
theorem loaded_disjoint_from_runner (address : Nat)
    (loaded : ∃ byte, Artifact.programImage.readByte? address = some byte) :
    address < canonicalRunnerLayout.inputBase ∧
      address < canonicalRunnerLayout.stackBase ∧
      address < canonicalRunnerLayout.sentinel := by
  obtain ⟨byte, hbyte⟩ := loaded
  have hseg := ProgramImage.readByte?_mem_segment hbyte
  obtain ⟨segment, hmem, hlo, hhi⟩ := hseg
  have hbound : segment.virtualAddress + segment.memorySize ≤ loadedCeiling :=
    of_decide_eq_true (List.all_eq_true.mp segments_below_ceiling segment hmem)
  have habove := layout_above_loaded
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- The input bound the public theorem states is exactly the buffer's capacity, so an admissible
input always fits and there is no second, looser bound anywhere in the runner. -/
theorem layout_input_capacity_is_theorem_bound :
    canonicalRunnerLayout.inputCapacity = Runtime.maximumInputBytes := rfl

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
