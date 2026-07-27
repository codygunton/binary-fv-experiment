import BinaryFv.SSZ.Zesu.Artifact.Symbols
import BinaryFv.SSZ.Zesu.Runtime.AllocationBound
import BinaryFv.SSZ.Zesu.Elfling.GeneratedDecoderGlobals
import DecoderGlobals

/-!
# Memory reserved by the executable runner

The linked decoder already occupies code, constants, globals, and a 64 MiB heap. The runner must add
an input buffer, machine stack, and return sentinel without overlapping any of them. `RunnerLayout`
records those locations, and this module proves that its ranges are aligned, non-wrapping, disjoint,
and above everything used by the ELF.

Getting this wrong is not a proof inconvenience, it is a silent unsoundness: a stack that overlapped
the heap would let the decoder's own frame corrupt an allocation and the run would still "succeed".
So the layout is one pinned record with concrete addresses, and each property below is a `decide` on
those numbers rather than a side condition carried around.

Rather than case over every loaded segment, the module
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

/-- **The arena and the decoder's private globals do not overlap.** Arena `[86048, 67194912)`,
BSS `[69292064, 69292928)`, so the arena ends about 2.1 MB below the globals begin.

Needed by the ownership discipline: a container whose record lives in the globals — the
`stored_result` object at `canonicalResultBuffer` — must be shown disjoint from every heap-allocated
sibling, and that cannot come from allocator monotonicity because the record is not in the arena at
all. This is the one global fact that discharges it, rather than an obligation per sibling pair.

**Stated as ceiling-of-one ≤ base-of-other, and it must be.** The tempting neighbour —
`heapCeiling ≤ globalsCeiling`, ordering the two *ceilings* — is also true and also closes by
`decide`, and it does **not** give disjointness: two regions can stand in any ceiling ordering while
one starts below the other's base and swallows it. A lemma in that form would prove cleanly and be
weaker than its name. -/
theorem arena_disjoint_from_globals :
    heapCeiling ≤ Elfling.GeneratedDecoderGlobals.bssBase := by decide

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

/-- **No loaded address is the sentinel**, as a disequality rather than a strict bound.

This is the `Nat`-level half of what `RiscV/Elfling/SentinelBridge.lean` calls
`regionAvoidsSentinel`/`exitAvoidsSentinel`: the bridge's two avoidance hypotheses are `pc ≠ sentinel`
for every pc the run retires at and every exit pc, and it says explicitly that neither can be
discharged generically — "the sentinel is chosen outside every mapped range, and every region and
exit address is inside one" is a target fact, and this is that fact.

Stated separately from `loaded_disjoint_from_runner` because the bridge wants `≠`, not `<`: deriving
one from the other is one `Nat.ne_of_lt`, and doing it once here is what keeps the per-region
avoidance proofs from each re-deriving it in a slightly different shape. -/
theorem loaded_ne_sentinel (address : Nat)
    (loaded : ∃ byte, Artifact.programImage.readByte? address = some byte) :
    address ≠ canonicalRunnerLayout.sentinel :=
  Nat.ne_of_lt (loaded_disjoint_from_runner address loaded).2.2

/-- The same fact about a machine word, which is the form the bridge's hypotheses are stated in.

The `toNat` round trip is the whole content: `canonicalRunnerLayout.sentinel` is below `2 ^ 64`
(`layout_no_wrap`), so `BitVec.ofNat 64` of it reads back as itself, and a pc whose `toNat` is a
loaded address therefore cannot be that word. -/
theorem loaded_word_ne_sentinel (pc : BitVec 64)
    (loaded : ∃ byte, Artifact.programImage.readByte? pc.toNat = some byte) :
    pc ≠ BitVec.ofNat 64 canonicalRunnerLayout.sentinel := by
  intro hpc
  refine loaded_ne_sentinel pc.toNat loaded ?_
  rw [hpc]
  simpa using Nat.mod_eq_of_lt layout_no_wrap.2.2

/-- The input bound the public theorem states is exactly the buffer's capacity, so an admissible
input always fits and there is no second, looser bound anywhere in the runner. -/
theorem layout_input_capacity_is_theorem_bound :
    canonicalRunnerLayout.inputCapacity = Runtime.maximumInputBytes := rfl

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
