import BinaryFv.RiscV.Execution.ImageLoad
import BinaryFv.RiscV.Execution.MemoryIo
import BinaryFv.RiscV.Logic.Framing

/-!
# Memory establishment for the sparse file-backed loader

The runner builds its entry state by materializing memory with a handful of loops
(`loadSegmentPrefix`, `loadBytes`, `loadFilledBytes`). Every later correspondence step needs to read
back what those loops wrote and to know they touched nothing else. This module proves exactly that,
bottom-up, so the state builder's memory facts (`fileBytesMatchMemory`, `MemoryBytes`, zeroed
globals) reduce to running the loaders.

Two disciplines carry the proofs:

* `loadSegmentPrefix` is a structural recursion on the byte count, so its establishment lemma is a
  plain induction: it writes `[virtualAddress, virtualAddress + count)` to the segment's file bytes,
  leaves every other address and every register untouched, and always succeeds (a `writeByte` cannot
  fail).
* the `for`-loop loaders (`loadBytes`, `loadFilledBytes`) are handled in a companion lemma set built
  on the same `writeByte` frame lemmas.

Everything here is target-independent; the SSZ runner instantiates it against `Artifact.programImage`
and `canonicalRunnerLayout`.
-/

namespace BinaryFv.RiscV

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The byte value `loadSegmentPrefix` writes at offset `i`: the segment's file byte, zero-extended,
defaulting to zero past the end of the file image. -/
def segmentPrefixByte (segment : LoadSegment) (i : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((segment.initialBytes[i]?).getD 0).toNat

/--
**`loadSegmentPrefix` establishes its window and frames everything else.** Running it from any state
succeeds in a state that holds the segment's first `count` file bytes at
`[virtualAddress, virtualAddress + count)`, agrees with the start state on every address outside that
window, and leaves the registers unchanged.

Proved by induction on `count`: the recursive step writes the top byte `virtualAddress + count`, then
the tail fills the lower window; the top write is invisible to the tail (a lower address) and the
tail's writes are invisible to the top (they are below it), so the two windows compose without
overlap.
-/
theorem loadSegmentPrefix_establishes (segment : LoadSegment) (count : Nat) (s0 : State) :
    ∃ s, Runs (loadSegmentPrefix segment count) s0 s () ∧
      s.regs = s0.regs ∧
      (∀ addr, addr < segment.virtualAddress → s.mem.get? addr = s0.mem.get? addr) ∧
      (∀ addr, segment.virtualAddress + count ≤ addr → s.mem.get? addr = s0.mem.get? addr) ∧
      (∀ i, i < count →
        s.mem.get? (segment.virtualAddress + i) = some (segmentPrefixByte segment i)) := by
  induction count generalizing s0 with
  | zero =>
    refine ⟨s0, ?_, rfl, fun _ _ => rfl, fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    show (loadSegmentPrefix segment 0).run s0 = .ok () s0
    rfl
  | succ count ih =>
    -- the top write, then the tail
    have hwrite : Runs (writeByte (segment.virtualAddress + count) (segmentPrefixByte segment count))
        s0 { s0 with mem := s0.mem.insert (segment.virtualAddress + count) (segmentPrefixByte segment count) } () := by
      show (writeByte (segment.virtualAddress + count) (segmentPrefixByte segment count)).run s0 = .ok () _
      rw [writeByte_run]
    obtain ⟨s, hrun, hregs, hlow, hhigh, hwin⟩ :=
      ih { s0 with mem := s0.mem.insert (segment.virtualAddress + count) (segmentPrefixByte segment count) }
    have hmidmem : ∀ addr, addr ≠ segment.virtualAddress + count →
        (s0.mem.insert (segment.virtualAddress + count) (segmentPrefixByte segment count)).get? addr
          = s0.mem.get? addr := by
      intro addr hne
      rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
      simp [Ne.symm hne]
    refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
    · have hstep : loadSegmentPrefix segment (count + 1)
          = (writeByte (segment.virtualAddress + count) (segmentPrefixByte segment count)
              >>= fun _ => loadSegmentPrefix segment count) := rfl
      rw [hstep]; exact Runs.bind hwrite hrun
    · rw [hregs]
    · intro addr haddr
      rw [hlow addr haddr, hmidmem addr (by omega)]
    · intro addr haddr
      rw [hhigh addr (by omega), hmidmem addr (by omega)]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact hwin i hlt
      · subst heq
        rw [hhigh (segment.virtualAddress + i) (Nat.le_refl _),
          Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
        simp only [beq_self_eq_true, if_true]

/-- **`loadFileSegment` establishes the segment's file bytes.** It is `loadSegmentPrefix` at the file
size, so every address the segment backs with a file byte reads that byte back, and every address
outside `[virtualAddress, virtualAddress + fileSize)` and every register is untouched. -/
theorem loadFileSegment_establishes (segment : LoadSegment) (s0 : State) :
    ∃ s, Runs (loadFileSegment segment) s0 s () ∧
      s.regs = s0.regs ∧
      (∀ addr, addr < segment.virtualAddress → s.mem.get? addr = s0.mem.get? addr) ∧
      (∀ addr, segment.initialEndAddress ≤ addr → s.mem.get? addr = s0.mem.get? addr) ∧
      (∀ addr byte, segment.readFileByte? addr = some byte →
        s.mem.get? addr = some (BitVec.ofNat 8 byte.toNat)) := by
  obtain ⟨s, hrun, hregs, hlow, hhigh, hwin⟩ := loadSegmentPrefix_establishes segment segment.fileSize s0
  refine ⟨s, hrun, hregs, hlow, ?_, ?_⟩
  · intro addr haddr
    exact hhigh addr (by simpa [LoadSegment.initialEndAddress] using haddr)
  · intro addr byte hfile
    -- decode `readFileByte?`: addr is in the file range and byte is the recorded byte
    rw [LoadSegment.readFileByte?] at hfile
    by_cases hin : segment.containsInitialByte addr
    · rw [if_pos hin] at hfile
      have hbounds : segment.virtualAddress ≤ addr ∧ addr < segment.initialEndAddress := by
        simpa [LoadSegment.containsInitialByte] using hin
      have hlt : addr - segment.virtualAddress < segment.fileSize := by
        have := hbounds.2; simp [LoadSegment.initialEndAddress] at this; omega
      have hidx : addr = segment.virtualAddress + (addr - segment.virtualAddress) := by omega
      have hval := hwin (addr - segment.virtualAddress) hlt
      rw [← hidx] at hval
      rw [hval]
      -- `segmentPrefixByte` at an in-file index is exactly the recorded byte
      have : segment.initialBytes[addr - segment.virtualAddress]? = some byte := hfile
      simp only [segmentPrefixByte, this, Option.getD_some]
    · rw [if_neg hin] at hfile; exact absurd hfile (by simp)

/-- The runner loads a single-segment image, so `loadFileBackedImage` reduces to one
`loadFileSegment` and establishes the whole image's file bytes.

For a one-segment image `image.readFileByte?` is exactly that segment's `readFileByte?` (the only
segment is the one `fileSegmentAt?` can find), and `loadFileBackedImage image = loadFileSegment seg`.
So the segment establishment lifts directly to `image.fileBytesMatchMemory`. -/
theorem loadFileBackedImage_single_establishes {image : ProgramImage} {segment : LoadSegment}
    (single : image.segments = #[segment]) (s0 : State) :
    ∃ s, Runs (loadFileBackedImage image) s0 s () ∧
      s.regs = s0.regs ∧
      (∀ addr, addr < segment.virtualAddress → s.mem.get? addr = s0.mem.get? addr) ∧
      (∀ addr, segment.initialEndAddress ≤ addr → s.mem.get? addr = s0.mem.get? addr) ∧
      image.fileBytesMatchMemory s.mem := by
  obtain ⟨s, hrun, hregs, hlow, hhigh, hfile⟩ := loadFileSegment_establishes segment s0
  have hlist : image.segments.toList.reverse = [segment] := by rw [single]; rfl
  have hrun' : Runs (loadFileBackedImage image) s0 s () := by
    show Runs (loadFileSegments image.segments.toList.reverse) s0 s ()
    rw [hlist]
    exact Runs.bind hrun (by show (loadFileSegments []).run s = .ok () s; rfl)
  refine ⟨s, hrun', hregs, hlow, hhigh, ?_⟩
  intro addr byte himg
  -- reduce the image read to the single segment's read
  have hseg : image.readFileByte? addr = segment.readFileByte? addr := by
    rw [ProgramImage.readFileByte?]
    show (match image.fileSegmentAt? addr with
      | some seg => seg.readFileByte? addr | none => none) = _
    rw [ProgramImage.fileSegmentAt?, single]
    by_cases hin : segment.containsInitialByte addr
    · simp [List.find?, hin]
    · simp [List.find?, hin, LoadSegment.readFileByte?]
  rw [hseg] at himg
  exact hfile addr byte himg

end BinaryFv.RiscV
