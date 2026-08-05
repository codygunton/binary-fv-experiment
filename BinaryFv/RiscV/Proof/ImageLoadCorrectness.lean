import BinaryFv.RiscV.Execution.ImageLoad
import BinaryFv.RiscV.Execution.MemoryIo
import BinaryFv.RiscV.Logic.Framing

/-!
# What the sparse memory loaders establish

The entry-state builder uses loops to load file-backed ELF bytes, copy the input, and fill global
regions. Later proofs need both the bytes written inside each window and preservation outside it.
This module supplies those target-independent facts.

There are two proof patterns:

* `loadSegmentPrefix` is a structural recursion on the byte count, so its establishment lemma is a
  plain induction: it writes `[virtualAddress, virtualAddress + count)` to the segment's file bytes,
  leaves every other address and every register untouched, and always succeeds (a `writeByte` cannot
  fail).
* the `for`-loop loaders (`loadBytes`, `loadFilledBytes`) are handled in a companion lemma set built
  on the same `writeByte` frame lemmas.

The SSZ runner applies these generic lemmas to its concrete image and memory layout.
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

/-! ## The `for`-loop loaders (`loadBytes`, `loadFilledBytes`)

`loadBytes` and `loadFilledBytes` are `forIn [:count]` loops of `writeByte`s. `forIn_eq_forIn_range'`
rewrites the range loop to a `List.range'` loop, which admits a clean front induction; the general
lemma below establishes any such write loop, and the two loaders are its specializations. -/

/-- **A `forIn` write loop establishes each write and frames the complement.** For a list `l` of
indices with pairwise-distinct target addresses (`(l.map addr).Nodup`), running
`writeByte (addr i) (val i)` for each `i ∈ l` leaves the registers unchanged, agrees with the start
state on every address not written, and reads each `addr i` back as `val i` (distinctness makes each
write the last to its address). -/
theorem forIn_writeBytes_establishes (addr : Nat → Nat) (val : Nat → BitVec 8) :
    ∀ (l : List Nat) (s0 : State), (l.map addr).Nodup →
      ∃ s, Runs (forIn l PUnit.unit
            (fun i _ => do let _ ← writeByte (addr i) (val i); pure (ForInStep.yield PUnit.unit)))
            s0 s () ∧
        s.regs = s0.regs ∧
        (∀ a, a ∉ l.map addr → s.mem.get? a = s0.mem.get? a) ∧
        (∀ i ∈ l, s.mem.get? (addr i) = some (val i)) := by
  intro l
  induction l with
  | nil =>
    intro s0 _
    refine ⟨s0, ?_, rfl, fun _ _ => rfl, fun i hi => absurd hi (List.not_mem_nil)⟩
    simp only [List.forIn_nil]; rfl
  | cons a l ih =>
    intro s0 hnodup
    have hnodup' : (l.map addr).Nodup := (List.nodup_cons.mp (by simpa using hnodup)).2
    have hnotmem : addr a ∉ l.map addr := (List.nodup_cons.mp (by simpa using hnodup)).1
    -- run the head write, then the tail loop
    have hwrite : Runs (writeByte (addr a) (val a)) s0
        { s0 with mem := s0.mem.insert (addr a) (val a) } () := by
      show (writeByte (addr a) (val a)).run s0 = .ok () _; rw [writeByte_run]
    obtain ⟨s, hrun, hregs, hframe, hwin⟩ := ih { s0 with mem := s0.mem.insert (addr a) (val a) } hnodup'
    have hmidmem : ∀ b, b ≠ addr a →
        (s0.mem.insert (addr a) (val a)).get? b = s0.mem.get? b := by
      intro b hne
      rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]; simp [Ne.symm hne]
    have hbody : Runs (do let _ ← writeByte (addr a) (val a); pure (ForInStep.yield PUnit.unit))
        s0 { s0 with mem := s0.mem.insert (addr a) (val a) } (ForInStep.yield PUnit.unit) :=
      Runs.bind hwrite (by
        show (pure (ForInStep.yield PUnit.unit) : SailM _).run _ = .ok _ _; rfl)
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · rw [List.forIn_cons]; exact Runs.bind hbody hrun
    · rw [hregs]
    · intro b hb
      have hb' : b ∉ l.map addr := fun hmem => hb (by simp [hmem])
      have hbne : b ≠ addr a := fun h => hb (by simp [h])
      rw [hframe b hb', hmidmem b hbne]
    · intro i hi
      rcases List.mem_cons.mp hi with heq | hmem
      · subst heq
        rw [hframe (addr i) hnotmem]
        rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]; simp
      · exact hwin i hmem

/-- The address map of both loaders, `fun i => base + i`, is injective, so its image over
`List.range' 0 count 1` has no duplicates. -/
theorem range'_map_add_nodup (base count : Nat) :
    ((List.range' 0 count 1).map (fun i => base + i)).Nodup := by
  rw [List.map_add_range']; exact List.nodup_range' 1

/-- **`loadFilledBytes` establishes a constant-valued window.** Every address in
`[base, base + count)` reads back `value`; everything else and every register is untouched. -/
theorem loadFilledBytes_establishes (base count : Nat) (value : UInt8) (s0 : State) :
    ∃ s, Runs (loadFilledBytes base count value) s0 s () ∧
      s.regs = s0.regs ∧
      (∀ a, a < base ∨ base + count ≤ a → s.mem.get? a = s0.mem.get? a) ∧
      (∀ i, i < count → s.mem.get? (base + i) = some (BitVec.ofNat 8 value.toNat)) := by
  obtain ⟨s, hrun, hregs, hframe, hwin⟩ :=
    forIn_writeBytes_establishes (fun i => base + i) (fun _ => BitVec.ofNat 8 value.toNat)
      (List.range' 0 count 1) s0 (range'_map_add_nodup base count)
  have hrun' : Runs (loadFilledBytes base count value) s0 s () := by
    show Runs (forIn [:count] PUnit.unit _ >>= fun _ => pure PUnit.unit) s0 s ()
    rw [Std.Range.forIn_eq_forIn_range']
    exact Runs.bind (by simpa using hrun) (by show (pure PUnit.unit : SailM Unit).run s = .ok () s; rfl)
  refine ⟨s, hrun', hregs, ?_, ?_⟩
  · intro a ha
    apply hframe
    simp only [List.mem_map, List.mem_range']
    rintro ⟨i, ⟨_, hi⟩, rfl⟩; omega
  · intro i hi
    exact hwin i (by simp [List.mem_range']; omega)

/-- A `forIn'` whose body ignores the membership proof is the corresponding `forIn`. Proved by
induction; the head step and the `ForInStep` matching are identical on both sides, and the tails agree
by the induction hypothesis. This is what lets `loadBytes` (a `forIn'` because its body reads
`bytes[index]` under the range proof) reduce to the `forIn` establishment above. -/
theorem forIn'_eq_forIn_ignore {α β : Type} (l : List α) (init : β)
    (g : α → β → SailM (ForInStep β)) :
    forIn' l init (fun a _ b => g a b) = forIn l init g := by
  induction l generalizing init with
  | nil => rw [List.forIn'_nil, List.forIn_nil]
  | cons a l ih =>
    rw [List.forIn'_cons, List.forIn_cons]
    refine bind_congr (fun x => ?_)
    cases x with
    | done b => rfl
    | yield b => exact ih b

/-- **`loadZeroBytes` establishes a zeroed window.** Specialization of `loadFilledBytes` at `0`. -/
theorem loadZeroBytes_establishes (base count : Nat) (s0 : State) :
    ∃ s, Runs (loadZeroBytes base count) s0 s () ∧
      s.regs = s0.regs ∧
      (∀ a, a < base ∨ base + count ≤ a → s.mem.get? a = s0.mem.get? a) ∧
      (∀ i, i < count → s.mem.get? (base + i) = some (0 : BitVec 8)) := by
  obtain ⟨s, hrun, hregs, hframe, hwin⟩ := loadFilledBytes_establishes base count 0 s0
  exact ⟨s, hrun, hregs, hframe, fun i hi => by simpa using hwin i hi⟩

/-- **`loadBytes` establishes `MemoryBytes`.** Every input byte reads back at its offset from `base`;
everything else and every register is untouched.

`loadBytes` is a `forIn'` loop (its body reads `bytes[index]` under the range membership proof). The
proof is only used to justify the safe index, and `bytes[index] = bytes[index]!` there, so the loop
equals a `forIn` loop with the proof-free `bytes[index]!` body, which `forIn_writeBytes_establishes`
discharges. -/
theorem loadBytes_establishes (base : Nat) (bytes : ByteArray) (s0 : State) :
    ∃ s, Runs (loadBytes base bytes) s0 s () ∧
      s.regs = s0.regs ∧
      (∀ a, a < base ∨ base + bytes.size ≤ a → s.mem.get? a = s0.mem.get? a) ∧
      (∀ i (h : i < bytes.size),
        s.mem.get? (base + i) = some (BitVec.ofNat 8 (bytes[i]'h).toNat)) := by
  -- the proof-free body used by the `forIn` establishment
  let g : Nat → PUnit → SailM (ForInStep PUnit) := fun index _ => do
    let _ ← writeByte (base + index) (BitVec.ofNat 8 (bytes[index]!).toNat)
    pure (ForInStep.yield PUnit.unit)
  have hrange : (List.range' [:bytes.size].start [:bytes.size].size [:bytes.size].step)
      = List.range' 0 bytes.size 1 := by simp [Std.Range.size]
  -- the loop of loadBytes (a `forIn'`) equals `forIn (range' 0 size 1) () g`
  have hA : (forIn' [:bytes.size] PUnit.unit (fun index _ r => do
        let _ ← writeByte (base + index) (BitVec.ofNat 8 bytes[index].toNat)
        pure (ForInStep.yield PUnit.unit)))
      = forIn (List.range' 0 bytes.size 1) PUnit.unit g := by
    rw [Std.Range.forIn'_eq_forIn'_range',
      List.forIn'_congr hrange rfl (g := fun a _ b => g a b) ?_]
    · exact forIn'_eq_forIn_ignore _ _ g
    · intro a hmem b
      have hlt : a < bytes.size := by have := List.mem_range'.mp hmem; omega
      simp only [g, getElem!_pos bytes a hlt]
  have hloop : loadBytes base bytes
      = (forIn (List.range' 0 bytes.size 1) PUnit.unit g >>= fun _ => pure PUnit.unit) := by
    show (forIn' [:bytes.size] PUnit.unit _ >>= fun _ => pure PUnit.unit) = _
    rw [hA]
  obtain ⟨s, hrun, hregs, hframe, hwin⟩ :=
    forIn_writeBytes_establishes (fun i => base + i) (fun i => BitVec.ofNat 8 (bytes[i]!).toNat)
      (List.range' 0 bytes.size 1) s0 (range'_map_add_nodup base bytes.size)
  have hrun' : Runs (loadBytes base bytes) s0 s () := by
    rw [hloop]
    exact Runs.bind (by simpa [g] using hrun)
      (by show (pure PUnit.unit : SailM Unit).run s = .ok () s; rfl)
  refine ⟨s, hrun', hregs, ?_, ?_⟩
  · intro a ha
    apply hframe
    simp only [List.mem_map, List.mem_range']
    rintro ⟨i, ⟨_, hi⟩, rfl⟩; omega
  · intro i h
    have := hwin i (by simp [List.mem_range']; omega)
    rwa [getElem!_pos bytes i h] at this

end BinaryFv.RiscV
