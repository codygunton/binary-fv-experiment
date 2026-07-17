import BinaryFv.Keccak.Reth.Proof.XorBlock.Steps.Control

/-!
# The 8-byte store's memory effect, and the rate-window frame
-/

namespace BinaryFv.Keccak.XorBlock
open BinaryFv.Binary
open BinaryFv.Keccak.SpecBridge
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open BinaryFv.Keccak
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Deliverable 4a: the 8-byte store's concrete memory effect

`writeBytes a v` (width 8) inserts the little-endian bytes of `v` at `a, a+1, …, a+7`.  `insertWord`
names that post-state; the two `get?` lemmas read the stored window and the disjoint complement. -/

/-- The byte-map after an 8-byte little-endian store of `v` at `a`. -/
def insertWord (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec (8 * 8)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((((((mem.insert a (v.extractLsb' 0 8)).insert (a + 1) (v.extractLsb' 8 8)).insert
    (a + 2) (v.extractLsb' 16 8)).insert (a + 3) (v.extractLsb' 24 8)).insert
    (a + 4) (v.extractLsb' 32 8)).insert (a + 5) (v.extractLsb' 40 8)).insert
    (a + 6) (v.extractLsb' 48 8)).insert (a + 7) (v.extractLsb' 56 8))

/-- The generated fixed-width store of a 64-bit word inserts its 8 little-endian bytes. -/
theorem writeBytes_word_run (s : State) (a : Nat) (v : BitVec (8 * 8)) :
    Runs (PreSail.writeBytes a v) s { s with mem := insertWord s.mem a v } true := by
  rw [writeBytes_eq]
  have hlist : (List.ofFn (fun i : Fin 8 => (a + i.val, v.extractLsb' (8 * i.val) 8)))
      = [(a, v.extractLsb' 0 8), (a + 1, v.extractLsb' 8 8), (a + 2, v.extractLsb' 16 8),
         (a + 3, v.extractLsb' 24 8), (a + 4, v.extractLsb' 32 8), (a + 5, v.extractLsb' 40 8),
         (a + 6, v.extractLsb' 48 8), (a + 7, v.extractLsb' 56 8)] := by
    simp [List.ofFn_succ, List.ofFn_zero]
  rw [hlist]
  simp only [List.forM]
  have hinner : Runs
      (do
        writeByte a (v.extractLsb' 0 8); writeByte (a + 1) (v.extractLsb' 8 8)
        writeByte (a + 2) (v.extractLsb' 16 8); writeByte (a + 3) (v.extractLsb' 24 8)
        writeByte (a + 4) (v.extractLsb' 32 8); writeByte (a + 5) (v.extractLsb' 40 8)
        writeByte (a + 6) (v.extractLsb' 48 8); writeByte (a + 7) (v.extractLsb' 56 8)
        pure PUnit.unit)
      s { s with mem := insertWord s.mem a v } PUnit.unit := by
    refine Runs.bind (writeByte_run s a _) ?_
    refine Runs.bind (writeByte_run _ (a + 1) _) ?_
    refine Runs.bind (writeByte_run _ (a + 2) _) ?_
    refine Runs.bind (writeByte_run _ (a + 3) _) ?_
    refine Runs.bind (writeByte_run _ (a + 4) _) ?_
    refine Runs.bind (writeByte_run _ (a + 5) _) ?_
    refine Runs.bind (writeByte_run _ (a + 6) _) ?_
    refine Runs.bind (writeByte_run _ (a + 7) _) ?_
    rfl
  exact Runs.bind hinner rfl

/-- The `i`-th little-endian byte of a 64-bit word. -/
theorem leBytes_extractLsb (v : BitVec (8 * 8)) (i : Nat) (hi : i < 8) :
    (leBytes 8 v)[i]'(by rw [leBytes_length]; exact hi) = v.extractLsb' (8 * i) 8 := by
  simp only [leBytes, List.getElem_ofFn]

/-- Reading a byte inside the stored 8-byte window. -/
theorem insertWord_get_in (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec (8 * 8))
    (i : Nat) (hi : i < 8) :
    (insertWord mem a v).get? (a + i) = some (v.extractLsb' (8 * i) 8) := by
  unfold insertWord
  match i, hi with
  | 0, _ =>
    rw [getInsertNe _ (a + 7) (a + 0) _ (by omega), getInsertNe _ (a + 6) (a + 0) _ (by omega), getInsertNe _ (a + 5) (a + 0) _ (by omega), getInsertNe _ (a + 4) (a + 0) _ (by omega), getInsertNe _ (a + 3) (a + 0) _ (by omega), getInsertNe _ (a + 2) (a + 0) _ (by omega), getInsertNe _ (a + 1) (a + 0) _ (by omega)]
    exact getInsertEq _ _ _
  | 1, _ =>
    rw [getInsertNe _ (a + 7) (a + 1) _ (by omega), getInsertNe _ (a + 6) (a + 1) _ (by omega), getInsertNe _ (a + 5) (a + 1) _ (by omega), getInsertNe _ (a + 4) (a + 1) _ (by omega), getInsertNe _ (a + 3) (a + 1) _ (by omega), getInsertNe _ (a + 2) (a + 1) _ (by omega)]
    exact getInsertEq _ _ _
  | 2, _ =>
    rw [getInsertNe _ (a + 7) (a + 2) _ (by omega), getInsertNe _ (a + 6) (a + 2) _ (by omega), getInsertNe _ (a + 5) (a + 2) _ (by omega), getInsertNe _ (a + 4) (a + 2) _ (by omega), getInsertNe _ (a + 3) (a + 2) _ (by omega)]
    exact getInsertEq _ _ _
  | 3, _ =>
    rw [getInsertNe _ (a + 7) (a + 3) _ (by omega), getInsertNe _ (a + 6) (a + 3) _ (by omega), getInsertNe _ (a + 5) (a + 3) _ (by omega), getInsertNe _ (a + 4) (a + 3) _ (by omega)]
    exact getInsertEq _ _ _
  | 4, _ =>
    rw [getInsertNe _ (a + 7) (a + 4) _ (by omega), getInsertNe _ (a + 6) (a + 4) _ (by omega), getInsertNe _ (a + 5) (a + 4) _ (by omega)]
    exact getInsertEq _ _ _
  | 5, _ =>
    rw [getInsertNe _ (a + 7) (a + 5) _ (by omega), getInsertNe _ (a + 6) (a + 5) _ (by omega)]
    exact getInsertEq _ _ _
  | 6, _ =>
    rw [getInsertNe _ (a + 7) (a + 6) _ (by omega)]
    exact getInsertEq _ _ _
  | 7, _ =>
    exact getInsertEq _ _ _

/-- Reading a byte outside the stored 8-byte window is unchanged. -/
theorem insertWord_get_out (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec (8 * 8))
    (b : Nat) (h : ∀ i : Nat, i < 8 → b ≠ a + i) :
    (insertWord mem a v).get? b = mem.get? b := by
  unfold insertWord
  rw [getInsertNe _ (a + 7) b _ (Ne.symm (h 7 (by omega))),
    getInsertNe _ (a + 6) b _ (Ne.symm (h 6 (by omega))),
    getInsertNe _ (a + 5) b _ (Ne.symm (h 5 (by omega))),
    getInsertNe _ (a + 4) b _ (Ne.symm (h 4 (by omega))),
    getInsertNe _ (a + 3) b _ (Ne.symm (h 3 (by omega))),
    getInsertNe _ (a + 2) b _ (Ne.symm (h 2 (by omega))),
    getInsertNe _ (a + 1) b _ (Ne.symm (h 1 (by omega))),
    getInsertNe _ a b _ (Ne.symm (h 0 (by omega)))]

/-- Storing an 8-byte word at addresses the image does not back preserves `matchesMemory`. -/
theorem matchesMemory_insertWord (image : ProgramImage) (mem : Std.ExtHashMap Nat (BitVec 8))
    (addr : Nat) (data : BitVec (8 * 8)) (hm : image.matchesMemory mem)
    (hnone : ∀ i : Nat, i < 8 → image.readByte? (addr + i) = none) :
    image.matchesMemory (insertWord mem addr data) := by
  intro a byte ha
  by_cases hin : addr ≤ a ∧ a < addr + 8
  · obtain ⟨h1, h2⟩ := hin
    have hn : image.readByte? a = none := by
      have := hnone (a - addr) (by omega)
      rwa [show addr + (a - addr) = a by omega] at this
    rw [hn] at ha; simp at ha
  · rw [insertWord_get_out mem addr data a (fun i hi => by omega)]; exact hm a byte ha

/-! ### Deliverable 4a (cont.): the rate-window memory frame

`xor_block` writes exactly the 136-byte rate window `[state0, state0+136)`: every store lands at
`state0 + 8k + i` with `k < 17` and `i < 8`.  We therefore track the *exact memory delta* relative to
a fixed reference state with the same `MemFramed` idiom the `memcpy` / `memset` / `copy_from_slice`
capstones export (`BinaryFv.Keccak.HelperFraming`), instantiated at `dst := state0`, `n := 136`.

The frame is the general conclusion: the capacity lanes (`17 ≤ m < 25`), the input block and the code
image all sit *outside* the rate window, so their preservation is derived from it rather than tracked
as independent ad-hoc conclusions.  The three lemmas below are the `xor_block` instances of
`HelperFraming`'s `frame_insert_step` / `MemFramed.mem_unchanged_outside` reading idiom, plus the
`toNat` plumbing for the concrete width `136`. -/

/-- The rate window is 136 bytes wide. -/
theorem rateWidth_toNat : (BitVec.ofNat 64 136).toNat = 136 := by decide

/-- Read the rate-window frame at an address outside `[state0, state0+136)`. -/
theorem memFramed_rate_apply {state0 : BitVec 64} {sref s : State}
    (h : MemFramed state0 (BitVec.ofNat 64 136) sref s) (addr : Nat)
    (haddr : ∀ j : Nat, j < 136 → addr ≠ (state0 + BitVec.ofNat 64 j).toNat) :
    s.mem.get? addr = sref.mem.get? addr :=
  h addr (fun j hj => haddr j (by rw [rateWidth_toNat] at hj; exact hj))

/-- Package a pointwise outside-the-rate-window agreement as a `MemFramed`. -/
theorem memFramed_rate_intro {state0 : BitVec 64} {sref s : State}
    (h : ∀ addr : Nat, (∀ j : Nat, j < 136 → addr ≠ (state0 + BitVec.ofNat 64 j).toNat) →
      s.mem.get? addr = sref.mem.get? addr) :
    MemFramed state0 (BitVec.ofNat 64 136) sref s :=
  fun addr haddr => h addr (fun j hj => haddr j (by rw [rateWidth_toNat]; exact hj))

/-- The lane store at `state0 + 8k` (`k < 17`) lands inside the rate window, so it never disturbs the
already-framed complement.  This is the `xor_block` (8 bytes at a time) analogue of
`HelperFraming.frame_insert_step`, and is the per-iteration step the loop invariant re-establishes. -/
theorem frame_rate_store {state0 : BitVec 64} {sref : State}
    {mem : Std.ExtHashMap Nat (BitVec 8)} {k : Nat} {v : BitVec (8 * 8)}
    (hstateFits : state0.toNat + 200 ≤ 2 ^ 64) (hk : k < 17)
    (hframe : ∀ addr : Nat, (∀ j : Nat, j < 136 → addr ≠ (state0 + BitVec.ofNat 64 j).toNat) →
      mem.get? addr = sref.mem.get? addr) :
    ∀ addr : Nat, (∀ j : Nat, j < 136 → addr ≠ (state0 + BitVec.ofNat 64 j).toNat) →
      (insertWord mem (state0 + BitVec.ofNat 64 (8 * k)).toNat v).get? addr
        = sref.mem.get? addr := by
  intro addr haddr
  rw [insertWord_get_out _ _ _ _ (fun i hi => by
    have h' := haddr (8 * k + i) (by omega)
    rw [dstAddr_toNat state0 (8 * k + i) (by omega)] at h'
    rw [dstAddr_toNat state0 (8 * k) (by omega)]
    omega)]
  exact hframe addr haddr

/-- Code-image preservation *derived from the frame*: the image backs no byte of the 200-byte state
region (`hstateImg`), hence none of the rate window either, and every address outside that window is
left untouched by a framed run. -/
theorem matchesMemory_of_rate_frame {state0 : BitVec 64} {sref s : State} {image : ProgramImage}
    (hframe : MemFramed state0 (BitVec.ofNat 64 136) sref s)
    (hstateImg : ∀ j : Nat, j < 200 → image.readByte? (state0 + BitVec.ofNat 64 j).toNat = none)
    (hm : image.matchesMemory sref.mem) :
    image.matchesMemory s.mem := by
  intro addr byte hread
  by_cases hin : ∃ j : Nat, j < 136 ∧ addr = (state0 + BitVec.ofNat 64 j).toNat
  · obtain ⟨j, hj, rfl⟩ := hin
    rw [hstateImg j (by omega)] at hread
    exact absurd hread (by simp)
  · rw [memFramed_rate_apply hframe addr (fun j hj heq => hin ⟨j, hj, heq⟩)]
    exact hm addr byte hread

end BinaryFv.Keccak.XorBlock
