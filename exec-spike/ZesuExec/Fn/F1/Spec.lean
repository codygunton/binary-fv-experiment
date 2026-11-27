import ZesuExec.Fn.Assumed
import ZesuExec.Fn.Stage

/-!
# F1 `array_list.Aligned([32]u8,null).ensureTotalCapacity` (`0x800cb40c`, 107 instructions)

Transcribes `keysEnsureCapacityDomain`, `keysEnsureCapacityAllows` and
`keysEnsureCapacityScratchAfter` of zesislar's `ZesuSsz/Contracts/KeysEnsureCapacityContract.v`
(and `ArrayListContract.v`). `a0` = list header `{items.ptr, items.len, capacity}`, `a1` =
allocator object `{ctx, vtable}`, `a2` = requested capacity. The result code returns in `a0`:
0 (success) or 2 (OutOfMemory).
-/

namespace ZesuExec.Fn.F1
open ZesuExec

def entry : Nat := 0x800cb40c
def bound : Nat := 197

def elemBytes : Nat := 32
def vtable : Nat := 0x801136d8

/-- Zig's growth rule `arrayListGrownCapacity`. -/
def grown (req : Nat) : Nat := req + req / 2 + 2

/-- The 64-bit word at `a` (`0` if it cannot be loaded). -/
def wordAt (m : Machine) (a : Word) : Word := (m.load a 8).getD 0

/-- The list header at `hdr` holds `p`, `n`, `c`. -/
def HeaderIs (m : Machine) (hdr p n c : Word) : Prop :=
  m.load hdr 8 = some p ∧ m.load (hdr + 8) 8 = some n ∧ m.load (hdr + 16) 8 = some c

/-- Little-endian bytes of a word. -/
def wordBytes (v : Word) : List Byte := (List.range 8).map fun j => v.extractLsb' (8 * j) 8

/-- The memcpy scratch word is unchanged. -/
def ScratchSame (m m' : Machine) : Prop :=
  ∀ j < 8, m'.mem (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j) =
    m.mem (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j)

/-- Two ranges do not meet. -/
def Apart (a : Word) (n : Nat) (b : Word) (k : Nat) : Prop :=
  a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat

section
variable (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (items : List Byte)

/-- Entry: `keysEnsureCapacityDomain` plus the owned resources of `keysEnsureCapacityEntry`. -/
def Pre (m : Machine) : Prop :=
  let hdr := m.reg 10; let ao := m.reg 11; let req := m.reg 12; let sp := m.reg 2
  let p := wordAt m hdr; let n := wordAt m (hdr + 8); let c := wordAt m (hdr + 16)
  RodataLoaded zesuImage m ∧ StackOk m 128 ∧ RetAligned m ∧
  -- list header and list state (`arrayListWellFormed keysElementBytes`)
  RamRange hdr 24 ∧ hdr.toNat % 8 = 0 ∧ HeaderIs m hdr p n c ∧
  n.toNat ≤ c.toNat ∧ items.length = n.toNat * elemBytes ∧ 0 < p.toNat ∧
  (0 < c.toNat → RamRange p (c.toNat * elemBytes) ∧ (p, c.toNat * elemBytes) ∈ L) ∧
  BytesAt m p items ∧
  -- allocator object `{ctx, alt_fl_alloc.vtable}`
  RamRange ao 16 ∧ ao.toNat % 8 = 0 ∧ (m.load ao 8).isSome ∧
  m.load (ao + 8) 8 = some (BitVec.ofNat 64 vtable) ∧
  req.toNat < 2 ^ 32 ∧
  -- the memcpy scratch word and the allocator state
  Present m (BitVec.ofNat 64 Layout.extraParams) 8 ∧ A.Heap L m ∧
  -- ownership: header, allocator object, stack, scratch and buffer are apart and avoid `Priv L`
  Apart hdr 24 ao 16 ∧ Apart hdr 24 (sp - 128) 128 ∧ Apart ao 16 (sp - 128) 128 ∧
  Apart hdr 24 (BitVec.ofNat 64 Layout.extraParams) 8 ∧
  Apart ao 16 (BitVec.ofNat 64 Layout.extraParams) 8 ∧
  Apart (sp - 128) 128 (BitVec.ofNat 64 Layout.extraParams) 8 ∧
  (0 < c.toNat → Apart p (c.toNat * elemBytes) hdr 24 ∧ Apart p (c.toNat * elemBytes) ao 16 ∧
    Apart p (c.toNat * elemBytes) (sp - 128) 128 ∧
    Apart p (c.toNat * elemBytes) (BitVec.ofNat 64 Layout.extraParams) 8) ∧
  (∀ a, InRange hdr 24 a ∨ InRange ao 16 a ∨ InRange (sp - 128) 128 a ∨
    InRange (BitVec.ofNat 64 Layout.extraParams) 8 a → ¬ A.Priv L a)

/-- Exit: `keysEnsureCapacityAllows`, `keysEnsureCapacityScratchAfter`, the allocator state
and the frame. -/
def Post (m m' : Machine) : Prop :=
  let hdr := m.reg 10; let req := m.reg 12; let sp := m.reg 2
  let p := wordAt m hdr; let n := wordAt m (hdr + 8); let c := wordAt m (hdr + 16)
  let scratch := BitVec.ofNat 64 Layout.extraParams
  Returns m m' ∧
  SameOutside (fun a => InRange hdr 24 a ∨ InRange (sp - 128) 128 a ∨ InRange scratch 8 a ∨
    A.Priv L a ∨ (0 < c.toNat ∧ InRange p (c.toNat * elemBytes) a)) m m' ∧
  (if req.toNat ≤ c.toNat then
     m'.reg 10 = 0 ∧ HeaderIs m' hdr p n c ∧ A.Heap L m' ∧ ScratchSame m m'
   else
     (m'.reg 10 = 0 ∧ ∃ p', HeaderIs m' hdr p' n (BitVec.ofNat 64 (grown req.toNat)) ∧ 0 < p'.toNat ∧
        RamRange p' (grown req.toNat * elemBytes) ∧ BytesAt m' p' items ∧
        A.Heap ((if 0 < c.toNat then L.erase (p, c.toNat * elemBytes) else L) ++
          [(p', grown req.toNat * elemBytes)]) m' ∧
        BytesAt m' scratch (wordBytes (BitVec.ofNat 64 (n.toNat * elemBytes)))) ∨
     (m'.reg 10 = 2 ∧ HeaderIs m' hdr p n c ∧ A.Heap L m' ∧ ScratchSame m m'))

end

open ZesuExec.Fn

/-! ## Non-vacuity -/

/-- The witness's own bytes: stack below `sp = 0xa0001000`, header at `0xa0002000`
(items.ptr 1, length 0, capacity 0), allocator object at `0xa0002020`, the scratch word. -/
def nvByte (a : Nat) : Option Nat :=
  if 0xa0000f80 ≤ a ∧ a < 0xa0001000 then some 0
  else if a = 0xa0002000 then some 1
  else if 0xa0002000 < a ∧ a < 0xa0002028 then some 0
  else if 0xa0002028 ≤ a ∧ a < 0xa0002030 then some ((vtable / 256 ^ (a - 0xa0002028)) % 256)
  else if Layout.extraParams ≤ a ∧ a < Layout.extraParams + 8 then some 0
  else none

def nvMachine (m0 : Machine) : Machine where
  regs := fun i => if i.val = 2 then 0xa0001000 else if i.val = 1 then 0x80000000
    else if i.val = 10 then 0xa0002000 else if i.val = 11 then 0xa0002020 else if i.val = 12 then 1 else 0
  pc := BitVec.ofNat 64 entry
  mem := fun a => match zesuImage.rodataByte? a.toNat with
    | some b => some (BitVec.ofNat 8 b)
    | none => match nvByte a.toNat with
      | some b => some (BitVec.ofNat 8 b)
      | none => m0.mem a

def bot : Machine := ⟨fun _ => 0, 0, fun _ => none⟩

theorem nv_mem (m0 : Machine) (a : Word) (h : (nvByte a.toNat).isSome = true) :
    (nvMachine m0).mem a = (nvMachine bot).mem a := by
  simp only [nvMachine]
  split
  · rfl
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h; simp [hb]

theorem nv_load (m0 : Machine) (a : Word) (n : Nat)
    (h : ∀ t < n, (nvByte (a + BitVec.ofNat 64 t).toNat).isSome = true) :
    (nvMachine m0).load a n = (nvMachine bot).load a n :=
  load_congr fun t ht => nv_mem m0 _ (h t ht)

example (m0 : Machine) : (nvMachine m0).load (BitVec.ofNat 64 0xa0002000) 8 = some 1 := by
  rw [nv_load m0 _ 8 (by decide)]; decide

theorem nv_present (m0 : Machine) (a : Word) (n : Nat)
    (h : ∀ t < n, (nvByte (a + BitVec.ofNat 64 t).toNat).isSome = true) :
    ∀ t < n, ((nvMachine m0).mem (a + BitVec.ofNat 64 t)).isSome = true := by
  intro t ht
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h t ht)
  show (match zesuImage.rodataByte? (a + BitVec.ofNat 64 t).toNat with
    | some b => some (BitVec.ofNat 8 b)
    | none => match nvByte (a + BitVec.ofNat 64 t).toNat with
      | some b => some (BitVec.ofNat 8 b)
      | none => m0.mem (a + BitVec.ofNat 64 t)).isSome = true
  split
  · rfl
  · rw [hb]; rfl

/-- `Pre` is satisfiable for any allocator whose heap predicate holds of some machine with an
empty block list and whose memory lies away from the witness's bytes. -/
theorem pre_nonvacuous (A : AllocAssumptions zesuImage) (m0 : Machine) (h0 : A.Heap [] m0)
    (hP : ∀ a, A.Priv [] a → 0xa0003000 ≤ a.toNat ∧
      ¬ (Layout.extraParams ≤ a.toNat ∧ a.toNat < Layout.extraParams + 8)) :
    ∃ m, Pre A [] [] m := by
  have r2 : (nvMachine m0).reg 2 = 0xa0001000 := rfl
  have r10 : (nvMachine m0).reg 10 = 0xa0002000 := rfl
  have r11 : (nvMachine m0).reg 11 = 0xa0002020 := rfl
  have r12 : (nvMachine m0).reg 12 = 1 := rfl
  have hp : (nvMachine m0).load 0xa0002000 8 = some 1 := by rw [nv_load m0 _ 8 (by decide)]; decide
  have hn : (nvMachine m0).load (0xa0002000 + 8) 8 = some 0 := by rw [nv_load m0 _ 8 (by decide)]; decide
  have hc : (nvMachine m0).load (0xa0002000 + 16) 8 = some 0 := by rw [nv_load m0 _ 8 (by decide)]; decide
  have hctx : (nvMachine m0).load 0xa0002020 8 = some 0 := by rw [nv_load m0 _ 8 (by decide)]; decide
  have hvt : (nvMachine m0).load (0xa0002020 + 8) 8 = some (BitVec.ofNat 64 vtable) := by
    rw [nv_load m0 _ 8 (by decide)]; decide
  have wp : wordAt (nvMachine m0) 0xa0002000 = 1 := by unfold wordAt; rw [hp]; rfl
  have wn : wordAt (nvMachine m0) (0xa0002000 + 8) = 0 := by unfold wordAt; rw [hn]; rfl
  have wc : wordAt (nvMachine m0) (0xa0002000 + 16) = 0 := by unfold wordAt; rw [hc]; rfl
  refine ⟨nvMachine m0, ?_⟩
  simp only [Pre, r2, r10, r11, r12, wp, wn, wc]
  have r1 : (nvMachine m0).reg 1 = 0x80000000 := rfl
  refine ⟨?_, ⟨by rw [r2]; decide, by rw [r2]; decide, by rw [r2]; decide, ?_⟩,
    by unfold RetAligned; rw [r1]; decide,
    by unfold RamRange; decide, by decide,
    ⟨hp, hn, hc⟩, by decide, by decide, by decide, fun h => absurd h (by decide),
    fun i h => by simp at h, by unfold RamRange; decide,
    by decide, by rw [hctx]; rfl, hvt, by decide, ?_, ?_, by unfold Apart; decide, by unfold Apart; decide,
    by unfold Apart; decide, by unfold Apart; decide, by unfold Apart; decide, by unfold Apart; decide,
    fun h => absurd h (by decide), ?_⟩
  · intro a b h
    have ha : a < 2 ^ 64 := by
      have := zesu_rodata_range h; unfold Layout.rodataHi at this; omega
    simp [nvMachine, Nat.mod_eq_of_lt ha, h]
  · rw [r2]; exact nv_present m0 _ 128 (by decide)
  · exact nv_present m0 _ 8 (by decide)
  · refine A.heap_frame [] m0 _ h0 fun a ha => ?_
    obtain ⟨h1, h2⟩ := hP a ha
    have hro : zesuImage.rodataByte? a.toNat = none := by
      cases hq : zesuImage.rodataByte? a.toNat with
      | none => rfl
      | some b => have := zesu_rodata_range hq; unfold Layout.rodataHi at this; omega
    have hnv : nvByte a.toNat = none := by
      simp only [Layout.extraParams] at h2
      simp only [nvByte, Layout.extraParams]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg h2]
    simp [nvMachine, hro, hnv]
  · intro a h ha
    obtain ⟨h1, h2⟩ := hP a ha
    have e1 : ((0xa0001000 : Word) - 128).toNat = 0xa0000f80 := by decide
    have e2 : (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams := by decide
    have e3 : (0xa0002000 : Word).toNat = 0xa0002000 := by decide
    have e4 : (0xa0002020 : Word).toNat = 0xa0002020 := by decide
    simp only [InRange, e1, e2, e3, e4] at h
    simp only [Layout.extraParams] at h h2
    omega

end ZesuExec.Fn.F1
