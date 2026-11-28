import ZesuExec.Fn.Alloc.Contract

/-!
# `array_list.Aligned(T,null).toOwnedSlice`: the shared statement, and F4

Transcribes `toOwnedSliceDomain`, `toOwnedSliceAllows` and `toOwnedSliceScratchAfter` of
zesislar's `ZesuSsz/Contracts/ArrayListContract.v` with the call shape of
`KeysToOwnedSliceCallSpec2.v` / `EntriesToOwnedSliceCallSpec2.v`. `a0` = 24-byte result
`{ptr, len, err : u16}`, `a1` = list header `{items.ptr, items.len, capacity}`, `a2` = allocator
object `{ctx, vtable}`. `ToOwned.Pre eb` and `ToOwned.Post eb empty` are generic in the element
size `eb` and the empty-list pointer `empty`; F4 (`[32]u8`) takes 32 and 1, F5
(`input.AccessListEntry`) 40 and 8.

F4 is `array_list.Aligned([32]u8,null).toOwnedSlice` (`0x800d677c`, 121 instructions).
-/

namespace ZesuExec.Fn.ToOwned
open ZesuExec

/-- `alt_fl_alloc`'s vtable `{alloc, resize, remap, free}` in rodata. -/
def vtable : Nat := 0x801136d8

/-- The 64-bit word at `a` (`0` if it cannot be loaded). -/
def wordAt (m : Machine) (a : Word) : Word := (m.load a 8).getD 0

/-- The list header at `a1`: `items.ptr`, `items.len`, `capacity`. -/
def listPtr (m : Machine) : Word := wordAt m (m.reg 11)
def listLen (m : Machine) : Word := wordAt m (m.reg 11 + 8)
def listCap (m : Machine) : Word := wordAt m (m.reg 11 + 16)

/-- The ZisK memcpy scratch word `ziskExtraParamsAddress`. -/
def scratch : Word := BitVec.ofNat 64 Layout.extraParams

/-- The list header at `hdr` holds `p`, `n`, `c` (`arrayListHeaderBytes`). -/
def HeaderIs (m : Machine) (hdr p n c : Word) : Prop :=
  m.load hdr 8 = some p ∧ m.load (hdr + 8) 8 = some n ∧ m.load (hdr + 16) 8 = some c

/-- Little-endian bytes of a word (`word64Bytes`). -/
def wordBytes (v : Word) : List Byte := (List.range 8).map fun j => v.extractLsb' (8 * j) 8

/-- The memcpy scratch word is unchanged. -/
def ScratchSame (m m' : Machine) : Prop :=
  ∀ j < 8, m'.mem (scratch + BitVec.ofNat 64 j) = m.mem (scratch + BitVec.ofNat 64 j)

/-- Two ranges do not meet. -/
def Apart (a : Word) (n : Nat) (b : Word) (k : Nat) : Prop :=
  a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat

/-- Bytes `[lo, hi)` at `a` are as in `m`. -/
def SameBytes (m m' : Machine) (a : Word) (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j < hi → m'.mem (a + BitVec.ofNat 64 j) = m.mem (a + BitVec.ofNat 64 j)

/-- `arrayListResultImage before ptr len`: `ptr`, `len`, error code 0 (2 bytes), padding kept. -/
def ResultImage (m m' : Machine) (res ptr len : Word) : Prop :=
  m'.load res 8 = some ptr ∧ m'.load (res + 8) 8 = some len ∧ m'.load (res + 16) 2 = some 0 ∧
    SameBytes m m' res 18 24

/-- `arrayListErrorImage before code`: only the 2-byte error code changes. -/
def ErrorImage (m m' : Machine) (res code : Word) : Prop :=
  SameBytes m m' res 0 16 ∧ m'.load (res + 16) 2 = some code ∧ SameBytes m m' res 18 24

section
variable (eb : Nat) (A : AllocContract zesuImage) (L : List (Word × Nat)) (items : List Byte)

/-- Entry: `toOwnedSliceDomain eb` plus the owned resources of `toOwnedSliceEntry`. -/
def Pre (m : Machine) : Prop :=
  let res := m.reg 10; let hdr := m.reg 11; let ao := m.reg 12; let sp := m.reg 2
  let p := listPtr m; let n := listLen m; let c := listCap m
  RodataLoaded zesuImage m ∧ StackOk m 112 ∧ RetAligned m ∧
  -- result (`resultBefore`, 24 bytes)
  RamRange res 24 ∧ res.toNat % 8 = 0 ∧ Present m res 24 ∧
  -- list header and list state (`arrayListWellFormed eb`)
  RamRange hdr 24 ∧ hdr.toNat % 8 = 0 ∧ HeaderIs m hdr p n c ∧
  n.toNat ≤ c.toNat ∧ items.length = n.toNat * eb ∧ 0 < p.toNat ∧
  (0 < c.toNat → RamRange p (c.toNat * eb) ∧ (p, c.toNat * eb) ∈ L) ∧
  BytesAt m p items ∧
  -- allocator object `{ctx, alt_fl_alloc.vtable}`
  RamRange ao 16 ∧ ao.toNat % 8 = 0 ∧ (m.load ao 8).isSome ∧
  m.load (ao + 8) 8 = some (BitVec.ofNat 64 vtable) ∧
  -- the memcpy scratch word and the allocator state
  Present m scratch 8 ∧ A.Heap L m ∧
  -- ownership: result, header, allocator object, stack, scratch and buffer are apart and
  -- avoid `Priv L`
  Apart res 24 hdr 24 ∧ Apart res 24 ao 16 ∧ Apart res 24 (sp - 112) 112 ∧ Apart res 24 scratch 8 ∧
  Apart hdr 24 ao 16 ∧ Apart hdr 24 (sp - 112) 112 ∧ Apart hdr 24 scratch 8 ∧
  Apart ao 16 (sp - 112) 112 ∧ Apart ao 16 scratch 8 ∧ Apart (sp - 112) 112 scratch 8 ∧
  (0 < c.toNat → Apart p (c.toNat * eb) res 24 ∧ Apart p (c.toNat * eb) hdr 24 ∧
    Apart p (c.toNat * eb) ao 16 ∧ Apart p (c.toNat * eb) (sp - 112) 112 ∧
    Apart p (c.toNat * eb) scratch 8) ∧
  (∀ a, InRange res 24 a ∨ InRange hdr 24 a ∨ InRange ao 16 a ∨ InRange (sp - 112) 112 a ∨
    InRange scratch 8 a → ¬ A.Priv L a)

/-- Exit: `toOwnedSliceAllows eb empty`, `toOwnedSliceScratchAfter eb`, the allocator state and
the frame. -/
def Post (empty : Word) (m m' : Machine) : Prop :=
  let res := m.reg 10; let hdr := m.reg 11; let sp := m.reg 2
  let p := listPtr m; let n := listLen m; let c := listCap m
  Returns m m' ∧
  SameOutside (fun a => InRange res 24 a ∨ InRange hdr 24 a ∨ InRange (sp - 112) 112 a ∨
    InRange scratch 8 a ∨ A.Priv L a ∨ (0 < c.toNat ∧ InRange p (c.toNat * eb) a)) m m' ∧
  (if n.toNat = 0 then
     -- free the buffer (if any), the list becomes `arrayListEmpty empty`, the slice is `{p, 0}`
     HeaderIs m' hdr empty 0 0 ∧ ResultImage m m' res p 0 ∧
     A.Heap (if 0 < c.toNat then L.erase (p, c.toNat * eb) else L) m' ∧ ScratchSame m m'
   else
     -- success: a new block of `n * eb` bytes holds the items; the old buffer is freed; the
     -- header keeps the pointer with length and capacity 0
     (∃ p', 0 < p'.toNat ∧ RamRange p' (n.toNat * eb) ∧ BytesAt m' p' items ∧
        HeaderIs m' hdr p 0 0 ∧ ResultImage m m' res p' n ∧
        A.Heap (L.erase (p, c.toNat * eb) ++ [(p', n.toNat * eb)]) m' ∧
        BytesAt m' scratch (wordBytes (BitVec.ofNat 64 (n.toNat * eb)))) ∨
     -- OutOfMemory: error code 2, the list unchanged
     (HeaderIs m' hdr p n c ∧ ErrorImage m m' res 2 ∧ A.Heap L m' ∧ ScratchSame m m'))

end

end ZesuExec.Fn.ToOwned

namespace ZesuExec.Fn.F4
open ZesuExec

def entry : Nat := 0x800d677c
def bound : Nat := 194

/-- `keysElementBytes`, `keysEmptyPointer`. -/
def elemBytes : Nat := 32
def emptyPtr : Word := BitVec.ofNat 64 1

abbrev Pre (A : AllocContract zesuImage) (L : List (Word × Nat)) (items : List Byte) :=
  ToOwned.Pre elemBytes A L items
abbrev Post (A : AllocContract zesuImage) (L : List (Word × Nat)) (items : List Byte) :=
  ToOwned.Post elemBytes A L items emptyPtr

end ZesuExec.Fn.F4
