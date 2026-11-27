import ZesuExec.Fn.Assumed

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
     m'.reg 10 = 0 ∧ HeaderIs m' hdr p n c ∧ A.Heap L m' ∧ BytesAt m' scratch (wordBytes (wordAt m scratch))
   else
     (m'.reg 10 = 0 ∧ ∃ p', HeaderIs m' hdr p' n (BitVec.ofNat 64 (grown req.toNat)) ∧ 0 < p'.toNat ∧
        RamRange p' (grown req.toNat * elemBytes) ∧ BytesAt m' p' items ∧
        A.Heap ((if 0 < c.toNat then L.erase (p, c.toNat * elemBytes) else L) ++
          [(p', grown req.toNat * elemBytes)]) m' ∧
        BytesAt m' scratch (wordBytes (BitVec.ofNat 64 (n.toNat * elemBytes)))) ∨
     (m'.reg 10 = 2 ∧ HeaderIs m' hdr p n c ∧ A.Heap L m' ∧
        BytesAt m' scratch (wordBytes (wordAt m scratch))))

end

end ZesuExec.Fn.F1
