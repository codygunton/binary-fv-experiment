import ZesuExec.Fn.TX.Spec

/-!
# TX regions and cut states (programme plan S6 steps 2-3)

Cut points: the map's 15 (entry, loop heads `0x800000c4` and `0x8000018c`, the 12 call return
sites) and two store sites, `0x80000230` (a key into the keys buffer) and `0x80000460` (an entry
into the entries buffer). The two store sites are cut points because the executor stores only at
constant offsets of a region: at those pcs the target address is in `a0`, and the cut's state
makes it the base of a 32- or 40-byte region (`slotR`); without them the runs from
`0x800001f8`, `0x8000025c`, `0x80000340` and `0x8000042c` would store at `ptr + 32·len` /
`ptr + 40·len`, which `storeSym` refuses.

Regions, the same indices at every cut (`OPEN/TX/CUTS.md`; deviation from its per-segment lists:
every cut carries the frame, the result, `rest`, the allocator object and the input, so register
and region indices agree across cuts; the store-site cuts add the slot):

| index | region | size | base (from the entry machine `g.m` unless noted) |
|---|---|---|---|
| 0 | frame `[S-576, S)` | 576 | `sp` at entry minus 576 |
| 1 | result | 24 | `a0` at entry |
| 2 | `rest` | 16 | `a2` at entry |
| 3 | allocator object | 16 | `a1` at entry |
| 4 | input | unknown (obligations) | the input pointer in `rest` at entry |
| 5 | slot (store-site cuts) | 32 / 40 | `a0` at the cut |

Registers at a cut: `sp = ptr 0 0` and `s0 = ptr 0 576` (after the prologue), `s1 = ptr 1 0`,
`s2 = ptr 3 0`; at the entry `sp = ptr 0 576`, `a0`, `a1`, `a2` the result, allocator object and
`rest`; at `0x80000068` `s6 = ptr 2 0`; at the store sites `a0 = ptr 5 0`. Every other register is
its own variable `var i`. `known` facts on initial memory: the allocator object's vtable word is
`alt_fl_alloc.vtable` (`0x801136d8`, rodata), so the vtable loads are rodata reads and the three
allocator calls direct calls; at `0x80000340` and `0x80000400` the frame's spill of that word
(`S-0x220`) holds it too; at `0x8000010c` and `0x800001a0` the payload pointer in the
`decodeItem` outcome (`S-0x180`, `S-0x100`) is `ptr 4 0 + var 40` (`var 40` = that word minus the
input pointer), so the address and key copies are input reads at a symbolic offset.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym

def frameBytes : Nat := 576

def frameR : Region := ⟨some frameBytes, 16, true⟩
def resR : Region := ⟨some 24, 1, true⟩
def restR : Region := ⟨some 16, 1, true⟩
def aoR : Region := ⟨some 16, 1, false⟩
def inR : Region := ⟨none, 1, false⟩
def slotR (n : Nat) : Region := ⟨some n, 1, true⟩

def baseRegions : List Region := [frameR, resR, restR, aoR, inR]

/-- The allocator object's vtable word. -/
def vtableKnown : Write := ⟨3, 8, 8, .lit vtable⟩

/-- Registers at every cut after the prologue. -/
def ovBody (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 0) else if i = 8 then some (.ptr 0 576)
  else if i = 9 then some (.ptr 1 0) else if i = 18 then some (.ptr 3 0) else none

def ovEntry (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 576) else if i = 10 then some (.ptr 1 0)
  else if i = 11 then some (.ptr 3 0) else if i = 12 then some (.ptr 2 0) else none

def ovRest (i : Nat) : Option Sym := if i = 22 then some (.ptr 2 0) else ovBody i

def ovSlot (i : Nat) : Option Sym := if i = 10 then some (.ptr 5 0) else ovBody i

/-- Frame offset of a slot `S - k`. -/
def fo (k : Nat) : Nat := frameBytes - k

/-- The payload pointer of the `decodeItem` outcome at `S - k` is the input at offset `var 40`. -/
def payloadKnown (k : Nat) : Write := ⟨0, fo k, 8, .bin .add (.ptr 4 0) (.var 40)⟩

/-- The frame spill of the vtable word (`S-0x220`). -/
def vtableSpill : Write := ⟨0, fo 0x220, 8, .lit vtable⟩

/-! ## The cut points and their start states -/

def cEntry : Nat := 0x80000000
def c068 : Nat := 0x80000068
def c0c4 : Nat := 0x800000c4
def c0d8 : Nat := 0x800000d8
def c10c : Nat := 0x8000010c
def c15c : Nat := 0x8000015c
def c18c : Nat := 0x8000018c
def c1a0 : Nat := 0x800001a0
def c1f8 : Nat := 0x800001f8
def c230 : Nat := 0x80000230
def c25c : Nat := 0x8000025c
def c340 : Nat := 0x80000340
def c3d4 : Nat := 0x800003d4
def c400 : Nat := 0x80000400
def c42c : Nat := 0x8000042c
def c460 : Nat := 0x80000460
def c4a0 : Nat := 0x800004a0

def cutPcs : List Nat :=
  [cEntry, c068, c0c4, c0d8, c10c, c15c, c18c, c1a0, c1f8, c230, c25c, c340, c3d4, c400, c42c,
    c460, c4a0]

def SEntry : SState := entryState ovEntry baseRegions [vtableKnown]
def S068 : SState := entryState ovRest baseRegions [vtableKnown]
def SBody : SState := entryState ovBody baseRegions [vtableKnown]
def S10c : SState := entryState ovBody baseRegions [vtableKnown, payloadKnown 0x180]
def S1a0 : SState := entryState ovBody baseRegions [vtableKnown, payloadKnown 0x100]
def SSpill : SState := entryState ovBody baseRegions [vtableKnown, vtableSpill]
def S230 : SState := entryState ovSlot (baseRegions ++ [slotR 32]) [vtableKnown]
def S460 : SState := entryState ovSlot (baseRegions ++ [slotR 40]) [vtableKnown]

end ZesuExec.Fn.TX
