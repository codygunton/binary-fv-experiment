import ZesuExec.Fn.Alloc.Spec
import ZesuExec.Sym.Tactic

/-!
# `alt_fl_alloc.alloc` (`0x80042494`): symbolic runs

`alloc` reads only RAM, never rodata, so it runs on `allocImage`, `zesuImage` without its rodata
(`RunsIn` depends only on `.text`, `runsIn_text`): `RodataLoaded allocImage` holds of every
machine.

Cut points (`Fn/Alloc/AllocVc.lean`): the entry; the two joins of the size-class search
(`0x8004267c`, `0x80042680`); after each `auipc` that addresses a global, where the global's
address becomes a region pointer: the head cell `free_lists[class]` (`0x800426a0`), the bump
pointers on the oversized path (`0x800426e0`, `0x80042708`) and on the fresh-block path
(`0x80042740`, `0x80042760`); and the pop path after its null test (`0x800426a8`), where the
head becomes a region pointer.
-/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym

def allocImage : Image := { zesuImage with rodata := [] }

def aCuts : List Nat :=
  [0x80042494, 0x8004267c, 0x80042680, 0x800426a0, 0x800426a8, 0x800426e0, 0x80042708,
   0x80042740, 0x80042760]

/-- An 8-byte word (`free_lists[class]`, or the first word of a free block). -/
def wordR : Region := ⟨some 8, 1, true⟩
/-- The 16-byte frame below `sp`. -/
def frameR : Region := ⟨some 16, 16, true⟩
/-- `ZKVM_HEAP_POS`, `ZKVM_HEAP_TOP`. -/
def varsR : Region := ⟨some 16, 1, true⟩

def ovP (i : Nat) : Option Sym := if i = 11 then some (.ptr 0 (-8)) else none
def ovP1 (i : Nat) : Option Sym :=
  if i = 11 then some (.ptr 0 (-8)) else if i = 10 then some (.ptr 1 0)
  else if i = 2 then some (.ptr 2 16) else none
def ovB (i : Nat) : Option Sym := if i = 12 then some (.ptr 0 0x21c) else none
def ovT (i : Nat) : Option Sym :=
  if i = 12 then some (.ptr 0 0x21c) else if i = 13 then some (.ptr 0 0x23c) else none
def ovO (i : Nat) : Option Sym := if i = 13 then some (.ptr 0 0x1bc) else none
def ovO2 (i : Nat) : Option Sym :=
  if i = 13 then some (.ptr 0 0x1bc) else if i = 12 then some (.ptr 0 0x1e4) else none

def SE : SState := Fn.entryState (fun _ => none) [] []
def SP : SState := Fn.entryState ovP [wordR] []
def SP1 : SState := Fn.entryState ovP1 [wordR, wordR, frameR] []
def SB : SState := Fn.entryState ovB [varsR] []
def ST : SState := Fn.entryState ovT [varsR] []
def SO : SState := Fn.entryState ovO [varsR] []
def SO2 : SState := Fn.entryState ovO2 [varsR] []

sym_run aRunE := run allocImage aCuts 64 0x80042494 SE
sym_run aRunJ1 := run allocImage aCuts 64 0x8004267c SE
sym_run aRunJ2 := run allocImage aCuts 64 0x80042680 SE
sym_run aRunP := run allocImage aCuts 64 0x800426a0 SP
sym_run aRunP1 := run allocImage aCuts 64 0x800426a8 SP1
sym_run aRunO := run allocImage aCuts 64 0x800426e0 SO
sym_run aRunO2 := run allocImage aCuts 64 0x80042708 SO2
sym_run aRunB := run allocImage aCuts 64 0x80042740 SB
sym_run aRunT := run allocImage aCuts 64 0x80042760 ST

end ZesuExec.Fn.Alloc
