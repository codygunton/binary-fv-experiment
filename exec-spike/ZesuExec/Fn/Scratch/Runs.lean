import ZesuExec.Fn.Alloc.Runs

/-!
# `scratch_arena.free` and `scratch_arena.remap`: symbolic runs

`ScratchArena` (`src/stateless/executor/scratch_arena.zig`): `child` (`ptr` at 0, `vtable` at 8),
`chunks` at 16 (the newest chunk or null), `last_chunk_size` at 24; a chunk header holds `next`
at 0, `cap` at 8, `used` at 16. Both functions load `chunks` and stop if it is null; otherwise
they set up a 16-byte frame and work on the newest chunk's header.

Cut points: the entry (region 0: the `chunks` word, `a0 = ptr 0 (-16)`) and the instruction after
the null test (`free`: region 0 the chunk's `used` word, `a0 = ptr 0 (-16)`; `remap`: region 0
the chunk's `cap` and `used` words, `a3 = ptr 0 (-8)`; region 1 the 16 bytes below `sp`).
-/

namespace ZesuExec.Fn.Scratch
open ZesuExec ZesuExec.Sym ZesuExec.Fn.Alloc

def freeEntry : Nat := 0x800db904
def freeJ : Nat := 0x800db90c
def remapEntry : Nat := 0x800db944
def remapJ : Nat := 0x800db94c

def capR : Region := ⟨some 16, 1, true⟩

def ovE (i : Nat) : Option Sym := if i = 10 then some (.ptr 0 (-16)) else none
def ovFJ (i : Nat) : Option Sym :=
  if i = 10 then some (.ptr 0 (-16)) else if i = 2 then some (.ptr 1 16) else none
def ovRJ (i : Nat) : Option Sym :=
  if i = 13 then some (.ptr 0 (-8)) else if i = 2 then some (.ptr 1 16) else none

def SE : SState := Fn.entryState ovE [wordR] []
def SFJ : SState := Fn.entryState ovFJ [wordR, frameR] []
def SRJ : SState := Fn.entryState ovRJ [capR, frameR] []

sym_run fsRunE := run allocImage [freeEntry, freeJ] 32 freeEntry SE
sym_run fsRunJ := run allocImage [freeEntry, freeJ] 32 freeJ SFJ
sym_run rsRunE := run allocImage [remapEntry, remapJ] 48 remapEntry SE
sym_run rsRunJ := run allocImage [remapEntry, remapJ] 48 remapJ SRJ

end ZesuExec.Fn.Scratch
