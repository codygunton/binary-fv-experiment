import ZesuExec.Fn.Scratch.Runs

/-!
# `scratch_arena.alloc` (`0x800db7a4`): symbolic runs

Regions: 0 the 64-byte frame below the entry `sp`, 1 the `ScratchArena` at `ctx = a0` (`child.ptr`
at 0, `child.vtable` at 8, known to hold `0x801136d8`, `chunks` at 16, `last_chunk_size` at 24);
after the null test of `chunks`, 2 the newest chunk's `cap` and `used` words; after the call's
null test, 2 the new chunk's 24-byte header.

Cut points: the entry; `0x800db7e4` after the null test of `chunks`; `0x800db820` where a new
chunk is requested; `0x800db87c` the return of the child allocator's `alloc`; `0x800db880` after
its null test.
-/

namespace ZesuExec.Fn.Scratch
open ZesuExec ZesuExec.Sym ZesuExec.Fn.Alloc

def allocEntryS : Nat := 0x800db7a4

def aCutsS : List Nat := [0x800db7a4, 0x800db7e4, 0x800db820, 0x800db87c, 0x800db880]

def frame64R : Region := ⟨some 64, 16, true⟩
def arenaR : Region := ⟨some 32, 1, true⟩
def hdrR : Region := ⟨some 24, 1, true⟩

/-- `child.vtable` holds `alt_fl_alloc`'s vtable `0x801136d8`. -/
def knownS : List Write := [⟨1, 8, 8, .lit 0x801136d8⟩]

def ovAE (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 64) else if i = 10 then some (.ptr 1 0) else none
/-- Inside the frame: `sp`, `s0 = sp + 64`, `s3 = ctx`. -/
def ovIn (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 0) else if i = 8 then some (.ptr 0 64)
  else if i = 19 then some (.ptr 1 0) else none
def ovAJ (i : Nat) : Option Sym := if i = 10 then some (.ptr 2 (-8)) else ovIn i
def ovAN (i : Nat) : Option Sym := if i = 10 then some (.ptr 2 0) else ovIn i

def SAE : SState := Fn.entryState ovAE [frame64R, arenaR] knownS
def SAJ : SState := Fn.entryState ovAJ [frame64R, arenaR, capR] knownS
def SAS : SState := Fn.entryState ovIn [frame64R, arenaR] knownS
def SAN : SState := Fn.entryState ovAN [frame64R, arenaR, hdrR] knownS

sym_run saRunE := run zesuImage aCutsS 64 0x800db7a4 SAE
sym_run saRunJ := run zesuImage aCutsS 64 0x800db7e4 SAJ
sym_run saRunS := run zesuImage aCutsS 64 0x800db820 SAS
sym_run saRunR := run zesuImage aCutsS 64 0x800db87c SAS
sym_run saRunN := run zesuImage aCutsS 64 0x800db880 SAN

end ZesuExec.Fn.Scratch
