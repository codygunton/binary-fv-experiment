import ZesuExec.Fn.Alloc.Runs

/-!
# `alt_fl_alloc.free` (`0x80041f38`): symbolic runs

On `allocImage` like `alloc`. Cut points (`Fn/Alloc/FreeVc.lean`): the entry; the two joins of
the size-class search (`0x80042130`, `0x80042134`), where the frame holding the saved `ra` and
`s0` is region 0; and the push (`0x80042170`, after `free_lists + 8 * class`), where the head
cell, the freed block's first word and the frame are regions 0, 1, 2.
-/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym

def fCuts : List Nat := [0x80041f38, 0x80042130, 0x80042134, 0x80042170]

def ovFE (i : Nat) : Option Sym := if i = 2 then some (.ptr 0 16) else none
def ovFJ (i : Nat) : Option Sym := if i = 2 then some (.ptr 0 0) else none
def ovFF (i : Nat) : Option Sym :=
  if i = 10 then some (.ptr 0 (-8)) else if i = 11 then some (.ptr 1 0)
  else if i = 2 then some (.ptr 2 0) else none

def SFE : SState := Fn.entryState ovFE [frameR] []
def SFJ : SState := Fn.entryState ovFJ [frameR] []
def SFF : SState := Fn.entryState ovFF [wordR, wordR, frameR] []

sym_run fRunE := run allocImage fCuts 64 0x80041f38 SFE
sym_run fRunJ1 := run allocImage fCuts 64 0x80042130 SFJ
sym_run fRunJ2 := run allocImage fCuts 64 0x80042134 SFJ
sym_run fRunF := run allocImage fCuts 64 0x80042170 SFF

end ZesuExec.Fn.Alloc
