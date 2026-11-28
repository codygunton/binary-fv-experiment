import ZesuExec.Fn.SszRoot.Spec
import ZesuExec.Sym.Tactic

/-!
# `progressiveRootAt` in the recursive obligation framework: runs

Cuts at the entry (`cE`), after the `sparseRoot` call (`cS`, `0x80042b84`), after the recursive
call (`cR`, `0x80042ba0`) and after `zkvm_sha256` (`cH`, `0x80042bb4`). The entry state has the
frame (`0xa0` bytes below `sp`) and the result as regions; `cS` and `cR` touch no memory; `cH`
reads the frame (at `sp`) and writes the result (at `s1`).
-/

namespace ZesuExec.Fn.SszRoot.Prog
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym

def pcS : Nat := 0x80042b84
def pcR : Nat := 0x80042ba0
def pcH : Nat := 0x80042bb4

def pcs : List Nat := [progEntry, pcS, pcR, pcH]
def fuel : Nat := 60

def frR : Region := ⟨some 0xa0, 1, true⟩
def frRo : Region := ⟨some 0xa0, 1, false⟩
def outW : Region := ⟨some 32, 1, true⟩

def ovE (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 0xa0) else if i = 10 then some (.ptr 1 0) else none
def ovH (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 0) else if i = 8 then some (.ptr 0 0xa0)
  else if i = 9 then some (.ptr 1 0) else none

def SE : SState := entryState ovE [frR, outW] []
def S0 : SState := entryState (fun _ => none) [] []
def SH : SState := entryState ovH [frRo, outW] []

def regsE (m : Machine) : List (Word × Nat) :=
  [(m.reg 2 - BitVec.ofNat 64 0xa0, 0xa0), (m.reg 10, 32)]
def regsH (m : Machine) : List (Word × Nat) := [(m.reg 2, 0xa0), (m.reg 9, 32)]

sym_run runE := run zesuImage pcs fuel progEntry SE
sym_run runS := run zesuImage pcs fuel pcS S0
sym_run runR := run zesuImage pcs fuel pcR S0
sym_run runH := run zesuImage pcs fuel pcH SH

end ZesuExec.Fn.SszRoot.Prog
