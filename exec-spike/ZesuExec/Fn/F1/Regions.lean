import ZesuExec.Fn.F1.Spec

/-!
# F1 regions

Region 0: the 112-byte frame below `sp` (`sp = ptr 0 112`). Region 1: the 24-byte list header
(`a0`). Region 2: the 16-byte allocator object (`a1`), whose second word is the vtable address.
-/

namespace ZesuExec.Fn.F1
open ZesuExec ZesuExec.Sym

def frameR : Region := ⟨some 112, 16, true⟩
def headerR : Region := ⟨some 24, 8, true⟩
def allocObjR : Region := ⟨some 16, 8, false⟩

def shape (m : Machine) : Shape :=
  [((m.reg 2 - 112, 112), frameR), ((m.reg 10, 24), headerR), ((m.reg 11, 16), allocObjR)]

def ov (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 112) else if i = 10 then some (.ptr 1 0)
  else if i = 11 then some (.ptr 2 0) else none

def known : List Write := [⟨2, 8, 8, .lit vtable⟩]

def S0 : SState := entryState ov [frameR, headerR, allocObjR] known

end ZesuExec.Fn.F1
