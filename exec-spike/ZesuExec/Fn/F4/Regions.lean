import ZesuExec.Fn.F4.Spec
import ZesuExec.Fn.Stage

/-!
# Regions of `toOwnedSlice` (F4 and F5 share them)

Region 0: the 96-byte frame below `sp` (`sp = ptr 0 96`). Region 1: the 24-byte result (`a0`).
Region 2: the 24-byte list header (`a1`). Region 3: the 16-byte allocator object (`a2`), whose
second word is the vtable address.
-/

namespace ZesuExec.Fn.ToOwned
open ZesuExec ZesuExec.Sym

def frameR : Region := ⟨some 96, 16, true⟩
def resultR : Region := ⟨some 24, 8, true⟩
def headerR : Region := ⟨some 24, 8, true⟩
def allocObjR : Region := ⟨some 16, 8, false⟩

def shape (m : Machine) : Shape :=
  [((m.reg 2 - 96, 96), frameR), ((m.reg 10, 24), resultR), ((m.reg 11, 24), headerR),
    ((m.reg 12, 16), allocObjR)]

def ov (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 96) else if i = 10 then some (.ptr 1 0)
  else if i = 11 then some (.ptr 2 0) else if i = 12 then some (.ptr 3 0) else none

def known : List Write := [⟨3, 8, 8, .lit vtable⟩]

def S0 : SState := entryState ov [frameR, resultR, headerR, allocObjR] known

end ZesuExec.Fn.ToOwned
