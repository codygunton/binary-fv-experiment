import ZesuExec.Fn.F0.Spec

/-! # F0 regions: region 0 is the 16-byte frame below `sp`; `sp = ptr 0 16`. -/

namespace ZesuExec.Fn.F0
open ZesuExec ZesuExec.Sym

def frame : Region := ⟨some 16, 16, true⟩

def shape (m : Machine) : Shape := [((m.reg 2 - 16, 16), frame)]

def ov (i : Nat) : Option Sym := if i = 2 then some (.ptr 0 16) else none

def S0 : SState := entryState ov [frame] []

end ZesuExec.Fn.F0
