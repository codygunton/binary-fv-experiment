import ZesuExec.Fn.F2.Spec

/-!
# F2 regions and cut states

Region 0: the 16-byte frame below the entry `sp`. Region 1: the input (`a2` bytes, size left to
`inBounds` obligations). Region 2: the 40-byte outcome struct.

Entry: `sp = ptr 0 16`, `a1 = ptr 1 0`, `a0 = ptr 2 0`. Loop heads (`0x800d6a24`,
`0x800d6ac4`): `sp = ptr 0 0`, `s0 = ptr 0 16`, `a0 = ptr 2 0`, the cursor
`a5 = ptr 1 1 + var 32` (`var 32` = length bytes read so far); the frame holds the saved `ra`
(`var 1`) and `s0` (`var 33`) as `known` facts. All other registers are their own variables.
-/

namespace ZesuExec.Fn.F2
open ZesuExec ZesuExec.Sym

def frameR : Region := ⟨some 16, 16, true⟩
def inputR : Region := ⟨none, 1, false⟩
def outR : Region := ⟨some 40, 8, true⟩
def regionsR : List Region := [frameR, inputR, outR]

/-- Frame base, input base and length, outcome base. -/
def shapeOf (fr inp : Word) (len : Nat) (out : Word) : Shape :=
  [((fr, 16), frameR), ((inp, len), inputR), ((out, 40), outR)]

def shape (m : Machine) : Shape := shapeOf (m.reg 2 - 16) (m.reg 11) (m.reg 12).toNat (m.reg 10)

def ov (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 16) else if i = 11 then some (.ptr 1 0)
  else if i = 10 then some (.ptr 2 0) else none

def S0 : SState := entryState ov regionsR []

def loopHead1 : Nat := 0x800d6a24
def loopHead2 : Nat := 0x800d6ac4

def ovL (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 0) else if i = 8 then some (.ptr 0 16)
  else if i = 10 then some (.ptr 2 0) else if i = 15 then some (.bin .add (.ptr 1 1) (.var 32))
  else none

def knownL : List Write := [⟨0, 8, 8, .var 1⟩, ⟨0, 0, 8, .var 33⟩]

def SL : SState := entryState ovL regionsR knownL

end ZesuExec.Fn.F2
