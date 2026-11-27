import ZesuExec.Fn.F3.Spec

/-!
# F3 regions and cut states

Region 0: the 96-byte frame below the entry `sp`; it holds the saved registers (offsets 48..95)
and decodeItem's 40-byte outcome (offsets 8..47). Region 1: the slice. Region 2: the result.
Region 3: the input (size left to `inBounds` obligations), whose base is the slice's first word.

Entry: `sp = ptr 0 96`, `a1 = ptr 1 0`, `a0 = ptr 2 0`, slice word 0 is `ptr 3 0`.
At the loop head (`0x800d6318`): `sp = ptr 0 0`, `s0 = ptr 0 96`, `s1 = ptr 2 0`, `s2 = ptr 1 0`,
`s3 = ptr 3 0`; the frame holds the saved `ra, s0..s4` as `var 33 .. var 38`; the cursor is
`a2 = ptr 3 0 + var 32`. The return address of decodeItem's call (`retPc`) is not a cut point:
`runWith` continues through the call (`Proof.lean`).
-/

namespace ZesuExec.Fn.F3
open ZesuExec ZesuExec.Sym

def frameR : Region := ⟨some 96, 16, true⟩
def sliceR : Region := ⟨some 16, 8, true⟩
def resR : Region := ⟨some 16, 8, true⟩
def inputR : Region := ⟨none, 1, false⟩
def regionsR : List Region := [frameR, sliceR, resR, inputR]

/-- Frame base, slice, result, input base and length. -/
def shapeOf (fr sl res inp : Word) (len : Nat) : Shape :=
  [((fr, 96), frameR), ((sl, 16), sliceR), ((res, 16), resR), ((inp, len), inputR)]

def shape (m : Machine) : Shape :=
  shapeOf (m.reg 2 - 96) (m.reg 11) (m.reg 10) (wordAt m (m.reg 11)) (wordAt m (m.reg 11 + 8)).toNat

def ov (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 96) else if i = 11 then some (.ptr 1 0)
  else if i = 10 then some (.ptr 2 0) else none

def S0 : SState := entryState ov regionsR [⟨1, 0, 8, .ptr 3 0⟩]

def retPc : Nat := 0x800d62b8
def loopHead : Nat := 0x800d6318

def ovR (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 0) else if i = 8 then some (.ptr 0 96)
  else if i = 9 then some (.ptr 2 0) else if i = 18 then some (.ptr 1 0)
  else if i = 19 then some (.ptr 3 0) else none

/-- The saved `ra, s0, s1, s2, s3, s4` at frame offsets 88, 80, .., 48. -/
def knownR : List Write :=
  [⟨0, 88, 8, .var 33⟩, ⟨0, 80, 8, .var 34⟩, ⟨0, 72, 8, .var 35⟩, ⟨0, 64, 8, .var 36⟩,
   ⟨0, 56, 8, .var 37⟩, ⟨0, 48, 8, .var 38⟩]

def ovL (i : Nat) : Option Sym :=
  if i = 12 then some (.bin .add (.ptr 3 0) (.var 32)) else ovR i

def SL : SState := entryState ovL regionsR knownR

end ZesuExec.Fn.F3
