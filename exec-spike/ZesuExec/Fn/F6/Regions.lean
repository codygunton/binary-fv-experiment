import ZesuExec.Fn.F6.Spec

/-!
# F6 regions and cut states

Region 0: the 400-byte frame below the entry `sp` (saved `ra, s0..s8` at offsets 392..320; the
decodeItem outcomes at 8, 64, 104, 176, 280; the slice words at 48/56; the nextUint64 results
at 144, 216, 248; the optional words at 160, 232, 264). Region 1: the 80-byte result. Region 2:
the input (size left to `inBounds` obligations).

Entry: `sp = ptr 0 400`, `a0 = ptr 1 0`, `a1 = ptr 2 0`. At every cut (the 20 call-return
points and the three loop heads): `sp = ptr 0 0`, `s0 = ptr 0 400`, `s1 = ptr 1 0`; the frame
holds the saved `ra, s0..s8` as `var 33 .. var 42` (`knownR`); `var 32` is the loop cursor's
input offset. Some cuts also fix `s7`, `s8`, `s2` (the optional words' pointers) or the loop
cursor `a1 = ptr 2 0 + var 32`.
-/

namespace ZesuExec.Fn.F6
open ZesuExec ZesuExec.Sym

def frameR : Region := ⟨some 400, 16, true⟩
def resR : Region := ⟨some 80, 8, true⟩
def inputR : Region := ⟨none, 1, false⟩
def regionsR : List Region := [frameR, resR, inputR]

/-- Frame base, result, input base and length. -/
def shapeOf (fr res inp : Word) (len : Nat) : Shape :=
  [((fr, 400), frameR), ((res, 80), resR), ((inp, len), inputR)]

def shape (m : Machine) : Shape := shapeOf (m.reg 2 - 400) (m.reg 10) (m.reg 11) (m.reg 12).toNat

def ov (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 400) else if i = 10 then some (.ptr 1 0)
  else if i = 11 then some (.ptr 2 0) else none

def S0 : SState := entryState ov regionsR []

/-- The registers saved at frame offset `392 - 8 k`: `ra, s0, .., s8`. -/
def savedRegs : List Nat := [1, 8, 9, 18, 19, 20, 21, 22, 23, 24]

/-- The saved registers as `var 33 .. var 42`. -/
def knownR : List Write :=
  [⟨0, 392, 8, .var 33⟩, ⟨0, 384, 8, .var 34⟩, ⟨0, 376, 8, .var 35⟩, ⟨0, 368, 8, .var 36⟩,
   ⟨0, 360, 8, .var 37⟩, ⟨0, 352, 8, .var 38⟩, ⟨0, 344, 8, .var 39⟩, ⟨0, 336, 8, .var 40⟩,
   ⟨0, 328, 8, .var 41⟩, ⟨0, 320, 8, .var 42⟩]

def ovC (x : Nat → Option Sym) (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 0) else if i = 8 then some (.ptr 0 400)
  else if i = 9 then some (.ptr 1 0) else x i

def SC (x : Nat → Option Sym) : SState := entryState (ovC x) regionsR knownR

/-- The rodata `None` constant (`__anon_17344`, 16 zero bytes). -/
def noneConst : Nat := 0x801152b0
/-- The constant error union (`__anon_18759`). -/
def errConst : Nat := 0x80114fb8

def xN : Nat → Option Sym := fun _ => none
def xL : Nat → Option Sym := fun i => if i = 11 then some (.bin .add (.ptr 2 0) (.var 32)) else none
def x15 : Nat → Option Sym := fun i => if i = 23 then some (.lit noneConst) else none
def x16 : Nat → Option Sym := fun i =>
  if i = 23 then some (.lit noneConst) else if i = 24 then some (.ptr 0 160) else none
def x18 : Nat → Option Sym := fun i =>
  if i = 23 then some (.lit noneConst) else if i = 24 then some (.ptr 0 160)
  else if i = 18 then some (.ptr 0 232) else none

/-! ## Cut points -/

def ret0 : Nat := 0x800d5cf8
def retS : List Nat := [0x800d5d38, 0x800d5dc0, 0x800d5dec, 0x800d5e18, 0x800d5e44, 0x800d5e70,
  0x800d5e9c, 0x800d5ec8, 0x800d5ef4]
def ret9 : Nat := 0x800d5f1c
def ret10 : Nat := 0x800d5fb8
def ret11 : Nat := 0x800d6020
def ret12 : Nat := 0x800d60b8
def ret13 : Nat := 0x800d60f0
def ret14 : Nat := 0x800d611c
def ret15 : Nat := 0x800d6160
def ret16 : Nat := 0x800d619c
def ret17 : Nat := 0x800d6220
def ret18 : Nat := 0x800d6254
def loop9 : Nat := 0x800d5f88
def loop10 : Nat := 0x800d5fec
def loop11 : Nat := 0x800d6054

def cuts : List Nat :=
  ret0 :: retS ++ [ret9, ret10, ret11, ret12, ret13, ret14, ret15, ret16, ret17, ret18,
    loop9, loop10, loop11]

end ZesuExec.Fn.F6
