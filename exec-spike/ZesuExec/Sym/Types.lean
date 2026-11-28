import ZesuExec.Logic
import Lean.ToExpr

/-!
# Symbolic values and states of the executor `ZesuExec.Sym.run`

No nested or mutual inductives: Lean 4.29 cannot derive `DecidableEq` for them.
-/

namespace ZesuExec.Sym

inductive BinOp | add | sub | and | or | xor | sll | srl | sltu | mul | mulhu | divu
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

inductive Sym
  /-- `n mod 2^64` -/
  | lit   (n : Nat)
  /-- unknown 64-bit value -/
  | var   (i : Nat)
  /-- base of region `r` plus `off` -/
  | ptr   (r : Nat) (off : Int)
  /-- `n ≤ 8` bytes of region `r`'s initial memory at `off`, zero-extended -/
  | init  (r off n : Nat)
  /-- `n ≤ 8` bytes of region `r`'s initial memory at `off + scale * idx`, zero-extended -/
  | initx (r off : Nat) (idx : Sym) (scale n : Nat)
  | bin   (op : BinOp) (a b : Sym)
  /-- sign-extend the low `bits` bits -/
  | sext  (bits : Nat) (a : Sym)
  /-- bytes `k .. k+n-1` of `a`, zero-extended -/
  | bytes (a : Sym) (k n : Nat)
  /-- low `nlo` bytes of `lo` below `hi` -/
  | cat   (lo hi : Sym) (nlo : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

inductive SBool
  | eq (a b : Sym) | ne (a b : Sym) | ltu (a b : Sym) | geu (a b : Sym) | lts (a b : Sym)
  | ges (a b : Sym)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- `n ≤ 8` bytes of `v` at a constant offset `off` of region `r`. -/
structure Write where
  r : Nat
  off : Nat
  n : Nat
  v : Sym
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Region where
  size : Option Nat
  align : Nat
  writable : Bool
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure SState where
  /-- 32 entries; entry 0 is read as `lit 0` -/
  regs : List Sym
  /-- newest first -/
  mem : List Write
  /-- facts about initial memory -/
  known : List Write
  regions : List Region
  steps : Nat
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

inductive Oblig
  /-- `off + scale * idx + n ≤ size of region r` -/
  | inBounds (r off : Nat) (idx : Sym) (scale n : Nat)
  /-- `x mod n = 0` -/
  | aligned (x : Sym) (n : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

inductive Exit
  | at (pc : Nat)
  | call (target ret : Nat)
  | callInd (target : Sym) (ret : Nat)
  | ret (target : Sym)
  | jumpInd (target : Sym)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Leaf where
  S : SState
  exit : Exit
  conds : List SBool
  obligs : List Oblig
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- How control leaves one symbolic instruction. -/
inductive StepExit
  | next (pc : Nat)
  | branch (c : SBool) (taken fall : Nat)
  | call (target ret : Nat)
  | callInd (target : Sym) (ret : Nat)
  | ret (target : Sym)
  | jumpInd (target : Sym)
  deriving DecidableEq, Repr

namespace SState

def reg (S : SState) (i : Nat) : Sym := if i = 0 then .lit 0 else S.regs.getD i (.lit 0)

def setReg (S : SState) (i : Nat) (v : Sym) : SState :=
  if i = 0 then S else { S with regs := S.regs.set i v }

def region (S : SState) (r : Nat) : Option Region := S.regions[r]?

end SState

end ZesuExec.Sym
