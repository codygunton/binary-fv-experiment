import ZesuExec.Sym.Env

/-!
# Smart constructors of `Sym`

Each folds literals or keeps `ptr r off ± literal` as `ptr`; each has an evaluation lemma in
`ZesuExec.Sym.SmartLemmas`.
-/

namespace ZesuExec.Sym

/-- `n mod 2^64` read as a signed 64-bit integer. -/
def toInt64 (n : Nat) : Int := (BitVec.ofNat 64 n).toInt

/-- `a + c` for `a` a pointer or a pointer plus an index. -/
def addConst (a : Sym) (c : Int) : Option Sym :=
  match a with
  | .ptr r o => some (.ptr r (o + c))
  | .bin .add (.ptr r o) i => some (.bin .add (.ptr r (o + c)) i)
  | _ => none

/-- `a + c` for a literal `c`. -/
def addLit (a : Sym) (c : Nat) : Sym :=
  if c % 2 ^ 64 = 0 then a else (addConst a (toInt64 c)).getD (.bin .add a (.lit c))

/-- `a - c` for a literal `c`. -/
def subLit (a : Sym) (c : Nat) : Sym :=
  if c % 2 ^ 64 = 0 then a else (addConst a (-toInt64 c)).getD (.bin .sub a (.lit c))

def mkAdd (a b : Sym) : Sym :=
  match a, b with
  | .lit x, .lit y => .lit ((x + y) % 2 ^ 64)
  | a, .lit c => addLit a c
  | .lit c, b => addLit b c
  | a, .ptr r o => .bin .add (.ptr r o) a
  | a, b => .bin .add a b

def mkSub (a b : Sym) : Sym :=
  match a, b with
  | .lit x, .lit y => .lit (BitVec.ofNat 64 x - BitVec.ofNat 64 y).toNat
  | .ptr r o, .ptr r' o' => if r = r' then .lit (BitVec.ofInt 64 (o - o')).toNat else .bin .sub a b
  | a, .lit c => subLit a c
  | a, b => .bin .sub a b

/-- Generic binary operation: folds two literals. -/
def mkBin (op : BinOp) (a b : Sym) : Sym :=
  match op, a, b with
  | .add, a, b => mkAdd a b
  | .sub, a, b => mkSub a b
  | op, .lit x, .lit y => .lit (op.eval (BitVec.ofNat 64 x) (BitVec.ofNat 64 y)).toNat
  | op, a, b => .bin op a b

def mkSext (bits : Nat) (a : Sym) : Sym :=
  match a with
  | .lit x => .lit (((BitVec.ofNat 64 x).setWidth bits).signExtend 64).toNat
  | a => .sext bits a

/-- Bytes `k .. k+n-1` of `a`; all eight bytes of `a` are `a`. -/
def mkBytes (a : Sym) (k n : Nat) : Sym :=
  if k = 0 ∧ n = 8 then a else .bytes a k n

/-- Little-endian join of single-byte values. -/
def joinBytes : List Sym → Sym
  | [] => .lit 0
  | [b] => b
  | b :: bs => .cat b (joinBytes bs) 1

end ZesuExec.Sym
