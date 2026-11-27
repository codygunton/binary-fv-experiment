import ZesuExec.Sym.Types

/-!
# Compact printing of symbolic values, conditions and leaves (programme plan S4 step 1)

`Repr`-free: registers by ABI name, literals in hex, terms deeper than `maxDepth` cut to `…`.
`Leaf.pp S l` lists only the registers of `l.S` that differ from `S` (the cut's state) and the
memory writes `l` added. Printing only; no proof uses these.
-/

namespace ZesuExec.Sym

def abiNames : Array String :=
  #["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6"]

def regName (i : Nat) : String := abiNames.getD i s!"x{i}"

def ppHex (n : Nat) : String :=
  if n < 10 then toString n else "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- A literal as a signed value when its top bit is set (`-1` for `2^64 - 1`). -/
def ppLit (n : Nat) : String :=
  if 2 ^ 63 ≤ n ∧ n < 2 ^ 64 then "-" ++ ppHex (2 ^ 64 - n) else ppHex n

def ppInt (i : Int) : String := if i < 0 then "-" ++ ppHex i.natAbs else "+" ++ ppHex i.natAbs

def BinOp.sym : BinOp → String
  | .add => "+" | .sub => "-" | .and => "&" | .or => "|" | .xor => "^" | .sll => "<<"
  | .srl => ">>" | .sltu => "<u" | .mul => "*" | .mulhu => "*hu"

def maxDepth : Nat := 6

/-- `var i` for `i < 32` is register `i` at the cut (`a0₀`); other variables print as `v<i>`. -/
def Sym.ppD : Nat → Sym → String
  | 0, _ => "…"
  | _ + 1, .lit n => ppLit n
  | _ + 1, .var i => if i < 32 then regName i ++ "₀" else s!"v{i}"
  | _ + 1, .ptr r off => if off = 0 then s!"R{r}" else s!"R{r}{ppInt off}"
  | _ + 1, .init r off n => s!"R{r}[{ppHex off}]:{n}"
  | d + 1, .initx r off idx scale n =>
    s!"R{r}[{ppHex off}+{scale}*{Sym.ppD d idx}]:{n}"
  | d + 1, .bin op a b => s!"({Sym.ppD d a} {op.sym} {Sym.ppD d b})"
  | d + 1, .sext bits a => s!"sext{bits}({Sym.ppD d a})"
  | d + 1, .bytes a k n => s!"{Sym.ppD d a}[{k}:{n}]"
  | d + 1, .cat lo hi n => s!"cat({Sym.ppD d lo}, {Sym.ppD d hi}, {n})"

def Sym.pp (s : Sym) : String := Sym.ppD maxDepth s

def SBool.pp : SBool → String
  | .eq a b => s!"{a.pp} == {b.pp}"
  | .ne a b => s!"{a.pp} != {b.pp}"
  | .ltu a b => s!"{a.pp} <u {b.pp}"
  | .geu a b => s!"{a.pp} >=u {b.pp}"
  | .lts a b => s!"{a.pp} <s {b.pp}"
  | .ges a b => s!"{a.pp} >=s {b.pp}"

def Exit.pp : Exit → String
  | .at pc => s!"at {ppHex pc}"
  | .call t r => s!"call {ppHex t} ret {ppHex r}"
  | .callInd t r => s!"callInd {t.pp} ret {ppHex r}"
  | .ret t => s!"ret {t.pp}"
  | .jumpInd t => s!"jumpInd {t.pp}"

def Oblig.pp : Oblig → String
  | .inBounds r off idx scale n => s!"inBounds R{r} {ppHex off}+{scale}*{idx.pp}+{n}"
  | .aligned x n => s!"aligned {x.pp} {n}"

def Write.pp (w : Write) : String := s!"R{w.r}[{ppHex w.off}]:{w.n} := {w.v.pp}"

/-- The leaf `l` of a run from the cut state `S`: exit, steps, changed registers, new writes,
conditions, obligations; one item per line. -/
def Leaf.pp (S : SState) (l : Leaf) : String := Id.run do
  let mut out := s!"{l.exit.pp}, {l.S.steps - S.steps} steps"
  for i in [1:32] do
    if l.S.reg i != S.reg i then out := out ++ s!"\n  {regName i} = {(l.S.reg i).pp}"
  for w in (l.S.mem.take (l.S.mem.length - S.mem.length)).reverse do
    out := out ++ s!"\n  {w.pp}"
  for c in l.conds do out := out ++ s!"\n  if {c.pp}"
  for o in l.obligs do out := out ++ s!"\n  need {o.pp}"
  out

end ZesuExec.Sym
