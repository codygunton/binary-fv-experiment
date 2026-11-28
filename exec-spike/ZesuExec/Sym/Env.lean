import ZesuExec.Sym.Types

/-!
# Meaning of symbolic values: `Env`, `Sym.eval`, `Match`

An `Env` fixes the unknowns of a symbolic state: the variables, the region bases and sizes,
and the initial bytes `mem0 r j` of each region `r` at offset `j`. `Match env S m` says that the concrete machine `m` is an
instance of the symbolic state `S` under `env`.
-/

namespace ZesuExec.Sym
open ZesuExec.Machine

/-- The bytes `f k, f (k+1), …, f (k+n-1)`. -/
def byteList (f : Nat → Byte) : Nat → Nat → List Byte
  | _, 0 => []
  | k, n + 1 => f k :: byteList f (k + 1) n

/-- Byte `j` of `x` (bits `8j .. 8j+7`). -/
abbrev byteOf (x : Word) (j : Nat) : Byte := x.extractLsb' (8 * j) 8

def BinOp.eval : BinOp → Word → Word → Word
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .sll, a, b => a <<< (b.toNat % 64)
  | .srl, a, b => a >>> (b.toNat % 64)
  | .sltu, a, b => if a.ult b then 1 else 0
  | .mul, a, b => a * b
  | .mulhu, a, b => BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)
  | .divu, a, b => if b = 0 then -1 else a / b
  | .remu, a, b => a % b

structure Env where
  vars : Nat → Word
  /-- (base, size) per region -/
  regions : List (Word × Nat)
  /-- initial byte of region `r` at offset `j` -/
  mem0 : Nat → Nat → Byte

namespace Env
def base (env : Env) (r : Nat) : Word := (env.regions.getD r (0, 0)).1
def size (env : Env) (r : Nat) : Nat := (env.regions.getD r (0, 0)).2
/-- Initial byte at offset `j` of region `r`. -/
def byte0 (env : Env) (r j : Nat) : Byte := env.mem0 r j
end Env

def Sym.eval (env : Env) : Sym → Word
  | .lit n => BitVec.ofNat 64 n
  | .var i => env.vars i
  | .ptr r off => env.base r + BitVec.ofInt 64 off
  | .init r off n => ofBytesLE (byteList (env.byte0 r) off n)
  | .initx r off idx scale n =>
    ofBytesLE (byteList (env.byte0 r) (off + scale * (Sym.eval env idx).toNat) n)
  | .bin op a b => op.eval (Sym.eval env a) (Sym.eval env b)
  | .sext bits a => ((Sym.eval env a).setWidth bits).signExtend 64
  | .bytes a k n => ofBytesLE (byteList (byteOf (Sym.eval env a)) k n)
  | .cat lo hi nlo =>
    (Sym.eval env lo &&& BitVec.ofNat 64 (2 ^ (8 * nlo) - 1)) ||| (Sym.eval env hi <<< (8 * nlo))

theorem Sym.eval_lit (env : Env) (n : Nat) : (Sym.lit n).eval env = BitVec.ofNat 64 n := rfl
theorem Sym.eval_var (env : Env) (i : Nat) : (Sym.var i).eval env = env.vars i := rfl
theorem Sym.eval_ptr (env : Env) (r : Nat) (o : Int) :
    (Sym.ptr r o).eval env = env.base r + BitVec.ofInt 64 o := rfl
theorem Sym.eval_bin (env : Env) (op : BinOp) (a b : Sym) :
    (Sym.bin op a b).eval env = op.eval (a.eval env) (b.eval env) := rfl
theorem Sym.eval_sext (env : Env) (bits : Nat) (a : Sym) :
    (Sym.sext bits a).eval env = ((a.eval env).setWidth bits).signExtend 64 := rfl

def SBool.eval (env : Env) : SBool → Bool
  | .eq a b => a.eval env == b.eval env
  | .ne a b => a.eval env != b.eval env
  | .ltu a b => (a.eval env).ult (b.eval env)
  | .geu a b => !(a.eval env).ult (b.eval env)
  | .lts a b => (a.eval env).slt (b.eval env)
  | .ges a b => !(a.eval env).slt (b.eval env)

def Write.covers (w : Write) (r j : Nat) : Bool := w.r == r && w.off ≤ j && j < w.off + w.n

/-- Byte at offset `j` of region `r` after the writes `ws` (newest first) over `mem0`. -/
def memByte (env : Env) (ws : List Write) (r j : Nat) : Byte :=
  match ws.find? (·.covers r j) with
  | some w => byteOf (w.v.eval env) (j - w.off)
  | none => env.byte0 r j

def Oblig.holds (env : Env) : Oblig → Prop
  | .inBounds r off idx scale n => off + scale * (idx.eval env).toNat + n ≤ env.size r
  | .aligned x n => (x.eval env).toNat % n = 0

/-- Region shapes: no wrap, pairwise disjoint, sizes and alignments as `S.regions` states,
writable regions in RAM, the others in rodata, input or RAM. -/
structure Env.WF (env : Env) (S : SState) : Prop where
  len : env.regions.length = S.regions.length
  disjoint : ∀ r r' j j', r ≠ r' → j < env.size r → j' < env.size r' →
    (env.base r).toNat + j ≠ (env.base r').toNat + j'
  size : ∀ r R s, S.regions[r]? = some R → R.size = some s → env.size r = s
  align : ∀ r R, S.regions[r]? = some R → (env.base r).toNat % R.align = 0
  range : ∀ r R, S.regions[r]? = some R →
    (if R.writable then writable (env.base r).toNat (env.size r)
     else readable (env.base r).toNat (env.size r)) = true

/-- `m` is an instance of `S` under `env`. -/
structure Match (env : Env) (S : SState) (m : Machine) : Prop where
  regsLen : S.regs.length = 32
  regs : ∀ i : Fin 32, (S.reg i.val).eval env = m.reg i
  mem : ∀ r j, r < S.regions.length → j < env.size r →
    m.mem (env.base r + BitVec.ofNat 64 j) = some (memByte env S.mem r j)
  known : ∀ k ∈ S.known, ∀ t < k.n, env.byte0 k.r (k.off + t) = byteOf (k.v.eval env) t

/-- An address inside a writable region of `S`. -/
def InWritable (env : Env) (S : SState) (a : Word) : Prop :=
  ∃ r R j, S.regions[r]? = some R ∧ R.writable = true ∧ j < env.size r ∧
    a = env.base r + BitVec.ofNat 64 j

/-- The rodata bytes of `img` inside `[Layout.rodataLo, Layout.rodataHi)` are loaded in `m`. -/
def RoLoaded (img : Image) (m : Machine) : Prop :=
  ∀ a b, Layout.rodataLo ≤ a → a < Layout.rodataHi → img.rodataByte? a = some b →
    m.mem (BitVec.ofNat 64 a) = some (BitVec.ofNat 8 b)

def ExitOk (env : Env) : Exit → Machine → Prop
  | .at pc, m => m.pc.toNat = pc
  | .call target _, m => m.pc.toNat = target
  | .callInd t _, m => m.pc = t.eval env
  | .ret t, m => m.pc = t.eval env
  | .jumpInd t, m => m.pc = t.eval env

end ZesuExec.Sym
