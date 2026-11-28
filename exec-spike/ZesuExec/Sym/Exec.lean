import ZesuExec.Sym.Smart

/-!
# The symbolic executor

`stepI` executes one decoded instruction on a symbolic state; `run` follows fall-through and
literal jumps, forks at conditional branches, and stops with a `Leaf` at a cut, a call, a
return, another indirect jump or the `memcpy` entry. At an address where nothing decodes (an
`unimp`, a form `decodeNat` lacks) it stops with a leaf carrying `Oblig.unreachable`, which never
holds: that leaf is a goal that its path is infeasible. Every function is structural recursion on
fuel or on lists, so the kernel evaluates it (`ZesuExec.Sym.Tactic`).
-/

namespace ZesuExec.Sym
open ZesuExec.Machine

/-- Where an address points. -/
inductive Place
  /-- a literal address (only rodata is readable this way) -/
  | ro (a : Nat)
  /-- region `r` at constant offset `off` -/
  | cst (r off : Nat)
  /-- region `r` at `off + scale * idx` -/
  | idx (r off : Nat) (i : Sym) (scale : Nat)

/-- An index and its scale: `x << k` has scale `2^k`. -/
def idxOf : Sym → Sym × Nat
  | .bin .sll x (.lit k) => if k < 64 then (x, 2 ^ k) else (.bin .sll x (.lit k), 1)
  | i => (i, 1)

def place : Sym → Option Place
  | .lit a => some (.ro a)
  | .ptr r o => if 0 ≤ o then some (.cst r o.toNat) else none
  | .bin .add (.ptr r o) i => if 0 ≤ o then some (.idx r o.toNat (idxOf i).1 (idxOf i).2) else none
  | _ => none

def Write.overlaps (w : Write) (r off n : Nat) : Bool := w.r == r && w.off < off + n && off < w.off + w.n

/-- The `n` rodata bytes of `img` at `a`, little-endian. -/
def roValue (img : Image) (a : Nat) : Nat → Option Nat
  | 0 => some 0
  | n + 1 => do
    let b ← img.rodataByte? a
    let rest ← roValue img (a + 1) n
    pure (b % 256 + 256 * rest)

/-- The current byte at offset `j` of region `r`, as a one-byte symbolic value. -/
def byteSym (S : SState) (r j : Nat) : Sym :=
  match S.mem.find? (·.covers r j) with
  | some w => .bytes w.v (j - w.off) 1
  | none => match S.known.find? (·.covers r j) with
    | some k => .bytes k.v (j - k.off) 1
    | none => .init r j 1

def byteSyms (S : SState) (r : Nat) : Nat → Nat → List Sym
  | _, 0 => []
  | j, n + 1 => byteSym S r j :: byteSyms S r (j + 1) n

/-- `n` bytes at a constant offset of region `r`. -/
def readConst (S : SState) (r off n : Nat) : Sym :=
  match S.mem.find? (·.overlaps r off n) with
  | some w => if w.off = off ∧ w.n = n then mkBytes w.v 0 n else joinBytes (byteSyms S r off n)
  | none => match S.known.find? (·.overlaps r off n) with
    | some k => if k.off = off ∧ k.n = n then mkBytes k.v 0 n else joinBytes (byteSyms S r off n)
    | none => .init r off n

/-- Constant-offset access check: bounds (or an obligation if the size is unknown). Any
alignment: `Machine.load`/`Machine.store` accept misaligned ranges. -/
def cstCheck (_R : Region) (r off n : Nat) : Option (List Oblig) :=
  match _R.size with
  | some s => if off + n ≤ s then some [] else none
  | none => some [.inBounds r off (.lit 0) 1 n]

def loadSym (img : Image) (S : SState) (a : Sym) (n : Nat) : Option (Sym × List Oblig) :=
  match place a with
  | some (.ro x) =>
    if inRange Layout.rodataLo Layout.rodataHi x n = true then
      (roValue img x n).map fun v => (.lit v, [])
    else none
  | some (.cst r off) =>
    match S.region r with
    | some R => (cstCheck R r off n).map fun ob => (readConst S r off n, ob)
    | none => none
  | some (.idx r off i sc) =>
    match S.region r with
    | some _ =>
      if S.mem.all (·.r != r) then
        some (.initx r off i sc n, [.inBounds r off i sc n])
      else none
    | none => none
  | none => none

def storeSym (S : SState) (a : Sym) (n : Nat) (v : Sym) : Option (SState × List Oblig) :=
  match place a with
  | some (.cst r off) =>
    match S.region r with
    | some R =>
      if R.writable then
        (cstCheck R r off n).map fun ob => ({ S with mem := ⟨r, off, n, v⟩ :: S.mem }, ob)
      else none
    | none => none
  | _ => none

/-- Statically known truth value. -/
def SBool.static? : SBool → Option Bool
  | .eq (.lit x) (.lit y) => some (BitVec.ofNat 64 x == BitVec.ofNat 64 y)
  | .ne (.lit x) (.lit y) => some (BitVec.ofNat 64 x != BitVec.ofNat 64 y)
  | .ltu (.lit x) (.lit y) => some ((BitVec.ofNat 64 x).ult (BitVec.ofNat 64 y))
  | .geu (.lit x) (.lit y) => some (!(BitVec.ofNat 64 x).ult (BitVec.ofNat 64 y))
  | .lts (.lit x) (.lit y) => some ((BitVec.ofNat 64 x).slt (BitVec.ofNat 64 y))
  | .ges (.lit x) (.lit y) => some (!(BitVec.ofNat 64 x).slt (BitVec.ofNat 64 y))
  | .eq (.ptr r o) (.ptr r' o') => if r = r' then some (BitVec.ofInt 64 o == BitVec.ofInt 64 o') else none
  | .ne (.ptr r o) (.ptr r' o') => if r = r' then some (BitVec.ofInt 64 o != BitVec.ofInt 64 o') else none
  | _ => none

def SBool.neg : SBool → SBool
  | .eq a b => .ne a b
  | .ne a b => .eq a b
  | .ltu a b => .geu a b
  | .geu a b => .ltu a b
  | .lts a b => .ges a b
  | .ges a b => .lts a b

/-- Literal of a word. -/
abbrev wlit (x : Word) : Sym := .lit x.toNat

def branchSym (S : SState) (pc : Nat) (c : SBool) (imm : BitVec 13) :
    Option (SState × StepExit × List Oblig) :=
  let t := (BitVec.ofNat 64 pc + sx imm).toNat
  let fall := (BitVec.ofNat 64 pc + 4).toNat
  match c.static? with
  | some true => if t % 4 = 0 then some (S, .next t, []) else none
  | some false => some (S, .next fall, [])
  | none => if t % 4 = 0 then some (S, .branch c t fall, []) else none

def loadI (img : Image) (S S1 : SState) (pc : Nat) (rd rs1 : Fin 32) (imm : BitVec 12) (n : Nat)
    (f : Sym → Sym) : Option (SState × StepExit × List Oblig) :=
  (loadSym img S (mkAdd (S.reg rs1) (wlit (sx imm))) n).map fun (v, ob) =>
    (S1.setReg rd (f v), .next (BitVec.ofNat 64 pc + 4).toNat, ob)

def storeI (S S1 : SState) (pc : Nat) (rs1 rs2 : Fin 32) (imm : BitVec 12) (n : Nat) :
    Option (SState × StepExit × List Oblig) :=
  (storeSym S1 (mkAdd (S.reg rs1) (wlit (sx imm))) n (S.reg rs2)).map fun (S2, ob) =>
    (S2, .next (BitVec.ofNat 64 pc + 4).toNat, ob)

/-- One instruction at `pc`. -/
def stepI (img : Image) (pc : Nat) (i : Instr) (S : SState) :
    Option (SState × StepExit × List Oblig) :=
  let S1 := { S with steps := S.steps + 1 }
  let fall := (BitVec.ofNat 64 pc + 4).toNat
  let wr (rd : Fin 32) (v : Sym) := some (S1.setReg rd v, StepExit.next fall, ([] : List Oblig))
  match i with
  | .lui rd imm => wr rd (wlit (sx (imm ++ (0 : BitVec 12))))
  | .auipc rd imm => wr rd (wlit (BitVec.ofNat 64 pc + sx (imm ++ (0 : BitVec 12))))
  | .jal rd imm =>
    let t := (BitVec.ofNat 64 pc + sx imm).toNat
    if t % 4 = 0 then
      some (S1.setReg rd (.lit fall), if rd.val = 1 then .call t fall else .next t, [])
    else none
  | .jalr rd rs1 imm =>
    let tgt := mkBin .and (mkAdd (S.reg rs1) (wlit (sx imm))) (wlit (~~~(1 : Word)))
    let S2 := S1.setReg rd (.lit fall)
    match tgt with
    | .lit t =>
      if t % 4 = 0 ∧ t < 2 ^ 64 then some (S2, if rd.val = 1 then .call t fall else .next t, [])
      else none
    | _ =>
      some (S2,
        if rd.val = 1 then .callInd tgt fall
        else if rd.val = 0 ∧ rs1.val = 1 ∧ imm = 0 then .ret tgt
        else .jumpInd tgt,
        [.aligned tgt 4])
  | .beq rs1 rs2 imm => branchSym S1 pc (.eq (S.reg rs1) (S.reg rs2)) imm
  | .bne rs1 rs2 imm => branchSym S1 pc (.ne (S.reg rs1) (S.reg rs2)) imm
  | .blt rs1 rs2 imm => branchSym S1 pc (.lts (S.reg rs1) (S.reg rs2)) imm
  | .bltu rs1 rs2 imm => branchSym S1 pc (.ltu (S.reg rs1) (S.reg rs2)) imm
  | .bgeu rs1 rs2 imm => branchSym S1 pc (.geu (S.reg rs1) (S.reg rs2)) imm
  | .lb rd rs1 imm => loadI img S S1 pc rd rs1 imm 1 (mkSext 8)
  | .lbu rd rs1 imm => loadI img S S1 pc rd rs1 imm 1 id
  | .lhu rd rs1 imm => loadI img S S1 pc rd rs1 imm 2 id
  | .lw rd rs1 imm => loadI img S S1 pc rd rs1 imm 4 (mkSext 32)
  | .ld rd rs1 imm => loadI img S S1 pc rd rs1 imm 8 id
  | .sb rs1 rs2 imm => storeI S S1 pc rs1 rs2 imm 1
  | .sh rs1 rs2 imm => storeI S S1 pc rs1 rs2 imm 2
  | .sw rs1 rs2 imm => storeI S S1 pc rs1 rs2 imm 4
  | .sd rs1 rs2 imm => storeI S S1 pc rs1 rs2 imm 8
  | .addi rd rs1 imm => wr rd (mkAdd (S.reg rs1) (wlit (sx imm)))
  | .andi rd rs1 imm => wr rd (mkBin .and (S.reg rs1) (wlit (sx imm)))
  | .xori rd rs1 imm => wr rd (mkBin .xor (S.reg rs1) (wlit (sx imm)))
  | .sltiu rd rs1 imm => wr rd (mkBin .sltu (S.reg rs1) (wlit (sx imm)))
  | .slli rd rs1 sh => wr rd (mkBin .sll (S.reg rs1) (.lit sh.toNat))
  | .srli rd rs1 sh => wr rd (mkBin .srl (S.reg rs1) (.lit sh.toNat))
  | .add rd rs1 rs2 => wr rd (mkAdd (S.reg rs1) (S.reg rs2))
  | .sub rd rs1 rs2 => wr rd (mkSub (S.reg rs1) (S.reg rs2))
  | .and rd rs1 rs2 => wr rd (mkBin .and (S.reg rs1) (S.reg rs2))
  | .or rd rs1 rs2 => wr rd (mkBin .or (S.reg rs1) (S.reg rs2))
  | .sll rd rs1 rs2 => wr rd (mkBin .sll (S.reg rs1) (S.reg rs2))
  | .sltu rd rs1 rs2 => wr rd (mkBin .sltu (S.reg rs1) (S.reg rs2))
  | .mul rd rs1 rs2 => wr rd (mkBin .mul (S.reg rs1) (S.reg rs2))
  | .mulhu rd rs1 rs2 => wr rd (mkBin .mulhu (S.reg rs1) (S.reg rs2))
  | .xor rd rs1 rs2 => wr rd (mkBin .xor (S.reg rs1) (S.reg rs2))
  | .addiw rd rs1 imm => wr rd (mkSext 32 (mkAdd (S.reg rs1) (wlit (sx imm))))
  | .bge rs1 rs2 imm => branchSym S1 pc (.ges (S.reg rs1) (S.reg rs2)) imm
  | .lwu rd rs1 imm => loadI img S S1 pc rd rs1 imm 4 id
  | .srliw rd rs1 sh =>
    wr rd (mkSext 32 (mkBin .srl (mkBin .and (S.reg rs1) (.lit 0xffffffff)) (.lit sh.toNat)))
  | .subw rd rs1 rs2 => wr rd (mkSext 32 (mkSub (S.reg rs1) (S.reg rs2)))
  | .lh rd rs1 imm => loadI img S S1 pc rd rs1 imm 2 (mkSext 16)
  | .ori rd rs1 imm => wr rd (mkBin .or (S.reg rs1) (wlit (sx imm)))
  | .srl rd rs1 rs2 => wr rd (mkBin .srl (S.reg rs1) (S.reg rs2))
  | .divu rd rs1 rs2 => wr rd (mkBin .divu (S.reg rs1) (S.reg rs2))
  | .remu rd rs1 rs2 => wr rd (mkBin .remu (S.reg rs1) (S.reg rs2))
  | .slliw rd rs1 sh => wr rd (mkSext 32 (mkBin .sll (S.reg rs1) (.lit sh.toNat)))
  | .slti rd rs1 imm => wr rd (mkBin .slt (S.reg rs1) (wlit (sx imm)))
  | .slt rd rs1 rs2 => wr rd (mkBin .slt (S.reg rs1) (S.reg rs2))
  | .srai rd rs1 sh => wr rd (mkBin .sra (S.reg rs1) (.lit sh.toNat))
  | .rev8 rd rs1 => wr rd (mkBin .rev8 (S.reg rs1) (.lit 0))
  | .maxu rd rs1 rs2 => wr rd (mkBin .maxu (S.reg rs1) (S.reg rs2))
  | .pack rd rs1 rs2 => wr rd (mkBin .pack (S.reg rs1) (S.reg rs2))
  | .packh rd rs1 rs2 => wr rd (mkBin .packh (S.reg rs1) (S.reg rs2))
  | .bext rd rs1 rs2 => wr rd (mkBin .bext (S.reg rs1) (S.reg rs2))
  | .bset rd rs1 rs2 => wr rd (mkBin .bset (S.reg rs1) (S.reg rs2))
  | .bclri rd rs1 sh => wr rd (mkBin .bclr (S.reg rs1) (.lit sh.toNat))
  | .clz rd rs1 => wr rd (mkBin .clz (S.reg rs1) (.lit 0))

/-- Fetch and decode at `pc` (inside `.text`, 4-aligned). -/
def fetchI (img : Image) (pc : Nat) : Option Instr :=
  if Layout.textLo ≤ pc ∧ pc < Layout.textHi ∧ pc % 4 = 0 then
    match img.word? pc with
    | some w => decodeNat w
    | none => none
  else none

def go (img : Image) (cuts : List Nat) :
    Nat → Bool → Nat → SState → List SBool → List Oblig → Option (List Leaf)
  | 0, _, _, _, _, _ => none
  | fuel + 1, started, pc, S, cs, os =>
    if (started && cuts.contains pc) || pc == Layout.memcpyEntry then some [⟨S, .at pc, cs, os⟩]
    else
      match fetchI img pc with
      | none => some [⟨S, .at pc, cs, os ++ [.unreachable pc]⟩]
      | some i =>
        match stepI img pc i S with
        | none => none
        | some (S', e, ob) =>
          let os' := os ++ ob
          match e with
          | .next pc' => go img cuts fuel true pc' S' cs os'
          | .branch c t f =>
            match go img cuts fuel true t S' (cs ++ [c]) os',
                  go img cuts fuel true f S' (cs ++ [c.neg]) os' with
            | some l₁, some l₂ => some (l₁ ++ l₂)
            | _, _ => none
          | .call t r => some [⟨S', .call t r, cs, os'⟩]
          | .callInd t r => some [⟨S', .callInd t r, cs, os'⟩]
          | .ret t => some [⟨S', .ret t, cs, os'⟩]
          | .jumpInd t => some [⟨S', .jumpInd t, cs, os'⟩]

def run (img : Image) (cuts : List Nat) (fuel pc : Nat) (S : SState) : Option (List Leaf) :=
  go img cuts fuel false pc S [] []

end ZesuExec.Sym
