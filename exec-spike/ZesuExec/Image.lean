import ZesuExec.Decode

/-!
# Program image and the concrete step

`Image` holds the `.text` words of the functions in scope and the `.rodata` byte ranges they
read. `step` fetches from the image, decodes with `decodeNat` and executes one of the 33 forms.
-/

namespace ZesuExec

/-- 32-bit instruction words starting at `base`. -/
structure Seg where
  base : Nat
  words : List Nat

/-- Read-only bytes starting at `base`. -/
structure RoSeg where
  base : Nat
  bytes : List Nat

structure Image where
  text : List Seg
  rodata : List RoSeg

def Seg.word? (s : Seg) (pc : Nat) : Option Nat :=
  if s.base ≤ pc ∧ (pc - s.base) % 4 = 0 then s.words[(pc - s.base) / 4]? else none

def RoSeg.byte? (s : RoSeg) (a : Nat) : Option Nat :=
  if s.base ≤ a then s.bytes[a - s.base]? else none

/-- Needs `(pc - base) % 4 = 0` for the segment that holds `pc`. -/
def Image.word? (img : Image) (pc : Nat) : Option Nat := img.text.findSome? (·.word? pc)

def Image.rodataByte? (img : Image) (a : Nat) : Option Nat := img.rodata.findSome? (·.byte? a)

namespace Machine

/-- Sign-extend a `w`-bit immediate to 64 bits. -/
abbrev sx {w : Nat} (x : BitVec w) : Word := x.signExtend 64

/-- Control transfer: the target must be a multiple of 4. -/
def jumpTo (m : Machine) (t : Word) : Option Machine :=
  if t.toNat % 4 = 0 then some { m with pc := t } else none

def advance (m : Machine) : Machine := { m with pc := m.pc + 4 }

def branch (m : Machine) (c : Bool) (imm : BitVec 13) : Option Machine :=
  if c then m.jumpTo (m.pc + sx imm) else some m.advance

def loadInto (m : Machine) (rd rs1 : Fin 32) (imm : BitVec 12) (n : Nat) (f : Word → Word) :
    Option Machine :=
  (m.load (m.reg rs1 + sx imm) n).map fun v => (m.setReg rd (f v)).advance

def storeFrom (m : Machine) (rs1 rs2 : Fin 32) (imm : BitVec 12) (n : Nat) : Option Machine :=
  (m.store (m.reg rs1 + sx imm) n (m.reg rs2)).map Machine.advance

def writeReg (m : Machine) (rd : Fin 32) (v : Word) : Option Machine := some (m.setReg rd v).advance

/-- Effect of one decoded instruction. -/
def exec (m : Machine) : Instr → Option Machine
  | .lui rd imm => m.writeReg rd (sx (imm ++ (0 : BitVec 12)))
  | .auipc rd imm => m.writeReg rd (m.pc + sx (imm ++ (0 : BitVec 12)))
  | .jal rd imm => ((m.setReg rd (m.pc + 4)).jumpTo (m.pc + sx imm))
  | .jalr rd rs1 imm =>
    (m.setReg rd (m.pc + 4)).jumpTo ((m.reg rs1 + sx imm) &&& ~~~(1 : Word))
  | .beq rs1 rs2 imm => m.branch (m.reg rs1 == m.reg rs2) imm
  | .bne rs1 rs2 imm => m.branch (m.reg rs1 != m.reg rs2) imm
  | .blt rs1 rs2 imm => m.branch ((m.reg rs1).slt (m.reg rs2)) imm
  | .bltu rs1 rs2 imm => m.branch ((m.reg rs1).ult (m.reg rs2)) imm
  | .bgeu rs1 rs2 imm => m.branch (!(m.reg rs1).ult (m.reg rs2)) imm
  | .lb rd rs1 imm => m.loadInto rd rs1 imm 1 fun v => (v.truncate 8).signExtend 64
  | .lbu rd rs1 imm => m.loadInto rd rs1 imm 1 id
  | .lhu rd rs1 imm => m.loadInto rd rs1 imm 2 id
  | .lw rd rs1 imm => m.loadInto rd rs1 imm 4 fun v => (v.truncate 32).signExtend 64
  | .ld rd rs1 imm => m.loadInto rd rs1 imm 8 id
  | .sb rs1 rs2 imm => m.storeFrom rs1 rs2 imm 1
  | .sh rs1 rs2 imm => m.storeFrom rs1 rs2 imm 2
  | .sw rs1 rs2 imm => m.storeFrom rs1 rs2 imm 4
  | .sd rs1 rs2 imm => m.storeFrom rs1 rs2 imm 8
  | .addi rd rs1 imm => m.writeReg rd (m.reg rs1 + sx imm)
  | .andi rd rs1 imm => m.writeReg rd (m.reg rs1 &&& sx imm)
  | .xori rd rs1 imm => m.writeReg rd (m.reg rs1 ^^^ sx imm)
  | .sltiu rd rs1 imm => m.writeReg rd (if (m.reg rs1).ult (sx imm) then 1 else 0)
  | .slli rd rs1 sh => m.writeReg rd (m.reg rs1 <<< sh.toNat)
  | .srli rd rs1 sh => m.writeReg rd (m.reg rs1 >>> sh.toNat)
  | .add rd rs1 rs2 => m.writeReg rd (m.reg rs1 + m.reg rs2)
  | .sub rd rs1 rs2 => m.writeReg rd (m.reg rs1 - m.reg rs2)
  | .and rd rs1 rs2 => m.writeReg rd (m.reg rs1 &&& m.reg rs2)
  | .or rd rs1 rs2 => m.writeReg rd (m.reg rs1 ||| m.reg rs2)
  | .sll rd rs1 rs2 => m.writeReg rd (m.reg rs1 <<< ((m.reg rs2).toNat % 64))
  | .sltu rd rs1 rs2 => m.writeReg rd (if (m.reg rs1).ult (m.reg rs2) then 1 else 0)
  | .mul rd rs1 rs2 => m.writeReg rd (m.reg rs1 * m.reg rs2)
  | .mulhu rd rs1 rs2 =>
    m.writeReg rd (BitVec.ofNat 64 ((m.reg rs1).toNat * (m.reg rs2).toNat / 2 ^ 64))
  | .xor rd rs1 rs2 => m.writeReg rd (m.reg rs1 ^^^ m.reg rs2)
  | .addiw rd rs1 imm => m.writeReg rd (((m.reg rs1 + sx imm).setWidth 32).signExtend 64)
  | .bge rs1 rs2 imm => m.branch (!(m.reg rs1).slt (m.reg rs2)) imm
  | .lwu rd rs1 imm => m.loadInto rd rs1 imm 4 id
  | .srliw rd rs1 sh => m.writeReg rd (((m.reg rs1).setWidth 32 >>> sh.toNat).signExtend 64)
  | .subw rd rs1 rs2 =>
    m.writeReg rd (((m.reg rs1).setWidth 32 - (m.reg rs2).setWidth 32).signExtend 64)
  | .lh rd rs1 imm => m.loadInto rd rs1 imm 2 fun v => (v.truncate 16).signExtend 64

end Machine

/-- Fetch (inside `.text`, 4-aligned), decode, execute. -/
def step (img : Image) (m : Machine) : Option Machine :=
  if Layout.textLo ≤ m.pc.toNat ∧ m.pc.toNat < Layout.textHi ∧ m.pc.toNat % 4 = 0 then
    match img.word? m.pc.toNat with
    | some w => match decodeNat w with
      | some i => m.exec i
      | none => none
    | none => none
  else none

end ZesuExec
