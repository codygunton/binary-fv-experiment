import ZesuExec.Machine

/-!
# The 33 RV64IM instruction forms used by F0–F6, `alloc` and `free`

`decodeNat` works on `Nat` with `/` and `%` so that kernel evaluation uses GMP arithmetic.
Every other word decodes to `none`.
-/

namespace ZesuExec

inductive Instr
  | lui (rd : Fin 32) (imm : BitVec 20)
  | auipc (rd : Fin 32) (imm : BitVec 20)
  | jal (rd : Fin 32) (imm : BitVec 21)
  | jalr (rd rs1 : Fin 32) (imm : BitVec 12)
  | beq (rs1 rs2 : Fin 32) (imm : BitVec 13)
  | bne (rs1 rs2 : Fin 32) (imm : BitVec 13)
  | blt (rs1 rs2 : Fin 32) (imm : BitVec 13)
  | bltu (rs1 rs2 : Fin 32) (imm : BitVec 13)
  | bgeu (rs1 rs2 : Fin 32) (imm : BitVec 13)
  | lb (rd rs1 : Fin 32) (imm : BitVec 12)
  | lbu (rd rs1 : Fin 32) (imm : BitVec 12)
  | lhu (rd rs1 : Fin 32) (imm : BitVec 12)
  | lw (rd rs1 : Fin 32) (imm : BitVec 12)
  | ld (rd rs1 : Fin 32) (imm : BitVec 12)
  | sb (rs1 rs2 : Fin 32) (imm : BitVec 12)
  | sh (rs1 rs2 : Fin 32) (imm : BitVec 12)
  | sw (rs1 rs2 : Fin 32) (imm : BitVec 12)
  | sd (rs1 rs2 : Fin 32) (imm : BitVec 12)
  | addi (rd rs1 : Fin 32) (imm : BitVec 12)
  | andi (rd rs1 : Fin 32) (imm : BitVec 12)
  | xori (rd rs1 : Fin 32) (imm : BitVec 12)
  | sltiu (rd rs1 : Fin 32) (imm : BitVec 12)
  | slli (rd rs1 : Fin 32) (shamt : BitVec 6)
  | srli (rd rs1 : Fin 32) (shamt : BitVec 6)
  | add (rd rs1 rs2 : Fin 32)
  | sub (rd rs1 rs2 : Fin 32)
  | and (rd rs1 rs2 : Fin 32)
  | or (rd rs1 rs2 : Fin 32)
  | sll (rd rs1 rs2 : Fin 32)
  | sltu (rd rs1 rs2 : Fin 32)
  | mul (rd rs1 rs2 : Fin 32)
  | mulhu (rd rs1 rs2 : Fin 32)
  | xor (rd rs1 rs2 : Fin 32)
  | addiw (rd rs1 : Fin 32) (imm : BitVec 12)
  | bge (rs1 rs2 : Fin 32) (imm : BitVec 13)
  deriving DecidableEq, Repr

namespace Decode

/-- Bits `[lo, lo+len)` of `w`. -/
def field (w lo len : Nat) : Nat := (w / 2 ^ lo) % 2 ^ len

def reg (w lo : Nat) : Fin 32 := ⟨field w lo 5, Nat.mod_lt _ (by decide)⟩

def immI (w : Nat) : BitVec 12 := BitVec.ofNat 12 (field w 20 12)
def immS (w : Nat) : BitVec 12 := BitVec.ofNat 12 (field w 25 7 * 32 + field w 7 5)
def immB (w : Nat) : BitVec 13 :=
  BitVec.ofNat 13 (field w 31 1 * 4096 + field w 7 1 * 2048 + field w 25 6 * 32 + field w 8 4 * 2)
def immJ (w : Nat) : BitVec 21 :=
  BitVec.ofNat 21
    (field w 31 1 * 1048576 + field w 12 8 * 4096 + field w 20 1 * 2048 + field w 21 10 * 2)
def immU (w : Nat) : BitVec 20 := BitVec.ofNat 20 (field w 12 20)

end Decode

open Decode in
/-- Decoder for the 33 forms; any other word (including words `≥ 2^32`) is `none`. -/
def decodeNat (w : Nat) : Option Instr :=
  if w < 4294967296 then
    let opc := field w 0 7
    let rd := reg w 7
    let f3 := field w 12 3
    let rs1 := reg w 15
    let rs2 := reg w 20
    let f7 := field w 25 7
    if opc = 0x37 then some (.lui rd (immU w))
    else if opc = 0x17 then some (.auipc rd (immU w))
    else if opc = 0x6f then some (.jal rd (immJ w))
    else if opc = 0x67 then (if f3 = 0 then some (.jalr rd rs1 (immI w)) else none)
    else if opc = 0x63 then
      if f3 = 0 then some (.beq rs1 rs2 (immB w))
      else if f3 = 1 then some (.bne rs1 rs2 (immB w))
      else if f3 = 4 then some (.blt rs1 rs2 (immB w))
      else if f3 = 5 then some (.bge rs1 rs2 (immB w))
      else if f3 = 6 then some (.bltu rs1 rs2 (immB w))
      else if f3 = 7 then some (.bgeu rs1 rs2 (immB w))
      else none
    else if opc = 0x03 then
      if f3 = 0 then some (.lb rd rs1 (immI w))
      else if f3 = 4 then some (.lbu rd rs1 (immI w))
      else if f3 = 5 then some (.lhu rd rs1 (immI w))
      else if f3 = 2 then some (.lw rd rs1 (immI w))
      else if f3 = 3 then some (.ld rd rs1 (immI w))
      else none
    else if opc = 0x23 then
      if f3 = 0 then some (.sb rs1 rs2 (immS w))
      else if f3 = 1 then some (.sh rs1 rs2 (immS w))
      else if f3 = 2 then some (.sw rs1 rs2 (immS w))
      else if f3 = 3 then some (.sd rs1 rs2 (immS w))
      else none
    else if opc = 0x13 then
      if f3 = 0 then some (.addi rd rs1 (immI w))
      else if f3 = 4 then some (.xori rd rs1 (immI w))
      else if f3 = 7 then some (.andi rd rs1 (immI w))
      else if f3 = 3 then some (.sltiu rd rs1 (immI w))
      else if f3 = 1 then
        (if field w 26 6 = 0 then some (.slli rd rs1 (BitVec.ofNat 6 (field w 20 6))) else none)
      else if f3 = 5 then
        (if field w 26 6 = 0 then some (.srli rd rs1 (BitVec.ofNat 6 (field w 20 6))) else none)
      else none
    else if opc = 0x33 then
      if f7 = 0 then
        if f3 = 0 then some (.add rd rs1 rs2)
        else if f3 = 1 then some (.sll rd rs1 rs2)
        else if f3 = 3 then some (.sltu rd rs1 rs2)
        else if f3 = 4 then some (.xor rd rs1 rs2)
        else if f3 = 6 then some (.or rd rs1 rs2)
        else if f3 = 7 then some (.and rd rs1 rs2)
        else none
      else if f7 = 0x20 then (if f3 = 0 then some (.sub rd rs1 rs2) else none)
      else if f7 = 1 then
        if f3 = 0 then some (.mul rd rs1 rs2)
        else if f3 = 3 then some (.mulhu rd rs1 rs2)
        else none
      else none
    else if opc = 0x1b then
      if f3 = 0 then some (.addiw rd rs1 (immI w))
      else none
    else none
  else none

def decodeWord (w : BitVec 32) : Option Instr := decodeNat w.toNat

/-- Constructor name, used by the decode table check in `ZesuExec.Test.Decode`. -/
def Instr.mnemonic : Instr → String
  | .lui .. => "lui" | .auipc .. => "auipc" | .jal .. => "jal" | .jalr .. => "jalr"
  | .beq .. => "beq" | .bne .. => "bne" | .blt .. => "blt" | .bltu .. => "bltu"
  | .bgeu .. => "bgeu" | .lb .. => "lb" | .lbu .. => "lbu" | .lhu .. => "lhu"
  | .lw .. => "lw" | .ld .. => "ld" | .sb .. => "sb" | .sh .. => "sh" | .sw .. => "sw"
  | .sd .. => "sd" | .addi .. => "addi" | .andi .. => "andi" | .xori .. => "xori"
  | .sltiu .. => "sltiu" | .slli .. => "slli" | .srli .. => "srli" | .add .. => "add"
  | .sub .. => "sub" | .and .. => "and" | .or .. => "or" | .sll .. => "sll"
  | .sltu .. => "sltu" | .mul .. => "mul" | .mulhu .. => "mulhu" | .xor .. => "xor"
  | .addiw .. => "addiw" | .bge .. => "bge"

end ZesuExec
