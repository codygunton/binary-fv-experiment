/-!
# Concrete RV64 machine for the Zesu spike

`Machine` is the concrete state the symbolic executor (`ZesuExec.Sym.run`) is proved sound
against, and that `ZesuExec.Sail.Rel` relates to the Sail model's `SequentialState`.
Memory is partial: an absent byte makes every access to it fault (`none`).
-/

namespace ZesuExec

abbrev Word := BitVec 64
abbrev Byte := BitVec 8

-- ZisK memory map (half-open intervals).
namespace Layout
def textLo : Nat := 0x80000000
def textHi : Nat := 0x8010fd78
def rodataLo : Nat := 0x8010fd80
def rodataHi : Nat := 0x80118678
def inputLo : Nat := 0x40000000
def inputHi : Nat := 0x80000000
def ramLo : Nat := 0xa0000000
def ramHi : Nat := 0xc0000000
def memcpyEntry : Nat := 0x800e06c0
def extraParams : Nat := 0xa0400f00
end Layout

structure Machine where
  regs : Fin 32 → Word
  pc   : Word
  /-- absent byte: any access faults -/
  mem  : Word → Option Byte

namespace Machine

def reg (m : Machine) (i : Fin 32) : Word := if i.val = 0 then 0 else m.regs i

/-- No effect for `i = 0`. -/
def setReg (m : Machine) (i : Fin 32) (v : Word) : Machine :=
  if i.val = 0 then m else { m with regs := fun j => if j = i then v else m.regs j }

/-- `lo ≤ a` and `a + n ≤ hi`. -/
def inRange (lo hi a n : Nat) : Bool := lo ≤ a && a + n ≤ hi

/-- `[a, a+n)` lies inside one of rodata, input, RAM. -/
def readable (a n : Nat) : Bool :=
  inRange Layout.rodataLo Layout.rodataHi a n || inRange Layout.inputLo Layout.inputHi a n ||
    inRange Layout.ramLo Layout.ramHi a n

/-- `[a, a+n)` lies inside RAM. -/
def writable (a n : Nat) : Bool := inRange Layout.ramLo Layout.ramHi a n

/-- The `n` bytes at `a, a+1, …`, if all present. -/
def readBytes (mem : Word → Option Byte) (a : Nat) : Nat → Option (List Byte)
  | 0 => some []
  | n + 1 =>
    match mem (BitVec.ofNat 64 a), readBytes mem (a + 1) n with
    | some b, some bs => some (b :: bs)
    | _, _ => none

/-- Little-endian, zero-extended. -/
def ofBytesLE : List Byte → Word
  | [] => 0
  | b :: bs => b.zeroExtend 64 ||| (ofBytesLE bs <<< 8)

/-- Write the low `n` bytes of `v` little-endian at `a`. -/
def writeBytes (mem : Word → Option Byte) (a : Nat) (v : Word) : Nat → (Word → Option Byte)
  | 0 => mem
  | n + 1 => fun x =>
    if x = BitVec.ofNat 64 a then some (v.extractLsb' 0 8)
    else writeBytes mem (a + 1) (v >>> 8) n x

/-- Naturally aligned load of `n` bytes from rodata, input or RAM, all bytes present. -/
def load (m : Machine) (a : Word) (n : Nat) : Option Word :=
  if a.toNat % n = 0 ∧ readable a.toNat n = true then
    (readBytes m.mem a.toNat n).map ofBytesLE
  else none

/-- Naturally aligned store of the low `n` bytes of `v` into RAM, all bytes present. -/
def store (m : Machine) (a : Word) (n : Nat) (v : Word) : Option Machine :=
  if a.toNat % n = 0 ∧ writable a.toNat n = true ∧ (readBytes m.mem a.toNat n).isSome then
    some { m with mem := writeBytes m.mem a.toNat v n }
  else none

end Machine
end ZesuExec
