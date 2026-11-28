import ZesuExec.Image

/-!
# ZisK services: common vocabulary (plan S14)

A *service step* is what ZisK does at an instruction sequence that its transpiler replaces by a
precompile (`/home/cody/zisk/core/src/riscv2zisk_context.rs`). Each CSR of the registry
(`ZesuExec/Service/*.lean`, one file per CSR number) gives a partial function
`Image → Machine → Option SvcEffect`: `none` outside the pattern or outside the domain where
the definition is stated.

`SvcEffect.apply` is the machine after the step: at most one register written, memory replaced by
`mem` (which may differ from the old memory only at `addrs`, all in RAM, see `SvcEffect.Framed`),
`pc` set, `cost` RISC-V instructions consumed.
-/

namespace ZesuExec

-- ZisK system-area addresses (`/home/cody/zisk/core/src/mem.rs`).
namespace Zisk
/-- `SYS_ADDR = RAM_ADDR` (`mem.rs:113`, `:109`). -/
def sysAddr : Nat := 0xa0000000
/-- `OUTPUT_ADDR = SYS_ADDR + SYS_SIZE` (`mem.rs:117`). -/
def outputAddr : Nat := 0xa0010000
/-- `INPUT_ADDR` (`mem.rs:103`). -/
def inputAddr : Nat := 0x40000000
/-- `CSR_ADDR = SYS_ADDR + 0x8000` (`mem.rs:151`): CSR `c` lives at `CSR_ADDR + 8 c`. -/
def csrAddr : Nat := 0xa0008000
/-- `ARCH_ID_ZISK` (`mem.rs:143`). -/
def archId : Nat := 0xFFFEEEE
/-- `CAUSE_EXIT` (`a7` value of the exit `ecall`; `riscv2zisk_context.rs:67`, trap handler
`:2486-2497`, output loop `:2276` `add_entry_exit_jmp`). -/
def causeExit : Nat := 93
end Zisk

/-- The effect of one service step. -/
structure SvcEffect where
  rd    : Fin 32 := 0
  v     : Word := 0
  addrs : List Nat := []
  mem   : Word → Option Byte
  pc    : Word
  cost  : Nat

/-- The machine after the step. -/
def SvcEffect.apply (e : SvcEffect) (m : Machine) : Machine :=
  { m.setReg e.rd e.v with mem := e.mem, pc := e.pc }

/-- `e` writes only the RAM addresses `addrs` and keeps every present byte present. -/
def SvcEffect.Framed (e : SvcEffect) (m : Machine) : Prop :=
  (∀ x : Word, x.toNat ∉ e.addrs → e.mem x = m.mem x) ∧
  (∀ a ∈ e.addrs, Layout.ramLo ≤ a ∧ a < 2 ^ 64) ∧
  (∀ x : Word, (m.mem x).isSome → (e.mem x).isSome)

namespace Svc
open Decode

/-- Instruction fields of a 32-bit word. -/
abbrev opc (w : Nat) : Nat := field w 0 7
abbrev rdF (w : Nat) : Nat := field w 7 5
abbrev f3 (w : Nat) : Nat := field w 12 3
abbrev rs1F (w : Nat) : Nat := field w 15 5
abbrev rs2F (w : Nat) : Nat := field w 20 5
abbrev f7 (w : Nat) : Nat := field w 25 7
/-- CSR number of a `csrr*` word. -/
abbrev csrF (w : Nat) : Nat := field w 20 12
/-- I-type immediate as an integer. -/
def immInt (w : Nat) : Int := (immI w).toInt

/-- `csrrs x0, csr, rs` with `rs ≠ x0` (`csrs csr, rs`; ZisK's `csrrs`, `rd = 0` branch,
`riscv2zisk_context.rs:1326`; `rs = rd = 0` is a no-op, `:1277`). -/
def isCsrs (w csr : Nat) : Bool :=
  w < 2 ^ 32 && opc w == 0x73 && f3 w == 2 && rdF w == 0 && rs1F w != 0 && csrF w == csr

/-- `addi x0, rs, imm`. -/
def isAddiX0 (w : Nat) : Bool := w < 2 ^ 32 && opc w == 0x13 && f3 w == 0 && rdF w == 0

/-- `add x0, rs1, rs2`. -/
def isAddX0 (w : Nat) : Bool :=
  w < 2 ^ 32 && opc w == 0x33 && f3 w == 0 && f7 w == 0 && rdF w == 0

/-- The service words are fetched like instructions: `.text`, 4-aligned. -/
def fetch (img : Image) (pc : Nat) : Option Nat :=
  if Layout.textLo ≤ pc ∧ pc < Layout.textHi ∧ pc % 4 = 0 then img.word? pc else none

end Svc

namespace Machine

/-- All `n` bytes at `a, a+1, …` are present. -/
def present (mem : Word → Option Byte) (a n : Nat) : Bool := (readBytes mem a n).isSome

/-- `[d, d+n)` filled with `b`. -/
def fillMem (mem : Word → Option Byte) (d n : Nat) (b : Byte) : Word → Option Byte :=
  fun x => if d ≤ x.toNat ∧ x.toNat < d + n then some b else mem x

/-- `n` bytes copied from `s` to `d`, reading the old memory (overlap allowed, as ZisK's
`Mem::memcpy`, `core/src/mem.rs:888-926`; `d = s` or `n = 0` leaves memory alone). -/
def copyMem (mem : Word → Option Byte) (d s n : Nat) : Word → Option Byte :=
  fun x =>
    let a := x.toNat
    if n ≠ 0 ∧ d ≠ s ∧ d ≤ a ∧ a < d + n then mem (BitVec.ofNat 64 (s + a - d)) else mem x

/-- `[d, d+n)` overwritten with `bs` (`0` past its end). -/
def putBytes (mem : Word → Option Byte) (d n : Nat) (bs : List Byte) : Word → Option Byte :=
  fun x => if d ≤ x.toNat ∧ x.toNat < d + n then some (bs.getD (x.toNat - d) 0) else mem x

/-- A source range that may be read: readable and present. -/
def srcOk (mem : Word → Option Byte) (a n : Nat) : Bool := readable a n && present mem a n

/-- A destination range that may be written: RAM and present. -/
def dstOk (mem : Word → Option Byte) (a n : Nat) : Bool := writable a n && present mem a n

end Machine

end ZesuExec
