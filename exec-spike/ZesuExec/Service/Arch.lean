import ZesuExec.Service.Basic

/-!
# CSR `0xf12` (`marchid`), the exit `ecall`, and ZisK's start-up state

* `csrrs rd, csr, x0` with `rd ≠ x0` reads CSR `csr` from memory: `rd := mem64[CSR_ADDR + 8 csr]`
  (`core/src/riscv2zisk_context.rs:1408-1426`; `CSR_ADDR`, `core/src/mem.rs:151`). Only `marchid`
  (`0xf12`, `mem.rs:157`) is defined here; `_start` reads it (`0x800f5b48`).
* The ROM's start-up code (`add_entry_exit_jmp`, `riscv2zisk_context.rs:2276-2340`) stores
  `ARCH_ID_ZISK` at `CSR_ADDR + 8·0xf12` (`:2283-2293`), the trap vector, `x10 = INPUT_ADDR`
  (`:2306-2317`) and `x11 = OUTPUT_ADDR` (`:2319-2330`), then calls the program. `ZiskBoot` states
  the facts a program can observe.
* `ecall` jumps to the trap handler (`:1117-1128`); with `x17 = CAUSE_EXIT` the handler
  (`:2486-2497`) runs the output loop, which publishes the 32 little-endian `u64` at
  `OUTPUT_ADDR` (`:2355-2470`), and ends. `ziskExit` is that output; the machine has no step
  after it.
-/

namespace ZesuExec
open Machine

/-- `csrrs rd, 0xf12, x0` with `rd ≠ x0` (`csrr rd, marchid`). -/
def Svc.isMarchidRead (w : Nat) : Bool :=
  w < 2 ^ 32 && Svc.opc w == 0x73 && Svc.f3 w == 2 && Svc.rdF w != 0 && Svc.rs1F w == 0 &&
    Svc.csrF w == 0xf12

/-- Where ZisK keeps `marchid`. -/
def Zisk.marchidAddr : Nat := Zisk.csrAddr + 8 * 0xf12

/-- The CSR `0xf12` read at `m.pc`. -/
def csrF12 (img : Image) (m : Machine) : Option SvcEffect :=
  match Svc.fetch img m.pc.toNat with
  | some w0 =>
    if Svc.isMarchidRead w0 then
      match m.load (BitVec.ofNat 64 Zisk.marchidAddr) 8 with
      | some v => some { rd := Decode.reg w0 7, v := v, mem := m.mem, pc := m.pc + 4, cost := 1 }
      | none => none
    else none
  | none => none

/-- The exit `ecall` at `m.pc`: the public output, 256 bytes at `OUTPUT_ADDR`. -/
def ziskExit (img : Image) (m : Machine) : Option (List Byte) :=
  if Svc.fetch img m.pc.toNat = some 0x73 ∧ m.reg 17 = BitVec.ofNat 64 Zisk.causeExit then
    readBytes m.mem Zisk.outputAddr 256
  else none

/-- What ZisK's start-up code establishes before the program's first instruction. -/
def ZiskBoot (m : Machine) : Prop :=
  m.load (BitVec.ofNat 64 Zisk.marchidAddr) 8 = some (BitVec.ofNat 64 Zisk.archId) ∧
  m.reg 10 = BitVec.ofNat 64 Zisk.inputAddr ∧ m.reg 11 = BitVec.ofNat 64 Zisk.outputAddr

end ZesuExec
