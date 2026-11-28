import ZesuExec.Service.Basic

/-!
# CSR `0x816`: ZisK DMA `memset` (`SYSCALL_DMA_MEMSET_ID`, `definitions/src/syscall.rs:27`)

Two transpiler patterns (`core/src/riscv2zisk_context.rs:1920-1992`,
`transpile_dma_memset_pattern`), each one `dma_xmemset` (`core/src/operations/dma_memset.rs:8-82`,
`Mem::memset`, `core/src/mem.rs:946-958`: `count = 0` does nothing) whose result `c = dst` goes to
the `rd` of the first `addi` (here required to be `x0`):

* register form, `csrs 0x816, rdst; addi x0, rcount, byte` (`:1960-1982`): fill
  `[rdst, rdst + rcount)` with `byte`; continue 8 bytes later;
* immediate form, `csrsi 0x816, 2; addi x0, rdst, count; addi _, _, byte` (`:1925-1951`; the
  `csrsi` reaches it through `csrrsi`, `:1711-1715`): fill `[rdst, rdst + count)`; continue 12
  bytes later.

ZisK asserts `0 ≤ byte ≤ 0xff` (`:1941`, `:1972`); the count immediate is used as `u64`, so a
negative one is outside the domain here.
-/

namespace ZesuExec
open Machine

/-- `csrrsi x0, 0x816, 2`. -/
def Svc.isCsrsi816 (w : Nat) : Bool :=
  w < 2 ^ 32 && Svc.opc w == 0x73 && Svc.f3 w == 6 && Svc.rdF w == 0 && Svc.rs1F w == 2 &&
    Svc.csrF w == 0x816

/-- `addi _, _, imm` with `0 ≤ imm ≤ 0xff`. -/
def Svc.byteImm? (w : Nat) : Option Byte :=
  if w < 2 ^ 32 ∧ Svc.opc w = 0x13 ∧ Svc.f3 w = 0 ∧ 0 ≤ Svc.immInt w ∧ Svc.immInt w ≤ 0xff then
    some (BitVec.ofNat 8 (Svc.immInt w).toNat)
  else none

/-- One fill of `[d, d+n)` with `b`, continuing at `pc + len`. -/
def memsetEffect (m : Machine) (d n : Nat) (b : Byte) (len : Nat) : Option SvcEffect :=
  if n == 0 || dstOk m.mem d n then
    some { addrs := (List.range n).map (d + ·), mem := fillMem m.mem d n b,
           pc := m.pc + BitVec.ofNat 64 len, cost := len / 4 }
  else none

/-- The CSR `0x816` service step at `m.pc`. -/
def csr816 (img : Image) (m : Machine) : Option SvcEffect :=
  match Svc.fetch img m.pc.toNat, Svc.fetch img (m.pc.toNat + 4) with
  | some w0, some w1 =>
    if Svc.isCsrs w0 0x816 ∧ Svc.isAddiX0 w1 then
      match Svc.byteImm? w1 with
      | some b =>
        memsetEffect m (m.reg (Decode.reg w0 15)).toNat (m.reg (Decode.reg w1 15)).toNat b 8
      | none => none
    else if Svc.isCsrsi816 w0 ∧ Svc.isAddiX0 w1 ∧ 0 ≤ Svc.immInt w1 then
      match Svc.fetch img (m.pc.toNat + 8) with
      | some w2 =>
        match Svc.byteImm? w2 with
        | some b =>
          memsetEffect m (m.reg (Decode.reg w1 15)).toNat (Svc.immInt w1).toNat b 12
        | none => none
      | none => none
    else none
  | _, _ => none

end ZesuExec
