import ZesuExec.Service.Basic

/-!
# CSR `0x813`: ZisK DMA `memcpy` (`SYSCALL_DMA_MEMCPY_ID`, `definitions/src/syscall.rs:24`)

Two transpiler patterns (`core/src/riscv2zisk_context.rs:1994-2035`,
`transpile_dma_memcpy_memcmp_pattern`), both `csrs 0x813, rsrc` followed by:

* `add x0, rdst, rcount`: the `csrs` becomes `sd rcount, [EXTRA_PARAMS_ADDR]`
  (`create_set_precompiles_param_op`, `:719-736`) and the `add` becomes `dma_memcpy`
  (`:105-114`), which reads the count back from `EXTRA_PARAMS_ADDR`
  (`core/src/operations/dma_memcpy.rs:15-23`) and copies with `Mem::memcpy`
  (`core/src/mem.rs:888-926`: `dst = src` or `count = 0` does nothing; overlapping ranges copy
  from a snapshot of the source). The result `c = dst` goes to `rd = x0`.
* `addi x0, rdst, count`: one `dma_xmemcpy` with the immediate count (`:2010-2026`), no staging.

Both continue 8 bytes later. The definition here stages at `Layout.extraParams`; ZisK stages at
`EXTRA_PARAMS_ADDR = 0xa0000f00` (`core/src/mem.rs:147`), see `OPEN/services/extra_params.md`.

`ziskMemcpy` is the function-level form at `memcpy`'s entry (`Layout.memcpyEntry`) that every
existing proof uses; it transcribes `ziskMemcpyMemory` (`ZesuSsz/Contracts/ZiskRuntime.v`) and
`ziskMemcpyCallDomain` (`ZesuSsz/Contracts/ZiskMemcpyPremise.v`) of zesislar: the register form
above with `rsrc = x11`, `rdst = x10`, `rcount = x12`, followed by `ret`.
`ziskMemcpyMem_eq` relates it to the CSR form.
-/

namespace ZesuExec
open Machine

/-- Memory after the register form: the count `len` staged little-endian at
`Layout.extraParams`, then `[d, d+len)` copied from `[s, s+len)` of the staged memory. -/
def dmaMemcpyMem (mem : Word → Option Byte) (d s : Nat) (len : Word) : Word → Option Byte :=
  let n := len.toNat
  let staged : Nat → Option Byte := fun a =>
    if Layout.extraParams ≤ a ∧ a < Layout.extraParams + 8 then
      some (len.extractLsb' (8 * (a - Layout.extraParams)) 8)
    else mem (BitVec.ofNat 64 a)
  fun x =>
    let a := x.toNat
    if n ≠ 0 ∧ d ≠ s ∧ d ≤ a ∧ a < d + n then staged (s + a - d) else staged a

/-- Domain of the register form: the staging word is present RAM; for a nonzero count the
source is present readable memory and the destination present RAM, neither wrapping. -/
def dmaMemcpyDomain (mem : Word → Option Byte) (d s n : Nat) : Bool :=
  writable Layout.extraParams 8 && present mem Layout.extraParams 8 &&
  (n == 0 || (readable s n && present mem s n && writable d n && present mem d n))

/-- The CSR `0x813` service step at `m.pc`. -/
def csr813 (img : Image) (m : Machine) : Option SvcEffect :=
  match Svc.fetch img m.pc.toNat, Svc.fetch img (m.pc.toNat + 4) with
  | some w0, some w1 =>
    if Svc.isCsrs w0 0x813 then
      let s := (m.reg (Decode.reg w0 15)).toNat
      let d := (m.reg (Decode.reg w1 15)).toNat
      if Svc.isAddX0 w1 then
        let len := m.reg (Decode.reg w1 20)
        if dmaMemcpyDomain m.mem d s len.toNat then
          some { addrs := (List.range 8).map (Layout.extraParams + ·) ++
                   (List.range len.toNat).map (d + ·),
                 mem := dmaMemcpyMem m.mem d s len, pc := m.pc + 8, cost := 2 }
        else none
      else if Svc.isAddiX0 w1 ∧ 0 ≤ Svc.immInt w1 then
        let n := (Svc.immInt w1).toNat
        if n == 0 || (srcOk m.mem s n && dstOk m.mem d n) then
          some { addrs := (List.range n).map (d + ·), mem := copyMem m.mem d s n,
                 pc := m.pc + 8, cost := 2 }
        else none
      else none
    else none
  | _, _ => none

/-! ## The function-level form at `memcpy`'s entry -/

/-- Domain of the service: `x1 & ~1` is 4-aligned, the 8 bytes at `Layout.extraParams` are
present RAM, and for a nonzero length the source range is present readable memory and the
destination range is present RAM, neither wrapping. -/
def ziskMemcpyDomain (m : Machine) : Bool :=
  let d := (m.reg 10).toNat
  let s := (m.reg 11).toNat
  let n := (m.reg 12).toNat
  ((m.reg 1 &&& ~~~(1 : Word)).toNat % 4 == 0) &&
  writable Layout.extraParams 8 && present m.mem Layout.extraParams 8 &&
  (n == 0 ||
    (readable s n && present m.mem s n && writable d n && present m.mem d n))

/-- Memory after the service, `ziskMemcpyMemory` of `ZiskRuntime.v`. -/
def ziskMemcpyMem (m : Machine) : Word → Option Byte :=
  let d := (m.reg 10).toNat
  let s := (m.reg 11).toNat
  let len := m.reg 12
  let n := len.toNat
  let staged : Nat → Option Byte := fun a =>
    if Layout.extraParams ≤ a ∧ a < Layout.extraParams + 8 then
      some (len.extractLsb' (8 * (a - Layout.extraParams)) 8)
    else m.mem (BitVec.ofNat 64 a)
  fun x =>
    let a := x.toNat
    if n ≠ 0 ∧ d ≠ s ∧ d ≤ a ∧ a < d + n then staged (s + a - d) else staged a

def ziskMemcpy (m : Machine) : Option Machine :=
  if ziskMemcpyDomain m then
    some { m with mem := ziskMemcpyMem m, pc := m.reg 1 &&& ~~~(1 : Word) }
  else none

/-- The function-level memory is the CSR form's with `x10`, `x11`, `x12`. -/
theorem ziskMemcpyMem_eq (m : Machine) :
    ziskMemcpyMem m = dmaMemcpyMem m.mem (m.reg 10).toNat (m.reg 11).toNat (m.reg 12) := rfl

end ZesuExec
