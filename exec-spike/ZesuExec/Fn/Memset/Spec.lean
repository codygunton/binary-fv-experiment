import ZesuExec.Fn.SvcSteps
import ZesuExec.Image.Gen

/-!
# `memset` (`0x800e06f0`, 1,036 instructions): contract

Drafted from the code (`compiler_rt`'s ZisK `memset`, `dst = a0`, `c = a1`, `n = a2`), unreviewed
(`map/reviews.json`, `STATEMENTS.md` S14):

    800e06f0: bnez a1, 0x800e0700
    800e06f4: csrs 0x816, a0 ; addi zero, a2, 0 ; ret              -- c = 0
    800e0700: zext.b a1, a1 ; slli a1, a1, 4 ; auipc t0, 0 ; addi t0, t0, 0x18
    800e0710: add t0, t0, a1 ; jr t0                                -- into the table
    800e0720 + 16 b: csrs 0x816, a0 ; addi zero, a2, b ; ret ; nop  -- b = 0 … 255

The indirect jump goes to entry `b = c & 0xff` of a 256-entry table (resolved here from the
code: target `0x800e0720 + 16 b`, `b < 256`). Each entry is one CSR `0x816` step (register form:
fill `[a0, a0 + a2)` with the byte `b`) and a return.

`Pre`: the return address is 4-aligned and the destination is empty or present RAM.
`Post`: memory is `fillMem` with the low byte of `a1`; `pc` is the return address; every register
except `t0` (`x5`) and `a1` (`x11`) is unchanged.
-/

namespace ZesuExec.Fn.Memset
open ZesuExec ZesuExec.Machine

def entry : Nat := 0x800e06f0
def bound : Nat := 10
/-- The jump table's first entry. -/
def table : Nat := 0x800e0720

def Pre (m : Machine) : Prop :=
  (m.reg 1 &&& ~~~(1 : Word)).toNat % 4 = 0 ∧
  ((m.reg 12).toNat = 0 ∨ dstOk m.mem (m.reg 10).toNat (m.reg 12).toNat = true)

def Post (m m' : Machine) : Prop :=
  m'.mem = fillMem m.mem (m.reg 10).toNat (m.reg 12).toNat ((m.reg 11).setWidth 8) ∧
  m'.pc = (m.reg 1 &&& ~~~(1 : Word)) ∧
  ∀ i : Fin 32, i ≠ 5 → i ≠ 11 → m'.reg i = m.reg i

end ZesuExec.Fn.Memset
