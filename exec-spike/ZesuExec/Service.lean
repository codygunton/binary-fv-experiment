import ZesuExec.Image

/-!
# The ZisK `memcpy` service and the machine's `next`

`ziskMemcpy` is the one trusted definition about ZisK. It transcribes `ziskMemcpyMemory`
(`ZesuSsz/Contracts/ZiskRuntime.v`) and `ziskMemcpyCallDomain`
(`ZesuSsz/Contracts/ZiskMemcpyPremise.v`) of zesislar: destination `x10`, source `x11`,
length `x12`. The length is stored first as a 64-bit little-endian word at
`Layout.extraParams`; the copy then reads that staged memory. Registers are unchanged and
`pc := x1` with bit 0 cleared.
-/

namespace ZesuExec
namespace Machine

/-- All `n` bytes at `a, a+1, …` are present. -/
def present (mem : Word → Option Byte) (a n : Nat) : Bool := (readBytes mem a n).isSome

end Machine

open Machine in
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

/-- One machine transition and its cost in instructions. -/
def next (img : Image) (m : Machine) : Option (Machine × Nat) :=
  if m.pc.toNat = Layout.memcpyEntry then (ziskMemcpy m).map (·, 3) else (step img m).map (·, 1)

end ZesuExec
