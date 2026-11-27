import ZesuExec.Fn.Common

/-!
# F2 `rlp.decodeItem` (`0x800d6960`, 116 instructions, 2 loops)

Transcribes zesislar's `ZesuSsz/Contracts/RlpDecodeItem.v` (`candidateDecodeItem`,
`candidateResult40`, `C1BResult`, `decodeItemEntryLayout`) and `RlpDecodeItemContract.v`
(`decodeItemC1BDomain`). `a0` = the 40-byte outcome struct, `a1` = input pointer, `a2` = input
length. The function writes the outcome `{payload ptr, payload len, isList, consumed, error}`
and saves `ra`, `s0` in a 16-byte frame.
-/

namespace ZesuExec.Fn.F2
open ZesuExec

def entry : Nat := 0x800d6960
/-- Longest path: long list with an 8-byte length (23 + 8 * 5 + 2 + 10). -/
def bound : Nat := 75

/-! ## The decoder as a pure function (`candidateDecodeItem`) -/

inductive Item
  | error
  | success (isList : Bool) (header payload : Nat)
  deriving DecidableEq, Repr

/-- `bigEndian`: `fold_left (fun acc b => 256 * acc + b) bytes 0`. -/
def bigEndian (bs : List Byte) : Nat := bs.foldl (fun acc b => 256 * acc + b.toNat) 0

/-- `checkedPayload`. -/
def checkedPayload (len header payload : Nat) (isList : Bool) : Item :=
  if (header + payload) % 2 ^ 64 ≤ len then .success isList header payload else .error

/-- `candidateDecodeItem`: the six return classes of the binary. -/
def decode : List Byte → Item
  | [] => .error
  | pre :: rest =>
    let f := pre.toNat
    let len := rest.length + 1
    if f ≤ 127 then .success false 0 1
    else if f = 128 then .success false 1 0
    else if f ≤ 183 then checkedPayload len 1 (f - 128) false
    else if f ≤ 191 then
      let w := f - 183
      if 1 + w ≤ len then checkedPayload len (1 + w) (bigEndian (rest.take w)) false else .error
    else if f ≤ 247 then checkedPayload len 1 (f - 192) true
    else
      let w := f - 247
      if 1 + w ≤ len then checkedPayload len (1 + w) (bigEndian (rest.take w)) true else .error

/-- Byte `j` of a word, little-endian. -/
abbrev byteOf (x : Word) (j : Nat) : Byte := x.extractLsb' (8 * j) 8

/-- Byte `j` of the 40-byte outcome after a call with input `input` at `inPtr`, the struct
holding `before` on entry (`candidateResult40`: `successResult40` / `errorResult40`). -/
def resultByte (inPtr : Word) (input before : List Byte) (j : Nat) : Byte :=
  match decode input with
  | .error => if j = 32 then 4 else 0
  | .success isList h p =>
    let ptr : Word := if input.head? = some 128 then 1 else inPtr + BitVec.ofNat 64 h
    if j < 8 then byteOf ptr j
    else if j < 16 then byteOf (BitVec.ofNat 64 p) (j - 8)
    else if j = 16 then (if isList then 1 else 0)
    else if j < 24 then before.getD j 0
    else if j < 32 then byteOf (BitVec.ofNat 64 (h + p)) (j - 24)
    else if j < 34 then 0
    else before.getD j 0

def result40 (inPtr : Word) (input before : List Byte) : List Byte :=
  (List.range 40).map (resultByte inPtr input before)

/-! ## Contract -/

/-- `decodeItemC1BDomain` plus the owned resources of `decodeItemEntryResources`. -/
def Pre (m : Machine) : Prop :=
  let out := m.reg 10; let inp := m.reg 11; let len := (m.reg 12).toNat
  let fr := m.reg 2 - 16
  RodataLoaded zesuImage m ∧ StackOk m 16 ∧ RetAligned m ∧
  -- input: `inputPointer ↦ₘ∗ input`, in a readable interval
  Machine.readable inp.toNat len = true ∧ (∀ j < len, (m.mem (inp + BitVec.ofNat 64 j)).isSome) ∧
  -- outcome: `outputPointer ↦ₘ∗ before`, 40 bytes in RAM, 8-aligned (aligned stores)
  Machine.writable out.toNat 40 = true ∧ out.toNat % 8 = 0 ∧
  (∀ j < 40, (m.mem (out + BitVec.ofNat 64 j)).isSome) ∧
  -- `separateRanges`
  Disjoint (inp, len) (out, 40) ∧ Disjoint (inp, len) (fr, 16) ∧ Disjoint (out, 40) (fr, 16)

/-- `decodeItemExitResources` and `C1BResult`: the outcome struct holds `result40`. -/
def Post (m m' : Machine) : Prop :=
  Returns m m' ∧
  SameOutside (fun a => InRange (m.reg 10) 40 a ∨ InRange (m.reg 2 - 16) 16 a) m m' ∧
  ∀ input before, BytesAt m (m.reg 11) input → input.length = (m.reg 12).toNat →
    BytesAt m (m.reg 10) before → before.length = 40 →
    BytesAt m' (m.reg 10) (result40 (m.reg 11) input before)

end ZesuExec.Fn.F2
