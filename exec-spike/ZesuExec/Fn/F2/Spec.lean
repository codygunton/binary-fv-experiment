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

/-- Byte `j` of a successful outcome (`successResult40`): payload pointer, payload length,
`isList` byte, bytes 17..23 kept, consumed length, zero error halfword, bytes 34..39 kept. -/
def successByte (ptr payload consumed : Word) (isList : Bool) (before : List Byte) (j : Nat) :
    Byte :=
  if j < 8 then Sym.byteOf ptr j
  else if j < 16 then Sym.byteOf payload (j - 8)
  else if j = 16 then (if isList then 1 else 0)
  else if j < 24 then before.getD j 0
  else if j < 32 then Sym.byteOf consumed (j - 24)
  else if j < 34 then 0
  else before.getD j 0

/-- Byte `j` of an error outcome (`errorResult40`): all zero but byte 32, which is 4. -/
def errorByte (j : Nat) : Byte := if j = 32 then 4 else 0

/-- Byte `j` of the 40-byte outcome after a call with input `input` at `inPtr`, the struct
holding `before` on entry (`candidateResult40`). The empty string `0x80` reports pointer 1. -/
def resultByte (inPtr : Word) (input before : List Byte) (j : Nat) : Byte :=
  match decode input with
  | .error => errorByte j
  | .success isList h p =>
    let ptr : Word := if input.head? = some 128 then 1 else inPtr + BitVec.ofNat 64 h
    successByte ptr (BitVec.ofNat 64 p) (BitVec.ofNat 64 (h + p)) isList before j

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

/-! ## Non-vacuity -/

/-- Bytes a witness machine holds outside rodata: the frame below `sp = 0xa0001000`, the
outcome struct at `0xa0002000`, one input byte at `0xa0003000`. -/
def witnessRam (n : Nat) : Bool :=
  (0xa0000ff0 ≤ n && n < 0xa0001000) || (0xa0002000 ≤ n && n < 0xa0002028) || n == 0xa0003000

/-- `a0 = 0xa0002000`, `a1 = 0xa0003000`, `a2 = 1` (input `[0x00]`), `sp = 0xa0001000`,
`ra = 0x80000000`, the image's rodata loaded, every other present byte zero. -/
def witness : Machine where
  regs := fun i =>
    if i.val = 2 then 0xa0001000 else if i.val = 1 then 0x80000000
    else if i.val = 10 then 0xa0002000 else if i.val = 11 then 0xa0003000
    else if i.val = 12 then 1 else 0
  pc := BitVec.ofNat 64 entry
  mem := fun a =>
    match zesuImage.rodataByte? a.toNat with
    | some b => some (BitVec.ofNat 8 b)
    | none => if witnessRam a.toNat then some 0 else none

theorem witness_rodata : RodataLoaded zesuImage witness := by
  intro a b h
  have ha : a < 2 ^ 64 := by
    have := zesu_rodata_range h; unfold Layout.rodataHi at this; omega
  simp [witness, Nat.mod_eq_of_lt ha, h]

theorem witness_present (c j : Nat) (h : witnessRam (c + j) = true) (hc : c + j < 2 ^ 64) :
    (witness.mem (BitVec.ofNat 64 c + BitVec.ofNat 64 j)).isSome := by
  have ha : (BitVec.ofNat 64 c + BitVec.ofNat 64 j).toNat = c + j := by
    simp [BitVec.toNat_add]; omega
  have hlo : 0xa0000000 ≤ c + j := by
    simp [witnessRam] at h; omega
  have hro : zesuImage.rodataByte? (c + j) = none := by
    cases h' : zesuImage.rodataByte? (c + j) with
    | none => rfl
    | some b => have := zesu_rodata_range h'; unfold Layout.rodataHi at this; omega
  simp only [witness, ha, hro, h, if_true, Option.isSome_some]

example : ∃ m, Pre m := by
  refine ⟨witness, witness_rodata, ⟨by decide, by decide, by decide, fun j hj => ?_⟩,
    by unfold RetAligned; decide, by decide, fun j hj => ?_, by decide, by decide,
    fun j hj => ?_, by unfold Disjoint; decide, by unfold Disjoint; decide,
    by unfold Disjoint; decide⟩
  · have e : witness.reg 2 - BitVec.ofNat 64 16 = BitVec.ofNat 64 0xa0000ff0 := by decide
    rw [e]
    exact witness_present _ _ (by simp [witnessRam]; omega) (by omega)
  · have e : witness.reg 11 = BitVec.ofNat 64 0xa0003000 := by decide
    have hj' : j = 0 := by
      have : (witness.reg 12).toNat = 1 := by decide
      omega
    rw [e, hj']
    exact witness_present _ _ (by decide) (by decide)
  · have e : witness.reg 10 = BitVec.ofNat 64 0xa0002000 := by decide
    rw [e]
    exact witness_present _ _ (by simp [witnessRam]; omega) (by omega)

end ZesuExec.Fn.F2
