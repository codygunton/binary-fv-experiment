import ZesuExec.Fn.F2.Spec

/-!
# F3 `rlp_decode.nextUint64` (`0x800d6274`, 53 instructions, 1 loop, 1 call)

Transcribes zesislar's `nextUint64RootResult` (`ZesuSsz/Contracts/ParentHeaderRootFacts.v`),
`nextUint64Success16` / `nextUint64Error16` (`ParentHeader.v`) and the domain
`nextUint64BoundaryDomain` (`NextUint64BlockEntries.v`). `a0` = the 16-byte result
`error!u64`, `a1` = the 16-byte input slice `{ptr, len}`. The function calls `rlp.decodeItem`
(F2) on the slice, accepts a non-list item of at most 8 payload bytes, returns their big-endian
value and advances the slice by the consumed length; otherwise it returns error code 3 and leaves
the slice. It uses a 96-byte frame; the callee's 16-byte frame lies below it.
-/

namespace ZesuExec.Fn.F3
open ZesuExec

def entry : Nat := 0x800d6274
/-- 17 + 75 (decodeItem) + 13 + 8 * 5 + 15. -/
def bound : Nat := 160

/-- The 64-bit word at `a` (0 if it cannot be loaded). -/
def wordAt (m : Machine) (a : Word) : Word := (m.load a 8).getD 0

/-! ## The function as a pure function of the input bytes -/

/-- `nextUint64RootResult`'s cases: the value and the consumed length, or `none` (error 3). -/
def nextUint64 (input : List Byte) : Option (Word × Nat) :=
  match F2.decode input with
  | .success false h p =>
    if p ≤ 8 then some (BitVec.ofNat 64 (F2.bigEndian ((input.drop h).take p)), h + p) else none
  | _ => none

/-- Byte `j` of the 16-byte result, `old` its byte on entry (`nextUint64Success16`: value,
zero tag, padding kept; `nextUint64Error16`: words 0 and 3). -/
def resultByte (input : List Byte) (old : Byte) (j : Nat) : Byte :=
  match nextUint64 input with
  | none => Sym.byteOf (BitVec.ofNat 64 (if j < 8 then 0 else 3)) (j % 8)
  | some (v, _) => if j < 8 then Sym.byteOf v j else if j < 10 then 0 else old

/-- Byte `j` of the slice after the call (`nextRestPointer`, `nextRestLength`). -/
def sliceByte (inp len : Word) (input : List Byte) (old : Byte) (j : Nat) : Byte :=
  match nextUint64 input with
  | none => old
  | some (_, c) =>
    if j < 8 then Sym.byteOf (inp + BitVec.ofNat 64 c) j
    else Sym.byteOf (len - BitVec.ofNat 64 c) (j - 8)

/-! ## Contract -/

/-- `nextUint64BoundaryDomain` plus the owned resources of `nextUint64BoundaryEntry`. -/
def Pre (m : Machine) : Prop :=
  let res := m.reg 10; let sl := m.reg 11; let st := m.reg 2 - 112
  let inp := wordAt m sl; let len := (wordAt m (sl + 8)).toNat
  RodataLoaded zesuImage m ∧ StackOk m 112 ∧ RetAligned m ∧
  -- result: 16 bytes in RAM, 8-aligned
  Machine.writable res.toNat 16 = true ∧ res.toNat % 8 = 0 ∧
  (∀ j < 16, (m.mem (res + BitVec.ofNat 64 j)).isSome) ∧
  -- slice: 16 bytes in RAM, 8-aligned
  Machine.writable sl.toNat 16 = true ∧ sl.toNat % 8 = 0 ∧
  (∀ j < 16, (m.mem (sl + BitVec.ofNat 64 j)).isSome) ∧
  -- input: `inputPointer ↦ₘ∗ input`, in a readable interval
  Machine.readable inp.toNat len = true ∧ (∀ j < len, (m.mem (inp + BitVec.ofNat 64 j)).isSome) ∧
  -- `separateRanges`; the stack is the 96-byte frame and the callee's 16 bytes
  Disjoint (inp, len) (res, 16) ∧ Disjoint (inp, len) (sl, 16) ∧ Disjoint (inp, len) (st, 112) ∧
  Disjoint (res, 16) (sl, 16) ∧ Disjoint (res, 16) (st, 112) ∧ Disjoint (sl, 16) (st, 112)

/-- `nextUint64ContractExit` with `nextUint64RootResult`. -/
def Post (m m' : Machine) : Prop :=
  let res := m.reg 10; let sl := m.reg 11
  let inp := wordAt m sl; let len := wordAt m (sl + 8)
  Returns m m' ∧
  SameOutside (fun a => InRange res 16 a ∨ InRange sl 16 a ∨ InRange (m.reg 2 - 112) 112 a) m m' ∧
  ∀ input, BytesAt m inp input → input.length = len.toNat →
    (∀ j < 16, m'.mem (res + BitVec.ofNat 64 j) =
      some (resultByte input ((m.mem (res + BitVec.ofNat 64 j)).getD 0) j)) ∧
    (∀ j < 16, m'.mem (sl + BitVec.ofNat 64 j) =
      some (sliceByte inp len input ((m.mem (sl + BitVec.ofNat 64 j)).getD 0) j))

end ZesuExec.Fn.F3
