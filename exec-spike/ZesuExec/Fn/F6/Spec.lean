import ZesuExec.Fn.F3.Spec

/-!
# F6 `rlp_decode.decodeParentHeader` (`0x800d5cb8`, 367 instructions, 3 loops, 21 calls)

Transcribes zesislar's `ParentHeaderContract.v` (`parentHeaderArgsWellFormed`, the entry and exit
resources, `parentHeaderAllows`), `ParentHeaderRootFacts.v` (`parentHeaderResult80`,
`parentHeaderError80`) and the candidate `Candidates/ParentHeaderCandidate.v`
(`parentHeaderFieldWalk`, `parentHeaderWalk`, `candidateParentHeader`,
`parentHeaderCandidateResult`) with the schedule of `Candidates/ParentHeaderDomain.v`.
`a0` = the 80-byte result (`error!ParentHeader`), `a1`/`a2` = the input slice. The function
decodes the outer list (`rlp.decodeItem`, F2), walks its 19 fields (skips by decodeItem, the
three required integers inline, the optional integers by `rlp_decode.nextUint64`, F3), and either
returns directly or tail-calls `memcpy` to copy the constant error union at `0x80114fb8`. It
uses a 400-byte frame; the callees use 112 bytes below it.
-/

namespace ZesuExec.Fn.F6
open ZesuExec

def entry : Nat := 0x800d5cb8

/-! ## The function as a pure function of the input bytes -/

/-- `ParentHeaderFieldKind`. -/
inductive Kind | reqSkip | reqInt | optSkip | optInt
  deriving DecidableEq, Repr

def Kind.isInt : Kind → Bool
  | .reqInt | .optInt => true
  | _ => false

def Kind.required : Kind → Bool
  | .reqSkip | .reqInt => true
  | _ => false

/-- `parentHeaderFieldSchedule` (the call PCs dropped). -/
def schedule : List Kind :=
  [.reqSkip, .reqSkip, .reqSkip, .reqSkip, .reqSkip, .reqSkip, .reqSkip, .reqSkip, .reqSkip,
   .reqInt, .reqInt, .reqInt, .optSkip, .optSkip, .optSkip, .optInt, .optSkip, .optInt, .optInt]

/-- `parentHeaderFieldWalk`'s final outcome: `none` for `walkMissingField` / `walkRejectField`,
`some values` for `walkAccept values` (the trace is dropped). -/
def fieldWalk : List Kind → List Byte → List Nat → Option (List Nat)
  | [], _, vals => some vals
  | k :: later, rem, vals =>
    match rem with
    | [] => if k.required then none else some vals
    | _ :: _ =>
      match F2.decode rem with
      | .error => none
      | .success b h p =>
        let rest := rem.drop ((h + p) % 2 ^ 64)
        if k.isInt then
          if b || 8 < p then none
          else fieldWalk later rest (vals ++ [F2.bigEndian ((rem.drop h).take p)])
        else fieldWalk later rest vals

/-- `parentHeaderWalkEnd`: the outer item is a list with a non-empty payload inside the input. -/
def walk (input : List Byte) : Option (List Nat) :=
  match F2.decode input with
  | .success true h p =>
    if 0 < p ∧ h + p ≤ input.length then fieldWalk schedule ((input.drop h).take p) [] else none
  | _ => none

/-- `longLengthWidth`. -/
def longWidth (pre : Nat) : Nat :=
  if 184 ≤ pre ∧ pre ≤ 191 then pre - 183 else if 248 ≤ pre ∧ pre ≤ 255 then pre - 247 else 0

/-- `headerFits` (`RlpDecodeItem.v`): a long header's length does not wrap `2^64`. -/
def headerFits : List Byte → Prop
  | [] => True
  | pre :: rest =>
    longWidth pre.toNat = 0 ∨ rest.length < longWidth pre.toNat ∨
      1 + longWidth pre.toNat + F2.bigEndian (rest.take (longWidth pre.toNat)) < 2 ^ 64

/-! ## Result bytes -/

/-- The 8 bytes at `a` hold `v` (`word64At`). -/
def WordIs (m : Machine) (a : Word) (v : Nat) : Prop :=
  ∀ t < 8, m.mem (a + BitVec.ofNat 64 t) = some (Sym.byteOf (BitVec.ofNat 64 v) t)

/-- `optionalWordAt`: the tag byte, and the value word when present. -/
def OptIs (m : Machine) (res : Word) (vo to : Nat) (v : Option Nat) : Prop :=
  m.mem (res + BitVec.ofNat 64 to) = some (if v.isSome then 1 else 0) ∧
    ∀ n, v = some n → WordIs m (res + BitVec.ofNat 64 vo) n

/-- `parentHeaderResult80` with `candidateHeaderOfValues vals`: three words, three optional
words, the zero error halfword at 72. -/
def ResultOK (m : Machine) (res : Word) (vals : List Nat) : Prop :=
  WordIs m res (vals.getD 0 0) ∧ WordIs m (res + 8) (vals.getD 1 0) ∧
  WordIs m (res + 16) (vals.getD 2 0) ∧ OptIs m res 24 32 vals[3]? ∧ OptIs m res 40 48 vals[4]? ∧
  OptIs m res 56 64 vals[5]? ∧ m.mem (res + 72) = some 0 ∧ m.mem (res + 73) = some 0

/-- `parentHeaderError80`: error tag 3 at byte 72. -/
def ErrorOK (m : Machine) (res : Word) : Prop :=
  m.mem (res + 72) = some 3 ∧ m.mem (res + 73) = some 0

/-! ## Contract -/

/-- `parentHeaderArgsWellFormed` and the owned resources of `parentHeaderEntryResources`. -/
def Pre (m : Machine) : Prop :=
  let res := m.reg 10; let inp := m.reg 11; let len := (m.reg 12).toNat; let sp := m.reg 2
  RodataLoaded zesuImage m ∧ StackOk m 512 ∧ RetAligned m ∧
  -- input: in the ZisK input buffer, `inputPointer ↦ₘ∗ input`
  Layout.inputLo ≤ inp.toNat ∧ inp.toNat + len ≤ Layout.inputHi ∧
  (∀ j < len, (m.mem (inp + BitVec.ofNat 64 j)).isSome) ∧
  -- result: 80 bytes in RAM, 8-aligned
  Machine.writable res.toNat 80 = true ∧ res.toNat % 8 = 0 ∧
  (∀ j < 80, (m.mem (res + BitVec.ofNat 64 j)).isSome) ∧
  -- the memcpy scratch word
  (∀ j < 8, (m.mem (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j)).isSome) ∧
  -- `separateRanges`: result, frame and callee area, scratch
  Disjoint (res, 80) (sp - 512, 512) ∧ Disjoint (BitVec.ofNat 64 Layout.extraParams, 8) (res, 80) ∧
  Disjoint (BitVec.ofNat 64 Layout.extraParams, 8) (sp - 512, 512) ∧
  -- `headerFits` of the outer header
  ∀ input, BytesAt m inp input → input.length = len → headerFits input

/-- `parentHeaderExitResources` with `parentHeaderAllows`: the result is the candidate's. -/
def Post (m m' : Machine) : Prop :=
  let res := m.reg 10; let inp := m.reg 11; let len := (m.reg 12).toNat
  Returns m m' ∧
  SameOutside (fun a => InRange res 80 a ∨ InRange (m.reg 2 - 512) 512 a ∨
    InRange (BitVec.ofNat 64 Layout.extraParams) 8 a) m m' ∧
  ∀ input, BytesAt m inp input → input.length = len →
    match walk input with
    | none => ErrorOK m' res
    | some vals => ResultOK m' res vals

/-! ## Non-vacuity -/

/-- Present bytes of the witness outside rodata: the 512 stack bytes below `0xa0001000`, the
result at `0xa0002000`, the scratch word. -/
def witnessRam (n : Nat) : Bool :=
  (0xa0000e00 ≤ n && n < 0xa0001000) || (0xa0002000 ≤ n && n < 0xa0002050) ||
    (Layout.extraParams ≤ n && n < Layout.extraParams + 8)

/-- `a0 = 0xa0002000` (result), `a1 = 0x40000000`, `a2 = 0` (empty input), `sp = 0xa0001000`,
`ra = 0x80000000`, rodata loaded. -/
def witness : Machine where
  regs := fun i =>
    if i.val = 2 then 0xa0001000 else if i.val = 1 then 0x80000000
    else if i.val = 10 then 0xa0002000 else if i.val = 11 then 0x40000000 else 0
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

theorem witness_present (c j : Nat) (hc : c + j < 2 ^ 64) (h : witnessRam (c + j) = true) :
    (witness.mem (BitVec.ofNat 64 c + BitVec.ofNat 64 j)).isSome := by
  have ha : (BitVec.ofNat 64 c + BitVec.ofNat 64 j).toNat = c + j := by
    simp [BitVec.toNat_add]; omega
  have hlo : 0xa0000000 ≤ c + j := by
    simp [witnessRam, Layout.extraParams] at h; omega
  have hro : zesuImage.rodataByte? (c + j) = none := by
    cases h' : zesuImage.rodataByte? (c + j) with
    | none => rfl
    | some b => have := zesu_rodata_range h'; unfold Layout.rodataHi at this; omega
  simp only [witness, ha, hro, h, if_true, Option.isSome_some]

example : ∃ m, Pre m := by
  refine ⟨witness, witness_rodata, ⟨by decide, by decide, by decide, fun j hj => ?_⟩,
    by unfold RetAligned; decide, by decide, by decide, fun j hj => ?_, by decide, by decide,
    fun j hj => ?_, fun j hj => ?_, by unfold Disjoint; decide, by unfold Disjoint; decide,
    by unfold Disjoint; decide, fun input _ hl => ?_⟩
  · have e : witness.reg 2 - BitVec.ofNat 64 512 = BitVec.ofNat 64 0xa0000e00 := by decide
    rw [e]
    exact witness_present _ _ (by omega) (by simp [witnessRam]; omega)
  · have : (witness.reg 12).toNat = 0 := by decide
    omega
  · have e : witness.reg 10 = BitVec.ofNat 64 0xa0002000 := by decide
    rw [e]
    exact witness_present _ _ (by omega) (by simp [witnessRam]; omega)
  · exact witness_present _ _ (by simp [Layout.extraParams]; omega)
      (by simp [witnessRam, Layout.extraParams]; omega)
  · have : (witness.reg 12).toNat = 0 := by decide
    rw [this, List.length_eq_zero_iff] at hl
    subst hl; trivial

end ZesuExec.Fn.F6
