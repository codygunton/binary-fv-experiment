import ZesuExec.Fn.Alloc.Contract
import ZesuExec.Fn.F2.Spec
import ZesuExec.Fn.Stage

/-!
# TX `rlp_decode.txAccessList` (`0x80000000`, 323 instructions, 2 loops)

Transcribes zesislar's `ZesuSsz/Contracts/TxAccessListContract.v` (`txAccessListArgsWellFormed`,
`txAccessListEntryResources`, `txAccessListExitResources`, `txAccessListAllows`), the reference
decoder of `ZesuSsz/Contracts/Candidates/AccessListCandidate.v` and the domain of
`ZesuSsz/Contracts/TxAccessListMeaning.v`. `a0` = 24-byte result `{ptr, len, err : u16}`,
`a1` = allocator object `{ctx, vtable}`, `a2` = the 16-byte `rest` slice `{pointer, length}`.
The frame is 576 bytes; the callee frames below it need 128 more (704 in all).

The Sail half of `TxAccessListMeaningModuloKnownBugs` (`txAccessListSailAgrees` or a known-bug
trigger) is not part of `Post`; it belongs to the compliance statement (as for F2). Differences
are listed in `STATEMENTS.md`, section TX.
-/

namespace ZesuExec.Fn.TX
open ZesuExec

def entry : Nat := 0x80000000
/-- `32 · len + 424` steps for an input of `len ≤ 2^30` bytes (the input buffer or RAM). -/
def bound : Nat := 32 * 2 ^ 30 + 424

/-! ## The reference decoder (`AccessListCandidate.v`) over `F2.decode` (`candidateDecodeItem`) -/

/-- Call sites of `rlp.decodeItem`, as offsets from the entry. -/
def outerCall : Nat := 0x64
def entryCall : Nat := 0xd4
def addressCall : Nat := 0x108
def keysCall : Nat := 0x158
def keyCall : Nat := 0x19c

/-- `AccessListEntryValue`. -/
structure EntryValue where
  address : List Byte
  keys : List (List Byte)
  deriving DecidableEq, Repr

/-- `AccessListCandidate`: `rejected (some n)` when the first item decoded as a list (`rest`
advanced by `n`), `rejected none` when `rest` is unchanged. -/
inductive Candidate
  | rejected (consumed : Option Nat)
  | accepted (entries : List EntryValue) (consumed : Nat)
  deriving DecidableEq, Repr

def itemPayload (input : List Byte) (h p : Nat) : List Byte := (input.drop h).take p
def itemConsumed (h p : Nat) : Nat := (h + p) % 2 ^ 64
def itemRest (input : List Byte) (h p : Nat) : List Byte := input.drop (itemConsumed h p)

/-- A reached `decodeItem` call: its call-site offset and its input slice. -/
abbrev Call := Nat × List Byte

/-- `accessListKeysWalk`. -/
def keysWalk : Nat → List Byte → List Call × Option (List (List Byte))
  | _, [] => ([], some [])
  | 0, _ :: _ => ([], none)
  | fuel + 1, keys@(_ :: _) =>
    let here := (keyCall, keys)
    match F2.decode keys with
    | .success false h p =>
      if p = 32 then
        let r := keysWalk fuel (itemRest keys h p)
        (here :: r.1, r.2.map (itemPayload keys h p :: ·))
      else ([here], none)
    | _ => ([here], none)

/-- `accessListEntry`: one entry's address and keys, or a rejection. -/
def entryWalk (e : List Byte) : List Call × Option EntryValue :=
  let aCall := (addressCall, e)
  match F2.decode e with
  | .success false ah al =>
    if al = 20 then
      let afterAddress := itemRest e ah al
      let kCall := (keysCall, afterAddress)
      match F2.decode afterAddress with
      | .success true kh kl =>
        let kp := itemPayload afterAddress kh kl
        let r := keysWalk kp.length kp
        (aCall :: kCall :: r.1, r.2.map fun ks => ⟨itemPayload e ah al, ks⟩)
      | _ => ([aCall, kCall], none)
    else ([aCall], none)
  | _ => ([aCall], none)

/-- `accessListEntriesWalk`. -/
def entriesWalk : Nat → List Byte → List Call × Option (List EntryValue)
  | _, [] => ([], some [])
  | 0, _ :: _ => ([], none)
  | fuel + 1, es@(_ :: _) =>
    let here := (entryCall, es)
    match F2.decode es with
    | .success true eh el =>
      let r := entryWalk (itemPayload es eh el)
      match r.2 with
      | some v =>
        let t := entriesWalk fuel (itemRest es eh el)
        (here :: r.1 ++ t.1, t.2.map (v :: ·))
      | none => (here :: r.1, none)
    | _ => ([here], none)

/-- `accessListWalk`: the reached calls in machine order and the decision. -/
def walk (input : List Byte) : List Call × Candidate :=
  let outer := (outerCall, input)
  match F2.decode input with
  | .success true h p =>
    let payload := itemPayload input h p
    let r := entriesWalk payload.length payload
    (outer :: r.1, match r.2 with
      | some vs => .accepted vs (itemConsumed h p)
      | none => .rejected (some (itemConsumed h p)))
  | _ => ([outer], .rejected none)

def candidate (input : List Byte) : Candidate := (walk input).2
def calls (input : List Byte) : List Call := (walk input).1

/-- `longLengthWidth`. -/
def longLengthWidth (pre : Nat) : Nat :=
  if 184 ≤ pre ∧ pre ≤ 191 then pre - 183 else if 248 ≤ pre ∧ pre ≤ 255 then pre - 247 else 0

/-- `headerFits` (`RlpDecodeItem.v`): a long length does not wrap `2^64`. -/
def HeaderFits : List Byte → Prop
  | [] => True
  | pre :: rest =>
    let w := longLengthWidth pre.toNat
    w = 0 ∨ rest.length < w ∨ 1 + w + F2.bigEndian (rest.take w) < 2 ^ 64

/-- `txAccessListDomain`: `accessListHeadersFit` and Sail's `2^30`-byte source limit. -/
def Domain (input : List Byte) : Prop :=
  (∀ c ∈ calls input, HeaderFits c.2) ∧
  match F2.decode input with
  | .success _ h p => h + p ≤ 2 ^ 30
  | .error => True

/-- `accessListCandidateConsumed`. -/
def candidateConsumed : Candidate → Nat
  | .accepted _ n => n
  | .rejected (some n) => n
  | .rejected none => 0

/-- `TxAccessListOutcomeClass`. -/
inductive OutcomeClass
  | ok (entries : List EntryValue)
  | invalidInput
  | allocationFailure

/-- `txAccessListOutcomeAllowed`. -/
def OutcomeAllowed (input : List Byte) : OutcomeClass → Nat → Prop
  | .ok entries, consumed => candidate input = .accepted entries consumed
  | .invalidInput, consumed =>
    (∃ r, candidate input = .rejected r) ∧ consumed = candidateConsumed (candidate input)
  | .allocationFailure, consumed =>
    ∃ h p, F2.decode input = .success true h p ∧ 0 < p ∧ consumed = itemConsumed h p

/-! ## Machine contract -/

/-- `txAccessListFrameBytes + txAccessListCalleeBytes`. -/
def stackBytes : Nat := 576 + 128
/-- `alt_fl_alloc`'s vtable `{alloc, resize, remap, free}` in rodata. -/
def vtable : Nat := 0x801136d8
def scratch : Word := BitVec.ofNat 64 Layout.extraParams
def entrySize : Nat := 40
def keySize : Nat := 32

/-- The 64-bit word at `a` (`0` if it cannot be loaded). -/
def wordAt (m : Machine) (a : Word) : Word := (m.load a 8).getD 0

/-- Little-endian bytes of a word (`word64Bytes`). -/
def wordBytes (v : Word) : List Byte := (List.range 8).map fun j => v.extractLsb' (8 * j) 8

/-- Two ranges do not meet (`separateRanges`). -/
def Apart (a : Word) (n : Nat) (b : Word) (k : Nat) : Prop :=
  a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat

/-- The input lies in the input buffer or in RAM. -/
def InputArea (a : Word) (n : Nat) : Prop :=
  (Layout.inputLo ≤ a.toNat ∧ a.toNat + n ≤ Layout.inputHi) ∨ RamRange a n

/-- `TxAccessListEntryImage`: the keys slice pointer and the 4 padding bytes of one entry. -/
structure EntryImage where
  keysPtr : Word
  padding : List Byte

/-- `txAccessListEntryBytes`: the 40-byte image of one returned entry. -/
def entryBytes (e : EntryValue) (i : EntryImage) : List Byte :=
  wordBytes i.keysPtr ++ wordBytes (BitVec.ofNat 64 e.keys.length) ++ e.address ++ i.padding

/-- `txAccessListEntriesBytes`. -/
def entriesBytes (es : List EntryValue) (is : List EntryImage) : List Byte :=
  (List.zipWith entryBytes es is).flatten

/-- The allocator blocks a successful call returns (`txAccessListReturnedHeap`): the entries
buffer and each non-empty keys buffer. -/
def returnedBlocks (p : Word) (es : List EntryValue) (is : List EntryImage) : List (Word × Nat) :=
  (if es = [] then [] else [(p, entrySize * es.length)]) ++
    (List.zip es is).filterMap fun (e, i) =>
      if e.keys = [] then none else some (i.keysPtr, keySize * e.keys.length)

/-- The parameters of one call: the input bytes and the allocator's live blocks. -/
structure Params where
  input : List Byte
  L : List (Word × Nat)

section
variable (A : AllocContract zesuImage) (g : Params)

/-- Entry: `txAccessListArgsWellFormed` plus the owned resources of
`txAccessListEntryResources`. -/
def Pre (m : Machine) : Prop :=
  let res := m.reg 10; let ao := m.reg 11; let rest := m.reg 12; let sp := m.reg 2
  let inp := wordAt m rest; let len := (wordAt m (rest + 8)).toNat
  let fr := sp - BitVec.ofNat 64 stackBytes
  RodataLoaded zesuImage m ∧ StackOk m stackBytes ∧ RetAligned m ∧
  -- result (24 bytes, `↦ₘ?`)
  RamRange res 24 ∧ res.toNat % 8 = 0 ∧ Present m res 24 ∧
  -- allocator object `{ctx, alt_fl_alloc.vtable}`
  RamRange ao 16 ∧ ao.toNat % 8 = 0 ∧ (m.load ao 8).isSome ∧
  m.load (ao + 8) 8 = some (BitVec.ofNat 64 vtable) ∧
  -- `rest` = `{input pointer, input length}`
  RamRange rest 16 ∧ rest.toNat % 8 = 0 ∧ (m.load rest 8).isSome ∧ (m.load (rest + 8) 8).isSome ∧
  -- the input bytes, in the domain of the meaning
  InputArea inp len ∧ BytesAt m inp g.input ∧ g.input.length = len ∧ Domain g.input ∧
  -- the memcpy scratch word and the allocator state
  Present m scratch 8 ∧ A.Heap g.L m ∧
  -- `separateRanges` of the owned argument ranges, the stack and the scratch word
  Apart res 24 ao 16 ∧ Apart res 24 rest 16 ∧ Apart ao 16 rest 16 ∧
  Apart inp len res 24 ∧ Apart inp len ao 16 ∧ Apart inp len rest 16 ∧
  Apart fr stackBytes res 24 ∧ Apart fr stackBytes ao 16 ∧ Apart fr stackBytes rest 16 ∧
  Apart fr stackBytes inp len ∧
  Apart scratch 8 res 24 ∧ Apart scratch 8 ao 16 ∧ Apart scratch 8 rest 16 ∧
  Apart scratch 8 inp len ∧ Apart scratch 8 fr stackBytes ∧
  -- the owned ranges avoid the allocator's private memory
  (∀ a, InRange res 24 a ∨ InRange ao 16 a ∨ InRange rest 16 a ∨ InRange inp len a ∨
    InRange fr stackBytes a ∨ InRange scratch 8 a → ¬ A.Priv g.L a)

/-- The result and heap of an outcome class (`txAccessListResultImage`,
`txAccessListHeapImage`, `txAccessListReturnedHeap`). -/
def OutcomeImage (res : Word) (m' : Machine) : OutcomeClass → Prop
  | .ok entries =>
    ∃ (p : Word) (is : List EntryImage),
      m'.load res 8 = some p ∧ m'.load (res + 8) 8 = some (BitVec.ofNat 64 entries.length) ∧
      m'.load (res + 16) 2 = some 0 ∧
      is.length = entries.length ∧
      (entries ≠ [] → RamRange p (entrySize * entries.length)) ∧
      BytesAt m' p (entriesBytes entries is) ∧
      (∀ x ∈ List.zip entries is, x.2.padding.length = 4 ∧
        (x.1.keys ≠ [] → RamRange x.2.keysPtr (keySize * x.1.keys.length)) ∧
        BytesAt m' x.2.keysPtr x.1.keys.flatten) ∧
      ∃ L', L'.Perm (g.L ++ returnedBlocks p entries is) ∧ A.Heap L' m'
  | .invalidInput | .allocationFailure =>
    m'.load res 8 = some 0 ∧ m'.load (res + 8) 8 = some 0 ∧ m'.load (res + 16) 8 = some 3 ∧
    -- error paths leak what they allocated
    ∃ leaked : List (Word × Nat), (∀ b ∈ leaked, 0 < b.2 ∧ RamRange b.1 b.2) ∧
      ∃ L', L'.Perm (g.L ++ leaked) ∧ A.Heap L' m'

/-- Exit: `txAccessListExitResources` and `txAccessListAllows` without its Sail half. -/
def Post (m m' : Machine) : Prop :=
  let res := m.reg 10; let rest := m.reg 12; let sp := m.reg 2
  let inp := wordAt m rest; let len := wordAt m (rest + 8)
  Returns m m' ∧
  SameOutside (fun a => InRange res 24 a ∨ InRange rest 16 a ∨
    InRange (sp - BitVec.ofNat 64 stackBytes) stackBytes a ∨ InRange scratch 8 a ∨
    A.Priv g.L a) m m' ∧
  Present m' scratch 8 ∧
  ∃ (cls : OutcomeClass) (consumed : Nat),
    OutcomeAllowed g.input cls consumed ∧
    m'.load rest 8 = some (inp + BitVec.ofNat 64 consumed) ∧
    m'.load (rest + 8) 8 = some (len - BitVec.ofNat 64 consumed) ∧
    OutcomeImage A g res m' cls

end

/-! ## The decoder on small inputs -/

/-- `c0`: an empty access list is accepted with no entries, consuming one byte. -/
example : candidate [0xc0] = .accepted [] 1 := by decide

/-- `80`: a byte string is rejected with `rest` unchanged. -/
example : candidate [0x80] = .rejected none := by decide

/-- One entry: a 20-byte address and one 32-byte key. -/
example : candidate ([0xf8, 0x38, 0xf7, 0x94] ++ List.replicate 20 1 ++ [0xe1, 0xa0] ++
    List.replicate 32 2) = .accepted [⟨List.replicate 20 1, [List.replicate 32 2]⟩] 58 := by
  decide

/-- A 19-byte address rejects after the outer list advanced `rest`. -/
example : candidate ([0xd5, 0xd4, 0x93] ++ List.replicate 19 1 ++ [0xc0]) =
    .rejected (some 22) := by decide

/-! ## Non-vacuity -/

open ZesuExec.Fn

/-- The witness's own bytes: 704 stack bytes below `sp = 0xa0001800`, the result at
`0xa0002000`, the allocator object `{0, vtable}` at `0xa0002020`, `rest` = `{0xa0002060, 1}` at
`0xa0002040`, the input `c0` (an empty access list) at `0xa0002060`, the scratch word. -/
def nvByte (a : Nat) : Option Nat :=
  if 0xa0001540 ≤ a ∧ a < 0xa0001800 then some 0
  else if 0xa0002000 ≤ a ∧ a < 0xa0002028 then some 0
  else if 0xa0002028 ≤ a ∧ a < 0xa0002030 then some ((vtable / 256 ^ (a - 0xa0002028)) % 256)
  else if 0xa0002040 ≤ a ∧ a < 0xa0002048 then some ((0xa0002060 / 256 ^ (a - 0xa0002040)) % 256)
  else if a = 0xa0002048 then some 1
  else if 0xa0002048 < a ∧ a < 0xa0002050 then some 0
  else if a = 0xa0002060 then some 0xc0
  else if Layout.extraParams ≤ a ∧ a < Layout.extraParams + 8 then some 0
  else none

def nvMachine (m0 : Machine) : Machine where
  regs := fun i => if i.val = 2 then 0xa0001800 else if i.val = 1 then 0x80000000
    else if i.val = 10 then 0xa0002000 else if i.val = 11 then 0xa0002020
    else if i.val = 12 then 0xa0002040 else 0
  pc := BitVec.ofNat 64 entry
  mem := fun a => match zesuImage.rodataByte? a.toNat with
    | some b => some (BitVec.ofNat 8 b)
    | none => match nvByte a.toNat with
      | some b => some (BitVec.ofNat 8 b)
      | none => m0.mem a

def bot : Machine := ⟨fun _ => 0, 0, fun _ => none⟩

theorem nv_mem (m0 : Machine) (a : Word) (h : (nvByte a.toNat).isSome = true) :
    (nvMachine m0).mem a = (nvMachine bot).mem a := by
  simp only [nvMachine]
  split
  · rfl
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h; simp [hb]

theorem nv_load (m0 : Machine) (a : Word) (n : Nat)
    (h : ∀ t < n, (nvByte (a + BitVec.ofNat 64 t).toNat).isSome = true) :
    (nvMachine m0).load a n = (nvMachine bot).load a n :=
  load_congr fun t ht => nv_mem m0 _ (h t ht)

theorem nv_present (m0 : Machine) (a : Word) (n : Nat)
    (h : ∀ t < n, (nvByte (a + BitVec.ofNat 64 t).toNat).isSome = true) :
    ∀ t < n, ((nvMachine m0).mem (a + BitVec.ofNat 64 t)).isSome = true := by
  intro t ht
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h t ht)
  show (match zesuImage.rodataByte? (a + BitVec.ofNat 64 t).toNat with
    | some b => some (BitVec.ofNat 8 b)
    | none => match nvByte (a + BitVec.ofNat 64 t).toNat with
      | some b => some (BitVec.ofNat 8 b)
      | none => m0.mem (a + BitVec.ofNat 64 t)).isSome = true
  split
  · rfl
  · rw [hb]; rfl

theorem domain_c0 : Domain [0xc0] := by
  have hc : calls [0xc0] = [(outerCall, [0xc0])] := by decide
  have hd : F2.decode [0xc0] = .success true 1 0 := by decide
  refine ⟨?_, by rw [hd]; exact (by decide : 1 + 0 ≤ 2 ^ 30)⟩
  rw [hc]
  intro c hc'
  simp only [List.mem_singleton] at hc'
  subst hc'
  exact Or.inl (by decide)

/-- `Pre` is satisfiable (input `c0`) for any allocator whose heap predicate holds of some
machine with an empty block list and whose private memory lies above `0xa0003000` and away from
the scratch word. -/
theorem pre_of_heap (A : AllocContract zesuImage) (m0 : Machine) (h0 : A.Heap [] m0)
    (hP : ∀ a, A.Priv [] a → 0xa0003000 ≤ a.toNat ∧
      ¬ (Layout.extraParams ≤ a.toNat ∧ a.toNat < Layout.extraParams + 8)) :
    ∃ m, Pre A ⟨[0xc0], []⟩ m := by
  have r1 : (nvMachine m0).reg 1 = 0x80000000 := rfl
  have r2 : (nvMachine m0).reg 2 = 0xa0001800 := rfl
  have r10 : (nvMachine m0).reg 10 = 0xa0002000 := rfl
  have r11 : (nvMachine m0).reg 11 = 0xa0002020 := rfl
  have r12 : (nvMachine m0).reg 12 = 0xa0002040 := rfl
  have hctx : (nvMachine m0).load 0xa0002020 8 = some 0 := by
    rw [nv_load m0 _ 8 (by decide)]; decide
  have hvt : (nvMachine m0).load (0xa0002020 + 8) 8 = some (BitVec.ofNat 64 vtable) := by
    rw [nv_load m0 _ 8 (by decide)]; decide
  have hinp : (nvMachine m0).load 0xa0002040 8 = some 0xa0002060 := by
    rw [nv_load m0 _ 8 (by decide)]; decide
  have hlen : (nvMachine m0).load (0xa0002040 + 8) 8 = some 1 := by
    rw [nv_load m0 _ 8 (by decide)]; decide
  have winp : wordAt (nvMachine m0) 0xa0002040 = 0xa0002060 := by unfold wordAt; rw [hinp]; rfl
  have wlen : wordAt (nvMachine m0) (0xa0002040 + 8) = 1 := by unfold wordAt; rw [hlen]; rfl
  have hbyte : (nvMachine m0).mem 0xa0002060 = some 0xc0 := by
    rw [nv_mem m0 _ (by decide)]; decide
  refine ⟨nvMachine m0, ?_⟩
  simp only [Pre, r2, r10, r11, r12, winp, wlen]
  refine ⟨?_, ⟨by rw [r2]; decide, by rw [r2]; decide, by rw [r2]; decide, ?_⟩,
    by unfold RetAligned; rw [r1]; decide,
    by unfold RamRange; decide, by decide, nv_present m0 _ 24 (by decide),
    by unfold RamRange; decide, by decide, by rw [hctx]; rfl, hvt,
    by unfold RamRange; decide, by decide, by rw [hinp]; rfl, by rw [hlen]; rfl,
    Or.inr (by unfold RamRange; decide), ?_, rfl, domain_c0,
    nv_present m0 _ 8 (by decide), ?_,
    by unfold Apart; decide, by unfold Apart; decide, by unfold Apart; decide,
    by unfold Apart; decide, by unfold Apart; decide, by unfold Apart; decide,
    by unfold Apart; decide, by unfold Apart; decide, by unfold Apart; decide,
    by unfold Apart; decide, by unfold Apart; decide, by unfold Apart; decide,
    by unfold Apart; decide, by unfold Apart; decide, by unfold Apart; decide, ?_⟩
  · intro a b h
    have ha : a < 2 ^ 64 := by
      have := zesu_rodata_range h; unfold Layout.rodataHi at this; omega
    simp [nvMachine, Nat.mod_eq_of_lt ha, h]
  · rw [r2]
    refine nv_present m0 _ stackBytes fun t ht => ?_
    have e : ((0xa0001800 : Word) - BitVec.ofNat 64 stackBytes + BitVec.ofNat 64 t).toNat =
        0xa0001540 + t := by
      have hs : (0xa0001800 : Word).toNat = 0xa0001800 := by decide
      simp only [stackBytes] at ht ⊢
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hs]
      omega
    rw [e]; simp only [nvByte, stackBytes] at ht ⊢; rw [if_pos (by omega)]; rfl
  · intro i hi
    have : i = 0 := by simpa using hi
    subst this
    simpa using hbyte
  · refine A.heap_frame [] m0 _ h0 (fun a ha => ?_) (by simp)
    obtain ⟨h1, h2⟩ := hP a ha
    have hro : zesuImage.rodataByte? a.toNat = none := by
      cases hq : zesuImage.rodataByte? a.toNat with
      | none => rfl
      | some b => have := zesu_rodata_range hq; unfold Layout.rodataHi at this; omega
    have hnv : nvByte a.toNat = none := by
      simp only [Layout.extraParams] at h2
      simp only [nvByte, Layout.extraParams]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg h2]
    simp [nvMachine, hro, hnv]
  · intro a h ha
    obtain ⟨h1, h2⟩ := hP a ha
    have e1 : ((0xa0001800 : Word) - BitVec.ofNat 64 stackBytes).toNat = 0xa0001540 := by decide
    have e2 : (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams := by decide
    have e3 : (0xa0002000 : Word).toNat = 0xa0002000 := by decide
    have e4 : (0xa0002020 : Word).toNat = 0xa0002020 := by decide
    have e5 : (0xa0002040 : Word).toNat = 0xa0002040 := by decide
    have e6 : (0xa0002060 : Word).toNat = 0xa0002060 := by decide
    have e7 : (1 : Word).toNat = 1 := by decide
    simp only [InRange, scratch, e1, e2, e3, e4, e5, e6, e7] at h
    simp only [Layout.extraParams, stackBytes] at h h2
    omega

/-- Contract rule (a): a concrete machine (the witness over `Alloc.initM`, input `c0`) satisfies
`Pre` of the proved allocator. -/
theorem pre_nonvacuous : ∃ m, Pre Alloc.contract ⟨[0xc0], []⟩ m :=
  pre_of_heap Alloc.contract Alloc.initM Alloc.contract_init fun a ha => by
    have := Alloc.contract_priv_nil ha
    unfold Alloc.Arena Alloc.flBase Alloc.posAddr Alloc.heapTop at this
    unfold Layout.extraParams; omega

end ZesuExec.Fn.TX
