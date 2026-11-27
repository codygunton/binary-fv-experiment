# Statements beside the Rocq contracts

Rocq paths are on zesislar `origin/main`, under `ZesuSsz/Contracts/`.

## F2

`rlp.decodeItem`, entry `0x800d6960`. Lean: `ZesuExec/Fn/F2/Spec.lean`.

End theorem (`ZesuExec/Fn/F2/Proof.lean`):

```lean
theorem f2_spec : Spec zesuImage entry bound Pre Post   -- entry = 0x800d6960, bound = 75
```

Axioms: `propext`, `Classical.choice`, `Quot.sound` (`#guard_msgs` at the end of `Proof.lean`).
It transcribes `decodeItemCallSpecDefinition` (`DecodeItemCallSpec2.v:22-40`) restricted to its
C1-B part, and the compositional register frame (`DecodeItemCompositional.v:17-76`).

| Lean | Rocq | Note |
|---|---|---|
| `Item`, `decode` (`Spec.lean`) | `candidateItem`, `candidateDecodeItem` (`RlpDecodeItem.v:110-146`) | same branches on `Nat` instead of `Z` |
| `bigEndian` | `bigEndian` (`RlpDecodeItem.v:54-55`) | same fold |
| `checkedPayload` | `checkedPayload` (`RlpDecodeItem.v:114-118`) | same |
| `successByte` | `successResult40` (`RlpDecodeItem.v:33-42`) | as a byte function; see difference 6 |
| `errorByte` | `errorResult40` (`RlpDecodeItem.v:44-46`) | same |
| `resultByte`, `result40` | `candidateResult40` (`RlpDecodeItem.v:148-161`) | same; pointer 1 for the `0x80` input |
| `Pre` | `decodeItemC1BDomain` = `decodeItemArgsWellFormed` (`RlpDecodeItemContract.v:44-53`) with `decodeItemEntryLayout` (`RlpDecodeItem.v:76-98`), plus the owned resources of `decodeItemEntryResources` (`RlpDecodeItemContract.v:124-141`) | see differences 1-4 |
| `Post` | `decodeItemExitResources` (`RlpDecodeItemContract.v:143-152`), `decodeItemExitResourcesCompositional` (`DecodeItemCompositional.v:73-76`), `decodeItemAllowsC1B` = `C1BResult` (`RlpDecodeItemContract.v:65-66`, `RlpDecodeItem.v:165-174`) | see differences 5-8 |
| `bound = 75` | none | the longest path: long list with 8 length bytes |

`Pre m`: `RodataLoaded zesuImage m`; `StackOk m 16`; `RetAligned m`; the input
`[a1, a1 + a2)` is `readable` and all its bytes are present; the 40-byte outcome at `a0` is
`writable` (RAM), `a0 % 8 = 0`, all 40 bytes present; input, outcome and the frame
`[sp - 16, sp)` are pairwise `Disjoint` (`separateRanges`, `RlpDecodeItem.v:71-72, 84-88`).

`Post m m'`: `Returns m m'` (pc = `ra` with bit 0 clear; `sp`, `s0`-`s11` restored);
`SameOutside` of the outcome struct and the frame; and for every `input`, `before` with
`BytesAt m a1 input`, `input.length = a2`, `BytesAt m a0 before`, `before.length = 40`:
`BytesAt m' a0 (result40 a1 input before)`.

Deliberate differences:

1. `zisk_input_end` and `zisk_free_input` (`DecodeItemCallSpec2.v:26-27`,
   `decodeItemInputEnd`, `RlpDecodeItem.v:97-98`) are dropped: the input slice is present,
   readable memory (plan S5 step 1). `readable` accepts rodata, input or RAM; Rocq accepts the
   input buffer or RAM (`RlpDecodeItem.v:90-94`). This weakens `Pre`.
2. `a0 % 8 = 0` is added: the outcome is written with `sd`, and the machine faults on
   unaligned accesses. Rocq does not constrain the alignment of `resultPointer`.
3. `StackOk m 16` adds `sp % 16 = 0`, which `decodeItemEntryLayout` does not require (it
   requires `ramBase + 16 ≤ sp ≤ ramEnd`, as `StackOk` does). The frame's 16 bytes must be
   present; Rocq owns them as `↦ₘ?` (any value), the same requirement.
4. `RetAligned m` asks `(ra & ~1) % 4 = 0`; Rocq asks `returnAddress mod 4 = 0`
   (`RlpDecodeItem.v:89`), and pins it through `decodeItemDomainAt`. This weakens `Pre`.
5. Registers: `Returns` gives `pc`, `sp`, `x8`, `x9`, `x18`-`x27`. Rocq also returns `x1`
   unchanged and leaves `x5`-`x7`, `x17`, `x28`-`x31` untouched
   (`DecodeItemCompositional.v:17-54`); `Post` does not state those.
6. The result: `successResult40` states the pointer word as the integer
   `inputPointer + headerLength`; `successByte` stores it modulo `2^64`. They agree because
   `Pre` keeps the input inside a readable interval and `headerLength ≤ length` on success.
   The payload length is below `2^64` (at most 8 big-endian bytes), so `BitVec.ofNat` loses
   nothing; the consumed word is `(header + payload) mod 2^64` in both.
7. `C1BResult`'s other conjuncts are not restated: `inputAddressFits` follows from `Pre`, and
   the `noWrapConsumed ∨ binaryWrapCase` disjunction holds for any natural header and payload.
   The Sail half of `DecodeMeaningModuloKnownBugs` (`RlpDecodeItemContract.v:105-109`) is
   S6 (`ZesuExec/Compliance/F2.lean`), not part of `Post`.
8. Ownership: separation logic becomes `SameOutside` of outcome ∪ frame, so the input and all
   other memory are unchanged; `before`/`input` are universally quantified in `Post` instead of
   being existentials of the precondition.

## Shared machine-level definitions

- `memcpy`: `ziskMemcpy` (`ZesuExec/Service.lean`) transcribes `ziskMemcpyMemory`
  (`ZiskRuntime.v:85`, staged count store, then copy from the staged memory) and
  `ziskMemcpyCallDomain` (`ZiskMemcpyPremise.v`). Difference: the source range must be present
  *readable* memory (rodata, input or RAM), as the plan states, where `ziskMemcpyCallDomain`
  requires writable RAM for the source; the destination must be present RAM. `memcpy_spec`
  (`Logic.lean`): `Spec img 0x800e06c0 3 MemcpyPre MemcpyPost` with `MemcpyPost m m' :=
  ziskMemcpy m = some m'`.
- `AllocAssumptions` (`Fn/Assumed.lean`) transcribes `altFlAllocCallSpec` (`AltFlAllocPremises.v:230`)
  and `altFlFreeCallSpec` (`:263`) without separation logic. `altFlHeap` (`:115`) becomes the
  abstract `Heap L m` over live blocks `L`; the memory it owns (state object, heap words, free
  lists, bump region) becomes the abstract `Priv L`, disjoint from live blocks (`priv_not_live`),
  and `Heap L` survives any change outside `Priv L` (`heap_frame`). Each caller states that its
  own regions avoid `Priv L` (the separation the Rocq `∗` gave). `alloc`: null keeps `Heap L`; a
  block `p` gives `Heap (L ++ [(p, bytes)])`, the block present, in RAM, carved from `Priv L`, and
  `Priv` shrinks. `free`: `Heap (L.erase (p, bytes))`, `Priv` grows by at most the block.
  Differences: the block-alignment fact (`altFlBlockAlignment`) and the slack token are not
  stated (no proof needs them); `alloc` and `free` are bounded by 53 and 42 instructions (the
  plan's figures); requests are `0 < bytes < 2^63`, `log2Align ≤ 3` as in `altFlAllocDomain`
  (`:227`) and `altFlFreeDomain` (`:260`). `remap` is not assumed: it is F0.
- Every `Pre` adds `RodataLoaded zesuImage m`, `StackOk m n` (16-aligned `sp`, `n` present RAM
  bytes below it) and `RetAligned m` (`x1 & ~1` is a multiple of 4: the machine faults on a
  misaligned `jalr` target). Every `Post` has `Returns m m'` (pc = `x1 & ~1`, `sp`, `s0`–`s11`
  restored) and a `SameOutside` frame. `zisk_input_end`/`zisk_free_input` are not modelled (the
  plan's machine has no such registers).

## F0 `alt_fl_alloc.remap` (`Fn/F0/Spec.lean`)

Not in zesislar (warm-up; replaces `altFlRemapCallSpec`, `AltFlAllocPremises.v:251`).
- `Pre m := RodataLoaded ∧ StackOk m 16 ∧ RetAligned m`.
- `Post m m' := Returns m m' ∧ m'.reg 10 = 0 ∧ SameOutside (InRange (sp - 16) 16) m m'`.
- `f0_spec : Spec zesuImage 0x8004218c 9 Pre Post`. Stronger than `altFlRemapCallSpec`, which
  only states the null result: F0 also bounds the frame.
- Non-vacuity: concrete `witness` machine.

## F1 `ensureTotalCapacity` (`Fn/F1/Spec.lean`)

- `Pre A L items m` transcribes `keysEnsureCapacityDomain` (`KeysEnsureCapacityContract.v:53`)
  with the owned resources of `keysEnsureCapacityEntry` (`:99`): header at `a0` read through
  three 8-byte loads (`arrayListHeaderBytes`, `ArrayListContract.v:47`); `arrayListWellFormed`
  (`:56`) with element 32 bytes; the items `BytesAt m p items` and, for capacity > 0, the buffer
  as a live block `(p, capacity·32) ∈ L` (`arrayListBuffer`, `:66`); the allocator object
  `{ctx, alt_fl_alloc.vtable}` (`altFlAllocatorObject`); request `< 2^32`
  (`keysEnsureCapacityMaxRequest`, `:28`); the 8 scratch bytes present; `A.Heap L m`; 128 stack
  bytes (`keysEnsureCapacityStackBytes`, `:25`). The `∗` separations become explicit `Apart`
  facts and "avoids `Priv L`".
- `Post A L items m m'` transcribes `keysEnsureCapacityAllows` (`:69`) and
  `keysEnsureCapacityScratchAfter` (`:88`): request ≤ capacity → code 0, header unchanged, heap
  unchanged, scratch unchanged; else code 0 with header `{p', length, grown(req)}`
  (`arrayListGrownCapacity`, `:32`), the items at `p'`, heap
  `(L minus the old buffer) ++ [(p', grown·32)]`, scratch = the copied byte count; or code 2 with
  everything unchanged. Frame: header, 128 stack bytes, scratch, `Priv L`, old buffer.
- `f1_spec (A) (L) (items) : Spec zesuImage 0x800cb40c 197 (Pre A L items) (Post A L items)`.
- Differences: the list state is read from memory (no ghost `ArrayListState`); the Rocq
  `arrayListWellFormed` after the call is implied by the stated header and range facts but not
  restated as one predicate; `zisk_input_end` not modelled.
- Non-vacuity: `pre_nonvacuous` — for any `A`, any machine `m0` with `A.Heap [] m0` and an
  allocator memory `Priv []` above `0xa0003000` and away from the scratch word, a machine with
  `Pre A [] [] m` exists (built from `m0` by overriding bytes outside `Priv []`).

## F4 `array_list.Aligned([32]u8,null).toOwnedSlice` (`Fn/F4/Spec.lean`)

Shared statement `ToOwned.Pre eb A L items` / `ToOwned.Post eb A L items empty` in
`Fn/F4/Spec.lean`; F4 instantiates `eb = 32` (`keysElementBytes`, `ArrayListContract.v:21`) and
`empty = 1` (`keysEmptyPointer`, `:23`); allocator calls pass log2 alignment 0 (`:22`). Call shape
as `KeysToOwnedSliceCallSpec2.v` (`keysToOwnedSliceCallArgs` `:17`, `BoundaryDomain` `:34`,
`BoundaryAllows` `:49`, `CallSpecDefinition` `:68`).

- `Pre` transcribes `toOwnedSliceDomain` (`ArrayListContract.v:156`) with the resources of
  `toOwnedSliceEntry` (`:222`): `a0` = 24-byte result, present, 8-aligned, in RAM
  (`toOwnedResultBefore` = its entry bytes); `a1` = header read through three 8-byte loads
  (`arrayListHeaderBytes`, `:47`) with `arrayListWellFormed eb` (`:56`): `n ≤ c`,
  `|items| = n·eb`, `0 < p`, capacity > 0 → buffer in RAM and live block `(p, c·eb) ∈ L`
  (`arrayListBuffer`, `:66`), `BytesAt m p items`; `a2` = allocator object `{ctx,
  alt_fl_alloc.vtable}` (`altFlAllocatorObject`); scratch word present; `A.Heap L m`; 112 stack
  bytes, `sp` 16-aligned (`arrayListStackLayout` `:114`, `arrayListToOwnedSliceStackBytes` `:34`);
  return address valid. The `∗` separations become explicit `Apart` facts (result, header,
  allocator object, stack, scratch, buffer) and "avoids `Priv L`".
- `Post` transcribes `toOwnedSliceAllows` (`:179`), `toOwnedSliceScratchAfter` (`:212`) and
  `toOwnedSliceExit` (`:253`): `Returns`; `SameOutside` of result, header, 112 stack bytes,
  scratch, `Priv L`, old buffer; then
  - length 0: header `{empty, 0, 0}` (`arrayListEmpty emptyPointer`), result
    `ResultImage p 0` (`arrayListResultImage before p 0`, `:122`), heap `L` minus the buffer if
    capacity > 0, scratch unchanged;
  - length > 0, success: `∃ p'`, `0 < p'`, `[p', p' + n·eb)` in RAM holding `items`, header
    `{p, 0, 0}`, result `ResultImage p' n`, heap `(L.erase (p, c·eb)) ++ [(p', n·eb)]`, scratch =
    `word64Bytes (n·eb)`;
  - length > 0, OutOfMemory: header unchanged, result `ErrorImage 2`
    (`arrayListErrorImage before 2`, `:126`), heap `L`, scratch unchanged.
- `f4_spec (A) (L) (items) : Spec zesuImage 0x800d677c 194 (Pre A L items) (Post A L items)`.
  Bound 194 = own 87 + remap (F0) 9 + alloc 53 + memcpy 3 + free 42 (the expected value).
- Differences: the list state is read from memory (no ghost `ArrayListState`/`Outcome`); the
  outcome kind is the disjunct taken, not a field; the two `arrayListWellFormed` of the outcome
  and `capacity = length` of the slice are implied by the stated header/range facts, not restated;
  `ResultImage`/`ErrorImage` state the result through loads (8, 8, 2 bytes) plus "bytes
  `[18,24)` (and `[0,16)` on error) unchanged" instead of a byte list; the allocator context
  bound `0 ≤ ctx < 2^64` is the 8-byte load being present; `zisk_input_end` is not modelled.
- Non-vacuity: `example` in `F4/Proof.lean` from `ToOwned.pre_satisfiable` (`F4/Witness.lean`):
  for any `A`, any `m0` with `A.Heap [] m0` and the image's rodata loaded, and a RAM window
  `[0xa0400000, 0xa0401000)` (containing the scratch word) outside `A.Priv []`, overriding the
  window gives a machine with `Pre A [] [] m` (empty list `{1, 0, 0}`).

## F5 `array_list.Aligned(input.AccessListEntry,null).toOwnedSlice` (`Fn/F5/Spec.lean`)

- `Pre`/`Post` = `ToOwned.Pre 40` / `ToOwned.Post 40 … 8` (`entriesElementBytes` `:24`,
  `entriesEmptyPointer` `:26`; allocator calls pass log2 alignment 3, `:25`), the same
  transcription and differences as F4. Call shape `EntriesToOwnedSliceCallSpec2.v` (`:17`, `:34`,
  `:49`, `:68`); contract model `EntriesToOwnedSliceContract.v:23`.
- `f5_spec (A) (L) (items) : Spec zesuImage 0x800d6554 204 (Pre A L items) (Post A L items)`.
  Bound 204 = own 97 + 9 + 53 + 3 + 42 (the expected value).
- Non-vacuity: `example` in `F5/Proof.lean`, same witness as F4.

## S6 compliance

### F2 (`ZesuExec/Compliance/F2.lean`)

Rocq: `DecodeMeaningModuloKnownBugs` (`RlpDecodeItemContract.v:105-109`), `decodeItemBugApplies`
(`:79-102`), `decodeItemSailResult` (`:72-77`), `relateItem` (`RlpDecodeItemSchema.v:51-62`),
`runRlpDecodeItem` (`ZesuSsz/Compliance/SailRun.v:113-115`), `KnownBug`/`knownBugs`
(`ZesuSsz/Compliance/KnownBugs.v`). Sail function: `Evm.Functions.rlp_decode_item`
(`vendor/evm-sail-lean/Evm/Lib/Rlp/Decoding.lean:171`, EVM-Sail d0e4aabd).

```lean
def sailRun (input : List Byte) (σ : SailRegs) : SailItemResult :=
  ((Evm.Functions.rlp_decode_item (k_source_off := 0) (k_source_len := input.length) {}).run
    (hostOf input)).run σ
theorem sailRun_eq : sailRun input σ = match sailItem input with
  | some (l, off, len) => .ok (⟨len, ⟨off + len, ⟨{}, l⟩⟩⟩, hostOf input) σ
  | none => .error .Exit σ
theorem f2_candidate_agrees (input : List Byte) (σ : SailRegs) :
    SailRelates (sailRun input σ) (decode input) ∨ ∃ bug ∈ knownBugs, bugApplies bug input σ
theorem f2_compliance (m : Machine) (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    Reaches zesuImage bound (Compliant m) m
theorem f2_compliance_sail (h : SailLink.Rel zesuImage m s) (hpc) (hpre : Pre m) :
    SailLink.SailReaches zesuImage bound
      (fun s' => ∃ m', SailLink.Rel zesuImage m' s' ∧ Compliant m m') s
```

Axioms of all three: `propext`, `Classical.choice`, `Quot.sound` (`#guard_msgs` in the file).

| Lean | Rocq | Note |
|---|---|---|
| `hostOf input`, cursor `{} : StatelessInputSliceFields 0 input.length` | `initializedInput bytes`, `decodeItemSailCursor` | Lean's host holds the input as `inputBytes`; any Sail register state `σ` |
| `sailRun` | `runRlpDecodeItem` | no `validInputSlice` bound: the Lean host reads `inputBytes.getD` |
| `SailRelates` | `relateItem` on items | field → `.success is_list (full - content) content`; `Error.Exit` → `.error`; other failures → `False` |
| `sailItem`, `sailHeader` | `rlp_decode_item`, `rlp_ref_hdr` | closed forms, proved equal to the Sail run (`decode_item_eval`, `ref_hdr_eval`) |
| `bugApplies .rlpLongLengthWrap` | `decodeItemBugApplies RlpLongLengthWrap` | candidate success with `2^64 ≤ header + payload` (`binaryWrapCase`) and Sail exits; other classes `False` |
| `encode40` | `encodeResult` | `result40 = encode40 · · · (decode input)` (`result40_eq`) |
| `DecodeMeaningModuloKnownBugs` | same name | `after = result40 …` (`decodeItemAllowsC1B`) and, for every `σ`, `after = encode40 … it` with `SailRelates (sailRun input σ) it`, or a listed bug applies |
| `Compliant m m'` | `decodeItemExitResources` + `DecodeMeaningModuloKnownBugs` | `Post m m'` and, for every `input`/`before` as in `Post`, the outcome bytes satisfy the meaning |

Differences: the meaning is stated over items and the 40 outcome bytes, not over Iris resources;
the wrap clause states the candidate success instead of `candidateResult40 … after` (the first
conjunct of `DecodeMeaningModuloKnownBugs` already fixes `after = result40`). Witnesses:
`wrapWitness` (`decodeItemWrapWitnessInput`) inhabits the wrap class; Sail and the candidate agree
on `[0]`.

## F3

`rlp_decode.nextUint64`, entry `0x800d6274`. Lean: `ZesuExec/Fn/F3/Spec.lean`.

End theorem (`ZesuExec/Fn/F3/Proof.lean`, axioms `propext`, `Classical.choice`, `Quot.sound`,
`#guard_msgs` at the end of the file):

```lean
theorem f3_spec : Spec zesuImage entry bound Pre Post   -- entry = 0x800d6274, bound = 160
```

It uses `F2.f2_spec` for the call to `rlp.decodeItem` (proved, not assumed) and transcribes
`nextUint64CallSpecDefinition` (`NextUint64CallSpec2.v:23-48`), i.e. `nextUint64ContractEntry` /
`nextUint64ContractExit` / `nextUint64ContractAllows` (`NextUint64Contract.v:13-48`).

| Lean | Rocq | Note |
|---|---|---|
| `nextUint64` | `nextUint64RootResult`'s case split (`ParentHeaderRootFacts.v:112-133`) | `none` = the error branches (decode error, list, more than 8 payload bytes); `some (value, consumed)` otherwise |
| `resultByte` | `nextUint64Success16`, `nextUint64Error16` (`ParentHeader.v:73-81`), `nextUint64ByteFold` (`ParentHeader.v:68-71`) | value word = big-endian payload; error = words 0 and 3; see difference 7 |
| `sliceByte` | `nextUint64SliceImage` (`NextUint64BlockEntries.v:67-68`) with `nextRestPointer`/`nextRestLength` | `inputPointer + consumed`, `length - consumed` on success, unchanged on error |
| `Pre` | `nextUint64BoundaryDomain` (`NextUint64BlockEntries.v:28-48`) with `nextUint64EntryLayout` (`ParentHeaderRootFacts.v:59-74`), the owned resources of `nextUint64CallSpecDefinition` (slice words, input bytes, 16 result bytes, 96 + 16 stack bytes) | see differences 1-5 |
| `Post` | `nextUint64ContractExit` (`NextUint64Contract.v:20-40`), `nextUint64RootResult` | see differences 6-9 |
| `bound = 160` | none | 17 + 75 (decodeItem) + 13 + 8 * 5 + 15 |

`Pre m`: `RodataLoaded zesuImage m`; `StackOk m 112` (the 96-byte frame and decodeItem's 16 bytes,
`nextUint64CallStackBytes`, `NextUint64CallData.v:13`); `RetAligned m`; result `a0` and slice
`a1`: 16 bytes each, `writable` (RAM), 8-aligned, present; the input `[inp, inp + len)` with
`inp`, `len` the slice's two words (`wordAt`) is `readable` and present; input, result, slice and
`[sp - 112, sp)` pairwise `Disjoint`.

`Post m m'`: `Returns m m'`; `SameOutside` of result ∪ slice ∪ `[sp - 112, sp)`; for every
`input` with `BytesAt m inp input` and `input.length = len`: each result byte `j < 16` is
`resultByte input old j` and each slice byte is `sliceByte inp len input old j`, `old` the byte
on entry.

Deliberate differences:

1. `zisk_input_end`, `zisk_free_input` and `nextUint64InputEnd` are dropped (plan S5 step 1):
   the input is present, readable memory. `readable` (rodata, input or RAM) is weaker than the
   input-buffer-or-RAM condition the domain inherits from `decodeItemEntryLayout`.
2. The input must be disjoint from the slice; `nextUint64EntryLayout` does not require it. Each
   symbolic region is disjoint from the others.
3. Result and slice are 8-aligned (word accesses fault unaligned in this machine); Rocq asks only
   that they lie in RAM.
4. `RetAligned` (`(ra & ~1) % 4 = 0`) is weaker than `returnAddress mod 4 = 0`.
5. The stack: `StackOk m 112` asks `ramBase + 112 ≤ sp ≤ ramEnd`, `16 ∣ sp` and the 112 bytes
   present; Rocq asks `112 ≤ sp < ramEnd` and `16 ∣ sp`, and owns the bytes (`↦ₘ?`).
6. Registers: `Returns` gives `pc`, `sp`, `s0`-`s11`; Rocq also returns `x1` unchanged.
7. Result padding (bytes 10..15 on success) is unchanged; Rocq leaves it unconstrained (stronger
   `Post`). Bytes 0..15 on error are exactly words 0 and 3, as `nextUint64Error16`.
8. The slice words are stated modulo `2^64`; on success `consumed ≤ length` (header ≤ 9 bytes,
   payload ≤ 8 bytes, `checkedPayload`), so there is no wrap and they equal Rocq's integers.
9. `inputAddressFits` follows from `Pre`; the decodeItem meaning modulo known bugs is used only
   through `F2.decode` (= `candidateDecodeItem`); the Sail half belongs to S6.
