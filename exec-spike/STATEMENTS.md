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
  and `Heap L` survives any change outside `Priv L` that keeps the live blocks present
  (`heap_frame`; every run keeps present bytes present, `heap_frame'`). Until S5-fix the presence
  premise was missing, which made the structure force every live block to be empty
  (S1StaticMap's `heap_blocks_empty`): `alloc`'s non-null answer was unsatisfiable and F1/F4/F5
  were vacuous for a real allocator. `Test/AllocModel.lean` now builds an instance with a
  non-empty live block (`heap_nonempty`). Each caller states that its
  own regions avoid `Priv L` (the separation the Rocq `∗` gave). `alloc`: null keeps `Heap L`; a
  block `p` gives `Heap (L ++ [(p, bytes)])`, the block present, in RAM, carved from `Priv L`, and
  `Priv` shrinks. `free`: `Heap (L.erase (p, bytes))`, `Priv` grows by at most the block.
  Differences: the block-alignment fact (`altFlBlockAlignment`) and the slack token are not
  stated (no proof needs them); `alloc` and `free` are bounded by 53 and 42 instructions (the
  plan's figures); requests are `0 < bytes < 2^63` as in `altFlAllocDomain` (`:227`) and
  `altFlFreeDomain` (`:260`), and `log2Align ≤ 4` (S7 trust-base change below; zesislar has 3).
  `remap` is not assumed: it is F0.
  **Trust-base change (S7, approved by the user via the coordinator): `log2Align ≤ 3` → `≤ 4`**
  in `alloc_spec` (`a2`) and `free_spec` (`a3`). It diverges from zesislar's
  `altFlMaxLog2Alignment := 3` (`AltFlAllocPremises.v:35`), which the Rocq premises keep. Reason:
  DTF's `txAuthList` buffer of 16-byte aligned `AuthorizationTuple`s calls `alloc`/`free` with 4
  (§ DTF point 7). Evidence that `alt_fl_alloc` handles alignment 16: the source
  (zesislar's `_build/p0c-zesu-source/src/zkvm/alt_fl_alloc.zig`, the linked `zesu.o`) takes the size class
  `max(sizeClassOfBytes len, log2_align - 3)` in both `alloc` and `free` (so `free` recomputes
  `alloc`'s class), a fresh block of class `k` is bump-allocated at alignment
  `max(2^log2_align, 2^(k+3))`, and an oversized request is bump-allocated at `2^log2_align`; the
  ELF agrees (`llvm-objdump -d -M no-aliases`, `build/stock-zisk/zesu-zisk.elf`):
  `alt_fl_alloc.alloc` `0x80042494` masks `a2 & 0x3f`, computes the byte class, then
  `a4 = a2 - 3`, `class = a4` when `a4 ≥ class` (`0x800424bc..0x8004267c`), takes the
  alignment-free path only when `a2 ≤ 3` (`0x80042684`), and the fresh path
  (`0x80042724..0x8004275c`) aligns the heap position to `max(8 << class, 1 << a2)`;
  `alt_fl_alloc.free` `0x80041f38` computes the same class from `a3` (`0x80041f50..0x80042130`)
  before pushing onto `free_lists[class]`. The path with `log2Align = 4` is no longer than with
  `≤ 3` (two instructions instead of three after the class), so the bounds 53 and 42 stand. No
  proof used the old bound beyond restating it: F1, F4, F5 and TX pass 0 or 3, DTF's generated
  `allocArgs` check now admits a literal `≤ 4`; `Test/AllocModel.lean` is unchanged (its
  `alloc_spec`/`free_spec` hold vacuously) and still builds a non-empty instance.
  Assumption-interface change (S6, TX): a fixed set `Arena` (the allocator's state object and
  heap area) with `arena_split`: under any `Heap L m`, `Arena a ↔ Priv L a ∨ InLive L a`. For
  `alt_fl_alloc` this is what `Priv` means (the allocator's memory not handed out as a live
  block of `L`: state object, heap words, free lists, bump region), and `alloc_spec`/`free_spec`
  move bytes between the two halves only. TX needs it because F1, F4 and F5 name only the new
  list in their `Post` (`Heap (L.erase old ++ [new])`): with `arena_split` a block live after
  the call lies in `Priv g.L` or is a block of `g.L`, so `Priv` of the new list stays inside
  `Priv g.L`, the caller's ranges (outside `Priv g.L`) stay apart from new blocks, and TX's
  writes into its blocks fall inside the `Post` frame `Priv g.L`. Without it these facts are
  not derivable. No proof constructs `AllocAssumptions`.
  Fixed arena (evidence): `alt_fl_alloc.zig` (zesislar `_build/p0c-zesu-source/src/zkvm/`) has
  no refill path: `sysAllocAligned` bumps `ZKVM_HEAP_POS` up to `ZKVM_HEAP_TOP` and returns null
  beyond it, `free` pushes blocks on `free_lists` (oversized blocks are leaked, not returned), and
  nothing writes `ZKVM_HEAP_TOP`. A scan of every `auipc`-relative access in
  `zesu-zisk.elf` finds 24 sites addressing `ZKVM_HEAP_TOP` (`0xa0d34528`), all loads; the
  stores go to `ZKVM_HEAP_POS` only. So `Arena` = `alt_fl_alloc.state`/`free_lists`
  (`0xa0534000..`), the two heap words and `[heap base, ZKVM_HEAP_TOP)` is the same set in every
  state; blocks on the free lists and live blocks lie in it. (Other functions inline the same
  bump path on `ZKVM_HEAP_POS`; they stay inside the same arena.)
  Consistency (model sketch): `Arena` as above; `Priv L a := Arena a ∧ ¬ InLive L a`;
  `Heap L m` := the blocks of `L` are pairwise disjoint, inside `Arena` and RAM and present, and
  `m` holds a well-formed `altFlHeapAt` state whose words, free chains and bump region lie in
  `Priv L`. Then `priv_not_live` and `arena_split` hold by definition and `alloc`/`free` keep
  the model. Caveat found while checking this (not caused by the new field): `heap_frame`
  (any `m'` agreeing with `m` on `Priv L` keeps `Heap L`) together with `live_ok`'s
  `Present m' b` forces every live block to be empty (`m'` := `m` with a live byte made absent;
  proved in Lean, scratch `heap_blocks_empty`), so `alloc_spec`'s non-null branch is
  unsatisfiable and the sketch above does not satisfy `heap_frame` as stated; reported to Main.
- Every `Pre` adds `RodataLoaded zesuImage m`, `StackOk m n` (16-aligned `sp`, `n` present RAM
  bytes below it) and `RetAligned m` (`x1 & ~1` is a multiple of 4: the machine faults on a
  misaligned `jalr` target). Every `Post` has `Returns m m'` (pc = `x1 & ~1`, `sp`, `s0`–`s11`
  restored) and a `SameOutside` frame. `zisk_input_end`/`zisk_free_input` are not modelled (the
  plan's machine has no such registers).
- Memory accesses (S5 probe 3): `Machine.load`/`Machine.store` accept any address whose `n` bytes
  lie in one permitted interval (rodata, input or RAM for loads, RAM for stores) and are present;
  natural alignment is no longer required. This matches the profile's Sail model
  (`plat_misaligned_access.load_store = none`: `vmem_read_addr`/`vmem_write_addr` split a
  misaligned access into aligned pieces) and ZisK. Every `Pre`/`Post` above that mentions
  `Machine.load` reads it with this meaning; their text is unchanged. The `Pre` alignment
  conjuncts that only served the old `load` (F2's `out % 8`, TX difference 1) remain and are now
  stronger than needed.

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
- `f1_spec_keep (A) (L) (items) : Spec zesuImage 0x800cb40c 197 (Pre A L items) (PostKeep A L items)`
  (new, S6 TX; `Fn/F1/Proof.lean`, `PostKeep` in `Fn/F1/Vc.lean`): `PostKeep := Post ∧ (req ≤
  capacity → BytesAt m' p items)` — on the no-growth branch the items stay at `p` (the early
  return writes only F1's frame and the header). It is `F1.reach` at the entry cut; `f1_spec` is
  derived from it by dropping the conjunct, its statement unchanged. TX's callee family for F1
  (`f1C`) uses `f1_spec_keep`, since the keys stored so far must survive a call that does not grow
  the keys list.
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

### F3 (`ZesuExec/Compliance/F3.lean`)

Rocq has no stand-alone Sail statement for `nextUint64`; `NextUint64Meaning.v` (header comment)
records that `rlp_decode_uint64` agrees one way and that the binary's acceptance of non-canonical
integers is the known bug `RlpUintNonCanonical` (`KnownBugs.v`), whose trigger
(`ParentHeaderBugTriggers.v:148-162`) tests `sailShortUintCanonical`
(`ParentHeaderSailItems.v:49-60`). Sail functions: `rlp_decode_item`, then `rlp_decode_uint64`
(`Decoding.lean:625`) on its field, the cursor advancing by the field's full length, as in
`_rec_decode_parent_header_fields` at fields 17 and 18 (`StatelessInput.lean:893-950`).

```lean
def sailNext (input : List Byte) : Evm.SailM (Nat × Nat)       -- (value, full length)
def sailRun (input : List Byte) (σ : SailRegs) := ((sailNext input).run (hostOf input)).run σ
theorem sailRun_eq : sailRun input σ = match sailItem input with
  | none => .error .Exit σ
  | some (l, off, len) => if l = false ∧ len ≤ 8 ∧ uintCanon input off len = true
      then .ok ((bigEndian ((input.drop off).take len), off + len), hostOf input) σ
      else .error .Exit σ
theorem f3_candidate_agrees (input : List Byte) (σ : SailRegs) :
    SailRelates (sailRun input σ) (nextUint64 input) ∨ ∃ bug ∈ knownBugs, bugApplies bug input σ
theorem f3_compliance (m) (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    Reaches zesuImage bound (Compliant m) m
theorem f3_compliance_sail (h : SailLink.Rel zesuImage m s) (hpc) (hpre : Pre m) :
    SailLink.SailReaches zesuImage bound
      (fun s' => ∃ m', SailLink.Rel zesuImage m' s' ∧ Compliant m m') s
```

Axioms of all three: `propext`, `Classical.choice`, `Quot.sound`.

| Lean | Rocq | Note |
|---|---|---|
| `nextUint64` (`Fn/F3/Spec.lean`) | `nextUint64RootResult` | candidate, reused |
| `SailRelates` | (none) | Sail `(v, c)` with `v < 2^64` ↔ `some (ofNat v, c)`; `Error.Exit` ↔ `none`; other failures `False` |
| `uintCanon xs off len` | `sailShortUintCanonical` | `rlp_item_uint_canonical` for `len ≤ 55`, proved equal (`uint_canonical_short`) |
| `bugApplies .rlpUintNonCanonical` | `uintNonCanonicalb` at one item | `decode = success false h p`, `p ≤ 8`, `uintCanon … h p = false`, Sail exits; other classes `False` |
| `NextUint64MeaningModuloKnownBugs input` | part of `ParentHeaderMeaningModuloKnownBugs` | `∀ σ`, agreement or a listed bug |
| `Compliant m m'` | `nextUint64ContractExit` + meaning | `Post m m'` and the meaning for every `input` read through the slice as in `Post` |

`rlpLongLengthWrap` never excuses an F3 result (`decode_header_le`: a success has header ≤ 9, and
the candidate accepts only payload ≤ 8). `ParentHeaderUintOver8` concerns base fee, which Sail
decodes with `rlp_decode_u256`, not `rlp_decode_uint64`; it is not part of this comparison.

## F6

`rlp_decode.decodeParentHeader`, entry `0x800d5cb8`. Lean: `ZesuExec/Fn/F6/Spec.lean`.

End theorem (`ZesuExec/Fn/F6/Proof.lean`, axioms `propext`, `Classical.choice`, `Quot.sound`,
`#guard_msgs` at the end of the file):

```lean
theorem f6_spec : Spec zesuImage entry 2178 Pre Post   -- entry = 0x800d5cb8
```

It uses `F2.f2_spec` for the 17 calls of `rlp.decodeItem`, `F3.f3_spec` for the 3 calls of
`rlp_decode.nextUint64` (both proved, not assumed) and `memcpy_spec` for the tail call. It
transcribes `parentHeaderContractResources` / `parentHeaderContractModel`
(`ParentHeaderContract.v`): `parentHeaderArgsWellFormed` (`:108-143`), the entry and exit resources
(`:171-260`) and `parentHeaderAllows` (`:52-60`) with the candidate of
`Candidates/ParentHeaderCandidate.v`.

| Lean | Rocq | Note |
|---|---|---|
| `Kind`, `schedule` | `ParentHeaderFieldKind`, `parentHeaderFieldSchedule` (`Candidates/ParentHeaderDomain.v`) | call PCs dropped |
| `fieldWalk` | `parentHeaderFieldWalk` (`ParentHeaderCandidate.v:76-109`) | final outcome only: `none` = `walkMissingField`/`walkRejectField`, `some vals` = `walkAccept vals`; item decoder `F2.decode` (`candidateDecodeItem`) |
| `walk` | `parentHeaderWalk`/`parentHeaderWalkEnd` (`:112-130`) | `none` also for `walkRejectOuter` |
| `headerFits`, `longWidth` | `headerFits`, `longLengthWidth` (`RlpDecodeItem.v:49-65`) | |
| `ResultOK m' res vals` | `parentHeaderResult80` (`ParentHeaderRootFacts.v:20-24`) with `parentHeaderResult72` (`ParentHeader.v:51-62`) of `candidateHeaderOfValues vals` | words at 0, 8, 16; `OptIs` = `optionalWordAt` (tag byte, value word if present) at 24/32, 40/48, 56/64; bytes 72, 73 zero |
| `ErrorOK m' res` | `parentHeaderError80` (`ParentHeaderRootFacts.v:28-30`) | byte 72 = 3, byte 73 = 0 |
| `Pre` | `parentHeaderArgsWellFormed`, `parentHeaderEntryResources` | see differences 1-5 |
| `Post` | `parentHeaderExitResources`, `parentHeaderAllows` (candidate conjunct of `ParentHeaderMeaningModuloKnownBugs`, `ParentHeaderRung2.v:32`) | see differences 6-9 |
| `bound = 2178` | none | longest path, all 19 fields present with 8-byte integers: 423 own steps + 17 · 75 + 3 · 160 |

`Pre m`: `RodataLoaded zesuImage m`; `StackOk m 512` (the 400-byte frame and the 112 callee
bytes); `RetAligned m`; the input `[a1, a1 + a2)` inside `[inputLo, inputHi]` and present; the
result `a0`: 80 bytes, `writable` (RAM), 8-aligned, present; the scratch word at
`Layout.extraParams` present; `Disjoint` result / `[sp - 512, sp)`, scratch / result, scratch /
`[sp - 512, sp)`; `headerFits input` for the input bytes.

`Post m m'`: `Returns m m'`; `SameOutside` of result ∪ `[sp - 512, sp)` ∪ scratch; for the input
bytes, `walk input = none → ErrorOK`, `walk input = some vals → ResultOK vals`.

Differences:

1. `inputPointer + inputLength ≤ zisk_input_end` is not stated: the Lean machine has no
   `zisk_input_end` register.
2. The result is 8-aligned (the Lean machine's stores are naturally aligned); Rocq states none.
3. `returnAddress mod 4 = 0` is `RetAligned` (`(ra & ~1) mod 4 = 0`, weaker); `sp < ramHigh` is
   `sp ≤ ramHi`.
4. The two read-only constants (`0x80114fb8`, `0x801152b0`) are owned through
   `RodataLoaded zesuImage m` (all of the image's rodata) instead of `↦ₘ∗`; every run keeps them
   (`Preserved`).
5. `↦ₘ?` (owned, any value) becomes "present"; the `∗` separations become `Disjoint` facts; the
   input lies below RAM, so it is apart from the stack, the result and the scratch word.
6. `parentHeaderScratchAfter` (unchanged on the direct path, `word64Bytes 80` on the memcpy
   tail) is weakened to "the 8 scratch bytes are in `SameOutside`'s set".
7. On the memcpy tail Rocq also states that the result is the memcpy source; Lean states
   `parentHeaderError80` for both error paths (the direct path writes only the tag at 72).
8. `headerAfterFrame` (400 bytes) and the callee area: in `SameOutside`'s set, any values.
9. `ParentHeaderMeaningModuloKnownBugs`: its domain conjunct is `Pre`, its candidate conjunct is
   `Post`'s result clause; its Sail conjunct belongs to S6 and is not part of `f6_spec`.

Non-vacuity: `example : ∃ m, Pre m` in `Spec.lean` (empty input at `0x40000000`, result at
`0xa0002000`, `sp = 0xa0001000`).

### F6 (`ZesuExec/Compliance/F6.lean`)

Rocq: `ParentHeaderMeaningModuloKnownBugs` (`ParentHeaderRung2.v:32`), `parentHeaderSailAgrees`,
`sailParentHeaderRun`, `ParentHeaderSharedFields` (`ProjectionParentHeader.v`),
`parentHeaderBugTrigger` (`ParentHeaderBugTriggers.v`). Sail: `rlp_node_cursor`, then
`decode_parent_header_fields cursor 0 EMPTY_PARENT_HEADER_FIELDS` (`StatelessInput.lean:968`), as
`_rec_index_witness_header_cursor` decodes a header.

```lean
def sailRun (input : List Byte) (σ : SailRegs) := ((parentAction input).run (hostOf input)).run σ
theorem parent_eval (hσ : σ.regs.get? .k_execution_profile = some prof) :
    RunRel (hostOf input) σ (sailRun input σ) (sailParent (profMax prof) (profLimit prof) input)
theorem f6_candidate_agrees (input) (σ) (prof) (hσ : σ.regs.get? .k_execution_profile = some prof) :
    SailRelates (sailRun input σ) (walk input) ∨
      ∃ bug ∈ knownBugs, trig (profMax prof) (profLimit prof) bug input
theorem f6_compliance (m) (hpc) (hpre : Pre m) : Reaches zesuImage 2178 (Compliant m) m
theorem f6_compliance_sail (h : SailLink.Rel zesuImage m s) (hpc) (hpre : Pre m) :
    SailLink.SailReaches zesuImage 2178
      (fun s' => ∃ m', SailLink.Rel zesuImage m' s' ∧ Compliant m m') s
```

Axioms of all three: `propext`, `Classical.choice`, `Quot.sound`.

| Lean | Rocq | Note |
|---|---|---|
| `walk` (`Fn/F6/Spec.lean`) | `candidateParentHeader` | candidate, reused |
| `sailRun`, `parentAction` | `sailParentHeaderRun` | Sail run on the whole input, any `σ` whose `k_execution_profile` is `prof` (Rocq: the default profile) |
| `SailRelates` | `parentHeaderSailAgrees` + `ParentHeaderSharedFields` | both reject (`Error.Exit`), or Sail's base fee / blob gas / excess blob gas (with `have_` flags) = candidate values 3/4/5, all `< 2^64`; other failures `False` |
| `sailParent`, `fieldsSpec`, `stepSpec`, `sailNode` | — | closed forms, proved equal to the Sail run (`parent_eval`) |
| `trig maxB limit` | `parentHeaderBugTrigger` | per class, below |
| `ParentHeaderMeaningModuloKnownBugs input` | Sail conjunct of the same | `∀ σ prof`, agreement or a trigger; domain/result conjuncts are `Pre`/`Post` |

Triggers (`ParentHeaderAgree.lean`); "reached" = a field `(i, bytes left)` the candidate walk
`scan` reaches inside the outer payload:

- `rlpLongLengthWrap`: a reached item's header + payload ≥ `2^64`.
- `parentHeaderMissingRequiredField`: the walk runs out before field 12 (includes `c0`).
- `parentHeaderTrailingBytes`: outer header + payload < input length (as Rocq).
- `parentHeaderSkippedFieldShape`: field 0 or 3 is a list or > 32 bytes.
- `parentHeaderBlobGasUnaligned`: field 17 canonical ≤ 8 bytes, value not a whole number of
  `2^17` blobs or more blobs than `prof`'s maximum.
- `rlpUintNonCanonical`: field 15/17/18 a string ≤ 8 bytes with `uintCanon = false`.
- `parentHeaderUintOver8`: field 15 canonical string of 9..32 bytes.
- `parentHeaderUndecodedFieldRejected`: field 9/10/11, no wrap, list or > 8 bytes.
- `parentHeaderExcessBlobGasAboveLimit`: field 18 canonical ≤ 8 bytes above `prof`'s limit.
- `parentHeaderTrailingItemMalformed`: the walk passes field 18 and the rest is not a sequence of
  items `rlp_decode_item` accepts (`ItemsOK`).

Differences from Rocq: blob and excess triggers are per reached field rather than conditioned on
the candidate's overall success (so they also fire where both reject later); the profile limits
come from `σ` instead of the fixed default; no `2^31` input bound is needed (the Lean host reads
`inputBytes.getD`); `headerFits` is not needed by the agreement.

## TX `rlp_decode.txAccessList` (`Fn/TX/Spec.lean`)

Rocq: `TxAccessListContract.v` (`txAccessListArgsWellFormed`, `txAccessListEntryResources`,
`txAccessListExitResources`, `txAccessListResultImage`, `txAccessListHeapImage`,
`txAccessListReturnedHeap`, `txAccessListAllows`), the reference decoder
`Candidates/AccessListCandidate.v` and the domain of `TxAccessListMeaning.v`.

| Lean | Rocq | note |
|---|---|---|
| `EntryValue`, `Candidate`, `keysWalk`, `entryWalk`, `entriesWalk`, `walk`, `candidate`, `calls` | `AccessListEntryValue`, `AccessListCandidate`, `accessListKeysWalk`, `accessListEntry`, `accessListEntriesWalk`, `accessListWalk`, `candidateAccessList`, `accessListCalls` | same recursion and fuel over `F2.decode` (`candidateDecodeItem`); lengths in `Nat` |
| `HeaderFits`, `Domain` | `headerFits` (`RlpDecodeItem.v:58`), `txAccessListDomain` (`accessListHeadersFit` and the `2^30` Sail source limit) | same |
| `OutcomeClass`, `OutcomeAllowed`, `candidateConsumed` | `TxAccessListOutcomeClass`, `txAccessListOutcomeAllowed`, `accessListCandidateConsumed` | same |
| `EntryImage`, `entryBytes`, `entriesBytes` | `TxAccessListEntryImage`, `txAccessListEntryBytes`, `txAccessListEntriesBytes` | keys pointer as a `Word` |
| `Params` | the logical part of `TxAccessListArgs` | input bytes and the allocator's live blocks `L`; the register and saved values are read from the entry machine |
| `Pre A g` | `txAccessListArgsWellFormed` with the owned resources of `txAccessListEntryResources` | see differences 1-4 |
| `OutcomeImage A g`, `Post A g` | `txAccessListResultImage`, `txAccessListHeapImage`, `txAccessListReturnedHeap`, `txAccessListExitResources`, `txAccessListAllows` | see differences 5-8 |

Differences:
1. `res` and `rest` are 8-aligned (`res.toNat % 8 = 0`, `rest.toNat % 8 = 0`): the machine's
   loads and stores are naturally aligned (as F2's outcome pointer). This strengthens `Pre`.
2. `zisk_input_end` (`txInputEnd`, `txAccessListSysRegs`) is dropped: the machine has no such
   register (as F2). The input lies in the input buffer `[2^30, 2^31)` or in RAM (`InputArea`).
3. Ownership `∗` becomes explicit `Apart` facts (the Rocq `separateRanges` list plus the scratch
   word against every other range) and "avoids `Priv L`" for every owned range (as F1).
4. The vtable cells (`altFlVtable`) are rodata (`RodataLoaded`); the allocator object holds
   `{ctx, 0x801136d8}`; `altFlHeap` is `A.Heap g.L`. Allocation alignment (`log2Align` 0 for keys,
   3 for entries) is not stated: `AllocAssumptions` blocks carry no alignment.
5. The Sail half of `TxAccessListMeaningModuloKnownBugs` (`txAccessListSailAgrees` or a known-bug
   trigger) is not in `Post`; it is the compliance statement's (S6 step 8), as for F2. `Domain`
   (which includes the Sail source limit) stays in `Pre`, as in `txAccessListArgsWellFormed`.
6. The returned heap (`txOwnedSlice`, `altFlBlock`) is `A.Heap L'` with `L'` a permutation of
   `g.L ++ returnedBlocks p entries images` on success, `g.L ++ leaked` on error; slice bytes are
   `BytesAt` facts. The success result's bytes 18..23 are unconstrained (as in Rocq).
7. The frame `txAccessListFrameBase ↦ₘ∗ txAfterFrame` and the callee area are the
   `SameOutside` range `[sp - 704, sp)`; the scratch word is `Present` with any value.
8. Registers: `Returns` (pc = `ra`, `sp` and `s0`–`s11` restored); the caller-saved registers
   are unconstrained, as in `txAccessListExitResources`.
- Non-vacuity: `pre_nonvacuous` — for any `A`, any machine `m0` with `A.Heap [] m0` and an
  allocator memory `Priv []` above `0xa0003000` and away from the scratch word, a machine with
  `Pre A ⟨[0xc0], []⟩ m` exists. The decoder is checked by `decide` on four inputs (empty list,
  byte string, one entry with one key, a 19-byte address).
- `bound := 32 · 2^30 + 424` (new def): the entry cut's budget `32 · len + 424` for an input of at
  most `2^30` bytes (input buffer or RAM, `len_le`).
- `tx_spec (A) (g) : Spec zesuImage 0x80000000 bound (Pre A g) (Post A g)` (`Fn/TX/Proof.lean`,
  from `TX.reach`); `tx_sail` by `sail_reaches` (`Fn/TX/Sail.lean`). Cut design: `OPEN/TX/CUTS.md`.
- Compliance (`ZesuExec/Compliance/TX.lean`): `tx_compliance (A) (g) (m) (hpc) (hpre) :
  Reaches zesuImage bound (Compliant A g m) m` and `tx_compliance_sail`, the `_of` forms
  specialised to `tx_spec`; `Compliant := Post ∧ TxAccessListMeaningModuloKnownBugs g.input`.

## DTF `rlp_decode.decodeTxFields` (`Fn/DTF/Spec.lean`) — draft

No zesislar contract exists. Drafted from zesu `b5483dda` `src/stateless/rlp_decode.zig:308-418`
(`decodeTxFields`) and `:420-588` (`txBytesView`, `txU64`, `txNonce`, `txU128`, `txU256`,
`txAddr`, `txAccessList`, `txHashList`, `txAuthList`), the binary (`OPEN/DTF/BLOCKERS.md`) and the
debug object's layout of `input.Transaction` (0x120 bytes; error code at `+0x120`).
`contract: draft`, `review: unreviewed`.

- Decoder: `body t` / `decode t payload` (one parser per field helper over `F2.decode`; the access
  list is TX's reference decoder `TX.candidate`); the bytes after the last field are not read, as in
  the source. Legacy `v`: EIP-155 / pre-155 split of `v_raw` with the `@intCast`s truncated to 64
  bits.
- `Pre A g`: result 0x128 bytes in RAM; allocator object `{ctx, alt_fl_alloc.vtable}`;
  **`tx_type ≤ 4`** (the binary's jump table has no range check; both callers ensure it); payload in
  the input buffer or RAM with `Domain` (TX's domain on the access list's input, when reached, and
  `Fits`: every item header the decoder can reach fits in 64 bits — point 6);
  scratch word, `A.Heap g.L`, separation and "avoids `Priv`" as for TX. Stack: frame 0x370 plus
  TX's 704.
- `Post A g`: `Returns`; frame (result, stack, scratch, `Priv`); the heap gains `fresh` blocks; and
  either error code 0 with `TxAt` of the decoded transaction (every scalar field, optional tags,
  the `data`, `access_list` (TX's `entriesBytes`), `blob_hashes` and `authorization_list` slices),
  or error code 3.

Open (to settle before review):
1. The error disjunct is allowed on every input: allocation failure (mapped to
   `error.InvalidBlock` by every `catch`) is not narrowed to inputs that reach a non-empty
   allocation, and an error is not tied to `decode = none`. A reviewed `Post` should state
   `decode = none → code 3` and restrict allocation failure (as TX's `OutcomeAllowed`).
2. Bytes of the result not written by the decoded variant (the `gas_priority_fee` / `chain_id` /
   `to` payloads when `null`, padding) are unconstrained.
3. (Settled.) Legacy `v`, checked against the disassembly (`0x80002a88..0x80002b28`): `v_raw`
   is a 4-limb u256 (`s10` low limb); `v_raw < 35` iff the high limbs are zero and the low limb is
   below 35. Otherwise `chain_id = ((v_raw - 35) >> 1) mod 2^64` (bits 1..64 of the difference,
   the borrow into limb 1 included: `srli`/`slli 0x3f`/`or`) and `v = (v_raw - 35) & 1`; below
   35 and from 27, `v = v_raw - 27` with `chain_id = null`; below 27, `v = 0`. This is `legacyV`.
   Snapshot `legacy_v_huge` (`v_raw = 2^70 + 36`) gives `chain_id = 0` (2^69 truncated) and
   `v = 1` on all three engines.
4. Heap shape: the returned slices are not tied to the `fresh` blocks (TX's `returnedBlocks`
   form), and leaked blocks on error are not separated from returned ones.
5. Sail agreement (EVM-Sail `decode_legacy_tx`, `decode_access_list_tx`, `decode_fee_market_tx`,
   `decode_blob_tx`, `decode_set_code_tx` in `vendor/evm-sail-lean/Evm/Lib/Rlp/Codecs/Transactions.lean`)
   and the known-bug classes belong to a later compliance statement.
6. (Settled; found in S7 step 4 by DTFCursor, change approved by the coordinator.) `Pre` had no
   header-fit domain for the items DTF itself decodes. `decodeItem` accepts an item whose `h + p`
   wraps (`(h + p) mod 2^64 ≤ len`, e.g. a long string header `0xbf` with `p = 2^64 - 1`), and the
   `data` field then calls the allocator with `n = p` (`0x800016e8`: only `n = 0` is tested) and
   `memcpy(block, ptr, p)`; the assumed allocator contract needs `n < 2^63` (`allocPre`), so the 5
   `data` `alloc` call leaves (from `0x800013c8`, `0x80001748`, `0x800018a4`, `0x80001940`,
   `0x800019dc`) could not be proved on such inputs. Likewise a wrapped list item (hash list,
   authorization list, a tuple) would hand `decodeItem` a slice longer than the input.
   **Change:** `Domain t payload` gains the conjunct `Fits t payload` (`Fn/DTF/Spec.lean`), modelled on
   TX's `Domain` and reusing `TX.HeaderFits`: `ItemsFit` — `HeaderFits` of the first
   `fieldCount t` top-level items (9/11/12/14/13 for `t` = 0..4), each reached while the items before
   it decode (`rest` advancing by `TX.itemRest`, as `skip`), and recursively of the items of every
   list item's payload, two levels deep (access-list entries, versioned hashes, authorization tuples,
   a tuple's fields). It over-approximates the calls the reference decoder reaches (it does not stop
   at a failing field check and descends into a list item at any position); `Domain` stays a single
   `Pre` conjunct, so no proof reading `Pre` by index changed. Checked on the 19 DTF snapshots'
   inputs (`test/snapshots/DTF/*.json`, `tx_type` = `a2`, payload = the `a4` bytes at `a3`): a
   scratch file proves `Fits t payload` for all 19 by `decide +kernel` over a `Bool` mirror
   (`itemsB`, `itemsB_iff`); not committed.
7. (Settled; found in S7 step 4 by DTFAuth, trust-base change approved by the user.) The
   `txAuthList` growth and `toOwnedSlice` paths call the allocator with log2 alignment 4
   (`AuthorizationTuple`, 16-byte aligned): `alloc` at `0x800029f8`/`0x80002c54` (`a2 = 4`),
   `free` at `0x80002a58`/`0x80002f04` (`a3 = 4`). The trusted contract (`Fn/Assumed.lean`)
   mirrored `altFlMaxLog2Alignment := 3` and allowed at most 3, so leaves `800029c8_2`,
   `800022e4_1` (alloc) and `80002a38_1`, `80002ee0_1` (free) were false under it; every
   nonempty authorization list reaches them. **Change:** `alloc_spec`/`free_spec` allow
   `log2Align ≤ 4` (§ `AllocAssumptions` above: evidence from the allocator's source and
   disassembly that alignment 16 is handled; diverges from zesislar).
- Non-vacuity: not yet stated; `decide` checks the decoder on four inputs.
