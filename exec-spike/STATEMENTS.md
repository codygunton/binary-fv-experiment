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
