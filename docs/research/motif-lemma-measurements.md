# What a motif lemma can and cannot save

Measurements from the motif lemma campaign, taken against the real Zesu SSZ decode endpoint
(`zesu-ssz-decode.o`, `.text` sha256 `40396298bca935a5…`, 17740 bytes = 4435 instructions).

Everything here is measured on one machine in one build state, from proofs that build. Nothing is
estimated, and the negative results are reported with the same weight as the positive ones.

## 1. The result that matters

**Fetch and decode are per-instruction and cannot be shared by a motif lemma.** Together they are
the majority of what one instruction costs, and no lemma over `n` instructions removes any of it.

The reason is structural, not incidental:

- Fetch is four `native_decide`s against the program image, one per byte. Each instruction sits at
  a different address and holds different bytes, so the four evaluations differ at every one.
- Decode is one `decode_run` per instruction, producing a different `instruction` value each time.

A lemma stated once for the shape `lbu lbu lbu lbu slli or slli slli or or` is still *applied* to
ten distinct words at each of its seven sites. The shape is shared; the words are not.

**The n-gram study's payoff model does not contain this term.** It scored a motif at
`uses × (n−1)`, counting the per-instruction step invocations a motif lemma replaces. That count is
right about the *step* layer and silent about fetch and decode, which is where the time goes.

## 2. Rates

`native_decide` against the image, and `decode_run`, measured by building modules that contain
nothing else.

| module | instructions | `native_decide` | wall clock | per call |
|---|---|---|---|---|
| Case A, one site | 10 | 50 | 4.9s | 98ms |
| Case A, all 7 sites | 70 | 280 | 22.0s | 79ms |
| Case F, 6 sites | 24 | 96 | 8.9s | 93ms |

Between 79ms and 98ms per `native_decide`, and the rate holds as the module grows — 280 calls cost
5.6× what 50 cost, against a 5.6× ratio in calls. **The cost is linear in instructions and it does
not amortise.**

`decode_run` measured separately: four decodes added 0.2s to a 4.9s module, so **~50ms each**.

So one instruction costs approximately:

| part | cost | shareable by a motif lemma? |
|---|---|---|
| fetch | 4 × ~90ms = **~360ms** | **no** |
| decode | **~50ms** | **no** |
| retire | one `StepPremises` field access + 4 `decide` | already shared, per segment |
| execute | per-instruction semantics | **this is the only place a lemma can win** |

Fetch outweighs decode roughly 7:1, and together they are the floor.

## 3. Per case

Fetch cost for every motif in the campaign, at every one of its sites. This is the part that is
paid whether or not a motif lemma is written.

| case | motif | n | sites | instructions | `native_decide` | wall clock |
|---|---|---|---|---|---|---|
| A | `mem.readInt` | 10 | 7 | 70 | 280 | 22.0s |
| B | `mem.writeInt` | 15 | 6 | 90 | 360 | *pending* |
| E | `sizeClassOfBytes` | 78 | 4 | 312 | 1248 | *pending* |
| F | `rawAlloc`/`rawRemap` | 4 | 6 | 24 | 96 | 8.9s |
| G | `decodeTxFields` tail | 32 | 5 | 160 | 640 | *pending* |

## 4. What this does to the campaign's question

The study proposed 149 class-level motif lemmas covering 74.2% of the binary — 3292 instructions.
Every one of those instructions carries its own fetch and decode regardless. At ~90ms per
`native_decide`:

```
3292 instructions × 4 native_decide × ~90ms  ≈  20 minutes
```

of elaboration that no arrangement of motif lemmas can avoid. That is the floor for proving the
covered part of this binary, before any semantic content is proved at all.

**A motif lemma competes only on the execute half.** Whether it wins there is a separate question,
still open, and it is the one Case A's remaining work answers.

## 5. What was already collapsed before this campaign started

The retire half is not a cost per instruction and has not been one since `StepPremises` was
introduced (ported here from the pre-wipe `InstructionStepPlatform`). One bundle is carried across
a whole segment; only the four register disequalities are per instruction, and they are `decide`.

That matters for reading the study: the 2.33× collapse `PLAN_PROOF_PATTERNS.md` measured for
instruction-step families was *this*, and it is already banked. A motif lemma does not get to claim
it again.

## 6. Provenance

| fact | where |
|---|---|
| the image and its geometry | `tools/generate_zesu_program.py`, nix `zesuSszDecodeProgramLean`, determinism-checked |
| the fetch obligation | `BinaryFv/Zesu/Machine/Target.lean:fetchInstruction` |
| the decode tactic | `BinaryFv/Zesu/Machine/DecodeTactic.lean`, ported from `d0f50581` |
| the retire step | `BinaryFv/Zesu/Machine/RegisterWrite.lean` |
| one instruction, end to end | `BinaryFv/Zesu/Machine/Step0x70.lean` |
| Case A | `BinaryFv/Zesu/Machine/CaseA.lean`, `CaseAAllSites.lean` |

Every byte read is checked against the generated image, and the image against the pinned object. A
wrong byte fails and names the address: `native_decide evaluated that the proposition
programImage.readByte? 112 = some 4 is false`.
