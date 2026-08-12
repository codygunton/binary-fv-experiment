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
| Case F, 6 sites | 24 | 96 | 8.9s | 93ms |
| Case A, all 7 sites | 70 | 280 | 22.0s | 79ms |
| Case B, 6 sites | 90 | 360 | 30.0s | 83ms |
| Case G, 5 sites | 160 | 640 | 54.4s | 85ms |
| Case E, 4 sites | 312 | 1248 | 107.1s | 86ms |
| **all five cases** | **656** | **2624** | **222.4s** | **84.8ms** |

The rate sits between 79ms and 93ms across a 13× range in module size, and the aggregate is
**84.8ms**. The largest module, Case E at 1248 calls, costs 13.0× the smallest at 96 calls, against
a 13.0× ratio in calls. **The cost is linear in instructions and it does not amortise.**

`decode_run` measured separately: four decodes added 0.2s to a 4.9s module, so **~50ms each**.

So one instruction costs approximately:

The execute half was measured the same way: ten applications of `execute_LOAD_lbu_run` with its
twelve premises abstract, in a module containing nothing else — **1.36s, so ~136ms each**.

| part | cost | shareable by a motif lemma? |
|---|---|---|
| fetch | 4 × 84.8ms = **339ms** | **no** |
| decode | **~50ms** | **no** |
| execute | **~136ms** | **yes — the only part** |
| retire | one `StepPremises` field + 4 `decide` | already shared, per segment |
| **total** | **~525ms** | **26% of it** |

So a motif lemma addresses **26%** of what one instruction costs, and only the `n·s → n+s` fraction
of that 26%.

A caution on the execute figure: 136ms is the cost of *applying* the contract with its premises
abstract. A real site must also prove those twelve premises, which costs more. That makes 136ms a
lower bound on the shareable part — but it is the right lower bound, because the premises a real
site proves are per-site memory facts that a motif lemma cannot share either.

## 3. Per case

Fetch cost for every motif in the campaign, at every one of its sites. This is the part that is
paid whether or not a motif lemma is written.

| case | motif | n | sites | instructions | `native_decide` | wall clock |
|---|---|---|---|---|---|---|
| A | `mem.readInt` | 10 | 7 | 70 | 280 | 22.0s |
| B | `mem.writeInt` | 15 | 6 | 90 | 360 | 30.0s |
| E | `sizeClassOfBytes` | 78 | 4 | 312 | 1248 | 107.1s |
| F | `rawAlloc`/`rawRemap` | 4 | 6 | 24 | 96 | 8.9s |
| G | `decodeTxFields` tail | 32 | 5 | 160 | 640 | 54.4s |

Case E is the study's largest single prize — one lemma covering 7.0% of the binary — and it is also
the largest fetch bill: **107 seconds that the lemma does not touch**.

## 3a. What a motif lemma actually saves, per case

A lemma is proved once (`n` execute contracts) and applied at each site (`s` applications), so
`n·s` execute obligations become `n + s`. Everything else is paid regardless.

| case | n | sites | instr | floor (fetch+decode) | execute, no lemma | execute, lemma | total no | total lemma | saving |
|---|---|---|---|---|---|---|---|---|---|
| A `mem.readInt` | 10 | 7 | 70 | 27.2s | 9.5s | 2.3s | 36.8s | 29.6s | **20%** |
| B `mem.writeInt` | 15 | 6 | 90 | 35.0s | 12.2s | 2.9s | 47.3s | 37.9s | **20%** |
| E `sizeClassOfBytes` | 78 | 4 | 312 | 121.4s | 42.4s | 11.2s | 163.9s | 132.6s | **19%** |
| F `rawAlloc`/`rawRemap` | 4 | 6 | 24 | 9.3s | 3.3s | 1.4s | 12.6s | 10.7s | **15%** |
| G `decodeTxFields` tail | 32 | 5 | 160 | 62.3s | 21.8s | 5.0s | 84.0s | 67.3s | **20%** |
| D `addi mv mv auipc` | 4 | 21 | 84 | 32.7s | 11.4s | 3.4s | 44.1s | 36.1s | **18%** |
| C `mv addi` | 2 | 45 | 90 | 35.0s | 12.2s | 6.4s | 47.3s | 41.4s | **12%** |
| C `ld ld addi` | 3 | 13 | 39 | 15.2s | 5.3s | 2.2s | 20.5s | 17.4s | **15%** |
| **all eight** | | | | | | | **456.4s** | **372.9s** | **18%** |

**Every case lands between 12% and 20%.** The spread the n-gram study predicted — where long motifs
at many sites should dominate short ones — collapses, because the term that varies with `n` and `s`
is only 26% of the cost and the other 74% scales with `n·s` no matter what.

Case C, the short-motif case, is worst at 12%. Case E, the study's largest prize, is 19% — the same
as everything else. **The ranking the study produced does not survive contact with the real cost
model.**

## 4. What this does to the campaign's question

The study proposed 149 class-level motif lemmas covering 74.2% of the binary — 3292 instructions.
Every one of those instructions carries its own fetch and decode regardless:

```
3292 instructions × 4 native_decide × 84.8ms  =  1116s  =  18.6 minutes
```

For the whole binary, 4435 instructions, **25.1 minutes**. That is the floor for proving the covered
part, before any semantic content is proved at all, and no arrangement of motif lemmas avoids it.

**A motif lemma competes only on the execute half**, and there its saving is real. A lemma for the
Case A shape is proved once, chaining ten execute contracts internally, then applied at seven sites:
70 execute obligations become 10 + 7 applications. That *is* `uses × (n−1)`, correctly scoped.

So the study's model is not wrong — it is **misapplied**. It prices the whole instruction at a rate
that only holds for one of its four parts. The correct reading is `uses × (n−1) × (execute share)`,
and the execute share is what section 4a will fix.

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
