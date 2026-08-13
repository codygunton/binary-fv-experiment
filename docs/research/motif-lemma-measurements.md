# What a motif lemma saves

Measurements from the motif lemma campaign, against the real Zesu SSZ decode endpoint
(`zesu-ssz-decode.o`, `.text` sha256 `40396298bca935a5…`, 17740 bytes = 4435 instructions).

## 0. A correction to an earlier version of this document

An earlier revision measured **elaboration time** and concluded that a motif lemma addresses only
26% of the cost, saving 12–20% per case. **That measured the wrong quantity.** The campaign exists
to reduce *proof authoring* cost — lines written and time spent writing them. Elaboration time is a
real operational cost but it is not the bottleneck, and the two move in **opposite directions**.

They diverge because of `autoParam`. An obligation discharged by an `autoParam` still costs its full
elaboration at every site, but it costs the author nothing, because nothing is written for it.

| quantity | shareable by a motif lemma? |
|---|---|
| elaboration time | **barely** — 4 `native_decide` per instruction, always, whatever the lemma |
| lines at a call site | **almost entirely** — one line per obligation, and a lemma removes `n−1` of every `n` |

The elaboration numbers below are kept because they are true and they bound CI cost. They are not
the campaign's answer.

## 1. The answer: lines

At a call site, one obligation is **one line**, whatever part of the instruction it belongs to:

```
fetchAt s 0x70 0x03 0x45 0x16 0x00 l
```

Measured: the ten instructions of Case A's motif, one line each, in
`BinaryFv/Zesu/Machine/AuthoringCost.lean`. The bytes stay explicit — they cannot be implicit,
because `native_decide` needs a closed goal and a metavariable byte fails with *"Expected type must
not contain metavariables"*. It is the four *proofs* an `autoParam` removes, not the four literals.

So lines obey `n·s → n+s` across the **whole** instruction. A lemma is written once, containing `n`
lines, then applied at each of `s` sites for one line apiece.

| case | motif | n | sites | no lemma | with lemma | saving |
|---|---|---|---|---|---|---|
| G | `decodeTxFields` tail | 32 | 5 | 160 | 37 | **77%** |
| B | `mem.writeInt` | 15 | 6 | 90 | 21 | **77%** |
| A | `mem.readInt` | 10 | 7 | 70 | 17 | **76%** |
| E | `sizeClassOfBytes` | 78 | 4 | 312 | 82 | **74%** |
| D | `addi mv mv auipc` | 4 | 21 | 84 | 25 | **70%** |
| C | `ld ld addi` | 3 | 13 | 39 | 16 | **59%** |
| F | `rawAlloc`/`rawRemap` | 4 | 6 | 24 | 10 | **58%** |
| C | `mv addi` | 2 | 45 | 90 | 47 | **48%** |
| **all eight** | | | | **869** | **255** | **71%** |

**The saving rises with `n`, exactly as the n-gram study predicted.** At seven sites: n=2 saves 36%,
n=4 saves 61%, n=10 saves 76%, n=32 saves 83%.

**So the study's ranking is sound in the currency that matters.** `uses × (n−1)` is a good proxy for
lines saved, and the earlier revision of this document was wrong to say otherwise. Long motifs at
many sites really do beat short ones: 77% against 48%, a spread the elaboration-time view flattened
to 20% against 12%.

## 2. Elaboration time, for completeness

Not the campaign's answer, but it bounds CI cost and it is genuinely unshareable.

| module | instructions | `native_decide` | wall clock | per call |
|---|---|---|---|---|
| Case F, 6 sites | 24 | 96 | 8.9s | 93ms |
| Case A, all 7 sites | 70 | 280 | 22.0s | 79ms |
| Case B, 6 sites | 90 | 360 | 30.0s | 83ms |
| Case G, 5 sites | 160 | 640 | 54.4s | 85ms |
| Case E, 4 sites | 312 | 1248 | 107.1s | 86ms |
| **all five** | **656** | **2624** | **222.4s** | **84.8ms** |

Linear across a 13× range. Per instruction: **339ms fetch, ~50ms decode, ~136ms execute, ~0 retire**.

`decide` cannot read the image at all — the `ByteArray` literal overflows the C stack — so
`native_decide` is structural here, not a convenience. The pre-wipe layer had settled this: it used
`native_decide` autoParams at 111 call sites.

Floor for the 149-lemma covering's 3292 instructions: **18.6 minutes**. Whole binary: **25.1**.
No arrangement of motif lemmas reduces it. That is a real argument for making image reads cheaper —
but it is an argument about CI, not about authoring.

## 3. What else the campaign established

- `0x70` retires — the first kernel-backed machine theorem on this target.
  `proof-map.json` had reported `formalCoverage: {level4PcCount: 0, …}` with its one authoring
  region `blocked` since the pivot.
- The extractor dropped `DW_AT_call_column`, collapsing 159 inline instances into 157 identities.
  Both collisions were in `alt_fl_alloc.sizeClass`/`sizeClassOfBytes` — Case E's family.
- Case D has 23 sites in the study but **21 provable**: its motif ends in `auipc`, and at `0x1ef8`
  and `0x2304` that `auipc` carries a `.rela.text` relocation.
- The retire half was already collapsed by `StepPremises` before the campaign began — one bundle per
  segment. That was the 2.33× in `PLAN_PROOF_PATTERNS.md`, and a motif lemma cannot claim it twice.

## 4. Provenance

| fact | where |
|---|---|
| image and geometry | `tools/generate_zesu_program.py`, nix `zesuSszDecodeProgramLean`, determinism-checked |
| the fetch obligation | `BinaryFv/Zesu/Machine/Target.lean:fetchInstruction` |
| **lines per call site** | `BinaryFv/Zesu/Machine/AuthoringCost.lean` |
| decode tactic | `BinaryFv/Zesu/Machine/DecodeTactic.lean`, ported from `d0f50581` |
| retire step | `BinaryFv/Zesu/Machine/RegisterWrite.lean` |
| one instruction end to end | `BinaryFv/Zesu/Machine/Step0x70.lean` |
| elaboration timings | `CaseA.lean`, `CaseAAllSites.lean`, `CaseB/E/F/G.lean`, `ExecuteCost.lean` |

A wrong byte fails and names the address: `native_decide evaluated that the proposition
programImage.readByte? 112 = some 4 is false`.
