# CI cost of proving the Zesu SSZ endpoint

Measured against the real endpoint (`zesu-ssz-decode.o`, `.text` sha256 `40396298bca935a5…`,
17740 bytes = 4435 instructions). Every number comes from a Lean module that builds.

## What this document is, and what it is not

This measures **elaboration time** — what CI pays to check a proof. It is a real cost and the
numbers are sound.

**It does not answer the motif campaign's question.** That question is whether a motif lemma reduces
the *lines a proof author writes*, and nothing here bears on it. An earlier revision claimed
otherwise, twice, in opposite directions. Both claims are retracted:

- It first concluded a motif lemma addresses only 26% of the cost, saving 12–20% per case. That
  measured elaboration time and presented it as the campaign's answer.
- It then concluded lines obey `n·s → n+s`, saving 48–77%. That was arithmetic on the n-gram study's
  own model, not a measurement of it, and its one supporting observation — that a call site is one
  line — came from `fetchAt`, which is the fetch part only.

The authoring measurement is being taken separately and will land in
`motif-lemma-authoring-cost.md`. Until it does, **no saving figure in this repository is measured.**

## Open

`Seg.stepOf` (`BinaryFv/RiscV/Elfling/Seg.lean`) takes nine arguments — `after`, `run`,
`stepWrites`, `stepMem`, `stepRetired`, `stepPc`, `learn`, `widen`, `keep`. A per-instruction step
in a real composition is that, not a one-line fetch. Whether a motif lemma over `n` instructions
costs less to write than `n` of those is unmeasured, and it is the only question that matters here.

## 1. Rates

`native_decide` against the program image, measured by building modules containing nothing else.

| module | instructions | `native_decide` | wall clock | per call |
|---|---|---|---|---|
| Case F, 6 sites | 24 | 96 | 8.9s | 93ms |
| Case A, all 7 sites | 70 | 280 | 22.0s | 79ms |
| Case B, 6 sites | 90 | 360 | 30.0s | 83ms |
| Case G, 5 sites | 160 | 640 | 54.4s | 85ms |
| Case E, 4 sites | 312 | 1248 | 107.1s | 86ms |
| **all five** | **656** | **2624** | **222.4s** | **84.8ms** |

Linear across a 13× range in module size. Per instruction: **339ms fetch** (4 calls), **~50ms
decode** (`decode_run`), **~136ms execute** (`execute_LOAD_lbu_run`, premises abstract), **~0
retire** (`StepPremises` is carried per segment).

## 2. Why `native_decide` and not `decide`

`decide` cannot read the image at all. It is 17740 bytes emitted as `ByteArray.mk` chunks joined by
`++`, and kernel reduction of that literal overflows the C stack in about three seconds. Raising
`maxRecDepth` does not help — the C stack is what runs out, not the counter.

The pre-wipe layer had settled this: `RegisterWriteStep.fetchInstruction` at `d0f50581` took its
four image lookups as `native_decide` `autoParam`s at 111 call sites. `tools/check_lean_trust.py`
forbids `sorry`, custom axioms, `implemented_by`/`extern` and `unsafe` — not `native_decide`.

This is structural: each instruction owns a different word, so no lemma shares its four evaluations.
**It bounds CI, and it says nothing about authoring cost.**

## 3. The CI floor

| scope | instructions | `native_decide` | time |
|---|---|---|---|
| the study's 149-lemma covering | 3292 | 13168 | **18.6 min** |
| the whole binary | 4435 | 17740 | **25.1 min** |

Irreducible by any arrangement of motif lemmas. Making image reads cheaper is a real project worth
roughly this much CI time — and a different project from this one.

## 4. Other results, measured

- **`0x70` retires** (`BinaryFv/Zesu/Machine/Step0x70.lean`) — the first kernel-backed machine
  theorem on this target. `proof-map.json` had reported
  `formalCoverage: {level4PcCount: 0, localPcCount: 0, rootPcCount: 0}` with its one authoring
  region `blocked` since the pivot.
- **The extractor dropped `DW_AT_call_column`**, collapsing 159 inline instances into 157
  identities. Both collisions were in `alt_fl_alloc.sizeClass`/`sizeClassOfBytes`. Fixed in
  `f961801e`.
- **Case D has 21 provable sites, not 23.** Its motif ends in `auipc`, and at `0x1ef8` and `0x2304`
  that `auipc` carries a `.rela.text` relocation, so its immediate is not final in the object.
- **The retire half was already collapsed** by `StepPremises` before this campaign — one bundle per
  segment. That was the 2.33× in `PLAN_PROOF_PATTERNS.md`.

## 5. Provenance

| fact | where |
|---|---|
| image and geometry | `tools/generate_zesu_program.py`, nix `zesuSszDecodeProgramLean`, determinism-checked |
| fetch obligation | `BinaryFv/Zesu/Machine/Target.lean:fetchInstruction` |
| decode tactic | `BinaryFv/Zesu/Machine/DecodeTactic.lean`, ported from `d0f50581` |
| retire step | `BinaryFv/Zesu/Machine/RegisterWrite.lean` |
| one instruction end to end | `BinaryFv/Zesu/Machine/Step0x70.lean` |
| timings | `CaseA.lean`, `CaseAAllSites.lean`, `CaseB/E/F/G.lean`, `ExecuteCost.lean` |

A wrong byte fails and names the address: `native_decide evaluated that the proposition
programImage.readByte? 112 = some 4 is false`.
