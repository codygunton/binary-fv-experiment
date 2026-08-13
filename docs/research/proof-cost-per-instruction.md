# Where the proof lines actually go

Measured on `rebase/hlevel2-contracts`, the in-progress Level 1 / Level 2 work, which targets the
same `ssz_decode_root` endpoint as the motif campaign.

This exists because the motif campaign nearly drew the wrong conclusion from the wrong denominator.
Proof code scales with the RISC-V it covers, so the metric is **lines per instruction covered**.

## 1. The rate

| | |
|---|---|
| `BinaryFv/Zesu/MachineExecution` | **14,975 code lines** across 439 declarations |
| distinct instruction addresses covered | **455** |
| **lines per instruction** | **33** |
| extrapolated to the whole 4435-instruction endpoint | **≈146,000 lines** |

That number is the campaign's real target. Everything else is a means to reduce it.

## 2. Composition is 80% of it

Classifying by declaration — how many distinct instruction addresses each theorem mentions:

| bucket | declarations | lines | share | lines / decl |
|---|---|---|---|---|
| touches 0 addresses (generic infrastructure) | 153 | 1,979 | 13.2% | 12.9 |
| touches 1 address | 42 | 985 | 6.6% | 23.5 |
| **touches ≥2 addresses — multi-instruction composition** | **244** | **12,011** | **80.2%** | **49.2** |

Inside the composition bucket: 1,358 address-slots over 12,011 lines = **8.8 lines per instruction
of composition**.

The largest are handoffs across many instructions:

| lines | addresses | declaration |
|---|---|---|
| 368 | 16 | `Level1WriteSuccessSteps.writeSuccessSecondMemcpyHandoff` |
| 289 | 17 | `Level1WriteSuccessSteps.writeSuccessTransactionsHandoff` |
| 287 | 14 | `Level2RuntimeLeaves.readInputInstanceContract` |
| 269 | 29 | `Level1WriteSuccessSteps.writeSuccessFirstTenTailPairsHandoff` |
| 219 | 30 | `Level1DecodeInputSteps.decodeInputSavePrefix` |

**A motif lemma reduces exactly this bucket.** That is what makes the campaign's measurement
load-bearing rather than academic.

## 3. What the measured saving is worth here

`motif-lemma-authoring-cost.md` measures a motif lemma cutting composition by 32% (n=2) to 70%
(n=32), across five cases that build.

| | lines |
|---|---|
| composition in the current 455-instruction coverage | 12,011 |
| saved at the measured 32–70% | **3,800 – 8,400** |
| as a share of all 14,975 lines | **26% – 56%** |

Extrapolated to the whole endpoint at the current rate:

| | lines |
|---|---|
| 4435 instructions, no motif lemmas | ≈146,000 |
| with composition cut 50% | ≈87,000 |
| **saved** | **≈58,000** |

## 4. A note on method, because the first attempt was wrong

Classifying *lines* by leading tactic put 49% into "other" — the bulk is continuation lines of
multi-line expressions, so a line does not have a single role. The declaration is the right unit,
and "how many distinct addresses does this theorem mention" is the right discriminator, because it
separates composition from per-instruction work without needing to parse tactics.

The first classifier was not merely imprecise; it reported composition at 3.7% when it is 80%. A
classifier whose largest bucket is "other" has not classified anything, and should be discarded
rather than interpreted.

## 5. Reproduce

```
git show rebase/hlevel2-contracts:BinaryFv/Zesu/MachineExecution/<file>.lean
```
for the six `MachineExecution` files, then count declarations and the distinct `0x[0-9a-f]{3,}`
literals each mentions. Code lines exclude blanks and comment lines.
