# Binary motif analysis

Corpus: 3369 owned instructions in 314 straight-line segments across 111 function instances.

Declared-region addresses 3444, of which 75 are unowned; objdump `.text` has 3984.

## Motifs that could be one `Seg` lemma

| n | occurrences | non-overlapping | owners | FWER p | gross lines | motif |
|---|---|---|---|---|---|---|
| 2 | 56 | 56 | 27 | 1.0000 | 2090 | `slli(r0,r0) or(r0,r0,r1)` |
| 2 | 101 | 101 | 26 | 1.0000 | 3800 | `addi(r0,sp) addi(r0,r0)` |
| 5 | 47 | 47 | 24 | 0.0002 | 4370 | `lbu(r0,r1) lbu(r2,r1) lbu(r3,r1) lbu(r4,r1) slli(r0,r0)` |
| 3 | 36 | 36 | 22 | 0.1190 | 1995 | `lbu(r0,r1) slli(r2,r2) or(r2,r2,r3)` |
| 6 | 34 | 34 | 21 | 0.0002 | 3762 | `lbu(r0,r1) lbu(r2,r1) lbu(r3,r1) lbu(r4,r1) slli(r0,r0) or(r0,r0,r2)` |
| 2 | 75 | 64 | 21 | 1.0000 | 2394 | `ld(r0,sp) ld(r1,sp)` |
| 4 | 21 | 21 | 20 | 0.0012 | 1520 | `slli(r0,r0) or(r0,r0,r1) slli(r2,r2) slli(r3,r3)` |
| 5 | 18 | 18 | 17 | 0.0002 | 1615 | `lbu(r0,r1) slli(r2,r2) or(r2,r2,r3) slli(r4,r4) slli(r0,r0)` |
| 2 | 36 | 34 | 17 | 1.0000 | 1254 | `ld(r0,r1) ld(r2,r1)` |
| 8 | 17 | 17 | 16 | 0.0002 | 2432 | `lbu(r0,r1) lbu(r2,r1) lbu(r3,r1) lbu(r4,r1) slli(r0,r0) or(r0,r0,r2) slli(r3,r3)` |
| 2 | 20 | 20 | 16 | 1.0000 | 722 | `ld(r0,r1) ld(r1,r1)` |
| 2 | 39 | 39 | 15 | 1.0000 | 1444 | `slli(r0,r0) or(r1,r0,r1)` |
| 3 | 23 | 23 | 13 | 0.9440 | 1254 | `slli(r0,r0) slli(r1,r1) or(r0,r1,r0)` |
| 2 | 14 | 14 | 12 | 1.0000 | 494 | `or(r0,r0,r1) or(r2,r3,r2)` |
| 2 | 13 | 13 | 12 | 1.0000 | 456 | `li(r0) addi(r1,sp)` |
| 2 | 21 | 21 | 11 | 1.0000 | 760 | `slli(r0,r0) or(r1,r0,r2)` |
| 3 | 12 | 12 | 11 | 1.0000 | 627 | `li(r0) addi(r1,sp) addi(r1,r1)` |
| 2 | 14 | 14 | 11 | 1.0000 | 494 | `li(r0) mv(r1,r2)` |
| 9 | 10 | 10 | 10 | 0.0002 | 1539 | `lbu(r0,r1) lbu(r2,r1) lbu(r3,r1) lbu(r4,r1) slli(r0,r0) or(r0,r0,r2) slli(r3,r3)` |
| 8 | 10 | 10 | 10 | 0.0002 | 1368 | `lbu(r0,r1) lbu(r2,r1) lbu(r3,r1) lbu(r4,r1) slli(r0,r0) slli(r2,r2) slli(r3,r3) ` |
| 2 | 10 | 10 | 10 | 1.0000 | 171 | `sd(r0,r1) li(r2)` |
| 2 | 17 | 17 | 9 | 1.0000 | 608 | `addi(r0,r1) li(r2)` |
| 2 | 12 | 12 | 9 | 1.0000 | 418 | `li(r0) ld(r1,sp)` |
| 2 | 9 | 9 | 9 | 1.0000 | 304 | `ld(ra,sp) ld(r0,sp)` |
| 3 | 9 | 9 | 9 | 1.0000 | 152 | `addi(sp,sp) sd(ra,sp) sd(r0,sp)` |
| 2 | 60 | 40 | 9 | 1.0000 | 0 | `sd(r0,sp) sd(r1,sp)` |
| 2 | 47 | 47 | 8 | 1.0000 | 1748 | `lui(r0) add(r0,sp,r0)` |
| 3 | 9 | 9 | 8 | 1.0000 | 456 | `slli(r0,r0) slli(r1,r1) or(r2,r1,r0)` |
| 2 | 14 | 12 | 8 | 1.0000 | 418 | `mv(r0,r1) mv(r2,r3)` |
| 3 | 8 | 8 | 8 | 1.0000 | 399 | `or(r0,r1,r0) or(r2,r3,r2) slli(r2,r2)` |
| 2 | 11 | 11 | 8 | 1.0000 | 380 | `addi(r0,r0) mv(r1,r2)` |
| 3 | 8 | 8 | 8 | 1.0000 | 133 | `sd(r0,r1) sd(r2,r1) li(r3)` |
| 2 | 74 | 74 | 7 | 1.0000 | 1387 | `lbu(r0,r1) sd(r0,sp)` |
| 2 | 17 | 17 | 7 | 1.0000 | 608 | `or(r0,r1,r0) ld(r1,sp)` |
| 4 | 7 | 7 | 7 | 0.9734 | 456 | `li(r0) addi(r1,sp) addi(r1,r1) li(r2)` |
| 6 | 6 | 6 | 6 | 0.0104 | 570 | `lbu(r0,r1) slli(r2,r2) or(r2,r2,r3) slli(r4,r4) slli(r0,r0) or(r3,r0,r4)` |
| 2 | 29 | 29 | 6 | 1.0000 | 532 | `or(r0,r1,r0) sd(r0,sp)` |
| 3 | 10 | 10 | 6 | 1.0000 | 513 | `addi(r0,sp) addi(r0,r0) ld(r1,sp)` |
| 3 | 9 | 9 | 6 | 1.0000 | 456 | `addi(r0,sp) addi(r0,r0) mv(r1,r2)` |
| 4 | 6 | 6 | 6 | 1.0000 | 380 | `or(r0,r1,r0) or(r2,r3,r2) slli(r2,r2) or(r0,r2,r0)` |

236 of 668 closed motifs are self-contained.

## Disqualified, by reason

- 273: some occurrences cross an owner boundary
- 88: confined to one function instance
- 66: contains a control transfer
- 3: tandem repeat of period 2: an unrolled loop
- 1: tandem repeat of period 3: an unrolled loop
- 1: tandem repeat of period 5: an unrolled loop

## Controls

- Shuffled corpus: 1 of 11 lengths significant at 0.05 (a working test reports approximately none).
- Planted motif: length 7, planted 9, recovered 9.
- Scheduler invariance n=4: 0 failures in 1194 re-schedulings, against 789 for the order-dependent control.
- Scheduler invariance n=6: 0 failures in 1420 re-schedulings, against 1210 for the order-dependent control.
- Scheduler invariance n=8: 0 failures in 1534 re-schedulings, against 1449 for the order-dependent control.
- Scheduler invariance n=12: 0 failures in 1580 re-schedulings, against 1560 for the order-dependent control.

## Sequence versus dependence-graph classes

| n | windows | distinct sequences | distinct DAG classes | budget exceeded |
|---|---|---|---|---|
| 4 | 2446 | 1049 | 859 | 0 |
| 6 | 2193 | 1269 | 1140 | 70 |
| 8 | 2021 | 1354 | 1245 | 94 |
| 12 | 1769 | 1363 | 1272 | 81 |
