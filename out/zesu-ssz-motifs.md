# Binary motif analysis

Corpus: 4435 owned instructions in 761 straight-line segments across 134 function instances.

Artifact totals: 4435 instructions, 37 functions, 159 function instances (123 inlined), 889 blocks; 5442 symbol instruction references.

## Motifs that could be one `Seg` lemma

| n | occurrences | non-overlapping | owners | FWER p | gross lines | motif |
|---|---|---|---|---|---|---|
| 2 | 141 | 96 | 35 | 0.0104 | 0 | `sd(r0,sp) sd(r1,sp)` |
| 2 | 61 | 61 | 29 | 0.9930 | 2280 | `mv(r0,r1) auipc(ra)` |
| 3 | 26 | 26 | 26 | 0.1332 | 475 | `addi(sp,sp) sd(ra,sp) sd(r0,sp)` |
| 2 | 41 | 37 | 25 | 1.0000 | 1368 | `mv(r0,r1) mv(r2,r3)` |
| 2 | 25 | 25 | 25 | 1.0000 | 912 | `ld(ra,sp) ld(r0,sp)` |
| 2 | 64 | 45 | 24 | 1.0000 | 0 | `sd(r0,r1) sd(r2,r1)` |
| 2 | 85 | 83 | 18 | 0.9304 | 3116 | `addi(r0,sp) addi(r1,sp)` |
| 2 | 36 | 36 | 18 | 1.0000 | 1330 | `slli(r0,r0) or(r0,r0,r1)` |
| 4 | 29 | 29 | 17 | 0.0002 | 2128 | `slli(r0,r0) or(r0,r0,r1) slli(r2,r2) slli(r3,r3)` |
| 2 | 31 | 31 | 17 | 1.0000 | 1140 | `or(r0,r0,r1) slli(r2,r2)` |
| 4 | 17 | 17 | 17 | 0.0012 | 304 | `addi(sp,sp) sd(ra,sp) sd(r0,sp) sd(r1,sp)` |
| 2 | 31 | 31 | 16 | 1.0000 | 1140 | `addi(r0,sp) mv(r1,r2)` |
| 3 | 16 | 16 | 16 | 0.9580 | 855 | `ld(ra,sp) ld(r0,sp) ld(r1,sp)` |
| 2 | 16 | 16 | 15 | 1.0000 | 570 | `ld(r0,r1) ld(r1,r1)` |
| 2 | 68 | 68 | 14 | 1.0000 | 2546 | `addi(r0,sp) auipc(ra)` |
| 3 | 22 | 22 | 14 | 0.4497 | 1197 | `mv(r0,r1) mv(r2,r3) auipc(ra)` |
| 2 | 26 | 26 | 14 | 1.0000 | 950 | `slli(r0,r0) or(r1,r0,r1)` |
| 2 | 16 | 16 | 14 | 1.0000 | 570 | `addi(r0,zero) mv(r1,r2)` |
| 2 | 14 | 14 | 14 | 1.0000 | 247 | `sd(r0,sp) mv(r1,r2)` |
| 4 | 17 | 17 | 12 | 0.0012 | 1216 | `lbu(r0,r1) lbu(r2,r1) slli(r3,r3) or(r3,r3,r4)` |
| 6 | 16 | 16 | 11 | 0.0002 | 1710 | `lbu(r0,r1) lbu(r2,r1) slli(r3,r3) or(r3,r3,r4) slli(r0,r0) slli(r2,r2)` |
| 6 | 16 | 16 | 11 | 0.0002 | 1710 | `lbu(r0,r1) lbu(r2,r1) lbu(r3,r1) lbu(r4,r1) slli(r0,r0) or(r0,r0,r2)` |
| 5 | 17 | 17 | 11 | 0.0002 | 1520 | `lbu(r0,r1) lbu(r2,r1) lbu(r3,r1) lbu(r4,r1) slli(r0,r0)` |
| 2 | 17 | 17 | 11 | 1.0000 | 608 | `ld(r0,sp) addi(r1,zero)` |
| 2 | 11 | 11 | 11 | 1.0000 | 190 | `sd(r0,sp) mv(r0,r1)` |
| 3 | 11 | 11 | 11 | 1.0000 | 190 | `sd(r0,sp) sd(r1,sp) mv(r2,r3)` |
| 2 | 11 | 11 | 11 | 1.0000 | 0 | `sd(r0,r1) sh(zero,r1)` |
| 3 | 75 | 34 | 11 | 0.0038 | 0 | `sd(r0,sp) sd(r1,sp) sd(r2,sp)` |
| 8 | 15 | 15 | 10 | 0.0002 | 2128 | `lbu(r0,r1) lbu(r2,r1) lbu(r3,r1) lbu(r4,r1) slli(r0,r0) or(r0,r0,r2) slli(r3,r3)` |
| 5 | 17 | 17 | 10 | 0.0002 | 1520 | `slli(r0,r0) or(r0,r0,r1) slli(r2,r2) slli(r3,r3) or(r2,r3,r2)` |
| 3 | 18 | 18 | 10 | 0.8524 | 969 | `addi(r0,sp) addi(r1,sp) mv(r2,r3)` |
| 6 | 10 | 10 | 10 | 0.0002 | 171 | `addi(sp,sp) sd(ra,sp) sd(r0,sp) sd(r1,sp) sd(r2,sp) sd(r3,sp)` |
| 4 | 54 | 24 | 10 | 0.0002 | 0 | `sd(r0,sp) sd(r1,sp) sd(r2,sp) sd(r3,sp)` |
| 5 | 9 | 9 | 9 | 0.0006 | 760 | `ld(ra,sp) ld(r0,sp) ld(r1,sp) ld(r2,sp) ld(r3,sp)` |
| 2 | 9 | 9 | 9 | 1.0000 | 304 | `or(r0,r1,r0) or(r2,r0,r2)` |
| 4 | 9 | 9 | 9 | 0.2370 | 304 | `addi(sp,sp) sd(ra,sp) sd(r0,sp) mv(r0,r1)` |
| 2 | 9 | 9 | 9 | 1.0000 | 152 | `addi(r0,zero) sd(zero,r1)` |
| 2 | 9 | 9 | 9 | 1.0000 | 0 | `sd(zero,r0) sd(r1,r0)` |
| 7 | 13 | 13 | 8 | 0.0002 | 1596 | `lbu(r0,r1) lbu(r2,r1) slli(r3,r3) or(r3,r3,r4) slli(r0,r0) slli(r2,r2) or(r0,r2,` |
| 4 | 43 | 21 | 8 | 0.0006 | 1520 | `slli(r0,r0) slli(r1,r1) slli(r2,r2) slli(r3,r3)` |

297 of 682 closed motifs are self-contained.

## Disqualified, by reason

- 155: some occurrences cross an owner boundary
- 140: contains a control transfer
- 80: confined to one function instance
- 8: tandem repeat of period 2: an unrolled loop
- 1: tandem repeat of period 1: an unrolled loop
- 1: tandem repeat of period 3: an unrolled loop

## Controls

- Shuffled corpus: 0 of 12 lengths significant at 0.05 (a working test reports approximately none).
- Planted motif: length 7, planted 9, recovered 9.
- Scheduler invariance n=4: 0 failures in 1167 re-schedulings, against 887 for the order-dependent control.
- Scheduler invariance n=6: 0 failures in 1344 re-schedulings, against 1228 for the order-dependent control.
- Scheduler invariance n=8: 0 failures in 1420 re-schedulings, against 1330 for the order-dependent control.
- Scheduler invariance n=12: 0 failures in 1480 re-schedulings, against 1454 for the order-dependent control.

## Sequence versus dependence-graph classes

| n | windows | distinct sequences | distinct DAG classes | budget exceeded |
|---|---|---|---|---|
| 4 | 2214 | 988 | 865 | 0 |
| 6 | 1707 | 1004 | 916 | 78 |
| 8 | 1378 | 941 | 842 | 113 |
| 12 | 983 | 798 | 693 | 112 |
