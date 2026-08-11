# `decodeRaw` direct `readOffset` metaprogramming study

Date: 2026-08-10.  Baseline: `5f59ec40`.  This study changes no production proof API.

## Verdict

The four occurrences are one source operation compiled into four interleaved ten-word schedules.
The right reusable unit is not “a function proof” or a contiguous PC interval.  It is an
artifact-derived occurrence descriptor containing the generated `FunctionInstance`, source offset,
ordered owned fragments, live accumulator registers, final destination, and sibling-preservation
set.  Generate the repetitive declarations and use one parameterized fragment-consumption theorem;
keep the interleaving composition handwritten because register lifetimes and sibling order are real
site-specific proof content.

## End-to-end comparison

All identities come from `build/elfling-program-lean/GeneratedProgram.lean`; all instructions and
owners come from `build/machine-regions-lean/machine-regions.json` (the production ELF extraction).
All four identities name `src/stateless/stateless/ssz_raw.zig:ssz_raw.readOffset`, inlined into
`ssz_raw.decodeRaw` at the indicated source call site.  Their shared Lean meaning is
`meaningReadOffset bytes offset`, bridged once by `readOffsetSourceMeaning_eq_lane_or`.

| site | offset | owner | generated regions (words) | non-final fragments | final operands | result | final word → result PC |
|---:|---:|---|---|---|---|---|---|
| 199:23 | 2 | `fi:9` | `10534+4, 10554+5, 105c4+1` | `10534..10540→10544`; `10554..10564→10568` | `a0,x10`; `a2,x12` | `s7,x23` | `105c4→105c8` |
| 200:23 | 6 | `fi:11` | `10544+4, 10578+3, 10590+2, 105c8+1` | `10544..10550→10554`; `10578..10580→10584`; `10590..10594→10598` | `a4,x14`; `a5,x15` | `s9,x25` | `105c8→105cc` |
| 201:23 | 10 | `fi:13` | `10568+4, 10584+3, 10598+2, 105cc+1` | `10568..10574→10578`; `10584..1058c→10590`; `10598..1059c→105a0` | `a1,x11`; `a3,x13` | `s8,x24` | `105cc→105d0` |
| 202:23 | 14 | `fi:15` | `105a0+9, 105d0+1` | `105a0..105c0→105c4` | `a6,x16`; `a7,x17` | `s3,x19` | `105d0→105d4` |

Each occurrence owns exactly ten instructions: four `lbu`, three `slli`, and three `or`.  Across the
contiguous 40-word block `0x10534..0x105d0`, ownership is interleaved in this order:

```
199 lbu×4; 200 lbu×4; 199 slli×3/or×2; 201 lbu×4;
200 slli×3; 201 slli×3; 200 or×2; 201 or×2;
202 lbu×4/slli/or/slli×2/or; final-or 199, 200, 201, 202.
```

Thus instruction semantics are identical modulo five parameter classes: byte offset
`2+4i`, temporary register bank, fragment partition, final register, and the registers belonging to
siblings that must survive each fragment.  Fragment partition is an optimizer result, not derivable
from the source call number: counts are `2,3,3,1`.

## Contract and proof duplication

`Level4Contracts.lean:425-716` already factors the semantic core and generic contract shape:
`ReadOffsetInlineArgs`, lane/shift assembly, fragment input/output, write sets,
`ReadOffsetFragmentContract`, and `ReadOffsetOccurrenceContract`.  The site catalog at
`Level4Contracts.lean:1416-1434` is 19 handwritten lines defining four interfaces and four schedules;
the four contract aliases at lines 1531-1534 add four more identical applications.

`Level4EntryEnvelopeOffsets.lean:1416-2182` spends 767 lines on the non-final reader phase.  Of
those, nine leaf fragment units occupy 563 lines (site starts `199-first`, `200-first`, `199-second`,
`201-first`, `200-second`, `201-second`, `200-third`, `201-third`, `202`).  Every leaf repeats the
same operations:

1. select one tuple from `reader.covers`;
2. build `ReadOffsetInlineArgs` and restrict `DecoderMachinePre`;
3. invoke the generated fragment contract;
4. transport code, memory, `x20`, retirement, and `ParentFrame` through `WritesOnlyRegs`;
5. publish the site-specific `readOffsetFragmentOutput`.

Only the tuple, occurrence interface, input/output register shape, and disjointness proof vary.
The 204 remaining lines in that range are meaningful interleaving compositions and trace appends.
The final-edge composition (`2279-2568`, 290 lines) repeats a four-stage template, but the growing
write-frame chains have depths `0,1,2,3`; generating those chains is safer than pretending they are
definitionally the same proof.

## Measured elaboration cost

Command (ambient heartbeat budget, no overrides):

```
lake env lean --tstack=65536 -Dtrace.profiler=true \
  -Dtrace.profiler.threshold=10 \
  BinaryFv/Zesu/MachineExecution/Level4EntryEnvelopeOffsets.lean
```

Wall time was 43.44 s with verbose 10 ms tracing (the same file without dense tracing was 16.32 s).
The nine leaf theorem elaboration times were `69,63,60,77,65,70,68,65,68 ms`: 605 ms total,
67 ms mean, 17 ms range.  Their handoff-structure kernel checks totaled approximately 1.65 s,
dominated by `Level4ReadOffset199FirstHandoff` at 847 ms.  The composed prefix theorem cost 240 ms;
`level4_read_offset_final_edges` cost 1.629 s and its result structure 427 ms.  Therefore this
abstraction is primarily a correctness/authoring multiplier, not a current build-critical-path fix.

## Prototype and projected reduction

`tools/studies/read_offset_occurrences.py` is a standalone generator/validator prototype.  Its four
records contain precisely the site-specific parameters above.  Against `machine-regions.json` it
checks that every schedule owns exactly its expected PCs, owns ten words, and ends in `or`; it emits
either the audit table or compilable Lean skeletons for the eight interface/schedule declarations:

```
python3 tools/studies/read_offset_occurrences.py
python3 tools/studies/read_offset_occurrences.py --format lean
```

This prototype reproduces the existing schedule declarations exactly (formatting aside) and rejects
an omitted/extra owned PC.  On these four sites generation replaces 19 manually maintained catalog
lines with four descriptor records; the standalone generator itself is 104 lines, so it pays only
when reused across Zesu's many generated `readOffset` instances.

Positive validation passed on the pinned JSON.  A mutation changing the owner of `0x10534` from
`fi:9` to `fi:999` exited 1 with `site 199: schedule/owner mismatch; missing=[66868], extra=[]`.

A realistic next Lean abstraction is a `ReadOffsetFragmentDescriptor` plus one theorem taking:
`interface`, a proven schedule-membership tuple, the parent frame, PC/input facts, and a generated
`RegSet.Disjoint` witness.  Keeping the nine small handoff result types but replacing their bodies by
one-line applications projects the 563 leaf lines to roughly 45 generic theorem lines + 9 wrappers
of about 8 lines + approximately 90 lines of result declarations: about 207 lines, a reduction of
356 lines (63%).  This estimate deliberately leaves all 204 composition lines and all final-edge
ordering intact.  Actual build savings should be expected below one second; the main gain is making
site addition deterministic and forcing artifact/schedule validation before proof authoring.

## Evidence and limits

`machine_regions_test.py` checks that the UI/inventory contains exactly these four direct
`readOffset` rows and validates generated regions. `Level4BoundaryInterfaces.lean` checks adapter
inventory, bounds, representative fragment write sets, all four final write sets, and negative
register cases. `GeneratedScaleEvidence.lean` records ten owned instructions and `meaningTieKind =
"offset"` for all four.  These are structural and measurable-clause checks; they do not empirically
execute all four machine schedules against an independent source oracle.  The common semantic bridge
is kernel-proved, while each occurrence contract remains an assumption at Level 4.  A generator must
not upgrade those contracts to theorems until production-ELF execution, independent source-oracle
comparison, and mutation rejection cover every measurable clause.

Recommendation: generate occurrence descriptors, schedules, interface/alias declarations, exact
write/disjointness facts, and wrapper invocations; retain a single reviewed generic fragment theorem
and handwritten interleaving composition.  This advances `root_compliance` by reducing transcription
risk while preserving the four explicit Level 4 assumptions selected by the UI.
