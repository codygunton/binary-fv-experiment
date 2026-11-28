# Go report sections

## S17

Map precision, no proofs. Python in `tools/zmap/precision.py` (hooks in `analyze.py`), tests in
`tools/zmap/tests/test_precision.py`; `map/static.json` regenerated (`zmap build`, 40 s wall).

**Method.** One forward abstract interpretation per function computes, at every indirect call
and jump, a term for the target address (the backward slice of the pointer source, field
`slice`). Values: constants, small constant sets, entry arguments, frame offsets, loads,
bounded index ranges (byte/halfword loads, low-bit masks, `bltu`/`bgeu` against a constant).
Frame slots are tracked; a call marks unknown the slots its callee may write through a pointer
argument (per-function write summaries: argument and offset window, least fixpoint, three
rounds); `memcpy`/`memmove`/`memset` copy or fill frame slots; a CSR instruction writes through
its operand. Assumptions are listed in the module docstring (map, not proof).

**Sites by resolution kind** (the 458 indirect call sites of the S0–S8 target set):

| Kind | Sites | Notes |
|---|---|---|
| exact | 49 | constant or slot of a constant `.rodata` table; 1 target each |
| precondition | 392 | field chain from an argument; targets from callers: 348 have targets, 296 complete, 44 none |
| unknown | 17 | value merged from paths or computed (`deinit`s, `executeIterative`, `_zisk_main`, …) |

All 504 sites of the binary: exact 49, precondition 437, unknown 18. The target set is now 222
functions (16 added: slots of the journal and allocator vtables whose address target code
materialises, and their callees); its 461 sites: exact 49, precondition 394, unknown 18.

**Heuristic against exact.** Of the 345 sites with complete targets, 342 have targets inside
the old candidate list, which held 1006 false candidates there (`Io.Writer.*` and journal
functions on allocator calls); 3 sites the heuristic left unresolved now resolve
(`scratch_arena.free` in `rlpBlobVersionedHashes`, `rlpAuthorizationList`). Checked by reading
disassembly: `txAccessList` `0x800003d0` (`ld a4,0(t0)`, `t0 = ld 8(a1)`; the only caller
chain passes guestMain's allocator at `0x801136d8`: `alt_fl_alloc.alloc` only, was 4
candidates), `0x8000033c`/`0x80000428` (`remap`, `free`); guestMain `0x8003ca0c` (`a5 = ld
0(ld -0x760(s0))`, slot written at `0x8003c984` with `0x80113708`: `Io.Writer.fixedDrain`);
`rlpBlobVersionedHashes` `0x80004864` (`ld 0x18(ld 8(s4))`: `free`); `ExecuteEvm.execute`
`0x8000d630` (`finalizeCreateFn`); runDispatch `0x800ab1b8` (`lbu`, `slli 3`, table
`0x80113d20`, 256 slots, 87 handlers); memset `0x800e0714` (`andi 0xff`, `slli 4`, base
`0x800e0720`: 256 targets).

**Indirect jumps** (S0–S8 target set): before 175 unresolved, 18 `table-heuristic`; after 188
`exact`, 5 `precondition` (the index reaches past the table, its bound is the argument's type:
`decodeTxFields` tx type, `JournalEntry.revert` tag, `guestMain`, `executeBlockStateless`,
`transitionWithContext`). runDispatch: 174/174 exact; memset: exact.

**Recursion and states.** Recursive target functions 19 → 7 (`builder.buildNode`,
`main.batchUpdateNodeIndexed`, `main.updNodeEx`, two `updNodeExImpl`, `ssz_output.sparseRoot`,
`progressiveRootAt`); `scratch_arena.alloc` is not recursive. States: ready 18 → 31, waiting 44
→ 38, blocked 318 → 317, out 132 → 126.

**Irreducible functions.** Cuts in the old map, cuts before cycle cuts (new blocks), after:

| Function | Old cuts | Uncut cycle regions (old) | Cuts before | Cycle cuts | Cuts after | Multi-entry regions (entries, blocks) |
|---|---|---|---|---|---|---|
| `ExecuteEvm.execute__anon_3724` | 266 | 0 | 266 | 0 | 266 | 1 (2, 19) |
| `BaTracker.computeHash__anon_5051` | 1032 | 3 (24 blocks) | 1032 | 3 | 1035 | 6 (2 each; 64, 59, 29, 9, 9, 9) |
| `transitionWithContext__anon_2321` | 729 | 0 | 728 | 0 | 728 | 2 (2, 220; 2, 177) |
| `main.executeBlockStateless` | 531 | 0 | 531 | 0 | 531 | 3 (2, 96; 2, 78; 2, 22) |
| `sort.block.block__anon_10892` | 727 | 3 (24 blocks) | 727 | 3 | 730 | 3 (2, 9 each) |
| `sort.block.block__anon_11541` | 776 | 0 | 776 | 0 | 776 | 1 (2, 13) |
| `BaTracker.detectAndRecord__anon_2554` | 145 | 0 | 145 | 0 | 145 | 1 (2, 43) |
| `runDispatch__anon_13271` (new: dispatch resolved) | 40 | 0 | 174 | 0 | 174 | 1 (86, 1026) |

In five of the seven, the existing cuts (loop heads, return sites, join cuts) already break
every cycle; two need 3 cuts each. Every cycle of every target function now passes a cut
(test), so `irreducible` is no longer a blocker (the flag and class stay).

**Fallbacks.** Contingency S17 applies to 17 unknown sites and 44 precondition sites with no
target; proofs treat every indirect call as a leaf goal anyway.

**Viewer.** Call-graph edges carry `resolution` `exact`/`precondition` (the colours in
`graph.html`); unknown sites have no targets, so no edges. `irreducible_regions` (`entries`,
`nodes`) is in `map.json` for the hatched hulls; `site.py` does not emit it yet (S9.2).

**Forecast.** The target set grows by 16 functions; the irreducible class needs 6 extra cut
points in total, not a new mechanism; 12 fewer recursive functions leave the S15 class to the
seven above.
