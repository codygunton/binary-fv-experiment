# TX `rlp_decode.txAccessList`: cut points, assertions, regions, budgets (S6 design)

Function id `TX`, entry `0x80000000` (`f_80000000`), 323 instructions. The contract is in
`ZesuExec/Fn/TX/Spec.lean` (`Params` = σ: input bytes and allocator live list; `Pre A g`,
`Post A g`). Offsets below are from the entry. `S` = the entry `sp` (the code keeps it in `s0`
from `+0x38` on), so `S-0x1c0` is the slot the code addresses as `-0x1c0(s0)`. Sources: the map
(`zmap show f_80000000`), the annotation file
`/home/cody/zesislar/.worktrees/aa-b5-tx-r41/tools/block/functions/txAccessList.annotations.json`
(rows quoted by id), and `TxAccessListLoopFacts.v` / `TxAccessListBlockEntries.v` in the same
worktree. The per-segment memory accesses were listed from the disassembly by walking each
segment of the map.

## Blocker found while designing: unaligned input loads (resolved by S5 probe 3)

Resolved on branch `probe-unaligned`: `Machine.load`/`Machine.store` take misaligned ranges,
`run_sound` is re-proved, and the Sail link covers them (`ZesuExec/Sail/Forms/Misaligned.lean`).
The `zesu-difftest --fn TX` runs agree on all 16 inputs. The analysis that led to it follows.

Two segments copy input bytes with doubleword loads at input-dependent addresses:

| site | segment | load | address |
|---|---|---|---|
| `+0x130` `+0x134` `+0x138` | ret `0x10c` | `ld`, `ld`, `lw` | the address item's payload pointer (call 3's outcome word 0) |
| `+0x1c4` .. `+0x1d0` | ret `0x1a0` | four `ld` | the key item's payload pointer (call 5's outcome word 0) |

and one segment stores a key with doublewords into the keys buffer at `ptr + 32 * len`:

| `+0x230` .. `+0x23c` | ret `0x1f8` | four `sd` | the keys buffer, allocated with log2 alignment 0 |

The payload of an RLP item starts after its header, so these addresses are aligned only by
accident (zesislar's input set: `one_entry_1_key` puts the address payload at input offset 4).
`Machine.load`/`Machine.store` require natural alignment (`Machine.lean`), so every run through
these sites returns `none` for most inputs. TX therefore needs the S5 probe 3 (unaligned
accesses) before S6 step 5 (runs), not only S7; or, if probe 3 takes its fallback (machine
change behind a predicate), `Pre` must carry that predicate and STATEMENTS.md must say so.
Whether the keys buffer is aligned depends on the allocator (`alloc` with alignment `2^0`); the
`AllocAssumptions` interface does not promise alignment.

## Cut points (fixed rule of the map: entry, loop heads, call return sites)

| cut | why | callee before it | segment ends (longest path, instructions) |
|---|---|---|---|
| `0x80000000` | entry | - | call F2 `+0x64` (26) |
| `0x80000068` | ret | F2 (outer item) | call F5 `+0x49c` (22), cut `0xc4` (23), return (24) |
| `0x800000c4` | loop (outer, `al.len > 0`) | - | call F2 `+0xd4` (5) |
| `0x800000d8` | ret | F2 (entry) | call F2 `+0x108` (13), return (24) |
| `0x8000010c` | ret | F2 (address) | call F2 `+0x158` (20), return (26) |
| `0x8000015c` | ret | F2 (keys list) | call F4 `+0x258` (16), cut `0x18c` (12), return (24) |
| `0x8000018c` | loop (inner, `kp.len > 0`) | - | call F2 `+0x19c` (5) |
| `0x800001a0` | ret | F2 (key) | call F1 `+0x1f4` (22), return (26) |
| `0x800001f8` | ret | F1 (keys capacity) | cut `0x18c` (20), call F4 `+0x258` (25), return (22) |
| `0x8000025c` | ret | F4 (keys to owned slice) | cut `0xc4` (34), call F5 (39), memcpy (56), alloc `+0x3d0` (53), remap `+0x33c` (52), return (58) |
| `0x80000340` | ret | remap (F0, via vtable slot 2) | cut `0xc4` (41), call F5 (46), memcpy (39), alloc (36), return (41) |
| `0x800003d4` | ret | alloc (vtable slot 0) | memcpy `+0x3fc` (9), return (22) |
| `0x80000400` | ret | memcpy | cut `0x42c` (1), free `+0x428` (11) |
| `0x8000042c` | ret | free (vtable slot 3); also join `join-42c` | cut `0xc4` (24), call F5 (29) |
| `0x800004a0` | ret | F5 (entries to owned slice) | return (23) |

The indirect calls `+0x33c`, `+0x3d0`, `+0x428` load their target from the vtable word at
`ao+8` (`Pre`: `0x801136d8`) at offsets `0x10`, `0`, `0x18`; the vtable is rodata (in the image),
so each `.callInd` leaf goal is closed by `RodataLoaded` and the `ao+8` fact: the target is
`alt_fl_alloc.remap` (F0), `alloc`, `free`.

Joins with `fanin_paths ≥ 4` (map `join_cut_candidates`): `0x390`, `0x3e4`, `0x448`, `0x48c`,
`0x4a8` (20), `0x4b8` (21). The annotation file has seeds for `join-248`, `join-42c`,
`join-448`, `join-48c`, `join-4a8`; they become join cuts if S5 probe 1 passes. Without join
cuts, `0x4a8`/`0x4b8` (error exit and epilogue) are re-run inside every segment that reaches
them: cheap (11 + 13 instructions), so they are not needed for run size.

## Regions per cut (design rule: only what the segment starting there reads or writes)

`res` = `a0` at entry (24 bytes), `ao` = `a1` (16), `rest` = `a2` (16), `inp`/`len` = the words
in `rest` at entry. `SAVE` = `[S-104, S)` (ra, s0..s11). Outcome structs of `decodeItem` are 40
bytes, results of `toOwnedSlice` 24.

| cut | regions of the SState | accesses |
|---|---|---|
| entry | `SAVE` (w), `rest` (r) | prologue stores; `+0x48`/`+0x4c` read `inp`, `len` |
| `0x68` | out1 `[S-0x1e8, +40)` (r), list header E `[S-0x1c0, +24)` (w), magic `[S-0x1f0, +8)` (w), `rest` (w), `res` (w), `SAVE` (r) | outcome words; `rest` advanced `+0x94`/`+0x98`; `{8,0,0}`; `0xffffffffcccccccd`; error result; epilogue |
| `0xc4` | none | argument set-up only |
| `0xd8` | out2 `[S-0x1a8, +40)` (r), `res`, `SAVE` | |
| `0x10c` | out3 `[S-0x180, +40)` (r), the address payload in the input (20 bytes, r, unaligned), copy A `[S-0x158, +20)` (w), `res`, `SAVE` | `+0x130..+0x148` |
| `0x15c` | out4 `[S-0x140, +40)` (r), keys header K `[S-0x118, +24)` (w), `res`, `SAVE` | `{s9,0,0}` at `+0x178..+0x180` |
| `0x18c` | none | |
| `0x1a0` | out5 `[S-0x100, +40)` (r), the key payload (32 bytes, r, unaligned), key copy `[S-0xd8, +32)` (w), `res`, `SAVE` | |
| `0x1f8` | K (r/w), key copy (r), the keys buffer slot `[ptr + 32 len, +32)` (w), `res`, `SAVE` | append |
| `0x25c` | F4 result `[S-0xb8, +24)` (r), copy A (r), copy B `[S-0xa0, +20)` (w), E (r/w), `ao` (r), spills `[S-0x240, S-0x1f8)` (w), flag byte `S-0x70` (w), the entries buffer slot `[p + 40 len, +40)` (w), `res`, `SAVE` | growth or append |
| `0x340` | spills (r/w), magic (r), flag byte (w), E (w), entries slot (w), copy B (r), `res`, `SAVE` | |
| `0x3d4` | spills (r), `res`, `SAVE` | |
| `0x400` | spills (r) | vtable slot 3 is rodata |
| `0x42c` | spills (r), E (w), entries slot (w), copy B (r) | |
| `0x4a0` | F5 result `[S-0x88, +24)` (r), `res` (w), `SAVE` (r) | success result `+0x4f4..+0x504` |

Everything else a cut's assertion mentions (finished keys slices, the allocator's other blocks,
the input outside the item being read, the caller's frame, the callee area below `S-576`) is a
machine-level fact of the assertion, carried across segments by `SameOutside`.

## Assertions

Common part `Inv g m0 m` of every cut after the entry (from `frame`, the entry row and the
callee rows): `m0` is the entry machine (part of σ at the cut, with `g`); `Pre A g m0`;
`m.reg 2 = S - 0x240` and `m.reg 8 = S` (after the prologue); `SAVE` holds the entry `ra`, `s0`,
`s1`, `s2..s11` at `S-8 .. S-104` (`frame` slots); `s1 = res`, `s2 = ao`, `s6 = rest` (code
registers, set at `+0x3c..+0x50`); the input bytes unchanged (`BytesAt m inp g.input`); `ao`'s two
words unchanged; the scratch word present; `RodataLoaded`; `A.Heap L' m` for the current live
list `L'` with `L'` = `g.L` ++ the blocks allocated so far (keys slices of finished entries, the
entries buffer, the current keys buffer), each block's bytes as below; `SameOutside` of `res`,
`rest`, `[S-704, S)`, scratch and `A.Priv g.L` from `m0` to `m`.

| cut | assertion beyond `Inv` (annotation rows) |
|---|---|
| `0x68` | F2's `Post` for the outer call: out1 = `F2.result40 inp g.input before` (`call-64`) |
| `0xc4` | `loop-c4`: cursor `x20 = inp + i`, remaining `x21 > 0`, `x21 + i` = outer payload length, `inp ≤ x20`, `x20 + x21 ≤ inp + len`; list E = `{p, n, c}` with `n = |done|`, `n ≤ c`, `40 c` bytes block in `L'`, items = `entriesBytes done images` (`Spec.lean`), each image padding 4 bytes and keys slice in RAM; `OuterWalked g.input (x20 - inp) done` (`TxAccessListLoopFacts.v`, to transcribe over `TX.entriesWalk`); `HeaderFits` of the remaining window; `decode g.input = success true h p`, `0 < p`, `rest` = `{inp + h + p, len - h - p}`; magic word `= 0xffffffffcccccccd` |
| `0xd8` | `0xc4`'s facts with the cursor unchanged; out2 = `result40 x20 window before`; `return-d8`: on the isList bit, the payload window lies in the input |
| `0x10c` | out3 = `result40` of the entry payload; the entry decoded as a list (else the error edge) |
| `0x15c` | out4 = `result40` after the address; address payload = 20 bytes, its pointer inside the input; copy A = those 20 bytes |
| `0x18c` | `loop-18c`: keys cursor `x23 = kp + i`, `x22 + i` = keys payload length, `x22 > 0`, window inside the input, `33 x24 = i`; keys list K = `{q, x24, c}`, items = `concat doneKeys`, block `(q, 32 c)` in `L'` when `c > 0`; `KeysWalked kpayload i doneKeys`; plus `0xc4`'s facts for the enclosing entry (cursor, E, done) and copy A |
| `0x1a0` | `0x18c`'s facts; out5 = `result40` of the remaining keys window |
| `0x1f8` | `0x18c`'s facts; key payload = 32 bytes copied to the key copy slot; F1's `Post`: `c ≥ len + 1` or OutOfMemory (`a0 = 2`) |
| `0x25c` | keys finished (`join-248` content): K handed to F4, F4's `Post` (result at `S-0xb8`: slice `{q', k}` and the new block, or error 2); `doneKeys` = all keys of the entry (`KeysWalked` at the end) |
| `0x340` | `0x25c`'s facts with the growth spills (`S-0x240 .. S-0x1f8`: old capacity, new capacity `c'`, sizes) and F0's `Post` (`a0 = 0`: `dead-344`) |
| `0x3d4` | spills; alloc's `Post`: `a0 = 0` with `Heap L'`, or a fresh block `(a0, 40 c')` |
| `0x400` | `join-42c`'s list `tx_grown` before the free: new block holds the old items (memcpy's `Post`), old block still live |
| `0x42c` | `join-42c`: `tx_grown` = `{s8, n, s9}`, `n < s9`, old block freed (free's `Post`) or old capacity 0 |
| `0x4a0` | `join-48c` content (all entries walked, `done` = the candidate's entries) handed to F5; F5's `Post` (result at `S-0x88`) |

Unreachable paths (each must come out as an infeasible leaf, never as an assumption):
`dead-3e0` (zero-size alloc: `+0x3bc` taken with `40 s9 = 0`, contradicting `s9 ≠ 0` and
`mulhu s9 40 = 0`; leaves of segments `0x25c` and `0x340` through `0x3e0`), `dead-344` (remap
success; F0's `Post` gives `a0 = 0`; leaves of segment `0x340` through `0x344`), `dead-2ec`
(entered only after `0x344`; leaves of `0x340` through `0x2ec`).

Not transcribed yet (needed by the assertions above, not by `Spec.lean`):
`txAccessListOuterWalked`, `txAccessListKeysWalked` (`TxAccessListLoopFacts.v:19-36`), the
`arrayListWellFormed`/`arrayListItems` view of a list header (F1/F4 state it as `HeaderIs`), and
the window lemma `txAccessListListPayloadInInput` (`TxAccessListCallSlice`).

## Budgets

Callee bounds: F2 75, F1 197, F4 194, F5 204, alloc 53, free 42, memcpy 3, F0 9. Segment
constants are the longest paths of the table above; S6 replaces each by the maximum `steps` of
the leaves `sym_run` reports for that segment.

- One key (`0x18c` → `0x18c`): `5 + 75 + 22 + 197 + 20 = 319` ≤ `10 · 33` (an accepted key is
  exactly 33 bytes of the keys payload).
- One entry with `k` keys (`0xc4` → `0xc4`): head `5+75+13+75+20+75 = 263`; keys part
  `≤ 12 + 319 k + 25 + 194 = 231 + 319 k` (or `16 + 194` with no keys); growth to the loop head
  `≤ 52 + 9 + 36 + 53 + 9 + 3 + 11 + 42 + 24 = 239`; total `733 + 319 k` ≤ `32 · (23 + 33 k)`
  (an accepted entry is at least 23 + 33 k bytes).
- Exit after the outer loop: `≤ 46 + 204 + 23 = 273`; error exit from any segment `≤ 58`.

| cut | budget (`r` = outer bytes left `x21`, `kr` = key bytes left `x22`, `R` = outer bytes left after the current entry) |
|---|---|
| entry | `32 · len + 1130` (`26 + 75 + 23 + B(0xc4)`; the empty list exits with `22 + 204 + 23`) |
| `0x68` | `23 + 32 · p + 1006` (`p` = outer payload length) |
| `0xc4` | `32 · r + 1006` |
| `0x18c` | `10 · kr + 219 + 239 + 32 · R + 1006` |
| ret cuts | the budget of the cut the segment reaches next plus the segment's longest path to it, maximised over its exits (e.g. `B(0xd8) = 13 + 75 + B(0x10c)`); each is closed in `r`, `kr`, `R` |

The step budgets of S2's `LeafGoal` (`c'.budget g m' ≤ rem`, and `k.bound + c'.budget ≤ rem` at
calls) then reduce to the inequalities above by `omega` once the leaf's `steps` replace the
static constants.

## Image change for S6 (not run yet)

`tools/gen_image.sh`: add `rlp_decode.txAccessList` to `--functions` and
`"rlp_decode.txAccessList": "TX"` to `SHORT` in `tools/gen_image.py`. TX's 323 words are the
only addition: every callee (F1, F2, F4, F5, F0, alloc, free, memcpy) is in the image, and TX
reads no rodata beyond the vtable `0x801136d8:32`, which is already listed (its only `lui` is the
`1/40` multiplier at `+0xb4`). After that, `ZesuExec/Test/Difftest.lean`'s `segOf` needs
`| "TX" => some Gen.TX`; `tools/snap.py --fn TX` already writes the snapshots (16 inputs of
zesislar's `inputs/txAccessList.json`, all `returned` under Unicorn).

## Compliance (S6 step 8)

`vendor/evm-sail-lean/Evm/Lib/Rlp/Codecs/Transactions.lean` has the decoder:
`decode_access_list` (l.180, `fatal_error RlpDecode` above `2^30` source bytes),
`decode_access_list_entries` (l.171), `_rec_decode_access_list_entries`,
`decode_access_list_keys` (l.127). It counts addresses and slots and returns the encoded
slice; it requires `rlp_cursor_expect_end` after the keys list (the binary ignores trailing
items: known bug `AccessListEntryTrailingBytes`) and decodes the address and keys with
`rlp_decode_word` (known bugs `AccessListAddressLength`, `AccessListKeyLength`;
`TxAccessListBugTriggers.v`). So `Compliance/TX.lean` is possible; no
`compliance-spec-missing` item.

## S6 as built (`Fn/TX/Regions.lean`, `Runs.lean`, `Cuts.lean`)

- 17 cut points: the 15 above plus the store sites `0x80000230` (key into the keys buffer) and
  `0x80000460` (entry into the entries buffer). `storeSym` only stores at constant offsets of a
  region; at both pcs the slot address is in `a0`, and the cut makes it region 5 (32 / 40 bytes).
- Regions: the same five at every cut (frame `[S-576, S)`, result, `rest`, allocator object,
  input), plus the slot at the store sites. `known` facts: the vtable word of the allocator
  object (so the three allocator calls are direct calls into the image), its frame spill at
  `0x80000340`/`0x80000400`, and at `0x8000010c`/`0x800001a0` the payload pointer of the
  `decodeItem` outcome as `ptr input + var 40`.
- Runs: 51 leaves in all (map estimate 53), 8 s for the 17 `sym_run`s together.
- Return-site assertions are `∃ mc, Site mc ∧ callee.Post mc m` (`ARet`): the call-site
  predicate at the machine of the call and the callee's `Post`. Callees with list/items
  parameters (`F1`, `F4`, `F5`, `alloc`, `free`) are families (`famCallee`): `Pre` = some
  instance holds, `Post` = the `Post` of an instance whose `Pre` held.
- Budgets (32 per outer payload byte ahead of the read position; the keys loop also counts 32
  per keys byte, an accepted key costs 319 ≤ 32 · 33): entry `32 len + 424`; `0x68`
  `32 p + 323`; `0xc4` `32 r + 300`; `0xd8` `+220`; `0x10c` `+132`; `0x15c` `+37` (`r` = `s5`);
  `0x18c` `32 (R + kr) + 738`, `0x1a0` `+658`, `0x1f8` `+439`, `0x230` `+744` (`R` = `s5 - s10`,
  `kr` = `s6`); `0x25c` `32 R + 539`, `0x340` `+478`, `0x3d4` `+389`, `0x400` `+377`, `0x42c`
  `+324`, `0x460` `+311`; `0x4a0` `23`.
- Assumption interface: TX needs `AllocAssumptions.Arena`/`arena_split` (`STATEMENTS.md`).
- Join cuts (S5 probe 1 passed; `zmap` now cuts at join candidates by default: TX 21 cuts, 50
  leaves estimated): not taken for TX. `0x448` → `0x460` is straight-line and `0x460` is already
  a cut (store site); `0x48c` is the F5 call, whose call-site predicate `Site49c` covers both
  paths; `0x390`/`0x3e4` lie inside the growth segment and their extra paths are the dead
  `0x344`/`0x3e0` branches; `0x4a8`/`0x4b8` (error result, epilogue) end 20 `ret` leaves, whose
  `Post` goes through one shared error-exit lemma instead of a join cut with its own run and
  generalised state. The 17-cut plan keeps 51 leaves; the join cuts would add 6 cuts and their
  `generalise` matching for a saving of 1 leaf.
