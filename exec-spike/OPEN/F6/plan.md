# F6 `rlp_decode.decodeParentHeader` (0x800d5cb8): open

State on 2026-11-27 (ProveF2). No F6 Lean module exists yet. F2 (`f2_spec`, bound 75) and F3 (`f3_spec`,
bound 160) are proved and are the callees, with `memcpy_spec` for the tail call.

## Image: resolved (commit 0cd60293, "rodata ranges for F6")

The image now holds `0x80114fb8:80` (`__anon_18759`, the error union that every early error
`memcpy`s into the result at `0x800d5da0`: 72 zeros, `3`, 7 zeros) and `0x801152b0:16`
(`__anon_17344`, `parentHeaderNoneConstant`, read by `ld a0,0(s7)`/`ld a1,8(s7)` at `0x800d61cc`).
F2/F3 use `Fn.zesu_rodata_range` instead of enumerating segments and build against the new image.

Checked in a scratch file (`scratch/f6a.lean`, image extended locally with these two segments): `run`
from the entry and from all 17 call-return points with a generic state evaluates (`some`), except the
four points after the three `nextUint64` calls and the last `decodeItem` call, where `s7`/`s8`/`s2`
must be the frame pointers or the rodata constant (as they are on the real paths), and the three loop
heads, where the cursor must be `ptr input + var` (as in F2/F3). No unaligned access was found.

## Contract to transcribe

`ZesuSsz/Contracts/ParentHeaderContract.v` (`parentHeaderArgsWellFormed` 108-143, entry/exit resources
171-260, `parentHeaderAllows` 52-60), `ParentHeader.v` (`parentHeaderResult72` 51-62),
`ParentHeaderRootFacts.v` (`parentHeaderResult80`, `parentHeaderError80` 20-30),
`Candidates/ParentHeaderCandidate.v` (`parentHeaderFieldWalk` 76-109, `parentHeaderWalk` 112-123,
`candidateParentHeader` 144-149, `parentHeaderCandidateResult` 153-157) and
`Candidates/ParentHeaderDomain.v` (`parentHeaderFieldSchedule`). The Lean result relation is the
candidate walk over `F2.decode` (fields 0-8 skipped, 9-11 required integers inlined, 12-14 skipped,
15 optional integer via `nextUint64`, 16 optional skip, 17-18 optional integers via `nextUint64`),
producing the 80 result bytes (72-byte record and the zero tag halfword at 72, or the copied error union
with tag 3). Domain differences to record: `headerFits` of the outer header is in the Rocq domain and
must be in `Pre`; the scratch word `0xa0400f00` must be present and in `SameOutside`'s set (memcpy
writes the length there); the input-buffer interval and `zisk_input_end` as in F2/F3.

## Proof design (from F3)

- Regions: frame 400 (`sp = ptr 0 400`), result 80, input (unknown size). The callee area (112 bytes:
  decodeItem 16, nextUint64 96 + 16) is below the frame; `StackOk m 512`.
- Cuts: the 20 call-return points and the three loop heads. After every call, decodeItem's (or
  nextUint64's) outcome lies inside F6's frame, so `after_call`/`SState.override` does not apply
  (it requires the regions unchanged). As in F3, each return point is a fresh `entryState` matched
  against a machine-level invariant through `F2.entry_match_vars`: saved `ra, s0..s8` as `known`
  frame words, the cursor `s3 = ptr input + var` and remaining `s2 = var`, the integer values found so
  far (`s5, s6, s4`), the slice words at frame offsets 48/56 (`-352(s0)`, `-344(s0)`) that
  `nextUint64` reads, and the walk state `candidateWalkState` (cursor, remaining, values) of
  `ParentHeaderCandidateWalk.v`. One invariant `Walk k` per schedule position covers the nine
  identical skip calls (11 steps each) with one lemma.
- Loops 0x800d5f88, 0x800d5fec, 0x800d6054: the F3 loop (`Inv`, `loop_reaches`, 5 steps per byte).
- Calls: `Reaches.trans (Reaches.preserve (F2.f2_spec m1 _ hpre))` and `F3.f3_spec`; the memcpy tail
  by `memcpy_spec` with `MemcpyPre` from the rodata source, the result range and the scratch word.
- Bound: own steps per path plus 75 per decodeItem call and 160 per nextUint64 call; the longest path
  is all 19 fields present with 8-byte integer payloads.

## Next command

After the image is regenerated: write `ZesuExec/Fn/F6/{Spec,Regions,Lemmas,Proof}.lean` following
`ZesuExec/Fn/F3/Proof.lean` (`CallState`, `match`, `of_leaf`, `outcome_ok`, `loop_step`), then
`lake build ZesuExec.Fn.F6.Proof`.
