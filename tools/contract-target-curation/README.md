# Contract-target curation tool

An interactive flame graph over the pinned production binary, for hand-picking the set of function
instances to write local contracts for. Built 2026-07-30. See
`HOW_TO_IDENTIFY_LOCAL_CONTRACT_TARGETS.md` at the repo root for the method this serves.

## Run

```sh
cd tools/contract-target-curation && python3 -m http.server 8420 --bind 0.0.0.0
```

Scroll zooms about the cursor, drag pans, double-click resets. Click a frame for its Zig definition;
shift-click or the sidebar checkbox adds it to the contract set. The coverage bar under the graph is
fixed to the whole program and never rescales with zoom. **AI suggested split** applies the rule in
§3.2 of the method document. **export** writes the set with instruction runs. Selection persists in
`localStorage`.

## Where the data comes from

`flame.json` is a prefix tree over **per-instruction inline stacks**, not over an extractor's regions.
That is what makes it exact: children always sum to their parent and nothing is double counted.

```sh
LLVM=/nix/store/<...>-llvm-21.1.8/bin
OBJ=$(ls -d /nix/store/*zesu-raw-ssz-rv64im-sidecar-96f1621 | head -1)/obj/zesu-raw-ssz-decoder.o

# object offset + 66224 == linked address, for this object only.
# (raw_allocator is a DIFFERENT object; its pcs are handled by owner fallback.)
$LLVM/llvm-symbolizer --obj="$OBJ" --inlining --functions=short --output-style=JSON \
    < allpcs.txt > allstacks.json
```

`allpcs.txt` is every instruction of every emitted function plus every reachable excluded routine,
as object-relative hex offsets. `flame.json` then nests callees under their call sites using
`externalCalls` from `build/elfling-program-lean/program.json`, and stores per node:

- `value` — subtree instruction count (the unit's footprint if you select it)
- `self` — instructions where this node is the innermost frame
- `runs` — instruction-index intervals, used by the coverage bar
- `frags` — number of maximal runs; **>1 means non-contiguous**, which matters because a fragmented
  unit cannot be a single region
- `src` — the Zig definition, brace-matched from the pinned source

Regenerating it is a handful of python over those two inputs; the exact scripts are in the session
transcript rather than committed, which is a gap worth closing.

## Facts baked in, for orientation

- 3,444 instructions total: 3,195 emitted plus 249 in reachable stdlib/cleanup routines.
- 172 nodes, 9 levels deep. 0 instructions carry an unnamed frame.
- The suggested split is 76 units at a 10% cap with 100% coverage, 47 distinct source names,
  and exactly one unit over cap: `readArray__anon_1576`, 611 instructions of its own straight-line
  code with nothing named inlined inside it. No source-level selection splits that one.

## Known limitations

1. **The tool is a selection aid, not a validator.** It says nothing about whether a chosen unit set
   tiles, composes, or has statable contracts. Run the §4 checks separately.
2. **`flame.json` is a snapshot** of `program.json` at `1db13ad`. Regenerate it if the extractor or
   the binary moves; nothing detects staleness.
3. **Call nesting depends on `externalCalls`**, which the extractor files under the *innermost*
   owning instance. A call made from inlined code is attributed to the inlined child, so a parent's
   own list is incomplete — the tree works around this by walking all instances whose regions
   intersect, but the underlying data defect is unfixed.
4. **`vendor/` is committed** (d3 + d3-flame-graph, MIT) so the tool works offline and does not
   acquire a network dependency at review time.

## Regenerating `allstacks.json`

Dropped from the commit at 3.4 MB; it is a pure intermediate. Recreate it with the
`llvm-symbolizer` command above fed from `allpcs.txt`. `flame.json` is committed, so the tool runs
without it.
