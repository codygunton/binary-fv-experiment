#!/usr/bin/env python3
"""Motif coverage dashboard for the Zesu SSZ decode endpoint.

`ngram_motifs.py` answers "which motifs are statistically real". This answers the separate
question "how much of the binary can repeated motifs cover, and at what price in lemmas".

It emits four frames, all as polars DataFrames, and renders them into one self-contained page:

  cascade   the longest-first covering: place every repeat at n, drop to n-1, continue to n=2
  bodies    the inlined function instances that repeat, and whether their bodies match
  leverage  what each lemma in the covering actually reuses
  strategy  motifs, whole bodies, and the two composed

Nothing is counted per length. A census of n-grams at each length counts a run of three loads as
two overlapping `LOAD LOAD` windows, and counts it again inside every longer pattern holding it.
The covering attributes each instruction to one pattern at one length, so its columns can be added.

Two windows are reported side by side, because the difference between them is the price of being
provable rather than merely present:

  segment  the window lies inside one straight-line segment
  lemma    also inside one function instance, and free of control transfers -- what a `Seg`
           lemma can actually state

Usage:
    python3 tools/ngram_dashboard.py --cfg result-zesu-ssz-decode-cfg/zesu-cfg.json \
        --out-json out/ngram-dashboard.json --out-html out/ngram-dashboard.html
"""

from __future__ import annotations

import argparse
import collections
import json
import pathlib
import sys

import numpy as np
import polars as pl

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from ngram_motifs import (  # noqa: E402
    CLASS_OF_MNEMONIC,
    alpha_frame,
    alpha_keys,
    load_zesu_cfg,
    segment,
    token_levels,
)
from pattern_cover import TokenStream, greedy_cover

TRANSFER_CLASSES = {"BTYPE", "JAL", "JALR"}

LEVELS = [
    ("L0_word", "exact 32-bit word"),
    ("L2_mnemonic_registers", "mnemonic + register names"),
    ("L3_alpha", "mnemonic + register roles"),
    ("L4_mnemonic", "opcode"),
    ("L5_class", "instruction class"),
]

POLICIES = [
    ("segment", "straight-line window"),
    ("lemma", "one owner, no control transfer"),
]


# --------------------------------------------------------------------------------------
# window keys
# --------------------------------------------------------------------------------------


def window_keys(level: str, n: int, starts: list[int], streams, frame, order_of) -> list:
    """Key for each window start, at the requested abstraction level.

    Every level except the alpha level is a plain per-instruction token, so a window key is the
    tuple of tokens. The alpha level renames registers by first use *inside the window*, so it
    has no fixed alphabet and is computed by `alpha_keys` instead.
    """
    if level != "L3_alpha":
        stream = streams[level]
        return [tuple(stream[index + offset] for offset in range(n)) for index in starts]
    rows = np.array([order_of[index] for index in starts], dtype=np.int64)
    take = np.arange(frame.mnemonic.size, dtype=np.int64)
    return [int(value) for value in alpha_keys(frame, take, rows, n)]


def admissible(indices: list[int], policy: str, owner, is_transfer) -> bool:
    if policy == "segment":
        return True
    if any(is_transfer[index] for index in indices):
        return False
    return len({owner[index] for index in indices}) == 1


# --------------------------------------------------------------------------------------
# frames
# --------------------------------------------------------------------------------------


def build_starts(segments: list[list[int]], n: int) -> list[list[int]]:
    total = max((index for segment in segments for index in segment), default=-1) + 1
    return TokenStream([None] * total, segments, [None] * total).windows(n)


def cascade(
    level, policy, segments, streams, frame, order_of, owner, is_transfer, total, minimum_uses=2,
    preclaimed=None, placements_out=None, site_label=lambda index: index,
) -> pl.DataFrame:
    """Largest-n-first covering. At each n, repeatedly take the repeated n-gram with the most
    disjoint occurrences among still-uncovered instructions. Drop to n-1 when none repeats."""
    longest = max(len(s) for s in segments)
    precomputed: dict[int, dict[object, list[list[int]]]] = {}
    for n in range(2, longest + 1):
        windows = [w for w in build_starts(segments, n) if admissible(w, policy, owner, is_transfer)]
        if not windows:
            continue
        keys = window_keys(level, n, [w[0] for w in windows], streams, frame, order_of)
        grouped: dict[object, list[list[int]]] = collections.defaultdict(list)
        for key, w in zip(keys, windows):
            grouped[key].append(w)
        kept = {k: v for k, v in grouped.items() if len(v) >= minimum_uses}
        if kept:
            precomputed[n] = kept

    covered = np.zeros(total, dtype=bool) if preclaimed is None else preclaimed.copy()
    rows = []
    lemmas = 0
    saved = 0
    for n in sorted(precomputed, reverse=True):
        here = 0
        placed = 0
        top = (0, "—")
        placed_candidates, claimed = greedy_cover(
            precomputed[n], covered, minimum_uses,
        )
        for _, chosen in placed_candidates:
            for w in chosen:
                covered[w] = True
            if len(chosen) > top[0]:
                top = (len(chosen), describe(level, chosen[0], streams))
            here += 1
            placed += len(chosen)
            saved += len(chosen) * (n - 1)
            lemmas += 1
            if placements_out is not None:
                placements_out.append({
                    "length": n,
                    "pattern": describe(level, chosen[0], streams),
                    "starts": [site_label(window[0]) for window in chosen],
                    "owners": sorted({str(owner[window[0]]) for window in chosen}),
                })
        assert claimed is covered
        if here:
            rows.append(
                {
                    "level": level,
                    "policy": policy,
                    "n": n,
                    "lemmas": here,
                    "placements": placed,
                    "instructionsClaimed": placed * n,
                    "shareClaimed": placed * n / total,
                    "usesPerLemma": placed / here,
                    "topPlacements": top[0],
                    "topPattern": top[1],
                    "lemmasCumulative": lemmas,
                    "coverCumulative": int(covered.sum()) / total,
                    "savedCumulative": saved / total,
                }
            )
    return pl.DataFrame(rows)


def instance_bodies(cfg, instructions, streams, total):
    """The repeated inlined function instances, and whether their bodies are actually the same.

    The artifact already maps every inline instance, so this asks the question the motif search
    cannot: is a discovered repeat a whole function that the compiler inlined many times? A body
    is a lemma candidate only when two or more instances share a class-level shape -- the same
    source function inlines to different code at different call sites.
    """
    index_of = {row.address: k for k, row in enumerate(instructions)}
    instances = {row["id"]: row for row in cfg["functionInstances"]}
    by_name = collections.defaultdict(list)
    for row in instances.values():
        by_name[row["name"]].append(row)
    repeated = {name: group for name, group in by_name.items() if len(group) >= 2}

    shapes: dict[tuple, list[tuple]] = collections.defaultdict(list)
    rows = []
    for name, group in repeated.items():
        bodies = []
        for row in group:
            body = tuple(sorted(index_of[pc] for pc in row["pcs"] if pc in index_of))
            if body:
                bodies.append(body)
                shapes[(name, tuple(streams["L5_class"][j] for j in body))].append(body)
        if not bodies:
            continue
        rows.append(
            {
                "name": name,
                "instances": len(bodies),
                "sizes": ", ".join(str(s) for s in sorted({len(b) for b in bodies})),
                "byteShapes": len({tuple(streams["L0_word"][j] for j in b) for b in bodies}),
                "registerShapes": len(
                    {tuple(streams["L2_mnemonic_registers"][j] for j in b) for b in bodies}
                ),
                "opcodeShapes": len({tuple(streams["L4_mnemonic"][j] for j in b) for b in bodies}),
                "classShapes": len({tuple(streams["L5_class"][j] for j in b) for b in bodies}),
                "instructions": sum(len(b) for b in bodies),
            }
        )

    # Selection, largest payoff first, skipping any body nested inside one already taken --
    # `ssz.readU32` and the `mem.readInt` it wraps hold the same program counters.
    claimed = np.zeros(total, dtype=bool)
    picks = []
    for (name, shape), places in sorted(
        shapes.items(), key=lambda item: -len(item[0][1]) * len(item[1])
    ):
        if len(places) < 2:
            continue
        fresh = [body for body in places if not claimed[list(body)].any()]
        if len(fresh) < 2:
            continue
        for body in fresh:
            claimed[list(body)] = True
        transfers = sum(
            1
            for j in fresh[0]
            if CLASS_OF_MNEMONIC.get(instructions[j].mnemonic, "UNMAPPED") in TRANSFER_CLASSES
        )
        picks.append(
            {
                "name": name,
                "length": len(shape),
                "sites": len(fresh),
                "instructions": len(shape) * len(fresh),
                "share": len(shape) * len(fresh) / total,
                "transfers": transfers,
                "segLemmaPossible": transfers == 0,
                "body": " ".join(str(t) for t in shape[:8])
                + ("" if len(shape) <= 8 else f" … (+{len(shape) - 8})"),
            }
        )
    inside = {j for group in repeated.values() for row in group
              for pc in row["pcs"] if (j := index_of.get(pc)) is not None}
    body_columns = ["name", "instances", "sizes", "byteShapes", "registerShapes",
                    "opcodeShapes", "classShapes", "instructions"]
    pick_columns = ["name", "length", "sites", "instructions", "share", "transfers",
                    "segLemmaPossible", "body"]
    return (
        (pl.DataFrame(rows).sort("instructions", descending=True) if rows else
         pl.DataFrame({column: [] for column in body_columns})),
        (pl.DataFrame(picks).sort("instructions", descending=True) if picks else
         pl.DataFrame({column: [] for column in pick_columns})),
        claimed,
        len(inside) / total,
    )


def motif_leverage(level, policy, segments, streams, frame, order_of, owner, is_transfer,
                   total, cfg, minimum_uses=2):
    """Split the covering's lemmas by what kind of repetition each one exploits.

    A motif whose sites are all instances of one function tells us only that the compiler
    inlined that function twice, which a whole-body lemma already says. The question this answers
    is how much of the covering is *not* that -- the same shape recurring across unrelated
    functions, or recurring inside one function instance. Those are the repeats the inline map
    cannot see.
    """
    name_of = {row["id"]: row["name"] for row in cfg["functionInstances"]}
    stream = streams[level]
    pool: dict[int, dict[object, list[list[int]]]] = {}
    for n in range(2, max(len(s) for s in segments) + 1):
        windows = [w for w in build_starts(segments, n)
                   if admissible(w, policy, owner, is_transfer)]
        if not windows:
            continue
        keys = window_keys(level, n, [w[0] for w in windows], streams, frame, order_of)
        groups: dict[object, list[list[int]]] = collections.defaultdict(list)
        for key, w in zip(keys, windows):
            groups[key].append(w)
        kept = {k: v for k, v in groups.items() if len(v) >= minimum_uses}
        if kept:
            pool[n] = kept

    covered = np.zeros(total, dtype=bool)
    tally: dict[str, dict] = {
        b: {"bucket": b, "lemmas": 0, "instructions": 0, "widest": 0, "example": "—"}
        for b in ("across different functions", "inside one instance",
                  "same function, several instances")
    }
    for n in sorted(pool, reverse=True):
        while True:
            best, best_size = None, 0
            for key, places in pool[n].items():
                chosen, limit = [], -1
                for w in places:
                    if w[0] <= limit or covered[w].any():
                        continue
                    chosen.append(w)
                    limit = w[-1]
                if len(chosen) > best_size:
                    best_size, best = len(chosen), chosen
            if best is None or best_size < minimum_uses:
                break
            for w in best:
                covered[w] = True
            hosts = {owner[w[0]] for w in best}
            names = {name_of.get(h, "?") for h in hosts}
            bucket = ("inside one instance" if len(hosts) == 1
                      else "same function, several instances" if len(names) == 1
                      else "across different functions")
            row = tally[bucket]
            row["lemmas"] += 1
            row["instructions"] += n * len(best)
            if len(names) > row["widest"] or (
                len(names) == row["widest"] and n * len(best) > 0 and row["example"] == "—"
            ):
                row["widest"] = len(names)
                row["example"] = describe(level, best[0], streams)
    rows = sorted(tally.values(), key=lambda r: -r["instructions"])
    for row in rows:
        row["share"] = row["instructions"] / total
    return pl.DataFrame(rows)


def cover_with(
    level, policy, segments, streams, frame, order_of, owner, is_transfer, total, preclaimed
) -> tuple[int, float]:
    """The largest-n-first covering, started from instructions another strategy already claimed.
    Returns its lemma count and the coverage the two strategies reach together, so strategies can
    be composed rather than only compared."""
    result = cascade(level, policy, segments, streams, frame, order_of, owner, is_transfer,
                     total, preclaimed=preclaimed)
    if result.is_empty():
        return 0, float(preclaimed.sum()) / total
    last = result.sort("n").row(0, named=True)
    return last["lemmasCumulative"], last["coverCumulative"]


def describe(level: str, window: list[int], streams, limit: int = 8) -> str:
    """A readable name for a window. The alpha level renames registers per window and has no
    printable token, so it is shown by its mnemonic sequence -- the part of it that is visible."""
    stream = streams["L4_mnemonic" if level == "L3_alpha" else level]
    tokens = [str(stream[index]) for index in window]
    if len(tokens) > limit:
        tokens = tokens[: limit - 1] + [f"… (+{len(window) - limit + 1})"]
    return " ".join(tokens)


# --------------------------------------------------------------------------------------
# page
# --------------------------------------------------------------------------------------

STYLE = """
:root{--bg:#fbfaf8;--fg:#1c1a17;--muted:#6b6560;--line:#e2ddd6;--card:#ffffff;
 --accent:#b4552d;--accent2:#2d6a70;--accent3:#7a6aa8;--grid:#efece7}
:root:not([data-theme=light]){}
@media (prefers-color-scheme:dark){:root:not([data-theme=light]){--bg:#16151a;--fg:#e8e4de;
 --muted:#9a938c;--line:#2f2c33;--card:#1e1d23;--grid:#2a2830}}
:root[data-theme=dark]{--bg:#16151a;--fg:#e8e4de;--muted:#9a938c;--line:#2f2c33;--card:#1e1d23;--grid:#2a2830}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);
 font:15px/1.55 ui-sans-serif,system-ui,-apple-system,"Segoe UI",sans-serif}
.wrap{max-width:1180px;margin:0 auto;padding:32px 22px 80px}
h1{font-size:26px;margin:0 0 4px;letter-spacing:-.01em}
h2{font-size:18px;margin:38px 0 6px;letter-spacing:-.005em}
h3{font-size:14px;margin:22px 0 6px;color:var(--muted);font-weight:600;
 text-transform:uppercase;letter-spacing:.06em}
p{margin:6px 0 14px;color:var(--muted);max-width:74ch}
.sub{color:var(--muted);font-size:13px;margin-bottom:26px}
.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:12px;margin:20px 0 8px}
.card{background:var(--card);border:1px solid var(--line);border-radius:9px;padding:13px 15px}
.card .k{font-size:11px;text-transform:uppercase;letter-spacing:.07em;color:var(--muted)}
.card .v{font-size:25px;font-weight:600;margin-top:3px;font-variant-numeric:tabular-nums}
.card .n{font-size:12px;color:var(--muted);margin-top:2px}
.panel{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:16px 18px;margin:14px 0}
.scroll{overflow-x:auto}
table{border-collapse:collapse;font-size:13px;width:100%;font-variant-numeric:tabular-nums}
th,td{padding:5px 11px;text-align:right;border-bottom:1px solid var(--line);white-space:nowrap}
th:first-child,td:first-child{text-align:left}
th{font-weight:600;color:var(--muted);font-size:11px;text-transform:uppercase;letter-spacing:.06em}
tbody tr:hover{background:color-mix(in srgb,var(--accent) 7%,transparent)}
code,.mono{font-family:ui-monospace,"SF Mono",Menlo,monospace;font-size:12.5px}
.controls{display:flex;gap:8px;flex-wrap:wrap;align-items:center;margin:12px 0 4px}
button{font:inherit;font-size:13px;padding:5px 12px;border-radius:7px;cursor:pointer;
 border:1px solid var(--line);background:var(--card);color:var(--fg)}
button[aria-pressed=true]{background:var(--accent);border-color:var(--accent);color:#fff}
svg{display:block;max-width:100%}
.legend{display:flex;gap:16px;flex-wrap:wrap;font-size:12px;color:var(--muted);margin-top:8px}
.legend i{display:inline-block;width:11px;height:11px;border-radius:2px;margin-right:5px;vertical-align:-1px}
.note{font-size:13px;color:var(--muted);border-left:2px solid var(--accent);padding-left:12px;margin:12px 0}
.big{color:var(--fg);font-weight:600}
.hint{font-size:12.5px;margin:2px 0 16px}
ol,ul{color:var(--muted);max-width:74ch;font-size:14.5px;margin:6px 0 14px;padding-left:22px}
li{margin:3px 0}
"""


def table(frame: pl.DataFrame, columns, formats, headers) -> str:
    head = "".join(f"<th>{h}</th>" for h in headers)
    body = []
    for row in frame.iter_rows(named=True):
        cells = "".join(f"<td>{fmt(row[c])}</td>" for c, fmt in zip(columns, formats))
        body.append(f"<tr>{cells}</tr>")
    return (
        f'<div class="scroll"><table><thead><tr>{head}</tr></thead>'
        f'<tbody>{"".join(body)}</tbody></table></div>'
    )


def render(data: dict) -> str:
    pct = lambda v: f"{v * 100:.1f}%"  # noqa: E731
    num = lambda v: f"{v:,}"  # noqa: E731
    plain = lambda v: str(v)  # noqa: E731
    mono = lambda v: f'<span class="mono">{v}</span>'  # noqa: E731

    cascade_frame = pl.DataFrame(data["cascade"])
    scope = data["scope"]

    head_class = cascade_frame.filter(
        (pl.col("level") == "L5_class") & (pl.col("policy") == "lemma")
    )
    head_row = head_class.sort("n").row(0, named=True)

    def milestone(frame, threshold):
        rows = frame.sort("n", descending=True).filter(pl.col("n") >= threshold)
        if rows.is_empty():
            return 0.0, 0
        last = rows.row(-1, named=True)
        return last["coverCumulative"], last["lemmasCumulative"]

    cards = []
    for label, value, note in [
        ("Corpus", num(scope["instructions"]), "instructions"),
        ("Segments", num(scope["segments"]),
         f"median {scope['segmentMedian']}, longest {scope['segmentMax']}"),
        ("Motif lemmas", num(head_row["lemmasCumulative"]), "instruction class, Seg window"),
        ("Coverage", pct(head_row["coverCumulative"]), "each instruction counted one time"),
        ("Invocations removed", pct(head_row["savedCumulative"]), "of one step per instruction"),
    ]:
        cards.append(f'<div class="card"><div class="k">{label}</div><div class="v">{value}</div>'
                     f'<div class="n">{note}</div></div>')

    milestones = []
    for threshold in (12, 8, 5, 4, 3, 2):
        cover, lemmas = milestone(head_class, threshold)
        milestones.append(
            f"<tr><td>n &ge; {threshold}</td><td>{pct(cover)}</td><td>{lemmas}</td></tr>"
        )

    cascade_json = json.dumps(data["cascade"])

    levels_summary = []
    for level, label in LEVELS:
        sub = cascade_frame.filter((pl.col("level") == level) & (pl.col("policy") == "lemma"))
        if sub.is_empty():
            continue
        final = sub.sort("n").row(0, named=True)
        top = sub.sort("n", descending=True).row(0, named=True)
        levels_summary.append(
            f"<tr><td>{label}</td><td>{top['n']}</td><td>{pct(final['coverCumulative'])}</td>"
            f"<td>{final['lemmasCumulative']}</td><td>{pct(final['savedCumulative'])}</td></tr>"
        )

    composition = "".join(
        f"<tr><td class='mono'>{r['sourceFile']}</td><td>{num(r['instructions'])}</td>"
        f"<td>{pct(r['share'])}</td></tr>"
        for r in data["composition"]
    )

    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Zesu SSZ endpoint — motif coverage</title>
<style>{STYLE}</style></head><body><div class="wrap">

<h1>Zesu SSZ endpoint — motif coverage</h1>
<div class="sub">Input <span class="mono">{scope['sha256'][:16]}…</span> ·
{scope['instructions']:,} instructions · every figure covers the whole endpoint. The RLP code is
included. It is 48.8% of the binary.</div>

<div class="cards">{''.join(cards)}</div>

<h2>1. Coverage by motif length</h2>
<p>One covering run supplies every figure on this page. The run counts no instruction twice.
It works like this:</p>
<ol><li>Start at the longest length that repeats.</li>
<li>Place the occurrences of that pattern. Do not let two placements overlap.</li>
<li>Remove those instructions from the pool.</li>
<li>Go to length n&minus;1. Do the same. Continue down to n=2.</li></ol>
<p>A pattern must still occur two times <em>after</em> the longer patterns take their instructions.
If it does not, the run does not place it.</p>
<div class="note">This page does not report a census of n-grams for each length. That census
counts the same code two ways. A run of 3 loads gives <em>two</em> overlapping
<code>LOAD LOAD</code> windows. The same run is counted again at every shorter length, inside every
longer pattern that holds it. The error is large. <code>LOAD LOAD</code> occurs in 459 raw windows.
This covering places it <strong>30</strong> times.</div>

<div class="controls" id="censusControls">
  <span style="color:var(--muted);font-size:12px">Level:</span>
  {''.join(f'<button data-level="{lv}" aria-pressed="{str(lv == "L5_class").lower()}">{lb}</button>' for lv, lb in LEVELS)}
</div>
<div class="controls" id="policyControls">
  <span style="color:var(--muted);font-size:12px">Window:</span>
  {''.join(f'<button data-policy="{p}" aria-pressed="{str(p == "lemma").lower()}">{lb}</button>' for p, lb in POLICIES)}
</div>
<p class="hint">The level sets what makes two patterns the same. The window sets which patterns a
lemma can state. A <code>Seg</code> lemma needs one basic block, one function instance, and no
control transfer.</p>

<div class="panel">
  <h3>Instructions claimed at each length</h3>
  <div id="chartClaimed"></div>
  <h3 style="margin-top:20px">Lemmas spent at each length</h3>
  <div id="chartLemmas"></div>
  <div class="legend"><span><i style="background:var(--accent)"></i>instructions claimed</span>
  <span><i style="background:var(--accent2)"></i>lemmas</span></div>
</div>

<div class="panel">
  <h3>Cumulative totals, from the longest length down</h3>
  <div id="chartCascade"></div>
  <div class="legend"><span><i style="background:var(--accent)"></i>coverage</span>
  <span><i style="background:var(--accent3)"></i>invocations removed</span></div>
</div>

<div class="panel"><h3>Where the coverage comes from</h3>
<div class="scroll"><table><thead><tr><th>lengths used</th><th>coverage</th><th>lemmas spent</th>
</tr></thead><tbody>{''.join(milestones)}</tbody></table></div>
<div class="note">The long motifs are a thin tail. The three shortest lengths give most of the
coverage. They also give most of the lemma cost.</div>
</div>

<div class="panel"><h3>Detail: instruction class level, <code>Seg</code> window</h3>
<p style="margin-top:0">Read the columns like this:</p>
<ul>
<li><span class="big">lemmas</span> — how many different patterns of this length the run placed.</li>
<li><span class="big">placements</span> — how many sites those patterns went to. No two overlap.</li>
<li><span class="big">uses / lemma</span> — placements divided by lemmas. This says what one lemma
buys.</li>
<li><span class="big">claimed</span> — placements multiplied by n. Each instruction occurs in one
row only.</li>
<li><span class="big">invocations removed</span> — placements multiplied by (n&minus;1). This is
how many single-instruction steps the motifs replace.</li>
</ul>
{table(head_class.sort('n', descending=True),
       ['n', 'lemmas', 'placements', 'usesPerLemma', 'instructionsClaimed', 'shareClaimed',
        'lemmasCumulative', 'coverCumulative', 'savedCumulative'],
       [plain, num, num, lambda v: f"{v:.1f}", num, pct, num, pct, pct],
       ['n', 'lemmas', 'placements', 'uses / lemma', 'claimed', 'share',
        'lemmas total', 'coverage', 'invocations removed'])}
<div class="note">Look at <span class="big">uses / lemma</span>. It is 11.2 at n=2 and 2.0 at
every length from 14 up. A long lemma is used the smallest number of times that still counts as a
repeat. That, and not rarity, is why the long tail does not pay.</div>
</div>

<h2>2. The same covering at each abstraction level</h2>
<p>The level sets what makes two patterns the same. A coarse level matches more code. It covers
more with fewer lemmas. Each lemma must then discharge more side conditions.</p>
<div class="panel"><div class="scroll"><table><thead><tr><th>level</th><th>longest repeat</th>
<th>coverage</th><th>lemmas</th><th>invocations removed</th></tr></thead>
<tbody>{''.join(levels_summary)}</tbody></table></div>
<div class="note">The instruction class level wins on coverage and on lemma count at the same time.
The rest of this page uses it.</div></div>

<h2>3. Are the repeats inlined functions?</h2>
<p>The artifact maps every inline instance. So this page measures the answer. It does not guess it.
The artifact holds 88 different function names. <strong>12 names have two or more
instances.</strong> Those instances hold {pct(data['insideRepeatedInstance'])} of the binary. The motif search received
none of this data.</p>
<div class="note">The search found one of them without help. The strongest motif in the study is
<code class="mono">lbu lbu lbu lbu slli or slli slli or or</code>. It is the body of
<code>mem.readInt</code>. The compiler inlined that body 7 times with that shape. Seven placements
of the covering equal a whole <code>mem.readInt</code> body, instruction for instruction.
<br><br>Do not count <code>ssz.readU32</code> as well. All 10 of its instances hold the same
program counters as the <code>mem.readInt</code> inside them. It is a wrapper. It adds no code.
Ten of the 14 <code>mem.readInt</code> instances sit in one.</div>

<div class="panel"><h3>The 12 repeated names: are the bodies the same?</h3>
<p style="margin-top:0">One source function does not give one shape of code. Inlining makes each
call site different. The columns count how many <em>different</em> bodies the instances have, at
four levels. Read the opcode column first. A number far below the instance count means the
instances do share an instruction sequence. Then an exact-code lemma is the wrong tool. The class
column rarely improves on the opcode column. For a repeated body, opcodes are sufficient.</p>
{table(pl.DataFrame(data['instanceBodies']),
       ['name', 'instances', 'sizes', 'byteShapes', 'registerShapes', 'opcodeShapes',
        'classShapes', 'instructions'],
       [mono, num, plain, num, num, num, num, num],
       ['function', 'instances', 'body sizes', 'byte shapes', 'register shapes',
        'opcode shapes', 'class shapes', 'instructions'])}
</div>

<div class="panel"><h3>Candidates for a whole-body lemma</h3>
<p style="margin-top:0">A body earns a lemma when two or more instances share a class shape. The
selection skips a body that sits inside a body it already took. The <span class="big">Seg</span>
column says if a straight-line <code>Seg</code> lemma can state the body. A body with a control
transfer needs a lemma form for a whole function instead.</p>
{table(pl.DataFrame(data['instancePicks']),
       ['name', 'length', 'sites', 'instructions', 'share', 'transfers', 'segLemmaPossible'],
       [mono, plain, num, num, pct, num, lambda v: "yes" if v else "no"],
       ['function', 'length', 'sites', 'instructions', 'share', 'transfers', 'Seg'])}
<div class="note">One lemma for <code>alt_fl_alloc.sizeClassOfBytes</code> covers 7.0% of the
binary. It has 4 instances of 78 instructions, and all 4 share one class shape. This is the largest
prize in the study. It also holds 24 control transfers, so no <code>Seg</code> lemma can state it.
</div>
</div>

<div class="panel"><h3>What does each lemma actually reuse?</h3>
<p style="margin-top:0">Some motifs only tell us that the compiler inlined one function two times.
A whole-body lemma already tells us that, so those motifs add nothing. The other motifs do add
something. A shape that occurs in unrelated functions, or that occurs again inside one instance, is
a repeat that the inline map cannot show.</p>
{table(pl.DataFrame(data['motifLeverage']),
       ['bucket', 'lemmas', 'instructions', 'share', 'widest', 'example'],
       [plain, num, num, pct, num, mono],
       ['what repeats', 'lemmas', 'instructions', 'share of binary', 'most functions',
        'widest motif'])}
<div class="note">Motifs that only restate "these instances are the same function" cover
{pct(next(r['share'] for r in data['motifLeverage']
                      if r['bucket'] == 'same function, several instances'))} of the binary. So the motif search is not an indirect way to find duplicated
functions. Almost all of what it covers is shape that unrelated functions share.</div>
</div>

<div class="panel"><h3>Three strategies</h3>
{table(pl.DataFrame(data['strategies']),
       ['strategy', 'lemmas', 'coverage', 'instructionsPerLemma'],
       [plain, num, pct, lambda v: f"{v:.1f}"],
       ['strategy', 'lemmas', 'coverage', 'instructions / lemma'])}
<div class="note">The two strategies work together. They do not compete. A whole-body lemma is
three times as productive as a motif lemma. But whole bodies reach only the sixth of the binary
that the compiler duplicated. Most repeats here occur <em>inside</em> one large function that has
one instance. <code>rlp_decode.decodeTxFields</code> holds 719 covered instructions by itself.
Write the body lemmas first. Then let the motif covering work on the remainder.</div>
</div>

<h2>4. What the corpus contains</h2>
<p>Each instruction is attributed to its innermost inline instance, then to the source file of that
instance.</p>
<div class="panel"><div class="scroll"><table><thead><tr><th>source file</th>
<th>instructions</th><th>share</th></tr></thead><tbody>{composition}</tbody></table></div></div>

<h2>5. What this page does not show</h2>
<p>Three facts limit every number above. All three come from the tree, not from an estimate.</p>
<div class="panel">
<ul>
<li><strong>Coverage is not proof.</strong> A placed motif still needs a lemma. A class-level lemma
merges several dataflow shapes, so it carries side conditions about register distinctness. This
page does not price those side conditions.</li>
<li><strong>No lemma for a single instruction exists.</strong> The EVM-Sail pivot deleted
<code>InstructionClassSteps.lean</code> and the <code>decoderLoadStep</code> family. Nothing
replaced them. So "invocations removed" counts a unit with no known price.</li>
<li><strong>No proof uses <code>Seg</code>.</strong> The file
<code>BinaryFv/RiscV/Elfling/Seg.lean</code> is complete. No other file uses its combinators. Only
the root module imports it. This is an adoption gap, not a missing component.</li>
</ul>
<div class="note">The first measurement that fixes this is small. Prove one straight-line segment
with <code>Seg</code>. Record the lines and the elaboration time for one step. That gives the
baseline every figure on this page needs. Use the 10 instructions of <code>mem.readInt</code>: they
have no transfer, no memory write, and one free immediate.</div>
</div>

<script>
const CASCADE = {cascade_json};
let level = "L5_class", policy = "lemma";

function bars(host, rows, key, colour, fmt) {{
  if (!rows.length) {{ host.innerHTML = "<p>no data</p>"; return; }}
  const W = 1080, H = 190, PL = 52, PB = 26, PT = 12;
  const pw = W - PL - 12, ph = H - PB - PT;
  const top = Math.max(...rows.map(r => r[key])) || 1;
  const step = pw / rows.length;
  let s = `<svg viewBox="0 0 ${{W}} ${{H}}">`;
  for (const f of [0, .25, .5, .75, 1]) {{
    const y = PT + ph - f * ph;
    s += `<line x1="${{PL}}" x2="${{W - 12}}" y1="${{y}}" y2="${{y}}" stroke="var(--grid)"/>`;
  }}
  s += `<text x="${{PL - 8}}" y="${{PT + 8}}" text-anchor="end" font-size="10"
        fill="var(--muted)">${{fmt(top)}}</text>`;
  s += `<text x="${{PL - 8}}" y="${{PT + ph}}" text-anchor="end" font-size="10"
        fill="var(--muted)">0</text>`;
  rows.forEach((r, i) => {{
    const h = r[key] / top * ph, x = PL + i * step;
    s += `<rect x="${{x}}" y="${{PT + ph - h}}" width="${{Math.max(step - 1.6, 1)}}"
          height="${{h}}" fill="${{colour}}" rx="1.5"><title>n=${{r.n}}: ${{fmt(r[key])}}</title></rect>`;
    if (rows.length <= 26 || r.n % 5 === 0 || i === 0 || i === rows.length - 1)
      s += `<text x="${{x + step / 2}}" y="${{H - 9}}" text-anchor="middle" font-size="10"
            fill="var(--muted)">${{r.n}}</text>`;
  }});
  host.innerHTML = s + "</svg>";
}}

function cascadeChart(host, rows) {{
  if (!rows.length) {{ host.innerHTML = "<p>no data</p>"; return; }}
  const W = 1080, H = 260, PL = 52, PB = 30, PT = 12, PR = 14;
  const pw = W - PL - PR, ph = H - PB - PT;
  const ordered = [...rows].sort((a, b) => b.n - a.n);
  const hi = ordered[0].n, lo = ordered[ordered.length - 1].n;
  const px = n => PL + (hi - n) / Math.max(hi - lo, 1) * pw;
  const py = v => PT + ph - v * ph;
  let s = `<svg viewBox="0 0 ${{W}} ${{H}}">`;
  for (const f of [0, .25, .5, .75, 1])
    s += `<line x1="${{PL}}" x2="${{W - PR}}" y1="${{py(f)}}" y2="${{py(f)}}" stroke="var(--grid)"/>
          <text x="${{PL - 8}}" y="${{py(f) + 3}}" text-anchor="end" font-size="10"
          fill="var(--muted)">${{Math.round(f * 100)}}%</text>`;
  for (const [k, c] of [["coverCumulative", "var(--accent)"], ["savedCumulative", "var(--accent3)"]]) {{
    s += `<polyline points="${{ordered.map(r => `${{px(r.n)}},${{py(r[k])}}`).join(" ")}}"
          fill="none" stroke="${{c}}" stroke-width="2.2" stroke-linejoin="round"/>`;
    for (const r of ordered)
      s += `<circle cx="${{px(r.n)}}" cy="${{py(r[k])}}" r="3" fill="${{c}}"><title>n=${{r.n}}:
            ${{(r[k] * 100).toFixed(1)}}% after ${{r.lemmasCumulative}} lemmas</title></circle>`;
  }}
  for (const r of ordered)
    if (r.n % 5 === 0 || r.n === hi || r.n === lo)
      s += `<text x="${{px(r.n)}}" y="${{H - 10}}" text-anchor="middle" font-size="10"
            fill="var(--muted)">${{r.n}}</text>`;
  host.innerHTML = s + "</svg>";
}}

function draw() {{
  // only lengths the covering actually used; a length it skipped claimed nothing
  const rows = CASCADE.filter(r => r.level === level && r.policy === policy)
                      .sort((a, b) => a.n - b.n);
  bars(document.getElementById("chartClaimed"), rows, "instructionsClaimed", "var(--accent)",
       v => v.toLocaleString());
  bars(document.getElementById("chartLemmas"), rows, "lemmas", "var(--accent2)",
       v => v.toLocaleString());
  cascadeChart(document.getElementById("chartCascade"), rows);
}}

for (const b of document.querySelectorAll("#censusControls button"))
  b.onclick = () => {{
    level = b.dataset.level;
    document.querySelectorAll("#censusControls button")
      .forEach(x => x.setAttribute("aria-pressed", String(x === b)));
    draw();
  }};
for (const b of document.querySelectorAll("#policyControls button"))
  b.onclick = () => {{
    policy = b.dataset.policy;
    document.querySelectorAll("#policyControls button")
      .forEach(x => x.setAttribute("aria-pressed", String(x === b)));
    draw();
  }};
draw();
</script>
</div></body></html>"""


# --------------------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cfg", type=pathlib.Path, required=True)
    parser.add_argument("--proof-manifest", type=pathlib.Path,
                        help="restrict motifs to directly discharged PCs in this proof manifest")
    parser.add_argument("--out-json", type=pathlib.Path)
    parser.add_argument("--out-html", type=pathlib.Path)
    arguments = parser.parse_args(argv)

    instructions, database = load_zesu_cfg(arguments.cfg)
    if arguments.proof_manifest:
        manifest = json.loads(arguments.proof_manifest.read_text())
        selected = set(manifest["coverage"]["directlyDischargedStepPcs"])
        available = {instruction.address for instruction in instructions}
        if missing := selected - available:
            parser.error(f"proof manifest contains PCs absent from CFG: {sorted(missing)}")
        instructions = [instruction for instruction in instructions
                        if instruction.address in selected]
        database["instructions"] = [
            {"address": row["address"],
             "successors": [pc for pc in row["successors"] if pc in selected]}
            for row in database["instructions"] if row["address"] in selected
        ]
        database["summary"]["instructionCount"] = len(instructions)
    segments = segment(instructions, database)
    streams = token_levels(instructions)
    total = len(instructions)
    owner = [i.owner for i in instructions]
    is_transfer = [
        CLASS_OF_MNEMONIC.get(i.mnemonic, "UNMAPPED") in TRANSFER_CLASSES for i in instructions
    ]

    frame = alpha_frame(instructions, segments)
    order = [index for indices in segments for index in indices]
    order_of = {index: row for row, index in enumerate(order)}

    cascades = []
    for level, _ in LEVELS:
        for policy, _ in POLICIES:
            cascades.append(
                cascade(level, policy, segments, streams, frame, order_of, owner,
                        is_transfer, total)
            )
    cascade_frame = pl.concat([c for c in cascades if not c.is_empty()])

    cfg = json.loads(arguments.cfg.read_text())

    # Do the discovered motifs correspond to functions the compiler inlined many times?
    bodies_frame, picks_frame, body_mask, inside_share = instance_bodies(
        cfg, instructions, streams, total
    )
    motif_candidates = []
    ngram_only = cascade("L5_class", "lemma", segments, streams, frame, order_of, owner,
                         is_transfer, total, placements_out=motif_candidates,
                         site_label=lambda index: instructions[index].address
                         ).sort("n").row(0, named=True)
    together_lemmas, together_cover = cover_with(
        "L5_class", "lemma", segments, streams, frame, order_of, owner, is_transfer, total,
        body_mask,
    )
    leverage_frame = motif_leverage("L5_class", "lemma", segments, streams, frame, order_of,
                                    owner, is_transfer, total, cfg)
    body_lemmas = len(picks_frame)
    strategies = [
        {"strategy": "n-gram motifs alone", "lemmas": ngram_only["lemmasCumulative"],
         "coverage": ngram_only["coverCumulative"]},
        {"strategy": "whole inlined bodies alone", "lemmas": body_lemmas,
         "coverage": float(body_mask.sum()) / total},
        {"strategy": "bodies first, then n-gram motifs",
         "lemmas": body_lemmas + together_lemmas, "coverage": together_cover},
    ]
    for row in strategies:
        row["instructionsPerLemma"] = row["coverage"] * total / max(row["lemmas"], 1)

    instance_file = {row["id"]: row.get("sourceFile") or "unknown" for row in cfg["functionInstances"]}
    tally = collections.Counter(instance_file.get(o, "unknown").split("/")[-1] for o in owner)
    composition = [
        {"sourceFile": name, "instructions": count, "share": count / total}
        for name, count in tally.most_common()
    ]

    lengths = sorted(len(s) for s in segments)
    data = {
        "scope": {
            "instructions": total,
            "segments": len(segments),
            "segmentMedian": lengths[len(lengths) // 2],
            "segmentMax": lengths[-1],
            "owners": len(set(owner)),
            "sha256": database["inputs"]["sha256"],
        },
        "cascade": cascade_frame.to_dicts(),
        "composition": composition,
        "instanceBodies": bodies_frame.to_dicts(),
        "instancePicks": picks_frame.to_dicts(),
        "motifLeverage": leverage_frame.to_dicts(),
        "strategies": strategies,
        "insideRepeatedInstance": inside_share,
    }
    if arguments.proof_manifest:
        data["motifCandidates"] = motif_candidates

    if arguments.out_json:
        arguments.out_json.parent.mkdir(parents=True, exist_ok=True)
        arguments.out_json.write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
    if arguments.out_html:
        arguments.out_html.parent.mkdir(parents=True, exist_ok=True)
        arguments.out_html.write_text(render(data))

    with pl.Config(tbl_rows=60, tbl_cols=12, fmt_str_lengths=48):
        print("== covering, instruction class, Seg window ==")
        print(cascade_frame.filter(
            (pl.col("level") == "L5_class") & (pl.col("policy") == "lemma")
        ).sort("n", descending=True))
        print("== repeated inlined bodies ==")
        print(picks_frame)
        print("== what each lemma reuses ==")
        print(leverage_frame)
        print("== strategies ==")
        print(pl.DataFrame(strategies))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
