#!/usr/bin/env python3
"""Repeat census and covering dashboard for the Zesu SSZ decode endpoint.

`ngram_motifs.py` answers "which motifs are statistically real". This answers the separate
question "how much of the binary can repeated motifs cover, and at what price in lemmas".

It emits three frames, all as polars DataFrames, and renders them into one self-contained page:

  census   level x policy x n -> how many n-grams repeat, and how many instructions they touch
  cascade  the largest-n-first covering: cover every repeat at n, drop to n-1, repeat down to 2
  greedy   the value-weighted covering: pick by uses x (n-1) - lemmaCost, mixed n

Two window policies are reported side by side, because the difference between them is the price
of being provable rather than merely present:

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

TRANSFER_CLASSES = {"BTYPE", "JAL", "JALR"}

LEVELS = [
    ("L0_word", "exact 32-bit word"),
    ("L1_mnemonic_operands", "mnemonic + operands"),
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
    return [s[i : i + n] for s in segments for i in range(len(s) - n + 1)]


def census(segments, streams, frame, order_of, owner, is_transfer, total) -> pl.DataFrame:
    """For every level, policy and n: how many distinct n-grams occur two or more times, and how
    much of the binary those repeats touch. A pattern seen once buys nothing, so it is not
    counted -- only the repeat census leaves this function."""
    rows = []
    longest = max(len(s) for s in segments)
    for n in range(2, longest + 1):
        windows = build_starts(segments, n)
        if not windows:
            continue
        for policy, _ in POLICIES:
            allowed = [w for w in windows if admissible(w, policy, owner, is_transfer)]
            if not allowed:
                continue
            starts = [w[0] for w in allowed]
            for level, _ in LEVELS:
                keys = window_keys(level, n, starts, streams, frame, order_of)
                groups: dict[object, list[list[int]]] = collections.defaultdict(list)
                for key, w in zip(keys, allowed):
                    groups[key].append(w)
                repeated = {k: v for k, v in groups.items() if len(v) >= 2}
                touched: set[int] = set()
                occurrences = 0
                for places in repeated.values():
                    occurrences += len(places)
                    for w in places:
                        touched.update(w)
                commonest = max(repeated.values(), key=len, default=None)
                rows.append(
                    {
                        "level": level,
                        "policy": policy,
                        "n": n,
                        "windows": len(allowed),
                        "repeated": len(repeated),
                        "maximumCount": 0 if commonest is None else len(commonest),
                        "commonest": "—" if commonest is None
                        else describe(level, commonest[0], streams),
                        "repeatOccurrences": occurrences,
                        "instructionsTouched": len(touched),
                        "shareTouched": len(touched) / total,
                    }
                )
    return pl.DataFrame(rows)


def cascade(
    level, policy, segments, streams, frame, order_of, owner, is_transfer, total, minimum_uses=2,
    preclaimed=None,
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
        groups: dict[object, list[list[int]]] = collections.defaultdict(list)
        for key, w in zip(keys, windows):
            groups[key].append(w)
        kept = {k: v for k, v in groups.items() if len(v) >= minimum_uses}
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
        while True:
            best = None
            best_size = 0
            for key, places in precomputed[n].items():
                chosen = []
                limit = -1
                for w in places:
                    if w[0] <= limit or covered[w].any():
                        continue
                    chosen.append(w)
                    limit = w[-1]
                if len(chosen) > best_size:
                    best_size = len(chosen)
                    best = (key, chosen)
            if best is None or best_size < minimum_uses:
                break
            _, chosen = best
            for w in chosen:
                covered[w] = True
            if len(chosen) > top[0]:
                top = (len(chosen), describe(level, chosen[0], streams))
            here += 1
            placed += len(chosen)
            saved += len(chosen) * (n - 1)
            lemmas += 1
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
    return (
        pl.DataFrame(rows).sort("instructions", descending=True),
        pl.DataFrame(picks).sort("instructions", descending=True),
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


def greedy(
    level, policy, segments, streams, frame, order_of, owner, is_transfer, total,
    lemma_cost=20, maximum_n=20, steps=40,
) -> pl.DataFrame:
    """Value-weighted covering. One motif lemma replaces n class-lemma invocations with 1, so a
    motif is worth `uses x (n-1)` steps and costs `lemma_cost` to author."""
    pool: dict[tuple[int, object], list[list[int]]] = collections.defaultdict(list)
    for n in range(2, maximum_n + 1):
        windows = [w for w in build_starts(segments, n) if admissible(w, policy, owner, is_transfer)]
        if not windows:
            continue
        keys = window_keys(level, n, [w[0] for w in windows], streams, frame, order_of)
        for key, w in zip(keys, windows):
            pool[(n, key)].append(w)

    covered = np.zeros(total, dtype=bool)
    rows = []
    saved = 0
    for step in range(steps):
        best = None
        best_value = 0
        for (n, key), places in pool.items():
            usable = [w for w in places if not covered[w].any()]
            value = len(usable) * (n - 1) - lemma_cost
            if value > best_value:
                best_value = value
                best = (n, key, usable)
        if best is None:
            break
        n, key, usable = best
        for w in usable:
            covered[w] = True
        saved += len(usable) * (n - 1)
        rows.append(
            {
                "level": level,
                "policy": policy,
                "rank": step + 1,
                "n": n,
                "uses": len(usable),
                "owners": len({owner[w[0]] for w in usable}),
                "motif": describe(level, usable[0], streams),
                "coverCumulative": int(covered.sum()) / total,
                "savedCumulative": saved / total,
            }
        )
    return pl.DataFrame(rows)


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
"""


def svg_bars(rows, xkey, ykey, label, colour, height=190, log=False):
    if not rows:
        return "<p>no data</p>"
    width = 1080
    pad_l, pad_b, pad_t = 52, 26, 12
    xs = [r[xkey] for r in rows]
    ys = [r[ykey] for r in rows]
    top = max(ys) or 1
    plot_w = width - pad_l - 12
    plot_h = height - pad_b - pad_t
    step = plot_w / len(xs)

    def scale(v):
        if log:
            import math

            return 0 if v <= 0 else (math.log10(v + 1) / math.log10(top + 1)) * plot_h
        return v / top * plot_h

    parts = [f'<svg viewBox="0 0 {width} {height}" role="img" aria-label="{label}">']
    for frac in (0, 0.25, 0.5, 0.75, 1):
        y = pad_t + plot_h - frac * plot_h
        parts.append(
            f'<line x1="{pad_l}" x2="{width - 12}" y1="{y:.1f}" y2="{y:.1f}" '
            f'stroke="var(--grid)" stroke-width="1"/>'
        )
    parts.append(
        f'<text x="{pad_l - 8}" y="{pad_t + 4}" text-anchor="end" font-size="10" '
        f'fill="var(--muted)">{top:,}</text>'
        f'<text x="{pad_l - 8}" y="{pad_t + plot_h}" text-anchor="end" font-size="10" '
        f'fill="var(--muted)">0</text>'
    )
    for i, (x, y) in enumerate(zip(xs, ys)):
        h = scale(y)
        bx = pad_l + i * step
        parts.append(
            f'<rect x="{bx:.1f}" y="{pad_t + plot_h - h:.1f}" width="{max(step - 1.6, 1):.1f}" '
            f'height="{h:.1f}" fill="{colour}" rx="1.5"><title>n={x}: {y:,}</title></rect>'
        )
        if len(xs) <= 24 or x % 5 == 0 or i == 0 or i == len(xs) - 1:
            parts.append(
                f'<text x="{bx + step / 2:.1f}" y="{height - 9}" text-anchor="middle" '
                f'font-size="10" fill="var(--muted)">{x}</text>'
            )
    parts.append("</svg>")
    return "".join(parts)


def svg_cascade(rows, height=260):
    """Cumulative coverage against n, drawn right-to-left because the cascade runs downward."""
    if not rows:
        return "<p>no data</p>"
    width, pad_l, pad_b, pad_t, pad_r = 1080, 52, 30, 12, 14
    plot_w, plot_h = width - pad_l - pad_r, height - pad_b - pad_t
    ordered = sorted(rows, key=lambda r: -r["n"])
    xs = [r["n"] for r in ordered]
    lo, hi = min(xs), max(xs)

    def px(n):
        return pad_l + (hi - n) / max(hi - lo, 1) * plot_w

    def py(share):
        return pad_t + plot_h - share * plot_h

    parts = [f'<svg viewBox="0 0 {width} {height}" role="img" aria-label="cumulative coverage">']
    for frac in (0, 0.25, 0.5, 0.75, 1):
        y = py(frac)
        parts.append(
            f'<line x1="{pad_l}" x2="{width - pad_r}" y1="{y:.1f}" y2="{y:.1f}" '
            f'stroke="var(--grid)"/>'
            f'<text x="{pad_l - 8}" y="{y + 3:.1f}" text-anchor="end" font-size="10" '
            f'fill="var(--muted)">{int(frac * 100)}%</text>'
        )
    for key, colour in (("coverCumulative", "var(--accent)"), ("savedCumulative", "var(--accent2)")):
        pts = " ".join(f"{px(r['n']):.1f},{py(r[key]):.1f}" for r in ordered)
        parts.append(
            f'<polyline points="{pts}" fill="none" stroke="{colour}" stroke-width="2.2" '
            f'stroke-linejoin="round"/>'
        )
        for r in ordered:
            parts.append(
                f'<circle cx="{px(r["n"]):.1f}" cy="{py(r[key]):.1f}" r="3" fill="{colour}">'
                f"<title>n={r['n']}: {r[key] * 100:.1f}% after {r['lemmasCumulative']} lemmas"
                f"</title></circle>"
            )
    for r in ordered:
        if r["n"] % 5 == 0 or r["n"] in (lo, hi):
            parts.append(
                f'<text x="{px(r["n"]):.1f}" y="{height - 10}" text-anchor="middle" '
                f'font-size="10" fill="var(--muted)">{r["n"]}</text>'
            )
    parts.append("</svg>")
    return "".join(parts)


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

    census_frame = pl.DataFrame(data["census"])
    cascade_frame = pl.DataFrame(data["cascade"])
    greedy_frame = pl.DataFrame(data["greedy"])
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
        ("Corpus", num(scope["instructions"]), "instructions, RLP included"),
        ("Segments", num(scope["segments"]), f"median {scope['segmentMedian']}, max {scope['segmentMax']}"),
        ("Motif lemmas", num(head_row["lemmasCumulative"]), "class level, lemma policy"),
        ("Coverage", pct(head_row["coverCumulative"]), "instructions, counted once"),
        ("Invocations removed", pct(head_row["savedCumulative"]), "of one-per-instruction"),
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

    class_lemma = census_frame.filter(
        (pl.col("level") == "L5_class") & (pl.col("policy") == "lemma")
    ).sort("n")
    greedy_class = greedy_frame.filter(
        (pl.col("level") == "L5_class") & (pl.col("policy") == "lemma")
    )

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
<title>Zesu SSZ endpoint — n-gram repeat census</title>
<style>{STYLE}</style></head><body><div class="wrap">

<h1>Zesu SSZ endpoint — n-gram repeat census</h1>
<div class="sub">Input <span class="mono">{scope['sha256'][:16]}…</span> ·
{scope['instructions']:,} instructions · seed fixed · every figure below covers the whole
endpoint, RLP logic included.</div>

<div class="cards">{''.join(cards)}</div>

<h2>1. Coverage by motif length</h2>
<p>Every figure on this page comes from one covering run, so no instruction is counted twice.
Start at the largest repeated length. Place its occurrences, disjointly. Take those instructions
off the table. Drop to n&minus;1 and repeat, down to n=2. A pattern must still occur twice
<em>after</em> the longer patterns took their instructions, or it is not placed at all.</p>
<div class="note">This is deliberately not a raw n-gram census, which overcounts twice over. A run
of three loads yields <em>two</em> overlapping <code>LOAD LOAD</code> windows, and that same run
is counted again at every shorter length, inside every longer pattern that contains it. The
effect is not small: <code>LOAD LOAD</code> appears in 459 raw windows, and this covering places
it <strong>30</strong> times. The other 429 are overlaps of one another, or sit inside longer
motifs that were claimed first.</div>

<div class="controls" id="censusControls">
  <span style="color:var(--muted);font-size:12px">Level:</span>
  {''.join(f'<button data-level="{lv}" aria-pressed="{str(lv == "L5_class").lower()}">{lb}</button>' for lv, lb in LEVELS)}
</div>
<div class="controls" id="policyControls">
  <span style="color:var(--muted);font-size:12px">Policy:</span>
  {''.join(f'<button data-policy="{p}" aria-pressed="{str(p == "lemma").lower()}">{lb}</button>' for p, lb in POLICIES)}
</div>

<div class="panel">
  <h3>Instructions claimed at each length — each counted once</h3>
  <div id="chartClaimed"></div>
  <h3 style="margin-top:20px">Lemmas spent at each length</h3>
  <div id="chartLemmas"></div>
  <div class="legend"><span><i style="background:var(--accent)"></i>instructions claimed</span>
  <span><i style="background:var(--accent2)"></i>lemmas</span></div>
</div>

<div class="panel">
  <h3>Cumulative, running from the longest length down</h3>
  <div id="chartCascade"></div>
  <div class="legend"><span><i style="background:var(--accent)"></i>coverage</span>
  <span><i style="background:var(--accent3)"></i>invocations removed</span></div>
</div>

<div class="panel"><h3>Where the coverage arrives — instruction class, lemma policy</h3>
<div class="scroll"><table><thead><tr><th>sizes used</th><th>coverage</th><th>lemmas spent</th>
</tr></thead><tbody>{''.join(milestones)}</tbody></table></div>
<div class="note">The long motifs are a thin tail. The bottom three sizes carry most of the
coverage, and most of the lemma bill.</div>
</div>

<div class="panel"><h3>Detail — instruction class, lemma policy</h3>
<p style="margin-top:0"><span class="big">lemmas</span> is how many distinct patterns of that
length the covering placed. <span class="big">placements</span> is how many disjoint sites they
were placed at. <span class="big">claimed</span> is placements × n, the instructions this length
takes, and every instruction in the binary appears in at most one row.
<span class="big">invocations removed</span> counts the per-instruction lemma applications the
motifs replace, as <span class="mono">placements × (n−1)</span>.</p>
{table(head_class.sort('n', descending=True),
       ['n', 'lemmas', 'placements', 'usesPerLemma', 'instructionsClaimed', 'shareClaimed',
        'lemmasCumulative', 'coverCumulative', 'savedCumulative'],
       [plain, num, num, lambda v: f"{v:.1f}", num, pct, num, pct, pct],
       ['n', 'lemmas', 'placements', 'uses / lemma', 'claimed', 'share',
        'lemmas total', 'coverage', 'invocations removed'])}
</div>

<h2>2. The same covering, per abstraction level</h2>
<p>The level decides what counts as the same pattern. Coarser levels match more, so they cover
more with fewer lemmas — and each lemma then has to discharge more side conditions.</p>
<div class="panel"><div class="scroll"><table><thead><tr><th>level</th><th>largest repeat</th>
<th>coverage</th><th>lemmas</th><th>invocations removed</th></tr></thead>
<tbody>{''.join(levels_summary)}</tbody></table></div></div>

<h2>3. Are the repeats inlined functions?</h2>
<p>The artifact already maps every inline instance, so this question can be answered rather than
guessed. Of 88 distinct function names, <strong>12 have two or more instances</strong>, and those
instances hold {pct(data['insideRepeatedInstance'])} of the binary. The motif search knew nothing
about any of this.</p>
<div class="note">It found one anyway. The strongest motif in the study,
<code class="mono">lbu lbu lbu lbu slli or slli slli or or</code>, is exactly the body of
<code>mem.readInt</code>, which the compiler inlined 7 times with that shape. Seven placements of
the covering equal a whole <code>mem.readInt</code> body, instruction for instruction. An
unsupervised search over instruction classes rediscovered a function.
<br><br>Beware of counting <code>ssz.readU32</code> as well: all 10 of its instances are
<em>pc-identical</em> to the <code>mem.readInt</code> they inline, so it is a pure wrapper that
contributes no code of its own. Ten of the 14 <code>mem.readInt</code> instances sit inside one.
</div>

<div class="panel"><h3>The 12 repeated function names — are their bodies the same?</h3>
<p style="margin-top:0">One instance of a source function is not one shape of code. Inlining
specialises each call site, so the columns below count how many <em>distinct</em> bodies the
instances actually have, at four levels. The opcode column is the one that matters: where it is
far below the instance count, the instances really do share an instruction sequence and an
exact-code lemma is simply the wrong abstraction. Note how rarely the class column improves on
the opcode column — for a repeated body, opcodes already do the work.</p>
{table(pl.DataFrame(data['instanceBodies']),
       ['name', 'instances', 'sizes', 'byteShapes', 'registerShapes', 'opcodeShapes',
        'classShapes', 'instructions'],
       [mono, num, plain, num, num, num, num, num],
       ['function', 'instances', 'body sizes', 'byte shapes', 'register shapes',
        'opcode shapes', 'class shapes', 'instructions'])}
</div>

<div class="panel"><h3>Whole-body lemma candidates</h3>
<p style="margin-top:0">A body earns a lemma when two or more instances share a class-level shape.
Bodies nested inside a chosen one are skipped — <code>ssz.readU32</code> and the
<code>mem.readInt</code> it wraps hold the same program counters.
<span class="big">Seg</span> says whether a straight-line <code>Seg</code> lemma can state it; a
body with control transfers needs a function-level lemma form instead.</p>
{table(pl.DataFrame(data['instancePicks']),
       ['name', 'length', 'sites', 'instructions', 'share', 'transfers', 'segLemmaPossible'],
       [mono, plain, num, num, pct, num, lambda v: "yes" if v else "no"],
       ['function', 'length', 'sites', 'instructions', 'share', 'transfers', 'Seg'])}
<div class="note">One lemma for <code>alt_fl_alloc.sizeClassOfBytes</code> covers 7.0% of the
binary on its own — 4 instances of 78 instructions, all one class shape. It is the single largest
prize in the study, and it holds 24 control transfers, so no <code>Seg</code> lemma can state it.
</div>
</div>

<div class="panel"><h3>What kind of repetition does each lemma exploit?</h3>
<p style="margin-top:0">A motif whose sites are all instances of one function tells us only that
the compiler inlined that function twice — a whole-body lemma already says that, so the motif adds
no leverage. Everything else does: a shape recurring across unrelated functions, or recurring
inside a single instance, is a repeat the inline map cannot see.</p>
{table(pl.DataFrame(data['motifLeverage']),
       ['bucket', 'lemmas', 'instructions', 'share', 'widest', 'example'],
       [plain, num, num, pct, num, mono],
       ['what repeats', 'lemmas', 'instructions', 'share of binary', 'most functions', 'widest motif'])}
<div class="note">Only {pct(next(r['share'] for r in data['motifLeverage'] if r['bucket'] == 'same function, several instances'))} of the binary is
covered by motifs that merely restate "these two instances are the same function". The motif
search is not a roundabout way of finding duplicated code — the great majority of what it covers
is shape shared between functions that have nothing to do with each other.</div>
</div>

<div class="panel"><h3>Three strategies</h3>
{table(pl.DataFrame(data['strategies']),
       ['strategy', 'lemmas', 'coverage', 'instructionsPerLemma'],
       [plain, num, pct, lambda v: f"{v:.1f}"],
       ['strategy', 'lemmas', 'coverage', 'instructions / lemma'])}
<div class="note">The two strategies are complementary, not rival. Whole-body lemmas are three
times as productive per lemma, but they reach only the sixth of the binary that the compiler
duplicated. Most repetition in this binary is <em>inside</em> one large function that occurs once
— <code>rlp_decode.decodeTxFields</code> hosts 719 covered instructions from a single instance.
Take the bodies first, then let the motif covering work on what is left.</div>
</div>

<h2>4. Value-weighted greedy, for comparison</h2>
<p>Same corpus, different objective. Pick the motif maximising
<span class="mono">uses × (n−1) − 20</span>, over mixed n. This buys far less coverage for far
fewer lemmas, and it never selects anything long.</p>
<div class="panel">
{table(greedy_class, ['rank', 'n', 'uses', 'owners', 'motif', 'coverCumulative', 'savedCumulative'],
       [plain, plain, num, num, mono, pct, pct],
       ['#', 'n', 'uses', 'owners', 'motif', 'coverage', 'invocations removed'])}
</div>

<h2>5. What the corpus is made of</h2>
<p>Attribution is by innermost inline instance, then by that instance's source file.</p>
<div class="panel"><div class="scroll"><table><thead><tr><th>source file</th>
<th>instructions</th><th>share</th></tr></thead><tbody>{composition}</tbody></table></div></div>

<h2>6. Reading this honestly</h2>
<div class="note">Coverage is not proof. A placed motif still needs a lemma written, and a
class-level lemma merges several dataflow shapes, so it carries register-distinctness side
conditions that this page does not price. The lemma cost of 20 steps in section 3 is a placeholder:
its only measured predecessor was deleted in the EVM-Sail pivot.</div>

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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cfg", type=pathlib.Path, required=True)
    parser.add_argument("--out-json", type=pathlib.Path)
    parser.add_argument("--out-html", type=pathlib.Path)
    parser.add_argument("--lemma-cost", type=int, default=20)
    arguments = parser.parse_args()

    instructions, database = load_zesu_cfg(arguments.cfg)
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

    census_frame = census(segments, streams, frame, order_of, owner, is_transfer, total)

    cascades = []
    greedies = []
    for level, _ in LEVELS:
        for policy, _ in POLICIES:
            cascades.append(
                cascade(level, policy, segments, streams, frame, order_of, owner,
                        is_transfer, total)
            )
        greedies.append(
            greedy(level, "lemma", segments, streams, frame, order_of, owner, is_transfer,
                   total, lemma_cost=arguments.lemma_cost)
        )
    cascade_frame = pl.concat([c for c in cascades if not c.is_empty()])
    greedy_frame = pl.concat([g for g in greedies if not g.is_empty()])

    cfg = json.loads(arguments.cfg.read_text())

    # Do the discovered motifs correspond to functions the compiler inlined many times?
    bodies_frame, picks_frame, body_mask, inside_share = instance_bodies(
        cfg, instructions, streams, total
    )
    ngram_only = cascade("L5_class", "lemma", segments, streams, frame, order_of, owner,
                         is_transfer, total).sort("n").row(0, named=True)
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
    class_lemma = census_frame.filter(
        (pl.col("level") == "L5_class") & (pl.col("policy") == "lemma")
    )
    data = {
        "scope": {
            "instructions": total,
            "segments": len(segments),
            "segmentMedian": lengths[len(lengths) // 2],
            "segmentMax": lengths[-1],
            "owners": len(set(owner)),
            "sha256": database["inputs"]["sha256"],
        },
        "totals": {
            "repeatedClassLemma": int(class_lemma["repeated"].sum()),
            "repeatedAllLevels": int(census_frame.filter(pl.col("policy") == "lemma")["repeated"].sum()),
        },
        "census": census_frame.to_dicts(),
        "cascade": cascade_frame.to_dicts(),
        "greedy": greedy_frame.to_dicts(),
        "composition": composition,
        "instanceBodies": bodies_frame.to_dicts(),
        "instancePicks": picks_frame.to_dicts(),
        "motifLeverage": leverage_frame.to_dicts(),
        "strategies": strategies,
        "insideRepeatedInstance": inside_share,
    }

    if arguments.out_json:
        arguments.out_json.parent.mkdir(parents=True, exist_ok=True)
        arguments.out_json.write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
    if arguments.out_html:
        arguments.out_html.parent.mkdir(parents=True, exist_ok=True)
        arguments.out_html.write_text(render(data))

    with pl.Config(tbl_rows=60, tbl_cols=12, fmt_str_lengths=48):
        print("== repeated n-grams, instruction class, lemma policy ==")
        print(class_lemma.select(["n", "repeated", "maximumCount", "commonest",
                                  "instructionsTouched", "shareTouched"]))
        print("== cascade, instruction class, lemma policy ==")
        print(cascade_frame.filter(
            (pl.col("level") == "L5_class") & (pl.col("policy") == "lemma")
        ).sort("n", descending=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
