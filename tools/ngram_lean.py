#!/usr/bin/env python3
"""Repeated-pattern analysis of Lean proof text, using the machine-code instrument's core.

`ngram_motifs.py` finds repeated instruction patterns in a compiled binary. The same question
applies to the proof that covers that binary, and the answer turns out to matter more: proof cost
scales with the RISC-V covered, and on `main` at `9935fb21` the rate is 51 lines of Lean for each
instruction. Over half of those lines sit inside a repeated pair of lines.

## What is shared, and what is not

The generic core of `ngram_motifs.py` operates on integer token streams and is reused verbatim:
`maximal_repeats` (suffix array + Kasai LCP + LCP-interval enumeration), `non_overlapping`,
`smallest_period`, `owner_support`, and the greedy covering. Nothing about it knows what a token is.

Four things are target-specific, and only these are written here.

| concern | machine code | proof text |
|---|---|---|
| item | one instruction | one non-blank, non-comment line |
| segment | basic block, one function instance, no control transfer | one declaration body |
| levels | word / operands / registers / roles / opcode / class | four normalisation strengths, below |
| owner | function instance | declaration name |

The segment rule is the real analogue. A machine-code motif may not cross a basic block because a
`Seg` lemma cannot state one that does. A proof pattern may not cross a `theorem` because a lemma
extracted from it would have to be applied inside one.

**There is no analogue of the alpha level.** In machine code, alpha renaming maps registers to
roles by order of first use, so two windows that differ by a consistent renaming become equal. Lean
identifiers carry no comparable positional structure, and inventing one would produce a number that
looks like the machine-code figure and means something else. The gap is recorded, not filled.

## The four levels

Coarser levels merge more lines, exactly as the machine-code lattice does.

* `L0_verbatim` — the line, whitespace-collapsed. Two lines match only if identical.
* `L1_addresses` — hex addresses and numerals abstracted. Merges sites that differ only by address.
* `L2_locals` — also abstracts state and step variable names (`state7`, `seg3`, `h12`, `trace4`).
  This is the level at which one extracted lemma could serve every site.
* `L3_tactic` — the leading tactic only. Shows the shape of a proof and nothing else. Useful as an
  upper bound on what any tactic-level automation could reach.

A share reported at `L2_locals` is a claim about how many lines *could* be replaced. It is not a
claim that a lemma exists to replace them. Section 4 of the report costs that separately.
"""

from __future__ import annotations

import argparse
import collections
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from ngram_motifs import maximal_repeats, non_overlapping, smallest_period  # noqa: E402
from pattern_cover import TokenStream, greedy_cover, groups  # noqa: E402

DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(theorem|lemma|def|abbrev|structure|instance|example)\s+([A-Za-z_][\w'.]*)?"
)
SKIP = re.compile(r"^\s*(import|open|namespace|end\s|set_option|universe|variable\b|deriving\b)")
HEX = re.compile(r"0x[0-9a-fA-F]+")
NUMBER = re.compile(r"\b\d+\b")
STATE_LOCAL = re.compile(r"\b(?:state|afterExec|after|before|cur|next|s)\d+\b")
STEP_LOCAL = re.compile(r"\b(?:seg|trace|step|h|g|n|run|premises|guard)\d+\b")
TACTIC_HEAD = re.compile(r"^\s*(?:·\s*)?([A-Za-z_][\w']*)")

LEVELS = ("L0_verbatim", "L1_addresses", "L2_locals", "L3_tactic")


def normalise(line: str, level: str) -> str:
    """One line at one abstraction level. Rules are listed in the module docstring."""
    text = re.sub(r"\s+", " ", line.strip())
    if level == "L0_verbatim":
        return text
    text = HEX.sub("⟨addr⟩", text)
    text = NUMBER.sub("⟨num⟩", text)
    if level == "L1_addresses":
        return text
    text = STATE_LOCAL.sub("⟨state⟩", text)
    text = STEP_LOCAL.sub("⟨local⟩", text)
    if level == "L2_locals":
        return text
    head = TACTIC_HEAD.match(text)
    return head.group(1) if head else "⟨continuation⟩"


class ProofStream:
    """A Lean corpus as a token stream, one item per code line, segmented by declaration.

    Mirrors what `load_zesu_cfg` produces for a binary: items in order, a segmentation those items
    may not be matched across, an owner for each item, and one token list per abstraction level.
    """

    def __init__(self, files: list[pathlib.Path]) -> None:
        self.lines: list[str] = []
        self.owner: list[str] = []
        self.file: list[str] = []
        self.segments: list[list[int]] = []
        current: list[int] = []
        owner = "<preamble>"
        for path in sorted(files):
            in_block_comment = False
            for raw in path.read_text().split("\n"):
                stripped = raw.strip()
                if in_block_comment:
                    if "-/" in stripped:
                        in_block_comment = False
                    continue
                if stripped.startswith("/-"):
                    if "-/" not in stripped:
                        in_block_comment = True
                    continue
                if not stripped or stripped.startswith("--") or SKIP.match(raw):
                    continue
                declaration = DECLARATION.match(raw)
                if declaration:
                    if current:
                        self.segments.append(current)
                    current = []
                    owner = f"{path.stem}.{declaration.group(2) or '<anonymous>'}"
                self.lines.append(raw)
                self.owner.append(owner)
                self.file.append(path.stem)
                current.append(len(self.lines) - 1)
            if current:
                self.segments.append(current)
                current = []
        self.levels = {
            level: [normalise(line, level) for line in self.lines] for level in LEVELS
        }

    def __len__(self) -> int:
        return len(self.lines)


def windows(stream: ProofStream, length: int) -> list[list[int]]:
    """Every run of `length` consecutive items inside one declaration."""
    return TokenStream(stream.lines, stream.segments, stream.owner).windows(length)


def census(stream: ProofStream, level: str, lengths: list[int]) -> list[dict]:
    """Per length: how many distinct patterns repeat, and how much of the corpus they cover.

    Coverage is a **greedy disjoint** cover, not a union of overlapping windows. A run of five
    identical lines yields four overlapping 2-line windows, and counting all four would report more
    covered lines than the corpus contains.
    """
    tokens = stream.levels[level]
    rows = []
    for length in lengths:
        grouped = groups(TokenStream(tokens, stream.segments, stream.owner), length)
        repeated = {key: value for key, value in grouped.items() if len(value) >= 2}
        placed, covered = greedy_cover(repeated)
        placements = sum(len(windows) for _, windows in placed)
        best = max((len(v) for v in grouped.values()), default=0)
        rows.append(
            {
                "level": level,
                "n": length,
                "windows": sum(len(v) for v in grouped.values()),
                "distinct": len(grouped),
                "repeated": len(repeated),
                "best": best,
                "placements": placements,
                "linesCovered": len(covered),
                "share": len(covered) / max(len(stream), 1),
            }
        )
    return rows


def top_patterns(stream: ProofStream, level: str, length: int, limit: int = 6) -> list[dict]:
    """The most-repeated patterns, with the owners and files they occur in."""
    tokens = stream.levels[level]
    groups: dict[tuple, list[list[int]]] = collections.defaultdict(list)
    for window in windows(stream, length):
        groups[tuple(tokens[index] for index in window)].append(window)
    out = []
    for key, places in sorted(groups.items(), key=lambda item: -len(item[1]))[:limit]:
        owners = {stream.owner[window[0]] for window in places}
        files = collections.Counter(stream.file[window[0]] for window in places)
        out.append(
            {
                "occurrences": len(places),
                "owners": len(owners),
                "files": dict(files.most_common(4)),
                "nonOverlapping": non_overlapping(sorted(w[0] for w in places), length),
                "period": smallest_period(tuple(range(length))),
                "pattern": list(key),
                "firstSite": stream.owner[places[0][0]],
            }
        )
    return out


def shuffled_control(stream: ProofStream, level: str, lengths: list[int], seed: int) -> list[dict]:
    """The control the study requires: shuffle lines inside each declaration and re-run.

    A pattern census that cannot come back near-empty on shuffled input has not been shown to
    measure order. This permutes within a declaration, so it preserves each declaration's length and
    its multiset of lines, and destroys only the order.
    """
    import numpy as np

    rng = np.random.default_rng(seed)
    shuffled = ProofStream.__new__(ProofStream)
    shuffled.lines = list(stream.lines)
    shuffled.owner = list(stream.owner)
    shuffled.file = list(stream.file)
    shuffled.segments = [list(segment) for segment in stream.segments]
    permuted = list(stream.levels[level])
    for segment in stream.segments:
        values = [stream.levels[level][index] for index in segment]
        order = rng.permutation(len(values))
        for slot, index in enumerate(segment):
            permuted[index] = values[order[slot]]
    shuffled.levels = {level: permuted}
    return census(shuffled, level, lengths)


def planted_control(stream: ProofStream, level: str, length: int, copies: int,
                    seed: int) -> dict:
    """Inject a synthetic pattern into shuffled text and require the census to recover it."""
    import numpy as np

    rng = np.random.default_rng(seed)
    permuted = list(stream.levels[level])
    for segment in stream.segments:
        values = [stream.levels[level][index] for index in segment]
        order = rng.permutation(len(values))
        for slot, index in enumerate(segment):
            permuted[index] = values[order[slot]]
    planted = [f"⟨planted-{k}⟩" for k in range(length)]
    hosts = [s for s in stream.segments if len(s) >= length][:copies]
    for segment in hosts:
        for offset, token in enumerate(planted):
            permuted[segment[offset]] = token
    probe = ProofStream.__new__(ProofStream)
    probe.lines, probe.owner, probe.file = stream.lines, stream.owner, stream.file
    probe.segments = stream.segments
    probe.levels = {level: permuted}
    groups: dict[tuple, list[list[int]]] = collections.defaultdict(list)
    for window in windows(probe, length):
        groups[tuple(permuted[index] for index in window)].append(window)
    found = groups.get(tuple(planted), [])
    return {"planted": len(hosts), "recovered": len(found), "length": length,
            "recoveredExactly": len(found) == len(hosts)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", type=pathlib.Path,
                        help="Lean files or directories to analyse")
    parser.add_argument("--lengths", default="2,3,4,5,6,8,10,12,16")
    parser.add_argument("--level", default="L2_locals", choices=LEVELS)
    parser.add_argument("--all-levels", action="store_true")
    parser.add_argument("--seed", type=int, default=20260817)
    parser.add_argument("--out-json", type=pathlib.Path)
    arguments = parser.parse_args(argv)

    files: list[pathlib.Path] = []
    for path in arguments.paths:
        files.extend(sorted(path.rglob("*.lean")) if path.is_dir() else [path])
    stream = ProofStream(files)
    lengths = [int(value) for value in arguments.lengths.split(",")]

    result = {
        "corpus": {
            "files": len(files),
            "lines": len(stream),
            "declarations": len(stream.segments),
            "owners": len(set(stream.owner)),
        },
        "levels": {},
        "controls": {},
        "seed": arguments.seed,
    }
    print(f"{len(files)} files, {len(stream)} code lines, {len(stream.segments)} declarations")
    for level in (LEVELS if arguments.all_levels else [arguments.level]):
        rows = census(stream, level, lengths)
        result["levels"][level] = rows
        print(f"\n{level}")
        print(f"{'n':>4}{'distinct':>10}{'repeated':>10}{'best':>7}{'covered':>9}{'share':>8}")
        for row in rows:
            print(f"{row['n']:>4}{row['distinct']:>10}{row['repeated']:>10}"
                  f"{row['best']:>7}{row['linesCovered']:>9}{row['share']*100:>7.1f}%")

    level = arguments.level
    control = shuffled_control(stream, level, lengths, arguments.seed)
    result["controls"]["shuffled"] = control
    print(f"\nshuffled control ({level}) — must be far below the real census")
    print(f"{'n':>4}{'real':>9}{'shuffled':>10}{'ratio':>8}")
    for real, fake in zip(result["levels"][level], control):
        ratio = real["share"] / fake["share"] if fake["share"] else float("inf")
        print(f"{real['n']:>4}{real['share']*100:>8.1f}%{fake['share']*100:>9.1f}%{ratio:>8.1f}x")

    planted = planted_control(stream, level, 7, 9, arguments.seed)
    result["controls"]["planted"] = planted
    print(f"\nplanted control: length {planted['length']}, planted {planted['planted']}, "
          f"recovered {planted['recovered']} — {'PASS' if planted['recoveredExactly'] else 'FAIL'}")

    result["topPatterns"] = {
        str(length): top_patterns(stream, level, length) for length in (3, 6, 10)
    }
    if arguments.out_json:
        arguments.out_json.parent.mkdir(parents=True, exist_ok=True)
        arguments.out_json.write_text(json.dumps(result, indent=1, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
