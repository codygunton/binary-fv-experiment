#!/usr/bin/env python3
"""Shared token-stream and greedy-cover primitives for proof and machine motifs."""

from __future__ import annotations

import collections
import dataclasses
from collections.abc import Callable, Hashable, Sequence


@dataclasses.dataclass(frozen=True)
class TokenStream:
    """Ordered tokens partitioned into windows that a candidate may not cross."""

    tokens: Sequence[Hashable]
    segments: Sequence[Sequence[int]]
    owners: Sequence[Hashable]

    def windows(self, length: int) -> list[list[int]]:
        return [
            list(segment[offset : offset + length])
            for segment in self.segments
            for offset in range(len(segment) - length + 1)
        ]


def groups(
    stream: TokenStream,
    length: int,
    key: Callable[[list[int]], Hashable] | None = None,
    admissible: Callable[[list[int]], bool] = lambda _window: True,
) -> dict[Hashable, list[list[int]]]:
    """Group admissible fixed-length windows by their normalized token key."""

    out: dict[Hashable, list[list[int]]] = collections.defaultdict(list)
    for window in stream.windows(length):
        if admissible(window):
            window_key = key(window) if key else tuple(stream.tokens[index] for index in window)
            out[window_key].append(window)
    return dict(out)


def greedy_cover(
    candidates: dict[Hashable, list[list[int]]],
    claimed: set[int] | None = None,
    minimum_uses: int = 2,
) -> tuple[list[tuple[Hashable, list[list[int]]]], set[int]]:
    """Repeatedly place the candidate with most disjoint currently-unclaimed windows."""

    covered = set() if claimed is None else set(claimed)
    placements: list[tuple[Hashable, list[list[int]]]] = []
    while True:
        best: tuple[Hashable, list[list[int]]] | None = None
        for candidate_key, windows in candidates.items():
            chosen: list[list[int]] = []
            limit = -1
            for window in windows:
                if window[0] <= limit or any(index in covered for index in window):
                    continue
                chosen.append(window)
                limit = window[-1]
            if best is None or len(chosen) > len(best[1]):
                best = candidate_key, chosen
        if best is None or len(best[1]) < minimum_uses:
            break
        candidate_key, chosen = best
        for window in chosen:
            covered.update(window)
        placements.append((candidate_key, chosen))
    return placements, covered
