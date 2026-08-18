#!/usr/bin/env python3

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from pattern_cover import TokenStream, greedy_cover, groups


class PatternCoverTest(unittest.TestCase):
    def test_windows_do_not_cross_segments(self) -> None:
        stream = TokenStream("abcabc", [[0, 1, 2], [3, 4, 5]], ["a"] * 6)
        self.assertEqual(stream.windows(2), [[0, 1], [1, 2], [3, 4], [4, 5]])

    def test_greedy_cover_is_disjoint(self) -> None:
        stream = TokenStream("aaaaaa", [list(range(6))], ["a"] * 6)
        placed, covered = greedy_cover(groups(stream, 2))
        self.assertEqual(len(placed), 1)
        self.assertEqual(placed[0][1], [[0, 1], [2, 3], [4, 5]])
        self.assertEqual(covered, set(range(6)))

    def test_owner_admissibility(self) -> None:
        stream = TokenStream("abab", [list(range(4))], [0, 0, 1, 1])
        grouped = groups(stream, 2, admissible=lambda w: len({stream.owners[i] for i in w}) == 1)
        self.assertEqual(sum(map(len, grouped.values())), 2)


if __name__ == "__main__":
    unittest.main()
