"""Graph algorithms, operand parsing and the ledger on small inputs."""
import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from zmap import analyze, elfread, ledger  # noqa: E402


class Graphs(unittest.TestCase):
    def test_dominators_and_loop(self):
        # 0 -> 1 -> 2 -> 1 (loop), 2 -> 3
        succ = {0: [1], 1: [2], 2: [1, 3], 3: []}
        idom = analyze.dominators(0, succ)
        self.assertEqual(idom, {0: 0, 1: 0, 2: 1, 3: 2})
        self.assertTrue(analyze.dominates(idom, 1, 2))
        preds = {1: [0, 2], 2: [1], 3: [2], 0: []}
        self.assertEqual(analyze.natural_loop(1, 2, preds), {1, 2})

    def test_irreducible_cycle_has_no_back_edge(self):
        # 0 -> 1, 0 -> 2, 1 <-> 2: neither 1 nor 2 dominates the other.
        succ = {0: [1, 2], 1: [2], 2: [1]}
        idom = analyze.dominators(0, succ)
        self.assertFalse(analyze.dominates(idom, 1, 2))
        self.assertFalse(analyze.dominates(idom, 2, 1))
        comps = analyze.tarjan([0, 1, 2], succ)
        self.assertIn([1, 2], comps)

    def test_segment_counts(self):
        # Diamond 0 -> {1, 2} -> 3 -> 4 (cut), 3 -> 5 (exit).
        succ = {0: [1, 2], 1: [3], 2: [3], 3: [4, 5], 4: [], 5: []}
        paths, into = analyze.segment_counts(0, succ, lambda n: n in {0, 4})
        self.assertEqual(paths, 4)
        self.assertEqual(into[3], 2)
        self.assertEqual(into[4], 2)

    def test_segment_counts_loop_head_start(self):
        # Loop head 1: body 2 returns to 1 (ends the path), exit 3.
        succ = {1: [2, 3], 2: [1], 3: []}
        paths, _ = analyze.segment_counts(1, succ, lambda n: n in {1})
        self.assertEqual(paths, 2)


class Parsing(unittest.TestCase):
    def test_parse_jalr_and_branch(self):
        i = elfread.parse_insn('80000064: 900080e7     \tjalr\tra, -0x700(ra) <rlp.decodeItem>')
        self.assertEqual((i.mn, i.size), ('jalr', 4))
        self.assertEqual(analyze.jalr_parts(i), ('ra', 'ra', -0x700))
        b = elfread.parse_insn('8000006c: 42051e63     \tbne\ta0, zero, 0x800004a8 <f+0x4a8>')
        self.assertEqual(b.target, 0x800004a8)
        c = elfread.parse_insn('800e06be: 8082         \tc.jr\tra')
        self.assertEqual(c.size, 2)

    def test_block_evaluation(self):
        lines = ['80000564: 00110597 \tauipc\ta1, 0x110',
                 '80000568: 00351513 \tslli\ta0, a0, 0x3',
                 '8000056c: aec58593 \taddi\ta1, a1, -0x514',
                 '80000570: 00a58533 \tadd\ta0, a1, a0',
                 '80000574: 00053503 \tld\ta0, 0x0(a0)']
        block = [elfread.parse_insn(l) for l in lines]
        v = analyze.evaluate(block, 0x80000578)('a0')
        self.assertEqual(v[0], 'ld')
        base, terms = analyze.linear(v[3])
        self.assertEqual(base, 0x80000564 + 0x110000 - 0x514)
        self.assertEqual(terms, [('shl', ('r', 'a0'), 3)])


class Ledger(unittest.TestCase):
    def test_log_appends_line(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, 'ledger.jsonl')
            ledger.log(path, '-', 'a', 'infra', 'me', 5, 'closed')
            ledger.log(path, 'f_80000000', 'b', 'leaf', 'me', 2.5, 'open', usd=0.1, requests=3)
            rows = [json.loads(l) for l in open(path)]
        self.assertEqual(len(rows), 2)
        self.assertIsNone(rows[0]['fn'])
        self.assertEqual(rows[1]['fn'], 'f_80000000')
        self.assertTrue(rows[0]['ts'].endswith('Z'))
        with self.assertRaises(ValueError):
            ledger.log(os.devnull, '-', 'c', 'bogus', 'me', 1, 'closed')


if __name__ == '__main__':
    unittest.main()
