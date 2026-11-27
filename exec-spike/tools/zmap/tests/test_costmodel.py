"""The cost model on a two-function map and a small ledger."""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from zmap import costmodel  # noqa: E402


def leaf(state, residual=''):
    return {'state': state, 'residual': residual}


MAP = {'functions': [
    {'id': 'f_1', 'name': 'one', 'set': 'target', 'state': 'closed', 'registered': True,
     'cuts': [{}, {}], 'loops': [{}], 'calls': [{}], 'joins': [], 'leaves_estimate': 4,
     'n_instr': 40, 'leaves': {'auto': 1, 'manual': 2, 'open': 0},
     'ledger': {'all': {'items': 2, 'minutes': 30.0, 'usd': 1.5}},
     'vc_cuts': [{'leaves': [leaf('auto'), leaf('manual', '2 goals; head Reaches'),
                             leaf('manual', '1 goal; head ExitGoal; x')]}]},
    {'id': 'f_2', 'name': 'two', 'set': 'target', 'state': 'ready', 'cuts': [{}], 'loops': [],
     'calls': [], 'joins': [{}], 'leaves_estimate': 2, 'n_instr': 10},
    {'id': 'f_3', 'name': 'three', 'set': 'out', 'state': 'out', 'n_instr': 99},
]}

ROWS = [
    {'ts': '2026-01-01T00:00:00Z', 'kind': 'leaf', 'minutes': 10.0, 'usd': 0.5, 'fn': 'f_1',
     'item': 'leaf a'},
    {'ts': '2026-01-01T00:01:00Z', 'kind': 'leaf', 'minutes': 20.0, 'usd': 1.0, 'fn': 'f_1',
     'item': 'leaf b'},
    {'ts': '2026-01-01T00:02:00Z', 'kind': 'rule', 'minutes': 0, 'usd': None, 'fn': 'f_1',
     'item': 'joins', 'note': 'auto_share F1 2/21 -> 5/21'},
]


class CostModel(unittest.TestCase):
    def test_kind_table(self):
        t = costmodel.kind_table(ROWS)
        self.assertEqual(t['leaf'], (2, 15.0, 30.0, 0.75, 1.5))
        self.assertNotIn('rule', t)  # share-note rows are not effort

    def test_leaves_and_classes(self):
        states, classes = costmodel.leaves_by_state(MAP)
        self.assertEqual(states, {'auto': 1, 'manual': 2, 'open': 0})
        self.assertEqual(classes, {'Reaches': 1, 'ExitGoal': 1})

    def test_share_history(self):
        self.assertEqual(costmodel.share_history(ROWS),
                         [('2026-01-01T00:02:00Z', 'joins', 'F1', 2, 21, 5, 21)])

    def test_render(self):
        md = costmodel.render(MAP, ROWS)
        self.assertIn('| leaf | 2 | 15 | 30 | 0.8 | 1.5 |', md)
        self.assertIn('| f_1 one | closed | 2 | 1 | 1 | 0 | 4 | 40 | 1/2/0 | 2 | 30 | 1.5 |', md)
        self.assertIn('| 2026-01-01T00:02:00Z | joins | F1 | 2/21 (10%) | 5/21 (24%) |', md)
        self.assertIn('| closed | 1 | 2 | 1 | 1 | 0 | 40 | 4 |', md)
        self.assertIn('| ready | 1 | 1 | 0 | 0 | 1 | 10 | 2 |', md)
        self.assertNotIn('| out |', md)
        self.assertNotIn('f_2 two', md.split('## Auto-closed')[0])
        self.assertIn('no extrapolated total', md)


if __name__ == '__main__':
    unittest.main()
