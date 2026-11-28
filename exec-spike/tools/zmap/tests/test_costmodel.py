"""The cost model on a two-function map and a few costed items."""
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
     'n_instr': 40, 'leaves': {'auto': 1, 'manual': 2, 'open': 0}, 'classes': ['size:<=150'],
     'cost': {'all': {'items': 2, 'minutes': 30.0, 'usd': 1.5}},
     'vc_cuts': [{'leaves': [leaf('auto'), leaf('manual', '2 goals; head Reaches'),
                             leaf('manual', '1 goal; head ExitGoal; x')]}]},
    {'id': 'f_2', 'name': 'two', 'set': 'target', 'state': 'ready', 'cuts': [{}], 'loops': [],
     'calls': [], 'joins': [{}], 'leaves_estimate': 2, 'n_instr': 10, 'classes': ['size:<=150']},
    {'id': 'f_3', 'name': 'three', 'set': 'out', 'state': 'out', 'n_instr': 99},
]}

ITEMS = [
    {'kind': 'leaf', 'minutes': 10.0, 'fn': 'f_1', 'item': 'leaf a',
     'cost': {'usd': 0.5, 'totalTokens': 100, 'requests': 2, 'builds': 1}},
    {'kind': 'leaf', 'minutes': 20.0, 'fn': 'f_1', 'item': 'leaf b',
     'cost': {'usd': 1.0, 'totalTokens': 300, 'requests': 4, 'builds': 0}},
]
ROWS = [{'ts': '2026-01-01T00:02:00Z', 'kind': 'rule', 'minutes': 0, 'fn': 'f_1',
         'item': 'joins', 'note': 'auto_share F1 2/21 -> 5/21'}]


class CostModel(unittest.TestCase):
    def test_kind_table(self):
        t = costmodel.kind_table(ITEMS)
        self.assertEqual(t['leaf'], (2, 15.0, 30.0, 0.75, 1.5, 400, 6, 1))

    def test_leaves_and_classes(self):
        states, classes = costmodel.leaves_by_state(MAP)
        self.assertEqual(states, {'auto': 1, 'manual': 2, 'open': 0})
        self.assertEqual(classes, {'Reaches': 1, 'ExitGoal': 1})
        self.assertEqual(costmodel.residual_class('1 goal; head LeafGoal; class oblig Eq'),
                         'oblig')

    def test_share_history(self):
        self.assertEqual(costmodel.share_history(ROWS),
                         [('2026-01-01T00:02:00Z', 'joins', 'F1', 2, 21, 5, 21)])

    def test_render(self):
        md = costmodel.render(MAP, ITEMS, ROWS, {})
        self.assertIn('| leaf | 2 | 15 | 30 | 0.75 | 1.50 | 400 | 6 | 1 |', md)
        self.assertIn('| f_1 one | closed | 2 | 1 | 1 | 0 | 4 | 40 | 1/2/0 | 2 | 30 | 1.50 |', md)
        self.assertIn('| 2026-01-01T00:02:00Z | joins | F1 | 2/21 (10%) | 5/21 (24%) |', md)
        self.assertIn('| closed | 1 | 2 | 1 | 1 | 0 | 40 | 4 |', md)
        self.assertIn('| ready | 1 | 1 | 0 | 0 | 1 | 10 | 2 |', md)
        self.assertNotIn('| out |', md)
        self.assertNotIn('f_2 two', md.split('## Auto-closed')[0])
        self.assertIn('| size:<=150 | 1 | 0.75 | - | - |', md)
        self.assertIn('## Forecast', md)


if __name__ == '__main__':
    unittest.main()
