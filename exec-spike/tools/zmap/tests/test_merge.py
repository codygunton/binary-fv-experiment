"""merge, queue and card on the committed static map with the legacy status fixture (plan S3)."""
import copy
import json
import os
import sys
import unittest

TOOLS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PACKAGE = os.path.dirname(TOOLS)
sys.path.insert(0, TOOLS)

from zmap import merge, workqueue  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
STATIC = None


def setUpModule():
    global STATIC, STATUS, REVIEWS
    with open(os.path.join(PACKAGE, 'map', 'static.json')) as f:
        STATIC = json.load(f)
    with open(os.path.join(HERE, 'fixtures', 'status_legacy.json')) as f:
        STATUS = json.load(f)
    with open(os.path.join(PACKAGE, 'map', 'reviews.json')) as f:
        REVIEWS = json.load(f)


def run(status, ledger=()):
    return merge.merge(copy.deepcopy(STATIC), status, REVIEWS, list(ledger))


class Legacy(unittest.TestCase):
    def test_states(self):
        m = run(STATUS)
        by = {f['id']: f for f in m['functions']}
        self.assertEqual(sum(m['state_counts'].values()), 524)
        for fid in ('f_8004218c', 'f_800cb40c', 'f_800d677c', 'f_800d6554'):
            self.assertEqual(by[fid]['state'], 'closed+sail')
        for fid in ('f_800d6960', 'f_800d6274', 'f_800d5cb8'):
            self.assertEqual(by[fid]['state'], 'closed+compliance')
        for fid in ('f_80042494', 'f_80041f38', 'f_800e06c0'):
            self.assertEqual(by[fid]['state'], 'assumed')
        self.assertEqual(by['f_800cb40c']['status_id'], 'F1')
        kinds = {t['kind'] for t in m['trust']}
        self.assertEqual(kinds, {'assumed', 'service', 'contract-unreviewed'})

    def test_card(self):
        m = run(STATUS)
        text = workqueue.card(m, workqueue.find(m, 'f_800cb40c'))
        self.assertIn('ensureTotalCapacity', text)
        self.assertIn('state: closed+sail', text)
        self.assertIs(workqueue.find(m, 'F1'), workqueue.find(m, 'f_800cb40c'))


class Conditional(unittest.TestCase):
    """A registered, assembled plan with one open leaf is `conditional` and heads the queue."""

    def test_open_leaf_first(self):
        status = copy.deepcopy(STATUS)
        status['functions'].append({
            'id': 'f_80000000', 'fn': 'TX', 'entry': 0x80000000, 'legacy': False,
            'assembled': True, 'open': ['leaf_800000c4_1'],
            'theorems': {'reach': False, 'spec': False, 'sail': False, 'compliance': False},
            'cuts': [{'pc': 0x800000c4, 'cut_lemma': 'manual', 'leaves': [
                {'i': 0, 'exit': 'at', 'target': 0x8000018c, 'state': 'auto', 'residual': None},
                {'i': 1, 'exit': 'call', 'target': 0x800d6960, 'state': 'open',
                 'residual': 'omega'}]}]})
        ledger = [{'fn': 'TX', 'kind': 'leaf', 'minutes': 3, 'usd': 0.5, 'requests': 2,
                   'outcome': 'closed'}]
        m = run(status, ledger)
        tx = next(f for f in m['functions'] if f['id'] == 'f_80000000')
        self.assertEqual(tx['state'], 'conditional')
        self.assertEqual(tx['leaves'], {'auto': 1, 'manual': 0, 'open': 1})
        self.assertEqual(tx['ledger']['all']['minutes'], 3)
        leaf = tx['vc_cuts'][0]['leaves']
        self.assertEqual(leaf[0]['cfg']['target_kind'], 'cut')
        self.assertEqual(leaf[1]['cfg']['target_kind'], 'callee')
        q = workqueue.build_queue(m)
        self.assertEqual((q[0]['type'], q[0]['fn'], q[0]['i']), ('leaf', 'f_80000000', 1))
        self.assertEqual([it['rank'] for it in q], list(range(1, len(q) + 1)))


if __name__ == '__main__':
    unittest.main()
