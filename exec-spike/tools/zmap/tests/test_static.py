"""Structural and heuristic facts of the static map of the Zesu ELF (plan stage S1)."""
import json
import os
import sys
import unittest

TOOLS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PACKAGE = os.path.dirname(TOOLS)
sys.path.insert(0, TOOLS)

from zmap import analyze, elfread  # noqa: E402

ELF = '/home/cody/zesislar/build/stock-zisk/zesu-zisk.elf'
SHA256 = 'e44c18d54ae3d77832df92aceb6eb7119de8eb2e8f1f1b4e585a6e33ea04ff95'
STATIC = os.path.join(PACKAGE, 'map', 'static.json')

MAP = None


def setUpModule():
    global MAP
    assert elfread.sha256(ELF) == SHA256
    MAP = analyze.build(ELF)


def fn(name):
    return next(f for f in MAP['functions'] if f['name'] == name)


def names(ids):
    by_id = {f['id']: f['name'] for f in MAP['functions']}
    return {by_id[i] for i in ids}


class Structure(unittest.TestCase):
    def test_totals(self):
        self.assertEqual(len(MAP['functions']), 524)
        self.assertEqual(sum(f['n_instr'] for f in MAP['functions']), 278372)

    def test_tx_access_list(self):
        f = fn('rlp_decode.txAccessList')
        self.assertEqual(f['id'], 'f_80000000')
        self.assertEqual(f['n_instr'], 323)
        self.assertEqual([l['head'] for l in f['loops']], [0x800000c4, 0x8000018c])
        cuts = {c['pc']: c['why'] for c in f['cuts']}
        self.assertEqual(cuts[0x80000000], 'entry')
        self.assertEqual(cuts[0x800000c4], 'loop')
        self.assertEqual(cuts[0x8000018c], 'loop')
        direct = {t for c in f['calls'] if c['kind'] == 'direct' for t in c['targets']}
        self.assertEqual(len(direct), 5)

    def test_ensure_total_capacity(self):
        f = fn('array_list.Aligned([32]u8,null).ensureTotalCapacity')
        self.assertEqual(f['n_instr'], 107)
        self.assertEqual(f['loops'], [])
        self.assertEqual(len([c for c in f['calls'] if c['kind'] != 'tail']), 4)

    def test_decode_item(self):
        self.assertEqual(len(fn('rlp.decodeItem')['loops']), 2)

    def test_start_in_target(self):
        self.assertEqual(fn('_start')['set'], 'target')


class Heuristics(unittest.TestCase):
    def test_tx_access_list_indirect_calls(self):
        f = fn('rlp_decode.txAccessList')
        ind = [c for c in f['calls'] if c['kind'] == 'indirect']
        self.assertEqual(len(ind), 3)
        self.assertTrue(all(c['resolution'] == 'table-heuristic' for c in ind))
        cands = set().union(*(names(c['targets']) for c in ind))
        self.assertLessEqual({'alt_fl_alloc.alloc', 'alt_fl_alloc.remap', 'alt_fl_alloc.free'},
                             cands)

    def test_decode_tx_fields_jump_table(self):
        f = fn('rlp_decode.decodeTxFields')
        jt = [j for j in f['jump_tables'] if j['site'] == 0x80000584]
        self.assertEqual(len(jt), 1)
        self.assertEqual(jt[0]['resolution'], 'table-heuristic')
        self.assertEqual(len(jt[0]['targets']), 5)


class Committed(unittest.TestCase):
    """The committed map/static.json is for this ELF and agrees with a fresh build."""

    def test_static_json(self):
        with open(STATIC) as fh:
            static = json.load(fh)
        self.assertEqual(static['schema'], 'zmap.static.v1')
        self.assertEqual(static['elf_sha256'], SHA256)
        fresh = {f['id']: (f['n_instr'], len(f['blocks']), f['leaves_estimate'], f['set'])
                 for f in MAP['functions']}
        stored = {f['id']: (f['n_instr'], len(f['blocks']), f['leaves_estimate'], f['set'])
                  for f in static['functions']}
        self.assertEqual(fresh, stored)


if __name__ == '__main__':
    unittest.main()
