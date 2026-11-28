"""Source functions and source edges of the source view (plan S9.4), from the debug object."""
import json
import os
import shutil
import sys
import tempfile
import unittest

TOOLS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PACKAGE = os.path.dirname(TOOLS)
sys.path.insert(0, TOOLS)

from zmap import elfread, site, source  # noqa: E402

ELF = '/home/cody/zesislar/build/stock-zisk/zesu-zisk.elf'
OBJ = ('/home/cody/zesislar-archive/stock-inputs/'
       'dcd4b1bec1b02f94d7c4bca3d8323c386cfc7b780995235d6947790bb68d1afe-zesu.o')
TARGET_INSTRUCTIONS = 203606
MAP = SRC = None


def setUpModule():
    global MAP, SRC
    with open(os.path.join(PACKAGE, 'map', 'map.json')) as f:
        MAP = json.load(f)
    SRC = source.load(ELF, OBJ, MAP, elfread.disassemble(ELF))


def by_name(name):
    hits = [f for f in SRC['functions'] if f['name'] == name]
    assert len(hits) == 1, (name, len(hits))
    return hits[0]


def edge_kinds(a, b):
    return {s[2] for e in SRC['edges'] if e['from'] == a['id'] and e['to'] == b['id'] for s in e['sites']}


class Source(unittest.TestCase):
    def test_every_instruction_has_one_owner(self):
        """Every target instruction belongs to exactly one innermost source function or to
        compiler (runtime: binary functions the debug object has no code for)."""
        owner = SRC['pc_owner']
        self.assertEqual(len(owner), TARGET_INSTRUCTIONS)
        self.assertEqual(sum(f['n_instr'] for f in MAP['functions'] if f['set'] == 'target'),
                         TARGET_INSTRUCTIONS)
        kinds = {SRC['functions'][s]['kind'] for s in owner.values()}
        self.assertLessEqual(kinds, {'source', 'compiler', 'runtime'})

    def test_location_totals(self):
        total = sum(L['instr'] for f in SRC['functions'] for L in f['locations'])
        self.assertEqual(total, TARGET_INSTRUCTIONS)

    def test_tx_access_list_edges(self):
        tx = by_name('rlp_decode.txAccessList')
        self.assertIn('call', edge_kinds(tx, by_name('rlp.decodeItem')))
        self.assertIn('indirect', edge_kinds(tx, by_name('alt_fl_alloc.alloc')))
        oof = [L for L in tx['locations'] if L['out_of_line']]
        self.assertEqual([L['fn'] for L in oof], ['f_80000000'])

    def test_site_lines_inside_caller(self):
        fns = SRC['functions']
        for e in SRC['edges']:
            a = fns[e['from']]
            for f, line, kind, addr, extra in e['sites']:
                if line is None:
                    continue
                self.assertEqual(f, a['file'], (a['name'], line, kind))
                self.assertTrue(a['lo'] <= line <= a['hi'], (a['name'], a['lo'], a['hi'], line, kind))

    def test_groups_and_generics(self):
        groups = {f['group'] for f in SRC['functions']}
        self.assertLessEqual(groups, set(source.GROUPS))
        self.assertTrue({'zesu', 'std', 'compiler'} <= groups)
        # A generic is one record holding all its compiled copies.
        blocks = [f for f in SRC['functions'] if f['name'] == 'sort.block.block']
        self.assertEqual(len(blocks), 1)
        self.assertGreater(sum(L['out_of_line'] for L in blocks[0]['locations']), 1)

    def test_closed_only_when_every_location_is(self):
        by_id = {f['id']: f for f in MAP['functions']}
        closed = ('closed', 'closed+sail', 'closed+compliance')
        for f in SRC['functions']:
            states = [by_id[L['fn']]['state'] for L in f['locations']]
            if f['derived']['proof'] in closed:
                self.assertTrue(all(s in closed for s in states), f['name'])

    def test_site_writes_source_data(self):
        out = tempfile.mkdtemp(prefix='zmap-src-')
        try:
            info = site.write_src(out, SRC, MAP)
            self.assertTrue(os.path.exists(os.path.join(out, 'src', 'index.js')))
            for fl in SRC['files']:
                self.assertTrue(os.path.exists(os.path.join(out, 'src', 'file', f'{fl["n"]}.js')))
            self.assertEqual(info['stats']['instructions'], TARGET_INSTRUCTIONS)
        finally:
            shutil.rmtree(out, ignore_errors=True)


if __name__ == '__main__':
    unittest.main()
