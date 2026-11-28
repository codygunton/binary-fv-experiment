"""Variable locations from the debug information (plan S23)."""
import json
import os
import sys
import unittest

TOOLS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PACKAGE = os.path.dirname(TOOLS)
sys.path.insert(0, TOOLS)

from elftools.dwarf.dwarf_expr import DWARFExprOp  # noqa: E402

from zmap import varloc, workqueue  # noqa: E402

ELF = '/home/cody/zesislar/build/stock-zisk/zesu-zisk.elf'
OBJ = ('/home/cody/zesislar-archive/stock-inputs/'
       'dcd4b1bec1b02f94d7c4bca3d8323c386cfc7b780995235d6947790bb68d1afe-zesu.o')
MAP_PATH = os.path.join(PACKAGE, 'map', 'map.json')
VARLOC = os.path.join(PACKAGE, 'map', 'varloc')

DBG = MAP = None


def setUpModule():
    global DBG, MAP
    DBG = varloc.Debug(ELF, OBJ)
    with open(MAP_PATH) as f:
        MAP = json.load(f)


def op(name, *args):
    return DWARFExprOp(0, name, list(args), 0)


def table(name):
    f = workqueue.find(MAP, name)
    return f, varloc.function_table(f, DBG.function(f['entry']))


def at_named(t, pc):
    return {t['vars'][vi]['name']: (t['vars'][vi]['locs'][li][3] if li >= 0 else None)
            for vi, li in varloc.at(t, pc)}


class Expressions(unittest.TestCase):
    def test_register(self):
        self.assertEqual(varloc.location([op('DW_OP_reg10')], 8), ('reg', 'a0', [['reg', None, 10, None]]))

    def test_frame_slot(self):
        kind, text, pieces = varloc.location([op('DW_OP_fbreg', -0x50)], 8)
        self.assertEqual((kind, text, pieces), ('mem', '[s0-0x50]', [['mem', None, 8, -0x50]]))

    def test_pieces(self):
        kind, text, pieces = varloc.location(
            [op('DW_OP_reg13'), op('DW_OP_piece', 8), op('DW_OP_piece', 8)], 8)
        self.assertEqual(kind, 'pieces')
        self.assertEqual(text, 'a3:8 ?:8')
        self.assertEqual(pieces, [['reg', 8, 13, None], ['undef', 8, None, None]])

    def test_constant_and_computed(self):
        self.assertEqual(varloc.location([op('DW_OP_lit0'), op('DW_OP_stack_value')], 8)[:2], ('const', '=0'))
        kind, text, _ = varloc.location([op('DW_OP_breg10', 0), op('DW_OP_breg16', 0), op('DW_OP_constu', 48),
                                         op('DW_OP_mul'), op('DW_OP_plus'), op('DW_OP_stack_value')], 8)
        self.assertEqual((kind, text), ('expr', '=(a0+(a6*48))'))


class Debug(unittest.TestCase):
    def test_relocated_variables(self):
        # every variable/parameter DIE of a subprogram with code; plan revision 3 counted 27,602
        # records with slightly different rules (abstract DIEs included)
        n = sum(len(f['vars']) for f in DBG.funcs)
        self.assertGreater(n, 27000)
        self.assertEqual(DBG.evidence['code_section_deltas'], {'1': 0x80000000, '6': 2148383292})

    def test_rotate_8330(self):
        f, t = table('mem.rotate__anon_8330')
        self.assertTrue(t['debug'])
        self.assertEqual(t['frame_base'], 8)
        self.assertEqual(len(t['cuts']), 8)
        # inner head of the first reversal (i1): reverse's i in a6, end in a5, rotate's amount in a2
        v = at_named(t, 0x8006469c)
        self.assertEqual((v['i'], v['end'], v['amount']), ('a6', 'a5', 'a2'))
        self.assertIsNone(v['tmp'])
        # outer head (o1): i has no location there (lit0 range ends at the head)
        self.assertIsNone(at_named(t, 0x80064688)['i'])
        self.assertEqual(t['coverage'], {'in_scope': 27, 'located': 16, 'cuts': 8})

    def test_merge_7964_ranges_in_pieces(self):
        f, t = table('sort.block.mergeInPlace__anon_7964')
        v = at_named(t, 0x8004f3dc)  # outer loop head: A = [as, ae) in a3, a7
        self.assertEqual(v['A'], 'a3:8 a7:8')
        self.assertEqual(v['B'], 't3:8')

    def test_no_debug_function(self):
        f, t = table('memcpy')
        self.assertFalse(t['debug'])
        self.assertEqual(t['coverage']['located'], 0)


class Hand(unittest.TestCase):
    def test_rotate_facts(self):
        fs, facts = varloc.hand_facts(PACKAGE, 'ZesuExec/Fn/Rotate/C8330')
        self.assertEqual(fs, 32)
        by = {}
        for x in facts:
            by[x['class']] = by.get(x['class'], 0) + 1
        self.assertEqual(by, {'param': 3, 'cut': 65, 'convention': 112})
        o1 = {x['loc']: x['value'] for x in facts if x['pc'] == 0x80064688 and x['class'] == 'cut'}
        self.assertEqual(o1[10], 'ptr m')
        self.assertEqual(len(o1), 11)
        i1 = [x for x in facts if x['pc'] == 0x8006469c and x['class'] == 'cut']
        self.assertEqual(len(i1), 14)  # eqO1, t3, and the byte pointers t4/t5

    def test_merge_11564_slots(self):
        fs, facts = varloc.hand_facts(PACKAGE, 'ZesuExec/Fn/MergeInPlace/C11564')
        self.assertEqual(fs, 0x110)
        r1 = {x['loc'] for x in facts if x['pc'] == 0x80098f78 and x['kind'] == 'slot' and x['class'] == 'cut'}
        self.assertEqual(r1, {0x8, 0x10, 0x18, 0x20, 0x30, 0x38, 0x40, 0x48, 0x50, 0x58, 0x60})

    def test_validation(self):
        report = {r['name']: r for r in varloc.validate(MAP, PACKAGE, DBG)}
        s = report['mem.rotate__anon_8330']['share']
        self.assertEqual((s['param']['supplied'], s['cut']['supplied']), (1, 11))
        f = report['sort.block.mergeInPlace__anon_11564']['facts']
        # rotation (R1): slot 0x48 holds mid, slot 0x50 as (= A.start)
        got = {x['loc']: x['supplied_by'] for x in f if x['pc'] == 0x80098f78 and x['kind'] == 'slot'}
        self.assertEqual(got[0x48], ['mid'])
        self.assertEqual(got[0x50], ['A'])
        self.assertEqual(got[0x10], [])
        self.assertIn('hand-written register and slot facts', varloc.validation_text(list(report.values())))


@unittest.skipUnless(os.path.exists(os.path.join(VARLOC, 'index.json')), 'map/varloc not built')
class Tables(unittest.TestCase):
    def test_every_target_function(self):
        with open(os.path.join(VARLOC, 'index.json')) as f:
            idx = json.load(f)
        target = [f for f in MAP['functions'] if f['set'] == 'target']
        self.assertEqual(set(idx['functions']), {f['id'] for f in target})
        cuts = sum(len(f['cuts']) for f in target)
        self.assertEqual(sum(idx['coverage']['per_cut'].values()), cuts)
        for f in target:
            self.assertTrue(os.path.exists(os.path.join(VARLOC, f'{f["id"]}.json')), f['id'])

    def test_brief_table(self):
        t = varloc.load(PACKAGE, 'f_80076ed0')
        text = varloc.render(t)
        cut_lines = [l for l in text.split('\n') if l.startswith('  0x')]
        self.assertEqual(len(cut_lines), len(t['cuts']))
        self.assertEqual(len(t['cuts']), 465)

    def test_block_rows(self):
        f = workqueue.find(MAP, 'mem.rotate__anon_8330')
        t = varloc.load(PACKAGE, f['id'])
        rows = varloc.block_rows(t, [b['start'] for b in f['blocks']])
        self.assertEqual(len(rows['blocks']), len(f['blocks']))
        self.assertEqual(len(rows['vars']), len(t['vars']))
        entry = {rows['vars'][v][0]: (rows['locs'][k] if k >= 0 else None) for v, k in rows['blocks'][0]}
        self.assertEqual(entry, {'amount': 'a2'})


if __name__ == '__main__':
    unittest.main()
