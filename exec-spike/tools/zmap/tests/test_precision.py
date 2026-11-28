"""Map precision (plan stage S17): indirect-transfer resolution on small programs, write
summaries, cycle cuts, and the facts of the committed static map."""
import json
import os
import sys
import unittest
from collections import Counter

TOOLS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PACKAGE = os.path.dirname(TOOLS)
sys.path.insert(0, TOOLS)

from zmap import analyze, elfread, precision  # noqa: E402

STATIC = os.path.join(PACKAGE, 'map', 'static.json')
RODATA = 0x2000


def code(start, rows):
    """Instructions from (mnemonic, operands) rows, 4 bytes each."""
    out, pc = [], start
    for mn, ops in rows:
        o = [x.strip() for x in ops.split(',')] if ops else []
        target = int(o[-1], 16) if mn in elfread.BRANCHES or mn == 'jal' else None
        out.append(elfread.Insn(pc, 4, mn, o, target))
        pc += 4
    return out


def words(*ws):
    return b''.join(w.to_bytes(8, 'little') for w in ws)


def program(funcs, rodata):
    """A Binary of named functions [(name, insns)] and a .rodata blob at RODATA."""
    insns = {i.pc: i for _, ins in funcs for i in ins}
    fns = [analyze.Function(ins[0].pc, 4 * len(ins), name, []) for name, ins in funcs]
    lo, hi = min(insns), max(insns) + 4
    sections = {'.text': (lo, hi - lo), '.rodata': (RODATA, len(rodata))}
    b = analyze.Binary(insns, fns, sections, {'.text': bytes(hi - lo), '.rodata': rodata})
    b.scan_fn_tables()
    return b


RET = ('jalr', 'zero, 0x0(ra)')
G = ('g', code(0x1800, [RET]))


def site(cfg, kind):
    return next(c for c in cfg['ctrl'].values() if c['kind'] == kind)


class Resolution(unittest.TestCase):
    def test_exact_constant_table_slot(self):
        f = code(0x1000, [('lui', 'a5, 0x2'), ('ld', 'a5, 0x0(a5)'), ('jalr', 'ra, 0x0(a5)'), RET])
        b = program([('f', f), G], words(0x1800))
        c = site(analyze.function_cfg(b, b.functions[0]), 'icall')
        self.assertEqual((c['resolution'], c['targets']), ('exact', [0x1800]))
        self.assertEqual(c['slice'], '0x1800')

    def test_precondition_targets_from_caller(self):
        h = code(0x1000, [('ld', 'a5, 0x8(a1)'), ('ld', 'a5, 0x0(a5)'), ('jalr', 'ra, 0x0(a5)'),
                          RET])
        caller = code(0x1100, [('addi', 'sp, sp, -0x20'), ('lui', 'a0, 0x2'),
                               ('sd', 'a0, 0x8(sp)'), ('addi', 'a1, sp, 0x0'),
                               ('jal', 'ra, 0x1000'), ('addi', 'sp, sp, 0x20'), RET])
        b = program([('h', h), ('caller', caller), G], words(0x1800))
        cfgs = [analyze.function_cfg(b, f) for f in b.functions]
        c = site(cfgs[0], 'icall')
        self.assertEqual((c['resolution'], c['slice']), ('precondition', 'ld8[ld8[(a1+0x8)]]'))
        precision.Interproc(b, cfgs).run()
        self.assertEqual((c['targets'], c['targets_complete']), ([0x1800], True))

    def test_unknown_call_result(self):
        f = code(0x1000, [('jal', 'ra, 0x1800'), ('jalr', 'ra, 0x0(a0)'), RET])
        b = program([('f', f), G], words(0))
        c = site(analyze.function_cfg(b, b.functions[0]), 'icall')
        self.assertEqual((c['resolution'], c['reason'], c['targets']),
                         ('unknown', 'call-result', []))

    def test_byte_indexed_dispatch_is_exact(self):
        f = code(0x1000, [('lbu', 'a0, 0x0(a1)'), ('slli', 'a0, a0, 0x3'), ('lui', 'a2, 0x2'),
                          ('add', 'a0, a2, a0'), ('ld', 'a0, 0x0(a0)'), ('jalr', 'zero, 0x0(a0)'),
                          RET, RET])
        b = program([('f', f)], words(*[0x1018, 0x101c] * 128))
        cfg = analyze.function_cfg(b, b.functions[0])
        c = site(cfg, 'ijump')
        self.assertEqual((c['resolution'], c['targets']), ('exact', [0x1018, 0x101c]))
        self.assertEqual(cfg['tables'][0x1014]['entries'], 256)

    def test_bound_check_refines_index(self):
        f = code(0x1000, [('addi', 'a2, zero, 0x2'), ('bgeu', 'a0, a2, 0x1020'),
                          ('slli', 'a0, a0, 0x3'), ('lui', 'a2, 0x2'), ('add', 'a0, a2, a0'),
                          ('ld', 'a0, 0x0(a0)'), ('jalr', 'zero, 0x0(a0)'), RET, RET])
        b = program([('f', f)], words(0x101c, 0x1020, 0, 0))
        c = site(analyze.function_cfg(b, b.functions[0]), 'ijump')
        self.assertEqual((c['resolution'], c['targets']), ('exact', [0x101c, 0x1020]))

    def test_unbounded_argument_index_is_precondition(self):
        f = code(0x1000, [('andi', 'a0, a0, 0xff'), ('slli', 'a0, a0, 0x3'), ('lui', 'a2, 0x2'),
                          ('add', 'a0, a2, a0'), ('ld', 'a0, 0x0(a0)'), ('jalr', 'zero, 0x0(a0)'),
                          RET, RET])
        b = program([('f', f)], words(0x1018, 0x101c, *[0] * 254))
        cfg = analyze.function_cfg(b, b.functions[0])
        c = site(cfg, 'ijump')
        self.assertEqual((c['resolution'], c['targets']), ('precondition', [0x1018, 0x101c]))
        self.assertEqual(cfg['tables'][0x1014]['entries'], 2)

    def test_computed_jump_into_code(self):
        slot = [('addi', 'a0, a0, 0x1')] * 3 + [RET]
        f = code(0x1000, [('andi', 'a1, a1, 0x3'), ('slli', 'a1, a1, 0x4'), ('auipc', 't0, 0x0'),
                          ('addi', 't0, t0, 0x18'), ('add', 't0, t0, a1'),
                          ('jalr', 'zero, 0x0(t0)'), RET, RET] + slot * 4)
        b = program([('f', f)], words(0))
        c = site(analyze.function_cfg(b, b.functions[0]), 'ijump')
        self.assertEqual((c['resolution'], c['targets']), ('exact', [0x1020, 0x1030, 0x1040,
                                                                     0x1050]))


class Summaries(unittest.TestCase):
    def test_kill_only_the_written_window(self):
        st = precision.State()
        st.store(-16, 8, ('c', 1))
        st.store(-8, 8, ('c', 2))
        st.set('a0', precision.add(precision.SP, precision.const(-16)))
        precision.kill_written(st, {'a0': (0, 8)})
        self.assertEqual(st.load(-16, 8, True), precision.TOP)
        self.assertEqual(st.load(-8, 8, True), ('c', 2))
        precision.kill_written(st, precision.UNKNOWN)
        self.assertEqual(st.load(-8, 8, True), precision.TOP)

    def test_transitive_window(self):
        callee = code(0x1000, [('sd', 'zero, 0x8(a0)'), RET])
        caller = code(0x1100, [('addi', 'a0, a1, 0x10'), ('jal', 'ra, 0x1000'), RET])
        b = program([('callee', callee), ('caller', caller)], words(0))
        w = precision.write_summaries([analyze.function_cfg(b, f) for f in b.functions])
        self.assertEqual(w[0x1000], {'a0': (8, 16)})
        self.assertEqual(w[0x1100], {'a1': (24, 32)})


class Cycles(unittest.TestCase):
    def test_multi_entry_region_and_cut(self):
        succ = {0: [1, 2], 1: [2], 2: [1, 3], 3: []}
        regions = precision.multi_entry_regions(0, list(succ), succ)
        self.assertEqual(regions, [{'entries': [1, 2], 'nodes': [1, 2]}])
        self.assertEqual(len(precision.uncut_regions(list(succ), succ, {0})), 1)
        added = precision.cycle_cuts(list(succ), succ, {0})
        self.assertEqual(len(added), 1)
        self.assertEqual(precision.uncut_regions(list(succ), succ, {0} | set(added)), [])

    def test_natural_loop_has_one_entry(self):
        succ = {0: [1], 1: [2, 3], 2: [1], 3: []}
        self.assertEqual(precision.multi_entry_regions(0, list(succ), succ), [])
        self.assertEqual(precision.cycle_cuts(list(succ), succ, {0, 1}), [])


class Committed(unittest.TestCase):
    """Facts of the committed map/static.json (plan S17)."""

    @classmethod
    def setUpClass(cls):
        with open(STATIC) as fh:
            cls.m = json.load(fh)
        cls.by_name = {f['name']: f for f in cls.m['functions']}
        cls.by_id = {f['id']: f for f in cls.m['functions']}

    def test_kinds(self):
        kinds = {c['resolution'] for f in self.m['functions'] for c in f['calls']
                 if c['kind'] == 'indirect'}
        self.assertLessEqual(kinds, {'exact', 'precondition', 'unknown'})
        self.assertEqual(self.m['precision']['indirect_calls_target'],
                         dict(Counter(c['resolution'] for f in self.m['functions']
                                      if f['set'] == 'target'
                                      for c in f['calls'] if c['kind'] == 'indirect')))

    def test_memset_and_dispatch_resolved(self):
        ms = self.by_name['memset']
        self.assertEqual([(j['resolution'], len(j['targets'])) for j in ms['jump_tables']],
                         [('exact', 256)])
        rd = self.by_name['interpreter.runDispatch__anon_13271']
        self.assertEqual({j['resolution'] for j in rd['jump_tables']}, {'exact'})
        self.assertEqual(len(rd['jump_tables']), 174)
        for f in (ms, rd):
            self.assertFalse(any(b['kind'] == 'indirect-jump-unresolved' for b in f['blockers']))

    def test_tx_access_list_allocator_calls(self):
        f = self.by_id['f_80000000']
        ind = [c for c in f['calls'] if c['kind'] == 'indirect']
        self.assertEqual({c['resolution'] for c in ind}, {'precondition'})
        self.assertTrue(all(c['targets_complete'] for c in ind))
        self.assertEqual({self.by_id[t]['name'] for c in ind for t in c['targets']},
                         {'alt_fl_alloc.alloc', 'alt_fl_alloc.remap', 'alt_fl_alloc.free'})

    def test_false_recursion_gone(self):
        self.assertFalse(self.by_name['scratch_arena.alloc']['recursive'])
        self.assertTrue(self.by_name['ssz_output.sparseRoot']['recursive'])

    def test_every_cycle_passes_a_cut(self):
        for f in self.m['functions']:
            if f['set'] != 'target':
                continue
            succ = {b['start']: b['succ'] for b in f['blocks']}
            cuts = {c['pc'] for c in f['cuts']}
            self.assertEqual(precision.uncut_regions(list(succ), succ, cuts), [], f['name'])
            self.assertFalse(any(b['kind'] == 'irreducible' for b in f['blockers']))

    def test_irreducible_regions(self):
        irr = [f for f in self.m['functions'] if f['irreducible']]
        self.assertGreaterEqual(len(irr), 7)
        for f in irr:
            self.assertTrue(f['irreducible_regions'], f['name'])
            for r in f['irreducible_regions']:
                self.assertGreater(len(r['entries']), 1)
                self.assertLessEqual(set(r['entries']), set(r['nodes']))


if __name__ == '__main__':
    unittest.main()
