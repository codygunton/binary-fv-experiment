"""Layout and site of the graph viewer (plan S9): built from the committed map.json."""
import json
import os
import shutil
import sys
import tempfile
import unittest

TOOLS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PACKAGE = os.path.dirname(TOOLS)
sys.path.insert(0, TOOLS)

from zmap import layout, site  # noqa: E402

UI = os.path.join(os.path.dirname(PACKAGE), 'tools', 'binary-regions-ui')
MAP = OUT = INDEX = None


def setUpModule():
    global MAP, OUT, INDEX
    with open(os.path.join(PACKAGE, 'map', 'map.json')) as f:
        MAP = json.load(f)
    with open(os.path.join(PACKAGE, 'map', 'reviews.json')) as f:
        reviews = json.load(f)
    OUT = tempfile.mkdtemp(prefix='zmap-site-')
    site.build(MAP, [], reviews, OUT, UI)
    INDEX = read_js(os.path.join(OUT, 'data', 'index.js'), 'window.ZMAP_INDEX = ', ';\n')


def tearDownModule():
    shutil.rmtree(OUT, ignore_errors=True)


def read_js(path, prefix, suffix):
    with open(path) as f:
        text = f.read()
    assert text.startswith(prefix) and text.endswith(suffix), path
    return json.loads(text[len(prefix):len(text) - len(suffix)])


def read_fn(fid):
    with open(os.path.join(OUT, 'data', 'fn', f'{fid}.js')) as f:
        text = f.read()
    return json.loads(text[text.index(', ') + 2:text.rindex(')')])


def target():
    return [f for f in MAP['functions'] if f['set'] == 'target']


def overlap(a, b):
    """Open rectangles (x0, y0, x1, y1) intersect."""
    return a[0] < b[2] and b[0] < a[2] and a[1] < b[3] and b[1] < a[3]


class Program(unittest.TestCase):
    def test_no_two_nodes_overlap(self):
        lay = INDEX['layout']
        items = lay['items']
        rects = [(it['x'] - it['w'] / 2, it['y'] - it['h'] / 2, it['x'] + it['w'] / 2,
                  it['y'] + it['h'] / 2, it['id']) for it in items]
        rects.sort()
        for i, a in enumerate(rects):
            for b in rects[i + 1:]:
                if b[0] >= a[2]:
                    break
                self.assertFalse(overlap(a, b), f'{a[4]} overlaps {b[4]}')
        # Expanded stack members: circles of their largest radius, inside the item's slot.
        for it in items:
            ms = [lay['functions'][m] for m in it['members']]
            for m in ms:
                r = max(m['r'].values())
                self.assertGreaterEqual(m['x'] - r, it['x'] - it['w'] / 2 - 0.2)
                self.assertLessEqual(m['x'] + r, it['x'] + it['w'] / 2 + 0.2)
            for a, b in zip(ms, ms[1:]):
                self.assertGreaterEqual(b['x'] - a['x'], max(a['r'].values()) + max(b['r'].values()))

    def test_every_edge_joins_known_nodes(self):
        fids = {f['id'] for f in INDEX['functions']}
        items = {it['id'] for it in INDEX['layout']['items']}
        for e in INDEX['edges']:
            self.assertIn(e['from'], fids)
            self.assertIn(e['to'], fids)
        for key in INDEX['layout']['routes']:
            a, b = key.split('>')
            self.assertIn(a, items)
            self.assertIn(b, items)
        self.assertEqual(fids, set(INDEX['layout']['functions']))

    def test_layers_respect_forward_calls(self):
        pos = INDEX['layout']['functions']
        back = {tuple(p) for p in INDEX['layout']['back']}
        for e in INDEX['edges']:
            if e['from'] != e['to'] and (e['from'], e['to']) not in back:
                self.assertLess(pos[e['from']]['layer'], pos[e['to']]['layer'])

    def test_root_on_top(self):
        root = INDEX['root']
        self.assertEqual(INDEX['layout']['functions'][root]['layer'], 0)


class Function(unittest.TestCase):
    def test_blocks_do_not_overlap(self):
        for f in target():
            lay = layout.function(f)
            rects = sorted((b['x'], b['y'], b['x'] + b['w'], b['y'] + b['h']) for b in lay['blocks'])
            for i, a in enumerate(rects):
                for b in rects[i + 1:]:
                    if b[0] >= a[2]:
                        break
                    self.assertFalse(overlap(a, b), f'{f["name"]}: blocks overlap at {a} {b}')

    def test_every_edge_joins_known_blocks(self):
        for f in target():
            lay = layout.function(f)
            starts = {b['start'] for b in lay['blocks']}
            self.assertEqual(len(lay['edges']), len(f['edges']), f['name'])
            for e in lay['edges']:
                self.assertIn(e['from'], starts)
                self.assertIn(e['to'], starts)
            stubs = {s['key'] for s in lay['callee_stubs']}
            for c in lay['calls']:
                self.assertIn(c['block'], starts)
                self.assertIn(c['stub'], stubs)

    def test_call_and_return_edges(self):
        """Every call site has a call edge and, unless tail or no-return, a return edge.

        A call whose return address lies past the function's end (8 sites, the callee never
        returns but the static map does not know it) has no return site and counts as no-return.
        """
        n_outside = 0
        for f in target():
            lay = layout.function(f)
            by_site = {c['site']: c for c in lay['calls']}
            self.assertEqual(set(by_site), {c['site'] for c in f['calls']}, f['name'])
            for c in f['calls']:
                row = by_site[c['site']]
                self.assertGreaterEqual(len(row['call']), 2)
                starts = {b['start'] for b in f['blocks']}
                if c['kind'] == 'tail' or c.get('noreturn') or c['ret'] not in starts:
                    self.assertIsNone(row['return'], f'{f["name"]} {c["site"]:#x}')
                    n_outside += c['kind'] != 'tail' and not c.get('noreturn')
                    self.assertEqual(row['no_return_site'], c['kind'] != 'tail' and c['ret'] not in starts)
                else:
                    self.assertIsNotNone(row['return'], f'{f["name"]} {c["site"]:#x}')
        self.assertEqual(n_outside, 8)

    def test_tx_access_list(self):
        tx = read_fn('f_80000000')['layout']
        self.assertEqual(len(tx['hulls']), 2)
        self.assertEqual(len(tx['calls']), 12)
        self.assertEqual(sum(c['return'] is not None for c in tx['calls']), 12)
        leaves = [l for c in tx['leaf_paths'].values() for l in c['leaves']]
        self.assertEqual(len(leaves), 51)
        self.assertFalse([l for l in leaves if l['approx']])


class Site(unittest.TestCase):
    def test_index_under_one_megabyte(self):
        self.assertLess(os.path.getsize(os.path.join(OUT, 'data', 'index.js')), 1 << 20)
        built = os.path.join(PACKAGE, 'map', 'site', 'data', 'index.js')
        if os.path.exists(built):
            self.assertLess(os.path.getsize(built), 1 << 20)

    def test_every_target_function_has_a_file(self):
        for f in target():
            self.assertTrue(os.path.exists(os.path.join(OUT, 'data', 'fn', f'{f["id"]}.js')), f['name'])
        self.assertEqual(len(INDEX['functions']), len(target()))

    def test_pages(self):
        self.assertTrue(os.path.exists(os.path.join(OUT, 'index.html')))
        self.assertTrue(os.path.exists(os.path.join(OUT, 'vendor', 'd3.min.js')))
        self.assertFalse(os.path.exists(os.path.join(OUT, 'map.html')))

    def test_meaning_from_reviews(self):
        by_id = {f['id']: f for f in INDEX['functions']}
        self.assertEqual(by_id['f_80000000']['meaning'], 'spec-sail')
        self.assertEqual(by_id['f_8000050c']['meaning'], 'machine-only')
        self.assertEqual(by_id['f_80042494']['meaning'], 'none')


if __name__ == '__main__':
    unittest.main()
