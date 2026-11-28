"""Tracking (programme plan S10): ledger schema 2, cost from session logs, backfill, attribution,
state rule, classes, metrics, history, brief, check, cost model, build measurements."""
import copy
import datetime
import importlib.util
import json
import os
import sys
import tempfile
import unittest

TOOLS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PACKAGE = os.path.dirname(TOOLS)
sys.path.insert(0, TOOLS)

from zmap import cost, costmodel, ledger, merge, metrics  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ALLOC, FREE = 0x80042494, 0x80041f38


def ts(s):
    return datetime.datetime.strptime(s, '%Y-%m-%dT%H:%M:%SZ').replace(
        tzinfo=datetime.timezone.utc)


def msg(t, usd, bash=None, usage=True):
    m = {'role': 'assistant', 'content': []}
    if usage:
        m['usage'] = {'input': 1, 'output': 2, 'cacheRead': 3, 'cacheWrite': 4, 'totalTokens': 10,
                      'cost': {'total': usd}}
    if bash:
        m['content'].append({'type': 'toolCall', 'name': 'bash', 'arguments': {'command': bash}})
    return {'type': 'message', 'timestamp': t, 'message': m}


def write_jsonl(path, rows):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w') as f:
        for r in rows:
            f.write(json.dumps(r, separators=(',', ':')) + '\n')


def rows_for(agent, session, spec):
    """Request rows [(iso ts, usd)] for one agent."""
    return [dict(cost._row({'totalTokens': 10, 'cost': {'total': u}}, cost.parse_ts(t), 0, None),
                 agent=agent, session=session) for t, u in spec]


class Ledger(unittest.TestCase):
    def test_start_stop_pairing(self):
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, 'ledger.jsonl')
            a = ledger.start(p, '-', 'x', 'infra', 'A', now=ts('2026-01-01T00:00:00Z'))
            with self.assertRaises(ValueError):  # one open item per agent
                ledger.start(p, 'f_1', 'y', 'leaf', 'A')
            b = ledger.start(p, 'f_1', 'y', 'leaf', 'B', now=ts('2026-01-01T00:01:00Z'))
            self.assertEqual((a['id'], b['id']), (1, 2))
            ledger.stop(p, 1, 'closed', note='n', now=ts('2026-01-01T00:05:00Z'))
            with self.assertRaises(ValueError):
                ledger.stop(p, 1, 'closed')
            with self.assertRaises(ValueError):
                ledger.stop(p, 9, 'closed')
            with self.assertRaises(ValueError):
                ledger.stop(p, 2, 'failed')  # schema 2 outcomes
            rows = ledger.read(p)
        items = ledger.pair(rows)
        self.assertEqual([i['id'] for i in items], [1, 2])
        self.assertEqual(items[0]['stop']['outcome'], 'closed')
        self.assertIsNone(items[1]['stop'])
        self.assertEqual([i['agent'] for i in ledger.open_items(rows)], ['B'])
        for r in rows:
            self.assertFalse(set(ledger.TYPED) & set(r))

    def test_ids_repeated_by_merged_branches(self):
        rows = [{'schema': 2, 'rec': 'start', 'id': 1, 'ts': '2026-01-01T00:00:00Z', 'agent': 'A',
                 'fn': None, 'item': 'a', 'kind': 'infra'},
                {'schema': 2, 'rec': 'start', 'id': 1, 'ts': '2026-01-01T00:00:00Z', 'agent': 'B',
                 'fn': None, 'item': 'b', 'kind': 'infra'},
                {'schema': 2, 'rec': 'stop', 'id': 1, 'agent': 'B', 'ts': '2026-01-01T00:01:00Z',
                 'outcome': 'closed', 'note': None}]
        items = {i['agent']: i for i in ledger.pair(rows)}
        self.assertIsNone(items['A']['stop'])
        self.assertEqual(items['B']['stop']['outcome'], 'closed')
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, 'ledger.jsonl')
            write_jsonl(p, rows[:2])
            with self.assertRaises(ValueError):  # ambiguous: both open
                ledger.stop(p, 1, 'closed')


class SessionLogs(unittest.TestCase):
    def test_files_and_rows(self):
        with tempfile.TemporaryDirectory() as root:
            s = os.path.join(root, 'S1')
            write_jsonl(s + '.jsonl', [
                {'type': 'session', 'timestamp': '2026-01-01T00:00:00Z'},
                msg('2026-01-01T00:00:01.500Z', 0.5, bash='cd P && lake build ZesuExec'),
                {'type': 'message', 'timestamp': '2026-01-01T00:00:02Z',
                 'message': {'role': 'user', 'content': [{'type': 'text', 'text': 'hi'}]}},
                {'type': 'model_usage', 'timestamp': '2026-01-01T00:00:03Z', 'purpose': 'job-caption',
                 'usage': {'input': 5, 'output': 1, 'totalTokens': 6, 'cost': {'total': 0.01}}},
                msg('2026-01-01T00:00:04Z', None, usage=False)])
            write_jsonl(os.path.join(s, 'Worker.jsonl'), [msg('2026-01-01T00:01:00Z', 1.0,
                                                              bash='lake env lean X.lean')])
            write_jsonl(os.path.join(s, 'Worker', 'Worker.Sub.jsonl'),
                        [msg('2026-01-01T00:02:00Z', 2.0)])
            write_jsonl(os.path.join(s, 'changes.jsonl'), [msg('2026-01-01T00:00:00Z', 9.0)])
            write_jsonl(os.path.join(s, 'local', 'x.jsonl'), [msg('2026-01-01T00:00:00Z', 9.0)])
            cfg = os.path.join(root, 'sessions.json')
            with open(cfg, 'w') as f:
                json.dump({'root': root, 'sessions': ['S1']}, f)
            self.assertEqual([a for a, _ in cost.agent_files(s)],
                             ['coordinator', 'Worker', 'Worker.Sub'])
            rows = cost.read_rows(cost.load_sessions(cfg))
        self.assertEqual([r['agent'] for r in rows],
                         ['coordinator', 'coordinator', 'coordinator', 'Worker', 'Worker.Sub'])
        c = rows[0]
        self.assertEqual((c['usd'], c['builds'], c['input'], c['totalTokens'], c['aux']),
                         (0.5, 1, 1, 10, None))
        self.assertEqual(rows[1]['aux'], 'job-caption')
        self.assertIsNone(rows[2]['usd'])  # no usage: unknown cost, still a request
        acc = cost._zero()
        for r in rows:
            cost.add(acc, r)
        self.assertEqual((acc['requests'], acc['unknown'], round(acc['usd'], 2), acc['builds']),
                         (5, 1, 3.51, 2))


class Attribution(unittest.TestCase):
    def setUp(self):
        self.rows = (rows_for('A', 'old', [('2026-01-01T00:00:00Z', 9.0)]) +
                     rows_for('A', 'new', [('2026-01-02T00:00:10Z', 1.0),
                                           ('2026-01-02T00:01:00Z', 2.0),
                                           ('2026-01-02T00:02:00Z', 4.0),
                                           ('2026-01-02T00:03:00Z', 8.0),
                                           ('2026-01-02T00:10:00Z', 16.0),
                                           ('2026-01-02T00:20:00Z', 32.0)]))
        self.rows.sort(key=lambda r: r['t'])
        self.agents = cost.Agents(self.rows)
        self.ledger = [
            {'ts': '2026-01-02T00:01:30Z', 'agent': 'A', 'item': 'a', 'fn': 'f_1', 'kind': 'leaf',
             'minutes': 99, 'outcome': 'closed'},
            {'ts': '2026-01-02T00:03:00Z', 'agent': 'A', 'item': 'b', 'fn': 'f_1', 'kind': 'leaf',
             'minutes': 99, 'outcome': 'closed'},
            {'ts': '2026-01-02T00:03:00Z', 'agent': 'A', 'item': 'c', 'fn': 'f_1', 'kind': 'leaf',
             'minutes': 99, 'outcome': 'open'},
            {'schema': 2, 'rec': 'start', 'id': 1, 'ts': '2026-01-02T00:05:00Z', 'agent': 'A',
             'fn': 'f_1', 'item': 'd', 'kind': 'contract'},
            {'schema': 2, 'rec': 'stop', 'id': 1, 'agent': 'A', 'ts': '2026-01-02T00:15:00Z',
             'outcome': 'abandoned', 'note': None}]

    def test_backfill_intervals(self):
        bf = cost.backfill_rows(self.ledger, self.agents)
        self.assertEqual([b['line'] for b in bf], [0, 1, 2])
        # first entry: from the session's first request (the old session is not used)
        self.assertEqual(bf[0]['cost']['usd'], 3.0)
        self.assertEqual(bf[0]['session'], 'new')
        # equal timestamps share (00:01:30, 00:03:00]: 4 + 8 = 12
        self.assertEqual([bf[1]['cost']['usd'], bf[2]['cost']['usd']], [6.0, 6.0])
        self.assertEqual(bf[1]['shared_by'], 2)
        self.assertEqual(bf[1]['minutes'], 0.75)
        self.assertTrue(all(b['backfill'] for b in bf))
        self.assertEqual(cost.backfill_rows(self.ledger, self.agents, done_lines={0, 1, 2}), [])

    def test_attribute(self):
        bf = cost.backfill_rows(self.ledger, self.agents)
        items, per = cost.attribute(self.ledger, bf, self.agents, now=0)
        v2 = [i for i in items if not i['backfill']]
        self.assertEqual(len(v2), 1)
        self.assertEqual(v2[0]['cost']['usd'], 16.0)  # (00:05, 00:15]
        self.assertEqual(v2[0]['minutes'], 10.0)
        self.assertEqual(v2[0]['outcome'], 'abandoned')
        a = per['A']
        self.assertEqual(a['session']['usd'], 72.0)
        self.assertEqual(a['items']['usd'], 31.0)
        self.assertEqual(a['unattributed']['usd'], 41.0)  # 9 old session + 32 after the item
        self.assertAlmostEqual(a['unattributed_share'], 41 / 72, places=4)

    def test_run_backfill_once(self):
        with tempfile.TemporaryDirectory() as d:
            lp, bp = os.path.join(d, 'ledger.jsonl'), os.path.join(d, 'backfill.jsonl')
            write_jsonl(lp, self.ledger[:1])
            sess = os.path.join(d, 'sessions.json')
            with open(sess, 'w') as f:
                json.dump({'root': d, 'sessions': []}, f)
            self.assertEqual(len(cost.run_backfill(lp, bp, sess)), 1)
            self.assertEqual(cost.run_backfill(lp, bp, sess), [])
            write_jsonl(lp, self.ledger[:2])
            self.assertEqual([b['line'] for b in cost.run_backfill(lp, bp, sess)], [1])
            write_jsonl(lp, self.ledger[1:3])  # history rewritten: refuse
            with self.assertRaises(ValueError):
                cost.run_backfill(lp, bp, sess)


STATIC = STATUS = REVIEWS = None


def setUpModule():
    global STATIC, STATUS, REVIEWS
    with open(os.path.join(PACKAGE, 'map', 'static.json')) as f:
        STATIC = json.load(f)
    with open(os.path.join(HERE, 'fixtures', 'status_legacy.json')) as f:
        STATUS = json.load(f)
    with open(os.path.join(PACKAGE, 'map', 'reviews.json')) as f:
        REVIEWS = json.load(f)


def merged(status=None, items=(), reviews=None):
    return merge.merge(copy.deepcopy(STATIC), copy.deepcopy(status or STATUS),
                       reviews or REVIEWS, list(items))


def with_alloc_hyp(status, fid):
    s = copy.deepcopy(status)
    for f in s['functions']:
        if f['id'] == fid:
            f['hyps'] = [{'name': 'A', 'type': 'AllocAssumptions', 'spec_entries': [ALLOC, FREE]}]
    return s


class StateRule(unittest.TestCase):
    def test_hypothesis_callees_make_closed_on_assumptions(self):
        m = merged(with_alloc_hyp(STATUS, 'f_800d677c'))
        by = {f['id']: f for f in m['functions']}
        f4 = by['f_800d677c']
        self.assertEqual(f4['state'], 'closed-on-assumptions')
        self.assertEqual(f4['rests_on'], ['f_80041f38', 'f_80042494'])
        self.assertEqual(f4['proved'], 'closed+sail')
        self.assertEqual(by['f_8004218c']['state'], 'closed+sail')  # F0 calls nothing assumed
        self.assertEqual(m['state_counts']['closed-on-assumptions'],
                         sum(f['state'] == 'closed-on-assumptions' for f in m['functions']))

    def test_rests_on_is_transitive_through_closed_callees(self):
        # a plan calling F4 rests on what F4 rests on
        s = with_alloc_hyp(STATUS, 'f_800d677c')
        s['functions'].append({
            'id': 'f_80000000', 'fn': 'TX', 'entry': 0x80000000, 'legacy': False,
            'assembled': True, 'open': [],
            'theorems': {'reach': True, 'spec': True, 'sail': True, 'compliance': True},
            'cuts': [{'pc': 0x80000000, 'cut_lemma': 'manual', 'leaves': [
                {'i': 0, 'exit': 'call', 'target': 0x800d677c, 'state': 'manual'},
                {'i': 1, 'exit': 'call', 'target': 0x800e06c0, 'state': 'auto'}]}]})
        m = merged(s)
        tx = next(f for f in m['functions'] if f['id'] == 'f_80000000')
        self.assertEqual(tx['proof_callees'], ['f_800d677c', 'f_800e06c0'])  # memcpy: service
        self.assertEqual(tx['state'], 'closed-on-assumptions')
        self.assertEqual(tx['rests_on'], ['f_80041f38', 'f_80042494'])
        self.assertEqual(tx['meaning'], 'spec-sail')
        self.assertEqual(tx['auto_share'], 0.5)

    def test_classes_meaning_links(self):
        rv = copy.deepcopy(REVIEWS)
        rv['contracts']['f_800d6960']['model'] = 'ZesuExec.Model.decodeItem'
        s = copy.deepcopy(STATUS)
        for f in s['functions']:
            if f['id'] == 'f_800d6960':
                f['post_consts'] = ['ZesuExec.Model.decodeItem']
                f['theorems']['compliance'] = False
        m = merged(s, reviews=rv)
        by = {f['id']: f for f in m['functions']}
        f2 = by['f_800d6960']
        self.assertEqual(f2['meaning'], 'model')
        self.assertTrue(f2['post_mentions_model'])
        self.assertEqual(by['f_800d6274']['meaning'], 'spec-sail')
        self.assertEqual(by['f_8004218c']['meaning'], 'machine-only')
        tx = by['f_80000000']
        self.assertEqual(tx['meaning'], 'machine-only')  # a contract, no theorem in the fixture
        self.assertEqual(by['f_80042494']['meaning'], 'none')
        self.assertIn('size:151-600', tx['classes'])
        self.assertIn('loops:1-3', tx['classes'])
        self.assertIn('indirect-call', tx['classes'])
        self.assertIn('accelerator', by['f_800e06c0']['classes'])
        sort_copies = [f for f in m['functions'] if f['set'] == 'target'
                       and f['stem'] == 'sort.block.mergeInPlace']
        self.assertGreater(len(sort_copies), 1)
        self.assertTrue(all('generic-copy' in f['classes'] for f in sort_copies))
        for f in m['functions']:
            self.assertEqual(sum(c.startswith('size:') for c in f['classes']), 1)
            self.assertEqual(sum(c.startswith('loops:') for c in f['classes']), 1)


def items_for(fid, n, usd, kind='leaf'):
    return [{'fn': fid, 'item': f'i{k}', 'kind': kind, 'agent': 'A', 'outcome': 'closed',
             'minutes': 1.0, 'backfill': True, 'open': False,
             'cost': {'usd': usd, 'requests': 1, 'totalTokens': 10, 'builds': 0}}
            for k in range(n)]


PER_AGENT = {'A': {'session': {'usd': 10.0, 'unknown': 0, 'requests': 4},
                   'items': {'usd': 6.0}, 'unattributed': {'usd': 4.0},
                   'unattributed_share': 0.4}}


class Metrics(unittest.TestCase):
    def setUp(self):
        self.items = items_for('F2', 4, 1.0) + items_for('F3', 2, 2.0) + \
            items_for(None, 1, 5.0, kind='infra')
        self.m = merged(with_alloc_hyp(STATUS, 'f_800d677c'), self.items)
        self.met = metrics.compute(self.m, self.items, PER_AGENT, None, PACKAGE,
                                   reviews_csr={}, history=[])

    def test_groups(self):
        self.assertEqual(set(metrics.GROUPS) <= set(self.met), True)
        cov = self.met['coverage']
        target = [f for f in self.m['functions'] if f['set'] == 'target']
        self.assertEqual(cov['headline']['cut_points_total'], sum(len(f['cuts']) for f in target))
        rows = {r[0]: r for r in cov['by_unit']['rows']}
        self.assertEqual(rows['functions'][-1], len(target))
        eff = self.met['effort']
        self.assertEqual(eff['total']['usd'], 13.0)
        self.assertAlmostEqual(eff['infrastructure_share'], 5 / 13, places=4)
        self.assertEqual(eff['unattributed_share'], 0.4)
        self.assertEqual(self.met['trust']['assumed_non_service'], 2)
        self.assertIn('note', self.met['build'])
        self.assertTrue(json.dumps(self.met))

    def test_forecast(self):
        fc = self.met['forecast']
        self.assertEqual(set(fc['sample_functions']), {'f_800d6960', 'f_800d6274'})
        t = fc['totals_usd']
        self.assertTrue(0 < t['p25'] <= t['p50'] <= t['p75'])
        self.assertGreater(fc['open_cut_points'], 0)
        self.assertTrue(0 <= fc['unsampled_share'] <= 1)
        by = {f['id']: f for f in self.m['functions']}
        self.assertIsNone(by['f_800d6960']['forecast'])  # proved: nothing open
        self.assertTrue(any(f.get('forecast') for f in self.m['functions']))
        md = metrics.render_group('forecast', fc)
        self.assertIn('| size band |', md)

    def test_history_one_line_per_commit(self):
        with tempfile.TemporaryDirectory() as d:
            h = os.path.join(d, 'history.jsonl')
            metrics.append_history(h, self.m, self.met, PACKAGE)
            metrics.append_history(h, self.m, self.met, PACKAGE)
            lines = metrics.read_history(h)
        self.assertEqual(len(lines), 1)
        line = lines[0]
        tx = line['fns']['f_80000000']
        self.assertEqual(line['state_codes'][tx[0]], 'waiting')
        self.assertEqual(line['meaning_codes'][tx[1]], 'machine-only')

    def test_rework(self):
        h = [{'hashes': {'f': {'pre': 'a', 'post': 'b', 'dep': False}}},
             {'hashes': {'f': {'pre': 'a2', 'post': 'b', 'dep': True}}},
             {'hashes': {'f': {'pre': 'a3', 'post': 'b', 'dep': True}}},
             {'hashes': {'f': {'pre': 'a3', 'post': 'b', 'dep': True}}},
             {'hashes': {'f': {'pre': 'a4', 'post': 'b', 'dep': True}}}]
        self.assertEqual(metrics.rework('f', h), 2)

    def test_brief(self):
        text = metrics.brief(self.m, 'f_80000000', self.items)
        self.assertLessEqual(len(text.splitlines()), 60)
        self.assertIn('rlp_decode.txAccessList', text)
        self.assertIn('cheapest comparable closed items', text)

    def test_costmodel(self):
        rows = [{'ts': '2026-01-01T00:00:00Z', 'kind': 'rule', 'item': 'r', 'fn': 'F1',
                 'note': 'auto_share F1 2/21 -> 5/21'}]
        md = costmodel.render(self.m, self.items, rows, self.met)
        self.assertIn('| leaf | 6 | 1 | 6 | 1 | 8 |', md)
        self.assertIn('| infra | 1 | 1 | 1 | 5 | 5 |', md)
        self.assertIn('| 2026-01-01T00:00:00Z | r | F1 | 2/21 (10%) | 5/21 (24%) |', md)
        self.assertIn('## Forecast', md)
        self.assertIn('## Unattributed cost per agent', md)
        self.assertIn('| A | 10 | 6 | 4 | 40% |', md)


class Check(unittest.TestCase):
    def make(self, d, ledger_rows, fn_overrides, metrics_newer=True, waivers=None):
        mp = os.path.join(d, 'map')
        os.makedirs(mp)
        write_jsonl(os.path.join(mp, 'ledger.jsonl'), ledger_rows)
        fns = [dict({'id': 'f_1', 'name': 'one', 'state': 'closed+sail', 'hyps': [],
                     'nonvacuity': 'X.pre_nonvacuous', 'snapshot': 'X.post_snapshot'},
                    **fn_overrides)]
        with open(os.path.join(mp, 'map.json'), 'w') as f:
            json.dump({'functions': fns}, f)
        with open(os.path.join(mp, 'waivers.json'), 'w') as f:
            json.dump({'pre_revision': [], 'waivers': waivers or {}}, f)
        mt = os.path.join(mp, 'metrics.json')
        with open(mt, 'w') as f:
            f.write('{}')
        t = os.path.getmtime(os.path.join(mp, 'map.json'))
        os.utime(mt, (t + 1, t + 1) if metrics_newer else (t - 1, t - 1))
        return d

    def test_pass(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(metrics.check(self.make(d, [], {})), [])

    def test_failures(self):
        now = cost.parse_ts('2026-01-03T00:00:00Z')
        rows = [{'schema': 2, 'rec': 'start', 'id': 1, 'ts': '2026-01-01T00:00:00Z', 'agent': 'A',
                 'fn': None, 'item': 'x', 'kind': 'infra'},
                {'schema': 2, 'rec': 'start', 'id': 2, 'ts': '2026-01-02T23:00:00Z', 'agent': 'B',
                 'fn': None, 'item': 'y', 'kind': 'infra', 'minutes': 5}]
        with tempfile.TemporaryDirectory() as d:
            fails = metrics.check(self.make(d, rows, {'hyps': [{'name': 'A'}], 'snapshot': None},
                                            metrics_newer=False), now=now)
        text = '\n'.join(fails)
        self.assertIn('ledger item 1', text)
        self.assertNotIn('ledger item 2', text)  # open less than 24 hours
        self.assertIn('typed minutes', text)
        self.assertIn('non-Pre hypotheses: A', text)
        self.assertIn('without a snapshot test', text)
        self.assertIn('older than map/map.json', text)
        self.assertEqual(len(fails), 5)

    def test_waiver_and_assumptions(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(metrics.check(self.make(
                d, [], {'nonvacuity': None, 'snapshot': None},
                waivers={'f_1': ['nonvacuity', 'snapshot']})), [])
        with tempfile.TemporaryDirectory() as d:  # closed on assumptions: not closed
            self.assertEqual(metrics.check(self.make(
                d, [], {'state': 'closed-on-assumptions', 'hyps': [{'name': 'A'}],
                        'nonvacuity': None})), [])


class BuildStat(unittest.TestCase):
    def test_parse_time(self):
        spec = importlib.util.spec_from_file_location(
            'buildstat', os.path.join(PACKAGE, 'tools', 'buildstat.py'))
        bs = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(bs)
        text = ('\tUser time (seconds): 12.50\n\tSystem time (seconds): 1.25\n'
                '\tElapsed (wall clock) time (h:mm:ss or m:ss): 1:02:03.5\n'
                '\tMaximum resident set size (kbytes): 2097152\n')
        self.assertEqual(bs.parse_time(text), {'user_s': 12.5, 'sys_s': 1.25,
                                               'peak_rss_mb': 2048.0, 'wall_s': 3723.5})
        self.assertEqual(bs.wall_seconds('0:07.25'), 7.25)
        mods = bs.modules()
        self.assertTrue(mods and all(m.startswith(bs.DIRS) for m in mods))


if __name__ == '__main__':
    unittest.main()
