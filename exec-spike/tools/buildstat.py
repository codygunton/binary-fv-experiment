#!/usr/bin/env python3
"""Per-module build measurements (programme plan S10.3).

After a full `lake build`, compiles every module under `ZesuExec/Fn/`, `ZesuExec/Compliance/` and
`ZesuExec/Sail/` again with `time -v lake env lean <file>`, 16 at a time, and writes wall
seconds, user and system CPU seconds and peak resident memory per module to `map/build.json`.
Run from anywhere: `tools/buildstat.py [--no-build] [-j N] [--only REGEX]`. Run at each merge
that changes Lean files. GNU time: the one `tools/verify.sh` uses, else `/usr/bin/time`.
"""
import argparse
import concurrent.futures
import datetime
import json
import os
import re
import subprocess
import sys
import time

P = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIRS = ('ZesuExec/Fn', 'ZesuExec/Compliance', 'ZesuExec/Sail')
GTIME = ('/home/cody/.cache/zesu-tmp/exec-spike/gtime/bin/time', '/usr/bin/time')
FIELDS = {'user_s': r'User time \(seconds\): ([\d.]+)',
          'sys_s': r'System time \(seconds\): ([\d.]+)',
          'peak_rss_kb': r'Maximum resident set size \(kbytes\): (\d+)',
          'wall': r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)'}


def modules(only=None):
    out = []
    for d in DIRS:
        for root, _, files in os.walk(os.path.join(P, d)):
            for f in files:
                if f.endswith('.lean'):
                    rel = os.path.relpath(os.path.join(root, f), P)
                    if only is None or re.search(only, rel):
                        out.append(rel)
    return sorted(out)


def wall_seconds(s):
    """`h:mm:ss` or `m:ss.ss` to seconds."""
    sec = 0.0
    for part in s.split(':'):
        sec = sec * 60 + float(part)
    return sec


def parse_time(text):
    """GNU `time -v` report to {user_s, sys_s, peak_rss_mb, wall_s}."""
    got = {}
    for k, rx in FIELDS.items():
        m = re.search(rx, text)
        if m:
            got[k] = m.group(1)
    out = {}
    if 'user_s' in got:
        out['user_s'] = float(got['user_s'])
    if 'sys_s' in got:
        out['sys_s'] = float(got['sys_s'])
    if 'peak_rss_kb' in got:
        out['peak_rss_mb'] = round(int(got['peak_rss_kb']) / 1024, 1)
    if 'wall' in got:
        out['wall_s'] = round(wall_seconds(got['wall']), 2)
    return out


def measure(gtime, rel):
    t0 = time.time()
    r = subprocess.run([gtime, '-v', 'lake', 'env', 'lean', rel], cwd=P, capture_output=True,
                       text=True)
    row = {'module': rel, 'ok': r.returncode == 0}
    row.update(parse_time(r.stderr))
    row.setdefault('wall_s', round(time.time() - t0, 2))
    if r.returncode != 0:
        row['error'] = (r.stdout + r.stderr).strip().splitlines()[:3]
    return row


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('--no-build', action='store_true', help='skip the full lake build first')
    ap.add_argument('-j', type=int, default=16)
    ap.add_argument('--only', help='regex on module paths')
    ap.add_argument('--out', default=os.path.join(P, 'map', 'build.json'))
    a = ap.parse_args(argv)
    gtime = next((g for g in GTIME if os.access(g, os.X_OK)), None)
    if gtime is None:
        sys.exit('buildstat: no GNU time at ' + ' or '.join(GTIME))
    if not a.no_build:
        subprocess.run(['lake', 'build'], cwd=P, check=True)
    mods = modules(a.only)
    with concurrent.futures.ThreadPoolExecutor(a.j) as ex:
        rows = list(ex.map(lambda m: measure(gtime, m), mods))
    commit = subprocess.run(['git', '-C', P, 'rev-parse', 'HEAD'], capture_output=True,
                            text=True).stdout.strip() or None
    out = {'schema': 'zmap.build.v1', 'commit': commit, 'jobs': a.j,
           'generated': datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
           'modules': rows}
    with open(a.out, 'w') as f:
        json.dump(out, f, indent=1)
        f.write('\n')
    bad = [r['module'] for r in rows if not r['ok']]
    print(f'buildstat: {len(rows)} modules, wall {sum(r["wall_s"] for r in rows):.0f} s, '
          f'cpu {sum(r.get("user_s", 0) for r in rows):.0f} s, '
          f'peak {max((r.get("peak_rss_mb", 0) for r in rows), default=0):.0f} MB, '
          f'{len(bad)} failed -> {a.out}')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
