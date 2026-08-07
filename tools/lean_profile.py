#!/usr/bin/env python3
"""Capture, merge and serve Lean's official profiler output for this project.

Lean emits a Firefox Profiler JSON per `lean` process when given
`-Dtrace.profiler=true -Dtrace.profiler.output=<file>.json`, and Lake runs one process per module,
so a build-wide profile does not exist natively. This script captures one file per module, merges
them into a single profile, and serves them to profiler.firefox.com.

    tools/lean_profile.py capture   # per-module profiles for every module over --threshold seconds
    tools/lean_profile.py merge     # combine them into one whole-project profile
    tools/lean_profile.py serve     # browse and open them in profiler.firefox.com

Read the merged profile with the **inverted call stack**, which ranks by self time. Do not sum the
nested totals: they are inclusive, and summing them is how you conclude that a 39 s module contains
twenty declarations of 30 s each. The same caution applies to the text output of
`-Dtrace.profiler=true`.

Two limits of the format, both worth knowing before you trust a number:

* Frames are trace classes (`Kernel`, `Elab.step: …simpAll`, `addDecl`), not declaration names, so
  the file cannot attribute cost to a declaration. Per-declaration timings come from the text trace,
  where they overlap.
* The samples are synthesised from Lean's trace tree rather than sampled by a profiler, so the
  weights inherit that same inclusive-overlap problem. Proportions inform; absolute totals do not.

And `-Dprofiler=true` (no `trace.`) is a different, useless option here: it prints
`type checking took 313s` with no declaration name and no source position.
"""
from __future__ import annotations

import argparse
import copy
import glob
import gzip
import http.server
import json
import os
import posixpath
import re
import socketserver
import subprocess
import sys
import urllib.parse
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_OUT = os.path.join(ROOT, ".lake", "profiles")
BUILT = re.compile(r"Built (\S+) \(([0-9.]+)(m?s)\)")


def module_times(build_log: str | None) -> dict[str, float]:
    """Per-module wall times, from a `lake build` log (or by running one)."""
    if build_log:
        text = open(build_log).read()
    else:
        print("  running `lake build` to collect module times …", file=sys.stderr)
        text = subprocess.run(["lake", "build", "BinaryFv"], cwd=ROOT,
                              capture_output=True, text=True).stdout
    out: dict[str, float] = {}
    for m in BUILT.finditer(text):
        t = float(m.group(2))
        out[m.group(1)] = t / 1000 if m.group(3) == "ms" else t
    return out


def cmd_capture(a: argparse.Namespace) -> None:
    os.makedirs(a.out, exist_ok=True)
    times = module_times(a.build_log)
    targets = [(m, t) for m, t in times.items() if t >= a.threshold]
    targets.sort(key=lambda x: -x[1])
    print(f"  {len(targets)} modules over {a.threshold}s (of {len(times)})")

    def one(item: tuple[str, float]) -> tuple[str, bool]:
        mod, _ = item
        src = os.path.join(ROOT, mod.replace(".", "/") + ".lean")
        if not os.path.exists(src):
            return mod, False
        dst = os.path.join(a.out, mod + ".json")
        r = subprocess.run(
            ["lake", "env", "lean", "--tstack=65536", "-Dtrace.profiler=true",
             f"-Dtrace.profiler.output={dst}", src],
            cwd=ROOT, capture_output=True, text=True)
        # a module can stack-overflow with tracing on while building fine without it
        return mod, os.path.exists(dst) and r.returncode == 0

    with ThreadPoolExecutor(max_workers=a.jobs) as ex:
        results = list(ex.map(one, targets))
    ok = [m for m, good in results if good]
    bad = [m for m, good in results if not good]
    print(f"  captured {len(ok)} profiles into {a.out}")
    for m in bad:
        print(f"    FAILED (often a stack overflow under tracing): {m}")


def cmd_report(a: argparse.Namespace) -> None:
    """Write stable Markdown from Lake's per-module timing lines."""
    times = module_times(a.build_log)
    ranked = sorted(times.items(), key=lambda item: (-item[1], item[0]))
    total = sum(times.values())
    print("<!-- binary-fv-lean-profile -->")
    print("Lean build profile: "
          f"**{len(times)} modules, {total:.1f}s aggregate module time**.")
    print("")
    print("| Slowest module | Time |")
    print("|---|---:|")
    for module, seconds in ranked[:a.limit]:
        print(f"| `{module}` | {seconds:.1f}s |")


def cmd_merge(a: argparse.Namespace) -> None:
    files = sorted(f for f in glob.glob(os.path.join(a.out, "*.json"))
                   if os.path.basename(f) not in ("merged.json", "index.json"))
    profs = []
    for f in files:
        try:
            profs.append((os.path.basename(f)[:-5], json.load(open(f))))
        except Exception as e:                                    # truncated / failed capture
            print(f"    skipping {os.path.basename(f)}: {e}")
    if not profs:
        sys.exit("no profiles to merge; run `capture` first")

    t0 = min(p["meta"]["startTime"] for _, p in profs)
    out = {"libs": profs[0][1].get("libs", []),
           "meta": copy.deepcopy(profs[0][1]["meta"]),
           "threads": []}
    out["meta"]["startTime"] = t0
    out["meta"]["product"] = f"lean — {os.path.basename(ROOT)} ({len(profs)} modules)"
    tid = 0
    for pid, (mod, p) in enumerate(profs):
        delta = p["meta"]["startTime"] - t0
        short = mod.replace("BinaryFv.", "")
        for i, th in enumerate(p["threads"]):
            th = copy.deepcopy(th)
            s = th.get("samples")
            if s and s.get("length"):
                s["time"] = [x + delta for x in s["time"]]
            named = th.get("name") and not str(th["name"]).isdigit()
            th.update(pid=str(pid), tid=tid, processName=short,
                      name=short if named else f"{short} ·w{i}",
                      isMainThread=bool(named),
                      processStartupTime=delta, registerTime=delta)
            tid += 1
            out["threads"].append(th)
    dst = os.path.join(a.out, "merged.json")
    json.dump(out, open(dst, "w"))
    n = sum(t["samples"]["length"] for t in out["threads"] if "samples" in t)
    print(f"  merged {len(profs)} modules, {len(out['threads'])} threads, {n:,} samples "
          f"-> {dst} ({os.path.getsize(dst)/1e6:.1f} MB)")
    print("  NOTE: the horizontal timeline is when each module was elaborated during the capture "
          "run,\n        not Lake's real build schedule. Sample data and durations are Lean's; only "
          "the\n        placement of modules relative to each other comes from the capture.")


INDEX = """<!doctype html><meta charset=utf-8><title>Lean build profile</title>
<style>
:root{--bg:#fff;--fg:#111;--dim:#666;--line:#e5e5e5;--bar:#3b82f6;--card:#fafafa;--acc:#8b5cf6}
@media(prefers-color-scheme:dark){:root{--bg:#0f1115;--fg:#e8e8ea;--dim:#8b8f98;--line:#242833;--card:#161922}}
*{box-sizing:border-box}
body{margin:0;padding:30px 20px 60px;background:var(--bg);color:var(--fg);max-width:1000px;
margin-inline:auto;font:14px/1.55 ui-sans-serif,-apple-system,"Segoe UI",Roboto,sans-serif}
h1{font-size:21px;margin:0 0 6px} p{color:var(--dim);font-size:13px;max-width:82ch}
code{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:12px}
.hero{background:var(--card);border:1px solid var(--acc);border-radius:10px;padding:16px 18px;margin:18px 0}
.btn{display:inline-block;background:var(--acc);color:#fff;border:0;border-radius:7px;padding:9px 15px;
font:inherit;font-size:13px;font-weight:600;cursor:pointer;text-decoration:none;margin-right:8px}
.btn.sec{background:transparent;color:var(--fg);border:1px solid var(--line);font-weight:400}
ul{list-style:none;padding:0;margin:12px 0 0}
li{display:grid;grid-template-columns:minmax(0,1fr) 170px 48px 42px;gap:10px;align-items:center;
padding:2px 0;border-bottom:1px solid var(--line)}
button.open{all:unset;cursor:pointer;overflow:hidden}
.nm{font-family:ui-monospace,monospace;font-size:11.5px;overflow:hidden;text-overflow:ellipsis;
white-space:nowrap;display:block}
button.open:hover .nm{color:var(--bar);text-decoration:underline}
.bar{background:var(--line);border-radius:3px;height:11px;overflow:hidden}
.bar i{display:block;height:100%;background:var(--bar)}
.v{text-align:right;font-variant-numeric:tabular-nums;font-size:11.5px;color:var(--dim)}
.raw{font-size:11px;color:var(--dim);text-align:right;text-decoration:none}
.note{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:12px 14px;
margin:14px 0;font-size:13px}
#status{position:fixed;left:50%;transform:translateX(-50%);bottom:22px;background:var(--card);
border:1px solid var(--line);border-radius:8px;padding:9px 15px;font-size:13px;
box-shadow:0 4px 18px #0004;display:none}
#status.on{display:block}
</style>
<h1>Lean build profile <span style="color:var(--dim);font-weight:400">— official Firefox Profiler format</span></h1>
<p>Emitted by <code>lean -Dtrace.profiler=true -Dtrace.profiler.output=&lt;file&gt;.json</code>, one
file per module. Bars are Lake's wall time.</p>
__HERO__
<div class="note"><b>Click a module</b> to open it in profiler.firefox.com. This page fetches the JSON
and hands it over by <code>postMessage</code> — the profiler cannot fetch an <code>http://</code> URL
from its <code>https://</code> page (mixed content), so a <code>from-url</code> link cannot work.
If a popup is blocked, use the <b>json</b> link and drag the file onto profiler.firefox.com.<br><br>
Use the <b>inverted call stack</b> to rank by self time. Nested totals are inclusive.</div>
<ul>__ITEMS__</ul>
<div id="status"></div>
<script>
const PROF='https://profiler.firefox.com';
const s=document.getElementById('status');
const say=(m,ms)=>{s.textContent=m;s.className='on';if(ms)setTimeout(()=>s.className='',ms);};
// Protocol (firefox-devtools/profiler, docs-developer/loading-in-profiles.md):
//   injector -> profiler : {name:'ready:request'}   -- must POLL; the tab may not be up yet
//   profiler -> injector : {name:'ready:response'}
//   injector -> profiler : {name:'inject-profile', profile}
async function open_(file){
  say('fetching '+file+' \\u2026');
  let profile;
  try{const r=await fetch(file); if(!r.ok) throw new Error('HTTP '+r.status); profile=await r.json();}
  catch(e){say('could not read '+file+': '+e.message,7000);return;}
  const win=window.open(PROF+'/from-post-message/','_blank');
  if(!win){say('popup blocked \\u2014 allow popups, or use the json link',8000);return;}
  say('handshaking with profiler.firefox.com \\u2026');
  let ready=false,sent=false;
  const listener=({origin,data})=>{
    if(origin!==PROF||!data)return;
    if(data.name==='ready:response'&&!sent){ready=true;sent=true;
      win.postMessage({name:'inject-profile',profile},PROF);say('profile sent',4000);}
    else if(data.name==='error'){say('profiler rejected it: '+(data.error||'unknown'),9000);
      window.removeEventListener('message',listener);}
  };
  window.addEventListener('message',listener);
  for(let i=0;i<150&&!ready;i++){
    try{win.postMessage({name:'ready:request'},PROF);}catch(e){}
    await new Promise(r=>setTimeout(r,100));
  }
  if(!ready){window.removeEventListener('message',listener);
    say('profiler never answered \\u2014 download the json and drag it in',9000);}
}
const merged=document.getElementById('mergedOpen');
if(merged) merged.addEventListener('click',()=>open_('merged.json'));
for(const b of document.querySelectorAll('button.open'))
  b.addEventListener('click',()=>open_(b.dataset.f));
</script>"""


def write_index(out: str, times: dict[str, float]) -> None:
    rows = []
    for f in sorted(glob.glob(os.path.join(out, "*.json"))):
        base = os.path.basename(f)[:-5]
        if base in ("merged", "index"):
            continue
        gz = f + ".gz"
        rows.append((times.get(base, 0.0), base,
                     round(os.path.getsize(gz if os.path.exists(gz) else f) / 1024)))
    rows.sort(key=lambda r: -r[0])
    mx = max([r[0] for r in rows], default=1) or 1
    items = "".join(
        f'<li><button class="open" data-f="{b}.json"><span class="nm">'
        f'{b.replace("BinaryFv.", "")}</span></button>'
        f'<span class="bar"><i style="width:{100*t/mx:.1f}%"></i></span>'
        f'<span class="v">{t:g}s</span>'
        f'<a class="raw" href="{b}.json" download>json</a></li>' for t, b, _ in rows)
    merged = os.path.join(out, "merged.json")
    hero = ""
    if os.path.exists(merged):
        mb = os.path.getsize(merged) / 1e6
        gz = merged + ".gz"
        gzs = f" ({os.path.getsize(gz)/1e6:.1f} MB gzipped)" if os.path.exists(gz) else ""
        hero = (f'<div class="hero"><h2 style="margin:0 0 4px;font-size:16px">Whole project — one '
                f'profile</h2><p>{len(rows)} modules · {mb:.1f} MB{gzs}. For a file this size, '
                f'<b>download and drag it onto profiler.firefox.com</b> — most reliable.</p>'
                f'<a class="btn" href="merged.json" download>Download merged.json</a>'
                f'<button class="btn sec" id="mergedOpen">Try opening directly</button></div>')
    html = INDEX.replace("__ITEMS__", items).replace("__HERO__", hero)
    open(os.path.join(out, "index.html"), "w").write(html)


class Handler(http.server.SimpleHTTPRequestHandler):
    """Serves a pre-made `<file>.json.gz` when `<file>.json` is asked for, with CORS."""
    directory_override = DEFAULT_OUT

    def __init__(self, *a, **kw):
        super().__init__(*a, directory=self.directory_override, **kw)

    def end_headers(self):
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def do_OPTIONS(self):
        self.send_response(204)
        self.end_headers()

    def do_GET(self):
        name = urllib.parse.unquote(posixpath.basename(urllib.parse.urlparse(self.path).path))
        gz = os.path.join(self.directory_override, name + ".gz")
        if name.endswith(".json") and os.path.exists(gz) \
                and "gzip" in self.headers.get("Accept-Encoding", ""):
            data = open(gz, "rb").read()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Encoding", "gzip")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)
            return
        super().do_GET()

    def log_message(self, *a):
        pass


def cmd_serve(a: argparse.Namespace) -> None:
    for f in glob.glob(os.path.join(a.out, "*.json")):                 # gzip: 21 MB -> 3.6 MB
        gz = f + ".gz"
        if not os.path.exists(gz) or os.path.getmtime(gz) < os.path.getmtime(f):
            with open(f, "rb") as src, gzip.open(gz, "wb") as dst:
                dst.writelines(src)
    write_index(a.out, module_times(a.build_log) if a.build_log else {})
    Handler.directory_override = a.out
    socketserver.TCPServer.allow_reuse_address = True
    print(f"  serving {a.out} at http://0.0.0.0:{a.port}/")
    with socketserver.TCPServer(("0.0.0.0", a.port), Handler) as httpd:
        httpd.serve_forever()


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--out", default=DEFAULT_OUT, help="profile directory")
    p.add_argument("--build-log", help="a saved `lake build` log to read module times from")
    sub = p.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("capture", help="one profile per module")
    c.add_argument("--threshold", type=float, default=1.5, help="skip modules faster than this")
    c.add_argument("--jobs", type=int, default=8)
    c.set_defaults(func=cmd_capture)
    r = sub.add_parser("report", help="Markdown summary of Lake module timings")
    r.add_argument("--limit", type=int, default=10)
    r.set_defaults(func=cmd_report)
    sub.add_parser("merge", help="combine into one profile").set_defaults(func=cmd_merge)
    s = sub.add_parser("serve", help="browse and open in profiler.firefox.com")
    s.add_argument("--port", type=int, default=7613)
    s.set_defaults(func=cmd_serve)
    a = p.parse_args()
    a.func(a)


if __name__ == "__main__":
    main()
