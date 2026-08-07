#!/usr/bin/env python3
"""Relocation acceptance test for the deterministic Elfling generator.

Given the canonical `program.json` and a `program.json` regenerated from the SAME sidecars and pinned
source but a linker map for a link at a DIFFERENT text base, this asserts the generator's REQUIREMENT
from the plan ("Verification and Acceptance": relink at a different text base and confirm handwritten
contracts/proofs need no address edits):

  * every address-free identity is byte-identical between the two runs — qualified name, source file,
    validated source hash, declaration line, inline call stack, nesting (parent/children), kind, DWARF
    entry offset, catalog/excluded classification — so `FunctionId`s and the contracts keyed by them
    are unchanged;
  * every generated address (`textBases`, `runtimeFuncBase`, each region start, `entryPc`, `exitPc`)
    shifts by exactly one constant, nonzero segment delta, and region sizes are unchanged.

A generator that folded a linked address into an identity, or that mapped a sidecar range through a
stale/hardcoded base, cannot pass both halves.
"""
import argparse, json, sys

# Identity-bearing occurrence fields: everything EXCEPT the address-bearing ones. `externalCalls` is
# emitted as callee (kind, index) references, which are relocation-stable, so it stays an identity
# field; blocks/edges/exits carry addresses that shift and are checked separately below.
ADDRESS_FIELDS = {"regions", "entryPc", "exitPc", "exits", "blocks", "edges"}


def load(path):
    return json.load(open(path))


def fail(msg):
    print(f"RELOCATION STABILITY FAILURE: {msg}", file=sys.stderr)
    sys.exit(1)


def segment_delta(canon, reloc):
    deltas = set()
    for kind, base in canon["textBases"].items():
        if kind not in reloc["textBases"]:
            fail(f"textBases missing {kind} after relink")
        deltas.add(reloc["textBases"][kind] - base)
    for fn, base in canon["runtimeFuncBase"].items():
        if fn not in reloc["runtimeFuncBase"]:
            fail(f"runtimeFuncBase missing {fn} after relink")
        deltas.add(reloc["runtimeFuncBase"][fn] - base)
    if len(deltas) != 1:
        fail(f"text placement did not shift uniformly; deltas={sorted(deltas)}")
    (delta,) = deltas
    if delta == 0:
        fail("relocated link has the same text base — the relocation test relinked nothing")
    return delta


def check_regions(what, i, cregs, rregs, delta):
    if len(cregs) != len(rregs):
        fail(f"{what}[{i}] region count changed under relocation")
    for j, (c, r) in enumerate(zip(cregs, rregs)):
        if c["size"] != r["size"]:
            fail(f"{what}[{i}] region {j} size changed under relocation")
        if r["start"] - c["start"] != delta:
            fail(f"{what}[{i}] region {j} start shifted by {r['start']-c['start']}, expected {delta}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--canonical", required=True)
    ap.add_argument("--relocated", required=True)
    a = ap.parse_args()
    canon, reloc = load(a.canonical), load(a.relocated)

    delta = segment_delta(canon, reloc)

    for scalar in ("entryIndex", "extractorVersion", "decoderTextSha256", "defects"):
        if canon[scalar] != reloc[scalar]:
            fail(f"{scalar} changed under relocation ({canon[scalar]!r} vs {reloc[scalar]!r})")

    co, ro = canon["function_instances"], reloc["function_instances"]
    if len(co) != len(ro):
        fail(f"occurrence count changed under relocation ({len(co)} vs {len(ro)})")
    for i, (c, r) in enumerate(zip(co, ro)):
        cid = {k: v for k, v in c.items() if k not in ADDRESS_FIELDS}
        rid = {k: v for k, v in r.items() if k not in ADDRESS_FIELDS}
        if cid != rid:
            diff = {k: (cid.get(k), rid.get(k)) for k in set(cid) | set(rid) if cid.get(k) != rid.get(k)}
            fail(f"occurrence[{i}] identity changed under relocation: {diff}")
        if r["entryPc"] - c["entryPc"] != delta:
            fail(f"occurrence[{i}] entryPc shifted by {r['entryPc']-c['entryPc']}, expected {delta}")
        if r["exitPc"] - c["exitPc"] != delta:
            fail(f"occurrence[{i}] exitPc shifted by {r['exitPc']-c['exitPc']}, expected {delta}")
        check_regions("occurrence", i, c["regions"], r["regions"], delta)
        if [e - delta for e in r.get("exits", [])] != c.get("exits", []):
            fail(f"occurrence[{i}] exits did not shift uniformly by {delta}")
        check_regions("occurrence", i, [b["range"] if "range" in b else b for b in c.get("blocks", [])],
                      [b["range"] if "range" in b else b for b in r.get("blocks", [])], delta)
        cedges, redges = c.get("edges", []), r.get("edges", [])
        if len(cedges) != len(redges) or any(
                re_["source"] - ce["source"] != delta or re_["target"] - ce["target"] != delta
                for ce, re_ in zip(cedges, redges)):
            fail(f"occurrence[{i}] edges did not shift uniformly by {delta}")

    ce, re = canon["excludedFunctionInstances"], reloc["excludedFunctionInstances"]
    if len(ce) != len(re):
        fail(f"excluded-function-instance count changed under relocation ({len(ce)} vs {len(re)})")
    for i, (c, r) in enumerate(zip(ce, re)):
        if (c["qualified"], c["category"]) != (r["qualified"], r["category"]):
            fail(f"excluded[{i}] identity/category changed under relocation")
        check_regions("excluded", i, c["regions"], r["regions"], delta)

    print(f"RELOCATION STABILITY OK: text base shifted by {delta:#x}; "
          f"{len(co)} occurrence + {len(ce)} excluded identities byte-stable, "
          f"every address shifted uniformly.")


if __name__ == "__main__":
    main()
