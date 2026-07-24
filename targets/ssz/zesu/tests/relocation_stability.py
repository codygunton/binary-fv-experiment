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

# Identity-bearing function instance fields: everything EXCEPT the address-bearing ones. `externalCalls` is
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

    canonical_function_instances = canon["function_instances"]
    relocated_function_instances = reloc["function_instances"]
    if len(canonical_function_instances) != len(relocated_function_instances):
        fail("function instance count changed under relocation "
             f"({len(canonical_function_instances)} vs {len(relocated_function_instances)})")
    for i, (canonical_function_instance, relocated_function_instance) in enumerate(
            zip(canonical_function_instances, relocated_function_instances)):
        canonical_identity = {
            k: v for k, v in canonical_function_instance.items() if k not in ADDRESS_FIELDS
        }
        relocated_identity = {
            k: v for k, v in relocated_function_instance.items() if k not in ADDRESS_FIELDS
        }
        if canonical_identity != relocated_identity:
            diff = {
                k: (canonical_identity.get(k), relocated_identity.get(k))
                for k in set(canonical_identity) | set(relocated_identity)
                if canonical_identity.get(k) != relocated_identity.get(k)
            }
            fail(f"function instance[{i}] identity changed under relocation: {diff}")
        if relocated_function_instance["entryPc"] - canonical_function_instance["entryPc"] != delta:
            fail(f"function instance[{i}] entryPc shifted by "
                 f"{relocated_function_instance['entryPc']-canonical_function_instance['entryPc']}, "
                 f"expected {delta}")
        if relocated_function_instance["exitPc"] - canonical_function_instance["exitPc"] != delta:
            fail(f"function instance[{i}] exitPc shifted by "
                 f"{relocated_function_instance['exitPc']-canonical_function_instance['exitPc']}, "
                 f"expected {delta}")
        check_regions("function instance", i, canonical_function_instance["regions"],
                      relocated_function_instance["regions"], delta)
        if ([e - delta for e in relocated_function_instance.get("exits", [])]
                != canonical_function_instance.get("exits", [])):
            fail(f"function instance[{i}] exits did not shift uniformly by {delta}")
        check_regions(
            "function instance", i,
            [b["range"] if "range" in b else b
             for b in canonical_function_instance.get("blocks", [])],
            [b["range"] if "range" in b else b
             for b in relocated_function_instance.get("blocks", [])],
            delta)
        cedges = canonical_function_instance.get("edges", [])
        redges = relocated_function_instance.get("edges", [])
        if len(cedges) != len(redges) or any(
                re_["source"] - ce["source"] != delta or re_["target"] - ce["target"] != delta
                for ce, re_ in zip(cedges, redges)):
            fail(f"function instance[{i}] edges did not shift uniformly by {delta}")

    ce, re = canon["excludedRoutines"], reloc["excludedRoutines"]
    if len(ce) != len(re):
        fail(f"excluded-routine count changed under relocation ({len(ce)} vs {len(re)})")
    for i, (c, r) in enumerate(zip(ce, re)):
        if (c["qualified"], c["category"]) != (r["qualified"], r["category"]):
            fail(f"excluded[{i}] identity/category changed under relocation")
        check_regions("excluded", i, c["regions"], r["regions"], delta)

    print(f"RELOCATION STABILITY OK: text base shifted by {delta:#x}; "
          f"{len(canonical_function_instances)} function instance + {len(ce)} excluded identities byte-stable, "
          f"every address shifted uniformly.")


if __name__ == "__main__":
    main()
