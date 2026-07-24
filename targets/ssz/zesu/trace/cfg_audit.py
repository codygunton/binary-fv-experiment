#!/usr/bin/env python3
"""Row C: audit the generated per-function_instance CFG (`edges` / `exits`) against the TRUE control transfers
decoded from the UNCHANGED production ELF disassembly.

For every function_instance this decodes each in-block instruction's real successors (conditional branches ->
taken target + fallthrough; `j`/`jal` -> target (+ return site); `jalr`/`ret` -> indirect/return) and
compares that ground truth to the function_instance's declared `edges`. It reports, per function_instance:

  missingInternal   a real transfer whose SOURCE and TARGET are both inside the function_instance's blocks but
                    which is absent from `edges` — a genuine hole in the generated CFG;
  declaredNotReal   a declared edge that is not a real successor of its source instruction;
  exitsOk           whether every real transfer leaving the function_instance's blocks has its source in `exits`.

This exists because the scaled validator must check the EXACT generated edges, not merely that transfer
targets land on block starts. Where the generated data is wrong, the extractor is the thing to repair —
the validator must not be weakened to accommodate it. Diagnostic-only; never imported by the proof.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
# The direct-vs-dynamic transfer rule is shared with the scaled checker and mirrors the extractor:
# objdump's `#` comment alone does NOT make a `jalr` direct (it prints one for a bare `jalr a5` too).
from riscv_transfers import COND, RET, disassemble, resolved_target  # noqa: E402

UNCOND = {"j", "jr"}
CALL = {"jal", "jalr"}


def target_of(ops: str):
    """The last operand as an absolute hex address, if it is one. objdump renders a resolved branch
    target as `11bb8 <zesu_decode_raw+0x1908>`, so the trailing `<symbol+offset>` must be stripped."""
    ops = re.sub(r"<[^>]*>", "", ops).strip()
    parts = [p.strip() for p in ops.split(",")]
    if not parts:
        return None
    m = re.match(r"^([0-9a-f]+)$", parts[-1])
    return int(m.group(1), 16) if m else None


def successors(addr: int, op: str, ops: str, next_addr: int | None, direct=None):
    """Real successors of one instruction: (list_of_targets, indirect_flag).

    `direct` is `riscv_transfers.resolved_target(addr, insns)` — the target of an `auipc`+`jalr`/`jr`
    long-range DIRECT call, or None when the transfer is genuinely dynamic."""
    if op in RET:
        return [], True
    if op in COND:
        t = target_of(ops)
        s = [next_addr] if next_addr is not None else []
        if t is not None:
            s = s + [t]
        return s, False
    if op == "j":
        t = target_of(ops)
        return ([t] if t is not None else []), t is None
    if op == "jal":
        t = target_of(ops) if target_of(ops) is not None else direct
        return ([t] if t is not None else []), t is None
    if op in ("jr", "jalr"):
        # Direct ONLY for the auipc+jalr pair; a bare `jalr rs` is indirect however objdump renders it.
        if direct is None:
            return [], True
        # `jalr` writes ra, so a resolved one is a CALL and also reaches its return site — the
        # generator declares both edges. `jr` writes x0: a tail jump, with no fall-through.
        if op == "jalr":
            return [x for x in [direct, next_addr] if x is not None], False
        return [direct], False
    return ([next_addr] if next_addr is not None else []), False


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--objdump", required=True)
    ap.add_argument("--elf", required=True)
    ap.add_argument("--program", required=True)
    ap.add_argument("--out-json", required=True)
    a = ap.parse_args()

    insns, order = disassemble(a.objdump, a.elf)
    nxt = {addr: order[i + 1] for i, addr in enumerate(order) if i + 1 < len(order)}
    function_instances = json.loads(Path(a.program).read_text())["function_instances"]

    # The generator attributes each PC's edges to the DEEPEST function instance owning it
    # (`owned = regions - children's regions`), so an edge appears exactly once across an inline chain.
    # The audit must use the same ownership, otherwise a parent looks "incomplete" for edges that are
    # correctly attributed to its inlined children.
    def region_pcs(o):
        s = set()
        for r in o["regions"]:
            s |= set(range(r["start"], r["start"] + r["size"], 2))
        return s

    rpcs = [region_pcs(o) for o in function_instances]

    report = []
    tot_missing = tot_bogus = tot_exitbad = 0
    for i, o in enumerate(function_instances):
        children = set()
        for c in o["children"]:
            children |= rpcs[c]
        owned = rpcs[i] - children
        region = rpcs[i]
        declared = {(e["source"], e["target"]) for e in o["edges"]}
        exits = set(o.get("exits") or [])
        real, indirect_sites = set(), []
        for pc in sorted(owned):
            if pc not in insns:
                continue
            op, ops, _ = insns[pc]
            succ, indirect = successors(pc, op, ops, nxt.get(pc), resolved_target(pc, insns))
            if indirect:
                indirect_sites.append(pc)
            for t in succ:
                if t is not None:
                    real.add((pc, t))
        missing = sorted(e for e in real if e not in declared)
        bogus = sorted(e for e in declared if e not in real)
        # every real transfer leaving the function instance's own regions must have its source in `exits`
        leaving_src = {pc for (pc, t) in real if t not in region}
        exit_bad = sorted(leaving_src - exits)
        tot_missing += len(missing); tot_bogus += len(bogus); tot_exitbad += len(exit_bad)
        report.append({
            "index": i, "qualified": o["qualified"],
            "realOwned": len(real), "declared": len(declared),
            "missingInternal": missing[:20], "missingCount": len(missing),
            "declaredNotReal": bogus[:20], "declaredNotRealCount": len(bogus),
            "leavingSourcesNotInExits": exit_bad[:20], "indirectSites": len(indirect_sites),
        })

    out = {
        "summary": {
            "function_instances": len(function_instances),
            "function_instancesWithMissingInternalEdges": sum(1 for r in report if r["missingCount"]),
            "totalMissingInternalEdges": tot_missing,
            "function_instancesWithDeclaredNotReal": sum(1 for r in report if r["declaredNotRealCount"]),
            "totalDeclaredNotReal": tot_bogus,
            "totalLeavingSourcesNotInExits": tot_exitbad,
        },
        "function_instances": report,
    }
    Path(a.out_json).write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    s = out["summary"]
    print(f"function_instances={s['function_instances']}")
    print(f"  with MISSING internal edges: {s['function_instancesWithMissingInternalEdges']} "
          f"(total {s['totalMissingInternalEdges']})")
    print(f"  with declared-but-not-real edges: {s['function_instancesWithDeclaredNotReal']} "
          f"(total {s['totalDeclaredNotReal']})")
    print(f"  leaving-transfer sources absent from `exits`: {s['totalLeavingSourcesNotInExits']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
