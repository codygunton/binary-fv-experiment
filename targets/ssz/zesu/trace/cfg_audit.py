#!/usr/bin/env python3
"""Row C: audit the generated per-function-instance CFG (`edges` / `exits`) against the TRUE control transfers
decoded from the UNCHANGED production ELF disassembly.

For every function instance this decodes each in-block instruction's real successors (conditional branches ->
taken target + fallthrough; `j`/`jal` -> target (+ return site); `jalr`/`ret` -> indirect/return) and
compares that ground truth to the function instance's declared `edges`. It reports, per function_instance:

  missingInternal   a real transfer whose SOURCE and TARGET are both inside the function instance's blocks but
                    which is absent from `edges` — a genuine hole in the generated CFG;
  declaredNotReal   a declared edge that is not a real successor of its source instruction;
  leavingSourcesNotInExits  a region PC that really leaves the function instance but is absent from `exits`;
  declaredNotLeaving        a declared exit that does NOT leave — the over-declaration direction.

`exits` and `edges` are computed from DIFFERENT successor sets, and this audit must keep them apart.
An edge is a direct successor; an exit is a CONTINUATION — where control goes and STAYS. A resolved
call has both successors `[callee, pc + 4]` (two declared edges) and the single continuation `pc + 4`,
so a call site is an exit only in tail position. That rule lives once, in
`riscv_transfers.leaves_region`, mirroring the extractor and Lean's `leavesFunctionInstance`; this
audit re-derives it from the disassembly and compares it to the generated `exits` in BOTH directions,
so neither under- nor OVER-declared exits can survive. (Over-declaration is not cosmetic: an exit at
every call site is what made the entry function instance's `FunctionTrace` stop at its first call.)

This exists because the scaled validator must check the EXACT generated edges, not merely that transfer
targets land on block starts. Where the generated data is wrong, the extractor is the thing to repair —
the validator must not be weakened to accommodate it. Diagnostic-only; never imported by the proof.
Exits non-zero on any defect, so it gates on its own rather than relying on its caller to read the JSON.
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
from riscv_transfers import COND, RET, disassemble, leaves_region, resolved_target  # noqa: E402

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
    def region_pcs(function_instance):
        s = set()
        for r in function_instance["regions"]:
            s |= set(range(r["start"], r["start"] + r["size"], 2))
        return s

    rpcs = [region_pcs(function_instance) for function_instance in function_instances]

    report = []
    tot_missing = tot_bogus = tot_exitbad = tot_overdeclared = 0
    for i, function_instance in enumerate(function_instances):
        children = set()
        for c in function_instance["children"]:
            children |= rpcs[c]
        owned = rpcs[i] - children
        region = rpcs[i]
        declared = {(e["source"], e["target"]) for e in function_instance["edges"]}
        exits = set(function_instance.get("exits") or [])
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
        # `exits` is re-derived from the disassembly by the SHARED continuation rule and compared in
        # both directions. The domain is the whole region, not just the owned PCs: the extractor
        # declares an exit for every region PC that leaves, child-owned ones included.
        really_leaves = {pc for pc in sorted(region)
                         if pc in insns and leaves_region(pc, insns, region.__contains__, nxt.get(pc))}
        exit_bad = sorted(really_leaves - exits)             # under-declared: a real departure is not an exit
        over_declared = sorted(exits - really_leaves)        # over-declared: an exit that does not leave
        tot_missing += len(missing); tot_bogus += len(bogus)
        tot_exitbad += len(exit_bad); tot_overdeclared += len(over_declared)
        report.append({
            "index": i, "qualified": function_instance["qualified"],
            "realOwned": len(real), "declared": len(declared),
            "missingInternal": missing[:20], "missingCount": len(missing),
            "declaredNotReal": bogus[:20], "declaredNotRealCount": len(bogus),
            "leavingSourcesNotInExits": exit_bad[:20], "indirectSites": len(indirect_sites),
            "declaredNotLeaving": over_declared[:20], "declaredNotLeavingCount": len(over_declared),
            "exitsDeclared": len(exits), "exitsReal": len(really_leaves),
        })

    out = {
        "summary": {
            "function_instances": len(function_instances),
            "function_instancesWithMissingInternalEdges": sum(1 for r in report if r["missingCount"]),
            "totalMissingInternalEdges": tot_missing,
            "function_instancesWithDeclaredNotReal": sum(1 for r in report if r["declaredNotRealCount"]),
            "totalDeclaredNotReal": tot_bogus,
            "totalLeavingSourcesNotInExits": tot_exitbad,
            "totalDeclaredNotLeaving": tot_overdeclared,
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
    print(f"  declared exits that do NOT leave: {s['totalDeclaredNotLeaving']}")
    # Gate here rather than leaving it to whoever reads the JSON: an over-declared exit (every call
    # site, say) is exactly the defect this audit exists to stop, and it must not pass silently.
    return 1 if (tot_missing or tot_bogus or tot_exitbad or tot_overdeclared) else 0


if __name__ == "__main__":
    raise SystemExit(main())
