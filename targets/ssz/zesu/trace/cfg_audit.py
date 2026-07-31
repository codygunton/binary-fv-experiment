#!/usr/bin/env python3
"""Row C: audit the generated per-occurrence CFG (`edges` / `exits`) against the TRUE control transfers
decoded from the UNCHANGED production ELF disassembly.

For every occurrence this decodes each in-block instruction's real successors (conditional branches ->
taken target + fallthrough; `j`/`jal` -> target (+ return site); `jalr`/`ret` -> indirect/return) and
compares that ground truth to the occurrence's declared `edges`. It reports, per occurrence:

  missingInternal   a real transfer whose SOURCE and TARGET are both inside the occurrence's blocks but
                    which is absent from `edges` — a genuine hole in the generated CFG;
  declaredNotReal   a declared edge that is not a real successor of its source instruction;
  exitsOk           whether every real transfer leaving the occurrence's blocks has its source in `exits`.

This exists because the scaled validator must check the EXACT generated edges, not merely that transfer
targets land on block starts. Where the generated data is wrong, the extractor is the thing to repair —
the validator must not be weakened to accommodate it. Diagnostic-only; never imported by the proof.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path

COND = {"beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "bgez", "blez", "bgtz", "bltz",
        "bgt", "ble", "bgtu", "bleu"}
UNCOND = {"j", "jr"}
CALL = {"jal", "jalr"}
RET = {"ret", "mret", "sret"}


def disassemble(objdump: str, elf: str):
    out = subprocess.run([objdump, "-d", "--no-show-raw-insn", elf],
                         capture_output=True, text=True, check=True).stdout
    insns = {}
    order = []
    for ln in out.splitlines():
        m = re.match(r"\s*([0-9a-f]+):\s+(\S+)\s*([^#]*)(#.*)?$", ln)
        if m:
            a = int(m.group(1), 16)
            ops = m.group(3).strip().rstrip(",")
            # objdump resolves `jalr N(ra)`-style long-range DIRECT calls in a trailing comment
            # (`# 13eb8 <memcpy>`); keep it so those targets are decoded rather than treated as indirect.
            resolved = None
            if m.group(4):
                r = re.search(r"#\s*([0-9a-f]+)", m.group(4))
                if r:
                    resolved = int(r.group(1), 16)
            insns[a] = (m.group(2), ops, resolved)
            order.append(a)
    return insns, order


def target_of(ops: str):
    """The last operand as an absolute hex address, if it is one. objdump renders a resolved branch
    target as `11bb8 <zesu_decode_raw+0x1908>`, so the trailing `<symbol+offset>` must be stripped."""
    ops = re.sub(r"<[^>]*>", "", ops).strip()
    parts = [p.strip() for p in ops.split(",")]
    if not parts:
        return None
    m = re.match(r"^([0-9a-f]+)$", parts[-1])
    return int(m.group(1), 16) if m else None


def successors(addr: int, op: str, ops: str, next_addr: int | None, resolved=None):
    """Real successors of one instruction: (list_of_targets, indirect_flag)."""
    if op in RET:
        return [], True
    if op in COND:
        t = target_of(ops)
        s = [next_addr] if next_addr is not None else []
        if t is not None:
            s = s + [t]
        return s, False
    if op in UNCOND:
        t = target_of(ops)
        if op == "jr":
            return [], True
        return ([t] if t is not None else []), t is None
    if op == "jal":
        t = target_of(ops) if target_of(ops) is not None else resolved
        return ([t] if t is not None else []), t is None
    if op == "jalr":
        # `jalr N(base)` that objdump resolved is a long-range DIRECT call: its target is known.
        if resolved is not None:
            return [resolved], False
        return [], True
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
    program = json.loads(Path(a.program).read_text())
    occ = program.get("function_instances", program.get("occurrences"))
    if occ is None:
        raise SystemExit("program has neither function_instances nor legacy occurrences")

    # The generator attributes each PC's edges to the DEEPEST occurrence owning it
    # (`owned = regions - children's regions`), so an edge appears exactly once across an inline chain.
    # The audit must use the same ownership, otherwise a parent looks "incomplete" for edges that are
    # correctly attributed to its inlined children.
    def region_pcs(o):
        s = set()
        for r in o["regions"]:
            s |= set(range(r["start"], r["start"] + r["size"], 2))
        return s

    rpcs = [region_pcs(o) for o in occ]

    report = []
    tot_missing = tot_bogus = tot_exitbad = 0
    for i, o in enumerate(occ):
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
            op, ops, resolved = insns[pc]
            succ, indirect = successors(pc, op, ops, nxt.get(pc), resolved)
            if indirect:
                indirect_sites.append(pc)
            for t in succ:
                if t is not None:
                    real.add((pc, t))
        missing = sorted(e for e in real if e not in declared)
        bogus = sorted(e for e in declared if e not in real)
        # every real transfer leaving the occurrence's own regions must have its source in `exits`
        # A resolved call leaves the caller's own regions temporarily and then resumes at its
        # continuation. The call edge is real CFG data, but its source is not a function exit.
        leaving_src = {pc for (pc, t) in real if t not in region and insns[pc][0] not in CALL}
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
            "occurrences": len(occ),
            "occurrencesWithMissingInternalEdges": sum(1 for r in report if r["missingCount"]),
            "totalMissingInternalEdges": tot_missing,
            "occurrencesWithDeclaredNotReal": sum(1 for r in report if r["declaredNotRealCount"]),
            "totalDeclaredNotReal": tot_bogus,
            "totalLeavingSourcesNotInExits": tot_exitbad,
        },
        "occurrences": report,
    }
    Path(a.out_json).write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    s = out["summary"]
    print(f"occurrences={s['occurrences']}")
    print(f"  with MISSING internal edges: {s['occurrencesWithMissingInternalEdges']} "
          f"(total {s['totalMissingInternalEdges']})")
    print(f"  with declared-but-not-real edges: {s['occurrencesWithDeclaredNotReal']} "
          f"(total {s['totalDeclaredNotReal']})")
    print(f"  leaving-transfer sources absent from `exits`: {s['totalLeavingSourcesNotInExits']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
