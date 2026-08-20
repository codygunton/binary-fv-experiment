#!/usr/bin/env python3
"""Check hLevel3 guidance concepts against two completed Level 2 child proofs."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


CASES = {
    0x14E00: "writeSuccessPrefixInstanceContract",
    0x14E7C: "writeSuccessPrevRandaoInstanceContract",
}


def theorem_body(source: str, theorem: str) -> str:
    match = re.search(rf"\btheorem\s+{re.escape(theorem)}\b", source)
    if not match:
        raise ValueError(f"missing completed theorem {theorem}")
    next_decl = re.search(r"\n(?:private\s+)?theorem\s+", source[match.end():])
    end = match.end() + next_decl.start() if next_decl else len(source)
    return source[match.start():end]


def build(manifest: dict, source: str) -> dict:
    by_entry = {row["entryPc"]: row for row in manifest["instances"]}
    cases = []
    for entry, theorem in CASES.items():
        if entry not in by_entry:
            raise ValueError(f"missing held-out Level 2 instance at 0x{entry:x}")
        row = by_entry[entry]
        body = theorem_body(source, theorem)
        mechanisms = {
            "Seg": "Seg" in body or "seg" in body,
            "configuredInstructionStep": "configured" in body,
            "exactMachineScope": "pcInRanges" in body or "owned_pc" in body,
            "registerOrMemoryFrame": "WritesOnly" in body or ".mem" in body,
        }
        if not all(mechanisms.values()):
            raise ValueError(f"guidance mechanisms do not cover completed theorem {theorem}")
        cases.append({
            "instanceId": row["id"], "entryPc": entry, "qualified": row["qualified"],
            "theorem": theorem, "executionInstructionCount": len(row["executionPcs"]),
            "mechanisms": mechanisms,
        })
    return {
        "schemaVersion": 1, "artifact": manifest["artifact"],
        "status": "passed", "caseCount": len(cases), "cases": cases,
        "claim": "The guidance categories retrieve mechanisms used by two completed contracts.",
        "nonClaim": "This check does not reconstruct or reprove either contract.",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = build(json.loads(args.manifest.read_text()), args.source.read_text())
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
