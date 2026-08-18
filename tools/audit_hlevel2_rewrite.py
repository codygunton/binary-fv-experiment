#!/usr/bin/env python3
"""Fail when the optimized hLevel2 proof regains known expensive proof shapes."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROOF_FILES = (
    "InstructionClassSteps.lean", "Level0MainSteps.lean", "Level1DecodeInputSteps.lean",
    "Level1WriteContracts.lean", "Level1WriteSuccessSteps.lean", "Level2RuntimeLeaves.lean")
MACHINE = ROOT / "BinaryFv/Zesu/MachineExecution"
ALLOWED_EXPLICIT_STATES = {
    ("Level2RuntimeLeaves.lean", "readInputInstanceContract"),
    # These three use Seg for the ordinary prefix. Their named states only bridge the final
    # endpoint-specific read/write/exit step, which Seg intentionally does not model.
    ("Level2RuntimeLeaves.lean", "writeOutputHandoff"),
    ("Level2RuntimeLeaves.lean", "zkvmExitInstanceContract"),
}


def declaration_at(text: str, offset: int) -> str:
    matches = list(re.finditer(
        r"^(?:private\s+)?(?:theorem|def|abbrev|structure)\s+([A-Za-z_][A-Za-z0-9_']*)",
        text[:offset], re.MULTILINE))
    return matches[-1].group(1) if matches else "<module>"


def main() -> int:
    violations: list[str] = []
    for filename in PROOF_FILES:
        path = MACHINE / filename
        text = path.read_text()
        if "set_option maxHeartbeats" in text:
            violations.append(f"{filename}: heartbeat override")
        for match in re.finditer(r"^\s*let\s+(?:s|state)\d+\s*:=", text, re.MULTILINE):
            declaration = declaration_at(text, match.start())
            if (filename, declaration) not in ALLOWED_EXPLICIT_STATES:
                line = text.count("\n", 0, match.start()) + 1
                violations.append(f"{filename}:{line}: explicit successor chain in {declaration}")
    if violations:
        raise SystemExit("\n".join(violations))
    print("hLevel2 rewrite shape audit: PASS")
    print("explicit states remain only at the three endpoint-step bridges")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
