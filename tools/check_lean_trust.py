#!/usr/bin/env python3
"""Reject trust-affecting Lean syntax and enforce a unique public root theorem."""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "BinaryFv"


def erase_comments_and_literals(text: str) -> str:
    """Preserve newlines while erasing nested comments, strings, and character literals."""
    out: list[str] = []
    i = 0
    block_depth = 0
    quote: str | None = None
    while i < len(text):
        pair = text[i:i + 2]
        char = text[i]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif quote:
            if char == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
                if char == quote:
                    quote = None
        elif pair == "/-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            if end < 0:
                out.extend(" " * (len(text) - i))
                break
            out.extend(" " * (end - i))
            i = end
        elif char == '"':
            quote = char
            out.append(" ")
            i += 1
        else:
            out.append(char)
            i += 1
    return "".join(out)


FORBIDDEN = {
    "proof placeholder": re.compile(r"\b(?:sorry|admit)\b"),
    "custom axiom": re.compile(r"\baxiom\s+[A-Za-z0-9_'.]+"),
    "implementation escape hatch": re.compile(r"@\[\s*(?:implemented_by|extern)\b"),
    "unsafe declaration": re.compile(
        r"\bunsafe\s+(?:def|abbrev|theorem|opaque|instance)\b"
    ),
}
ROOT_DECL = re.compile(
    r"\b(?:def|theorem|lemma|abbrev|opaque)\s+(root_[A-Za-z0-9_']+)\b"
)


def main() -> int:
    probes = {
        "inline sorry": "theorem bad : True := sorry",
        "inline admit": "theorem bad : True := by admit",
        "custom axiom": "axiom bad : False",
        "implemented_by": "@[implemented_by bad] opaque x : Nat",
        "extern": "@[extern \"bad\"] opaque x : Nat",
        "unsafe declaration": "unsafe def bad := 0",
    }
    for label, source in probes.items():
        if not any(pattern.search(erase_comments_and_literals(source))
                   for pattern in FORBIDDEN.values()):
            raise AssertionError(f"trust audit power probe did not detect {label}")
    comment_probe = "-- sorry\n/- axiom bad : False -/\ntheorem good : True := by trivial"
    if any(pattern.search(erase_comments_and_literals(comment_probe))
           for pattern in FORBIDDEN.values()):
        raise AssertionError("trust audit matched prose rather than Lean syntax")

    violations: list[str] = []
    roots: list[str] = []
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        clean = erase_comments_and_literals(path.read_text())
        rel = path.relative_to(ROOT)
        for label, pattern in FORBIDDEN.items():
            for match in pattern.finditer(clean):
                line = clean.count("\n", 0, match.start()) + 1
                violations.append(f"{rel}:{line}: {label}: {match.group(0)!r}")
        roots.extend(ROOT_DECL.findall(clean))

    expected_roots = ["root_compliance"]
    if roots != expected_roots:
        violations.append(
            "public root theorem mismatch: expected "
            f"{expected_roots!r}, found {roots!r}"
        )
    if violations:
        print("Lean trust audit failed:", file=sys.stderr)
        print("\n".join(f"  {item}" for item in violations), file=sys.stderr)
        return 1
    print(f"Lean trust audit passed: unique root theorem {roots[0]}; no forbidden syntax")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
