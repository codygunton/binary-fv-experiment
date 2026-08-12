#!/usr/bin/env python3
"""Reject unexpected axioms in Lean's `#print axioms root_compliance` output."""

import re
import sys
from pathlib import Path


STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NATIVE_MARKERS = ("._native.native_decide.ax_", "._native.bv_decide.ax_")


def checked_axioms(text: str):
    match = re.search(r"root_compliance' depends on axioms: \[(.*?)\]", text, re.DOTALL)
    if match is None:
        raise AssertionError("missing root_compliance axiom report")
    axioms = {item.strip().removesuffix("✝") for item in match.group(1).split(",")}
    unexpected = sorted(
        axiom for axiom in axioms
        if axiom not in STANDARD and not any(marker in axiom for marker in NATIVE_MARKERS)
    )
    if unexpected:
        raise AssertionError(f"unexpected root_compliance axioms: {unexpected}")
    return axioms


if __name__ == "__main__":
    checked_axioms(Path(sys.argv[1]).read_text())
