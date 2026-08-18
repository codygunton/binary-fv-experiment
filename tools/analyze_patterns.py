#!/usr/bin/env python3
"""Single entry point for machine-instruction and Lean-proof pattern analysis."""

from __future__ import annotations

import argparse


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", choices=("machine", "lean"))
    arguments, remaining = parser.parse_known_args()
    if arguments.corpus == "lean":
        from ngram_lean import main as lean_main

        return lean_main(remaining)
    from ngram_dashboard import main as machine_main

    return machine_main(remaining)


if __name__ == "__main__":
    raise SystemExit(main())
