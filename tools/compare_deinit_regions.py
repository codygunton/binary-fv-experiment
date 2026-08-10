#!/usr/bin/env python3
"""Compare generated instruction/CFG shapes for two machine-region owners.

This is deliberately a retrieval tool, not a proof generator: all input facts come from the
generated machine-regions artifact and every proposed match remains subject to exact Lean checking.
"""

from __future__ import annotations

import argparse
import difflib
import json
import pathlib
import re
from collections import Counter


REGISTER = re.compile(r"\b(?:zero|ra|sp|gp|tp|t[0-6]|s(?:[0-9]|10|11)|a[0-7])\b")
NUMBER = re.compile(r"(?<![A-Za-z0-9_])-?(?:0x[0-9a-f]+|[0-9]+)")


def instructions(document: dict, owner: str) -> list[dict]:
    result = sorted(
        (item for item in document["instructions"] if item["owner"] == owner),
        key=lambda item: item["address"],
    )
    if not result:
        raise ValueError(f"owner {owner!r} has no instructions")
    return result


def operand_shape(operands: str) -> str:
    """Erase concrete register names, immediates, and rendered branch targets."""
    operands = re.sub(r"\s*<[^>]+>", "", operands)
    operands = REGISTER.sub("R", operands)
    return NUMBER.sub("N", operands).replace(" ", "")


def signature(item: dict) -> str:
    memory = "+".join(sorted(effect.get("kind", "memory") for effect in item["memory"])) or "-"
    external = sum(successor not in {item["address"] + 4} for successor in item["successors"])
    return ":".join(
        (
            item["mnemonic"],
            operand_shape(item["operands"]),
            f"r{len(item['reads'])}",
            f"w{len(item['writes'])}",
            memory,
            f"x{external}",
        )
    )


def cfg_summary(items: list[dict]) -> dict:
    addresses = {item["address"] for item in items}
    internal = []
    external = []
    terminals = []
    for item in items:
        if not item["successors"]:
            terminals.append(item["address"])
        for successor in item["successors"]:
            edge = [item["address"], successor]
            (internal if successor in addresses else external).append(edge)
    return {
        "internalEdges": internal,
        "externalEdges": external,
        "terminals": terminals,
        "linearInternalEdges": sum(target == source + 4 for source, target in internal),
    }


def matching_blocks(left: list[str], right: list[str], minimum: int = 2) -> list[dict]:
    matcher = difflib.SequenceMatcher(a=left, b=right, autojunk=False)
    return [
        {"leftIndex": block.a, "rightIndex": block.b, "length": block.size,
         "signatures": left[block.a:block.a + block.size]}
        for block in matcher.get_matching_blocks()
        if block.size >= minimum
    ]


def shared_ngrams(left: list[str], right: list[str], size: int) -> list[dict]:
    def occurrences(sequence: list[str]) -> dict[tuple[str, ...], list[int]]:
        result: dict[tuple[str, ...], list[int]] = {}
        for index in range(len(sequence) - size + 1):
            result.setdefault(tuple(sequence[index:index + size]), []).append(index)
        return result

    left_occurrences = occurrences(left)
    right_occurrences = occurrences(right)
    return [
        {"signature": list(key), "left": left_occurrences[key], "right": right_occurrences[key]}
        for key in sorted(left_occurrences.keys() & right_occurrences.keys())
    ]


def analyze(document: dict, left_owner: str, right_owner: str) -> dict:
    left_items = instructions(document, left_owner)
    right_items = instructions(document, right_owner)
    left = [signature(item) for item in left_items]
    right = [signature(item) for item in right_items]
    matcher = difflib.SequenceMatcher(a=left, b=right, autojunk=False)
    blocks = matching_blocks(left, right)
    return {
        "schemaVersion": 1,
        "owners": {
            "left": {"id": left_owner, "count": len(left_items),
                     "start": left_items[0]["address"], "stop": left_items[-1]["address"] + 4,
                     "mnemonics": dict(Counter(item["mnemonic"] for item in left_items)),
                     "cfg": cfg_summary(left_items), "signatures": left},
            "right": {"id": right_owner, "count": len(right_items),
                      "start": right_items[0]["address"], "stop": right_items[-1]["address"] + 4,
                      "mnemonics": dict(Counter(item["mnemonic"] for item in right_items)),
                      "cfg": cfg_summary(right_items), "signatures": right},
        },
        "comparison": {
            "sequenceRatio": matcher.ratio(),
            "lcsBlocks": blocks,
            "matchedInstructions": sum(block["length"] for block in blocks),
            "shared3grams": shared_ngrams(left, right, 3),
            "shared5grams": shared_ngrams(left, right, 5),
        },
    }


def self_test(result: dict) -> None:
    left = result["owners"]["left"]
    right = result["owners"]["right"]
    assert left["count"] == 29
    assert right["count"] == 45
    assert (left["start"], left["stop"]) == (0x13038, 0x130AC)
    assert (right["start"], right["stop"]) == (0x131EC, 0x132A0)
    assert len(left["cfg"]["terminals"]) == len(right["cfg"]["terminals"]) == 1
    assert len(left["cfg"]["externalEdges"]) == 3
    assert len(right["cfg"]["externalEdges"]) == 5
    assert len(left["cfg"]["internalEdges"]) == left["cfg"]["linearInternalEdges"] == 28
    assert len(right["cfg"]["internalEdges"]) == right["cfg"]["linearInternalEdges"] == 44
    comparison = result["comparison"]
    assert abs(comparison["sequenceRatio"] - 0.6216216216216216) < 1e-15
    assert comparison["matchedInstructions"] == 21
    assert len(comparison["shared3grams"]) == 15
    assert len(comparison["shared5grams"]) == 11
    assert max(block["length"] for block in comparison["lcsBlocks"]) == 13


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("machine_regions", type=pathlib.Path)
    parser.add_argument("--left", default="excluded:0")
    parser.add_argument("--right", default="excluded:3")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    result = analyze(json.loads(args.machine_regions.read_text()), args.left, args.right)
    if args.self_test:
        self_test(result)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
