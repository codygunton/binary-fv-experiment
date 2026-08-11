#!/usr/bin/env python3
"""Validate the generated authentic-Zesu CFG and its evidence boundary."""

import argparse
import copy
import json
from pathlib import Path


def validate(path: Path) -> None:
    data = json.loads(path.read_text())
    assert data["artifact"]["kind"] == "ELF64 RISC-V relocatable object"
    assert data["sourceMapping"]["confidence"] == "exact-line-table"
    assert data["formalStatus"].startswith("No kernel-backed")
    assert data["totals"]["functions"] == len(data["functions"])
    assert data["totals"]["blocks"] == sum(len(fn["blocks"]) for fn in data["functions"])
    assert data["totals"]["symbolInstructionReferences"] == sum(fn["instructionCount"] for fn in data["functions"])
    assert any(fn["semanticGroup"] == "ssz" for fn in data["functions"])
    helper = next(fn for fn in data["functions"] if fn["name"] == "ssz.decodeByteListList")
    assert helper["sourceFile"] == "deps/zesu/src/stateless/stateless/ssz.zig"
    assert helper["blocks"][0]["successors"] == ["0x40", "0x20"]
    for fn in data["functions"]:
        ids = {block["id"] for block in fn["blocks"]}
        assert fn["sourceFile"] and not fn["sourceFile"].startswith("/build/source/")
        assert fn["proofStatus"] == "not_started"
        for block in fn["blocks"]:
            assert block["instructionCount"] == len(block["instructions"])
            assert set(block["successors"]) <= ids
            assert block["sourceFile"] and not block["sourceFile"].startswith("/build/source/")

    flame = json.loads(path.with_name("flame.json").read_text())
    assert flame["total"] == data["totals"]["instructions"]
    assert flame["programTotal"] > flame["total"] * 3 // 4
    assert {node["name"] for node in flame["tree"]["children"]} == {"program", "not-called-by-program"}

    proof = json.loads(path.with_name("proof-map.json").read_text())
    validate_proof(proof)
    forged = copy.deepcopy(proof)
    forged["formalCoverage"]["localPcCount"] = 1
    try:
        validate_proof(forged)
    except AssertionError:
        pass
    else:
        raise AssertionError("forged formal coverage was accepted")


def validate_proof(proof: dict) -> None:
    manifest_pcs = {pc for manifest in proof["manifests"] for pc in manifest["pcs"]}
    assert proof["formalCoverage"]["localPcCount"] == len(manifest_pcs)
    assert proof["formalCoverage"]["level4PcCount"] <= len(manifest_pcs)
    assert proof["formalCoverage"]["rootPcCount"] <= proof["formalCoverage"]["level4PcCount"]
    assert not manifest_pcs


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("cfg", type=Path)
    validate(parser.parse_args().cfg)
