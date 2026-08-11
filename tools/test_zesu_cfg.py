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
    validate_instances(data)
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
    assert flame["tree"]["name"].startswith("main [fn:")
    assert flame["schemaVersion"] == 3
    assert sum(row["self"] for row in flame["meta"].values()) == flame["programTotal"]
    inline_nodes = [row for row in flame["meta"].values() if row["kind"] == "inlinedFunctionInstance"]
    assert len(inline_nodes) > 100
    decode = next(row for row in inline_nodes if row["qualified"] == "ssz.decode")
    assert decode["file"] == "deps/zesu/src/stateless/stateless/ssz.zig"
    assert decode["self"] > 0
    if len(data["functions"]) < 100:
        assert decode["callFile"] == "deps/zesu/src/zkvm/ssz_decode_root.zig"
        assert decode["value"] == 818

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

    orphaned = copy.deepcopy(data)
    next(row for row in orphaned["functionInstances"] if row["kind"] == "inlined")["parent"] = None
    try:
        validate_instances(orphaned)
    except AssertionError:
        pass
    else:
        raise AssertionError("orphaned inline function instance was accepted")

    forged_range = copy.deepcopy(data)
    inline = next(row for row in forged_range["functionInstances"] if row["kind"] == "inlined")
    inline["ranges"] = [{"start": inline["entryPc"] + 4, "end": inline["entryPc"] + 8}]
    try:
        validate_instances(forged_range)
    except AssertionError:
        pass
    else:
        raise AssertionError("forged inline function range was accepted")


def validate_instances(data: dict) -> None:
    instances = data["functionInstances"]
    by_id = {row["id"]: row for row in instances}
    assert len(by_id) == len(instances) == data["totals"]["functionInstances"]
    assert sum(row["kind"] == "inlined" for row in instances) == data["totals"]["inlinedFunctionInstances"]
    assert data["totals"]["inlinedFunctionInstances"] > 100
    for row in instances:
        assert row["kind"] in {"concrete", "inlined"}
        assert row["instructionCount"] == len(row["pcs"]) > 0
        assert row["entryPc"] == min(row["pcs"])
        assert row["sourceFile"] and not row["sourceFile"].startswith("/build/source/")
        assert all(any(region["start"] <= pc < region["end"] for region in row["ranges"]) for pc in row["pcs"])
        if row["kind"] == "concrete":
            assert row["parent"] is None
        else:
            assert row["parent"] in by_id
            assert set(row["pcs"]) <= set(by_id[row["parent"]]["pcs"])
    decode = next(row for row in instances if row["name"] == "ssz.decode" and row["kind"] == "inlined")
    if len(data["functions"]) < 100:
        assert decode["instructionCount"] == 818
    assert decode["sourceFile"] == "deps/zesu/src/stateless/stateless/ssz.zig"


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
