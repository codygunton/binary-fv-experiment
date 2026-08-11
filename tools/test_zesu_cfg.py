#!/usr/bin/env python3
"""Validate the generated authentic-Zesu CFG and its evidence boundary."""

import argparse
import copy
import json
from collections import Counter
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
    validate_flame(data, flame)
    assert flame["total"] == data["totals"]["instructions"]
    assert flame["programTotal"] > flame["total"] * 3 // 4
    assert flame["tree"]["name"].startswith("main [fn:")
    assert flame["schemaVersion"] == 3
    inline_nodes = [row for row in flame["meta"].values() if row["kind"] == "inlinedFunctionInstance"]
    assert len(inline_nodes) > 100
    decode = next(row for row in inline_nodes if row["qualified"] == "ssz.decode")
    assert decode["file"] == "deps/zesu/src/stateless/stateless/ssz.zig"
    assert decode["self"] > 0
    if len(data["functions"]) < 100:
        assert decode["callFile"] == "deps/zesu/src/zkvm/ssz_decode_root.zig"
        assert decode["machineInstructionCount"] == 818
        tx_key, tx = next((key, row) for key, row in flame["meta"].items()
                          if row["qualified"] == "rlp_decode.decodeTxFields")
        assert "|ssz.decode [" in tx_key and "|rlp_decode.decodeSingleTx [" in tx_key
        assert tx_key.index("|ssz.decode [") < tx_key.index("|rlp_decode.decodeSingleTx [")
        assert tx["displayAnchorName"] == "rlp_decode.decodeSingleTx"
        assert tx["displayCallsites"] == [0x274c, 0x27a0]

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

    forged_anchor = copy.deepcopy(flame)
    tx = next(row for row in forged_anchor["meta"].values() if row["qualified"] == "rlp_decode.decodeTxFields")
    tx["displayCallsites"] = [0]
    try:
        validate_flame(data, forged_anchor)
    except AssertionError:
        pass
    else:
        raise AssertionError("forged inline callsite anchor was accepted")


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


def validate_flame(data: dict, flame: dict) -> None:
    instances = {row["id"]: row for row in data["functionInstances"]}
    assert sum(row["self"] for row in flame["meta"].values()) == flame["programTotal"]
    assert len({row["owner"] for row in flame["meta"].values()}) == len(flame["meta"])
    seen_levels = {}

    def record_levels(node: dict, level: int = 0) -> None:
        seen_levels[node["key"]] = level
        for child in node["children"]:
            record_levels(child, level + 1)

    record_levels(flame["tree"])
    assert set(seen_levels) == set(flame["meta"])
    for row in flame["meta"].values():
        assert row["machineInstructionCount"] > 0
        if row["kind"] == "inlinedFunctionInstance":
            assert row["owner"] in instances
            assert row["machineInstructionCount"] == instances[row["owner"]]["instructionCount"]
        elif row["displayAnchor"] and row["displayAnchor"].startswith("fi:"):
            assert row["displayAnchor"] in instances
            anchor_pcs = set(instances[row["displayAnchor"]]["pcs"])
            assert row["displayCallsites"] and set(row["displayCallsites"]) <= anchor_pcs
    assert all(flame["meta"][key]["refinementLevel"] == level for key, level in seen_levels.items())
    assert flame["meta"][flame["tree"]["key"]]["refinementLevel"] == 0
    if len(data["functions"]) < 100:
        level_one = Counter(flame["meta"][child["key"]]["qualified"] for child in flame["tree"]["children"])
        assert level_one == Counter({
            "alt_fl_alloc.get": 1,
            "ssz.decode": 1,
            "ssz_decode_root.put": 10,
            "extern_io.write_output": 1,
            "mem.Allocator.allocBytesWithAlignment__anon_1965": 1,
        })


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
