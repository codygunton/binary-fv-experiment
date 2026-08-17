#!/usr/bin/env python3
"""Build an honest baseline for the proof below ``root_compliance hLevel2``."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

PROVED_LEVEL2_ENTRIES = {0x14E00, 0x14E7C}
PROVED_LEVEL2_NAMES = {"memcpy"}
PROVED_LEVEL1_NAMES = {"read_input", "zkvm_exit", "alt_fl_alloc.get"}


def read_dependencies(path: Path) -> tuple[list[dict], list[dict]]:
    declarations, edges = [], []
    for line in path.read_text().splitlines():
        kind, left, right = line.split("\t")
        if kind == "declaration":
            declarations.append({"name": left, "module": right})
        elif kind == "edge":
            edges.append({"declaration": left, "dependency": right})
        else:
            raise ValueError(f"unknown dependency row {kind!r}")
    names = {row["name"] for row in declarations}
    if "BinaryFv.Zesu.root_compliance" not in names:
        raise ValueError("dependency graph does not contain root_compliance")
    if any(edge["declaration"] not in names or edge["dependency"] not in names
           for edge in edges):
        raise ValueError("dependency edge escapes the declaration closure")
    return declarations, edges


def build(dependency_path: Path, cfg: dict, flame: dict, level1: dict, level2: dict) -> dict:
    artifacts = [cfg["artifact"], level1["artifact"], level2["artifact"]]
    if any(artifact != artifacts[0] for artifact in artifacts[1:]):
        raise ValueError("CFG and contract manifests describe different artifacts")
    declarations, edges = read_dependencies(dependency_path)
    root_entry = int(flame["tree"]["name"].rsplit("[fn:", 1)[1].rstrip("]"), 16)
    main = next(row for row in cfg["functionInstances"]
                if row["kind"] == "concrete" and row["entryPc"] == root_entry)
    l1_by_id = {row["id"]: row for row in level1["instances"]}
    l2_by_parent: dict[str, set[int]] = {}
    for row in level2["instances"]:
        for parent in row["parentInstanceIds"]:
            l2_by_parent.setdefault(parent, set()).update(row["executionPcs"])

    l1_extent = {pc for row in level1["instances"] for pc in row["executionPcs"]}
    level0_direct = set(main["pcs"]) - l1_extent
    level1_direct: dict[str, list[int]] = {}
    for row in level1["instances"]:
        level1_direct[row["id"]] = sorted(set(row["executionPcs"]) -
                                           l2_by_parent.get(row["id"], set()))
    proved_l2 = [row for row in level2["instances"]
                 if row["qualified"] in PROVED_LEVEL2_NAMES or
                 row["entryPc"] in PROVED_LEVEL2_ENTRIES]
    direct_regions = {
        "level0Parent": sorted(level0_direct),
        "provedLevel1": sorted({pc for row in level1["instances"]
                                if row["qualified"] in PROVED_LEVEL1_NAMES
                                for pc in row["executionPcs"]}),
        "conditionalLevel1Parent": sorted({pc for ident, pcs in level1_direct.items()
                                           if l1_by_id[ident]["qualified"] not in
                                           PROVED_LEVEL1_NAMES for pc in pcs}),
        "provedLevel2": sorted({pc for row in proved_l2 for pc in row["executionPcs"]}),
    }
    boundary_union = sorted({pc for pcs in direct_regions.values() for pc in pcs})
    elf_pcs = {instruction["pc"] for function in cfg["functions"]
               for block in function["blocks"] for instruction in block["instructions"]}
    if missing := set(boundary_union) - elf_pcs:
        raise ValueError(f"baseline contains PCs absent from the ELF: {sorted(missing)}")

    unresolved = [row for row in level2["instances"] if row not in proved_l2]
    return {
        "schemaVersion": 1,
        "artifact": artifacts[0],
        "root": "BinaryFv.Zesu.root_compliance",
        "declarations": declarations,
        "dependencyEdges": edges,
        "counts": {
            "transitiveProjectDeclarations": len(declarations),
            "dependencyEdges": len(edges),
            "level0DirectRegionPcs": len(direct_regions["level0Parent"]),
            "conditionalLevel1DirectRegionPcs": len(direct_regions["conditionalLevel1Parent"]),
            "boundaryRegionUniquePcs": len(boundary_union),
            "unresolvedLevel2Contracts": len(unresolved),
        },
        "coverage": {
            "meaning": "Region geometry; this is not an executed-step count.",
            "regions": direct_regions,
            "boundaryUnion": boundary_union,
            "directlyDischargedStepPcs": [],
            "directStepStatus": "pending declaration-to-step attribution",
            "conditionalContractRegions": [
                {"id": row["id"], "qualified": row["qualified"],
                 "pcs": row["executionPcs"]} for row in unresolved
            ],
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dependencies", required=True, type=Path)
    for name in ("cfg", "flame", "level1", "level2", "output"):
        parser.add_argument(f"--{name}", required=True, type=Path)
    args = parser.parse_args()
    result = build(args.dependencies, *(
        json.loads(getattr(args, name).read_text()) for name in
        ("cfg", "flame", "level1", "level2")))
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
