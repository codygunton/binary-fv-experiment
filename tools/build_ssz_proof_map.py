#!/usr/bin/env python3
"""Build the SSZ proof-authoring view from authoritative generated artifacts."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def build(cfg: dict, flame: dict, manifest: dict, evidence: dict) -> dict:
    if cfg["artifact"] != manifest["artifact"] or cfg["artifact"] != evidence["artifact"]:
        raise ValueError("CFG, manifest, and evidence artifact identities differ")
    root = flame["tree"]
    root_display_id = root["name"].rsplit("[fn:", 1)[1].rstrip("]")
    root_entry = int(root_display_id, 16)
    main = next(row for row in cfg["functionInstances"]
                if row["kind"] == "concrete" and row["entryPc"] == root_entry)
    selected_extent = {pc for row in manifest["instances"] for pc in row["executionPcs"]}
    glue_pcs = sorted(set(main["pcs"]) - selected_extent)
    if len(glue_pcs) != root["self"]:
        raise ValueError("Level 0 glue count disagrees with the flame hierarchy")

    instruction_by_pc = {}
    block_by_pc = {}
    for function in cfg["functions"]:
        for block in function["blocks"]:
            for instruction in block["instructions"]:
                instruction_by_pc.setdefault(instruction["pc"], instruction)
                block_by_pc.setdefault(instruction["pc"], block)

    observed = {}
    for vector in evidence["vectors"]:
        for row in vector["instances"]:
            slot = observed.setdefault(row["id"], {
                "vectors": [], "owned": set(), "extent": set(), "exits": set(),
            })
            if row["entryReached"]:
                slot["vectors"].append(vector["label"])
            slot["owned"].update(row["executedOwnedPcs"])
            slot["extent"].update(row["executedExtentPcs"])
            slot["exits"].update(tuple(edge) for edge in row["observedExitTransitions"])

    boundaries, regions, nodes, edges = [], [], [], []
    nodes.append({
        "id": "spec", "label": "EVM-Sail StatelessInput + transaction decode",
        "kind": "specification", "column": 0, "status": "artifact", "instructionCount": 0,
    })
    for row in manifest["instances"]:
        capture = observed[row["id"]]
        boundary_id = "level1-" + row["id"].replace(":", "-")
        source = row["functionInstanceIdentity"]["function"]["declaration"]
        boundaries.append({
            "id": boundary_id, "instanceId": row["id"], "qualified": row["qualified"],
            "entryPc": row["entryPc"], "instructionPcs": row["instructionPcs"],
            "executionPcs": row["executionPcs"], "ownedInstructionCount": row["ownedInstructionCount"],
            "subtreeInstructionCount": row["subtreeInstructionCount"],
            "source": source, "observedVectors": sorted(capture["vectors"]),
            "observedOwnedInstructionCount": len(capture["owned"]),
            "observedExtentInstructionCount": len(capture["extent"]),
            "observedExitTransitions": [list(edge) for edge in sorted(capture["exits"])],
            "evidenceStatus": "captured", "kernelStatus": "not_started",
        })
        regions.append({
            "id": boundary_id, "label": row["qualified"], "authoringState": "blocked",
            "blocker": "Review the typed entry/result binding before stating this Level 1 contract.",
            "scope": "selected-child", "pcs": row["executionPcs"], "boundaryIds": [boundary_id],
            "evidence": "production entry registers, PCs, memory accesses, and exits captured",
            "preparation": {
                "liveRegisters": [], "protectedMemory": [],
                "prerequisites": ["typed source/machine boundary review"],
                "sourceIdentity": f"{source['file']}::{source['qualifiedName']}",
            },
        })
        node_id = "contract-" + boundary_id
        nodes.append({
            "id": node_id, "label": row["qualified"], "kind": "level1Contract",
            "column": 1, "status": "evidence", "boundaryId": boundary_id,
            "instructionCount": row["subtreeInstructionCount"],
            "source": source["file"],
        })
        edges.append({"source": "spec", "target": node_id, "kind": "semantic-review"})
        edges.append({"source": node_id, "target": "conversion", "kind": "dependency"})

    regions.append({
        "id": "level0-glue", "label": "main parent-owned glue", "authoringState": "ready",
        "blocker": "Prove these instructions while composing all selected Level 1 contracts.",
        "scope": "parent", "pcs": glue_pcs, "boundaryIds": [],
        "evidence": "production ELF structure and endpoint differential fixtures",
        "preparation": {"liveRegisters": [], "protectedMemory": [],
                        "prerequisites": ["admitted Level 1 bindings"],
                        "sourceIdentity": "deps/zesu/src/zkvm/ssz_decode_root.zig::main"},
    })
    nodes.extend([
        {"id": "glue", "label": "main parent-owned glue", "kind": "parentGlue", "column": 1,
         "status": "ready", "phase": "level0-glue", "instructionCount": len(glue_pcs),
         "provedInstructionCount": 0},
        {"id": "conversion", "label": "exportedContracts_of_level1", "kind": "conversion",
         "column": 2, "status": "blocked"},
        {"id": "root", "label": "root_compliance", "kind": "parent", "column": 3,
         "status": "blocked"},
    ])
    edges.extend([
        {"source": "glue", "target": "conversion", "kind": "dependency"},
        {"source": "conversion", "target": "root", "kind": "dependency"},
    ])

    instructions = []
    for pc in sorted(set(main["pcs"]) | selected_extent):
        row = instruction_by_pc[pc]
        instructions.append({
            "pc": pc, "mnemonic": row["mnemonic"], "operands": row["operands"],
            "successors": block_by_pc[pc]["successors"], "reads": [], "writes": [], "memory": [],
            "owner": "main", "sourceFile": block_by_pc[pc]["sourceFile"],
            "sourceLine": block_by_pc[pc]["sourceLine"], "formalManifests": [],
            "artifactState": "same-elf",
        })
    return {
        "schemaVersion": 2, "target": flame["machineRegionInputs"]["target"],
        "artifact": cfg["artifact"], "instructions": instructions, "blocks": [],
        "boundaries": boundaries, "manifests": [],
        "formalCoverage": {"localPcCount": 0, "level1PcCount": 0, "rootPcCount": 0},
        "compilerProvenance": {"state": "same-ELF DWARF"},
        "phases": [{"id": "level0-glue", "label": "main parent-owned glue", "pcs": glue_pcs}],
        "authoringRegions": regions,
        "refinementGraph": {"nodes": nodes, "edges": edges},
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    for name in ("cfg", "flame", "manifest", "evidence", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    result = build(*(json.loads(getattr(args, name).read_text())
                     for name in ("cfg", "flame", "manifest", "evidence")))
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
