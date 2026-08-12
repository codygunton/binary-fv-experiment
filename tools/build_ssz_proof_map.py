#!/usr/bin/env python3
"""Build the SSZ proof-authoring view from authoritative generated artifacts."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def build(cfg: dict, flame: dict, manifest: dict, evidence: dict, bindings: dict) -> dict:
    if any(cfg["artifact"] != document["artifact"]
           for document in (manifest, evidence, bindings)):
        raise ValueError("CFG, manifest, evidence, and boundary-binding artifact identities differ")
    root = flame["tree"]
    root_display_id = root["name"].rsplit("[fn:", 1)[1].rstrip("]")
    root_entry = int(root_display_id, 16)
    main = next(row for row in cfg["functionInstances"]
                if row["kind"] == "concrete" and row["entryPc"] == root_entry)
    selected_extent = {pc for row in manifest["instances"] for pc in row["executionPcs"]}
    glue_pcs = sorted(set(main["pcs"]) - selected_extent)
    absorbed = sum(len(row["absorbedInstructionPcs"]) for row in manifest["instances"])
    if len(glue_pcs) + absorbed != root["self"]:
        raise ValueError("Level 0 glue plus reviewed inline absorption disagrees with flame ownership")

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
    bindings_by_id = {row["id"]: row["bindings"] for row in bindings["instances"]}
    consumed_level1 = {"read_input", "alt_fl_alloc.get"}
    proved_level0_pcs = {
        0x14CB0, 0x14CB4, 0x14CB8, 0x14CBC, 0x14CC0, 0x14CC4, 0x14CC8,
    }

    boundaries, regions, nodes, edges = [], [], [], []
    nodes.append({
        "id": "spec", "label": "EVM-Sail StatelessInput + transaction decode",
        "kind": "specification", "column": 0, "status": "artifact", "instructionCount": 0,
    })
    for row in manifest["instances"]:
        capture = observed[row["id"]]
        boundary_bindings = bindings_by_id[row["id"]]
        boundary_id = "level1-" + row["id"].replace(":", "-")
        source = row["functionInstanceIdentity"]["function"]["declaration"]
        contract_status = "specified_assumption"
        boundaries.append({
            "id": boundary_id, "instanceId": row["id"], "qualified": row["qualified"],
            "entryPc": row["entryPc"], "instructionPcs": row["instructionPcs"],
            "executionPcs": row["executionPcs"], "ownedInstructionCount": row["ownedInstructionCount"],
            "subtreeInstructionCount": row["subtreeInstructionCount"],
            "source": source, "observedVectors": sorted(capture["vectors"]),
            "observedOwnedInstructionCount": len(capture["owned"]),
            "observedExtentInstructionCount": len(capture["extent"]),
            "observedExitTransitions": [list(edge) for edge in sorted(capture["exits"])],
            "dwarfBindings": boundary_bindings,
            "evidenceStatus": "captured", "contractStatus": contract_status,
            "level0UseStatus": ("consumed" if row["qualified"] in consumed_level1
                                else "pending"),
            "proofStatus": "not_started", "kernelStatus": "not_started",
        })
        regions.append({
            "id": boundary_id, "label": row["qualified"],
            "authoringState": ("contract_consumed" if row["qualified"] in consumed_level1
                               else "contract_" + contract_status),
            "blocker": "Machine proof is deferred to later refinement; Level 0 may use this assumption.",
            "scope": "selected-child", "pcs": row["executionPcs"], "boundaryIds": [boundary_id],
            "evidence": "production entry registers, PCs, memory accesses, and exits captured",
            "preparation": {
                "liveRegisters": [
                    f"{binding['name']} = x{binding['machineRegister']}"
                    for binding in boundary_bindings if binding["machineRegister"] is not None
                ], "protectedMemory": [],
                "prerequisites": ["typed source/machine boundary review"],
                "sourceIdentity": f"{source['file']}::{source['qualifiedName']}",
            },
        })
        node_id = "contract-" + boundary_id
        nodes.append({
            "id": node_id, "label": row["qualified"], "kind": "level1Contract",
            "column": 1,
            "status": ("contract_consumed" if row["qualified"] in consumed_level1
                       else "contract_" + contract_status),
            "evidenceStatus": "captured", "contractStatus": contract_status,
            "level0UseStatus": ("consumed" if row["qualified"] in consumed_level1
                                else "pending"),
            "proofStatus": "not_started", "boundaryId": boundary_id,
            "instructionCount": row["subtreeInstructionCount"],
            "source": source["file"],
        })
        edges.append({"source": "spec", "target": node_id, "kind": "semantic-review"})
        edges.append({"source": node_id, "target": "conversion", "kind": "dependency"})

    regions.append({
        "id": "level0-glue", "label": "main parent-owned glue", "authoringState": "proof_in_progress",
        "blocker": "Continue from allocatorGet return PC 0x14cec through decodeInput and both exits.",
        "scope": "parent", "pcs": glue_pcs, "boundaryIds": [],
        "evidence": "production ELF structure and endpoint differential fixtures",
        "preparation": {"liveRegisters": [], "protectedMemory": [],
                        "prerequisites": ["admitted Level 1 bindings"],
                        "sourceIdentity": "deps/zesu/src/zkvm/ssz_decode_root.zig::main"},
    })
    nodes.extend([
        {"id": "glue", "label": "main parent-owned glue", "kind": "parentGlue", "column": 1,
         "status": "proof_in_progress", "proofStatus": "in_progress",
         "phase": "level0-glue", "instructionCount": len(glue_pcs),
         "absorbedInlineInstructionCount": absorbed,
         "provedInstructionCount": len(proved_level0_pcs)},
        {"id": "conversion", "label": "exportedContracts_of_level1", "kind": "conversion",
         "column": 2, "status": "not_started", "proofStatus": "not_started"},
        {"id": "root", "label": "root_compliance", "kind": "parent", "column": 3,
         "status": "not_started", "proofStatus": "not_started"},
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
        "formalCoverage": {"localPcCount": len(proved_level0_pcs),
                           "level1PcCount": 0, "rootPcCount": 0},
        "compilerProvenance": {"state": "same-ELF DWARF"},
        "phases": [{"id": "level0-glue", "label": "main parent-owned glue", "pcs": glue_pcs}],
        "authoringRegions": regions,
        "flameProgress": {
            "states": [
                {"owner": main["id"], "qualified": "main", "status": "in_progress"},
                *({"owner": row["id"], "qualified": row["qualified"],
                   "status": "contracted"} for row in manifest["instances"]),
            ],
        },
        "refinementGraph": {"nodes": nodes, "edges": edges},
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    for name in ("cfg", "flame", "manifest", "evidence", "bindings", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    result = build(*(json.loads(getattr(args, name).read_text())
                     for name in ("cfg", "flame", "manifest", "evidence", "bindings")))
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
