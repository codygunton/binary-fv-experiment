#!/usr/bin/env python3
"""Build the SSZ proof-authoring view from authoritative generated artifacts."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def build(cfg: dict, flame: dict, manifest: dict, evidence: dict, bindings: dict,
          level2_manifest: dict | None = None, level2_evidence: dict | None = None,
          level2_bindings: dict | None = None, baseline: dict | None = None,
          hlevel3_inventory: dict | None = None, hlevel3_guidance: dict | None = None,
          hlevel3_admission: dict | None = None,
          hlevel3_direct_proofs: dict | None = None) -> dict:
    if any(cfg["artifact"] != document["artifact"]
           for document in (manifest, evidence, bindings)):
        raise ValueError("CFG, manifest, evidence, and boundary-binding artifact identities differ")
    if baseline is not None and cfg["artifact"] != baseline["artifact"]:
        raise ValueError("CFG and hLevel2 baseline artifact identities differ")
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
    consumed_level1 = {
        "read_input", "zkvm_exit", "alt_fl_alloc.get", "ssz_decode_root.decodeInput",
        "ssz_decode_observation.writeSuccess",
        "ssz_decode_observation.writeFailure",
    }
    level1_local_proofs = {
        "read_input": "proved",
        "zkvm_exit": "proved",
        "alt_fl_alloc.get": "proved",
        "ssz_decode_root.decodeInput": "conditionally_proven",
        "ssz_decode_observation.writeSuccess": "conditionally_proven",
        "ssz_decode_observation.writeFailure": "conditionally_proven",
    }
    level2_local_proofs = ({
        row["id"]: "proved"
        for row in level2_manifest["instances"]
        if row["qualified"] == "memcpy" or row["entryPc"] in {0x14E00, 0x14E7C}
    } if level2_manifest is not None else {})
    proved_level0_pcs = {
        0x14CB0, 0x14CB4, 0x14CB8, 0x14CBC, 0x14CC0, 0x14CC4, 0x14CC8,
        0x14CEC, 0x14CF0, 0x14CF4, 0x14CF8, 0x14CFC, 0x14D00,
        0x14D04, 0x14D08, 0x14D0C, 0x14D10, 0x14D14, 0x14D18,
        0x14D1C, 0x14D20, 0x14D24, 0x14D28, 0x14D2C,
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
            "proofStatus": level1_local_proofs[row["qualified"]],
            "kernelStatus": level1_local_proofs[row["qualified"]],
        })
        regions.append({
            "id": boundary_id, "label": row["qualified"],
            "authoringState": level1_local_proofs[row["qualified"]],
            "blocker": ("None: this leaf contract is proved unconditionally."
                        if level1_local_proofs[row["qualified"]] == "proved"
                        else "Proved conditionally from the selected Level 2 contracts."),
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
            "status": level1_local_proofs[row["qualified"]],
            "evidenceStatus": "captured", "contractStatus": contract_status,
            "level0UseStatus": ("consumed" if row["qualified"] in consumed_level1
                                else "pending"),
            "proofStatus": level1_local_proofs[row["qualified"]],
            "boundaryId": boundary_id,
            "instructionCount": row["subtreeInstructionCount"],
            "source": source["file"],
        })
        edges.append({"source": "spec", "target": node_id, "kind": "semantic-review"})
        edges.append({"source": node_id, "target": "conversion", "kind": "dependency"})

    level2_states = []
    if level2_manifest is not None or level2_evidence is not None or level2_bindings is not None:
        if level2_manifest is None or level2_evidence is None or level2_bindings is None:
            raise ValueError("Level 2 manifest, evidence, and bindings must be supplied together")
        if any(cfg["artifact"] != document["artifact"]
               for document in (level2_manifest, level2_evidence, level2_bindings)):
            raise ValueError("CFG and Level 2 artifact identities differ")
        level2_observed = {}
        for vector in level2_evidence["vectors"]:
            for measured in vector["instances"]:
                slot = level2_observed.setdefault(measured["id"], {
                    "vectors": [], "owned": set(), "extent": set(), "exits": set(),
                })
                if measured["entryReached"]:
                    slot["vectors"].append(vector["label"])
                slot["owned"].update(measured["executedOwnedPcs"])
                slot["extent"].update(measured["executedExtentPcs"])
                slot["exits"].update(tuple(edge) for edge in measured["observedExitTransitions"])
        level2_bindings_by_id = {
            row["id"]: row["bindings"] for row in level2_bindings["instances"]
        }
        for row in level2_manifest["instances"]:
            capture = level2_observed[row["id"]]
            source = row["functionInstanceIdentity"]["function"]["declaration"]
            boundary_id = "level2-" + row["id"].replace(":", "-")
            boundary_bindings = level2_bindings_by_id[row["id"]]
            local_proof = level2_local_proofs.get(row["id"], "not_started")
            authoring_state = ("proof_revalidation_pending"
                               if local_proof == "proof_revalidation_pending"
                               else "proved"
                               if local_proof == "proved"
                               else "proof_in_progress" if local_proof == "in_progress"
                               else "contract_specified_assumption")
            boundaries.append({
                "id": boundary_id, "instanceId": row["id"], "qualified": row["qualified"],
                "entryPc": row["entryPc"], "instructionPcs": row["instructionPcs"],
                "executionPcs": row["executionPcs"],
                "ownedInstructionCount": row["ownedInstructionCount"],
                "subtreeInstructionCount": row["subtreeInstructionCount"],
                "source": source, "parentInstanceIds": row["parentInstanceIds"],
                "observedVectors": sorted(capture["vectors"]),
                "observedOwnedInstructionCount": len(capture["owned"]),
                "observedExtentInstructionCount": len(capture["extent"]),
                "observedExitTransitions": [list(edge) for edge in sorted(capture["exits"])],
                "dwarfBindings": boundary_bindings,
                "evidenceStatus": "captured",
                "contractStatus": "specified",
                "level0UseStatus": "not_applicable", "proofStatus": local_proof,
                "kernelStatus": ("proved" if local_proof == "proved"
                                 else "not_complete"),
            })
            regions.append({
                "id": boundary_id, "label": row["qualified"],
                "authoringState": authoring_state,
                "blocker": ("None: the exact machine contract is proved unconditionally."
                            if local_proof == "proved"
                            else "Existing exact-byte proof must be rechecked against the regenerated program image."
                            if local_proof == "proof_revalidation_pending"
                            else "Exact Sail proof is in progress."
                            if local_proof == "in_progress"
                            else "Typed contract is specified and remains an hLevel2 assumption."),
                "scope": "selected-child", "pcs": row["executionPcs"],
                "boundaryIds": [boundary_id],
                "evidence": "production entry registers, PCs, memory accesses, and exits captured",
                "preparation": {
                    "liveRegisters": [
                        f"{binding['name']} = x{binding['machineRegister']}"
                        for binding in boundary_bindings if binding["machineRegister"] is not None
                    ],
                    "protectedMemory": [],
                    "prerequisites": ["typed source/spec boundary review"],
                    "sourceIdentity": f"{source['file']}::{source['qualifiedName']}",
                },
            })
            level2_states.append({
                "owner": row["id"], "qualified": row["qualified"],
                "status": authoring_state,
            })

    hlevel3_preparation = None
    if any(row is not None for row in
           (hlevel3_inventory, hlevel3_guidance, hlevel3_admission)):
        if any(row is None for row in
               (hlevel3_inventory, hlevel3_guidance, hlevel3_admission)):
            raise ValueError("all hLevel3 preparation artifacts must be supplied together")
        if any(cfg["artifact"] != document["artifact"] for document in
               (hlevel3_inventory, hlevel3_guidance, hlevel3_admission)):
            raise ValueError("CFG and hLevel3 preparation artifact identities differ")
        guide_by_id = {row["id"]: row for row in hlevel3_guidance["obligations"]}
        admission_by_id = {row["instanceId"]: row for row in hlevel3_admission["instances"]}
        direct_rows = hlevel3_direct_proofs["proofs"] if hlevel3_direct_proofs else []
        direct_by_field = {row["field"]: row for row in direct_rows}
        if len(direct_by_field) != len(direct_rows):
            raise ValueError("duplicate hLevel3 direct-proof field")
        inventory_fields = {row["field"] for row in hlevel3_inventory["proposedLevel3Contracts"]}
        unknown_direct = sorted(set(direct_by_field) - inventory_fields)
        if unknown_direct:
            raise ValueError(f"unknown hLevel3 direct-proof fields: {unknown_direct}")
        hlevel3_preparation = {
            "summary": hlevel3_inventory["summary"],
            "admissionSummary": hlevel3_admission["summary"],
            "proofProgress": {
                "directProofCount": len(direct_by_field),
                "remainingContractCount": len(inventory_fields) - len(direct_by_field),
            },
            "parents": [],
        }
        for parent in hlevel3_inventory["parents"]:
            children = []
            for child in parent["children"]:
                prepared = admission_by_id.get(child.get("instanceId"))
                direct = direct_by_field.get(child.get("level3Field"))
                children.append({
                    **child,
                    "contractFamily": prepared["contractFamily"] if prepared else None,
                    "contractStatus": ("proved_unconditionally" if direct else
                                       prepared["contractStatus"] if prepared else
                                       child["disposition"]),
                    "proofStatus": "proved" if direct else "not_proved",
                    "proofTheorem": direct["theorem"] if direct else None,
                    "observedVectors": prepared["empirical"]["vectors"] if prepared else [],
                })
            obligations = [guide_by_id[row["id"]] for row in parent["glueObligations"]]
            hlevel3_preparation["parents"].append({
                "field": parent["field"], "instanceId": parent["instanceId"],
                "source": parent["source"], "glueInstructionCount": len(parent["gluePcs"]),
                "children": children, "glueObligations": obligations,
                "stagingTheorem": f"resolve_{parent['field']}",
            })

    regions.append({
        "id": "level0-glue", "label": "main parent-owned glue", "authoringState": "local",
        "blocker": "None: the conditional Level 0 theorem and refinement edge are proved.",
        "scope": "parent", "pcs": glue_pcs, "boundaryIds": [],
        "evidence": "production ELF structure and endpoint differential fixtures",
        "preparation": {"liveRegisters": [], "protectedMemory": [],
                        "prerequisites": ["admitted Level 1 bindings"],
                        "sourceIdentity": "deps/zesu/src/zkvm/ssz_decode_root.zig::main"},
    })
    nodes.extend([
        {"id": "glue", "label": "main parent-owned glue", "kind": "parentGlue", "column": 1,
         "status": "proved", "proofStatus": "proved",
         "phase": "level0-glue", "instructionCount": len(glue_pcs),
         "absorbedInlineInstructionCount": absorbed,
         "provedInstructionCount": len(proved_level0_pcs)},
        {"id": "conversion", "label": "exportedContracts_of_level1", "kind": "conversion",
         "column": 2, "status": "proved", "proofStatus": "proved"},
        {"id": "root", "label": "root_compliance", "kind": "parent", "column": 3,
         "status": "conditionally_proven", "proofStatus": "conditionally_proven",
         "description": "Canonical equality between the executed Zesu binary and EVM-Sail decode"},
    ])
    edges.extend([
        {"source": "glue", "target": "conversion", "kind": "dependency"},
        {"source": "conversion", "target": "root", "kind": "dependency"},
    ])

    direct_pcs = set(baseline["coverage"]["directlyDischargedStepPcs"] if baseline else [])
    instructions = []
    for pc in sorted(set(main["pcs"]) | selected_extent):
        row = instruction_by_pc[pc]
        instructions.append({
            "pc": pc, "mnemonic": row["mnemonic"], "operands": row["operands"],
            "successors": block_by_pc[pc]["successors"], "reads": [], "writes": [], "memory": [],
            "owner": "main", "sourceFile": block_by_pc[pc]["sourceFile"],
            "sourceLine": block_by_pc[pc]["sourceLine"],
            "formalManifests": (["hlevel2-direct"] if pc in direct_pcs else []),
            "artifactState": "same-elf",
        })
    return {
        "schemaVersion": 2, "target": flame["machineRegionInputs"]["target"],
        "targetModel": {
            "status": "valid_bare_metal",
            "reason": "ELF uses the fixed memory context and contains no ecall instruction",
        },
        "artifact": cfg["artifact"], "instructions": instructions, "blocks": [],
        "boundaries": boundaries, "manifests": ([{
            "id": "hlevel2-direct", "connection": "root",
            "description": "Exact-PC source declarations in the root_compliance dependency slice",
        }] if baseline else []),
        "formalCoverage": {
            "directPcCount": len(direct_pcs),
            "boundaryRegionPcCount": (baseline["counts"]["boundaryRegionUniquePcs"]
                                      if baseline else len(proved_level0_pcs)),
            "conditionalContractPcCount": (baseline["counts"]["conditionalContractUniquePcs"]
                                           if baseline else 0),
            "endpointPcCount": flame["uniqueProgramTotal"],
        },
        "compilerProvenance": {"state": "same-ELF DWARF"},
        "phases": [{"id": "level0-glue", "label": "main parent-owned glue", "pcs": glue_pcs}],
        "authoringRegions": regions,
        "hLevel3Preparation": hlevel3_preparation,
        "flameProgress": {
            "states": [
                {"owner": main["id"], "qualified": "main", "status": "conditionally_proven"},
                *({"owner": row["id"], "qualified": row["qualified"],
                   "status": level1_local_proofs[row["qualified"]]}
                  for row in manifest["instances"]),
                *level2_states,
            ],
        },
        "refinementGraph": {"nodes": nodes, "edges": edges},
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    for name in ("cfg", "flame", "manifest", "evidence", "bindings", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    for name in ("level2-manifest", "level2-evidence", "level2-bindings"):
        parser.add_argument("--" + name, type=Path)
    parser.add_argument("--hlevel2-baseline", type=Path)
    for name in ("hlevel3-inventory", "hlevel3-guidance", "hlevel3-admission",
                 "hlevel3-direct-proofs"):
        parser.add_argument("--" + name, type=Path)
    parser.add_argument("--flame-progress-output", type=Path)
    args = parser.parse_args()
    documents = [json.loads(getattr(args, name).read_text())
                 for name in ("cfg", "flame", "manifest", "evidence", "bindings")]
    documents.extend(json.loads(getattr(args, name.replace("-", "_")).read_text())
                     if getattr(args, name.replace("-", "_")) else None
                     for name in ("level2-manifest", "level2-evidence", "level2-bindings"))
    result = build(
        *documents,
        baseline=(json.loads(args.hlevel2_baseline.read_text())
                  if args.hlevel2_baseline else None),
        hlevel3_inventory=(json.loads(args.hlevel3_inventory.read_text())
                           if args.hlevel3_inventory else None),
        hlevel3_guidance=(json.loads(args.hlevel3_guidance.read_text())
                          if args.hlevel3_guidance else None),
        hlevel3_admission=(json.loads(args.hlevel3_admission.read_text())
                           if args.hlevel3_admission else None),
        hlevel3_direct_proofs=(json.loads(args.hlevel3_direct_proofs.read_text())
                              if args.hlevel3_direct_proofs else None))
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    if args.flame_progress_output:
        args.flame_progress_output.write_text(
            json.dumps(result["flameProgress"], sort_keys=True, separators=(",", ":")) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
