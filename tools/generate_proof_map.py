#!/usr/bin/env python3
"""Join production machine geometry, kernel-linked manifests, and authoring metadata."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
from collections import Counter
from pathlib import Path


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def analyzer_module(path: Path):
    spec = importlib.util.spec_from_file_location("machine_proof_corridors", path)
    if spec is None or spec.loader is None:
        raise ValueError(f"cannot load corridor analyzer: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def basic_blocks(instructions: list[dict], owned: set[int]) -> list[dict]:
    rows = {row["address"]: row for row in instructions if row["address"] in owned}
    predecessors: Counter[int] = Counter(
        successor for row in rows.values() for successor in row["successors"] if successor in owned
    )
    leaders = {min(owned)}
    for row in rows.values():
        internal = [successor for successor in row["successors"] if successor in owned]
        if len(internal) != 1 or internal[0] != row["address"] + 4:
            leaders.update(internal)
        for successor in internal:
            if predecessors[successor] != 1:
                leaders.add(successor)
    blocks = []
    consumed: set[int] = set()
    for leader in sorted(leaders):
        if leader in consumed:
            continue
        pcs = []
        pc = leader
        while pc in rows and pc not in consumed:
            pcs.append(pc); consumed.add(pc)
            successors = [successor for successor in rows[pc]["successors"] if successor in owned]
            if len(successors) != 1 or successors[0] != pc + 4 or successors[0] in leaders:
                break
            pc = successors[0]
        terminal = rows[pcs[-1]]
        blocks.append({
            "id": f"block-0x{leader:x}", "entryPc": leader, "pcs": pcs,
            "successors": terminal["successors"],
        })
    for pc in sorted(owned - consumed):
        blocks.append({"id": f"block-0x{pc:x}", "entryPc": pc, "pcs": [pc],
                       "successors": rows[pc]["successors"]})
    return sorted(blocks, key=lambda block: block["entryPc"])


def starter_proof(region: dict, machine_map: dict[int, object]) -> dict | None:
    """Emit an explicitly untrusted Lean outline; every machine obligation remains visible."""
    pcs = region.get("pcs") or region.get("templateQueryPcs")
    if not pcs:
        return None
    rows = [machine_map[pc] for pc in pcs]
    wrapper_kind = {
        "sd": "decoderStoreDwordStep",
        "sh": "decoderStoreHalfStep",
        "ld": "decoderLoadStepOfDecoderAgree",
        "lbu": "decoderLoadStepOfDecoderAgree",
        "jal": "decoderJumpStep",
        "jalr": "decoderRetStep",
    }
    lines = ["-- UNTRUSTED STARTER: replace every obligation before declaring a theorem.",
             "obtain ⟨_, seg⟩ := Seg.nil (atPc := by exact pre.atPc)"]
    for row in rows:
        wrapper = wrapper_kind.get(row.mnemonic, "decoderITypeStepOfDecoderAgree")
        lines.extend([
            f"-- 0x{row.pc:x}: {row.mnemonic} {row.operands}",
            f"obtain ⟨run, _step⟩ := {wrapper} (pc := 0x{row.pc:x})",
            "  (access := by TODO) (alignment := by TODO) (frame := by TODO)",
            "-- Append with Seg.step / Seg.stepStoreWitness and retain live register bindings.",
        ])
    return {"trust": "authoring-suggestion", "language": "lean4", "text": "\n".join(lines)}


def generate(machine: dict, boundaries: dict, manifests: dict, authoring: dict,
             lean_root: Path, analyzer_path: Path, llvm_ir: Path | None = None) -> dict:
    if manifests.get("schemaVersion") != 1 or authoring.get("schemaVersion") != 1:
        raise ValueError("unsupported proof-map input schema")
    owner = next(row for row in machine["callGraph"]["owners"]
                 if row["qualified"] == "ssz_raw.decodeRaw")
    owned = set(owner["instructions"])
    if len(owned) != 172 or manifests.get("ownerInstructionCount") != 172:
        raise ValueError("decodeRaw direct-owner inventory is not 172 PCs")
    instruction_rows = {row["address"]: row for row in machine["instructions"]}
    manifest_pcs: set[int] = set()
    pc_manifests: dict[int, list[str]] = {}
    for manifest in manifests["manifests"]:
        pcs = manifest["pcs"]
        if len(pcs) != len(set(pcs)) or not set(pcs) <= owned:
            raise ValueError(f"manifest {manifest['id']} has duplicate or non-parent PCs")
        overlap = manifest_pcs & set(pcs)
        if overlap:
            raise ValueError(f"formal manifests overlap at {sorted(overlap)}")
        manifest_pcs.update(pcs)
        for pc in pcs:
            pc_manifests.setdefault(pc, []).append(manifest["id"])
    formal = manifests["formalCoverage"]
    if formal["localPcCount"] != len(manifest_pcs):
        raise ValueError("formal local coverage count does not equal the exact manifest union")
    phase_by_pc: dict[int, str] = {}
    for phase in manifests.get("phases", []):
        for pc in phase["pcs"]:
            if pc in phase_by_pc or pc not in owned:
                raise ValueError(f"invalid Level 4 phase PC 0x{pc:x}")
            phase_by_pc[pc] = phase["id"]
    if set(phase_by_pc) != owned:
        raise ValueError("Level 4 phases do not partition the 172 parent PCs")

    boundary_by_qualified: dict[str, list[dict]] = {}
    for boundary in boundaries["boundaries"]:
        boundary_by_qualified.setdefault(boundary["qualified"], []).append(boundary)
    analyzer = analyzer_module(analyzer_path)
    machine_map = analyzer.machine_instructions_from_document(machine)
    corridors = analyzer.lean_corridors(lean_root, machine_map)
    regions = []
    for region in authoring["regions"]:
        row = dict(region)
        if row["scope"] == "parent" and not set(row.get("pcs", [])) <= owned:
            raise ValueError(f"parent authoring region {row['id']} contains non-parent PCs")
        qualified = row.get("boundaryQualified")
        if qualified:
            matches = boundary_by_qualified.get(qualified, [])
            if not matches:
                raise ValueError(f"authoring region {row['id']} names an absent boundary")
            row["boundaryIds"] = [match["id"] for match in matches]
            row["boundaryInstructionCount"] = sum(len(match["instructionPcs"]) for match in matches)
        query = tuple(row.get("templateQueryPcs", []))
        row["templateMatches"] = analyzer.retrieve(corridors, machine_map, query, 3) if query else []
        packet_pcs = row.get("pcs") or list(query)
        packet_rows = [machine_map[pc] for pc in packet_pcs]
        packet_artifact_rows = [instruction_rows[pc] for pc in packet_pcs]
        row["preparation"] = {
            "instructions": [{"pc": item.pc, "mnemonic": item.mnemonic,
                              "operands": item.operands} for item in packet_rows],
            "liveRegisters": sorted({register for item in packet_artifact_rows
                                     for register in (*item["reads"], *item["writes"])}),
            "successors": sorted({successor for item in packet_rows
                                  for successor in item.successors}),
            "protectedMemory": row.get("protectedMemory", []),
            "prerequisites": row.get("prerequisites", []),
            "sourceIdentity": row.get("sourceIdentity", "ssz_raw.decodeRaw / pinned DWARF"),
        }
        row["starterProof"] = starter_proof(row, machine_map)
        regions.append(row)

    instructions = []
    for pc in sorted(owned):
        machine_row = instruction_rows[pc]
        instructions.append({
            "pc": pc, "mnemonic": machine_row["mnemonic"], "operands": machine_row["operands"],
            "successors": machine_row["successors"], "reads": machine_row["reads"],
            "writes": machine_row["writes"], "memory": machine_row["memory"],
            "sourceFile": owner.get("sourceFile"), "sourceLine": owner.get("declLine"),
            "formalManifests": pc_manifests.get(pc, []),
            "artifactState": "production-elf-validated",
        })
    compiler_provenance = {"state": "unavailable"}
    if llvm_ir is not None:
        compiler_provenance = {
            "state": "explanatory-only",
            "artifact": "optimized LLVM IR",
            "sha256": hashlib.sha256(llvm_ir.read_bytes()).hexdigest(),
        }
    blocks = basic_blocks(machine["instructions"], owned)
    boundary_entries = {row["entryPc"]: row for row in boundaries["boundaries"]}
    boundary_returns: dict[int, list[dict]] = {}
    for boundary in boundaries["boundaries"]:
        for edge in boundary.get("exits", []):
            boundary_returns.setdefault(edge["target"], []).append(boundary)
    for block in blocks:
        block["phase"] = phase_by_pc[block["entryPc"]]
        block["childCalls"] = [{"id": boundary_entries[pc]["id"],
                                "qualified": boundary_entries[pc]["qualified"], "entryPc": pc}
                               for pc in block["successors"] if pc in boundary_entries]
        block["childReturns"] = [{"id": row["id"], "qualified": row["qualified"]}
                                 for row in boundary_returns.get(block["entryPc"], [])]
    return {
        "schemaVersion": 1,
        "owner": {"id": owner["id"], "qualified": owner["qualified"], "entryPc": owner["entryPc"]},
        "trustTracks": ["formal", "artifact", "empirical", "authoring"],
        "compilerProvenance": compiler_provenance,
        "formalCoverage": formal,
        "instructions": instructions,
        "phases": [{"id": row["id"], "label": row["label"], "pcCount": len(row["pcs"])}
                   for row in manifests.get("phases", [])],
        "blocks": blocks,
        "manifests": manifests["manifests"],
        "boundaries": [{"id": row["id"], "qualified": row["qualified"],
                        "entryPc": row["entryPc"], "instructionCount": len(row["instructionPcs"]),
                        "exits": row.get("exits", [])}
                       for row in boundaries["boundaries"]],
        "authoringRegions": regions,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--machine-regions", type=Path, required=True)
    parser.add_argument("--level4-boundaries", type=Path, required=True)
    parser.add_argument("--manifests", type=Path, required=True)
    parser.add_argument("--authoring", type=Path, required=True)
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--analyzer", type=Path, required=True)
    parser.add_argument("--llvm-ir", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    output = generate(load(args.machine_regions), load(args.level4_boundaries), load(args.manifests),
                      load(args.authoring), args.lean_root, args.analyzer, args.llvm_ir)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
