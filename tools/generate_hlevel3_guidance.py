#!/usr/bin/env python3
"""Annotate hLevel3 obligations with proof idioms, motifs, and proved examples."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path

from analyze_machine_proof_corridors import Corridor, Instruction as CorridorInstruction
from analyze_machine_proof_corridors import lean_corridors, score
from ngram_motifs import alpha_rename, dag_canonical_form, load_zesu_cfg


def matches(idiom: dict, instructions: list) -> bool:
    shape = idiom["shape"]
    if len(instructions) < shape.get("minimumLength", 0):
        return False
    mnemonics = shape.get("mnemonics")
    if mnemonics and not any(row.mnemonic in mnemonics for row in instructions):
        return False
    classes = shape.get("instructionClasses")
    if classes and "*" not in classes and not any(row.klass in classes for row in instructions):
        return False
    transfers = shape.get("transfers")
    if transfers and not any(row.transfer in transfers for row in instructions):
        return False
    return True


def corridor_machine(cfg: dict, instructions: list) -> dict[int, CorridorInstruction]:
    raw = {row["pc"]: row for function in cfg["functions"] for block in function["blocks"]
           for row in block["instructions"]}
    return {
        row.address: CorridorInstruction(
            pc=row.address, mnemonic=row.mnemonic, operands=raw[row.address]["operands"],
            writes=row.writes, memory=row.memory, successors=(), transfer=row.transfer)
        for row in instructions
    }


def proved_matches(query_pcs: list[int], corridors: list[Corridor], machine: dict) -> list[dict]:
    query = Corridor("<query>", "query", tuple(query_pcs),
                     tuple(machine[pc] for pc in query_pcs), ())
    candidates = [row for row in corridors if row.composition_backed and row.pcs != tuple(query_pcs)]
    candidates.sort(key=lambda row: (score(query, row), row.module, row.name), reverse=True)
    return [{"score": score(query, row), "module": row.module, "pcList": row.name,
             "composingTheorems": list(row.composing_theorems), "pcs": list(row.pcs)}
            for row in candidates]


def repeated_motifs(obligations: list[dict], instruction_by_pc: dict) -> tuple[list[dict], int]:
    groups: dict[tuple[str, ...], list[dict]] = defaultdict(list)
    for obligation in obligations:
        body = [instruction_by_pc[pc] for pc in obligation["pcs"]]
        for length in range(2, len(body) + 1):
            for offset in range(len(body) - length + 1):
                window = body[offset:offset + length]
                signature = tuple(alpha_rename(window))
                groups[signature].append({
                    "obligationId": obligation["id"], "startPc": window[0].address,
                    "pcs": [row.address for row in window], "instructions": window,
                })
    result = []
    for signature, sites in groups.items():
        distinct = {(site["obligationId"], site["startPc"]): site for site in sites}
        sites = [distinct[key] for key in sorted(distinct)]
        if len(sites) < 2:
            continue
        transfers = sorted({row.transfer for site in sites for row in site["instructions"]
                            if row.transfer != "ordinary"})
        digest = hashlib.sha256("\n".join(signature).encode()).hexdigest()[:16]
        result.append({
            "id": "motif:" + digest, "length": len(signature), "signature": list(signature),
            "siteCount": len(sites), "ownerCount": len({site["obligationId"] for site in sites}),
            "sites": [{key: value for key, value in site.items() if key != "instructions"}
                      for site in sites],
            "transfers": transfers,
            "disposition": ("existing-idiom-sequence" if not transfers
                            else "review-control-transfer-before-shared-lemma"),
        })
    raw_count = len(result)
    result.sort(key=lambda row: (-row["length"], -row["siteCount"], row["id"]))
    claimed: set[tuple[str, int]] = set()
    selected = []
    for motif in result:
        usable = [site for site in motif["sites"]
                  if all((site["obligationId"], pc) not in claimed for pc in site["pcs"])]
        if len(usable) < 2:
            continue
        motif["sites"] = usable
        motif["siteCount"] = len(usable)
        motif["ownerCount"] = len({site["obligationId"] for site in usable})
        for site in usable:
            claimed.update((site["obligationId"], pc) for pc in site["pcs"])
        evaluated = usable[:2] if motif["length"] <= 8 else []
        forms = {dag_canonical_form(
            [instruction_by_pc[pc] for pc in site["pcs"]], leaf_budget=16) for site in evaluated}
        motif["dataflowCanonical"] = next(iter(forms)) if evaluated and len(forms) == 1 else None
        motif["dataflowFormCount"] = len(forms)
        motif["dataflowEvaluatedSiteCount"] = len(evaluated)
        motif["dataflowStatus"] = ("candidate-match" if evaluated and len(forms) == 1 else
                                   "candidate-mismatch" if evaluated else
                                   "not-run-length-over-8")
        selected.append(motif)
    return selected, raw_count


def build(inventory: dict, cfg: dict, catalogue: dict, lean_root: Path) -> dict:
    if inventory["artifact"] != cfg["artifact"]:
        raise ValueError("hLevel3 inventory and CFG artifact identities differ")
    families = {row["family"] for row in catalogue["idioms"]}
    missing_families = set(catalogue["requiredFamilies"]) - families
    if missing_families:
        raise ValueError(f"idiom catalogue misses required families: {sorted(missing_families)}")
    ids = [row["id"] for row in catalogue["idioms"]]
    if len(ids) != len(set(ids)):
        raise ValueError("idiom catalogue contains duplicate identifiers")
    instructions, _ = load_zesu_cfg(Path(cfg.pop("__path__"))) if "__path__" in cfg else (None, None)
    if instructions is None:
        raise ValueError("CFG input path is required for instruction analysis")
    instruction_by_pc = {row.address: row for row in instructions}
    machine = corridor_machine(cfg, instructions)
    corridors = lean_corridors(lean_root, machine)
    obligations = []
    def api(hint: dict) -> dict:
        if "declaration" in hint:
            return {"kind": "declaration", "name": hint["declaration"]}
        return {"kind": "tactic", "name": hint["syntax"]}

    for parent in inventory["parents"]:
        for fragment in parent["glueObligations"]:
            body = [instruction_by_pc[pc] for pc in fragment["pcs"]]
            hints = [row for row in catalogue["idioms"] if matches(row, body)]
            hints.sort(key=lambda row: (row["priority"], row["id"]))
            by_family: dict[str, list[dict]] = defaultdict(list)
            for hint in hints:
                by_family[hint["family"]].append({
                    "id": hint["id"], "api": api(hint),
                    "reason": hint["goal"], "restrictions": hint["restrictions"],
                })
            obligations.append({
                **fragment, "parentField": parent["field"], "parentInstanceId": parent["instanceId"],
                "instructionClasses": [row.klass for row in body],
                "mnemonics": [row.mnemonic for row in body],
                "transfers": [row.transfer for row in body],
                "idiomHints": [{"id": row["id"], "api": api(row),
                                "reason": row["goal"], "restrictions": row["restrictions"]}
                               for row in hints],
                "preferredStrategy": {
                    "composition": by_family.get("segment-composition", [])[:2],
                    "instructionSteps": by_family.get("instruction-class", []),
                    "frames": [*by_family.get("register-frame", []),
                               *by_family.get("memory-frame", []),
                               *by_family.get("representation-transport", [])],
                    "support": [*by_family.get("exact-site", []),
                                *by_family.get("configured-context", []),
                                *by_family.get("owned-region", []),
                                *by_family.get("automation", [])],
                },
                "closestProvedCorridors": proved_matches(fragment["pcs"], corridors, machine),
            })
    motifs, analyzed_motif_count = repeated_motifs(obligations, instruction_by_pc)
    motifs_by_obligation: dict[str, list[str]] = defaultdict(list)
    for motif in motifs:
        for site in motif["sites"]:
            motifs_by_obligation[site["obligationId"]].append(motif["id"])
    for obligation in obligations:
        obligation["motifIds"] = sorted(set(motifs_by_obligation[obligation["id"]]))
        if not obligation["idiomHints"]:
            obligation["disposition"] = "unmatched-proof-api"
        elif obligation["motifIds"]:
            obligation["disposition"] = "existing-idiom-plus-motif-review"
        else:
            obligation["disposition"] = "existing-idiom"
    child_groups: dict[tuple[str, tuple[str, ...]], list[dict]] = defaultdict(list)
    for parent in inventory["parents"]:
        for child in parent["children"]:
            child_body = [instruction_by_pc[pc] for pc in child["subtreePcs"]]
            signature = tuple(alpha_rename(child_body))
            child_groups[(child["qualified"], signature)].append({
                "parentField": parent["field"], "routeId": child["id"],
                "machineOwner": child["machineOwner"], "callsitePc": child["callsitePc"],
            })
    sibling_groups = [{"qualified": key[0], "normalizedInstructions": list(key[1]),
                       "occurrences": value, "reuseClass": "normalized-machine-shape"}
                      for key, value in child_groups.items() if len(value) > 1]
    sibling_groups.sort(key=lambda row: (-len(row["occurrences"]), row["qualified"],
                                        row["normalizedInstructions"]))
    return {
        "schemaVersion": 1, "artifact": inventory["artifact"],
        "summary": {"obligationCount": len(obligations), "idiomCount": len(catalogue["idioms"]),
                    "analyzedMotifCount": analyzed_motif_count,
                    "selectedMotifCount": len(motifs),
                    "unmatchedObligationCount": sum(row["disposition"] == "unmatched-proof-api"
                                                    for row in obligations),
                    "exactSiblingGroupCount": len(sibling_groups)},
        "idiomCatalogue": catalogue, "obligations": obligations,
        "motifs": motifs, "exactSiblingGroups": sibling_groups,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    for name in ("inventory", "cfg", "catalogue", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--lean-root", type=Path, default=Path("BinaryFv/Zesu/MachineExecution"))
    args = parser.parse_args()
    inventory = json.loads(args.inventory.read_text())
    cfg = json.loads(args.cfg.read_text())
    cfg["__path__"] = str(args.cfg)
    result = build(inventory, cfg, json.loads(args.catalogue.read_text()), args.lean_root)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
