#!/usr/bin/env python3
"""Generate the exact hLevel3 boundary and parent-glue work inventory."""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path


def owner_pcs(cfg: dict) -> dict[str, list[int]]:
    result = {row["id"]: sorted(set(row["pcs"])) for row in cfg["functionInstances"]}
    result.update({f"fn:0x{row['start']:x}": sorted(
        instruction["pc"] for block in row["blocks"] for instruction in block["instructions"])
        for row in cfg["functions"]})
    return result


def flatten_tree(node: dict, parent_key: str | None = None) -> list[tuple[dict, str | None]]:
    rows = [(node, parent_key)]
    for child in node.get("children", []):
        rows.extend(flatten_tree(child, node["key"]))
    return rows


def subtree_pcs(node: dict, meta: dict, pcs_by_owner: dict[str, list[int]]) -> set[int]:
    details = meta[node["key"]]
    result = set(pcs_by_owner.get(details["machineOwner"], []))
    for child in node.get("children", []):
        result.update(subtree_pcs(child, meta, pcs_by_owner))
    return result


def exact_own_pcs(node: dict, meta: dict, pcs_by_owner: dict[str, list[int]]) -> set[int]:
    details = meta[node["key"]]
    result = set(pcs_by_owner.get(details["machineOwner"], []))
    for child in node.get("children", []):
        result.difference_update(subtree_pcs(child, meta, pcs_by_owner))
    return result


def block_fragments(cfg: dict, pcs: list[int]) -> list[dict]:
    selected = set(pcs)
    result = []
    for function in cfg["functions"]:
        for block in function["blocks"]:
            block_pcs = [row["pc"] for row in block["instructions"] if row["pc"] in selected]
            if not block_pcs:
                continue
            runs = []
            current = [block_pcs[0]]
            for pc in block_pcs[1:]:
                if pc == current[-1] + 4:
                    current.append(pc)
                else:
                    runs.append(current)
                    current = [pc]
            runs.append(current)
            for run in runs:
                result.append({
                    "id": f"glue:0x{run[0]:x}-0x{run[-1]:x}",
                    "entryPc": run[0], "pcs": run, "instructionCount": len(run),
                    "successors": [int(value, 16) for value in block["successors"]],
                    "sourceFile": block["sourceFile"], "sourceLine": block["sourceLine"],
                })
    result.sort(key=lambda row: row["entryPc"])
    return result


def lean_field(identifier: str, qualified: str) -> str:
    safe_name = "".join(character if character.isalnum() else "_" for character in qualified)
    safe_id = identifier.replace(":", "_")
    return f"{safe_name}_{safe_id}"


def build(cfg: dict, flame: dict, manifest: dict, level3_manifest: dict, evidence: dict,
          level3_evidence: dict, clauses: dict, targets: dict) -> dict:
    artifacts = (cfg["artifact"], manifest["artifact"], level3_manifest["artifact"],
                 evidence["artifact"], level3_evidence["artifact"])
    if any(artifact != artifacts[0] for artifact in artifacts[1:]):
        raise ValueError("CFG, Level 2 manifest, and evidence artifact identities differ")
    target_rows = targets["targets"]
    if len(target_rows) != 17 or len({row["field"] for row in target_rows}) != 17:
        raise ValueError("hLevel3 preparation must map exactly 17 distinct Level 2 fields")
    manifest_by_id = {row["id"]: row for row in manifest["instances"]}
    target_ids = {row["instanceId"] for row in target_rows}
    absorbed_attributions = {row["instanceId"]: row
                             for row in targets.get("absorbedInlineAttributions", [])}
    if len(absorbed_attributions) != len(targets.get("absorbedInlineAttributions", [])):
        raise ValueError("duplicate absorbed inline attribution")
    level3_rows = [row for row in level3_manifest["instances"]
                   if set(row["parentInstanceIds"]) & target_ids]
    level3_by_id = {row["id"]: row for row in level3_rows}
    closed_children = {row["instanceId"]: row["theorem"]
                       for row in targets.get("unconditionalChildren", [])}
    cfg_by_id = {row["id"]: row for row in cfg["functionInstances"]}
    pcs_by_owner = owner_pcs(cfg)
    flat = flatten_tree(flame["tree"])
    meta = flame["meta"]
    nodes_by_owner: dict[str, list[dict]] = defaultdict(list)
    child_owners: dict[str, set[str]] = defaultdict(set)
    parent_by_key = {}
    for node, parent_key in flat:
        parent_by_key[node["key"]] = parent_key
        details = meta[node["key"]]
        nodes_by_owner[details["machineOwner"]].append(node)
        child_owners[details["machineOwner"]].update(
            meta[child["key"]]["machineOwner"] for child in node.get("children", []))

    def complete_owner_subtree(owner: str, active: frozenset[str] = frozenset()) -> set[int]:
        if owner in active:
            return set(pcs_by_owner.get(owner, []))
        result = set(pcs_by_owner.get(owner, []))
        for child_owner in child_owners[owner]:
            result.update(complete_owner_subtree(child_owner, active | {owner}))
        return result
    def observations(document: dict) -> dict[str, dict]:
        observed: dict[str, dict] = defaultdict(lambda: {"vectors": set(), "entries": 0,
                                                          "owned": set(), "extent": set(),
                                                          "exits": set()})
        for vector in document["vectors"]:
            for row in vector["instances"]:
                slot = observed[row["id"]]
                if row["entryReached"]:
                    slot["entries"] += 1
                    slot["vectors"].add(vector["label"])
                slot["owned"].update(row["executedOwnedPcs"])
                slot["extent"].update(row["executedExtentPcs"])
                slot["exits"].update(tuple(edge) for edge in row["observedExitTransitions"])
        return observed

    observed = observations(evidence)
    level3_observed = observations(level3_evidence)

    parents = []
    selected_ids = set()
    child_route_ids = set()
    consumed_attributions = set()
    total_glue = set()
    for target in target_rows:
        instance_id = target["instanceId"]
        if instance_id in selected_ids:
            raise ValueError(f"duplicate Level 2 target instance: {instance_id}")
        selected_ids.add(instance_id)
        if instance_id not in manifest_by_id or instance_id not in cfg_by_id:
            raise ValueError(f"unknown Level 2 target instance: {instance_id}")
        parent = manifest_by_id[instance_id]
        occurrences = nodes_by_owner.get(instance_id, [])
        if not occurrences:
            raise ValueError(f"Level 2 target is absent from the reviewed flamegraph: {instance_id}")
        occurrence_own = [exact_own_pcs(node, meta, pcs_by_owner) for node in occurrences]
        own = sorted(occurrence_own[0])
        if any(candidate != occurrence_own[0] for candidate in occurrence_own[1:]):
            raise ValueError(f"Level 2 occurrences disagree on parent-owned PCs: {instance_id}")
        if own != sorted(parent["instructionPcs"]):
            raise ValueError(f"Level 2 owned PCs disagree with the CFG: {instance_id}")
        routes = {}
        attribution_glue = set()
        for occurrence in occurrences:
            for child in occurrence.get("children", []):
                child_meta = meta[child["key"]]
                callsite = child_meta.get("callsitePc")
                route_id = f"{instance_id}:{callsite if callsite is not None else child_meta['machineOwner']}:{child_meta['machineOwner']}"
                route = routes.setdefault(route_id, {
                    "id": route_id, "machineOwner": child_meta["machineOwner"],
                    "qualified": child_meta["qualified"], "callsitePc": callsite,
                    "entryPcs": set(), "occurrencePaths": [], "ownPcs": set(),
                    "subtreePcs": set(),
                    "subtreeInstructionCount": child["value"],
                    "sourceFile": child_meta.get("file"), "sourceLine": child_meta.get("line"),
                    "inline": child_meta["kind"] == "inlinedFunctionInstance",
                })
                route["entryPcs"].update(child_meta.get("entries", []))
                route["occurrencePaths"].append(child["key"])
                route["ownPcs"].update(exact_own_pcs(child, meta, pcs_by_owner))
                route["subtreePcs"].update(complete_owner_subtree(child_meta["machineOwner"]))
        child_rows = []
        for route_id, route in sorted(routes.items()):
            if route_id in child_route_ids:
                raise ValueError(f"duplicate canonical Level 3 child route: {route_id}")
            child_route_ids.add(route_id)
            route["entryPcs"] = sorted(route["entryPcs"])
            route["occurrencePaths"] = sorted(set(route["occurrencePaths"]))
            route["ownPcs"] = sorted(route["ownPcs"])
            route["subtreePcs"] = sorted(route["subtreePcs"])
            route["occurrenceCount"] = len(route["occurrencePaths"])
            owner = route["machineOwner"]
            if owner in absorbed_attributions:
                correction = absorbed_attributions[owner]
                if (correction["parentInstanceId"] != instance_id or
                        correction["qualified"] != route["qualified"] or
                        sorted(correction["executionPcs"]) != route["subtreePcs"] or
                        route["ownPcs"]):
                    raise ValueError(f"absorbed inline attribution disagrees with {owner}")
                attribution_glue.update(route["subtreePcs"])
                consumed_attributions.add(owner)
                continue
            if owner in level3_by_id:
                route["disposition"] = "level3-assumption"
                route["level3Field"] = lean_field(owner, level3_by_id[owner]["qualified"])
            elif owner in target_ids:
                route["disposition"] = "level2-sibling-dependency"
                route["level2Field"] = next(
                    row["field"] for row in target_rows if row["instanceId"] == owner)
            elif owner in closed_children:
                route["disposition"] = "unconditional-child-proof"
                route["theorem"] = closed_children[owner]
            else:
                raise ValueError(f"Level 3 child has no proof disposition: {owner}")
            child_rows.append(route)
        absorbed = sorted(set(parent["absorbedInstructionPcs"]))
        glue = sorted(set(own) | set(absorbed) | attribution_glue)
        covered = set(glue)
        for route in child_rows:
            covered.update(route["subtreePcs"])
        if covered != set(parent["executionPcs"]):
            missing = sorted(set(parent["executionPcs"]) - covered)
            extra = sorted(covered - set(parent["executionPcs"]))
            raise ValueError(
                f"Level 3 children and parent glue do not cover {instance_id}: "
                f"missing={missing[:8]} extra={extra[:8]}")
        schema = clauses["schemas"].get(target["schema"])
        if schema is None:
            raise ValueError(f"unknown contract schema: {target['schema']}")
        capture = observed[instance_id]
        fragments = block_fragments(cfg, glue)
        total_glue.update(glue)
        parents.append({
            **target, "qualified": parent["qualified"], "entryPc": parent["entryPc"],
            "ownedPcs": own, "ownedInstructionCount": len(own),
            "absorbedGluePcs": absorbed, "gluePcs": glue,
            "executionPcs": parent["executionPcs"],
            "subtreeInstructionCount": parent["subtreeInstructionCount"],
            "source": parent["functionInstanceIdentity"]["function"]["declaration"],
            "inlineStack": parent["functionInstanceIdentity"]["inlineStack"],
            "glueObligations": fragments, "children": child_rows,
            "contractClauses": schema["clauses"],
            "evidence": {"entryCount": capture["entries"],
                         "vectors": sorted(capture["vectors"]),
                         "observedOwnedPcs": sorted(capture["owned"]),
                         "observedExtentPcs": sorted(capture["extent"]),
                         "observedExitTransitions": [list(edge) for edge in sorted(capture["exits"])]},
        })
    if consumed_attributions != set(absorbed_attributions):
        missing = sorted(set(absorbed_attributions) - consumed_attributions)
        raise ValueError(f"unused absorbed inline attributions: {missing}")
    dependencies = {row["field"]: set() for row in parents}
    for parent in parents:
        dependencies[parent["field"]].update(
            child["level2Field"] for child in parent["children"]
            if child["disposition"] == "level2-sibling-dependency")
    ready = sorted(field for field, needs in dependencies.items() if not needs)
    resolution_order = []
    remaining = {field: set(needs) for field, needs in dependencies.items()}
    while ready:
        field = ready.pop(0)
        if field in resolution_order:
            continue
        resolution_order.append(field)
        for candidate in sorted(remaining):
            remaining[candidate].discard(field)
            if not remaining[candidate] and candidate not in resolution_order:
                ready.append(candidate)
        ready.sort()
    if len(resolution_order) != len(parents):
        cycle = sorted(set(remaining) - set(resolution_order))
        raise ValueError(f"Level 2 sibling contract dependency cycle: {cycle}")
    proposed = []
    for row in level3_rows:
        if row["id"] in absorbed_attributions:
            continue
        capture = level3_observed[row["id"]]
        jump_table = next((table for table in cfg.get("resolvedJumpTables", [])
                           if table["source"] in row["executionPcs"]), None)
        proposed.append({
            "field": lean_field(row["id"], row["qualified"]),
            "instanceId": row["id"], "qualified": row["qualified"], "entryPc": row["entryPc"],
            "parentInstanceIds": sorted(set(row["parentInstanceIds"]) & target_ids),
            "source": row["functionInstanceIdentity"]["function"]["declaration"],
            "inlineStack": row["functionInstanceIdentity"]["inlineStack"],
            "ownedPcs": row["instructionPcs"], "executionPcs": row["executionPcs"],
            "exitPcs": row["exitPcs"],
            "jumpTableTargets": jump_table["targets"] if jump_table else [],
            "evidence": {"entryCount": capture["entries"],
                         "vectors": sorted(capture["vectors"]),
                         "observedOwnedPcs": sorted(capture["owned"]),
                         "observedExtentPcs": sorted(capture["extent"]),
                         "observedExitTransitions": [list(edge) for edge in sorted(capture["exits"])]},
        })
    return {
        "schemaVersion": 1, "artifact": cfg["artifact"],
        "summary": {"level2FieldCount": len(parents),
                    "level3ChildRouteCount": sum(len(row["children"]) for row in parents),
                    "level3ContractCount": len(proposed),
                    "parentGlueInstructionCount": len(total_glue),
                    "parentGlueObligationCount": sum(len(row["glueObligations"]) for row in parents)},
        "proposedLevel3Contracts": proposed,
        "level2ResolutionOrder": resolution_order,
        "parents": parents,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    for name in ("cfg", "flame", "manifest", "level3-manifest", "evidence", "level3-evidence", "clauses", "targets", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    inputs = [json.loads(getattr(args, name).read_text())
              for name in ("cfg", "flame", "manifest", "level3_manifest", "evidence", "level3_evidence", "clauses", "targets")]
    result = build(*inputs)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
