#!/usr/bin/env python3
"""Classify proposed Level 3 instances by the cheapest sound refinement strategy."""

import argparse
import json
import re
from pathlib import Path


DIRECT_NOW = {
    "mem.readInt": "ten-instruction leaf; prove one shared fixed-width read theorem",
    "mem.writeInt": "one-instruction leaf; reuse the staged store contract",
    "ssz.forkNameFromSchemaByte": "twelve-instruction leaf with finite result branches",
    "ssz.decode__struct_1051.f": "one contiguous checked-slice machine region",
}

NON_CONTIGUOUS_RETAIN = {
    "fi:1:34fd": "later machine region needs a typed re-entry contract",
    "fi:1:3541": "entry jump and later machine region need a typed re-entry contract",
    "fi:1:3566": "entry exit and later machine region need a typed re-entry contract",
    "fi:1:358b": "later machine region needs a typed re-entry contract",
}

DIRECT_AFTER = {
    "ssz.readU32": "wrapper around the shared mem.readInt leaf",
    "ssz.readU64": "wrapper around the shared mem.readInt leaf",
    "extern_io.write_output": "3-5 owned instructions around the proved write_output leaf",
    "ssz_decode_observation.Encoder.raw": "wrapper around extern_io.write_output",
    "ssz_decode_observation.Encoder.int": "wrapper around mem.writeInt and Encoder.raw",
    "ssz_decode_observation.Encoder.optionalU128":
        "12 owned instructions around reviewed Boolean and integer encoders",
    "ssz_decode_observation.Encoder.optionalAddress":
        "13 owned instructions around reviewed Boolean and raw encoders",
    "ssz.decodeWithdrawal": "fixed-record decoder with three shared mem.readInt children",
}

RETAIN = {
    "mem.Allocator.alloc__anon_1045": "allocator subtree delegates to allocAdvancedWithRetAddr",
    "mem.Allocator.alloc__anon_1151": "allocator subtree delegates to allocAdvancedWithRetAddr",
    "mem.Allocator.alloc__anon_1173": "allocator subtree delegates to allocAdvancedWithRetAddr",
    "mem.Allocator.alloc__anon_1432": "allocator subtree delegates to allocAdvancedWithRetAddr",
    "mem.Allocator.dupe__anon_1128": "allocator copy has allocation and memcpy descendants",
    "ssz.decodeByteListList": "runtime-sized offset loop and allocator descendants",
    "rlp_decode.decodeSingleTx": "large RLP subtree with several parser children",
    "ssz_decode_observation.Encoder.accessList": "runtime-sized collection encoder",
    "ssz_decode_observation.Encoder.authorizations": "runtime-sized collection encoder",
}


def classify(qualified: str) -> tuple[str, str]:
    if qualified in DIRECT_NOW:
        return "direct-now", DIRECT_NOW[qualified]
    if qualified in DIRECT_AFTER:
        return "direct-after-dependencies", DIRECT_AFTER[qualified]
    if qualified in RETAIN:
        return "retain-contract", RETAIN[qualified]
    raise ValueError(f"unreviewed Level 3 source operation: {qualified}")


def classify_instance(instance_id: str, qualified: str) -> tuple[str, str]:
    """Classify one exact machine instance, including reviewed re-entry exceptions."""
    if instance_id in NON_CONTIGUOUS_RETAIN:
        if qualified != "ssz.decode__struct_1051.f":
            raise ValueError(f"re-entry exception changed source operation: {instance_id}")
        return "retain-contract", NON_CONTIGUOUS_RETAIN[instance_id]
    return classify(qualified)


def flame_nodes(tree: dict) -> dict[str, dict]:
    result = {}
    pending = [tree]
    while pending:
        node = pending.pop()
        match = re.search(r"\[(fi:[^]]+)\]$", node.get("name", ""))
        if match and node.get("value", 0) >= result.get(match.group(1), {}).get("value", -1):
            result[match.group(1)] = node
        pending.extend(node.get("children", []))
    return result


def flame_meta_instances(flame: dict) -> set[str]:
    """Return machine-owner ids, including shared bodies expanded at several call sites."""
    meta = flame.get("meta", [])
    if not isinstance(meta, list):
        return set()
    return {
        item["machineOwner"]
        for item in meta
        if isinstance(item, dict) and item.get("machineOwner", "").startswith("fi:")
    }


def child_source_name(name: str) -> str:
    return name.split(" @", 1)[0].split(" [", 1)[0]


def validate_direct_children(qualified: str, children: list[str]) -> None:
    names = [child_source_name(name) for name in children]
    expected = {
        "ssz.readU32": {"mem.readInt"},
        "ssz.readU64": {"mem.readInt"},
        "extern_io.write_output": {"write_output"},
        "ssz_decode_observation.Encoder.raw": {"extern_io.write_output"},
        "ssz_decode_observation.Encoder.int": {
            "mem.writeInt", "ssz_decode_observation.Encoder.raw"},
        "ssz_decode_observation.Encoder.optionalU128": {
            "ssz_decode_observation.Encoder.boolean",
            "ssz_decode_observation.Encoder.int__anon_1645"},
        "ssz_decode_observation.Encoder.optionalAddress": {
            "ssz_decode_observation.Encoder.boolean", "ssz_decode_observation.Encoder.raw"},
        "ssz.decodeWithdrawal": {"mem.readInt"},
    }
    if qualified in DIRECT_NOW and names:
        raise ValueError(f"direct leaf {qualified} has children: {names}")
    if qualified in expected and set(names) != expected[qualified]:
        raise ValueError(f"unexpected children for {qualified}: {names}")


def render(inventory: dict, flames: list[dict]) -> str:
    nodes = {}
    meta_instances = set()
    for flame in flames:
        meta_instances.update(flame_meta_instances(flame))
        for instance_id, node in flame_nodes(flame["tree"]).items():
            if node.get("value", 0) >= nodes.get(instance_id, {}).get("value", -1):
                nodes[instance_id] = node
    rows = []
    for item in inventory["proposedLevel3Contracts"]:
        disposition, reason = classify_instance(item["instanceId"], item["qualified"])
        node = nodes.get(item["instanceId"])
        if (disposition != "retain-contract" and node is None
                and item["instanceId"] not in meta_instances):
            raise ValueError(f"missing flame node for direct candidate {item['instanceId']}")
        children = [] if node is None else [child["name"] for child in node.get("children", [])]
        if disposition != "retain-contract" and node is not None:
            validate_direct_children(item["qualified"], children)
        rows.append({
            "id": item["instanceId"],
            "qualified": item["qualified"],
            "entry": item["entryPc"],
            "execution": len(item["executionPcs"]),
            "owned": len(item["ownedPcs"]),
            "observed": item["evidence"]["entryCount"],
            "disposition": disposition,
            "reason": reason,
        })
    counts = {name: sum(row["disposition"] == name for row in rows) for name in (
        "direct-now", "direct-after-dependencies", "retain-contract")}
    if len(rows) != 57 or counts != {
            "direct-now": 4, "direct-after-dependencies": 40, "retain-contract": 13}:
        raise ValueError(f"review coverage changed: instances={len(rows)}, counts={counts}")
    lines = [
        "# Level 3 direct-discharge review",
        "",
        "This report classifies every proposed Level 3 instance. `direct-now` instances have no",
        "unresolved child proof. `direct-after-dependencies` instances become direct proofs after",
        "the named shared leaf or wrapper proof exists. `retain-contract` instances keep a Level 3",
        "assumption because they contain a runtime loop, a large parser, an unresolved allocator,",
        "or a machine region that requires typed re-entry.",
        "The validator also accepts a shared concrete body when the core flame metadata records its",
        "machine owner at expanded call sites. The current tree uses this form for `fi:1:43a9`.",
        "",
        f"Counts: {counts['direct-now']} direct now; "
        f"{counts['direct-after-dependencies']} direct after shared dependencies; "
        f"{counts['retain-contract']} retained contracts.",
        "",
        "| Instance | Source operation | Entry | Execution | Owned | Observed | Decision | Reason |",
        "|---|---|---:|---:|---:|---:|---|---|",
    ]
    for row in sorted(rows, key=lambda value: (value["disposition"], value["entry"])):
        lines.append(
            f"| `{row['id']}` | `{row['qualified']}` | `0x{row['entry']:x}` | "
            f"{row['execution']} | {row['owned']} | {row['observed']} | "
            f"{row['disposition']} | {row['reason']} |")
    lines.extend([
        "",
        "## Recommended proof order",
        "",
        "1. Prove generic `mem.readInt`, staged `mem.writeInt`, fork-name, and the one contiguous checked-slice region.",
        "2. Discharge all `ssz.readU32`, `ssz.readU64`, and `extern_io.write_output` wrappers.",
        "3. Discharge `Encoder.raw`, then `Encoder.int`, then the two optional encoders.",
        "4. Discharge `ssz.decodeWithdrawal` with the shared integer-read theorem.",
        "5. Keep assumptions for nine large instances and four checked-slice re-entry instances.",
        "",
        "A direct proof still needs a local semantic theorem statement. It avoids exposing that",
        "statement as an `hLevel3` premise and avoids a second refinement level for the wrapper.",
        "",
    ])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--inventory", required=True, type=Path)
    parser.add_argument("--flame", required=True, action="append", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    inventory = json.loads(args.inventory.read_text())
    flames = [json.loads(path.read_text()) for path in args.flame]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(render(inventory, flames))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
