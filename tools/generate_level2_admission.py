#!/usr/bin/env python3
"""Join Level 2 source semantics with measured production-boundary evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from generate_level2_lean import source_name


SEMANTICS = {
    "memcpy": ("byte-copy", "dst[0..n] becomes src[0..n]", "C memcpy loop"),
    "sszDecode": ("ssz-and-transaction-decode",
                  "decode StatelessInput and eagerly decode transaction RLP",
                  "EVM-Sail StatelessInput and transaction decoders modulo knownBugs"),
    "writeSuccessRawLine131": ("observation-write", "append ZSSZ v1 success prefix", "ZSSZ format"),
    "writeSuccessRawLine135": ("observation-write", "append parent_hash bytes", "ZSSZ format"),
    "writeSuccessRawLine136": ("observation-write", "append fee_recipient bytes", "ZSSZ format"),
    "writeSuccessRawLine137": ("observation-write", "append state_root bytes", "ZSSZ format"),
    "writeSuccessRawLine138": ("observation-write", "append receipts_root bytes", "ZSSZ format"),
    "writeSuccessRawLine139": ("observation-write", "append logs_bloom bytes", "ZSSZ format"),
    "writeSuccessRawLine140": ("observation-write", "append prev_randao bytes", "ZSSZ format"),
    "writeSuccessRawLine147": ("observation-write", "append block_hash bytes", "ZSSZ format"),
    "writeSuccessTransactions": ("observation-encode", "append structured transactions", "ZSSZ format"),
    "writeSuccessWithdrawals": ("observation-encode", "append structured withdrawals", "ZSSZ format"),
    "writeSuccessRawLine156": ("observation-write", "append parent_beacon_block_root bytes", "ZSSZ format"),
    "writeSuccessHashes": ("observation-encode", "append versioned_hashes", "ZSSZ format"),
    "writeSuccessBoolean": ("observation-encode", "append one-byte boolean", "ZSSZ format"),
    "writeSuccessOptionalU64": ("observation-encode", "append optional u64", "ZSSZ format"),
    "writeSuccessByteLists": ("observation-encode", "append length-delimited byte-list list", "ZSSZ format"),
    "writeSuccessBytes": ("observation-encode", "append length-delimited bytes", "ZSSZ format"),
    "writeSuccessInt": ("observation-encode", "append fixed-width little-endian integer", "ZSSZ format"),
    "writeFailureRawLine127": ("observation-write", "append ZSSZ v1 failure record", "ZSSZ format"),
}

FIXED_WRITE_BYTES = {
    "writeSuccessRawLine131": bytes.fromhex("5a53535a0101"),
    "writeSuccessRawLine135": bytes(32),
    "writeSuccessRawLine136": bytes(20),
    "writeSuccessRawLine137": bytes(32),
    "writeSuccessRawLine138": bytes(32),
    "writeSuccessRawLine139": bytes(256),
    "writeSuccessRawLine140": bytes(32),
    "writeSuccessRawLine147": bytes(32),
    "writeSuccessRawLine156": bytes(32),
    "writeFailureRawLine127": bytes.fromhex("5a53535a0100"),
}


def build(manifest: dict, evidence: dict, bindings: dict, cfg: dict) -> dict:
    if any(manifest["artifact"] != document["artifact"]
           for document in (evidence, bindings, cfg)):
        raise ValueError("Level 2 admission inputs describe different ELFs")
    cfg_instances = {row["id"]: row for row in cfg["functionInstances"]}
    binding_rows = {row["id"]: row["bindings"] for row in bindings["instances"]}
    observations: dict[str, dict] = {}
    for vector in evidence["vectors"]:
        for row in vector["instances"]:
            slot = observations.setdefault(row["id"], {
                "vectors": [], "entries": 0, "exits": set(), "loads": 0, "stores": 0,
                "hostWrites": [], "occurrences": [],
            })
            if row["entryReached"]:
                slot["vectors"].append(vector["label"])
                slot["entries"] += len(row["entryRegisters"])
            slot["exits"].update(tuple(edge) for edge in row["observedExitTransitions"])
            slot["loads"] += sum(access["kind"] == "load" for access in row["memoryAccesses"])
            slot["stores"] += sum(access["kind"] == "store" for access in row["memoryAccesses"])
            slot["hostWrites"].extend({"vector": vector["label"], **write}
                                      for write in row["hostWrites"])
            slot["occurrences"].extend({"vector": vector["label"], **occurrence}
                                       for occurrence in row["occurrences"])
    rows = []
    for instance in manifest["instances"]:
        name = source_name(instance, cfg_instances)
        semantic_kind, semantic_clause, specification = SEMANTICS[name]
        observed = observations[instance["id"]]
        dwarf = binding_rows[instance["id"]]
        entry_binding = None
        if name in FIXED_WRITE_BYTES:
            writes = observed["hostWrites"]
            if not writes or any(
                    bytes.fromhex(write["bytes"]) != FIXED_WRITE_BYTES[name] for write in writes):
                raise ValueError(f"fixed source write mismatch for {name}")
            if name not in {"writeSuccessRawLine131", "writeFailureRawLine127"}:
                snapshots = [snapshot for vector in evidence["vectors"]
                             for row in vector["instances"] if row["id"] == instance["id"]
                             for snapshot in row["entryRegisters"]]
                if len(snapshots) != len(writes) or any(
                        snapshot["values"][10] != write["address"]
                        for snapshot, write in zip(snapshots, writes, strict=True)):
                    raise ValueError(f"fixed source pointer binding mismatch for {name}")
                entry_binding = {"pointerRegister": 10, "width": len(FIXED_WRITE_BYTES[name])}
        elif name == "writeSuccessBoolean":
            for occurrence in observed["occurrences"]:
                writes = occurrence["hostWrites"]
                value = occurrence["entryRegisters"]["values"][10] & 1
                if len(writes) != 1 or bytes.fromhex(writes[0]["bytes"]) != bytes([value]):
                    raise ValueError("boolean entry/output binding mismatch")
            entry_binding = {"valueRegister": 10, "encoding": "low-bit-u8"}
        elif name == "writeSuccessInt":
            for occurrence in observed["occurrences"]:
                writes = occurrence["hostWrites"]
                value = occurrence["entryRegisters"]["values"][10]
                if len(writes) != 1 or bytes.fromhex(writes[0]["bytes"]) != value.to_bytes(8, "little"):
                    raise ValueError("u64 entry/output binding mismatch")
            entry_binding = {"valueRegister": 10, "encoding": "little-u64"}
        elif name == "writeSuccessBytes":
            for occurrence in observed["occurrences"]:
                writes = occurrence["hostWrites"]
                registers = occurrence["entryRegisters"]["values"]
                address, length = registers[10], registers[11]
                if not writes or bytes.fromhex(writes[0]["bytes"]) != length.to_bytes(8, "little"):
                    raise ValueError("byte-slice length binding mismatch")
                if length == 0:
                    if len(writes) not in {1, 2} or (len(writes) == 2 and writes[1]["bytes"] != ""):
                        raise ValueError("empty byte slice emitted nonempty payload bytes")
                elif len(writes) != 2 or writes[1]["address"] != address or \
                        len(bytes.fromhex(writes[1]["bytes"])) != length:
                    raise ValueError("byte-slice pointer/length binding mismatch")
            entry_binding = {"pointerRegister": 10, "lengthRegister": 11,
                             "encoding": "length-prefixed-bytes"}
        elif name in {"writeSuccessTransactions", "writeSuccessWithdrawals",
                      "writeSuccessHashes", "writeSuccessByteLists"}:
            count_register = {
                "writeSuccessTransactions": 10,
                "writeSuccessWithdrawals": 9,
                "writeSuccessHashes": 8,
                "writeSuccessByteLists": 11,
            }[name]
            for occurrence in observed["occurrences"]:
                writes = occurrence["hostWrites"]
                count = occurrence["entryRegisters"]["values"][count_register]
                if not writes or bytes.fromhex(writes[0]["bytes"]) != count.to_bytes(8, "little"):
                    raise ValueError(f"{name} count binding mismatch")
            entry_binding = {"countRegister": count_register, "encoding": "little-u64-prefix"}
        rows.append({
            "id": instance["id"], "leanName": name, "qualified": instance["qualified"],
            "parentInstanceIds": instance["parentInstanceIds"],
            "source": instance["functionInstanceIdentity"],
            "semanticReview": {
                "status": "reviewed", "kind": semantic_kind,
                "clause": semantic_clause, "reference": specification,
            },
            "measured": {
                "vectors": sorted(observed["vectors"]),
                "entrySnapshotCount": observed["entries"],
                "observedExitTransitions": [list(edge) for edge in sorted(observed["exits"])],
                "loadCount": observed["loads"], "storeCount": observed["stores"],
                "hostWrites": observed["hostWrites"],
                "occurrences": observed["occurrences"],
                "validatedEntryBinding": entry_binding,
                "dwarfBindings": dwarf,
            },
            "unmeasured": [
                "universal termination bound", "universal register and memory frame",
                "source-value relation at optimized inline boundary",
            ],
            "contractStatus": "not-admitted",
        })
    if {row["leanName"] for row in rows} != set(SEMANTICS):
        raise ValueError("semantic review does not cover the exact Level 2 inventory")
    return {"schemaVersion": 1, "artifact": manifest["artifact"], "instances": rows}


def main() -> int:
    parser = argparse.ArgumentParser()
    for name in ("manifest", "evidence", "bindings", "cfg", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    result = build(*(json.loads(getattr(args, name).read_text())
                     for name in ("manifest", "evidence", "bindings", "cfg")))
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
