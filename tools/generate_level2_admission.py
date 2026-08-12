#!/usr/bin/env python3
"""Join Level 2 source semantics with measured production-boundary evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from generate_level2_lean import source_name


SEMANTICS = {
    "readInputSyscall": ("linux-read", "read(0, buffer, requested)", "runtime syscall3"),
    "zkvmExitSyscall": ("linux-exit", "exit(code)", "runtime syscall3"),
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
                "hostWrites": [],
            })
            if row["entryReached"]:
                slot["vectors"].append(vector["label"])
                slot["entries"] += len(row["entryRegisters"])
            slot["exits"].update(tuple(edge) for edge in row["observedExitTransitions"])
            slot["loads"] += sum(access["kind"] == "load" for access in row["memoryAccesses"])
            slot["stores"] += sum(access["kind"] == "store" for access in row["memoryAccesses"])
            slot["hostWrites"].extend({"vector": vector["label"], **write}
                                      for write in row["hostWrites"])
    rows = []
    for instance in manifest["instances"]:
        name = source_name(instance, cfg_instances)
        semantic_kind, semantic_clause, specification = SEMANTICS[name]
        observed = observations[instance["id"]]
        dwarf = binding_rows[instance["id"]]
        if name in FIXED_WRITE_BYTES:
            writes = observed["hostWrites"]
            if len(writes) != 1 or bytes.fromhex(writes[0]["bytes"]) != FIXED_WRITE_BYTES[name]:
                raise ValueError(f"fixed source write mismatch for {name}")
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
