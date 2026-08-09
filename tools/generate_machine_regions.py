#!/usr/bin/env python3
"""Generate the canonical, untrusted per-instruction proof-region database.

LLVM supplies disassembly.  The existing Elfling artifact supplies checked DWARF provenance and the
root-reachable instruction set.  This program derives ownership, the instruction CFG, SCCs, unit
entries/exits, conservative register effects, and liveness in one deterministic pass.

Nothing in this output is trusted by Lean.  In particular, unresolved indirect transfers remain
explicit and register effects are deliberately conservative when an opcode is not recognized.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys
from collections import defaultdict


FUNCTION = re.compile(r"^([0-9a-f]+) <([^>]+)>:$")
INSTRUCTION = re.compile(
    r"^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s+([.a-z0-9]+)(?:\s+(.*?))?\s*$"
)
HEX_TARGET = re.compile(r"(?:^|,\s*)(0x[0-9a-f]+)(?:\s+<[^>]+>)?$")
MEMORY = re.compile(r"(-?0x[0-9a-f]+|-?\d+)\(([^)]+)\)")

REGISTERS = (
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1",
    "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7",
    "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11",
    "t3", "t4", "t5", "t6",
)
REGISTER_SET = set(REGISTERS)
CONDITIONAL = {
    "beq", "bne", "blt", "bge", "bltu", "bgeu",
    "beqz", "bnez", "bltz", "bgez", "blez", "bgtz", "ble", "bgt",
}
LOADS = {"lb": 1, "lbu": 1, "lh": 2, "lhu": 2, "lw": 4, "lwu": 4, "ld": 8}
STORES = {"sb": 1, "sh": 2, "sw": 4, "sd": 8}
NO_DESTINATION = CONDITIONAL | set(STORES) | {
    "j", "tail", "ret", "jr", "fence", "fence.i", "ecall", "ebreak", "unimp",
}


def run(command: list[str]) -> str:
    result = subprocess.run(command, check=True, capture_output=True, text=True)
    return result.stdout


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_disassembly(text: str) -> dict[int, dict]:
    result: dict[int, dict] = {}
    function = "<outside-symbol>"
    for raw_line in text.splitlines():
        line = raw_line.strip()
        match = FUNCTION.match(line)
        if match:
            function = match.group(2)
            continue
        match = INSTRUCTION.match(raw_line)
        if not match:
            continue
        address = int(match.group(1), 16)
        if address in result:
            raise ValueError(f"duplicate instruction address 0x{address:x}")
        result[address] = {
            "address": address,
            "word": int(match.group(2), 16),
            "mnemonic": match.group(3),
            "operands": (match.group(4) or "").strip(),
            "symbol": function,
        }
    if not result:
        raise ValueError("LLVM produced no disassembled instructions")
    return result


def in_regions(address: int, regions: list[dict]) -> bool:
    return any(region["start"] <= address < region["start"] + region["size"] for region in regions)


def instance_depth(index: int, instances: list[dict]) -> int:
    depth = 0
    seen = set()
    parent = instances[index].get("parentIdx")
    while parent is not None:
        if parent in seen:
            raise ValueError(f"cycle in DWARF instance parents at {index}")
        seen.add(parent)
        depth += 1
        parent = instances[parent].get("parentIdx")
    return depth


def assign_owners(program: dict, reachable: set[int]) -> tuple[dict[int, str], dict[str, dict]]:
    instances = program["function_instances"]
    candidates: dict[int, list[tuple[int, int]]] = defaultdict(list)
    owners: dict[str, dict] = {}
    for index, instance in enumerate(instances):
        owner = f"fi:{index}"
        owners[owner] = {
            "id": owner,
            "kind": instance["kind"],
            "qualified": instance["qualified"],
            "parent": (
                f"fi:{instance['parentIdx']}" if instance.get("parentIdx") is not None else None
            ),
            "sourceFile": instance.get("sourceFile"),
            "declLine": instance.get("declLine", 0),
            "specialization": instance.get("specialization", []),
            "inlineStack": instance.get("inlineStack", []),
            "regions": instance["regions"],
            "entryPc": instance["entryPc"],
        }
        depth = instance_depth(index, instances)
        for address in reachable:
            if in_regions(address, instance["regions"]):
                candidates[address].append((depth, index))
    excluded = program.get("excludedFunctionInstances", [])
    for index, excluded_function_instance in enumerate(excluded):
        owner = f"excluded:{index}"
        owners[owner] = {
            "id": owner,
            "kind": excluded_function_instance["category"],
            "qualified": excluded_function_instance["qualified"],
            "parent": None,
            "sourceFile": excluded_function_instance.get("sourceFile"),
            "declLine": 0,
            "inlineStack": [],
            "regions": excluded_function_instance["regions"],
            "entryPc": excluded_function_instance["entryPc"],
        }
        for address in reachable:
            if in_regions(address, excluded_function_instance["regions"]):
                candidates[address].append((-1, -(index + 1)))

    assignment: dict[int, str] = {}
    for address in sorted(reachable):
        choices = candidates.get(address, [])
        if not choices:
            raise ValueError(f"reachable instruction 0x{address:x} has no owner")
        best_depth = max(depth for depth, _ in choices)
        best = sorted(index for depth, index in choices if depth == best_depth)
        if len(best) != 1:
            raise ValueError(f"reachable instruction 0x{address:x} has ambiguous owners {best}")
        index = best[0]
        assignment[address] = f"fi:{index}" if index >= 0 else f"excluded:{-index - 1}"
    return assignment, owners


def owner_rows_for_addresses(
    owners_by_address: dict[int, str], owners: dict[str, dict]
) -> list[dict]:
    return [
        {
            **owners[owner],
            "instructions": sorted(
                address for address, selected in owners_by_address.items() if selected == owner
            ),
        }
        for owner in sorted(owners)
    ]


def addresses_in_declared_regions(program: dict, disassembly: dict[int, dict]) -> set[int]:
    """All instructions in generated function-instance or explicitly excluded regions."""
    regions = [
        region
        for item in program["function_instances"] + program.get("excludedFunctionInstances", [])
        for region in item["regions"]
    ]
    return {
        address for address in disassembly
        if any(in_regions(address, [region]) for region in regions)
    }


def function_instance_ref(reference: list) -> str:
    kind, index = reference
    if kind == "function_instance":
        return f"fi:{index}"
    if kind == "excl":
        return f"excluded:{index}"
    raise ValueError(f"unknown generated call target kind {kind!r}")


def allocator_vtable_slot(
    source: int, owner: str, instructions: dict[int, dict], owners_by_address: dict[int, str]
) -> tuple[int, int] | None:
    """Resolve only reviewed Zig Allocator.VTable transfers to their byte slot."""
    instruction = instructions[source]
    if instruction["mnemonic"] == "jalr":
        _rd, rs1 = jalr_registers(instruction)
        call_register = REGISTERS[rs1]
    elif instruction["mnemonic"] == "jr":
        parts = operands(instruction)
        call_register = parts[0] if len(parts) == 1 else None
    else:
        return None
    if call_register is None:
        return None
    for address in sorted(
        (address for address in instructions
         if source - 32 <= address < source and owners_by_address.get(address) == owner),
        reverse=True,
    ):
        candidate = instructions[address]
        parts = operands(candidate)
        if candidate["mnemonic"] != "ld" or len(parts) != 2 or parts[0] != call_register:
            continue
        match = MEMORY.fullmatch(parts[1])
        if match:
            return address, int(match.group(1), 0)
    return None


def dominator_parents(nodes: set[str], edges: set[tuple[str, str]], root: str) -> dict[str, str]:
    """Immediate dominators turn the production call DAG into one reviewable tree."""
    predecessors = {node: set() for node in nodes}
    for caller, callee in edges:
        if caller in nodes and callee in nodes:
            predecessors[callee].add(caller)
    dominators = {node: ({root} if node == root else set(nodes)) for node in nodes}
    changed = True
    while changed:
        changed = False
        for node in sorted(nodes - {root}):
            incoming = predecessors[node]
            new = {node} if not incoming else {
                node
            } | set.intersection(*(dominators[parent] for parent in incoming))
            if new != dominators[node]:
                dominators[node] = new
                changed = True
    result = {}
    for node in sorted(nodes - {root}):
        strict = dominators[node] - {node}
        if strict:
            result[node] = max(strict, key=lambda candidate: len(dominators[candidate]))
    return result


def build_call_graph(
    program: dict, disassembly: dict[int, dict], addresses: set[int]
) -> dict:
    owners_by_address, owners = assign_owners(program, addresses)
    owner_rows = owner_rows_for_addresses(owners_by_address, owners)
    owner_ids = {row["id"] for row in owner_rows}
    qualified = {row["id"]: row["qualified"] for row in owner_rows}
    by_qualified: dict[str, list[str]] = defaultdict(list)
    for owner, name in qualified.items():
        by_qualified[name].append(owner)

    calls: set[tuple[str, str, str, int | None, int | None]] = set()
    for index, instance in enumerate(program["function_instances"]):
        caller = f"fi:{index}"
        if instance.get("parentIdx") is not None:
            calls.add((f"fi:{instance['parentIdx']}", caller, "inlined", instance["entryPc"], None))
        for reference in instance.get("externalCalls", []):
            calls.add((caller, function_instance_ref(reference), "direct", None, None))

    graph, transfers = {}, {}
    for address in sorted(addresses):
        next_addresses, transfer = successors(address, disassembly[address], disassembly, addresses)
        graph[address], transfers[address] = next_addresses, transfer
    entry_owner = {
        instance["entryPc"]: f"fi:{index}"
        for index, instance in enumerate(program["function_instances"])
    }
    for source, next_addresses in graph.items():
        if transfers[source] not in {"directCall", "directJump"}:
            continue
        caller = owners_by_address[source]
        for destination in next_addresses:
            callee = entry_owner.get(destination)
            if callee and callee != caller and owners[callee]["kind"] == "emitted":
                kind = "direct" if transfers[source] == "directCall" else "tail"
                calls.add((caller, callee, kind, source, destination))
    # The Elfling CFG records exact decoded edges even when LLVM prints a transfer operand in a
    # form the presentation parser does not recognize. Use those checked edges as a second source.
    for instance in program["function_instances"]:
        for edge in instance.get("edges", []):
            source, destination = edge["source"], edge["target"]
            if source not in owners_by_address:
                continue
            caller, callee = owners_by_address[source], entry_owner.get(destination)
            if callee and callee != caller and owners[callee]["kind"] == "emitted":
                transfer = transfers.get(source)
                kind = "direct" if transfer == "directCall" else "tail"
                calls.add((caller, callee, kind, source, destination))

    allocator_targets = {
        0: "raw_decoder_root.allocatorAlloc",
        8: "raw_decoder_root.allocatorResize",
        16: "raw_decoder_root.allocatorRemap",
        24: "raw_decoder_root.allocatorFree",
    }
    reviewed_slots = {
        "ssz_raw.decodePublicKeys": 24,
        "mem.Allocator.free__anon_1214": 24,
        "mem.Allocator.allocBytesWithAlignment__anon_1331": 0,
        "mem.Allocator.free__anon_1471": 24,
        "mem.Allocator.free__anon_1468": 24,
        "mem.Allocator.allocBytesWithAlignment__anon_1511": 0,
        "mem.Allocator.free__anon_1465": 24,
        "mem.Allocator.free__anon_1428": 24,
        "mem.Allocator.free__anon_1555": 24,
    }
    resolved_indirect, unresolved_indirect = [], []
    for source in sorted(address for address, transfer in transfers.items()
                         if transfer.startswith("indirect")):
        caller = owners_by_address[source]
        expected_slot = reviewed_slots.get(qualified[caller])
        loaded = allocator_vtable_slot(source, caller, disassembly, owners_by_address)
        if expected_slot is None or loaded is None or loaded[1] != expected_slot:
            unresolved_indirect.append(source)
            continue
        load_address, slot = loaded
        targets = by_qualified[allocator_targets[slot]]
        if len(targets) != 1:
            raise ValueError(f"allocator vtable slot {slot} has no unique emitted target")
        callee = targets[0]
        calls.add((caller, callee, "allocatorVtable", source, load_address))
        resolved_indirect.append({
            "source": source, "load": load_address, "slot": slot,
            "caller": caller, "callee": callee,
        })

    program_node = "program"
    runner_names = (
        "raw_decoder_root.zesu_decode_raw",
        "raw_decoder_root.zesu_raw_result",
        "raw_decoder_root.zesu_raw_error",
    )
    for name in runner_names:
        targets = by_qualified[name]
        if len(targets) != 1:
            raise ValueError(f"runner target {name} is not unique")
        calls.add((program_node, targets[0], "runner", None, None))

    call_edges = {(caller, callee) for caller, callee, *_ in calls}
    reachable = {program_node}
    changed = True
    while changed:
        changed = False
        for caller, callee in call_edges:
            if caller in reachable and callee not in reachable:
                reachable.add(callee)
                changed = True
    reachable_owners = reachable - {program_node}
    result = {
        "owners": owner_rows,
        "calls": [
            {"caller": caller, "callee": callee, "kind": kind,
             "source": source, "evidence": evidence}
            for caller, callee, kind, source, evidence in sorted(
                calls, key=lambda row: (row[0], row[1], row[2], row[3] or -1)
            )
        ],
        "resolvedIndirectCalls": resolved_indirect,
        "unresolvedIndirectCalls": unresolved_indirect,
        "dominatorParent": dominator_parents(reachable, call_edges, program_node),
        "reachableOwners": sorted(reachable_owners),
        "unreachableOwners": sorted(owner_ids - reachable_owners),
        "instructionAddresses": sorted(addresses),
    }
    validate_reviewed_call_spots(result)
    return result


def validate_reviewed_call_spots(call_graph: dict) -> None:
    """Reject drift at representative runner, inline, direct-tail, and vtable edges."""
    ids: dict[str, list[str]] = defaultdict(list)
    for owner in call_graph["owners"]:
        ids[owner["qualified"]].append(owner["id"])

    def unique(name: str) -> str:
        if len(ids[name]) != 1:
            raise ValueError(f"reviewed call spot {name} is not unique")
        return ids[name][0]

    calls = {(row["caller"], row["callee"], row["kind"]) for row in call_graph["calls"]}
    decoder = unique("raw_decoder_root.zesu_decode_raw")
    raw_result = unique("raw_decoder_root.zesu_raw_result")
    raw_error = unique("raw_decoder_root.zesu_raw_error")
    if {callee for caller, callee, kind in calls if caller == "program" and kind == "runner"} != {
        decoder, raw_result, raw_error,
    }:
        raise ValueError("program runner calls are not exactly decoder, result, and error")
    if (decoder, unique("ssz_raw.decode"), "inlined") not in calls:
        raise ValueError("reviewed inlined decode edge is absent")
    if (unique("raw_decoder_root.allocatorAlloc"), unique("raw_allocator.zesu_raw_alloc"), "tail") not in calls:
        raise ValueError("allocatorAlloc tail call to zesu_raw_alloc is absent")
    for name, slot in (("raw_decoder_root.allocatorAlloc", 0),
                       ("raw_decoder_root.allocatorFree", 24)):
        if not any(row["callee"] == unique(name) and row["slot"] == slot
                   for row in call_graph["resolvedIndirectCalls"]):
            raise ValueError(f"no allocator slot-{slot} call resolves to {name}")
    for name in ("raw_decoder_root.allocatorResize", "raw_decoder_root.allocatorRemap"):
        if unique(name) not in call_graph["unreachableOwners"]:
            raise ValueError(f"uncalled vtable entry {name} incorrectly appears reachable")

    parents = call_graph["dominatorParent"]
    memcpy = unique("memcpy")
    decode_inline = unique("ssz_raw.decode")
    allocator_inline = unique("raw_decoder_root.allocator")
    decode_raw = unique("ssz_raw.decodeRaw")
    prefix = unique("ssz_raw.hasExactErePrefix")
    if parents[decoder] != "program" or parents[raw_result] != "program" or parents[raw_error] != "program":
        raise ValueError("Level 1 runner hierarchy changed")
    if {parents[allocator_inline], parents[decode_inline], parents[memcpy]} != {decoder}:
        raise ValueError("Level 2 decoder hierarchy changed")
    if parents[prefix] != decode_inline or parents[decode_raw] != decode_inline:
        raise ValueError("Level 3 decode hierarchy changed")
    validate_level4_displayed_boundaries(call_graph, decode_raw)


def validate_level4_displayed_boundaries(call_graph: dict, decode_raw: str) -> None:
    level4 = level4_displayed_boundaries(call_graph, decode_raw)
    expected_level4 = {
        ("emitted", "raw_decoder_root.allocatorFree"): 1,
        ("inlined", "ssz_raw.requireU32Length"): 1,
        ("inlined", "ssz_raw.readOffset"): 4,
        ("inlined", "ssz_raw.decodeNewPayloadRequest"): 1,
        ("inlined", "ssz_raw.decodeExecutionWitness"): 1,
        ("inlined", "ssz_raw.decodeChainConfig"): 1,
        ("inlined", "ssz_raw.decodePublicKeys"): 1,
        ("reachableCleanupNoOp", "ssz_raw.RawExecutionWitness.deinit"): 1,
        ("reachableStdlib", "mem.Allocator.free__anon_1214"): 1,
        ("reachableStdlib", "mem.Allocator.allocBytesWithAlignment__anon_1331"): 1,
        ("reachableCleanupNoOp", "ssz_raw.RawNewPayloadRequest.deinit"): 1,
        ("emitted", "ssz_raw.decodeByteListList"): 1,
        ("emitted", "ssz_raw.requireCanonicalOffsets"): 1,
        ("emitted", "raw_decoder_root.allocatorAlloc"): 1,
        ("emitted", "memmove"): 1,
    }
    observed_level4: dict[tuple[str, str], int] = defaultdict(int)
    for owner in level4:
        observed_level4[(owner["kind"], owner["qualified"])] += 1
    if observed_level4 != expected_level4:
        raise ValueError("Level 4 displayed boundary inventory changed")
    if len(level4) != 18 or len(observed_level4) != 15:
        raise ValueError("Level 4 no longer displays 18 boundaries from 15 source families")
    offset_sites = sorted(
        (owner["entryPc"], tuple(
            (frame["callerQualified"], frame["line"], frame["column"])
            for frame in owner.get("inlineStack", [])
        ))
        for owner in level4 if owner["qualified"] == "ssz_raw.readOffset"
    )
    expected_offset_sites = [
        (66868, (("ssz_raw.decodeRaw", 199, 23),)),
        (66884, (("ssz_raw.decodeRaw", 200, 23),)),
        (66920, (("ssz_raw.decodeRaw", 201, 23),)),
        (66976, (("ssz_raw.decodeRaw", 202, 23),)),
    ]
    if offset_sites != expected_offset_sites:
        raise ValueError("Level 4 direct readOffset occurrence inventory changed")
    if sum(len(owner["instructions"]) for owner in call_graph["owners"]
           if owner["id"] == decode_raw) != 172:
        raise ValueError("Level 4 decodeRaw no longer owns exactly 172 instruction PCs")


def level4_displayed_boundaries(call_graph: dict, decode_raw: str) -> list[dict]:
    """The Level 4 rows directly displayed below emitted ``ssz_raw.decodeRaw`` in the UI.

    The UI groups the production call DAG by immediate dominator.  These rows are a display and
    review inventory, not a replacement for `FunctionInstance.children`. Excluded cleanup regions
    stay excluded identities and must receive inline-region contracts rather than
    `FunctionInstanceContract` values.
    """
    parents = call_graph["dominatorParent"]
    return [owner for owner in call_graph["owners"] if parents.get(owner["id"]) == decode_raw]


def level4_boundary_manifest(database: dict) -> dict:
    """A contract-admission inventory for every Level 4 row displayed below ``decodeRaw``.

    `instructionPcs` deliberately comes from each row's full generated execution regions, rather
    than from exclusive instruction ownership.  An inlined `readOffset` can have zero exclusive PCs
    because its nested reader owns every instruction, but its contract still needs the nonempty
    boundary execution region that the production binary executes.
    """
    call_graph = database["callGraph"]
    decode_raw = next(
        owner for owner in call_graph["owners"]
        if owner["kind"] == "emitted" and owner["qualified"] == "ssz_raw.decodeRaw"
    )
    boundaries = level4_displayed_boundaries(call_graph, decode_raw["id"])
    instruction_rows = {row["address"]: row for row in database["instructions"]}
    instruction_addresses = set(call_graph["instructionAddresses"])
    calls_by_owner: dict[str, list[dict]] = defaultdict(list)
    for call in call_graph["calls"]:
        if call["source"] is not None:
            calls_by_owner[call["caller"]].append({
                "id": call["callee"], "kind": call["kind"], "source": call["source"],
                "evidence": call["evidence"],
            })

    rows = []
    for owner in sorted(boundaries, key=lambda row: (row["entryPc"], row["id"])):
        instruction_pcs = sorted(
            address for address in instruction_addresses if in_regions(address, owner["regions"])
        )
        instruction_set = set(instruction_pcs)
        exits = [
            {"source": address, "target": successor}
            for address in instruction_pcs
            for successor in instruction_rows.get(address, {"successors": []})["successors"]
            if successor not in instruction_set
        ]
        stores = [
            {"pc": address, "bytes": memory["bytes"]}
            for address in instruction_pcs
            for memory in instruction_rows.get(address, {"memory": []})["memory"]
            if memory["kind"] == "write"
        ]
        row = {
            "id": owner["id"],
            "kind": owner["kind"],
            "qualified": owner["qualified"],
            "entryPc": owner["entryPc"],
            "instructionPcs": instruction_pcs,
            "exits": exits,
            "parent": decode_raw["id"],
        }
        if owner["kind"] in {"emitted", "inlined"}:
            row["functionInstanceIdentity"] = {
                "sourceFile": owner["sourceFile"],
                "qualified": owner["qualified"],
                "specialization": owner["specialization"],
                "inlineStack": owner["inlineStack"],
            }
        if calls_by_owner[owner["id"]]:
            row["calls"] = calls_by_owner[owner["id"]]
        if stores:
            row["stores"] = stores
        rows.append(row)
    manifest = {
        "schemaVersion": 1,
        "parent": {
            "id": decode_raw["id"], "kind": decode_raw["kind"],
            "qualified": decode_raw["qualified"], "entryPc": decode_raw["entryPc"],
        },
        "boundaries": rows,
    }
    validate_level4_boundary_manifest(manifest)
    return manifest


def validate_level4_boundary_manifest(manifest: dict) -> None:
    """Reject a malformed or incomplete Level 4 contract-admission inventory."""
    if manifest.get("schemaVersion") != 1:
        raise ValueError("Level 4 boundary manifest schema version changed")
    parent = manifest.get("parent")
    boundaries = manifest.get("boundaries")
    if not isinstance(parent, dict) or parent.get("qualified") != "ssz_raw.decodeRaw":
        raise ValueError("Level 4 boundary manifest parent is not decodeRaw")
    if not isinstance(parent.get("id"), str) or not isinstance(parent.get("entryPc"), int):
        raise ValueError("Level 4 boundary manifest parent has an invalid identity")
    if not isinstance(boundaries, list) or len(boundaries) != 18:
        raise ValueError("Level 4 boundary manifest does not contain 18 boundaries")
    ids = [row.get("id") for row in boundaries]
    if len(set(ids)) != 18 or any(not isinstance(identifier, str) for identifier in ids):
        raise ValueError("Level 4 boundary manifest identities are not unique")
    families = {row.get("qualified") for row in boundaries}
    if len(families) != 15:
        raise ValueError("Level 4 boundary manifest does not contain 15 source families")
    for row in boundaries:
        required = ("id", "kind", "qualified", "entryPc", "instructionPcs", "exits", "parent")
        if any(key not in row for key in required):
            raise ValueError("Level 4 boundary manifest row omits a required field")
        if (not isinstance(row["kind"], str) or not isinstance(row["qualified"], str)
                or not isinstance(row["entryPc"], int) or not isinstance(row["exits"], list)):
            raise ValueError("Level 4 boundary manifest row has an invalid required field")
        pcs = row["instructionPcs"]
        if not isinstance(pcs, list) or not pcs or pcs != sorted(set(pcs)):
            raise ValueError("Level 4 boundary manifest row has empty or unsorted instruction PCs")
        if row["parent"] != parent["id"]:
            raise ValueError("Level 4 boundary manifest row has the wrong parent")
        identity = row.get("functionInstanceIdentity")
        if row["kind"] in {"emitted", "inlined"}:
            if not isinstance(identity, dict) or identity.get("qualified") != row["qualified"]:
                raise ValueError("Level 4 FunctionInstance boundary lacks its generated identity")
        elif identity is not None:
            raise ValueError("Level 4 excluded boundary falsely claims a FunctionInstance identity")
        for optional_field in ("calls", "stores"):
            if optional_field in row and not isinstance(row[optional_field], list):
                raise ValueError(f"Level 4 boundary manifest {optional_field} field is not a list")
    direct_offsets = [row for row in boundaries if row["qualified"] == "ssz_raw.readOffset"]
    if len(direct_offsets) != 4 or any(not row["instructionPcs"] for row in direct_offsets):
        raise ValueError("Level 4 direct readOffset boundaries are incomplete")


def operands(instruction: dict) -> list[str]:
    return [part.strip() for part in instruction["operands"].split(",") if part.strip()]


def target(instruction: dict) -> int | None:
    match = HEX_TARGET.search(instruction["operands"])
    return int(match.group(1), 16) if match else None


def sign_extend(value: int, bits: int) -> int:
    sign = 1 << (bits - 1)
    return (value ^ sign) - sign


def jalr_registers(instruction: dict) -> tuple[int, int]:
    word = instruction["word"]
    return (word >> 7) & 0x1F, (word >> 15) & 0x1F


def resolved_auipc_jalr_target(
    address: int, instruction: dict, all_instructions: dict[int, dict]
) -> int | None:
    if instruction["mnemonic"] != "jalr":
        return None
    previous = all_instructions.get(address - 4)
    if not previous or previous["mnemonic"] != "auipc":
        return None
    _rd, rs1 = jalr_registers(instruction)
    auipc_rd = (previous["word"] >> 7) & 0x1F
    if rs1 != auipc_rd:
        return None
    upper = sign_extend(previous["word"] & 0xFFFFF000, 32)
    lower = sign_extend(instruction["word"] >> 20, 12)
    return ((address - 4) + upper + lower) & ~1


def register(token: str) -> str | None:
    token = token.strip()
    if token in REGISTER_SET:
        return token
    match = MEMORY.fullmatch(token)
    return match.group(2) if match and match.group(2) in REGISTER_SET else None


def register_effects(instruction: dict) -> tuple[set[str], set[str], list[dict], bool]:
    mnemonic = instruction["mnemonic"]
    parts = operands(instruction)
    reads: set[str] = set()
    writes: set[str] = set()
    memory: list[dict] = []
    known = True

    if mnemonic in LOADS and len(parts) == 2:
        writes.add(parts[0])
        base = register(parts[1])
        if base:
            reads.add(base)
        memory.append({"kind": "read", "bytes": LOADS[mnemonic]})
    elif mnemonic in STORES and len(parts) == 2:
        value, base = register(parts[0]), register(parts[1])
        if value:
            reads.add(value)
        if base:
            reads.add(base)
        memory.append({"kind": "write", "bytes": STORES[mnemonic]})
    elif mnemonic in CONDITIONAL:
        for part in parts[:-1]:
            reg = register(part)
            if reg:
                reads.add(reg)
    elif mnemonic == "ret":
        reads.add("ra")
    elif mnemonic == "jr":
        if parts and register(parts[0]):
            reads.add(register(parts[0]))
    elif mnemonic in {"j", "tail", "fence", "fence.i", "ebreak", "unimp"}:
        pass
    elif mnemonic == "call":
        writes.add("ra")
    elif mnemonic == "ecall":
        # The execution environment is outside ordinary instruction liveness.
        reads.update(f"a{i}" for i in range(8))
        writes.add("a0")
    elif parts:
        destination = register(parts[0])
        if mnemonic not in NO_DESTINATION and destination:
            writes.add(destination)
            sources = parts[1:]
        else:
            sources = parts
        for part in sources:
            reg = register(part)
            if reg:
                reads.add(reg)
        if mnemonic == "jal" and (not parts or target(instruction) is not None):
            writes.add(destination or "ra")
        if mnemonic == "jalr" and len(parts) >= 2:
            base = register(parts[-1])
            if base:
                reads.add(base)
    else:
        known = mnemonic in {"nop"}

    if any(reg not in REGISTER_SET for reg in reads | writes):
        known = False
    if not known:
        # Unknown means maximally conservative, never accidental preservation.
        reads = set(REGISTERS)
        writes = set(REGISTERS) - {"zero"}
    writes.discard("zero")
    reads.discard("zero")
    return reads, writes, memory, known


def successors(
    address: int, instruction: dict, all_instructions: dict[int, dict], reachable: set[int]
) -> tuple[list[int], str]:
    mnemonic = instruction["mnemonic"]
    destination = target(instruction)
    fallthrough = address + 4
    result: set[int] = set()
    transfer = "ordinary"
    if mnemonic in CONDITIONAL:
        transfer = "conditional"
        if destination is not None:
            result.add(destination)
        result.add(fallthrough)
    elif mnemonic in {"j", "tail"}:
        transfer = "directJump"
        if destination is not None:
            result.add(destination)
    elif mnemonic in {"call", "jal"}:
        parts = operands(instruction)
        link = not parts or parts[0] not in {"zero", "x0"}
        transfer = "directCall" if link else "directJump"
        if destination is not None:
            result.add(destination)
        if link:
            result.add(fallthrough)
    elif mnemonic == "jalr" and (
        resolved_target := resolved_auipc_jalr_target(address, instruction, all_instructions)
    ) is not None:
        rd, _rs1 = jalr_registers(instruction)
        link = rd != 0
        transfer = "directCall" if link else "directJump"
        result.add(resolved_target)
        if link:
            result.add(fallthrough)
    elif mnemonic == "ret":
        transfer = "return"
    elif mnemonic in {"jr", "jalr"}:
        transfer = "indirectCall" if mnemonic == "jalr" else "indirectTransfer"
    elif mnemonic in {"ebreak", "unimp"}:
        transfer = "terminal"
    else:
        result.add(fallthrough)
    return sorted(result & reachable), transfer


def strongly_connected_components(graph: dict[int, set[int]]) -> list[list[int]]:
    # A production function can contain thousands of straight-line nodes. Python's default recursion
    # ceiling is lower than that; size this implementation's private DFS stack to the checked graph.
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 2 * len(graph) + 100))
    clock = 0
    indices: dict[int, int] = {}
    low: dict[int, int] = {}
    stack: list[int] = []
    active: set[int] = set()
    components: list[list[int]] = []

    def visit(node: int) -> None:
        nonlocal clock
        indices[node] = low[node] = clock
        clock += 1
        stack.append(node)
        active.add(node)
        for successor in sorted(graph[node]):
            if successor not in indices:
                visit(successor)
                low[node] = min(low[node], low[successor])
            elif successor in active:
                low[node] = min(low[node], indices[successor])
        if low[node] == indices[node]:
            component = []
            while True:
                member = stack.pop()
                active.remove(member)
                component.append(member)
                if member == node:
                    break
            components.append(sorted(component))

    for node in sorted(graph):
        if node not in indices:
            visit(node)
    return sorted(components, key=lambda component: component[0])


def liveness(
    graph: dict[int, set[int]], effects: dict[int, tuple[set[str], set[str]]]
) -> tuple[dict[int, set[str]], dict[int, set[str]]]:
    live_in = {address: set() for address in graph}
    live_out = {address: set() for address in graph}
    changed = True
    while changed:
        changed = False
        for address in sorted(graph, reverse=True):
            reads, writes = effects[address]
            new_out = set().union(*(live_in[next_address] for next_address in graph[address]))
            new_in = reads | (new_out - writes)
            if new_in != live_in[address] or new_out != live_out[address]:
                live_in[address], live_out[address] = new_in, new_out
                changed = True
    return live_in, live_out


def condensation_ranks(
    graph: dict[int, set[int]], component_of: dict[int, int], component_count: int
) -> list[int]:
    dag = {index: set() for index in range(component_count)}
    indegree = [0] * component_count
    for source, successors_ in graph.items():
        source_component = component_of[source]
        for destination in successors_:
            destination_component = component_of[destination]
            if source_component != destination_component:
                dag[source_component].add(destination_component)
    for successors_ in dag.values():
        for destination in successors_:
            indegree[destination] += 1
    ready = sorted(index for index, degree in enumerate(indegree) if degree == 0)
    ranks = [-1] * component_count
    rank = 0
    while ready:
        component = ready.pop(0)
        ranks[component] = rank
        rank += 1
        for destination in sorted(dag[component]):
            indegree[destination] -= 1
            if indegree[destination] == 0:
                ready.append(destination)
                ready.sort()
    if any(value < 0 for value in ranks):
        raise ValueError("SCC condensation graph is cyclic")
    return ranks


def spanning_tree(
    component: list[int], graph: dict[int, set[int]], reverse: bool = False
) -> dict[int, tuple[int, int]]:
    members = set(component)
    adjacency = {address: set() for address in component}
    for source in component:
        for destination in graph[source] & members:
            if reverse:
                adjacency[destination].add(source)
            else:
                adjacency[source].add(destination)
    root = min(component)
    result = {root: (root, 0)}
    queue = [root]
    while queue:
        source = queue.pop(0)
        for destination in sorted(adjacency[source]):
            if destination not in result:
                result[destination] = (source, result[source][1] + 1)
                queue.append(destination)
    if set(result) != members:
        direction = "reverse" if reverse else "forward"
        raise ValueError(f"SCC is not {direction}-connected from 0x{root:x}")
    return result


def build_database(elf: pathlib.Path, program_path: pathlib.Path, llvm_objdump: str) -> dict:
    program = json.loads(program_path.read_text())
    disassembly = parse_disassembly(run([llvm_objdump, "--disassemble", str(elf)]))
    reachable = {row["addr"] for row in program["reachable"]}
    missing = sorted(reachable - disassembly.keys())
    if missing:
        raise ValueError(f"{len(missing)} reachable addresses absent from LLVM disassembly")
    owners_by_address, owners = assign_owners(program, reachable)

    graph: dict[int, set[int]] = {}
    transfers: dict[int, str] = {}
    effects: dict[int, tuple[set[str], set[str]]] = {}
    effect_rows: dict[int, tuple[list[dict], bool]] = {}
    for address in sorted(reachable):
        instruction = disassembly[address]
        next_addresses, transfer = successors(address, instruction, disassembly, reachable)
        graph[address] = set(next_addresses)
        transfers[address] = transfer
        reads, writes, memory, known = register_effects(instruction)
        effects[address] = reads, writes
        effect_rows[address] = memory, known

    components = strongly_connected_components(graph)
    component_of = {
        address: index for index, component in enumerate(components) for address in component
    }
    component_ranks = condensation_ranks(graph, component_of, len(components))
    forward_trees = {
        index: spanning_tree(component, graph)
        for index, component in enumerate(components)
    }
    reverse_trees = {
        index: spanning_tree(component, graph, reverse=True)
        for index, component in enumerate(components)
    }
    loops = {
        index for index, component in enumerate(components)
        if len(component) > 1 or component[0] in graph[component[0]]
    }
    live_in, live_out = liveness(graph, effects)

    entries: dict[str, set[int]] = defaultdict(set)
    exits: dict[str, set[tuple[int, int]]] = defaultdict(set)
    for source, next_addresses in graph.items():
        source_owner = owners_by_address[source]
        for destination in next_addresses:
            destination_owner = owners_by_address[destination]
            if source_owner != destination_owner:
                entries[destination_owner].add(destination)
                exits[source_owner].add((source, destination))
    root_entry = program["function_instances"][program["entryIndex"]]["entryPc"]
    entries[owners_by_address[root_entry]].add(root_entry)

    instructions = []
    for address in sorted(reachable):
        instruction = disassembly[address]
        reads, writes = effects[address]
        memory, known_effects = effect_rows[address]
        instructions.append({
            **instruction,
            "owner": owners_by_address[address],
            "successors": sorted(graph[address]),
            "transfer": transfers[address],
            "scc": component_of[address],
            "loop": component_of[address] in loops,
            "reads": sorted(reads),
            "writes": sorted(writes),
            "memory": memory,
            "knownEffects": known_effects,
            "liveIn": sorted(live_in[address]),
            "liveOut": sorted(live_out[address]),
        })

    owner_rows = []
    for owner in sorted(owners):
        owned = sorted(address for address, selected in owners_by_address.items() if selected == owner)
        owner_rows.append({
            **owners[owner],
            "instructions": owned,
            "entries": sorted(entries[owner]),
            "exits": [
                {"source": source, "target": destination}
                for source, destination in sorted(exits[owner])
            ],
            "loopSccs": sorted({component_of[address] for address in owned if component_of[address] in loops}),
        })

    unresolved = [
        row["address"] for row in instructions
        if row["transfer"] in {"indirectCall", "indirectTransfer"}
    ]
    database = {
        "schemaVersion": 1,
        "producer": "tools/generate_machine_regions.py",
        "inputs": {
            "elfSha256": sha256(elf),
            "programJsonSha256": sha256(program_path),
            "decoderTextSha256": program["decoderTextSha256"],
        },
        "entry": root_entry,
        "instructions": instructions,
        "owners": owner_rows,
        "sccs": [
            {
                "id": index,
                "rank": component_ranks[index],
                "instructions": component,
                "loop": index in loops,
            }
            for index, component in enumerate(components)
        ],
        "sccForwardTree": [
            {"address": address, "parent": parent, "depth": depth}
            for index, component in enumerate(components)
            for address, (parent, depth) in sorted(forward_trees[index].items())
        ],
        "sccReverseTree": [
            {"address": address, "parent": parent, "depth": depth}
            for index, component in enumerate(components)
            for address, (parent, depth) in sorted(reverse_trees[index].items())
        ],
        "unresolvedIndirectTransfers": unresolved,
        "summary": {
            "instructionCount": len(instructions),
            "ownerCount": len(owner_rows),
            "activeOwnerCount": sum(bool(owner["instructions"]) for owner in owner_rows),
            "edgeCount": sum(len(edges) for edges in graph.values()),
            "loopSccCount": len(loops),
            "unresolvedIndirectTransferCount": len(unresolved),
            "unknownEffectCount": sum(not row["knownEffects"] for row in instructions),
        },
    }
    complete_addresses = addresses_in_declared_regions(program, disassembly)
    database["callGraph"] = build_call_graph(program, disassembly, complete_addresses)
    database["summary"]["binaryInstructionCount"] = len(complete_addresses)
    return database


def validate(database: dict) -> None:
    rows = database["instructions"]
    addresses = [row["address"] for row in rows]
    if addresses != sorted(set(addresses)):
        raise ValueError("instructions are not uniquely sorted")
    address_set = set(addresses)
    graph = {row["address"]: set(row["successors"]) for row in rows}
    owned = [address for owner in database["owners"] for address in owner["instructions"]]
    if sorted(owned) != addresses:
        raise ValueError("owners do not exactly tile instructions")
    owner_ids = {owner["id"] for owner in database["owners"]}
    for row in rows:
        if row["owner"] not in owner_ids:
            raise ValueError(f"instruction 0x{row['address']:x} names absent owner")
        if not set(row["successors"]) <= address_set:
            raise ValueError(f"instruction 0x{row['address']:x} has absent successor")
        reads, writes = set(row["reads"]), set(row["writes"])
        if set(row["liveIn"]) != reads | (set(row["liveOut"]) - writes):
            raise ValueError(f"liveness equation fails at 0x{row['address']:x}")
    scc_members = sorted(address for scc in database["sccs"] for address in scc["instructions"])
    if scc_members != addresses:
        raise ValueError("SCCs do not exactly tile instructions")
    recomputed_components = strongly_connected_components(graph)
    if [scc["instructions"] for scc in database["sccs"]] != recomputed_components:
        raise ValueError("SCC inventory disagrees with the instruction graph")
    recomputed_component_of = {
        address: index
        for index, component in enumerate(recomputed_components)
        for address in component
    }
    recomputed_ranks = condensation_ranks(
        graph, recomputed_component_of, len(recomputed_components)
    )
    if [scc["rank"] for scc in database["sccs"]] != recomputed_ranks:
        raise ValueError("SCC ranks disagree with the condensation graph")
    for name in ("sccForwardTree", "sccReverseTree"):
        tree_addresses = sorted(row["address"] for row in database[name])
        if tree_addresses != addresses:
            raise ValueError(f"{name} does not exactly tile instructions")
    unresolved = sorted(
        row["address"] for row in rows
        if row["transfer"] in {"indirectCall", "indirectTransfer"}
    )
    if unresolved != database["unresolvedIndirectTransfers"]:
        raise ValueError("unresolved-indirect inventory disagrees with instructions")

    owner_of = {row["address"]: row["owner"] for row in rows}
    expected_entries: dict[str, set[int]] = defaultdict(set)
    expected_exits: dict[str, set[tuple[int, int]]] = defaultdict(set)
    for source, successors_ in graph.items():
        for destination in successors_:
            if owner_of[source] != owner_of[destination]:
                expected_exits[owner_of[source]].add((source, destination))
                expected_entries[owner_of[destination]].add(destination)
    expected_entries[owner_of[database["entry"]]].add(database["entry"])
    for owner in database["owners"]:
        exits = {(edge["source"], edge["target"]) for edge in owner["exits"]}
        if exits != expected_exits[owner["id"]]:
            raise ValueError(f"owner {owner['id']} exit inventory disagrees with ownership and CFG")
        if set(owner["entries"]) != expected_entries[owner["id"]]:
            raise ValueError(f"owner {owner['id']} entry inventory disagrees with ownership and CFG")

    call_graph = database["callGraph"]
    call_owner_ids = {owner["id"] for owner in call_graph["owners"]}
    call_addresses = call_graph["instructionAddresses"]
    call_owned = sorted(
        address for owner in call_graph["owners"] for address in owner["instructions"]
    )
    if call_owned != call_addresses or call_addresses != sorted(set(call_addresses)):
        raise ValueError("call-graph owners do not exactly tile the instruction inventory")
    for call in call_graph["calls"]:
        if call["caller"] != "program" and call["caller"] not in call_owner_ids:
            raise ValueError("call edge names an absent caller")
        if call["callee"] not in call_owner_ids:
            raise ValueError("call edge names an absent callee")
    reachable_owners = set(call_graph["reachableOwners"])
    unreachable_owners = set(call_graph["unreachableOwners"])
    if reachable_owners & unreachable_owners or reachable_owners | unreachable_owners != call_owner_ids:
        raise ValueError("reachable and uncalled owners do not partition owners")
    parents = call_graph["dominatorParent"]
    if set(parents) != reachable_owners:
        raise ValueError("call-dominator parents do not cover every reachable owner")
    for parent in parents.values():
        if parent != "program" and parent not in reachable_owners:
            raise ValueError("call-dominator parent is not reachable")


def validate_input_hashes(database: dict, elf: pathlib.Path, program_path: pathlib.Path) -> None:
    if database["inputs"]["elfSha256"] != sha256(elf):
        raise ValueError("ELF hash does not match machine-region database")
    if database["inputs"]["programJsonSha256"] != sha256(program_path):
        raise ValueError("program JSON hash does not match machine-region database")


def lean_array(name: str, type_: str, rows: list[str]) -> str:
    chunks = [rows[index:index + 200] for index in range(0, len(rows), 200)]
    declarations = []
    for index, chunk in enumerate(chunks):
        body = ",\n  ".join(chunk)
        declarations.append(f"private def {name}Chunk{index} : Array {type_} := #[\n  {body}\n]\n")
    if not chunks:
        declarations.append(f"def {name} : Array {type_} := #[]\n")
    else:
        joined = " ++ ".join(f"{name}Chunk{index}" for index in range(len(chunks)))
        declarations.append(f"def {name} : Array {type_} := {joined}\n")
    return "\n".join(declarations)


def write_lean(database: dict, path: pathlib.Path) -> None:
    owner_index = {owner["id"]: index for index, owner in enumerate(database["owners"])}
    instructions = database["instructions"]
    text = [
        "-- GENERATED FILE: produced by tools/generate_machine_regions.py. DO NOT EDIT.\n",
        "set_option maxRecDepth 10000\n\n",
        "namespace BinaryFv.Zesu.MachineRegions.Generated\n\n",
        "structure SccTreeRow where\n"
        "  address : Nat\n"
        "  parent : Nat\n"
        "  depth : Nat\n"
        "deriving DecidableEq\n\n",
        lean_array(
            "words", "(Nat × Nat)",
            [f"({row['address']}, {row['word']})" for row in instructions],
        ),
        "\n",
        lean_array(
            "edges", "(Nat × Nat)",
            [
                f"({row['address']}, {successor})"
                for row in instructions for successor in row["successors"]
            ],
        ),
        "\n",
        lean_array(
            "ownership", "(Nat × Nat)",
            [(f"({row['address']}, {owner_index[row['owner']]})") for row in instructions],
        ),
        "\n",
        lean_array(
            "sccMembership", "(Nat × Nat)",
            [f"({row['address']}, {row['scc']})" for row in instructions],
        ),
        "\n",
        lean_array(
            "sccRanks", "(Nat × Nat)",
            [f"({scc['id']}, {scc['rank']})" for scc in database["sccs"]],
        ),
        "\n",
        lean_array(
            "sccRoots", "(Nat × Nat)",
            [f"({scc['id']}, {min(scc['instructions'])})" for scc in database["sccs"]],
        ),
        "\n",
        lean_array(
            "sccForwardTree", "SccTreeRow",
            [
                f"{{ address := {row['address']}, parent := {row['parent']}, depth := {row['depth']} }}"
                for row in database["sccForwardTree"]
            ],
        ),
        "\n",
        lean_array(
            "sccReverseTree", "SccTreeRow",
            [
                f"{{ address := {row['address']}, parent := {row['parent']}, depth := {row['depth']} }}"
                for row in database["sccReverseTree"]
            ],
        ),
        "\n",
        lean_array(
            "unresolvedIndirectTransfers", "Nat",
            [str(address) for address in database["unresolvedIndirectTransfers"]],
        ),
        "\nend BinaryFv.Zesu.MachineRegions.Generated\n",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(text))


def instruction_runs(indices: list[int]) -> list[list[int]]:
    if not indices:
        return []
    runs = []
    start = previous = indices[0]
    for index in indices[1:]:
        if index != previous + 1:
            runs.append([start, previous + 1])
            start = index
        previous = index
    runs.append([start, previous + 1])
    return runs


def build_flame(database: dict) -> dict:
    call_graph = database["callGraph"]
    all_addresses = call_graph["instructionAddresses"]
    address_index = {address: index for index, address in enumerate(all_addresses)}
    by_id = {owner["id"]: owner for owner in call_graph["owners"]}
    checked_by_id = {owner["id"]: owner for owner in database["owners"]}
    callers: dict[str, list[dict]] = defaultdict(list)
    callees: dict[str, list[dict]] = defaultdict(list)
    for call in call_graph["calls"]:
        callees[call["caller"]].append(call)
        callers[call["callee"]].append(call)

    binary_node, program_node, unused_node = "binary", "program", "not-called-by-program"
    parents = dict(call_graph["dominatorParent"])
    parents[program_node] = binary_node
    parents[unused_node] = binary_node
    unreachable = set(call_graph["unreachableOwners"])
    for owner_id in unreachable:
        structural_parent = by_id[owner_id].get("parent")
        parents[owner_id] = structural_parent if structural_parent in unreachable else unused_node

    children: dict[str, list[str]] = defaultdict(list)
    for child, parent in parents.items():
        children[parent].append(child)
    for child_ids in children.values():
        child_ids.sort(key=lambda owner: (
            min(by_id.get(owner, {}).get("instructions", []) or [2**64]), owner
        ))

    meta: dict[str, dict] = {}

    def make_node(owner_id: str, parent_key: str | None) -> tuple[dict, set[int]]:
        synthetic = owner_id in {binary_node, program_node, unused_node}
        if synthetic:
            names = {
                binary_node: "binary",
                program_node: "program",
                unused_node: "not called by program",
            }
            name = names[owner_id]
            qualified = owner_id
            own_addresses: set[int] = set()
            owner = None
        else:
            owner = by_id[owner_id]
            name = f"{owner['qualified']} [{owner_id}]"
            qualified = owner["qualified"]
            own_addresses = set(owner["instructions"])
        key = name if parent_key is None else f"{parent_key}|{name}"
        child_nodes = []
        subtree = set(own_addresses)
        for child_id in children[owner_id]:
            child_node, child_addresses = make_node(child_id, key)
            child_nodes.append(child_node)
            subtree.update(child_addresses)
        indices = sorted(address_index[address] for address in subtree)
        own_indices = sorted(address_index[address] for address in own_addresses)
        node = {
            "name": name,
            "value": len(indices),
            "self": len(own_indices),
            "children": child_nodes,
            "key": key,
        }
        checked = checked_by_id.get(owner_id, {})
        meta[key] = {
            "owner": None if synthetic else owner_id,
            "qualified": qualified,
            "kind": "synthetic" if synthetic else owner["kind"],
            "hierarchy": "synthetic" if synthetic else "callDominator",
            "runs": instruction_runs(indices),
            "frags": len(instruction_runs(indices)),
            "value": len(indices),
            "self": len(own_indices),
            "file": None if synthetic else owner.get("sourceFile"),
            "line": 0 if synthetic else owner.get("declLine", 0),
            "entries": [] if synthetic else checked.get("entries", []),
            "exits": [] if synthetic else checked.get("exits", []),
            "loopSccs": [] if synthetic else checked.get("loopSccs", []),
            "callers": callers[owner_id],
            "callees": callees[owner_id],
            "src": None,
        }
        return node, subtree

    tree, covered = make_node(binary_node, None)
    if covered != set(all_addresses):
        raise ValueError("call hierarchy does not exactly cover the instruction inventory")
    program_key = "binary|program"
    program_total = meta[program_key]["value"]
    cap = max(1, program_total // 10)
    selected: list[str] = []
    residual: dict[str, int] = {}
    needs_split: list[str] = []

    def select(node: dict) -> None:
        key = node["key"]
        if node["value"] <= cap:
            selected.append(key)
            residual[key] = node["value"]
            return
        for child in node["children"]:
            select(child)
        if node["self"]:
            selected.append(key)
            residual[key] = node["self"]
            if node["self"] > cap:
                needs_split.append(key)

    program_tree = next(child for child in tree["children"] if child["name"] == "program")
    for child in program_tree["children"]:
        select(child)
    return {
        "schemaVersion": 2,
        "machineRegionInputs": database["inputs"],
        "total": len(all_addresses),
        "programTotal": program_total,
        "loAddr": min(all_addresses),
        "tree": tree,
        "meta": meta,
        "suggest": {
            "cap": cap,
            "coverage": program_total,
            "units": selected,
            "residual": residual,
            "needsSubFunctionSplit": needs_split,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--elf", type=pathlib.Path, required=True)
    parser.add_argument("--program-json", type=pathlib.Path, required=True)
    parser.add_argument("--llvm-objdump", required=True)
    parser.add_argument("--out", type=pathlib.Path, required=True)
    parser.add_argument("--out-lean", type=pathlib.Path)
    parser.add_argument("--out-flame", type=pathlib.Path)
    parser.add_argument("--out-level4-boundaries", type=pathlib.Path)
    arguments = parser.parse_args()
    database = build_database(arguments.elf, arguments.program_json, arguments.llvm_objdump)
    validate(database)
    validate_input_hashes(database, arguments.elf, arguments.program_json)
    arguments.out.parent.mkdir(parents=True, exist_ok=True)
    arguments.out.write_text(json.dumps(database, indent=2, sort_keys=True) + "\n")
    if arguments.out_lean:
        write_lean(database, arguments.out_lean)
    if arguments.out_flame:
        arguments.out_flame.parent.mkdir(parents=True, exist_ok=True)
        arguments.out_flame.write_text(json.dumps(build_flame(database), separators=(",", ":")) + "\n")
    if arguments.out_level4_boundaries:
        arguments.out_level4_boundaries.parent.mkdir(parents=True, exist_ok=True)
        arguments.out_level4_boundaries.write_text(
            json.dumps(level4_boundary_manifest(database), indent=2, sort_keys=True) + "\n"
        )


if __name__ == "__main__":
    main()
