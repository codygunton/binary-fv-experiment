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
            "exitPcs": instance.get("exits", []),
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


def descendant_owner_ids(owners_by_id: dict[str, dict], root: str) -> set[str]:
    """The full generated extent of an instance includes every nested FunctionInstance."""
    children: dict[str, list[str]] = defaultdict(list)
    for owner in owners_by_id.values():
        if owner.get("parent") is not None:
            children[owner["parent"]].append(owner["id"])
    result, todo = set(), [root]
    while todo:
        owner_id = todo.pop()
        if owner_id in result:
            continue
        result.add(owner_id)
        todo.extend(children[owner_id])
    return result


def dynamic_full_execution_pcs(owner: dict, owners_by_id: dict[str, dict]) -> list[int]:
    """All instruction PCs in an instance and its nested generated instances."""
    descendant_ids = descendant_owner_ids(owners_by_id, owner["id"])
    return sorted({
        address
        for candidate in owners_by_id.values() if candidate["id"] in descendant_ids
        for region in candidate["regions"]
        for address in range(region["start"], region["start"] + region["size"], 4)
    })


def dynamic_owned_execution_pcs(owner: dict, instruction_rows: dict[int, dict]) -> list[int]:
    """The decoder's direct, deepest ownership, read from decoded instruction attribution."""
    return sorted(
        address for address, instruction in instruction_rows.items()
        if instruction.get("owner") == owner["id"]
    )


def function_identity(owner: dict) -> dict:
    """The stable source identity used to select generated FunctionInstances."""
    return {
        "sourceFile": owner["sourceFile"],
        "qualified": owner["qualified"],
        "specialization": owner.get("specialization", []),
        "inlineStack": owner.get("inlineStack", []),
    }


def generated_target_identity(callee: dict) -> dict:
    """A tagged generated target identity: FunctionInstance or ExcludedFunctionInstance."""
    if callee["id"].startswith("excluded:"):
        return {
            "kind": "excludedFunctionInstance", "sourceFile": callee["sourceFile"],
            "qualified": callee["qualified"],
        }
    return {"kind": "functionInstance", **function_identity(callee)}


def dynamic_call_target_extent(callee: dict, owners_by_id: dict[str, dict]) -> dict:
    """The generated Program extent a dynamic call frame may execute before returning.

    This is intentionally the full nested FunctionInstance extent, rather than the caller's
    fragment ``instructionPcs``.  A callee may run nested generated instances before it reaches
    its runtime continuation, and the source identity prevents catalog-position selection.
    """
    full_execution_pcs = dynamic_full_execution_pcs(callee, owners_by_id)
    return {
        "targetIdentity": generated_target_identity(callee),
        "activeCalleeExecutionPcs": full_execution_pcs,
    }


def source_less_call_return_sites(
    caller: dict, callee: dict, instruction_rows: dict[int, dict]
) -> list[dict]:
    """Exact ``jalr x1, x1`` return obligations for a source-less external declaration."""
    result = []
    for source, instruction in sorted(instruction_rows.items()):
        if instruction.get("owner") != caller["id"] or callee["entryPc"] not in instruction["successors"]:
            continue
        if instruction.get("transfer") != "directCall" or instruction.get("mnemonic") != "jalr":
            raise ValueError("source-less Level 4 call site is not a decoded direct jalr call")
        link, base = jalr_registers(instruction)
        if (link, base) != (1, 1):
            raise ValueError("source-less Level 4 call site does not bind RA through jalr x1, x1")
        return_pc = source + 4
        if return_pc not in instruction["successors"]:
            raise ValueError("source-less Level 4 call site lacks its RA fall-through")
        result.append({
            "sourcePc": source, "targetPc": callee["entryPc"], "returnPc": return_pc,
            "linkRegister": "ra",
        })
    if not result:
        raise ValueError("source-less Level 4 call has no caller-owned direct call site")
    return result


def direct_call_return_sites(
    caller: dict, call: dict, callee: dict, instruction_rows: dict[int, dict]
) -> list[dict]:
    """Every decoded `jalr x1, x1` return site for one static direct-call boundary.

    A source-level declaration can have no single machine call PC after inlining.  In that case
    recover every physical site from the CFG.  A resolved declaration still gets its one physical
    site: retaining it makes every direct active-callee frame state the RA value on which its
    continuation relies.
    """
    if call["kind"] != "direct":
        return []
    if call["sourcePc"] is None:
        return source_less_call_return_sites(caller, callee, instruction_rows)
    source = call["sourcePc"]
    instruction = instruction_rows.get(source)
    if (instruction is None or instruction.get("owner") != caller["id"]
            or callee["entryPc"] not in instruction.get("successors", [])
            or instruction.get("transfer") != "directCall" or instruction.get("mnemonic") != "jalr"):
        raise ValueError("resolved Level 4 call site is not a decoded direct jalr call")
    link, base = jalr_registers(instruction)
    if (link, base) != (1, 1):
        raise ValueError("resolved Level 4 call site does not bind RA through jalr x1, x1")
    return_pc = source + 4
    if return_pc not in instruction["successors"]:
        raise ValueError("resolved Level 4 call site lacks its RA fall-through")
    return [{
        "sourcePc": source, "targetPc": callee["entryPc"], "returnPc": return_pc,
        "linkRegister": "ra",
    }]


def declared_level4_calls(owner_id: str, call_graph: dict, owners_by_id: dict[str, dict]) -> list[dict]:
    """Declared direct/tail/vtable call frames with the callee's concrete entry PC."""
    declarations = [
        call for call in call_graph.get("calls", [])
        if call["caller"] == owner_id and call["kind"] in {"direct", "tail", "allocatorVtable"}
    ]
    return [
        {"id": call["callee"], "kind": call["kind"], "sourcePc": call["source"],
         "targetPc": owners_by_id[call["callee"]]["entryPc"]}
        for call in declarations
        if call["source"] is not None or not any(
            concrete["callee"] == call["callee"] and concrete["kind"] == call["kind"]
            and concrete["source"] is not None for concrete in declarations)
    ]


def deepest_call_target_owner(target_pc: int, owners_by_id: dict[str, dict]) -> dict:
    """Resolve a decoded direct-call target to its deepest generated or excluded identity."""
    candidates = [owner for owner in owners_by_id.values() if owner["entryPc"] == target_pc]
    if not candidates:
        raise ValueError("decoded Level 4 direct call target has no generated owner identity")

    def depth(owner: dict) -> int:
        result, current = 0, owner
        while current.get("parent") is not None:
            result += 1
            current = owners_by_id[current["parent"]]
        return result

    deepest = max(candidates, key=depth)
    if sum(depth(owner) == depth(deepest) for owner in candidates) != 1:
        raise ValueError("decoded Level 4 direct call target has ambiguous deepest identity")
    return deepest


def decoded_direct_call_target(source_pc: int, instruction: dict) -> int:
    """The non-fall-through CFG target of one concrete `jalr x1, x1` call instruction."""
    if instruction.get("transfer") != "directCall" or instruction.get("mnemonic") != "jalr":
        raise ValueError("selected Level 4 call site is not a decoded direct jalr call")
    link, base = jalr_registers(instruction)
    if (link, base) != (1, 1):
        raise ValueError("selected Level 4 call site does not bind RA through jalr x1, x1")
    successors = instruction.get("successors", [])
    return_pc = source_pc + 4
    if return_pc not in successors:
        raise ValueError("selected Level 4 call site lacks its RA fall-through")
    targets = [pc for pc in successors if pc != return_pc]
    if len(targets) != 1:
        raise ValueError("selected Level 4 call site lacks one resolved CFG call target")
    return targets[0]


def active_extent_calls(
    active_owner: dict, call_graph: dict, owners_by_id: dict[str, dict], instruction_rows: dict[int, dict]
) -> list[dict]:
    """Every decoded physical direct call in an active frame's exact structural extent.

    `callGraph.calls` is not complete for optimized excluded bodies, so it is never used to
    select these frames.  Decoded instruction transfer/CFG data selects each physical call; the
    call graph's source-derived owner identities only enrich the resulting frame.  The source must
    be both in the active full extent and owned by its structural inline subtree.
    """
    del call_graph
    subtree_ids = descendant_owner_ids(owners_by_id, active_owner["id"])
    extent = set(dynamic_full_execution_pcs(active_owner, owners_by_id))
    expanded = []
    for source_pc in sorted(extent):
        instruction = instruction_rows.get(source_pc)
        if instruction is None or instruction.get("transfer") != "directCall":
            continue
        caller_id = instruction.get("owner")
        if caller_id not in subtree_ids:
            raise ValueError("decoded active Level 4 call has a non-descendant deepest owner")
        target_pc = decoded_direct_call_target(source_pc, instruction)
        callee = deepest_call_target_owner(target_pc, owners_by_id)
        expanded.append({
            "id": callee["id"], "callerId": caller_id, "kind": "direct",
            "sourcePc": source_pc, "targetPc": target_pc,
        })
    deduplicated = {}
    for call in expanded:
        key = (call["sourcePc"], call["targetPc"], call["kind"])
        previous = deduplicated.setdefault(key, call)
        if previous["callerId"] != call["callerId"] or previous["id"] != call["id"]:
            raise ValueError("active Level 4 call source has conflicting deepest-owner targets")
    return sorted(deduplicated.values(), key=lambda call: (
        call["sourcePc"], call["targetPc"], call["kind"], call["callerId"]
    ))


def cycle_back_edge(callee: dict, call: dict, return_sites: list[dict], owners_by_id: dict[str, dict]) -> dict:
    """The concrete transition closing a recursive active-callee path back to an ancestor."""
    sources = sorted({site["sourcePc"] for site in return_sites} | {call["sourcePc"]})
    return {
        "ancestorId": callee["id"],
        "ancestorIdentity": generated_target_identity(callee),
        "ancestorExecutionPcs": dynamic_full_execution_pcs(callee, owners_by_id),
        "transitions": [{"sourcePc": source, "targetPc": callee["entryPc"]} for source in sources],
    }


def active_callee_frame(caller: dict, call: dict, call_graph: dict, owners_by_id: dict[str, dict],
                        instruction_rows: dict[int, dict], seen: frozenset[str] = frozenset()) -> dict:
    """One explicit active callee boundary, recursively retaining its declared child calls."""
    caller = owners_by_id[call.get("callerId", caller["id"])]
    callee = owners_by_id[call["id"]]
    return_sites = direct_call_return_sites(caller, call, callee, instruction_rows)
    frame = {
        **call,
        "callerIdentity": generated_target_identity(caller),
        **dynamic_call_target_extent(callee, owners_by_id),
        "returnSites": return_sites,
        "cycleBackEdge": (cycle_back_edge(callee, call, return_sites, owners_by_id)
                          if callee["id"] in seen else None),
        "activeCalleeFrames": [],
    }
    if frame["cycleBackEdge"] is not None:
        return frame
    frame["activeCalleeFrames"] = [
        active_callee_frame(callee, child, call_graph, owners_by_id, instruction_rows,
                            seen | {callee["id"]})
        for child in active_extent_calls(callee, call_graph, owners_by_id, instruction_rows)
    ]
    return frame


def active_callee_frame_count(frames: list[dict]) -> int:
    """Count every retained frame, including nested cycle-back-edge leaves."""
    return sum(1 + active_callee_frame_count(frame["activeCalleeFrames"]) for frame in frames)


LEVEL4_DYNAMIC_INLINE_IDENTITIES = {
    ("ssz_raw.decodeNewPayloadRequest", "ssz_raw.decodeRaw", 207, 61),
    ("ssz_raw.decodeExecutionWitness", "ssz_raw.decodeRaw", 209, 48),
    ("ssz_raw.decodeChainConfig", "ssz_raw.decodeRaw", 211, 48),
    ("ssz_raw.decodePublicKeys", "ssz_raw.decodeRaw", 212, 46),
}


def is_level4_dynamic_decoder(owner: dict) -> bool:
    frame = (owner.get("inlineStack") or [{}])[-1]
    return (owner["qualified"], frame.get("callerQualified"), frame.get("line"), frame.get("column")) \
        in LEVEL4_DYNAMIC_INLINE_IDENTITIES


def attribution_fragment_handoffs(
    owner: dict, decode_raw: dict, owners_by_id: dict[str, dict], instruction_rows: dict[int, dict]
) -> list[dict]:
    """Every decoded-owned dynamic-decoder edge which hands control back to decodeRaw.

    A source-derived inline identity, rather than a catalog position, selects the four rows.  This
    is deliberately broader than the six historical completion edges: every transition from the
    selected decoder's deepest-owned code into decodeRaw's deepest-owned code is an attribution
    fragment handoff.  Nested descendants and ordinary in-fragment edges are therefore excluded.
    """
    if not is_level4_dynamic_decoder(owner):
        return []
    subtree_ids = (descendant_owner_ids(owners_by_id, owner["id"])
                   if owners_by_id else {owner["id"]})
    owned = {address for address, instruction in instruction_rows.items()
             if instruction.get("owner") in subtree_ids}
    parent_owned = set(dynamic_owned_execution_pcs(decode_raw, instruction_rows))
    result = []
    for source_pc in sorted(owned):
        instruction = instruction_rows.get(source_pc)
        for target_pc in instruction["successors"]:
            if target_pc in parent_owned:
                result.append({"sourcePc": source_pc, "targetPc": target_pc})
    return result


def parent_fragment_reentries(
    owner: dict, decode_raw: dict, owners_by_id: dict[str, dict], instruction_rows: dict[int, dict]
) -> list[dict]:
    """Every decoded-owned decodeRaw edge which enters a direct dynamic decoder fragment."""
    if not is_level4_dynamic_decoder(owner):
        return []
    subtree_ids = (descendant_owner_ids(owners_by_id, owner["id"])
                   if owners_by_id else {owner["id"]})
    owned = {address for address, instruction in instruction_rows.items()
             if instruction.get("owner") in subtree_ids}
    parent_owned = set(dynamic_owned_execution_pcs(decode_raw, instruction_rows))
    return [
        {"sourcePc": source_pc, "targetPc": target_pc}
        for source_pc in sorted(parent_owned)
        for target_pc in instruction_rows[source_pc]["successors"]
        if target_pc in owned
    ]


def recursive_active_return_sites(frames: list[dict]) -> set[tuple[int, int]]:
    """The retained caller-to-continuation edges for every active callee frame.

    A decoded direct call has both the callee target and its syntactic fall-through in the CFG.
    The latter is a valid route predecessor transition only when the generated recursive frame
    records its exact RA return site.  This avoids treating an arbitrary direct-call fall-through
    as though it were a completed call while keeping nested and recursive callee extents explicit.
    """
    result = set()
    for frame in frames:
        extent = set(frame.get("activeCalleeExecutionPcs", []))
        if frame.get("targetPc") in extent:
            result.update((site["sourcePc"], site["returnPc"])
                          for site in frame.get("returnSites", []))
        result.update(recursive_active_return_sites(frame.get("activeCalleeFrames", [])))
    return result


def admissible_route_predecessors(
    owner: dict, handoff: dict, reentries: list[dict], instruction_rows: dict[int, dict],
    owners_by_id: dict[str, dict], active_callee_frames: list[dict], handoffs: list[dict],
) -> list[int]:
    """Exact initial/re-entry stages that can reach one H source in the selected subtree.

    The finite stage domain is the selected decoder entry plus every generated parent-to-child
    re-entry target.  Traversal stays in the selected inline subtree, halts at every *other* H
    source, and permits a direct-call fall-through only if its recursively retained callee frame
    records that RA continuation.  Thus an H route cannot borrow a predecessor from another H
    boundary or from an unframed call extent.
    """
    subtree_ids = (descendant_owner_ids(owners_by_id, owner["id"])
                   if owners_by_id else {owner["id"]})
    selected_pcs = {
        pc for pc, instruction in instruction_rows.items()
        if instruction.get("owner") in subtree_ids
    }
    return_sites = recursive_active_return_sites(active_callee_frames)
    other_handoff_sources = {
        edge["sourcePc"] for edge in handoffs if edge != handoff
    }
    stages = [owner["entryPc"]] + sorted({edge["targetPc"] for edge in reentries}
                                        - {owner["entryPc"]})

    def reaches_handoff_source(stage: int) -> bool:
        todo, seen = [stage], set()
        while todo:
            pc = todo.pop()
            if pc in seen or pc not in selected_pcs:
                continue
            seen.add(pc)
            if pc == handoff["sourcePc"]:
                return True
            if pc in other_handoff_sources:
                continue
            instruction = instruction_rows[pc]
            for successor in instruction["successors"]:
                if successor not in selected_pcs:
                    continue
                if instruction.get("transfer") == "directCall" and (pc, successor) not in return_sites:
                    continue
                if successor not in seen:
                    todo.append(successor)
        return False

    return [stage for stage in stages if reaches_handoff_source(stage)]


# These are source-review labels, not semantic facts imported into Lean.  The function identity is
# the checked raw-DWARF inline identity consumed by `is_level4_dynamic_decoder`; the continuation
# instruction descriptions below are independently checked against the linked production ELF.
# Keeping roles here makes the later contract writer name the machine carrier it must prove instead
# of treating a fragment handoff as an arbitrary universal state.
LEVEL4_OUTCOME_CARRIER_REVIEWS = {
    ("ssz_raw.decodeNewPayloadRequest", "ssz_raw.decodeRaw", 207, 61): {
        "sourceLine": 230,
        "sourceResult": "RawNewPayloadRequest",
        "carrierPcs": [0x1201c],
        "registers": [
            {"pc": 0x1201c, "register": "sp", "role": "parent-frame-base"},
            {"pc": 0x1201c, "register": "a0", "role": "parent-continuation-address"},
            {"pc": 0x1201c, "register": "s7", "role": "status-tag-candidate"},
        ],
        "stackDescriptors": [
            {"pc": 0x1201c, "instructionKind": "addi", "register": "a0", "baseRegister": "sp",
             "offset": 0x7ff, "role": "parent-continuation-address-stage-1"},
        ],
        "statusTag": {"state": "unmeasured", "register": "s7",
                      "reason": "liveness does not establish the status-tag value"},
        "allocation": {"state": "source-reviewed", "reason": "nested source fields allocate"},
        "heapArrayRep": {"state": "unmeasured", "reason": "no array representation recovered"},
    },
    ("ssz_raw.decodeExecutionWitness", "ssz_raw.decodeRaw", 209, 48): {
        "sourceLine": 315,
        "sourceResult": "RawExecutionWitness",
        "carrierPcs": [0x1294c],
        "registers": [
            {"pc": pc, "register": register, "role": role}
            for pc, register, role in ((0x12924, "s6", "state-base"), (0x12928, "s5", "state-length"),
                                       (0x1292c, "s8", "codes-base"), (0x12930, "s7", "codes-length"),
                                       (0x12944, "a0", "headers-base"), (0x12948, "a1", "headers-length"))
        ],
        "stackDescriptors": [
            {"pc": pc, "instructionKind": "store", "register": register, "baseRegister": "sp",
             "offset": offset, "role": role}
            for pc, register, offset, role in ((0x12924, "s6", 0x580, "state-base"),
                                               (0x12928, "s5", 0x588, "state-length"),
                                               (0x1292c, "s8", 0x590, "codes-base"),
                                               (0x12930, "s7", 0x598, "codes-length"),
                                               (0x12944, "a0", 0x5a0, "headers-base"),
                                               (0x12948, "a1", 0x5a8, "headers-length"))
        ],
        "statusTag": {"state": "not-applicable", "reason": "successful RawExecutionWitness carrier"},
        "allocation": {"state": "source-reviewed", "reason": "three decoded lists allocate"},
        "heapArrayRep": {"state": "obligation", "reason": "three slice representations require machine proof"},
        # `try decodeExecutionWitness` failures join decodeRaw's status cleanup at 0x12738.
        # This is not a successful child carrier (and therefore carries no result metadata).
        "rejectionHandoffs": [(0x12850, 0x12738), (0x12884, 0x12738), (0x1302c, 0x12738)],
    },
    ("ssz_raw.decodeChainConfig", "ssz_raw.decodeRaw", 211, 48): {
        "sourceLine": 349,
        "sourceResult": "RawChainConfig",
        "carrierPcs": [0x12e64],
        "registers": [
            {"pc": 0x12e64, "register": "sp", "role": "parent-frame-base"},
            {"pc": 0x12e64, "register": "a4", "role": "chain-config-word-0"},
            {"pc": 0x12e68, "register": "a5", "role": "chain-config-word-1"},
            {"pc": 0x12e6c, "register": "a6", "role": "chain-config-word-2"},
            {"pc": 0x12e70, "register": "a7", "role": "chain-config-word-3"},
        ],
        "stackDescriptors": [
            {"pc": pc, "instructionKind": "store", "register": register, "baseRegister": "sp", "offset": offset,
             "role": "chain-config-parent-store"}
            for pc, register, offset in ((0x12e64, "a4", 0x5c0), (0x12e68, "a5", 0x5c8),
                                         (0x12e6c, "a6", 0x5d0), (0x12e70, "a7", 0x5d8))
        ],
        "statusTag": {"state": "unmeasured", "reason": "status is written after this continuation"},
        "allocation": {"state": "source-reviewed", "reason": "chain config itself has no allocation"},
        "heapArrayRep": {"state": "not-applicable", "reason": "RawChainConfig is a fixed record"},
    },
    ("ssz_raw.decodePublicKeys", "ssz_raw.decodeRaw", 212, 46): {
        "sourceLine": 491,
        "sourceResult": "[][PUBLIC_KEY_SIZE]u8",
        "carrierPcs": [0x12f90, 0x12f94, 0x12f98, 0x12f9c, 0x12fa0, 0x12fa4, 0x12fa8],
        "registers": [
            {"pc": 0x12f90, "register": "sp", "role": "parent-frame-base"},
            {"pc": 0x12f90, "register": "s6", "role": "public-key-array-base"},
            {"pc": 0x12f94, "register": "s1", "role": "public-key-array-count"},
            {"pc": 0x12f98, "register": "a0", "role": "status-record-pointer"},
        ],
        "stackDescriptors": [
            {"pc": 0x12f90, "instructionKind": "store", "register": "s6", "baseRegister": "sp", "offset": 0x600,
             "role": "public-key-array-base-store"},
            {"pc": 0x12f94, "instructionKind": "store", "register": "s1", "baseRegister": "sp", "offset": 0x608,
             "role": "public-key-array-count-store"},
        ],
        "statusTag": {"state": "static-ELF", "pc": 0x12f9c, "baseRegister": "a0", "offset": 0x340,
                      "width": 2, "value": 0, "reason": "sh zero, 0x340(a0)"},
        "allocation": {"state": "source-reviewed", "reason": "alloc.alloc([PUBLIC_KEY_SIZE]u8, count)"},
        "heapArrayRep": {"state": "obligation", "baseRegister": "s6", "countRegister": "s1",
                         "elementBytes": 65,
                         "reason": "source allocation and parent descriptor stores need a machine proof"},
    },
}


def source_line_contains(lines: list[str], line: int, text: str, label: str) -> None:
    if line <= 0 or line > len(lines) or text not in lines[line - 1]:
        raise ValueError(f"Level 4 source review {label} no longer matches pinned source line {line}")


def level4_source_review_evidence(program: dict, source_root: pathlib.Path) -> dict:
    """Bind each semantic carrier classification to the pinned source declaration and call site."""
    evidence = {}
    for instance in program["function_instances"]:
        owner = {
            "qualified": instance["qualified"], "inlineStack": instance.get("inlineStack", []),
            "sourceFile": instance.get("sourceFile"), "declLine": instance.get("declLine"),
        }
        identity = dynamic_identity_key(owner)
        key = dynamic_identity_text(identity)
        review = LEVEL4_OUTCOME_CARRIER_REVIEWS.get(identity)
        if review is None:
            continue
        source_file = source_root / owner["sourceFile"]
        if not source_file.is_file():
            raise ValueError("Level 4 source review source file is absent from the pinned source tree")
        lines = source_file.read_text().splitlines()
        source_line_contains(lines, review["sourceLine"], f"fn {owner['qualified'].split('.')[-1]}", "declaration")
        frame = owner["inlineStack"][-1]
        source_line_contains(
            lines, frame["line"], f"try {owner['qualified'].split('.')[-1]}(", "decodeRaw call site"
        )
        evidence[key] = {
            "sourceContentSha256": sha256(source_file),
            "sourceDeclaration": lines[review["sourceLine"] - 1].strip(),
            "sourceCall": lines[frame["line"] - 1].strip(),
        }
    if set(evidence) != {dynamic_identity_text(key) for key in LEVEL4_OUTCOME_CARRIER_REVIEWS}:
        raise ValueError("Level 4 source review identities are incomplete")
    return evidence


def dynamic_identity_key(owner: dict) -> tuple[str, str | None, int | None, int | None]:
    frame = (owner.get("inlineStack") or [{}])[-1]
    return owner["qualified"], frame.get("callerQualified"), frame.get("line"), frame.get("column")


def dynamic_identity_text(key: tuple[str, str | None, int | None, int | None]) -> str:
    """JSON-safe stable spelling for an identity used as a source-review evidence key."""
    return json.dumps(key, separators=(",", ":"))


def reaches_any(start: int, goals: set[int], instruction_rows: dict[int, dict]) -> bool:
    """CFG reachability used only to distinguish resumable fragments from source-outcome routes."""
    todo, seen = [start], set()
    while todo:
        pc = todo.pop()
        if pc in seen:
            continue
        seen.add(pc)
        if pc in goals:
            return True
        todo.extend(successor for successor in instruction_rows[pc]["successors"]
                    if successor in instruction_rows and successor not in seen)
    return False


def continuation_path(
    start: int, goal: int, owner_ids: set[str], instruction_rows: dict[int, dict],
    allow_goal_outside: bool = False,
) -> list[int] | None:
    """One concrete production-CFG path confined to the decoded `decodeRaw` ownership subtree."""
    if start not in instruction_rows or instruction_rows[start]["owner"] not in owner_ids:
        return None
    previous = {start: None}
    todo = [start]
    while todo:
        pc = todo.pop(0)
        if pc == goal:
            result = []
            while pc is not None:
                result.append(pc)
                pc = previous[pc]
            return list(reversed(result))
        for successor in instruction_rows[pc]["successors"]:
            if (successor in instruction_rows and successor not in previous
                    and (instruction_rows[successor]["owner"] in owner_ids
                         or allow_goal_outside and successor == goal)):
                previous[successor] = pc
                todo.append(successor)
    return None


def outcome_carrier_routes(
    owner: dict, decode_raw: dict, instruction_rows: dict[int, dict],
    source_review_evidence: dict[str, dict] | None = None,
    continuation_owners: set[str] | None = None,
    owners_by_id: dict[str, dict] | None = None,
    active_callee_frames: list[dict] | None = None,
) -> list[dict]:
    """Classify every attribution handoff without mistaking a fragment boundary for a result.

    A source-reviewed outcome route needs a concrete path from its handoff target through only
    ``decodeRaw``-owned production CFG instructions to every listed carrier PC.  A resumption is
    intermediate; a non-resuming target without such a path is explicitly unclassified rather than
    guessed to be an error or outcome.  The source declaration and call-site text are separately
    checked from the pinned raw-SSZ source before a semantic classification is emitted.
    """
    if not is_level4_dynamic_decoder(owner):
        return []
    review = LEVEL4_OUTCOME_CARRIER_REVIEWS[dynamic_identity_key(owner)]
    if owner.get("declLine") != review["sourceLine"]:
        raise ValueError("Level 4 carrier source review does not match the raw-DWARF declaration line")
    reentry_targets = {edge["targetPc"] for edge in parent_fragment_reentries(
        owner, decode_raw, owners_by_id or {}, instruction_rows
    )}
    continuation_owners = continuation_owners or {decode_raw["id"]}
    evidence = (source_review_evidence or {}).get(dynamic_identity_text(dynamic_identity_key(owner)))
    if source_review_evidence is not None and evidence is None:
        raise ValueError("Level 4 carrier source review lacks pinned source content evidence")
    owners_by_id = owners_by_id or {}
    handoffs = attribution_fragment_handoffs(owner, decode_raw, owners_by_id, instruction_rows)
    reentries = parent_fragment_reentries(owner, decode_raw, owners_by_id, instruction_rows)
    routes = []
    for handoff in handoffs:
        rejection = tuple((handoff["sourcePc"], handoff["targetPc"])) in set(review.get("rejectionHandoffs", []))
        resumable = reaches_any(handoff["targetPc"], reentry_targets, instruction_rows)
        paths = [
            continuation_path(handoff["targetPc"], carrier_pc, continuation_owners, instruction_rows,
                              allow_goal_outside=True)
            for carrier_pc in review["carrierPcs"]
        ]
        outcome = not rejection and not resumable and all(path is not None for path in paths)
        routes.append({
            "sourceIdentity": function_identity(owner),
            "handoff": handoff,
            "classification": (
                "rejectionPhaseHandoff" if rejection else "sourceReviewedOutcomePath" if outcome
                else "intermediate" if resumable else "unclassified"
            ),
            "intermediateReason": "reenters-child" if resumable else None,
            "unclassifiedReason": (
                "handoff-target-does-not-reach-reviewed-carrier-in-parent-cfg"
                if not outcome and not resumable and not rejection else None
            ),
            "sourceReview": {
                "sourceFile": owner["sourceFile"], "sourceLine": review["sourceLine"],
                "sourceResult": review["sourceResult"],
                **(evidence or {}),
            },
            "admissiblePredecessors": admissible_route_predecessors(
                owner, handoff, reentries, instruction_rows, owners_by_id,
                active_callee_frames or [], handoffs,
            ),
            "carrierPcs": review["carrierPcs"] if outcome else [],
            "carrierPaths": [
                {"carrierPc": carrier_pc, "pcs": path,
                 "ownerIds": [instruction_rows[pc]["owner"] for pc in path]}
                for carrier_pc, path in zip(review["carrierPcs"], paths) if path is not None
            ] if outcome else [],
            "registers": review["registers"] if outcome else [],
            "stackDescriptors": review["stackDescriptors"] if outcome else [],
            "statusTag": review["statusTag"] if outcome else {"state": "not-applicable"},
            "allocation": review["allocation"] if outcome else {"state": "not-applicable"},
            "heapArrayRep": review["heapArrayRep"] if outcome else {"state": "not-applicable"},
        })
    return routes


def validate_outcome_carrier_instructions(
    routes: list[dict], parent_id: str, instruction_rows: dict[int, dict],
    continuation_owners: set[str] | None = None,
    owners_by_id: dict[str, dict] | None = None,
) -> None:
    """Reject carrier metadata that does not match the concrete parent-continuation instructions."""
    for route in routes:
        if route["classification"] != "sourceReviewedOutcomePath":
            continue
        for pc in route["carrierPcs"]:
            carrier_owner = instruction_rows.get(pc, {}).get("owner")
            owner = (owners_by_id or {}).get(carrier_owner)
            # A reviewed successful child may hand the parent directly into its next selected
            # decoder.  The endpoint is then that child's exact entry PC; all preceding path PCs
            # remain confined to the parent continuation region.
            successor_entry = (owner is not None and owner.get("parent") == parent_id
                               and owner.get("entryPc") == pc)
            if carrier_owner != parent_id and not successor_entry:
                raise ValueError("Level 4 outcome carrier PC is absent from its parent production CFG")
        expected_paths = {
            pc: continuation_path(route["handoff"]["targetPc"], pc, continuation_owners or {parent_id}, instruction_rows,
                                  allow_goal_outside=True)
            for pc in route["carrierPcs"]
        }
        if (set(expected_paths) != {path.get("carrierPc") for path in route["carrierPaths"]}
                or any(path is None for path in expected_paths.values())
                or any(path.get("pcs") != expected_paths[path["carrierPc"]]
                       or path.get("ownerIds") != [instruction_rows[pc]["owner"]
                                                   for pc in expected_paths[path["carrierPc"]]]
                       for path in route["carrierPaths"])):
            raise ValueError("Level 4 outcome carrier path is absent, unreachable, or forged")
        for register in route["registers"]:
            instruction = instruction_rows.get(register["pc"])
            mentioned = (set(instruction["reads"]) | set(instruction["writes"]) |
                         set(instruction["liveIn"]) | set(instruction["liveOut"])) if instruction else set()
            if instruction is None or register["register"] not in mentioned:
                raise ValueError(
                    "Level 4 carrier register does not match its production instruction: "
                    f"{register} at {instruction}"
                )
        for descriptor in route["stackDescriptors"]:
            instruction = instruction_rows.get(descriptor["pc"])
            operand = f"0x{descriptor['offset']:x}({descriptor['baseRegister']})"
            expected_kind = descriptor["instructionKind"]
            matches = False
            if instruction is not None and expected_kind == "addi":
                matches = (instruction["mnemonic"] == "addi" and instruction["operands"] ==
                           f"{descriptor['register']}, {descriptor['baseRegister']}, 0x{descriptor['offset']:x}")
            elif instruction is not None and expected_kind == "load":
                matches = (instruction["mnemonic"].startswith("l")
                           and descriptor["register"] in instruction["operands"] and operand in instruction["operands"])
            elif instruction is not None and expected_kind == "store":
                matches = (instruction["mnemonic"].startswith("s")
                           and descriptor["register"] in instruction["operands"] and operand in instruction["operands"])
            if not matches:
                raise ValueError(
                    "Level 4 carrier stack descriptor does not match its production instruction: "
                    f"{descriptor} at {instruction}"
                )
        status = route["statusTag"]
        if status["state"] == "static-ELF":
            instruction = instruction_rows.get(status["pc"])
            operand = f"0x{status['offset']:x}({status['baseRegister']})"
            if (instruction is None or instruction["mnemonic"] != "sh"
                    or instruction["operands"] != f"zero, {operand}"):
                raise ValueError("Level 4 carrier status tag does not match its production instruction")
        heap = route["heapArrayRep"]
        if (heap["state"] == "obligation" and heap.get("elementBytes") is not None
                and heap["elementBytes"] != 65):
            raise ValueError("Level 4 public-key HeapArrayRep width changed")


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
    owners_by_id = {owner["id"]: owner for owner in call_graph["owners"]}
    decode_raw_continuation_owners = descendant_owner_ids(owners_by_id, decode_raw["id"])
    parent_regions = decode_raw["regions"]
    calls_by_owner = {
        owner_id: declared_level4_calls(owner_id, call_graph, owners_by_id)
        for owner_id in owners_by_id
    }

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
            row["functionInstanceIdentity"] = function_identity(owner)
        owner_calls = (active_extent_calls(owner, call_graph, owners_by_id, instruction_rows)
                       if is_level4_dynamic_decoder(owner) else calls_by_owner[owner["id"]])
        if owner_calls:
            row["calls"] = [
                active_callee_frame(owner, call, call_graph, owners_by_id, instruction_rows,
                                    frozenset({owner["id"]})) if is_level4_dynamic_decoder(owner) else call
                for call in owner_calls
            ]
        tail_dependencies = []
        for call in calls_by_owner[owner["id"]]:
            if call["kind"] != "tail":
                continue
            callee = owners_by_id[call["id"]]
            callee_pcs = sorted(
                address for address in instruction_addresses if in_regions(address, callee["regions"])
            )
            tail_dependencies.append({
                "functionInstanceId": callee["id"],
                "functionInstanceIdentity": function_identity(callee),
                "transfer": {"sourcePc": call["sourcePc"], "targetPc": call["targetPc"]},
                "calleeInstructionPcs": callee_pcs,
                "completionSourcePcs": callee.get("exitPcs", []),
                "combinedInstructionPcs": sorted(set(instruction_pcs) | set(callee_pcs)),
            })
        if tail_dependencies:
            row["tailDependencies"] = tail_dependencies
        handoffs = attribution_fragment_handoffs(owner, decode_raw, owners_by_id, instruction_rows)
        if is_level4_dynamic_decoder(owner):
            row["fullExecutionPcs"] = dynamic_full_execution_pcs(owner, owners_by_id)
            row["ownedExecutionPcs"] = dynamic_owned_execution_pcs(owner, instruction_rows)
            row["subtreeOwnedExecutionPcs"] = sorted(
                address for address, instruction in instruction_rows.items()
                if instruction.get("owner") in descendant_owner_ids(owners_by_id, owner["id"]))
            row["fragmentHandoffs"] = handoffs
            row["parentReentryEdges"] = parent_fragment_reentries(
                owner, decode_raw, owners_by_id, instruction_rows
            )
            row["carrierRoutes"] = outcome_carrier_routes(
                owner, decode_raw, instruction_rows, database.get("level4SourceReviewEvidence"),
                decode_raw_continuation_owners, owners_by_id, row.get("calls", []),
            )
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
    validate_level4_attribution_boundaries(database, manifest)
    return manifest


def validate_level4_attribution_boundaries(database: dict, manifest: dict) -> None:
    """Recompute every dynamic boundary from Program identities and decoded ownership/CFG."""
    owners_by_id = {owner["id"]: owner for owner in database["callGraph"]["owners"]}
    instructions = {row["address"]: row for row in database["instructions"]}
    decode_raw = owners_by_id[manifest["parent"]["id"]]
    decode_raw_continuation_owners = descendant_owner_ids(owners_by_id, decode_raw["id"])
    for row in manifest["boundaries"]:
        owner = owners_by_id[row["id"]]
        if not is_level4_dynamic_decoder(owner):
            continue
        expected_full = dynamic_full_execution_pcs(owner, owners_by_id)
        expected_owned = dynamic_owned_execution_pcs(owner, instructions)
        expected_subtree_owned = sorted(address for address, instruction in instructions.items()
                                        if instruction.get("owner") in descendant_owner_ids(owners_by_id, owner["id"]))
        expected_handoffs = attribution_fragment_handoffs(owner, decode_raw, owners_by_id, instructions)
        expected_reentries = parent_fragment_reentries(owner, decode_raw, owners_by_id, instructions)
        for call in row.get("calls", []):
            validate_active_callee_frame_shape(call)
        expected_calls = [active_callee_frame(owner, call, database["callGraph"], owners_by_id,
                                               instructions, frozenset({owner["id"]}))
                          for call in active_extent_calls(owner, database["callGraph"], owners_by_id,
                                                          instructions)]
        if row.get("fullExecutionPcs") != expected_full:
            raise ValueError("Level 4 full execution PCs are incomplete or forged")
        if row.get("ownedExecutionPcs") != expected_owned:
            raise ValueError("Level 4 owned execution PCs are incomplete or forged")
        if row.get("subtreeOwnedExecutionPcs") != expected_subtree_owned:
            raise ValueError("Level 4 subtree-owned execution PCs are incomplete or forged")
        if row.get("fragmentHandoffs") != expected_handoffs:
            raise ValueError("Level 4 attribution fragment handoffs are incomplete or forged")
        if row.get("parentReentryEdges") != expected_reentries:
            raise ValueError("Level 4 parent fragment re-entries are incomplete or forged")
        # Small unit fixtures exercise the attribution validator in isolation and predate the
        # carrier schema. The complete manifest validator below requires this field for every
        # production dynamic row, so a generated-manifest deletion is still rejected.
        if "carrierRoutes" in row:
            expected_carriers = outcome_carrier_routes(
                owner, decode_raw, instructions, database.get("level4SourceReviewEvidence"),
                decode_raw_continuation_owners, owners_by_id, expected_calls,
            )
            if row["carrierRoutes"] != expected_carriers:
                raise ValueError("Level 4 outcome carrier routes are incomplete or forged")
            validate_outcome_carrier_instructions(
                row["carrierRoutes"], decode_raw["id"], instructions, decode_raw_continuation_owners, owners_by_id
            )
        if row.get("calls", []) != expected_calls:
            raise ValueError("Level 4 dynamic call target extents are incomplete or forged")


def validate_attribution_target_identity(identity: object) -> None:
    if (not isinstance(identity, dict)
            or identity.get("kind") not in {"functionInstance", "excludedFunctionInstance"}
            or not isinstance(identity.get("qualified"), str)
            or not isinstance(identity.get("sourceFile"), str)):
        raise ValueError("Level 4 active callee lacks a tagged source identity")


def validate_active_callee_frame_shape(call: object, ancestors: frozenset[str] = frozenset()) -> None:
    """Check the recursive manifest shape before recomputing it from the production CFG.

    The recursive recomputation below is the authoritative check.  This structural pass gives a
    precise rejection for malformed children and prevents a forged cycle back-edge from hiding a
    foreign sibling before the recomputation gets a chance to compare the full tree.
    """
    if (not isinstance(call, dict) or not isinstance(call.get("id"), str)
            or not isinstance(call.get("kind"), str)
            or not isinstance(call.get("sourcePc"), (int, type(None)))
            or not isinstance(call.get("targetPc"), int)):
        raise ValueError("Level 4 active callee lacks concrete call identity and PCs")
    validate_attribution_target_identity(call.get("callerIdentity"))
    validate_attribution_target_identity(call.get("targetIdentity"))
    extent = call.get("activeCalleeExecutionPcs")
    if not isinstance(extent, list) or not extent or extent != sorted(set(extent)):
        raise ValueError("Level 4 active callee has an invalid exact execution extent")
    return_sites = call.get("returnSites")
    if not isinstance(return_sites, list):
        raise ValueError("Level 4 active callee lacks per-site RA obligations")
    if call["kind"] == "direct" and not return_sites:
        raise ValueError("Level 4 direct active callee lacks per-site RA obligations")
    for site in return_sites:
        if (not isinstance(site, dict)
                or not isinstance(site.get("sourcePc"), int)
                or not isinstance(site.get("targetPc"), int)
                or not isinstance(site.get("returnPc"), int)
                or site.get("linkRegister") != "ra"
                or site["targetPc"] != call["targetPc"]
                or site["returnPc"] != site["sourcePc"] + 4
                or (call["sourcePc"] is not None and site["sourcePc"] != call["sourcePc"])):
            raise ValueError("Level 4 active callee has an invalid RA obligation")
    cycle_back_edge = call.get("cycleBackEdge")
    children = call.get("activeCalleeFrames")
    if not isinstance(children, list):
        raise ValueError("Level 4 active callee lacks recursive cycle metadata")
    is_cycle = call["id"] in ancestors
    if is_cycle:
        if not isinstance(cycle_back_edge, dict):
            raise ValueError("Level 4 active callee lacks its ancestor cycle back-edge")
        if (cycle_back_edge.get("ancestorId") != call["id"]
                or cycle_back_edge.get("ancestorIdentity") != call["targetIdentity"]
                or cycle_back_edge.get("ancestorExecutionPcs") != call["activeCalleeExecutionPcs"]):
            raise ValueError("Level 4 active callee has a forged ancestor cycle back-edge")
        transitions = cycle_back_edge.get("transitions")
        if (not isinstance(transitions, list) or not transitions
                or transitions != sorted(transitions, key=lambda edge: edge.get("sourcePc", -1))):
            raise ValueError("Level 4 active callee has incomplete cycle back-edge transitions")
        if any(not isinstance(edge, dict) or not isinstance(edge.get("sourcePc"), int)
               or edge.get("targetPc") != call["targetPc"] for edge in transitions):
            raise ValueError("Level 4 active callee has invalid cycle back-edge transitions")
        if children:
            raise ValueError("Level 4 active callee expands beyond its ancestor cycle back-edge")
        return
    if cycle_back_edge is not None:
        raise ValueError("Level 4 active callee has a forged ancestor cycle back-edge")
    for child in children:
        validate_active_callee_frame_shape(child, ancestors | {call["id"]})


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
        if "stores" in row:
            raise ValueError("Level 4 boundary manifest cannot claim dynamic stores statically")
        if "calls" in row:
            if not isinstance(row["calls"], list):
                raise ValueError("Level 4 boundary manifest calls field is not a list")
            for call in row["calls"]:
                if (not isinstance(call, dict) or not isinstance(call.get("sourcePc"), (int, type(None)))
                        or not isinstance(call.get("targetPc"), int)):
                    raise ValueError("Level 4 boundary manifest call lacks concrete PCs")
                if "targetIdentity" in call:
                    validate_active_callee_frame_shape(call)
        dependencies = row.get("tailDependencies", [])
        if not isinstance(dependencies, list):
            raise ValueError("Level 4 boundary manifest tailDependencies field is not a list")
        for dependency in dependencies:
            if (not isinstance(dependency, dict)
                    or not isinstance(dependency.get("functionInstanceId"), str)
                    or not isinstance(dependency.get("functionInstanceIdentity"), dict)
                    or not isinstance(dependency.get("functionInstanceIdentity", {}).get("qualified"), str)
                    or not isinstance(dependency.get("transfer"), dict)
                    or not isinstance(dependency.get("transfer", {}).get("sourcePc"), int)
                    or not isinstance(dependency.get("transfer", {}).get("targetPc"), int)):
                raise ValueError("Level 4 tail dependency lacks a generated identity or transfer PCs")
            for field in ("calleeInstructionPcs", "completionSourcePcs", "combinedInstructionPcs"):
                pcs = dependency.get(field)
                if not isinstance(pcs, list) or not pcs or pcs != sorted(set(pcs)):
                    raise ValueError(f"Level 4 tail dependency has invalid {field}")
            callee_pcs = set(dependency["calleeInstructionPcs"])
            combined_pcs = set(dependency["combinedInstructionPcs"])
            if dependency["transfer"]["sourcePc"] not in row["instructionPcs"]:
                raise ValueError("Level 4 tail dependency transfer source is outside its wrapper")
            if dependency["transfer"]["targetPc"] not in callee_pcs:
                raise ValueError("Level 4 tail dependency transfer target is outside its callee")
            if not set(dependency["completionSourcePcs"]) <= callee_pcs:
                raise ValueError("Level 4 tail dependency completion is outside its callee")
            if combined_pcs != set(row["instructionPcs"]) | callee_pcs:
                raise ValueError("Level 4 tail dependency combined region is not exact")
        handoffs = row.get("fragmentHandoffs")
        if handoffs is not None:
            full_pcs = row.get("fullExecutionPcs")
            owned_pcs = row.get("ownedExecutionPcs")
            subtree_pcs = row.get("subtreeOwnedExecutionPcs")
            reentries = row.get("parentReentryEdges")
            carrier_routes = row.get("carrierRoutes")
            if (not isinstance(full_pcs, list) or not full_pcs
                    or full_pcs != sorted(set(full_pcs))):
                raise ValueError("Level 4 dynamic boundary lacks a full execution extent")
            if (not isinstance(owned_pcs, list) or not owned_pcs
                    or owned_pcs != sorted(set(owned_pcs)) or not set(owned_pcs) <= set(full_pcs)):
                raise ValueError("Level 4 dynamic boundary lacks owned execution PCs")
            if (not isinstance(subtree_pcs, list) or not subtree_pcs
                    or subtree_pcs != sorted(set(subtree_pcs)) or not set(subtree_pcs) <= set(full_pcs)):
                raise ValueError("Level 4 dynamic boundary lacks subtree-owned execution PCs")
            if not isinstance(carrier_routes, list) or len(carrier_routes) != len(handoffs):
                raise ValueError("Level 4 dynamic boundary lacks one carrier route per handoff")
            handoff_keys = {(edge["sourcePc"], edge["targetPc"]) for edge in handoffs}
            route_keys = set()
            for route in carrier_routes:
                if not isinstance(route, dict) or not isinstance(route.get("handoff"), dict):
                    raise ValueError("Level 4 carrier route lacks a handoff")
                handoff = route["handoff"]
                key = handoff.get("sourcePc"), handoff.get("targetPc")
                if key not in handoff_keys or key in route_keys:
                    raise ValueError("Level 4 carrier route does not key one declared handoff")
                route_keys.add(key)
                identity = route.get("sourceIdentity")
                review = route.get("sourceReview")
                if (not isinstance(identity, dict) or identity.get("qualified") != row["qualified"]
                        or not isinstance(review, dict) or review.get("sourceFile") != row.get(
                            "functionInstanceIdentity", {}).get("sourceFile")
                        or not isinstance(review.get("sourceContentSha256"), str)
                        or not isinstance(review.get("sourceDeclaration"), str)
                        or not isinstance(review.get("sourceCall"), str)):
                    raise ValueError("Level 4 carrier route lacks its source identity and review")
                classification = route.get("classification")
                if classification not in {"intermediate", "unclassified", "rejectionPhaseHandoff",
                                          "sourceReviewedOutcomePath"}:
                    raise ValueError("Level 4 carrier route has an invalid classification")
                predecessors = route.get("admissiblePredecessors")
                if (not isinstance(predecessors, list)
                        or any(not isinstance(pc, int) for pc in predecessors)
                        or len(predecessors) != len(set(predecessors))):
                    raise ValueError("Level 4 carrier route lacks exact admissible predecessors")
                for field in ("carrierPcs", "carrierPaths", "registers", "stackDescriptors"):
                    if not isinstance(route.get(field), list):
                        raise ValueError(f"Level 4 carrier route lacks {field}")
                for path in route["carrierPaths"]:
                    if (not isinstance(path, dict) or not isinstance(path.get("carrierPc"), int)
                            or not isinstance(path.get("pcs"), list) or not path["pcs"]
                            or not isinstance(path.get("ownerIds"), list)
                            or len(path["pcs"]) != len(path["ownerIds"])
                            or any(not isinstance(owner_id, str) for owner_id in path["ownerIds"])):
                        raise ValueError("Level 4 carrier path lacks exact CFG ownership")
                for descriptor in route["stackDescriptors"]:
                    if (not isinstance(descriptor, dict)
                            or descriptor.get("instructionKind") not in {"addi", "load", "store"}
                            or not isinstance(descriptor.get("pc"), int)
                            or not isinstance(descriptor.get("register"), str)
                            or not isinstance(descriptor.get("baseRegister"), str)
                            or not isinstance(descriptor.get("offset"), int)):
                        raise ValueError("Level 4 carrier stack descriptor is malformed")
                if classification in {"intermediate", "unclassified", "rejectionPhaseHandoff"} and any(route[field] for field in (
                        "carrierPcs", "carrierPaths", "registers", "stackDescriptors")):
                    raise ValueError("Level 4 non-outcome route falsely claims an outcome carrier")
                if classification == "intermediate" and route.get("intermediateReason") != "reenters-child":
                    raise ValueError("Level 4 intermediate route lacks its non-outcome reason")
                if classification == "unclassified" and route.get("unclassifiedReason") != (
                        "handoff-target-does-not-reach-reviewed-carrier-in-parent-cfg"):
                    raise ValueError("Level 4 unclassified route lacks its CFG reason")
                if classification == "rejectionPhaseHandoff" and (
                        route.get("intermediateReason") is not None or route.get("unclassifiedReason") is not None):
                    raise ValueError("Level 4 rejection handoff falsely claims another route class")
                if classification == "sourceReviewedOutcomePath":
                    if route.get("intermediateReason") is not None or route.get("unclassifiedReason") is not None:
                        raise ValueError("Level 4 outcome route falsely claims a non-outcome reason")
                    if len(route["carrierPaths"]) != len(route["carrierPcs"]):
                        raise ValueError("Level 4 outcome route lacks one path per carrier PC")
            if route_keys != handoff_keys:
                raise ValueError("Level 4 carrier route inventory is incomplete or forged")
            for edges, label in ((handoffs, "handoffs"), (reentries, "re-entries")):
                if (not isinstance(edges, list) or not edges
                        or edges != sorted(edges, key=lambda edge: (edge.get("sourcePc", -1), edge.get("targetPc", -1)))):
                    raise ValueError(f"Level 4 attribution fragment {label} are absent or unsorted")
            for edge in handoffs:
                if (not isinstance(edge, dict) or not isinstance(edge.get("sourcePc"), int)
                        or not isinstance(edge.get("targetPc"), int)
                        or edge["sourcePc"] not in subtree_pcs):
                    raise ValueError("Level 4 attribution handoff source is outside subtree execution")
            for edge in reentries:
                if (not isinstance(edge, dict) or not isinstance(edge.get("sourcePc"), int)
                        or not isinstance(edge.get("targetPc"), int)
                        or edge["targetPc"] not in subtree_pcs):
                    raise ValueError("Level 4 attribution re-entry target is outside subtree execution")
    direct_offsets = [row for row in boundaries if row["qualified"] == "ssz_raw.readOffset"]
    if len(direct_offsets) != 4 or any(not row["instructionPcs"] for row in direct_offsets):
        raise ValueError("Level 4 direct readOffset boundaries are incomplete")


def lean_name_component(text: str) -> str:
    component = re.sub(r"[^A-Za-z0-9_']", "_", text)
    component = re.sub(r"_+", "_", component).strip("_")
    return component or "anonymous"


def function_instance_lean_name(identity: dict) -> str:
    """The same source-derived generated name as generate_elfling_program.py."""
    parts = ["functionInstance", lean_name_component(identity["qualified"])]
    if identity.get("specialization"):
        parts += ["specialized"] + [lean_name_component(value) for value in identity["specialization"]]
    for frame in identity.get("inlineStack", []):
        parts += ["in", lean_name_component(frame["callerQualified"]), "at",
                  str(frame["line"]), str(frame["column"])]
    return "_".join(parts)


def target_lean_name(identity: dict) -> str:
    if identity["kind"] == "excludedFunctionInstance":
        return "excludedFunctionInstance_" + lean_name_component(identity["qualified"])
    return function_instance_lean_name(identity)


def emit_level4_attribution_lean(database: dict) -> str:
    """Emit the four dynamic attribution boundaries as typed, source-identity keyed Lean data."""
    manifest = level4_boundary_manifest(database)
    rows = [row for row in manifest["boundaries"] if "fragmentHandoffs" in row]
    expected_handoffs = [14, 8, 12, 5]
    expected_reentries = [4, 4, 2, 1]
    expected_call_frames = [38, 6, 5, 2]
    if [len(row["fragmentHandoffs"]) for row in rows] != expected_handoffs:
        raise ValueError("Level 4 attribution fragment handoff inventory changed")
    if [len(row["parentReentryEdges"]) for row in rows] != expected_reentries:
        raise ValueError("Level 4 attribution fragment re-entry inventory changed")
    if [len(row.get("calls", [])) for row in rows] != expected_call_frames:
        raise ValueError("Level 4 dynamic call-frame inventory changed")
    recursive_call_frame_count = active_callee_frame_count(
        [frame for row in rows for frame in row.get("calls", [])]
    )
    if recursive_call_frame_count != 79:
        raise ValueError("Level 4 recursive decoded call-frame inventory changed")
    def recursive_frames(frames: list[dict]) -> list[dict]:
        return [frame for root in frames for frame in
                [root, *recursive_frames(root["activeCalleeFrames"])]]
    decoded_frames = recursive_frames([frame for row in rows for frame in row.get("calls", [])])
    required_decoded_calls = {
        # fi:45's direct allocator boundary, and the previously omitted excluded-body calls.
        ("fi:45", 0x115e8, 0x135e0),
        ("excluded:5", 0x1356c, 0x135e0),
        ("excluded:10", 0x136d0, 0x130ac),
        ("excluded:10", 0x136e4, 0x136f8),
    }
    actual_decoded_calls = {
        (frame["callerId"], frame["sourcePc"], frame["targetPc"])
        for frame in decoded_frames
    }
    if not required_decoded_calls <= actual_decoded_calls:
        raise ValueError("Level 4 required decoded excluded-body call inventory changed")
    parent_owner = next(owner for owner in database["callGraph"]["owners"]
                        if owner["id"] == manifest["parent"]["id"])
    parent_identity = {
        "qualified": parent_owner["qualified"],
        "specialization": parent_owner.get("specialization", []),
        "inlineStack": parent_owner.get("inlineStack", []),
    }
    parent_name = function_instance_lean_name(parent_identity)
    owners_by_id = {owner["id"]: owner for owner in database["callGraph"]["owners"]}
    instruction_rows = {instruction["address"]: instruction for instruction in database["instructions"]}
    L = [
        "-- GENERATED FILE: produced by tools/generate_machine_regions.py. DO NOT EDIT.",
        "import BinaryFv.RiscV.Elfling.Boundary",
        "import BinaryFv.Zesu.Elflings.GeneratedProgramCfg",
        "import GeneratedProgram",
        "",
        "set_option maxRecDepth 8000",
        "",
        "/-! Exact Level 4 dynamic inline attribution boundaries.  The source-derived identities,",
        "decoded deepest ownership, and CFG determine every list below.  The Lean facts establish",
        "exact emitted decoded-call/target/identity/RA data; the Python validator independently",
        "recomputes complete lists from the production Program and decoded CFG. -/",
        "",
        "namespace BinaryFv.Zesu.Elflings.GeneratedLevel4Attribution",
        "",
        "open BinaryFv.Binary.Elfling",
        "open BinaryFv.RiscV.Elfling",
        "open BinaryFv.Zesu.Elflings.Generated",
        "open BinaryFv.Zesu.Elflings.Validation",
        "",
        "inductive AttributionCallTarget where",
        "  | functionInstance : FunctionInstanceId → AttributionCallTarget",
        "  | excludedFunctionInstance : FunctionInstanceId → AttributionCallTarget",
        "",
        "inductive ReturnAddressBinding where",
        "  | jalrX1X1 : ReturnAddressBinding",
        "  deriving DecidableEq",
        "",
        "structure AttributionReturnObligation where",
        "  callSource : Nat",
        "  calleeTarget : Nat",
        "  returnPc : Nat",
        "  raBinding : ReturnAddressBinding",
        "  deriving DecidableEq",
        "",
        "structure AttributionCycleBackEdge where",
        "  ancestor : AttributionCallTarget",
        "  ancestorExecutionPcs : Array Nat",
        "  transitions : Array DirectEdge",
        "",
        "structure AttributionCallFrame where",
        "  kind : String",
        "  source : Option Nat",
        "  target : Nat",
        "  caller : AttributionCallTarget",
        "  callee : AttributionCallTarget",
        "  activeCalleeExecutionPcs : Array Nat",
        "  returnObligations : Array AttributionReturnObligation",
        "  activeCalleeFrames : Array AttributionCallFrame",
        "  cycleBackEdge : Option AttributionCycleBackEdge",
        "",
        "structure AttributionFragmentBoundary where",
        "  child : FunctionInstanceId",
        "  ownedExecutionPcs : Array Nat",
        "  subtreeOwnedExecutionPcs : Array Nat",
        "  fullExecutionPcs : Array Nat",
        "  callFrames : Array AttributionCallFrame",
        "  handoffs : Array DirectEdge",
        "  reentries : Array DirectEdge",
        "",
        "/-- Classification of a decoded child-to-parent handoff. This is geometry and audited",
        "source provenance, not a contract postcondition. -/",
        "inductive OutcomeCarrierRouteClass where",
        "  | intermediate",
        "  | unclassified",
        "  | rejectionPhaseHandoff",
        "  | sourceReviewedOutcomePath",
        "",
        "structure CarrierRegister where",
        "  pc : Nat",
        "  register : String",
        "  role : String",
        "",
        "structure CarrierStackDescriptor where",
        "  pc : Nat",
        "  instructionKind : String",
        "  register : String",
        "  baseRegister : String",
        "  offset : Nat",
        "  role : String",
        "",
        "structure CarrierPath where",
        "  carrierPc : Nat",
        "  pcs : Array Nat",
        "",
        "structure CarrierStatusTag where",
        "  state : String",
        "  pc : Option Nat",
        "  baseRegister : Option String",
        "  offset : Option Nat",
        "  width : Option Nat",
        "  value : Option Nat",
        "  reason : String",
        "",
        "structure CarrierAllocation where",
        "  state : String",
        "  reason : String",
        "",
        "structure CarrierHeapArrayRep where",
        "  state : String",
        "  baseRegister : Option String",
        "  countRegister : Option String",
        "  elementBytes : Option Nat",
        "  reason : String",
        "",
        "/-- The exact source-identity-plus-edge key and its audited parent continuation data.",
        "The carrier fields distinguish static/source review from outstanding machine obligations;",
        "they do not assert an outcome value, HeapArrayRep, or universal frame. -/",
        "structure AttributionOutcomeCarrierRoute where",
        "  child : FunctionInstanceId",
        "  handoff : DirectEdge",
        "  classification : OutcomeCarrierRouteClass",
        "  intermediateReason : Option String",
        "  unclassifiedReason : Option String",
        "  sourceLine : Nat",
        "  sourceResult : String",
        "  admissiblePredecessors : Array Nat",
        "  carrierPcs : Array Nat",
        "  carrierPaths : Array CarrierPath",
        "  registers : Array CarrierRegister",
        "  stackDescriptors : Array CarrierStackDescriptor",
        "  statusTag : CarrierStatusTag",
        "  allocation : CarrierAllocation",
        "  heapArrayRep : CarrierHeapArrayRep",
        "",
    ]
    boundary_names = []
    carrier_route_names = []
    for row in rows:
        identity = row["functionInstanceIdentity"]
        name = function_instance_lean_name(identity)
        boundary_name = f"{name}_attributionBoundary"
        boundary_names.append(boundary_name)
        child = name
        pairs = lambda edges: ", ".join(
            f"{{ source := {edge['sourcePc']}, target := {edge['targetPc']} }}" for edge in edges)
        edge_array = lambda edges: f"(#[{pairs(edges)}] : Array DirectEdge)"
        pcs = lambda xs: ", ".join(str(x) for x in xs)
        def source_owner_disjunction(edges: list[dict], endpoint: str) -> str:
            """Exact deepest generated owner for each dynamic subtree edge endpoint.

            ``ownedBy`` only describes one direct FunctionInstance. Dynamic boundary edges may
            instead originate in a nested inline child, so the generated fact names the decoded
            deepest owner for every finite handoff/re-entry endpoint rather than pretending the
            selected root directly owns all of them.
            """
            clauses = []
            for edge in edges:
                pc = edge[endpoint]
                owner = owners_by_id[instruction_rows[pc]["owner"]]
                if owner["id"].startswith("excluded:"):
                    raise ValueError("Level 4 dynamic attribution edge endpoint is excluded")
                clauses.append(
                    f"(edge.{endpoint[:-2]} = {pc} ∧ ownedBy generatedProgram "
                    f"{function_instance_lean_name(owner)} edge.{endpoint[:-2]} = true)"
                )
            return " ∨ ".join(clauses)
        def carrier_route(route: dict) -> str:
            classification = {
                "intermediate": ".intermediate",
                "unclassified": ".unclassified",
                "rejectionPhaseHandoff": ".rejectionPhaseHandoff",
                "sourceReviewedOutcomePath": ".sourceReviewedOutcomePath",
            }[route["classification"]]
            handoff = route["handoff"]
            registers = ", ".join(
                '{ pc := %s, register := "%s", role := "%s" }' %
                (register["pc"], register["register"], register["role"])
                for register in route["registers"]
            )
            descriptors = ", ".join(
                '{ pc := %s, instructionKind := "%s", register := "%s", baseRegister := "%s", offset := %s, role := "%s" }' %
                (descriptor["pc"], descriptor["instructionKind"], descriptor["register"], descriptor["baseRegister"],
                 descriptor["offset"], descriptor["role"])
                for descriptor in route["stackDescriptors"]
            )
            paths = ", ".join(
                '{ carrierPc := %s, pcs := #[%s] }' % (path["carrierPc"], pcs(path["pcs"]))
                for path in route["carrierPaths"]
            )
            optional_nat = lambda value: "none" if value is None else f"some {value}"
            optional_string = lambda value: "none" if value is None else f'some "{value}"'
            status = route["statusTag"]
            status_lean = (
                '{ state := "%s", pc := %s, baseRegister := %s, offset := %s, width := %s, '
                'value := %s, reason := "%s" }' %
                (status["state"], optional_nat(status.get("pc")), optional_string(status.get("baseRegister")),
                 optional_nat(status.get("offset")), optional_nat(status.get("width")),
                 optional_nat(status.get("value")), status.get("reason", ""))
            )
            allocation = route["allocation"]
            allocation_lean = '{ state := "%s", reason := "%s" }' % (
                allocation["state"], allocation.get("reason", ""))
            heap = route["heapArrayRep"]
            heap_lean = (
                '{ state := "%s", baseRegister := %s, countRegister := %s, elementBytes := %s, reason := "%s" }' %
                (heap["state"], optional_string(heap.get("baseRegister")),
                 optional_string(heap.get("countRegister")), optional_nat(heap.get("elementBytes")),
                 heap.get("reason", ""))
            )
            return (
                "{ child := %sId, handoff := { source := %s, target := %s }, classification := %s, intermediateReason := %s, unclassifiedReason := %s, sourceLine := %s, sourceResult := \"%s\", "
                "admissiblePredecessors := #[%s], carrierPcs := #[%s], carrierPaths := #[%s], registers := #[%s], stackDescriptors := #[%s], "
                "statusTag := %s, allocation := %s, heapArrayRep := %s }"
                % (child, handoff["sourcePc"], handoff["targetPc"], classification,
                   optional_string(route["intermediateReason"]), optional_string(route["unclassifiedReason"]),
                   route["sourceReview"]["sourceLine"], route["sourceReview"]["sourceResult"],
                   pcs(route["admissiblePredecessors"]), pcs(route["carrierPcs"]), paths, registers, descriptors, status_lean, allocation_lean,
                   heap_lean)
            )
        def cycle_back_edge_expr(cycle: dict | None) -> str:
            if cycle is None:
                return "none"
            ancestor_identity = cycle["ancestorIdentity"]
            ancestor = target_lean_name(ancestor_identity)
            ancestor_target = (f".excludedFunctionInstance {ancestor}Id"
                               if ancestor_identity["kind"] == "excludedFunctionInstance"
                               else f".functionInstance {ancestor}Id")
            transitions = ", ".join(
                f"{{ source := {edge['sourcePc']}, target := {edge['targetPc']} }}"
                for edge in cycle["transitions"]
            )
            return (f"some {{ ancestor := {ancestor_target}, ancestorExecutionPcs := "
                    f"#[{pcs(cycle['ancestorExecutionPcs'])}], transitions := #[{transitions}] }}")

        def call_target_expr(identity: dict) -> str:
            name = target_lean_name(identity)
            return (f".excludedFunctionInstance {name}Id"
                    if identity["kind"] == "excludedFunctionInstance"
                    else f".functionInstance {name}Id")

        def call_frame(call: dict) -> str:
            caller_identity = call["callerIdentity"]
            identity = call["targetIdentity"]
            caller_target = call_target_expr(caller_identity)
            target = call_target_expr(identity)
            source = "none" if call["sourcePc"] is None else f"some {call['sourcePc']}"
            obligations = ", ".join(
                "{ callSource := %s, calleeTarget := %s, returnPc := %s, raBinding := .jalrX1X1 }"
                % (site["sourcePc"], site["targetPc"], site["returnPc"])
                for site in call.get("returnSites", [])
            )
            cycle_back_edge = cycle_back_edge_expr(call["cycleBackEdge"])
            children = ", ".join(call_frame(child) for child in call.get("activeCalleeFrames", []))
            return (
                "{ kind := \"%s\", source := %s, target := %s, caller := %s, callee := %s, "
                "activeCalleeExecutionPcs := #[%s], returnObligations := #[%s], "
                "activeCalleeFrames := #[%s], cycleBackEdge := %s }"
                % (call["kind"], source, call["targetPc"], caller_target, target,
                   pcs(call["activeCalleeExecutionPcs"]), obligations, children,
                   cycle_back_edge)
            )
        call_frames = f"(#[{', '.join(call_frame(call) for call in row.get('calls', []))}] : Array AttributionCallFrame)"
        carrier_route_names_for_boundary = [
            f"{boundary_name}_carrierRoute_{route['handoff']['sourcePc']}_{route['handoff']['targetPc']}"
            for route in row["carrierRoutes"]
        ]
        carrier_route_names.extend(carrier_route_names_for_boundary)
        carrier_routes = "(#[%s] : Array AttributionOutcomeCarrierRoute)" % ", ".join(
            carrier_route_names_for_boundary)
        for carrier_route_name, route in zip(carrier_route_names_for_boundary, row["carrierRoutes"]):
            predecessor_array = f"(#[{pcs(route['admissiblePredecessors'])}] : Array Nat)"
            stages = [row["entryPc"]] + sorted(
                {edge["targetPc"] for edge in row["parentReentryEdges"]} - {row["entryPc"]}
            )
            stage_disjunction = " ∨ ".join(f"pc = {stage}" for stage in stages)
            L.extend([
                f"noncomputable def {carrier_route_name} : AttributionOutcomeCarrierRoute :=",
                f"  {carrier_route(route)}",
                f"theorem {carrier_route_name}_admissiblePredecessors_exact :",
                f"    {carrier_route_name}.admissiblePredecessors = {predecessor_array} := rfl",
                f"theorem {carrier_route_name}_admissiblePredecessors_are_stages :",
                f"    ∀ pc ∈ {predecessor_array}, {stage_disjunction} := by native_decide",
                "",
            ])
        L.extend([
            f"noncomputable def {boundary_name} : AttributionFragmentBoundary :=",
            f"  {{ child := {child}Id, ownedExecutionPcs := #[{pcs(row['ownedExecutionPcs'])}],",
            f"    subtreeOwnedExecutionPcs := #[{pcs(row['subtreeOwnedExecutionPcs'])}],",
            f"    fullExecutionPcs := #[{pcs(row['fullExecutionPcs'])}],",
            f"    callFrames := {call_frames},",
            f"    handoffs := {edge_array(row['fragmentHandoffs'])},",
            f"    reentries := {edge_array(row['parentReentryEdges'])} }}",
            f"",
            f"theorem {boundary_name}_child : {boundary_name}.child = {child}Id := rfl",
            f"theorem {boundary_name}_ownedExecutionPcs_exact :",
            f"    {boundary_name}.ownedExecutionPcs = #[{pcs(row['ownedExecutionPcs'])}] := rfl",
            f"theorem {boundary_name}_subtreeOwnedExecutionPcs_exact :",
            f"    {boundary_name}.subtreeOwnedExecutionPcs = #[{pcs(row['subtreeOwnedExecutionPcs'])}] := rfl",
            f"theorem {boundary_name}_fullExecutionPcs_exact :",
            f"    {boundary_name}.fullExecutionPcs = #[{pcs(row['fullExecutionPcs'])}] := rfl",
            f"theorem {boundary_name}_callFrames_exact :",
            f"    {boundary_name}.callFrames = {call_frames} := rfl",
            f"theorem {boundary_name}_handoffs_exact :",
            f"    {boundary_name}.handoffs = {edge_array(row['fragmentHandoffs'])} := rfl",
            f"theorem {boundary_name}_reentries_exact :",
            f"    {boundary_name}.reentries = {edge_array(row['parentReentryEdges'])} := rfl",
            f"noncomputable def {boundary_name}_carrierRoutes : Array AttributionOutcomeCarrierRoute :=",
            f"  {carrier_routes}",
            f"theorem {boundary_name}_carrierRoutes_exact :",
            f"    {boundary_name}_carrierRoutes = {carrier_routes} := rfl",
            f"theorem {boundary_name}_counts :",
            f"    {edge_array(row['fragmentHandoffs'])}.size = {len(row['fragmentHandoffs'])} ∧",
            f"    {edge_array(row['parentReentryEdges'])}.size = {len(row['parentReentryEdges'])} := by native_decide",
            f"theorem {boundary_name}_cfg_and_ownership :",
            f"    (∀ edge ∈ {edge_array(row['fragmentHandoffs'])},",
            f"      programContainsEdge generatedProgram edge = true ∧",
            f"      ({source_owner_disjunction(row['fragmentHandoffs'], 'sourcePc')}) ∧",
            f"      ownedBy generatedProgram {parent_name} edge.target = true) ∧",
            f"    (∀ edge ∈ {edge_array(row['parentReentryEdges'])},",
            f"      programContainsEdge generatedProgram edge = true ∧",
            f"      ownedBy generatedProgram {parent_name} edge.source = true ∧",
            f"      ({source_owner_disjunction(row['parentReentryEdges'], 'targetPc')})) := by native_decide",
            "",
        ])
        for route_index, (carrier_route_name, route) in enumerate(
                zip(carrier_route_names_for_boundary, row["carrierRoutes"])):
            if route["classification"] != "sourceReviewedOutcomePath":
                continue
            for path_index, path in enumerate(route["carrierPaths"]):
                path_name = (
                    f"{boundary_name}_carrierRoute_{route['handoff']['sourcePc']}_"
                    f"{route['handoff']['targetPc']}_path_{path['carrierPc']}"
                )
                path_pcs = f"#[{pcs(path['pcs'])}]"
                path_edges = [
                    {"sourcePc": source, "targetPc": target}
                    for source, target in zip(path["pcs"], path["pcs"][1:])
                ]
                endpoint_owner = target_lean_name(owners_by_id[path["ownerIds"][-1]])
                path_owner_disjunction = " ∨ ".join(
                    f"(pc = {pc} ∧ ownedBy generatedProgram "
                    f"{target_lean_name(owners_by_id[owner_id])} pc = true)"
                    for pc, owner_id in zip(path["pcs"], path["ownerIds"])
                )
                L.extend([
                    f"theorem {path_name}_exact :",
                    f"    {carrier_route_name}.carrierPaths[{path_index}]? =",
                    f"      some {{ carrierPc := {path['carrierPc']}, pcs := {path_pcs} }} := rfl",
                    f"theorem {path_name}_cfg_and_ownership :",
                    f"    inRegions {parent_name} {path['carrierPc']} = true ∧",
                    f"    ownedBy generatedProgram {endpoint_owner} {path['carrierPc']} = true ∧",
                    f"    (∀ pc ∈ {path_pcs},",
                    f"      ({path_owner_disjunction})) ∧",
                    f"    (∀ edge ∈ {edge_array(path_edges)},",
                    f"      programContainsEdge generatedProgram edge = true) := by native_decide",
                    "",
                ])
        def target_membership(identity: dict, pc: str) -> str:
            name = target_lean_name(identity)
            return (f"inRegions {name} {pc}"
                    if identity["kind"] == "functionInstance"
                    else f"Program.inRanges {name}.regions {pc}")

        def emit_call_frame_facts(call: dict, path: tuple[int, ...], frame_option: str) -> None:
            """Emit exact projections and concrete Program facts at every recursive frame path."""
            path_name = "_".join(str(index) for index in path)
            call_name = f"{boundary_name}_call_{path_name}"
            full_pcs = f"#[{pcs(call['activeCalleeExecutionPcs'])}]"
            frame = call_frame(call)
            membership = target_membership(call["targetIdentity"], "pc")
            source = f"some {call['sourcePc']}"
            caller_target = call_target_expr(call["callerIdentity"])
            callee_target = call_target_expr(call["targetIdentity"])
            L.extend([
                f"theorem {call_name}_exact : {frame_option} = some {frame} := rfl",
                f"theorem {call_name}_decodedCall_target_and_identities_exact :",
                f"    ({frame_option}).map (fun frame =>",
                f"      (frame.source, frame.target, frame.caller, frame.callee)) =",
                f"    some ({source}, {call['targetPc']}, {caller_target}, {callee_target}) := rfl",
                f"theorem {call_name}_extent_membership :",
                f"    ∀ pc ∈ {full_pcs}, {membership} = true := by native_decide",
                f"theorem {call_name}_cycleBackEdge_exact :",
                f"    ({frame_option}).map (·.cycleBackEdge) = some "
                f"{cycle_back_edge_expr(call['cycleBackEdge'])} := rfl",
                "",
            ])
            if call["cycleBackEdge"] is not None:
                transitions = ", ".join(
                    f"{{ source := {edge['sourcePc']}, target := {edge['targetPc']} }}"
                    for edge in call["cycleBackEdge"]["transitions"]
                )
                transition_array = f"(#[{transitions}] : Array DirectEdge)"
                L.extend([
                    f"theorem {call_name}_cycleBackEdge_transitions_cfg :",
                    f"    ∀ edge ∈ {transition_array},",
                    f"      programContainsEdge generatedProgram edge = true ∧ edge.target = {call['targetPc']} := by native_decide",
                    "",
                ])
            obligations = ", ".join(
                "{ callSource := %s, calleeTarget := %s, returnPc := %s, raBinding := .jalrX1X1 }"
                % (site["sourcePc"], site["targetPc"], site["returnPc"])
                for site in call["returnSites"]
            )
            obligation_array = f"(#[{obligations}] : Array AttributionReturnObligation)"
            L.extend([
                f"theorem {call_name}_returnObligations_exact :",
                f"    ({frame_option}).map (·.returnObligations) = some {obligation_array} := rfl",
                f"theorem {call_name}_decodedCall_target_and_ra_exact :",
                f"    ∀ obligation ∈ {obligation_array},",
                f"      obligation.calleeTarget = {call['targetPc']} ∧",
                f"      obligation.returnPc = obligation.callSource + 4 ∧",
                f"      obligation.raBinding = .jalrX1X1 := by native_decide",
                "",
            ])
            for index, nested in enumerate(call["activeCalleeFrames"]):
                emit_call_frame_facts(
                    nested, path + (index,),
                    f"({frame_option}).bind (fun frame => frame.activeCalleeFrames[{index}]?)",
                )

        for index, call in enumerate(row.get("calls", [])):
            emit_call_frame_facts(call, (index,), f"({boundary_name}.callFrames[{index}]?)")
    L.extend([
        "/-- The four selected direct dynamic decoder identities, in source call-site order. -/",
        "noncomputable def level4AttributionFragmentBoundaries : Array AttributionFragmentBoundary :=",
        "  #[" + ", ".join(boundary_names) + "]",
        "",
        "theorem level4AttributionFragmentBoundaries_count :",
        "    level4AttributionFragmentBoundaries.size = 4 := rfl",
        f"def level4AttributionFragmentHandoffCounts : Array Nat := #[{pcs(expected_handoffs)}]",
        f"def level4AttributionFragmentReentryCounts : Array Nat := #[{pcs(expected_reentries)}]",
        f"def level4AttributionCallFrameCounts : Array Nat := #[{pcs(expected_call_frames)}]",
        f"def level4AttributionRecursiveCallFrameCount : Nat := {recursive_call_frame_count}",
        "theorem level4AttributionFragmentHandoff_counts :",
        f"    level4AttributionFragmentHandoffCounts = #[{pcs(expected_handoffs)}] := rfl",
        "theorem level4AttributionFragmentReentry_counts :",
        f"    level4AttributionFragmentReentryCounts = #[{pcs(expected_reentries)}] := rfl",
        "theorem level4AttributionCallFrame_counts :",
        f"    level4AttributionCallFrameCounts = #[{pcs(expected_call_frames)}] := rfl",
        "theorem level4AttributionRecursiveCallFrameCount_exact :",
        f"    level4AttributionRecursiveCallFrameCount = {recursive_call_frame_count} := rfl",
        "theorem level4AttributionFragmentBoundary_totals :",
        "    14 + 8 + 12 + 5 = 39 ∧ 4 + 4 + 2 + 1 = 11 := by decide",
        "/-- All 39 dynamic child-to-parent handoffs, keyed by source-derived child identity and",
        "exact decoded edge. Consumers must inspect `classification` before using carrier fields. -/",
        "noncomputable def level4OutcomeCarrierRoutes : Array AttributionOutcomeCarrierRoute :=",
        "  #[" + ", ".join(carrier_route_names) + "]",
        "theorem level4OutcomeCarrierRoutes_count : level4OutcomeCarrierRoutes.size = 39 := rfl",
        "",
        "end BinaryFv.Zesu.Elflings.GeneratedLevel4Attribution",
        "",
    ])
    return "\n".join(L)


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
    attribution_handoffs = {}
    attribution_reentries = {}
    carrier_routes = {}
    attribution_active_callee_frames = {}
    if any(owner["qualified"] == "ssz_raw.decodeRaw" for owner in call_graph["owners"]):
        boundaries = level4_boundary_manifest(database)["boundaries"]
        attribution_handoffs = {row["id"]: row["fragmentHandoffs"] for row in boundaries
                                if "fragmentHandoffs" in row}
        attribution_reentries = {row["id"]: row["parentReentryEdges"] for row in boundaries
                                 if "parentReentryEdges" in row}
        carrier_routes = {row["id"]: row["carrierRoutes"] for row in boundaries
                          if "carrierRoutes" in row}
        attribution_active_callee_frames = {row["id"]: row.get("calls", []) for row in boundaries
                                            if "fragmentHandoffs" in row}
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
        tail_dependencies = [] if synthetic else [
            {
                "id": call["callee"],
                "qualified": by_id[call["callee"]]["qualified"],
                "transfer": {"source": call["source"], "target": call["evidence"]},
                "completionSourcePcs": by_id[call["callee"]].get("exitPcs", []),
            }
            for call in callees[owner_id] if call["kind"] == "tail"
        ]
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
            "tailDependencies": tail_dependencies,
            "fragmentHandoffs": [] if synthetic else attribution_handoffs.get(owner_id, []),
            "parentReentryEdges": [] if synthetic else attribution_reentries.get(owner_id, []),
            "carrierRoutes": [] if synthetic else carrier_routes.get(owner_id, []),
            "activeCalleeFrames": [] if synthetic else attribution_active_callee_frames.get(owner_id, []),
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
    parser.add_argument("--source-root", type=pathlib.Path, required=True)
    parser.add_argument("--llvm-objdump", required=True)
    parser.add_argument("--out", type=pathlib.Path, required=True)
    parser.add_argument("--out-lean", type=pathlib.Path)
    parser.add_argument("--out-flame", type=pathlib.Path)
    parser.add_argument("--out-level4-boundaries", type=pathlib.Path)
    parser.add_argument("--out-level4-attribution-lean", type=pathlib.Path)
    arguments = parser.parse_args()
    database = build_database(arguments.elf, arguments.program_json, arguments.llvm_objdump)
    database["level4SourceReviewEvidence"] = level4_source_review_evidence(
        json.loads(arguments.program_json.read_text()), arguments.source_root
    )
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
    if arguments.out_level4_attribution_lean:
        arguments.out_level4_attribution_lean.parent.mkdir(parents=True, exist_ok=True)
        arguments.out_level4_attribution_lean.write_text(emit_level4_attribution_lean(database))


if __name__ == "__main__":
    main()
