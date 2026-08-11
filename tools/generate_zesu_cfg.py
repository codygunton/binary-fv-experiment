#!/usr/bin/env python3
"""Generate a deterministic function/basic-block CFG from the authentic Zesu RV64 object."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict, deque
from pathlib import Path

from capstone import CS_ARCH_RISCV, CS_MODE_RISCV64, Cs
from elftools.elf.elffile import ELFFile


COND = {"beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "bltz", "bgez", "blez", "bgtz"}
UNCOND = {"j"}
RET = {"ret", "jr"}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def line_map(elf: ELFFile) -> dict[int, tuple[str, int]]:
    result: dict[int, tuple[str, int]] = {}
    # This relocatable object has a zero-based .text section. pyelftools does not implement one of
    # Zig's RISC-V DWARF relocation kinds; leaving relocations unapplied preserves those addresses.
    dwarf = elf.get_dwarf_info(relocate_dwarf_sections=False)
    for cu in dwarf.iter_CUs():
        program = dwarf.line_program_for_CU(cu)
        if program is None:
            continue
        dirs = [b"."] + list(program["include_directory"])
        files = program["file_entry"]
        for entry in program.get_entries():
            state = entry.state
            if state is None or state.end_sequence or state.file == 0:
                continue
            file = files[state.file - 1]
            directory = dirs[file.dir_index] if file.dir_index < len(dirs) else b"."
            name = file.name.decode(errors="replace")
            source = str(Path(directory.decode(errors="replace")) / name)
            marker = "/deps/zesu/"
            if marker in source:
                source = "deps/zesu/" + source.split(marker, 1)[1]
            elif source.startswith("/build/source/"):
                source = "deps/zesu/" + source.removeprefix("/build/source/")
            result[state.address] = (source, state.line or 0)
    return result


def nearest_source(address: int, rows: dict[int, tuple[str, int]]) -> tuple[str | None, int | None]:
    candidates = [pc for pc in rows if pc <= address]
    if not candidates:
        return None, None
    return rows[max(candidates)]


def decode_text(elf: ELFFile) -> dict[int, dict]:
    text = elf.get_section_by_name(".text")
    decoder = Cs(CS_ARCH_RISCV, CS_MODE_RISCV64)
    result = {}
    for insn in decoder.disasm(text.data(), text["sh_addr"]):
        result[insn.address] = {
            "pc": insn.address,
            "size": insn.size,
            "mnemonic": insn.mnemonic,
            "operands": insn.op_str,
            "bytes": insn.bytes.hex(),
        }
    return result


def functions(elf: ELFFile) -> list[dict]:
    symtab = elf.get_section_by_name(".symtab")
    rows = []
    for symbol in symtab.iter_symbols():
        if symbol["st_info"]["type"] != "STT_FUNC" or symbol["st_size"] == 0:
            continue
        rows.append({"name": symbol.name, "start": symbol["st_value"], "size": symbol["st_size"]})
    return sorted(rows, key=lambda item: (item["start"], item["name"]))


def immediate_target(insn: dict) -> int | None:
    operand = insn["operands"].split(",")[-1].strip()
    try:
        # Capstone prints RISC-V control-flow immediates as signed PC-relative displacements.
        return insn["pc"] + int(operand, 0)
    except ValueError:
        return None


def make_blocks(fn: dict, instructions: dict[int, dict], sources: dict[int, tuple[str, int]]) -> list[dict]:
    start, end = fn["start"], fn["start"] + fn["size"]
    pcs = [pc for pc in sorted(instructions) if start <= pc < end]
    if not pcs:
        return []
    leaders = {pcs[0]}
    for index, pc in enumerate(pcs):
        insn = instructions[pc]
        mnemonic = insn["mnemonic"]
        if mnemonic in COND | UNCOND:
            target = immediate_target(insn)
            if target is not None and start <= target < end:
                leaders.add(target)
        if mnemonic in COND | UNCOND | RET | {"jal", "jalr"} and index + 1 < len(pcs):
            leaders.add(pcs[index + 1])
    ordered = sorted(leaders)
    blocks = []
    for index, first in enumerate(ordered):
        stop = ordered[index + 1] if index + 1 < len(ordered) else end
        body = [instructions[pc] for pc in pcs if first <= pc < stop]
        if not body:
            continue
        source_file, source_line = nearest_source(first, sources)
        blocks.append({
            "id": f"0x{first:x}", "start": first, "end": body[-1]["pc"] + body[-1]["size"],
            "instructionCount": len(body), "sourceFile": source_file, "sourceLine": source_line,
            "instructions": body, "successors": [],
        })
    by_pc = {block["start"]: block for block in blocks}
    for index, block in enumerate(blocks):
        tail = block["instructions"][-1]
        mnemonic = tail["mnemonic"]
        target = immediate_target(tail) if mnemonic in COND | UNCOND else None
        if target in by_pc:
            block["successors"].append(f"0x{target:x}")
        if mnemonic not in UNCOND | RET and index + 1 < len(blocks):
            block["successors"].append(blocks[index + 1]["id"])
        block["successors"] = list(dict.fromkeys(block["successors"]))
    return blocks


def semantic_group(name: str, source: str | None) -> str:
    text = f"{name} {source or ''}".lower()
    for group in ("ssz", "stateless", "zkvm", "evm", "rlp", "trie", "crypto", "allocator"):
        if group in text:
            return group
    return "support"


def assigned_pcs(function_rows: list[dict], instructions: dict[int, dict]) -> dict[str, list[int]]:
    """Assign overlapping symbol ranges once, preferring the narrowest concrete function."""
    result: dict[str, list[int]] = {fn["name"]: [] for fn in function_rows}
    for pc in instructions:
        candidates = [fn for fn in function_rows if fn["start"] <= pc < fn["start"] + fn["size"]]
        if candidates:
            owner = min(candidates, key=lambda fn: (fn["size"], fn["name"]))
            result[owner["name"]].append(pc)
    return result


def direct_calls(elf: ELFFile, function_rows: list[dict], instructions: dict[int, dict]) -> list[dict]:
    by_entry = {fn["start"]: fn["name"] for fn in function_rows}
    owner_at = {}
    for fn in function_rows:
        for pc in range(fn["start"], fn["start"] + fn["size"], 4):
            owner_at.setdefault(pc, fn["name"])
    calls = []
    relocation_calls = {}
    relocations = elf.get_section_by_name(".rela.text")
    if relocations is not None:
        symbols = elf.get_section(relocations["sh_link"])
        for relocation in relocations.iter_relocations():
            symbol = symbols.get_symbol(relocation["r_info_sym"])
            # Zig emits direct function calls as AUIPC/JALR pairs with a relocation on AUIPC.
            if symbol.name in by_entry.values():
                relocation_calls[relocation["r_offset"]] = symbol.name
    pcs = sorted(instructions)
    for index, pc in enumerate(pcs):
        row = instructions[pc]
        target = None
        relocated_callee = relocation_calls.get(pc)
        if relocated_callee:
            caller = owner_at.get(pc)
            if caller and caller != relocated_callee:
                calls.append({"caller": caller, "callee": relocated_callee, "source": pc,
                              "target": next(fn["start"] for fn in function_rows if fn["name"] == relocated_callee),
                              "kind": "call"})
            continue
        if row["mnemonic"] == "jal":
            target = immediate_target(row)
        elif row["mnemonic"] == "jalr" and index and pcs[index - 1] + 4 == pc:
            high = instructions[pcs[index - 1]]
            if high["mnemonic"] == "auipc":
                high_parts, low_parts = [x.strip() for x in high["operands"].split(",")], [x.strip() for x in row["operands"].split(",")]
                if len(high_parts) == 2 and len(low_parts) == 3 and high_parts[0] == low_parts[1]:
                    upper = int(high_parts[1], 0)
                    if upper & (1 << 19):
                        upper -= 1 << 20
                    target = high["pc"] + upper * 4096 + int(low_parts[2], 0)
        caller, callee = owner_at.get(pc), by_entry.get(target)
        if caller and callee and caller != callee:
            calls.append({"caller": caller, "callee": callee, "source": pc, "target": target, "kind": "call"})
    unique = {(row["caller"], row["callee"], row["source"]): row for row in calls}
    return [unique[key] for key in sorted(unique)]


def dominator_parents(root: str, names: set[str], calls: list[dict]) -> tuple[dict[str, str], set[str]]:
    successors: dict[str, set[str]] = defaultdict(set)
    predecessors: dict[str, set[str]] = defaultdict(set)
    for call in calls:
        successors[call["caller"]].add(call["callee"])
        predecessors[call["callee"]].add(call["caller"])
    reachable, todo = set(), [root]
    while todo:
        node = todo.pop()
        if node in reachable:
            continue
        reachable.add(node); todo.extend(successors[node] - reachable)
    dom = {node: ({root} if node == root else set(reachable)) for node in reachable}
    changed = True
    while changed:
        changed = False
        for node in sorted(reachable - {root}):
            incoming = predecessors[node] & reachable
            value = {node} | (set.intersection(*(dom[p] for p in incoming)) if incoming else set())
            if value != dom[node]: dom[node] = value; changed = True
    parents = {}
    for node in reachable - {root}:
        strict = dom[node] - {node}
        parents[node] = max(strict, key=lambda candidate: len(dom[candidate])) if strict else root
    return parents, reachable


def build_flame(function_rows: list[dict], instructions: dict[int, dict], calls: list[dict]) -> dict:
    ownership = assigned_pcs(function_rows, instructions)
    known = {fn["name"] for fn in function_rows if ownership[fn["name"]]}
    root = "main" if "main" in known else min(known)
    parents, reachable = dominator_parents(root, known, calls)
    children: dict[str, list[str]] = defaultdict(list)
    children["program"].append(root)
    children["binary"].extend(["program", "not-called-by-program"])
    for child, parent in parents.items(): children[parent].append(child)
    for name in known - reachable: children["not-called-by-program"].append(name)
    starts = {fn["name"]: fn["start"] for fn in function_rows}
    for rows in children.values(): rows.sort(key=lambda name: (starts.get(name, -2), name))
    fn_by_name = {fn["name"]: fn for fn in function_rows}
    meta = {}
    callers, callees = defaultdict(list), defaultdict(list)
    for call in calls: callers[call["callee"]].append(call); callees[call["caller"]].append(call)

    def node(name: str, parent_key: str | None) -> tuple[dict, set[int]]:
        synthetic = name in {"binary", "program", "not-called-by-program"}
        label = name if synthetic else f"{name} [fn:0x{fn_by_name[name]['start']:x}]"
        key = label if parent_key is None else f"{parent_key}|{label}"
        own = set() if synthetic else set(ownership[name])
        child_nodes, subtree = [], set(own)
        for child in children[name]:
            child_node, child_pcs = node(child, key); child_nodes.append(child_node); subtree |= child_pcs
        fn = fn_by_name.get(name, {})
        meta[key] = {"owner": None if synthetic else name, "qualified": name, "kind": "synthetic" if synthetic else "function",
                     "hierarchy": "callDominator", "runs": [], "frags": 1, "value": len(subtree), "self": len(own),
                     "file": fn.get("sourceFile"), "line": fn.get("sourceLine", 0), "entries": [] if synthetic else [fn["start"]],
                     "exits": [], "loopSccs": [], "callers": callers[name], "callees": callees[name], "tailDependencies": [],
                     "fragmentHandoffs": [], "parentReentryEdges": [], "carrierRoutes": [], "activeCalleeFrames": [], "src": None}
        return {"name": label, "value": len(subtree), "self": len(own), "children": child_nodes, "key": key}, subtree

    tree, covered = node("binary", None)
    if covered != set().union(*(set(pcs) for name, pcs in ownership.items() if name in known)):
        raise ValueError("call hierarchy does not cover the symbol-owned instruction inventory")
    return {"schemaVersion": 2, "machineRegionInputs": {"target": "upstream-zesu-d8071c4-release-small"},
            "total": len(instructions), "programTotal": len(set().union(*(set(ownership[name]) for name in reachable))),
            "loAddr": min(instructions), "tree": tree, "meta": meta,
            "suggest": {"cap": 0, "coverage": len(covered), "units": [], "residual": {}, "needsSubFunctionSplit": []}}


def build_proof_map(functions_output: list[dict], formal_total: int) -> dict:
    target = next(fn for fn in functions_output if fn["name"] == "ssz.decodeByteListList")
    instructions = []
    for block in target["blocks"]:
        for row in block["instructions"]:
            instructions.append({"pc": row["pc"], "mnemonic": row["mnemonic"], "operands": row["operands"],
                                 "successors": block["successors"], "reads": [], "writes": [], "memory": [],
                                 "owner": target["name"], "sourceFile": block["sourceFile"], "sourceLine": block["sourceLine"],
                                 "formalManifests": [], "artifactState": "same-object-release-small"})
    blocks = [{"id": b["id"], "entryPc": b["start"], "pcs": [i["pc"] for i in b["instructions"]],
               "successors": [int(s, 16) for s in b["successors"]], "phase": "ssz-helper", "instructionCount": b["instructionCount"],
               "parentInstructionCount": b["instructionCount"], "provedParentInstructionCount": 0,
               "sourceMappings": [{"ownerId": target["name"], "qualified": target["name"], "sourceFile": b["sourceFile"],
                                   "declLine": b["sourceLine"], "inlineStack": [], "pcStart": b["start"], "pcEnd": b["end"] - 4,
                                   "instructionCount": b["instructionCount"], "basis": "same-object DWARF line table"}]}
              for b in target["blocks"]]
    pcs = [row["pc"] for row in instructions]
    return {"schemaVersion": 1, "target": "upstream-zesu-d8071c4", "instructions": instructions, "blocks": blocks,
            "boundaries": [], "manifests": [], "formalCoverage": {"localPcCount": 0, "level4PcCount": 0, "rootPcCount": 0},
            "compilerProvenance": {"state": "same-object-dwarf"},
            "phases": [{"id": "ssz-helper", "label": "ssz.decodeByteListList", "pcs": pcs}],
            "authoringRegions": [{"id": "ssz-byte-list-list", "label": "ssz.decodeByteListList machine proof",
                                  "authoringState": "blocked", "blocker": "No kernel-backed machine theorem exists for this authentic target.",
                                  "scope": "parent", "pcs": pcs, "evidence": "ReleaseSmall object structure and same-object DWARF only",
                                  "preparation": {"liveRegisters": [], "protectedMemory": [], "prerequisites": ["state a target contract against EVM-Sail"],
                                                  "sourceIdentity": "deps/zesu/src/stateless/stateless/ssz.zig:67"}}],
            "refinementGraph": {"nodes": [
                {"id": "spec", "label": "EVM-Sail decode_stateless_input", "kind": "level4Contract", "column": 0, "status": "artifact", "boundaryId": "none", "instructionCount": 0, "source": "deps/evm-sail"},
                {"id": "target", "label": "Zesu SSZ machine regions", "kind": "parentGlue", "column": 1, "status": "blocked", "phase": "ssz-helper", "instructionCount": len(pcs), "provedInstructionCount": 0},
                {"id": "conversion", "label": "future Zesu/EVM-Sail refinement", "kind": "conversion", "column": 2, "status": "blocked"},
                {"id": "root", "label": "root_compliance", "kind": "parent", "column": 3, "status": "blocked"}],
                "edges": [{"source": "spec", "target": "conversion", "kind": "dependency"}, {"source": "target", "target": "conversion", "kind": "dependency"}, {"source": "conversion", "target": "root", "kind": "dependency"}]}}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--object", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--flame", type=Path)
    parser.add_argument("--proof-map", type=Path)
    args = parser.parse_args()
    with args.object.open("rb") as stream:
        elf = ELFFile(stream)
        source_rows = line_map(elf)
        instruction_rows = decode_text(elf)
        function_rows = functions(elf)
        call_rows = direct_calls(elf, function_rows, instruction_rows)
        output_functions = []
        for fn in function_rows:
            source_file, source_line = nearest_source(fn["start"], source_rows)
            blocks = make_blocks(fn, instruction_rows, source_rows)
            output_functions.append({
                **fn, "instructionCount": sum(b["instructionCount"] for b in blocks),
                "blockCount": len(blocks), "sourceFile": source_file, "sourceLine": source_line,
                "semanticGroup": semantic_group(fn["name"], source_file), "blocks": blocks,
                "proofStatus": "not_started",
            })
    payload = {
        "schemaVersion": 1,
        "artifact": {"kind": "ELF64 RISC-V relocatable object", "sha256": digest(args.object)},
        "sourceMapping": {"kind": "DWARF from the same ReleaseSmall object", "confidence": "exact-line-table"},
        "formalStatus": "No kernel-backed target proof manifest is present.",
        "functions": output_functions,
        "totals": {"functions": len(output_functions), "instructions": len(instruction_rows),
                   "symbolInstructionReferences": sum(fn["instructionCount"] for fn in output_functions),
                   "blocks": sum(fn["blockCount"] for fn in output_functions)},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n")
    if args.flame:
        args.flame.write_text(json.dumps(build_flame(output_functions, instruction_rows, call_rows), sort_keys=True, separators=(",", ":")) + "\n")
    if args.proof_map:
        args.proof_map.write_text(json.dumps(build_proof_map(output_functions, len(instruction_rows)), sort_keys=True, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
