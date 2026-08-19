#!/usr/bin/env python3
"""Generate a deterministic function/basic-block CFG from the authentic Zesu RV64 object."""

from __future__ import annotations

import argparse
import bisect
import hashlib
import json
from collections import defaultdict, deque
from pathlib import Path

from capstone import CS_ARCH_RISCV, CS_MODE_RISCV64, Cs
from elftools.common.exceptions import ELFRelocationError
from elftools.common.utils import struct_parse
from elftools.dwarf.ranges import BaseAddressEntry, RangeEntry
from elftools.elf.elffile import ELFFile
from elftools.elf.relocation import RelocationHandler
from elf_identity import load_image_sha256


COND = {"beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "bltz", "bgez", "blez", "bgtz"}
UNCOND = {"j"}
RET = {"ret", "jr"}
_SOURCE_KEYS: dict[int, list[int]] = {}


def enable_riscv_debug_relocations() -> None:
    """Teach pyelftools the five fixed-width RISC-V relocations Zig emits in DWARF."""
    original = RelocationHandler._do_apply_relocation

    def apply(handler, stream, relocation, symbols):
        if handler.elffile.get_machine_arch() != "RISC-V":
            return original(handler, stream, relocation, symbols)
        kind = relocation["r_info_type"]
        sizes = {1: 4, 2: 8, 34: 2, 38: 2, 57: 4}  # 32, 64, ADD16, SUB16, 32_PCREL
        if kind not in sizes:
            raise ELFRelocationError(f"unsupported RISC-V DWARF relocation type: {kind}")
        size = sizes[kind]
        value_type = {
            2: handler.elffile.structs.Elf_half(""),
            4: handler.elffile.structs.Elf_word(""),
            8: handler.elffile.structs.Elf_word64(""),
        }[size]
        value = struct_parse(value_type, stream, stream_pos=relocation["r_offset"])
        symbol = symbols.get_symbol(relocation["r_info_sym"])["st_value"]
        addend = relocation["r_addend"]
        if kind in {1, 2}:
            relocated = symbol + addend
        elif kind == 34:
            relocated = value + symbol + addend
        elif kind == 38:
            relocated = value - symbol - addend
        else:
            relocated = symbol + addend - relocation["r_offset"]
        stream.seek(relocation["r_offset"])
        value_type.build_stream(relocated % (1 << (size * 8)), stream)

    RelocationHandler._do_apply_relocation = apply


enable_riscv_debug_relocations()


def digest(path: Path, kind: str) -> str:
    return (load_image_sha256(path)
            if "linked executable" in kind else hashlib.sha256(path.read_bytes()).hexdigest())


def normalize_source(source: str) -> str:
    marker = "/deps/zesu/"
    if marker in source:
        return "deps/zesu/" + source.split(marker, 1)[1]
    if source.startswith("/build/source/"):
        return "deps/zesu/" + source.removeprefix("/build/source/")
    if source.startswith("/tmp/nix-build-") and "/source/" in source:
        return "deps/zesu/" + source.split("/source/", 1)[1]
    runtime_marker = "-source/runtime/"
    if runtime_marker in source:
        return "runtime/" + source.split(runtime_marker, 1)[1]
    isolated_runtime = "-binary-fv-riscv64-runtime/"
    if isolated_runtime in source:
        return "runtime/riscv64/" + source.split(isolated_runtime, 1)[1]
    zig_std = "/lib/zig/std/"
    if zig_std in source:
        return "zig/std/" + source.split(zig_std, 1)[1]
    return source


def dwarf_info(elf: ELFFile):
    return elf.get_dwarf_info(relocate_dwarf_sections=True)


def cu_directories(cu, program) -> list[bytes]:
    comp_dir = cu.get_top_DIE().attributes.get("DW_AT_comp_dir")
    return [comp_dir.value if comp_dir is not None else b"."] + list(program["include_directory"])


def line_map(elf: ELFFile) -> dict[int, tuple[str, int]]:
    result: dict[int, tuple[str, int]] = {}
    dwarf = dwarf_info(elf)
    for cu in dwarf.iter_CUs():
        program = dwarf.line_program_for_CU(cu)
        if program is None:
            continue
        dirs = cu_directories(cu, program)
        files = program["file_entry"]
        for entry in program.get_entries():
            state = entry.state
            if state is None or state.end_sequence or state.file == 0:
                continue
            file = files[state.file - 1]
            directory = dirs[file.dir_index] if file.dir_index < len(dirs) else b"."
            name = file.name.decode(errors="replace")
            source = str(Path(directory.decode(errors="replace")) / name)
            result[state.address] = (normalize_source(source), state.line or 0)
    return result


def die_text(die, attribute: str) -> str | None:
    current = die
    seen = set()
    while current is not None and current.offset not in seen:
        seen.add(current.offset)
        value = current.attributes.get(attribute)
        if value is not None:
            raw = value.value
            return raw.decode(errors="replace") if isinstance(raw, bytes) else str(raw)
        reference = current.attributes.get("DW_AT_abstract_origin") or current.attributes.get("DW_AT_specification")
        current = current.get_DIE_from_attribute(reference.name) if reference is not None else None
    return None


def die_source(die, attribute: str) -> tuple[str | None, int | None]:
    current = die
    seen = set()
    while current is not None and current.offset not in seen:
        seen.add(current.offset)
        file_attribute = current.attributes.get(attribute)
        if file_attribute is not None:
            program = current.dwarfinfo.line_program_for_CU(current.cu)
            files = program["file_entry"]
            directories = cu_directories(current.cu, program)
            index = file_attribute.value
            if index and index <= len(files):
                file = files[index - 1]
                directory = directories[file.dir_index] if file.dir_index < len(directories) else b"."
                path = Path(directory.decode(errors="replace")) / file.name.decode(errors="replace")
                line_name = "DW_AT_call_line" if attribute == "DW_AT_call_file" else "DW_AT_decl_line"
                line = current.attributes.get(line_name)
                return normalize_source(str(path)), line.value if line is not None else None
        reference = current.attributes.get("DW_AT_abstract_origin") or current.attributes.get("DW_AT_specification")
        current = current.get_DIE_from_attribute(reference.name) if reference is not None else None
    return None, None


def die_ranges(die) -> list[tuple[int, int]]:
    attributes = die.attributes
    if "DW_AT_low_pc" in attributes:
        start = attributes["DW_AT_low_pc"].value
        high = attributes["DW_AT_high_pc"]
        end = high.value if high.form == "DW_FORM_addr" else start + high.value
        return [(start, end)] if start < end else []
    if "DW_AT_ranges" not in attributes:
        return []
    base = die.cu.get_top_DIE().attributes.get("DW_AT_low_pc")
    base_address = base.value if base is not None else 0
    result = []
    entries = die.dwarfinfo.range_lists().get_range_list_at_offset(attributes["DW_AT_ranges"].value, die.cu)
    for entry in entries:
        if isinstance(entry, BaseAddressEntry):
            base_address = entry.base_address
        elif isinstance(entry, RangeEntry):
            start = entry.begin_offset if entry.is_absolute else base_address + entry.begin_offset
            end = entry.end_offset if entry.is_absolute else base_address + entry.end_offset
            if start < end:
                result.append((start, end))
    return result


def function_instances(elf: ELFFile, instructions: dict[int, dict]) -> list[dict]:
    """Extract every concrete and inlined function instance with machine-code coverage."""
    dwarf = dwarf_info(elf)
    instances = []
    instruction_pcs = sorted(instructions)
    die_to_id = {}
    dies = {}
    for cu_index, cu in enumerate(dwarf.iter_CUs()):
        for die in cu.iter_DIEs():
            dies[die.offset] = die
            if die.tag not in {"DW_TAG_subprogram", "DW_TAG_inlined_subroutine"}:
                continue
            ranges = die_ranges(die)
            pcs = []
            for start, end in ranges:
                left = bisect.bisect_left(instruction_pcs, start)
                right = bisect.bisect_left(instruction_pcs, end)
                pcs.extend(instruction_pcs[left:right])
            pcs = sorted(set(pcs))
            if not pcs:
                continue
            kind = "inlined" if die.tag == "DW_TAG_inlined_subroutine" else "concrete"
            instance_id = f"fi:{cu_index}:{die.offset:x}"
            die_to_id[die.offset] = instance_id
            name = die_text(die, "DW_AT_linkage_name") or die_text(die, "DW_AT_name") or "<anonymous>"
            source_file, decl_line = die_source(die, "DW_AT_decl_file")
            if name == "_start" and source_file is None:
                source_file, decl_line = "runtime/riscv64/riscv64_start.S", 8
            call_file, call_line = die_source(die, "DW_AT_call_file") if kind == "inlined" else (None, None)
            instances.append({
                "id": instance_id, "name": name, "kind": kind,
                "ranges": [{"start": start, "end": end} for start, end in ranges],
                "pcs": pcs, "entryPc": min(pcs), "instructionCount": len(pcs),
                "sourceFile": source_file, "declLine": decl_line,
                "callFile": call_file, "callLine": call_line,
                "dieOffset": die.offset, "parent": None,
            })
    for instance in instances:
        # DWARF nesting passes through lexical blocks; choose the nearest function-instance ancestor.
        die = dies[instance["dieOffset"]]
        parent = die.get_parent()
        while parent is not None and parent.offset not in die_to_id:
            parent = parent.get_parent()
        instance["parent"] = die_to_id.get(parent.offset) if parent is not None else None
    return sorted(instances, key=lambda row: (row["entryPc"], row["kind"] != "concrete", row["dieOffset"]))


def nearest_source(address: int, rows: dict[int, tuple[str, int]]) -> tuple[str | None, int | None]:
    keys = _SOURCE_KEYS.setdefault(id(rows), sorted(rows))
    index = bisect.bisect_right(keys, address)
    if not index:
        return None, None
    return rows[keys[index - 1]]


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


def make_blocks(fn: dict, instructions: dict[int, dict], sources: dict[int, tuple[str, int]],
                instruction_pcs: list[int] | None = None) -> list[dict]:
    start, end = fn["start"], fn["start"] + fn["size"]
    all_pcs = instruction_pcs or sorted(instructions)
    pcs = all_pcs[bisect.bisect_left(all_pcs, start):bisect.bisect_left(all_pcs, end)]
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
    owners = {}
    instruction_pcs = sorted(instructions)
    for fn in function_rows:
        left = bisect.bisect_left(instruction_pcs, fn["start"])
        right = bisect.bisect_left(instruction_pcs, fn["start"] + fn["size"])
        for pc in instruction_pcs[left:right]:
            current = owners.get(pc)
            if current is None or (fn["size"], fn["name"]) < (current["size"], current["name"]):
                owners[pc] = fn
    for pc, owner in owners.items():
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


def allocator_vtable_calls(elf: ELFFile, function_rows: list[dict],
                           instructions: dict[int, dict]) -> list[dict]:
    """Resolve the six Zig `std.mem.Allocator` calls through this endpoint's fixed vtable."""
    symbols = elf.get_section_by_name(".symtab")
    if symbols is None:
        raise ValueError("linked endpoint has no symbol table")
    by_name = {symbol.name: symbol for symbol in symbols.iter_symbols()}
    vtable = by_name["alt_fl_alloc.vtable"]["st_value"]
    methods = {
        0: "alt_fl_alloc.alloc",
        8: "alt_fl_alloc.resize",
        16: "alt_fl_alloc.remap",
        24: "alt_fl_alloc.free",
    }

    def bytes_at(address: int, width: int) -> bytes:
        for segment in elf.iter_segments():
            start, size = segment["p_vaddr"], segment["p_filesz"]
            if start <= address and address + width <= start + size:
                offset = address - start
                return segment.data()[offset:offset + width]
        raise ValueError(f"ELF address {address:#x} is not file-backed")

    for offset, target_name in methods.items():
        target = by_name[target_name]["st_value"]
        encoded = int.from_bytes(bytes_at(vtable + offset, 8), "little")
        if encoded != target:
            raise ValueError(f"allocator vtable slot {offset} does not name {target_name}")

    function_at = {}
    for function in function_rows:
        for pc in range(function["start"], function["start"] + function["size"], 4):
            function_at.setdefault(pc, function["name"])
    rows = []
    for pc, instruction in sorted(instructions.items()):
        if instruction["mnemonic"] != "jalr" or instruction["operands"].startswith(("ra,", "zero,")):
            continue
        caller = function_at.get(pc)
        if caller is None:
            raise ValueError(f"indirect call {pc:#x} has no function owner")
        if caller.startswith("mem.Allocator.allocBytesWithAlignment__anon_"):
            slot = 0
        elif caller.startswith("mem.Allocator.remap__anon_"):
            slot = 16
        else:
            raise ValueError(f"unreviewed indirect call {pc:#x} in {caller}")
        callee = methods[slot]
        rows.append({
            "caller": caller,
            "callee": callee,
            "source": pc,
            "target": by_name[callee]["st_value"],
            "kind": "allocator-vtable",
            "vtable": vtable,
            "slot": slot,
        })
    if len(rows) != 6:
        raise ValueError(f"expected six allocator vtable calls, found {len(rows)}")
    return rows


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


def build_flame(function_rows: list[dict], instances: list[dict], instructions: dict[int, dict], calls: list[dict]) -> dict:
    symbol_ownership = assigned_pcs(function_rows, instructions)
    concrete_by_id = {row["id"]: row for row in instances if row["kind"] == "concrete"}
    inline_by_id = {row["id"]: row for row in instances if row["kind"] == "inlined"}
    concrete_symbol = {}
    for instance_id, instance in concrete_by_id.items():
        candidates = [fn for fn in function_rows if fn["start"] <= instance["entryPc"] < fn["start"] + fn["size"]]
        if candidates:
            concrete_symbol[instance_id] = min(candidates, key=lambda fn: (fn["size"], fn["name"]))["name"]
    concrete_for_name = {name: instance_id for instance_id, name in concrete_symbol.items()}
    inline_children: dict[str, list[str]] = defaultdict(list)
    for row in inline_by_id.values():
        if row["parent"]:
            inline_children[row["parent"]].append(row["id"])
    for rows in inline_children.values():
        rows.sort(key=lambda item: (inline_by_id[item]["entryPc"], item))

    # Each instruction is owned by its deepest lexical inline instance, or by its emitted function.
    inline_ownership: dict[str, set[int]] = {key: set() for key in inline_by_id}
    concrete_self: dict[str, set[int]] = {}
    inline_at_pc: dict[int, str] = {}
    inline_pc_sets = {key: set(row["pcs"]) for key, row in inline_by_id.items()}
    inline_symbol = {}
    for instance_id, row in inline_by_id.items():
        ancestor = row["parent"]
        while ancestor in inline_by_id:
            ancestor = inline_by_id[ancestor]["parent"]
        inline_symbol[instance_id] = concrete_symbol.get(ancestor)
    for name, pcs in symbol_ownership.items():
        candidates = [row for instance_id, row in inline_by_id.items() if inline_symbol[instance_id] == name]
        own = set(pcs)
        for pc in pcs:
            containing = [row for row in candidates if pc in inline_pc_sets[row["id"]]]
            if containing:
                # Nested DIE depth is represented by the smallest machine range, then DIE offset.
                owner = min(containing, key=lambda row: (row["instructionCount"], -row["dieOffset"]))
                inline_ownership[owner["id"]].add(pc)
                inline_at_pc[pc] = owner["id"]
                own.discard(pc)
        concrete_self[name] = own

    ownership = symbol_ownership
    known = {fn["name"] for fn in function_rows if ownership[fn["name"]]}
    root = "main" if "main" in known else min(known)
    call_successors: dict[str, set[str]] = defaultdict(set)
    for call in calls:
        call_successors[call["caller"]].add(call["callee"])
    reachable, todo = set(), [root]
    while todo:
        current = todo.pop()
        if current in reachable:
            continue
        reachable.add(current)
        todo.extend(call_successors[current] - reachable)
    starts = {fn["name"]: fn["start"] for fn in function_rows}
    fn_by_name = {fn["name"]: fn for fn in function_rows}
    meta = {}
    callers, callees = defaultdict(list), defaultdict(list)
    for call in calls: callers[call["callee"]].append(call); callees[call["caller"]].append(call)

    # Display concrete functions once per static callsite.  A shared emitted body is not a function
    # instance: each callsite has its own caller bindings, return PC, evidence, and composition
    # obligation even when every instruction in the callee body is byte-identical.
    anchored_calls: dict[str, list[dict]] = defaultdict(list)
    for call in calls:
        if call["caller"] not in reachable or call["callee"] not in reachable:
            continue
        anchor = inline_at_pc.get(call["source"], call["caller"])
        anchored_calls[anchor].append(call)
    for rows in anchored_calls.values():
        rows.sort(key=lambda row: (row["source"], row["target"], row["callee"]))

    # A callsite is one static proof obligation, even when its caller is itself reached at several
    # callsites.  The tree expands the body below the first deterministic occurrence and leaves later
    # caller instances as body references; otherwise a shared caller multiplies every descendant.
    expanded_calls: set[int] = set()
    expanded_inline: set[str] = set()

    def inline_node(instance_id: str, parent_key: str, level: int,
                    active_functions: tuple[str, ...]) -> tuple[dict, int]:
        instance = inline_by_id[instance_id]
        label = f"{instance['name']} [{instance_id}]"
        key = f"{parent_key}|{label}"
        own = inline_ownership[instance_id]
        child_nodes, subtree_size = [], len(own)
        body_expanded = instance_id not in expanded_inline
        expanded_inline.add(instance_id)
        if body_expanded:
            for child_id in inline_children[instance_id]:
                child_node, child_size = inline_node(child_id, key, level + 1, active_functions)
                child_nodes.append(child_node); subtree_size += child_size
            for call in anchored_calls[instance_id]:
                if call["source"] in expanded_calls:
                    continue
                expanded_calls.add(call["source"])
                child_node, child_size = node(call["callee"], key, level + 1, call, active_functions)
                child_nodes.append(child_node); subtree_size += child_size
        invocation_id = key
        meta[key] = {
            "owner": invocation_id, "machineOwner": instance_id,
            "qualified": instance["name"], "kind": "inlinedFunctionInstance",
            "refinementLevel": level,
            "displayTreeLevel": level,
            "hierarchy": "dwarfInlineNesting", "runs": instance["ranges"], "frags": len(instance["ranges"]),
            "machineInstructionCount": instance["instructionCount"], "value": subtree_size,
            "self": len(own),
            "file": instance["sourceFile"],
            "line": instance["declLine"] or 0, "callFile": instance["callFile"],
            "callLine": instance["callLine"] or 0, "entries": [instance["entryPc"]], "exits": [],
            "loopSccs": [], "callers": [], "callees": [], "tailDependencies": [],
            "fragmentHandoffs": [], "parentReentryEdges": [], "carrierRoutes": [],
            "activeCalleeFrames": [], "src": None,
            "sharedBodyExpansionTruncated": not body_expanded,
        }
        return {"name": label, "value": subtree_size, "self": len(own),
                "children": child_nodes, "key": key}, subtree_size

    def node(name: str, parent_key: str | None, level: int, incoming: dict | None = None,
             active_functions: tuple[str, ...] = ()) -> tuple[dict, int]:
        callsite = f" @0x{incoming['source']:x}" if incoming is not None else ""
        label = f"{name}{callsite} [fn:0x{fn_by_name[name]['start']:x}]"
        key = label if parent_key is None else f"{parent_key}|{label}"
        own = concrete_self[name]
        child_nodes, subtree_size = [], len(own)
        cycle = name in active_functions
        next_active = (*active_functions, name)
        concrete_id = concrete_for_name.get(name)
        if concrete_id is not None and not cycle:
            for inline_id in inline_children[concrete_id]:
                child_node, child_size = inline_node(inline_id, key, level + 1, next_active)
                child_nodes.append(child_node); subtree_size += child_size
        if not cycle:
            for call in anchored_calls[name]:
                if call["source"] in expanded_calls:
                    continue
                expanded_calls.add(call["source"])
                child_node, child_size = node(call["callee"], key, level + 1, call, next_active)
                child_nodes.append(child_node); subtree_size += child_size
        fn = fn_by_name.get(name, {})
        invocation_id = key
        display_anchor = None if incoming is None else inline_at_pc.get(incoming["source"], incoming["caller"])
        display_anchor_name = (None if display_anchor is None else
                               inline_by_id[display_anchor]["name"] if display_anchor in inline_by_id else
                               incoming["caller"])
        machine_owner = concrete_id or f"fn:0x{fn_by_name[name]['start']:x}"
        meta[key] = {"owner": invocation_id, "machineOwner": machine_owner,
                     "qualified": name, "kind": "concreteCallsiteInstance",
                     "refinementLevel": level,
                     "displayTreeLevel": level,
                     "hierarchy": "callDominatorAnchoredAtDeepestCommonInlineCallsite", "runs": [], "frags": 1,
                     "machineInstructionCount": len(ownership[name]), "value": subtree_size,
                     "self": len(own),
                     "displayAnchor": display_anchor,
                     "displayAnchorName": display_anchor_name,
                     "displayHoisted": False, "displayRelation": "actual static callsite instance",
                     "displayCallsites": [] if incoming is None else [incoming["source"]],
                     "callsitePc": None if incoming is None else incoming["source"],
                     "returnPc": None if incoming is None else incoming["source"] + 4,
                     "cycleTruncated": cycle,
                     "sharedBodyExpansionTruncated": bool(incoming) and not child_nodes and bool(anchored_calls[name]),
                     "file": fn.get("sourceFile"), "line": fn.get("sourceLine", 0), "entries": [fn["start"]],
                     "exits": [], "loopSccs": [], "callers": callers[name], "callees": callees[name], "tailDependencies": [],
                     "fragmentHandoffs": [], "parentReentryEdges": [], "carrierRoutes": [], "activeCalleeFrames": [], "src": None}
        return {"name": label, "value": subtree_size, "self": len(own),
                "children": child_nodes, "key": key}, subtree_size

    tree, expanded_total = node(root, None, 0)
    reachable_pcs = set().union(*(set(ownership[name]) for name in reachable))
    displayed_instances = {row["machineOwner"] for row in meta.values()}
    expected_instances = {instance_id for instance_id, name in concrete_symbol.items() if name in reachable}
    expected_instances |= {instance_id for instance_id, name in inline_symbol.items() if name in reachable}
    expected_instances |= {
        f"fn:0x{fn_by_name[name]['start']:x}" for name in reachable if name not in concrete_for_name
    }
    if not expected_instances <= displayed_instances:
        missing = sorted(expected_instances - displayed_instances)
        raise ValueError(
            "displayed call hierarchy does not contain every main-reachable DWARF function instance: "
            f"missing={missing}"
        )
    return {"schemaVersion": 3, "machineRegionInputs": {"target": "zesu-ssz-decode-c36bb99-release-small",
                                                         "functionInstances": "same-ELF DWARF"},
            "total": len(instructions), "programTotal": expanded_total,
            "uniqueProgramTotal": len(reachable_pcs),
            "loAddr": min(instructions), "tree": tree, "meta": meta,
            "suggest": {"cap": 0, "coverage": len(reachable_pcs), "units": [], "residual": {}, "needsSubFunctionSplit": []}}


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
        elf_kind = {
            "ET_REL": "ELF64 RISC-V relocatable object",
            "ET_EXEC": "ELF64 RISC-V linked executable",
        }.get(elf["e_type"], f"ELF64 RISC-V {elf['e_type']}")
        source_rows = line_map(elf)
        instruction_rows = decode_text(elf)
        function_rows = functions(elf)
        instance_rows = function_instances(elf, instruction_rows)
        call_rows = direct_calls(elf, function_rows, instruction_rows)
        indirect_call_rows = allocator_vtable_calls(elf, function_rows, instruction_rows) \
            if elf["e_type"] == "ET_EXEC" else []
        output_functions = []
        instruction_pcs = sorted(instruction_rows)
        for fn in function_rows:
            source_file, source_line = nearest_source(fn["start"], source_rows)
            blocks = make_blocks(fn, instruction_rows, source_rows, instruction_pcs)
            output_functions.append({
                **fn, "instructionCount": sum(b["instructionCount"] for b in blocks),
                "blockCount": len(blocks), "sourceFile": source_file, "sourceLine": source_line,
                "semanticGroup": semantic_group(fn["name"], source_file), "blocks": blocks,
                "proofStatus": "not_started",
            })
    payload = {
        "schemaVersion": 1,
        "artifact": {
            "kind": elf_kind,
            "identityScope": ("ELF PT_LOAD memory image"
                              if "linked executable" in elf_kind else "complete file"),
            "sha256": digest(args.object, elf_kind),
        },
        "sourceMapping": {"kind": "DWARF from the same ReleaseSmall ELF", "confidence": "exact-line-table"},
        "formalStatus": "No kernel-backed target proof manifest is present.",
        "functions": output_functions,
        "functionInstances": instance_rows,
        "calls": call_rows,
        "reviewedIndirectCalls": indirect_call_rows,
        "totals": {"functions": len(output_functions), "instructions": len(instruction_rows),
                   "functionInstances": len(instance_rows),
                   "inlinedFunctionInstances": sum(row["kind"] == "inlined" for row in instance_rows),
                   "symbolInstructionReferences": sum(fn["instructionCount"] for fn in output_functions),
                   "blocks": sum(fn["blockCount"] for fn in output_functions)},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n")
    if args.flame:
        args.flame.write_text(json.dumps(build_flame(output_functions, instance_rows, instruction_rows, call_rows), sort_keys=True, separators=(",", ":")) + "\n")
    if args.proof_map:
        args.proof_map.write_text(json.dumps(build_proof_map(output_functions, len(instruction_rows)), sort_keys=True, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
