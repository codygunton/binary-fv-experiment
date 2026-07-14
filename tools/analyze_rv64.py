#!/usr/bin/env python3
"""Conservative, reproducible structural analysis for a linked RISC-V ELF.

Direct control-flow targets are followed from the supplied entry symbol. Indirect control flow is
left explicit in the output rather than guessed, so the reachability numbers are auditable.
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import fnmatch
import json
import pathlib
import re
import subprocess
import sys


FUNCTION = re.compile(r"^\s*([0-9a-fA-F]+) <([^>]+)>:$")
INSTRUCTION = re.compile(
    r"^\s*([0-9a-fA-F]+):\s+([0-9a-fA-F]+(?:\s+[0-9a-fA-F]+)*)"
    r"\s+([.A-Za-z][._A-Za-z0-9]*)(?:\s+(.*?))?\s*$"
)
TARGET = re.compile(r"\b([0-9a-fA-F]+)\s+<[^>]+>")
CONDITIONAL = re.compile(r"^(?:b(?:eq|ne|lt|ge|ltu|geu)|c\.b)")

I_OPS = {
    "lui", "auipc", "jal", "jalr", "beq", "bne", "blt", "bge", "bltu", "bgeu",
    "lb", "lh", "lw", "ld", "lbu", "lhu", "lwu", "sb", "sh", "sw", "sd",
    "addi", "slti", "sltiu", "xori", "ori", "andi", "slli", "srli", "srai",
    "addiw", "slliw", "srliw", "sraiw", "add", "sub", "sll", "slt", "sltu",
    "xor", "srl", "sra", "or", "and", "addw", "subw", "sllw", "srlw", "sraw",
    "fence", "fence.i", "ecall", "ebreak", "csrrw", "csrrs", "csrrc", "csrrwi",
    "csrrsi", "csrrci", "wfi", "sfence.vma",
}
M_OPS = {
    "mul", "mulh", "mulhsu", "mulhu", "div", "divu", "rem", "remu", "mulw",
    "divw", "divuw", "remw", "remuw",
}
ZICCLSM_OPS = {"cbo.clean", "cbo.flush", "cbo.inval"}
ALIASES = {"call", "tail", "j", "jr", "ret", "li", "mv", "nop"}


@dataclasses.dataclass(frozen=True)
class Insn:
    address: int
    bytes_: str
    mnemonic: str
    operands: str
    function: str

    @property
    def size(self) -> int:
        return len(self.bytes_.replace(" ", "")) // 2


@dataclasses.dataclass(frozen=True)
class Block:
    start: int
    insns: tuple[Insn, ...]

    @property
    def function(self) -> str:
        return self.insns[0].function


def parse(text: str) -> tuple[list[Insn], dict[str, int]]:
    functions: dict[str, int] = {}
    insns: list[Insn] = []
    current = "<outside-symbol>"
    for line in text.splitlines():
        match = FUNCTION.match(line)
        if match:
            current = match.group(2)
            functions.setdefault(current, int(match.group(1), 16))
            continue
        match = INSTRUCTION.match(line)
        if match:
            insns.append(
                Insn(
                    int(match.group(1), 16),
                    match.group(2),
                    match.group(3).lower(),
                    (match.group(4) or "").strip(),
                    current,
                )
            )
    if not insns:
        raise ValueError("objdump produced no disassembled instructions")
    return insns, functions


def target(insn: Insn) -> int | None:
    match = TARGET.search(insn.operands)
    return int(match.group(1), 16) if match else None


def rd(insn: Insn) -> str | None:
    return insn.operands.split(",", 1)[0].strip() or None


def conditional(insn: Insn) -> bool:
    return bool(CONDITIONAL.match(insn.mnemonic))


def returns(insn: Insn) -> bool:
    return insn.mnemonic == "ret" or (
        insn.mnemonic == "jalr"
        and insn.operands.replace(" ", "") in {"zero,0(ra)", "x0,0(ra)"}
    )


def direct_call(insn: Insn) -> bool:
    if insn.mnemonic == "call":
        return True
    if insn.mnemonic in {"jal", "jalr"}:
        return rd(insn) not in {None, "zero", "x0"} and target(insn) is not None
    return False


def direct_jump(insn: Insn) -> bool:
    return insn.mnemonic in {"j", "tail"} or (
        insn.mnemonic in {"jal", "jalr"} and rd(insn) in {"zero", "x0"} and target(insn) is not None
    )


def terminal(insn: Insn) -> bool:
    # Linux syscalls use ecall but ordinarily return to the next instruction. A syscall that
    # exits has an explicit following terminal loop in this harness, which the normal CFG rules
    # preserve. Treating every ecall as terminal would cut off stdin-driven target execution.
    return returns(insn) or insn.mnemonic in {"ebreak", "unimp"}


def partition(insns: list[Insn]) -> tuple[list[Block], dict[int, int]]:
    by_function: dict[str, list[Insn]] = collections.defaultdict(list)
    for insn in insns:
        by_function[insn.function].append(insn)
    blocks: list[Block] = []
    containing: dict[int, int] = {}
    for function_insns in by_function.values():
        position = {insn.address: index for index, insn in enumerate(function_insns)}
        leaders = {function_insns[0].address}
        for index, insn in enumerate(function_insns):
            if target(insn) in position:
                leaders.add(target(insn))
            if index + 1 < len(function_insns) and (
                conditional(insn) or direct_call(insn) or direct_jump(insn) or terminal(insn)
            ):
                leaders.add(function_insns[index + 1].address)
        indices = sorted(position[address] for address in leaders)
        for index, start in enumerate(indices):
            stop = indices[index + 1] if index + 1 < len(indices) else len(function_insns)
            block = Block(function_insns[start].address, tuple(function_insns[start:stop]))
            number = len(blocks)
            blocks.append(block)
            for insn in block.insns:
                containing[insn.address] = number
    return blocks, containing


def make_graph(
    blocks: list[Block], containing: dict[int, int]
) -> tuple[dict[int, set[int]], dict[int, set[int]], set[int]]:
    starts = {block.start: number for number, block in enumerate(blocks)}
    cfg: dict[int, set[int]] = {number: set() for number in range(len(blocks))}
    calls: dict[int, set[int]] = {number: set() for number in range(len(blocks))}
    unresolved: set[int] = set()
    for number, block in enumerate(blocks):
        insn = block.insns[-1]
        destination = starts.get(target(insn))
        fallthrough = containing.get(insn.address + insn.size)
        if conditional(insn):
            if destination is not None:
                cfg[number].add(destination)
            if fallthrough is not None:
                cfg[number].add(fallthrough)
        elif direct_call(insn):
            if destination is not None:
                cfg[number].add(destination)
                calls[number].add(destination)
            if fallthrough is not None:
                cfg[number].add(fallthrough)
        elif direct_jump(insn):
            if destination is not None:
                cfg[number].add(destination)
        elif terminal(insn):
            pass
        else:
            if insn.mnemonic == "jalr":
                unresolved.add(number)
            if fallthrough is not None:
                cfg[number].add(fallthrough)
    return cfg, calls, unresolved


def reach(graph: dict[int, set[int]], entries: list[int]) -> set[int]:
    seen: set[int] = set()
    todo = list(entries)
    while todo:
        node = todo.pop()
        if node in seen:
            continue
        seen.add(node)
        todo.extend(graph[node] - seen)
    return seen


def sccs(graph: dict[object, set[object]], nodes: set[object]) -> list[set[object]]:
    clock = 0
    index: dict[object, int] = {}
    low: dict[object, int] = {}
    stack: list[object] = []
    active: set[object] = set()
    answer: list[set[object]] = []

    def visit(node: object) -> None:
        nonlocal clock
        index[node] = low[node] = clock
        clock += 1
        stack.append(node)
        active.add(node)
        for next_node in graph[node] & nodes:
            if next_node not in index:
                visit(next_node)
                low[node] = min(low[node], low[next_node])
            elif next_node in active:
                low[node] = min(low[node], index[next_node])
        if low[node] == index[node]:
            component: set[object] = set()
            while True:
                member = stack.pop()
                active.remove(member)
                component.add(member)
                if member == node:
                    break
            answer.append(component)

    for node in nodes:
        if node not in index:
            visit(node)
    return answer


def opcode_class(insn: Insn) -> str:
    mnemonic = insn.mnemonic
    if mnemonic in I_OPS:
        return "I/system"
    if mnemonic in M_OPS:
        return "M"
    if mnemonic in ZICCLSM_OPS:
        return "Zicclsm"
    if mnemonic.startswith("amo") or mnemonic.startswith("lr.") or mnemonic.startswith("sc."):
        return "A"
    if mnemonic.startswith("f") and mnemonic not in {"fence", "fence.i"}:
        return "F/D"
    if mnemonic.startswith("c."):
        return "C"
    if mnemonic in ALIASES:
        return "alias"
    return "unknown"


def forbidden(insn: Insn) -> str | None:
    if insn.size == 2:
        return "compressed 16-bit encoding (C)"
    kind = opcode_class(insn)
    return kind if kind in {"A", "C", "F/D", "unknown"} else None


def owners(values: list[str]) -> list[tuple[str, str]]:
    parsed: list[tuple[str, str]] = []
    for value in values:
        if "=" not in value:
            raise ValueError(f"invalid owner rule: {value!r}")
        parsed.append(tuple(value.split("=", 1)))
    return parsed


def owner(function: str, rules: list[tuple[str, str]]) -> str:
    for pattern, name in rules:
        if fnmatch.fnmatchcase(function, pattern):
            return name
    return "unclassified"


def call_depth(blocks: list[Block], calls: dict[int, set[int]], reachable: set[int]) -> tuple[int | None, bool]:
    functions = {blocks[number].function for number in reachable}
    graph: dict[str, set[str]] = {function: set() for function in functions}
    for source in reachable:
        for destination in calls[source] & reachable:
            # A compiler may use `jal ra, local_label` as an intra-symbol control-flow
            # primitive. It is a direct call instruction for the instruction-count metric,
            # but it is not recursive function invocation and must not poison the call-depth
            # result.
            caller = blocks[source].function
            callee = blocks[destination].function
            if caller != callee:
                graph[caller].add(callee)
    cyclic = any(
        len(component) > 1 or any(node in graph[node] for node in component)
        for component in sccs(graph, set(graph))
    )
    if cyclic:
        return None, True
    memo: dict[str, int] = {}

    def depth(node: str) -> int:
        if node not in memo:
            memo[node] = 1 + max((depth(child) for child in graph[node]), default=0)
        return memo[node]

    return max((depth(node) for node in graph), default=0), False


def analyze(
    insns: list[Insn], functions: dict[str, int], entries: list[str], rules: list[tuple[str, str]]
) -> dict[str, object]:
    blocks, containing = partition(insns)
    cfg, calls, unresolved = make_graph(blocks, containing)
    function_blocks = {
        name: containing[address] for name, address in functions.items() if address in containing
    }
    absent = [name for name in entries if name not in function_blocks]
    if absent:
        raise ValueError(f"missing entry symbol(s): {', '.join(absent)}")
    reachable = reach(cfg, [function_blocks[name] for name in entries])
    reachable_insns = sorted(
        (insn for number in reachable for insn in blocks[number].insns), key=lambda insn: insn.address
    )
    reachable_functions = sorted({blocks[number].function for number in reachable})
    local_cfg = {
        number: {
            destination for destination in cfg[number] if blocks[destination].function == blocks[number].function
        }
        for number in reachable
    }
    loops = [
        component for component in sccs(local_cfg, reachable)
        if len(component) > 1 or any(number in local_cfg[number] for number in component)
    ]
    depth, recursive = call_depth(blocks, calls, reachable)
    classes = collections.Counter(opcode_class(insn) for insn in reachable_insns)
    violations = [
        {
            "address": f"0x{insn.address:x}",
            "function": insn.function,
            "mnemonic": insn.mnemonic,
            "operands": insn.operands,
            "reason": reason,
        }
        for insn in reachable_insns
        if (reason := forbidden(insn)) is not None
    ]
    counts: dict[str, dict[str, object]] = {}
    for function in reachable_functions:
        group = counts.setdefault(owner(function, rules), {"functions": [], "instructions": 0})
        group["functions"].append(function)
    for insn in reachable_insns:
        counts.setdefault(owner(insn.function, rules), {"functions": [], "instructions": 0})["instructions"] += 1
    for group in counts.values():
        group["functions"].sort()
        group["function_count"] = len(group["functions"])
    return {
        "entries": entries,
        "full_instruction_count": len(insns),
        "reachable_instruction_count": len(reachable_insns),
        "reachable_function_count": len(reachable_functions),
        "reachable_functions": reachable_functions,
        "basic_blocks": len(reachable),
        "cfg_edges": sum(len(cfg[number] & reachable) for number in reachable),
        "conditional_branches": sum(conditional(insn) for insn in reachable_insns),
        "direct_calls": sum(len(calls[number] & reachable) for number in reachable),
        "unresolved_indirect_call_blocks": [f"0x{blocks[number].start:x}" for number in sorted(unresolved & reachable)],
        "loop_sccs": len(loops),
        "loop_scc_blocks": [sorted(f"0x{blocks[number].start:x}" for number in component) for component in loops],
        "maximum_direct_call_depth": depth,
        "recursive_direct_calls": recursive,
        "opcode_classes": dict(sorted(classes.items())),
        "forbidden_reachable_instructions": violations,
        "ownership": dict(sorted(counts.items())),
    }


def markdown(target_name: str, report: dict[str, object]) -> str:
    values = [
        ("Full instructions", report["full_instruction_count"]),
        ("Reachable instructions", report["reachable_instruction_count"]),
        ("Reachable functions", report["reachable_function_count"]),
        ("Basic blocks", report["basic_blocks"]),
        ("CFG edges", report["cfg_edges"]),
        ("Conditional branches", report["conditional_branches"]),
        ("Direct calls", report["direct_calls"]),
        ("Loop SCCs", report["loop_sccs"]),
        ("Maximum direct-call depth", "recursive" if report["recursive_direct_calls"] else report["maximum_direct_call_depth"]),
    ]
    lines = [f"# {target_name} RV64 structural analysis", "", "| Metric | Value |", "|---|---:|"]
    lines.extend(f"| {name} | {value} |" for name, value in values)
    lines.extend(["", "## Opcode classes", "", "| Class | Instructions |", "|---|---:|"])
    lines.extend(f"| {name} | {value} |" for name, value in report["opcode_classes"].items())
    lines.extend(["", "## ISA gate", ""])
    bad = report["forbidden_reachable_instructions"]
    if not bad:
        lines.append("All reachable instructions are RV64IM_Zicclsm.")
    else:
        lines.append("| Address | Function | Instruction | Reason |")
        lines.append("|---|---|---|---|")
        lines.extend(
            f"| {item['address']} | {item['function']} | {item['mnemonic']} {item['operands']} | {item['reason']} |"
            for item in bad
        )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf")
    parser.add_argument("--objdump", required=True, help="target objdump executable")
    parser.add_argument("--entry", action="append", default=[])
    parser.add_argument("--owner", action="append", default=[], metavar="GLOB=OWNER")
    parser.add_argument("--target", default="RV64 target")
    parser.add_argument("--json", type=pathlib.Path)
    parser.add_argument("--markdown", type=pathlib.Path)
    parser.add_argument("--allow-forbidden", action="store_true")
    args = parser.parse_args()
    try:
        completed = subprocess.run(
            [args.objdump, "-d", "-M", "no-aliases", args.elf],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        insns, functions = parse(completed.stdout)
        report = analyze(insns, functions, args.entry or ["_start"], owners(args.owner))
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        parser.error(str(error))
    payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.json:
        args.json.write_text(payload)
    else:
        sys.stdout.write(payload)
    if args.markdown:
        args.markdown.write_text(markdown(args.target, report))
    return int(bool(report["forbidden_reachable_instructions"]) and not args.allow_forbidden)


if __name__ == "__main__":
    raise SystemExit(main())
