#!/usr/bin/env python3
"""Statistical motif analysis of a compiled RISC-V binary, for proof-reuse planning.

The question this answers is not "which instruction sequences are frequent" but "which repeat
often enough, across enough distinct function instances, that one parameterised lemma pays for
itself". Those are different questions, and raw n-gram frequency answers the first badly:

  * occurrences of a periodic motif overlap themselves, inflating long motifs by ~8x here;
  * an unrolled byte copy inside one function instance looks identical to a genuinely shared idiom
    until you count distinct owners;
  * with one alphabet symbol at 14% of the stream, an i.i.d. null calls almost everything
    significant.

So this tool reports four counts per motif rather than one, enumerates maximal repeats with a
suffix array instead of fixing n in advance, and tests against randomisation nulls that preserve
the structure the compiler actually imposes. It also computes the scheduler-invariant motif count,
because the instruction scheduler interleaves independent instructions and thereby fragments one
idiom into many sequence-distinct variants.

Nothing here is trusted by any proof. It ranks candidates for a human to act on.
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import json
import pathlib
import re
import sys

import numpy as np

# --------------------------------------------------------------------------------------------
# RISC-V surface facts
# --------------------------------------------------------------------------------------------

ABI_REGISTERS = {
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "fp", "s1",
    "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7",
    "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11",
    "t3", "t4", "t5", "t6",
}

# Registers whose identity a lemma cannot abstract over: the ABI pins their meaning.
PINNED_REGISTERS = {"zero", "ra", "sp", "gp", "tp"}

# Instruction classes as implemented in BinaryFv/Zesu/MachineExecution/InstructionClassSteps.lean.
# MULDIV has no class lemma there yet; it is named so the gap shows up in the report instead of
# being silently folded into RTYPE.
CLASS_OF_MNEMONIC = {
    **{m: "ITYPE" for m in (
        "addi", "andi", "ori", "xori", "slti", "sltiu", "addiw", "li", "mv", "sext.w", "not",
        "neg", "negw", "seqz", "snez", "zext.w",
    )},
    **{m: "SHIFTIOP" for m in ("slli", "srli", "srai", "slliw", "srliw", "sraiw")},
    **{m: "RTYPE" for m in (
        "add", "sub", "sll", "slt", "sltu", "xor", "srl", "sra", "or", "and",
        "addw", "subw", "sllw", "srlw", "sraw",
    )},
    **{m: "MULDIV" for m in (
        "mul", "mulh", "mulhsu", "mulhu", "div", "divu", "rem", "remu",
        "mulw", "divw", "divuw", "remw", "remuw",
    )},
    **{m: "LOAD" for m in ("lb", "lh", "lw", "ld", "lbu", "lhu", "lwu")},
    **{m: "STORE" for m in ("sb", "sh", "sw", "sd")},
    **{m: "BTYPE" for m in (
        "beq", "bne", "blt", "bge", "bltu", "bgeu",
        "beqz", "bnez", "blez", "bgez", "bltz", "bgtz", "bgt", "ble", "bgtu", "bleu",
    )},
    **{m: "JAL" for m in ("jal", "j")},
    **{m: "JALR" for m in ("jalr", "jr", "ret", "tail")},
    "auipc": "AUIPC",
    "lui": "LUI",
    "ecall": "SYSTEM",
    "ebreak": "SYSTEM",
    "fence": "FENCE",
    "fence.i": "FENCE",
    "nop": "ITYPE",
    "unimp": "SYSTEM",
}

MEMORY_OPERAND = re.compile(r"^(-?0x[0-9a-fA-F]+|-?\d+)\(([a-z0-9]+)\)$")
IMMEDIATE = re.compile(r"^-?(?:0x[0-9a-fA-F]+|\d+)$")


# --------------------------------------------------------------------------------------------
# Operand parsing
# --------------------------------------------------------------------------------------------

@dataclasses.dataclass(frozen=True)
class Operands:
    """Positional operands. The region database stores reads/writes as sorted sets, which loses
    the dataflow role of each register; recovering it is what makes alpha-renaming meaningful."""

    registers: tuple[str, ...]      # in source order, including a memory base register
    immediates: tuple[int, ...]     # in source order
    branch_target: int | None


def parse_operands(text: str) -> Operands:
    body = text.split(" <", 1)[0].strip()
    if not body:
        return Operands((), (), None)
    registers: list[str] = []
    immediates: list[int] = []
    target: int | None = None
    for field in (f.strip() for f in body.split(",")):
        if not field:
            continue
        memory = MEMORY_OPERAND.match(field)
        if memory:
            immediates.append(int(memory.group(1), 0))
            registers.append(memory.group(2))
            continue
        if field in ABI_REGISTERS:
            registers.append(field)
            continue
        if IMMEDIATE.match(field):
            value = int(field, 0)
            # A bare immediate large enough to be a code address in a transfer operand is the
            # branch target, not an immediate the lemma would take as an argument.
            if value >= 0x10000:
                target = value
            else:
                immediates.append(value)
            continue
        raise ValueError(f"unparsed operand field {field!r} in {text!r}")
    return Operands(tuple(registers), tuple(immediates), target)


# --------------------------------------------------------------------------------------------
# Corpus
# --------------------------------------------------------------------------------------------

@dataclasses.dataclass
class Instruction:
    address: int
    mnemonic: str
    operands: Operands
    reads: tuple[str, ...]
    writes: tuple[str, ...]
    memory: tuple[tuple[str, int], ...]   # (kind, bytes)
    transfer: str
    owner: str
    symbol: str
    word: int
    scc: int
    loop: bool
    live_out: tuple[str, ...]

    @property
    def klass(self) -> str:
        return CLASS_OF_MNEMONIC.get(self.mnemonic, "UNMAPPED")


def load_regions(path: pathlib.Path) -> tuple[list[Instruction], dict]:
    database = json.loads(path.read_text())
    rows = sorted(database["instructions"], key=lambda row: row["address"])
    instructions = [
        Instruction(
            address=row["address"],
            mnemonic=row["mnemonic"],
            operands=parse_operands(row["operands"]),
            reads=tuple(row["reads"]),
            writes=tuple(row["writes"]),
            memory=tuple((entry["kind"], entry["bytes"]) for entry in row["memory"]),
            transfer=row["transfer"],
            owner=row["owner"],
            symbol=row["symbol"],
            word=row["word"],
            scc=row["scc"],
            loop=row["loop"],
            live_out=tuple(row["liveOut"]),
        )
        for row in rows
    ]
    return instructions, database


def segment(instructions: list[Instruction], database: dict) -> list[list[int]]:
    """Maximal straight-line runs. A motif may not cross a boundary, because a `Seg` lemma cannot."""
    predecessors: collections.Counter[int] = collections.Counter()
    for row in database["instructions"]:
        for successor in row["successors"]:
            predecessors[successor] += 1
    segments: list[list[int]] = []
    current: list[int] = []
    for index, instruction in enumerate(instructions):
        if current:
            previous = instructions[current[-1]]
            contiguous = (
                instruction.address == previous.address + 4
                and previous.transfer == "ordinary"
                and predecessors[instruction.address] <= 1
            )
            if not contiguous:
                segments.append(current)
                current = []
        current.append(index)
    if current:
        segments.append(current)
    return segments


# --------------------------------------------------------------------------------------------
# Token lattice
# --------------------------------------------------------------------------------------------

def token_L0(window: list[Instruction], index: int) -> str:
    instruction = window[index]
    return f"{instruction.mnemonic} {instruction.operands}"


def alpha_rename(window: list[Instruction]) -> list[str]:
    """Rename registers by order of first appearance inside the window, holding ABI-pinned
    registers fixed. A motif at this level corresponds to one parameterised `Seg` theorem, with
    the renamed registers and the immediates as its arguments."""
    mapping: dict[str, str] = {}

    def rename(register: str) -> str:
        if register in PINNED_REGISTERS:
            return register
        if register not in mapping:
            mapping[register] = f"r{len(mapping)}"
        return mapping[register]

    tokens = []
    for instruction in window:
        roles = ",".join(rename(register) for register in instruction.operands.registers)
        tokens.append(f"{instruction.mnemonic}({roles})")
    return tokens


def token_levels(instructions: list[Instruction]) -> dict[str, list[str]]:
    """Every level is reported. The abstraction level dominates every other choice in this
    analysis, so it is an axis of the result rather than a hidden parameter."""
    levels: dict[str, list[str]] = {}
    levels["L0_word"] = [f"{i.word:08x}" for i in instructions]
    levels["L1_mnemonic_operands"] = [
        f"{i.mnemonic} {i.operands.registers} {i.operands.immediates}" for i in instructions
    ]
    levels["L2_mnemonic_registers"] = [
        f"{i.mnemonic}|{','.join(i.operands.registers)}" for i in instructions
    ]
    # L3 is window-relative, so it is built per window rather than per instruction; the
    # per-instruction placeholder keeps the dict uniform and is never used for enumeration.
    levels["L4_mnemonic"] = [i.mnemonic for i in instructions]
    levels["L5_class"] = [i.klass for i in instructions]
    return levels


# --------------------------------------------------------------------------------------------
# Suffix array, LCP, maximal repeats
# --------------------------------------------------------------------------------------------

def suffix_array(stream: list[int]) -> list[int]:
    n = len(stream)
    if n == 0:
        return []
    order = list(range(n))
    rank = list(stream)
    step = 1
    while True:
        key = lambda i: (rank[i], rank[i + step] if i + step < n else -1)
        order.sort(key=key)
        new_rank = [0] * n
        for position in range(1, n):
            new_rank[order[position]] = new_rank[order[position - 1]] + (
                key(order[position]) != key(order[position - 1])
            )
        rank = new_rank
        if rank[order[-1]] == n - 1:
            return order
        step *= 2


def lcp_array(stream: list[int], order: list[int]) -> list[int]:
    """Kasai. lcp[i] is the common prefix length of order[i-1] and order[i]; lcp[0] is 0."""
    n = len(stream)
    position = [0] * n
    for index, suffix in enumerate(order):
        position[suffix] = index
    lcp = [0] * n
    length = 0
    for suffix in range(n):
        if position[suffix] == 0:
            length = 0
            continue
        previous = order[position[suffix] - 1]
        while (
            suffix + length < n
            and previous + length < n
            and stream[suffix + length] == stream[previous + length]
        ):
            length += 1
        lcp[position[suffix]] = length
        if length:
            length -= 1
    return lcp


def maximal_repeats(stream: list[int], minimum_length: int = 2) -> list[tuple[int, list[int]]]:
    """All maximal repeats: right-maximal by construction from LCP intervals, then filtered for
    left-maximality. For substrings this is exactly the set of closed frequent patterns, which is
    why the result set is a property of the binary rather than of the enumeration order."""
    n = len(stream)
    if n == 0:
        return []
    order = suffix_array(stream)
    lcp = lcp_array(stream, order)

    results: list[tuple[int, list[int]]] = []
    seen: set[tuple[int, int]] = set()

    def emit(length: int, low: int, high: int) -> None:
        if length < minimum_length or high - low + 1 < 2:
            return
        if (length, order[low]) in seen:
            return
        seen.add((length, order[low]))
        positions = sorted(order[low : high + 1])
        left = {stream[p - 1] if p > 0 else None for p in positions}
        if len(left) < 2:
            return                       # left-extendable: not a maximal repeat
        results.append((length, positions))

    stack: list[tuple[int, int]] = []    # (lcp value, interval start)
    for index in range(1, n + 1):
        value = lcp[index] if index < n else 0
        start = index
        while stack and stack[-1][0] > value:
            length, low = stack.pop()
            emit(length, low - 1, index - 1)
            start = low
        if not stack or stack[-1][0] < value:
            stack.append((value, start))
    return results


# --------------------------------------------------------------------------------------------
# Occurrence statistics
# --------------------------------------------------------------------------------------------

def non_overlapping(positions: list[int], length: int) -> int:
    """Greedy leftmost, which is exact for occurrences of one fixed-length string."""
    count = 0
    limit = -1
    for position in positions:
        if position >= limit:
            count += 1
            limit = position + length
    return count


def smallest_period(tokens: tuple[int, ...]) -> int:
    """KMP failure function; a period shorter than the motif means the motif is a tandem repeat,
    which is an unrolled loop and belongs to an induction lemma, not to a motif lemma."""
    length = len(tokens)
    failure = [0] * length
    k = 0
    for i in range(1, length):
        while k and tokens[i] != tokens[k]:
            k = failure[k - 1]
        if tokens[i] == tokens[k]:
            k += 1
        failure[i] = k
    return length - failure[-1]


def owner_support(positions: list[int], length: int, owner_of: list[str]) -> tuple[int, int]:
    """Owners that contain a whole occurrence, and the number of occurrences that straddle an
    owner boundary. A motif that straddles is not a per-instance reusable lemma."""
    owners: set[str] = set()
    straddling = 0
    for position in positions:
        window = owner_of[position : position + length]
        if len(set(window)) == 1:
            owners.add(window[0])
        else:
            straddling += 1
    return len(owners), straddling


# --------------------------------------------------------------------------------------------
# Scheduler-invariant canonical form
# --------------------------------------------------------------------------------------------

def effective_reads(instruction: Instruction) -> tuple[str, ...]:
    """The region database leaves `reads` empty for `jalr`, whose operand register is the link it
    jumps through. Taking the union with the parsed source operands stops a re-scheduling from
    hoisting a call above the `auipc` that sets up its target."""
    return tuple(
        sorted(set(instruction.reads) | {register for _, register in source_slots(instruction)})
    )


def dependence_edges(window: list[Instruction]) -> list[tuple[int, int, str]]:
    """Intra-window dependences that any valid re-scheduling must respect: register RAW/WAR/WAW,
    memory ordering between accesses we cannot prove disjoint, and the rule that a control
    transfer terminates its straight-line segment and so cannot move earlier."""
    edges: list[tuple[int, int, str]] = []
    last_write: dict[str, int] = {}
    last_reads: dict[str, list[int]] = collections.defaultdict(list)
    last_store: int | None = None
    last_loads: list[int] = []
    for index, instruction in enumerate(window):
        if instruction.transfer != "ordinary":
            edges.extend((earlier, index, "terminator") for earlier in range(index))
        for register in effective_reads(instruction):
            if register in last_write:
                edges.append((last_write[register], index, "raw"))
            last_reads[register].append(index)
        for register in instruction.writes:
            if register in last_write:
                edges.append((last_write[register], index, "waw"))
            for reader in last_reads.get(register, ()):
                if reader != index:
                    edges.append((reader, index, "war"))
            last_reads[register] = []
            last_write[register] = index
        kinds = {kind for kind, _ in instruction.memory}
        if "read" in kinds:
            if last_store is not None:
                edges.append((last_store, index, "mem"))
            last_loads.append(index)
        if "write" in kinds:
            if last_store is not None:
                edges.append((last_store, index, "mem"))
            for loader in last_loads:
                edges.append((loader, index, "mem"))
            last_loads = []
            last_store = index
    return sorted(set(edges))


def source_slots(instruction: Instruction) -> list[tuple[int, str]]:
    """Operand slots that are read. Slot 0 is the destination whenever the instruction writes a
    register and is not a store or a branch; everything else is a source, including a memory base
    register. Without this, a destination operand is mistaken for a use of a live-in register."""
    registers = instruction.operands.registers
    if not registers:
        return []
    writes_first_slot = bool(instruction.writes) and registers[0] in instruction.writes
    start = 1 if writes_first_slot else 0
    return [(slot, registers[slot]) for slot in range(start, len(registers))]


def dag_graph(window: list[Instruction]) -> tuple[list[str], list[tuple[int, int, str]]]:
    """Nodes labelled by mnemonic alone, plus one virtual node per register the window reads
    before writing.

    Register *identity* is carried by the edges, not by the node labels: a use is tied to its
    defining node, and two uses of the same live-in register share a virtual source. That is what
    makes the form invariant under re-scheduling — an alpha-renaming computed from the emitted
    order would not be, because a differently scheduled occurrence of the same idiom renames its
    registers differently.
    """
    size = len(window)
    labels = [instruction.mnemonic for instruction in window]
    edges = list(dependence_edges(window))

    live_in: dict[str, int] = {}
    defined: set[str] = set()

    def source_node(register: str) -> int:
        if register not in live_in:
            live_in[register] = size + len(live_in)
            labels.append(f"in:{register}" if register in PINNED_REGISTERS else "in")
        return live_in[register]

    for index, instruction in enumerate(window):
        explicit = set()
        for slot, register in source_slots(instruction):
            explicit.add(register)
            if register not in defined:
                edges.append((source_node(register), index, f"in{slot}"))
        for register in effective_reads(instruction):
            if register not in explicit and register not in defined:
                edges.append((source_node(register), index, "in*"))
        defined.update(instruction.writes)
    return labels, sorted(set(edges))


def _refine(
    colour: list[str],
    predecessors: dict[int, list[tuple[int, str]]],
    successors: dict[int, list[tuple[int, str]]],
) -> list[str]:
    size = len(colour)
    for _ in range(size):
        refined = []
        for node in range(size):
            up = sorted((kind, colour[source]) for source, kind in predecessors[node])
            down = sorted((kind, colour[sink]) for sink, kind in successors[node])
            refined.append(f"{colour[node]}<{up}|{down}>")
        table = {value: index for index, value in enumerate(sorted(set(refined)))}
        new_colour = [str(table[value]) for value in refined]
        if new_colour == colour:
            break
        colour = new_colour
    return colour


def dag_canonical_form(window: list[Instruction], leaf_budget: int = 256) -> str:
    """Weisfeiler-Leman refinement, then individualisation-refinement on the remaining ties.

    Refinement alone is not enough: when two nodes keep the same colour, emitting them in their
    original index order reintroduces exactly the scheduling dependence this form exists to
    remove. Ties are therefore resolved by individualising each tied node in turn and taking the
    lexicographically smallest result. `budgetExceeded` marks the windows where the search was cut
    off, so an approximate answer is never reported as an exact one.
    """
    labels, edges = dag_graph(window)
    size = len(labels)
    predecessors: dict[int, list[tuple[int, str]]] = collections.defaultdict(list)
    successors: dict[int, list[tuple[int, str]]] = collections.defaultdict(list)
    for source, sink, kind in edges:
        predecessors[sink].append((source, kind))
        successors[source].append((sink, kind))

    leaves = 0

    def emit(colour: list[str]) -> str:
        order = sorted(range(size), key=lambda node: colour[node])
        rank = {node: index for index, node in enumerate(order)}
        return "|".join(
            f"{labels[node]}:{sorted((rank[s], k) for s, k in predecessors[node])}"
            for node in order
        )

    def search(colour: list[str]) -> str:
        nonlocal leaves
        classes: dict[str, list[int]] = collections.defaultdict(list)
        for node, value in enumerate(colour):
            classes[value].append(node)
        tied = [nodes for nodes in classes.values() if len(nodes) > 1]
        if not tied:
            leaves += 1
            return emit(colour)
        target = min(tied, key=lambda nodes: (len(nodes), colour[nodes[0]]))
        best: str | None = None
        for node in target:
            if leaves >= leaf_budget:
                break
            individualised = list(colour)
            individualised[node] = colour[node] + "!"
            candidate = search(_refine(individualised, predecessors, successors))
            if best is None or candidate < best:
                best = candidate
        if best is None:                       # budget exhausted before any leaf
            leaves += 1
            return emit(colour)
        return best

    form = search(_refine(list(labels), predecessors, successors))
    return form if leaves < leaf_budget else "approx:" + form


def reschedule(
    window: list[Instruction], rng: np.random.Generator
) -> list[Instruction] | None:
    """A uniformly chosen valid topological order of the window's dependence graph, or None when
    the schedule is forced."""
    size = len(window)
    indegree = [0] * size
    successors: dict[int, list[int]] = collections.defaultdict(list)
    for source, sink, _ in dependence_edges(window):
        successors[source].append(sink)
        indegree[sink] += 1
    ready = [node for node in range(size) if indegree[node] == 0]
    order: list[int] = []
    while ready:
        node = ready.pop(int(rng.integers(len(ready))))
        order.append(node)
        for sink in successors[node]:
            indegree[sink] -= 1
            if indegree[sink] == 0:
                ready.append(sink)
    if len(order) != size or order == list(range(size)):
        return None
    return [window[node] for node in order]


def validate_dag_invariance(
    windows: list[list[Instruction]], rng: np.random.Generator, trials: int = 8
) -> dict:
    """Re-schedule real windows and require the canonical form to be unchanged, then require a
    deliberately order-dependent form to break under the same re-schedulings.

    The second half is the point. A canonical form that returned a constant would pass the first
    half perfectly, so invariance alone is not evidence of anything.
    """
    reschedules = 0
    failures = 0
    control_failures = 0
    for window in windows:
        base = dag_canonical_form(window)
        control = "|".join(alpha_rename(window))
        for _ in range(trials):
            permuted = reschedule(window, rng)
            if permuted is None:
                continue
            reschedules += 1
            if dag_canonical_form(permuted) != base:
                failures += 1
            if "|".join(alpha_rename(permuted)) != control:
                control_failures += 1
    return {
        "windowsChecked": len(windows),
        "reschedulesTried": reschedules,
        "failures": failures,
        "orderDependentControlFailures": control_failures,
    }


# --------------------------------------------------------------------------------------------
# Nulls and significance
# --------------------------------------------------------------------------------------------

MAXIMUM_SLOTS = 3
PINNED_OFFSET = 1 << 20
PADDING_CODE = 1 << 21


@dataclasses.dataclass
class AlphaFrame:
    """The corpus in the form the nulls resample: one row per instruction, so a null permutes
    whole instructions and the alpha-renaming is recomputed from whatever lands where."""

    mnemonic: np.ndarray          # (n,)
    registers: np.ndarray         # (n, MAXIMUM_SLOTS) register ids, -1 for an empty slot
    pinned: np.ndarray            # (n, MAXIMUM_SLOTS) bool
    owner: np.ndarray             # (n,)
    bounds: list[tuple[int, int]]


def alpha_frame(instructions: list[Instruction], segments: list[list[int]]) -> AlphaFrame:
    order = [index for indices in segments for index in indices]
    bounds = []
    offset = 0
    for indices in segments:
        bounds.append((offset, offset + len(indices)))
        offset += len(indices)

    mnemonics: dict[str, int] = {}
    registers_table: dict[str, int] = {}
    mnemonic = np.empty(len(order), dtype=np.int64)
    registers = np.full((len(order), MAXIMUM_SLOTS), -1, dtype=np.int64)
    pinned = np.zeros((len(order), MAXIMUM_SLOTS), dtype=bool)
    owner = np.empty(len(order), dtype=np.int64)
    owners_table: dict[str, int] = {}
    for row, index in enumerate(order):
        instruction = instructions[index]
        mnemonic[row] = mnemonics.setdefault(instruction.mnemonic, len(mnemonics))
        owner[row] = owners_table.setdefault(instruction.owner, len(owners_table))
        for slot, register in enumerate(instruction.operands.registers[:MAXIMUM_SLOTS]):
            registers[row, slot] = registers_table.setdefault(register, len(registers_table))
            pinned[row, slot] = register in PINNED_REGISTERS
    return AlphaFrame(mnemonic, registers, pinned, owner, bounds)


def alpha_keys(frame: AlphaFrame, take: np.ndarray, starts: np.ndarray, length: int) -> np.ndarray:
    """Alpha-renamed window keys for every start, vectorised.

    `take[p]` is the instruction now sitting at stream position `p`, which is how a null permutes
    the corpus. Renaming is by first occurrence within the window, computed as the index of the
    first equal slot, with ABI-pinned registers and empty slots given codes of their own.
    """
    rows = starts[:, None] + np.arange(length)[None, :]
    chosen = take[rows]                                        # (windows, length)
    registers = frame.registers[chosen].reshape(len(starts), length * MAXIMUM_SLOTS)
    pinned = frame.pinned[chosen].reshape(len(starts), length * MAXIMUM_SLOTS)
    empty = registers < 0

    equal = registers[:, :, None] == registers[:, None, :]
    first = np.argmax(equal, axis=1)                           # first slot holding the same value
    code = np.where(empty, PADDING_CODE, np.where(pinned, PINNED_OFFSET + registers, first))

    key = np.zeros(len(starts), dtype=np.uint64)
    multiplier = np.uint64(1_000_003)
    for column in range(length):
        key = key * multiplier + frame.mnemonic[chosen[:, column]].astype(np.uint64)
    for column in range(code.shape[1]):
        key = key * multiplier + code[:, column].astype(np.uint64)
    return key


def alpha_max_statistics(
    frame: AlphaFrame, take: np.ndarray, starts: np.ndarray, length: int
) -> tuple[int, int]:
    """Largest non-overlapping count and largest owner support over all alpha-motifs of this
    length. Groups are visited largest first and the scan stops when no remaining group can win,
    which is exact rather than a sample."""
    if starts.size == 0:
        return 0, 0
    keys = alpha_keys(frame, take, starts, length)
    order = np.argsort(keys, kind="stable")
    sorted_keys = keys[order]
    sorted_starts = starts[order]
    boundaries = np.flatnonzero(np.r_[True, sorted_keys[1:] != sorted_keys[:-1]])
    sizes = np.r_[boundaries[1:], sorted_keys.size] - boundaries

    owners_at = frame.owner[take]
    best_count = 0
    best_owners = 0
    for group in np.argsort(-sizes, kind="stable"):
        size = int(sizes[group])
        if size < 2 or (size <= best_count and size <= best_owners):
            break
        begin = int(boundaries[group])
        positions = np.sort(sorted_starts[begin : begin + size])
        count = 0
        limit = -1
        owners = set()
        for position in positions:
            if position >= limit:
                count += 1
                limit = position + length
            window = owners_at[position : position + length]
            if np.all(window == window[0]):
                owners.add(int(window[0]))
        best_count = max(best_count, count)
        best_owners = max(best_owners, len(owners))
    return best_count, best_owners


def null_take_within_segment(frame: AlphaFrame, rng: np.random.Generator) -> np.ndarray:
    """N2. Permute whole instructions inside each straight-line segment. Preserves each segment's
    exact instruction multiset, so it tests ordering and register linkage and nothing else."""
    take = np.arange(frame.mnemonic.size)
    for begin, end in frame.bounds:
        take[begin:end] = rng.permutation(take[begin:end])
    return take


def null_take_within_owner(frame: AlphaFrame, rng: np.random.Generator) -> np.ndarray:
    """N3. Permute whole instructions inside each owner. Preserves each function instance's exact
    composition while destroying the ordering it shares with other instances, which is the claim
    the reuse argument rests on."""
    take = np.arange(frame.mnemonic.size)
    for owner in np.unique(frame.owner):
        index = np.flatnonzero(frame.owner == owner)
        take[index] = index[rng.permutation(index.size)]
    return take


def null_take_markov(frame: AlphaFrame, rng: np.random.Generator) -> np.ndarray:
    """N1. Draw a mnemonic sequence from a fitted order-1 chain, then draw a real instruction of
    that mnemonic. Adjacent-pair structure and the per-mnemonic operand distribution both survive;
    only the register linkage between neighbours is destroyed."""
    alphabet = int(frame.mnemonic.max()) + 1
    counts = np.zeros((alphabet, alphabet))
    initial = np.zeros(alphabet)
    for begin, end in frame.bounds:
        initial[frame.mnemonic[begin]] += 1
        np.add.at(counts, (frame.mnemonic[begin : end - 1], frame.mnemonic[begin + 1 : end]), 1)
    initial /= initial.sum()
    totals = counts.sum(axis=1, keepdims=True)
    transitions = np.where(totals > 0, counts / np.maximum(totals, 1), 1.0 / alphabet)

    pool = {value: np.flatnonzero(frame.mnemonic == value) for value in range(alphabet)}
    initial_cdf = np.cumsum(initial)
    transition_cdf = np.cumsum(transitions, axis=1)
    starts = np.array([begin for begin, _ in frame.bounds])
    lengths = np.array([end - begin for begin, end in frame.bounds])

    drawn = np.empty(frame.mnemonic.size, dtype=np.int64)
    state = np.searchsorted(initial_cdf, rng.random(starts.size))
    drawn[starts] = state
    for offset in range(1, int(lengths.max())):
        live = np.flatnonzero(lengths > offset)
        if live.size == 0:
            break
        following = (rng.random(live.size)[:, None] > transition_cdf[state[live]]).sum(axis=1)
        np.clip(following, 0, alphabet - 1, out=following)
        state[live] = following
        drawn[starts[live] + offset] = following

    take = np.empty_like(drawn)
    for value, candidates in pool.items():
        where = np.flatnonzero(drawn == value)
        if where.size:
            take[where] = candidates[rng.integers(candidates.size, size=where.size)]
    return take


ALPHA_NULLS = {
    "N1_markovInstruction": null_take_markov,
    "N2_segmentPermutation": null_take_within_segment,
    "N3_ownerPermutation": null_take_within_owner,
}


def alpha_permutation_test(
    frame: AlphaFrame, lengths: list[int], resamples: int, rng: np.random.Generator
) -> dict:
    """Westfall-Young max-statistic test at the alpha level.

    Comparing an observed motif against the distribution of the *maximum* statistic over every
    motif of its length controls the family-wise error rate directly, so no correction is applied
    afterwards and no candidate set has to be declared in advance.
    """
    identity = np.arange(frame.mnemonic.size)
    starts_by_length = {
        length: np.array(
            [
                position
                for begin, end in frame.bounds
                for position in range(begin, end - length + 1)
            ],
            dtype=np.int64,
        )
        for length in lengths
    }
    observed = {
        length: alpha_max_statistics(frame, identity, starts_by_length[length], length)
        for length in lengths
    }
    distributions: dict[str, dict[int, dict[str, list[int]]]] = {}
    for name, draw in ALPHA_NULLS.items():
        per_length = {length: {"count": [], "owners": []} for length in lengths}
        for _ in range(resamples):
            take = draw(frame, rng)
            for length in lengths:
                count, owners = alpha_max_statistics(
                    frame, take, starts_by_length[length], length
                )
                per_length[length]["count"].append(count)
                per_length[length]["owners"].append(owners)
        distributions[name] = per_length
    return {"observed": observed, "null": distributions, "resamples": resamples}


def empirical_p(null_values: list[int], observed: int) -> float:
    """Add-one estimator: never reports p = 0, which a finite resample cannot justify."""
    exceed = sum(1 for value in null_values if value >= observed)
    return (exceed + 1) / (len(null_values) + 1)


# --------------------------------------------------------------------------------------------
# Motif enumeration over the token lattice
# --------------------------------------------------------------------------------------------

MAXIMUM_LENGTH = 40


def stream_with_separators(
    tokens: list[str], segments: list[list[int]]
) -> tuple[list[int], list[int], dict[int, int]]:
    """One integer stream, segments joined by separators unique to each boundary so that no repeat
    can span two segments. Returns the stream, the stream positions, and stream->instruction."""
    table: dict[str, int] = {}
    stream: list[int] = []
    to_instruction: dict[int, int] = {}
    positions: list[int] = []
    for number, indices in enumerate(segments):
        if number:
            stream.append(-1 - number)
        for index in indices:
            token = tokens[index]
            to_instruction[len(stream)] = index
            positions.append(len(stream))
            stream.append(table.setdefault(token, len(table)))
    return stream, positions, to_instruction


def length_spectrum(tokens: list[str], segments: list[list[int]]) -> dict[int, dict]:
    """Distinct and repeated window counts at every length. Reported so the choice of length is
    visibly made by the data rather than assumed."""
    spectrum: dict[int, dict] = {}
    for length in range(2, MAXIMUM_LENGTH + 1):
        counts: collections.Counter[tuple[str, ...]] = collections.Counter()
        windows = 0
        for indices in segments:
            for start in range(len(indices) - length + 1):
                counts[tuple(tokens[i] for i in indices[start : start + length])] += 1
                windows += 1
        repeated = {gram: count for gram, count in counts.items() if count >= 2}
        if not windows:
            break
        spectrum[length] = {
            "windows": windows,
            "distinct": len(counts),
            "repeated": len(repeated),
            "maximumRawCount": max(repeated.values(), default=0),
        }
    return spectrum


def alpha_motifs(
    instructions: list[Instruction], segments: list[list[int]]
) -> dict[int, dict[tuple[str, ...], list[int]]]:
    """Alpha-renamed motifs by length, mapping each motif to its occurrence start indices.

    Alpha-renaming is window-relative, so a suffix array over a fixed token stream cannot
    enumerate these; they are built length by length instead.
    """
    by_length: dict[int, dict[tuple[str, ...], list[int]]] = {}
    for length in range(2, MAXIMUM_LENGTH + 1):
        occurrences: dict[tuple[str, ...], list[int]] = collections.defaultdict(list)
        any_window = False
        for indices in segments:
            for start in range(len(indices) - length + 1):
                any_window = True
                window = [instructions[i] for i in indices[start : start + length]]
                occurrences[tuple(alpha_rename(window))].append(indices[start])
        if not any_window:
            break
        by_length[length] = {
            motif: sorted(starts) for motif, starts in occurrences.items() if len(starts) >= 2
        }
    return by_length


def closed_alpha_motifs(
    by_length: dict[int, dict[tuple[str, ...], list[int]]]
) -> list[tuple[int, tuple[str, ...], list[int]]]:
    """Keep only motifs no extension preserves the occurrence set.

    Without this every window of a frequent long motif is reported as its own finding, and the
    result set describes the enumeration rather than the binary.
    """
    closed: list[tuple[int, tuple[str, ...], list[int]]] = []
    for length, motifs in by_length.items():
        longer = by_length.get(length + 1, {})
        right_extended: dict[tuple[int, ...], int] = collections.Counter()
        left_extended: dict[tuple[int, ...], int] = collections.Counter()
        for starts in longer.values():
            right_extended[tuple(starts)] += 1
            left_extended[tuple(start + 1 for start in starts)] += 1
        for motif, starts in motifs.items():
            key = tuple(starts)
            if right_extended.get(key) or left_extended.get(key):
                continue                      # an extension has the identical occurrence set
            closed.append((length, motif, starts))
    return closed


def describe_motif(
    length: int,
    motif: tuple[str, ...],
    starts: list[int],
    instructions: list[Instruction],
    owner_of: list[str],
) -> dict:
    positions = sorted(starts)
    owners, straddling = owner_support(positions, length, owner_of)
    codes = {token: index for index, token in enumerate(sorted(set(motif)))}
    period = smallest_period(tuple(codes[token] for token in motif))

    windows = [instructions[start : start + length] for start in positions]
    flat = [instruction for window in windows for instruction in window]
    immediates = {tuple(i.operands.immediates for i in window) for window in windows}
    register_writes = sum(1 for instruction in windows[0] if instruction.writes)

    return {
        "length": length,
        "motif": list(motif),
        "rawCount": len(positions),
        "nonOverlapping": non_overlapping(positions, length),
        "ownerSupport": owners,
        "straddlingOccurrences": straddling,
        "period": period,
        "tandem": period < length,
        "addresses": [f"0x{instructions[start].address:x}" for start in positions],
        "owners": sorted({owner_of[start] for start in positions}),
        "inLoop": any(instruction.loop for instruction in flat),
        "allOrdinaryTransfers": all(i.transfer == "ordinary" for i in flat),
        "memoryKinds": sorted({kind for i in flat for kind, _ in i.memory}),
        "distinctImmediateTuples": len(immediates),
        "immediatesConstant": len(immediates) == 1,
        "registerWriteSteps": register_writes,
        "liveOutAtExit": sorted(
            {register for window in windows for register in window[-1].live_out}
        ),
    }


def self_contained(motif: dict) -> tuple[bool, str]:
    """Whether the motif could be stated as one `Seg` lemma at all, before asking whether it pays."""
    if motif["straddlingOccurrences"]:
        return False, "some occurrences cross an owner boundary"
    if not motif["allOrdinaryTransfers"]:
        return False, "contains a control transfer"
    if motif["ownerSupport"] < 2:
        return False, "confined to one function instance"
    if motif["tandem"]:
        return False, f"tandem repeat of period {motif['period']}: an unrolled loop"
    return True, ""


# Only one authoring rate in PLAN_PROOF_PATTERNS.md is a measurement rather than an estimate.
MEASURED_LINES_PER_REGISTER_WRITE_STEP = 19


def payoff(motif: dict) -> dict:
    """Gross saving in the one unit that was actually measured, plus the break-even lemma cost.

    The authoring cost of a new lemma was never measured, so it is reported as a threshold the
    reader can judge rather than filled in with a number.
    """
    reuses = motif["nonOverlapping"] - 1
    covered = motif["registerWriteSteps"] * reuses
    gross = covered * MEASURED_LINES_PER_REGISTER_WRITE_STEP
    return {
        "reuses": reuses,
        "registerWriteStepsSaved": covered,
        "grossLinesSaved": gross,
        "unestimatedSteps": (motif["length"] - motif["registerWriteSteps"]) * reuses,
        "worthwhileIfLemmaCostsUnder": gross,
    }


# --------------------------------------------------------------------------------------------
# Controls
# --------------------------------------------------------------------------------------------

OBJDUMP_FUNCTION = re.compile(r"^([0-9a-f]+) <([^>]+)>:")
OBJDUMP_INSTRUCTION = re.compile(r"^\s+([0-9a-f]+):\s+[0-9a-f]+\s+(\S+)(?:\s+(.*?))?\s*$")


def read_objdump(path: pathlib.Path) -> dict[str, list[tuple[int, str, str]]]:
    functions: dict[str, list[tuple[int, str, str]]] = collections.defaultdict(list)
    name = None
    for line in path.read_text().splitlines():
        header = OBJDUMP_FUNCTION.match(line)
        if header:
            name = header.group(2)
            continue
        body = OBJDUMP_INSTRUCTION.match(line)
        if body and name:
            functions[name].append((int(body.group(1), 16), body.group(2), body.group(3) or ""))
    return dict(functions)


def objdump_mnemonic_motifs(path: pathlib.Path, minimum_count: int = 3) -> dict:
    """Mnemonic-level motifs from a plain disassembly, for the cross-target control. No owner or
    liveness metadata exists here, so this level is all the control can support."""
    functions = read_objdump(path)
    flat = [row for rows in functions.values() for row in rows]
    targets = set()
    for _, _, operands in flat:
        for match in re.finditer(r"\b0x([0-9a-f]+)\b", operands):
            targets.add(int(match.group(1), 16))
    ordered = sorted(flat)
    segments: list[list[str]] = []
    current: list[str] = []
    for address, mnemonic, _ in ordered:
        if current and address in targets:
            segments.append(current)
            current = []
        current.append(mnemonic)
        if CLASS_OF_MNEMONIC.get(mnemonic) in {"BTYPE", "JAL", "JALR"}:
            segments.append(current)
            current = []
    if current:
        segments.append(current)
    counts: collections.Counter[tuple[str, ...]] = collections.Counter()
    for length in range(3, 13):
        for tokens in segments:
            for start in range(len(tokens) - length + 1):
                counts[tuple(tokens[start : start + length])] += 1
    return {
        "instructions": len(flat),
        "functions": sorted(functions),
        "motifs": {
            " ".join(gram): count
            for gram, count in counts.items()
            if count >= minimum_count
        },
    }


def planted_motif_control(
    instructions: list[Instruction],
    segments: list[list[int]],
    rng: np.random.Generator,
    plant_length: int = 7,
    plant_count: int = 9,
) -> dict:
    """Shuffle the corpus, plant a known motif a known number of times, and require the enumerator
    to recover both length and count. A pipeline that cannot find a motif it was handed has not
    been shown to find one."""
    tokens = [instruction.mnemonic for instruction in instructions]
    shuffled = list(tokens)
    rng.shuffle(shuffled)
    template = tuple(f"plant{index}" for index in range(plant_length))
    slots = [indices for indices in segments if len(indices) >= plant_length]
    for slot in rng.permutation(len(slots))[:plant_count]:
        indices = slots[int(slot)]
        for offset, token in enumerate(template):
            shuffled[indices[offset]] = token

    occurrences: collections.Counter[tuple[str, ...]] = collections.Counter()
    for indices in segments:
        for start in range(len(indices) - plant_length + 1):
            occurrences[tuple(shuffled[i] for i in indices[start : start + plant_length])] += 1
    recovered = occurrences[template]
    return {
        "plantedLength": plant_length,
        "plantedCount": min(plant_count, len(slots)),
        "recoveredCount": recovered,
        "recovered": recovered == min(plant_count, len(slots)),
    }


def shuffled_corpus_control(
    frame: AlphaFrame,
    test: dict,
    lengths: list[int],
    rng: np.random.Generator,
) -> dict:
    """Feed the significance test a corpus with its structure shuffled out, and require it to find
    nothing.

    This is the control the whole analysis rests on. Reporting the real binary as significant
    proves nothing unless the same test declines to report noise, and a max-statistic test is
    exactly the kind that can look decisive while being incapable of returning a null result.
    """
    fake = null_take_within_segment(frame, rng)
    rows = {}
    for length in lengths:
        starts = np.array(
            [
                position
                for begin, end in frame.bounds
                for position in range(begin, end - length + 1)
            ],
            dtype=np.int64,
        )
        count, owners = alpha_max_statistics(frame, fake, starts, length)
        null = test["null"]["N2_segmentPermutation"][length]
        rows[str(length)] = {
            "observedNonOverlapping": count,
            "observedOwnerSupport": owners,
            "pNonOverlapping": empirical_p(null["count"], count),
            "pOwnerSupport": empirical_p(null["owners"], owners),
        }
    significant = sum(
        1 for row in rows.values() if min(row["pNonOverlapping"], row["pOwnerSupport"]) < 0.05
    )
    return {"perLength": rows, "significantLengths": significant, "lengthsTested": len(rows)}


# --------------------------------------------------------------------------------------------
# Driver
# --------------------------------------------------------------------------------------------

def reconcile_scope(objdump_path: pathlib.Path | None, database: dict) -> dict:
    summary = database["summary"]
    scope = {
        "regionRows": summary["instructionCount"],
        "declaredRegionAddresses": summary["binaryInstructionCount"],
        "unownedInDeclaredRegions": (
            summary["binaryInstructionCount"] - summary["instructionCount"]
        ),
    }
    if objdump_path and objdump_path.exists():
        functions = read_objdump(objdump_path)
        per_symbol = {name: len(rows) for name, rows in sorted(functions.items())}
        scope["objdumpTextInstructions"] = sum(per_symbol.values())
        scope["objdumpPerSymbol"] = per_symbol
        covered = {row["symbol"] for row in database["instructions"]}
        scope["symbolsOutsideDeclaredRegions"] = sorted(set(per_symbol) - covered)
    return scope


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--regions", type=pathlib.Path, required=True)
    parser.add_argument("--out-json", type=pathlib.Path, required=True)
    parser.add_argument("--out-md", type=pathlib.Path, default=None)
    parser.add_argument("--objdump", type=pathlib.Path, default=None)
    parser.add_argument("--control-objdump", type=pathlib.Path, default=None)
    parser.add_argument("--resamples", type=int, default=2000)
    parser.add_argument("--maximum-test-length", type=int, default=16)
    parser.add_argument("--dag-lengths", type=int, nargs="*", default=[4, 6, 8])
    parser.add_argument("--dag-windows", type=int, default=300)
    parser.add_argument("--seed", type=int, default=20260810)
    arguments = parser.parse_args()

    rng = np.random.default_rng(arguments.seed)
    instructions, database = load_regions(arguments.regions)
    segments = segment(instructions, database)
    owner_of = [instruction.owner for instruction in instructions]

    result: dict = {
        "producer": {"tool": "ngram_motifs.py", "seed": arguments.seed},
        "inputs": database["inputs"],
        "scope": reconcile_scope(arguments.objdump, database),
        "corpus": {
            "instructions": len(instructions),
            "segments": len(segments),
            "owners": len(set(owner_of)),
            "alphabet": {
                name: len(set(tokens)) for name, tokens in token_levels(instructions).items()
            },
        },
    }

    result["lengthSpectrum"] = {
        name: {str(length): row for length, row in length_spectrum(tokens, segments).items()}
        for name, tokens in token_levels(instructions).items()
    }

    by_length = alpha_motifs(instructions, segments)
    result["lengthSpectrum"]["L3_alpha"] = {
        str(length): {
            "repeated": len(motifs),
            "maximumRawCount": max((len(s) for s in motifs.values()), default=0),
        }
        for length, motifs in by_length.items()
    }

    described = []
    for length, motif, starts in closed_alpha_motifs(by_length):
        row = describe_motif(length, motif, starts, instructions, owner_of)
        usable, reason = self_contained(row)
        row["selfContained"] = usable
        row["disqualification"] = reason
        row["payoff"] = payoff(row)
        described.append(row)
    described.sort(
        key=lambda row: (-row["ownerSupport"], -row["payoff"]["grossLinesSaved"], row["length"])
    )

    # Significance: family-wise max-statistic permutation test, at the same alpha level the
    # motifs are stated in. Lengths are taken from the motifs that survived, so no length that
    # produced a candidate goes untested.
    frame = alpha_frame(instructions, segments)
    lengths = sorted(
        {row["length"] for row in described if row["selfContained"]}
        & set(range(2, arguments.maximum_test_length + 1))
    )
    test = alpha_permutation_test(frame, lengths, arguments.resamples, rng)
    result["permutationTest"] = {
        "resamples": test["resamples"],
        "lengths": lengths,
        "statistic": "family-wise maximum over all alpha-motifs of each length",
        "observedMaximum": {
            str(length): {"nonOverlapping": value[0], "ownerSupport": value[1]}
            for length, value in test["observed"].items()
        },
        "nullMaximum": {
            name: {
                str(length): {
                    statistic: {
                        "mean": round(float(np.mean(values)), 3),
                        "p95": float(np.quantile(values, 0.95)),
                        "max": int(max(values)),
                    }
                    for statistic, values in per_length.items()
                }
                for length, per_length in by_length_null.items()
            }
            for name, by_length_null in test["null"].items()
        },
    }

    for row in described:
        length = row["length"]
        if length not in test["null"]["N2_segmentPermutation"]:
            continue
        row["pValues"] = {
            name: {
                "nonOverlapping": empirical_p(
                    per_length[length]["count"], row["nonOverlapping"]
                ),
                "ownerSupport": empirical_p(per_length[length]["owners"], row["ownerSupport"]),
            }
            for name, per_length in test["null"].items()
        }
        # The worst case across the three nulls is the one to report: a motif that survives only
        # the weakest null has not been shown to be more than an artefact of that null's blind
        # spot. No further multiplicity correction is applied, and none is owed — comparing
        # against the distribution of the family-wise *maximum* already adjusts for every motif of
        # that length. Applying Benjamini-Hochberg on top would correct twice.
        row["familywiseP"] = max(
            value for null in row["pValues"].values() for value in null.values()
        )
    tested = [row for row in described if "familywiseP" in row]
    result["motifs"] = described
    result["testedMotifCount"] = len(tested)
    result["significantMotifCount"] = sum(
        1 for row in tested if row["selfContained"] and row["familywiseP"] < 0.05
    )

    # Scheduler invariance and the sequence-versus-DAG gap. Windows containing a control transfer
    # are excluded: they cannot be `Seg` lemmas anyway, and the database reports no register
    # effects for `jalr`, so their dependence graph would rest on a guess.
    result["dag"] = {}
    for length in arguments.dag_lengths:
        sample = [
            [instructions[i] for i in indices[start : start + length]]
            for indices in segments
            for start in range(0, max(0, len(indices) - length + 1))
        ]
        sample = [
            window
            for window in sample
            if all(instruction.transfer == "ordinary" for instruction in window)
        ]
        forms = [dag_canonical_form(window) for window in sample]
        exact = [form for form in forms if not form.startswith("approx:")]
        result["dag"][str(length)] = {
            "windows": len(sample),
            "budgetExceeded": len(forms) - len(exact),
            "distinctSequences": len({tuple(alpha_rename(window)) for window in sample}),
            "distinctDagClasses": len(set(exact)),
            "invariance": validate_dag_invariance(
                sample[: arguments.dag_windows], rng, trials=4
            ),
        }

    result["controls"] = {
        "planted": planted_motif_control(instructions, segments, rng),
        "shuffledCorpus": shuffled_corpus_control(frame, test, lengths, rng),
    }
    if arguments.control_objdump and arguments.control_objdump.exists():
        result["controls"]["crossTarget"] = objdump_mnemonic_motifs(arguments.control_objdump)

    arguments.out_json.parent.mkdir(parents=True, exist_ok=True)
    arguments.out_json.write_text(json.dumps(result, indent=1, sort_keys=True) + "\n")
    if arguments.out_md:
        arguments.out_md.write_text(markdown(result))
    return 0


def markdown(result: dict) -> str:
    lines = ["# Binary motif analysis", ""]
    scope = result["scope"]
    lines += [
        f"Corpus: {result['corpus']['instructions']} owned instructions in "
        f"{result['corpus']['segments']} straight-line segments across "
        f"{result['corpus']['owners']} function instances.",
        "",
        f"Declared-region addresses {scope['declaredRegionAddresses']}, of which "
        f"{scope['unownedInDeclaredRegions']} are unowned; "
        f"objdump `.text` has {scope.get('objdumpTextInstructions', 'n/a')}.",
        "",
        "## Motifs that could be one `Seg` lemma",
        "",
        "| n | occurrences | non-overlapping | owners | FWER p | gross lines | motif |",
        "|---|---|---|---|---|---|---|",
    ]
    usable = [row for row in result["motifs"] if row["selfContained"]]
    for row in usable[:40]:
        lines.append(
            f"| {row['length']} | {row['rawCount']} | {row['nonOverlapping']} | "
            f"{row['ownerSupport']} | {row.get('familywiseP', float('nan')):.4f} | "
            f"{row['payoff']['grossLinesSaved']} | `{' '.join(row['motif'])[:80]}` |"
        )
    lines += ["", f"{len(usable)} of {len(result['motifs'])} closed motifs are self-contained.", ""]

    lines += ["## Disqualified, by reason", ""]
    reasons = collections.Counter(
        row["disqualification"] for row in result["motifs"] if not row["selfContained"]
    )
    for reason, count in reasons.most_common():
        lines.append(f"- {count}: {reason}")

    control = result["controls"]["shuffledCorpus"]
    planted = result["controls"]["planted"]
    lines += [
        "",
        "## Controls",
        "",
        f"- Shuffled corpus: {control['significantLengths']} of {control['lengthsTested']} "
        "lengths significant at 0.05 (a working test reports approximately none).",
        f"- Planted motif: length {planted['plantedLength']}, planted "
        f"{planted['plantedCount']}, recovered {planted['recoveredCount']}.",
    ]
    for length, row in sorted(result["dag"].items(), key=lambda item: int(item[0])):
        lines.append(
            f"- Scheduler invariance n={length}: {row['invariance']['failures']} failures in "
            f"{row['invariance']['reschedulesTried']} re-schedulings, against "
            f"{row['invariance']['orderDependentControlFailures']} for the order-dependent "
            f"control."
        )
    lines += ["", "## Sequence versus dependence-graph classes", "",
              "| n | windows | distinct sequences | distinct DAG classes | budget exceeded |",
              "|---|---|---|---|---|"]
    for length, row in sorted(result["dag"].items(), key=lambda item: int(item[0])):
        lines.append(
            f"| {length} | {row['windows']} | {row['distinctSequences']} | "
            f"{row['distinctDagClasses']} | {row['budgetExceeded']} |"
        )
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    sys.exit(main())
