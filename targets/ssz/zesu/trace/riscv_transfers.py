#!/usr/bin/env python3
"""Row C: the ONE definition of "is this control transfer direct or dynamic", shared by every
validator script that reads the production disassembly.

Why this module exists
----------------------

`objdump` prints a resolved-target comment on some `jalr`/`jr` instructions. That comment is a *hint*,
not a classification: for a bare `jalr a5` — a genuine indirect call through a register — objdump still
prints `# 10000 <main-0xe8>`, because it renders the instruction as `jalr 0(a5)` and symbolizes the
zero. Treating "has a `#` comment" as "is a direct call" therefore misclassifies real indirect calls as
resolved ones. Two Row C scripts did exactly that and disagreed with the extractor as a result.

The extractor (`tools/generate_elfling_program.py:classify`) gets it right, and mirrors Sail's
`DecodedWord.controlTransfer`: a `jr`/`jalr` is direct only when the IMMEDIATELY PRECEDING instruction
is an `auipc` writing the very base register the transfer uses — the `auipc`+`jalr` long-range direct
call pair the linker emits. Anything else is dynamic. This module is that rule, written once, so the
validators cannot drift from the generated data they are supposed to be checking.
"""
from __future__ import annotations

import re
import subprocess

COND = {"beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "bgez", "blez", "bgtz", "bltz",
        "bgt", "ble", "bgtu", "bleu"}
RET = {"ret", "mret", "sret"}


def disassemble(objdump: str, elf: str):
    """pc -> (mnemonic, operand string with <sym+off> stripped, resolved-comment target or None),
    plus the ordered pc list."""
    out = subprocess.run([objdump, "-d", "--no-show-raw-insn", elf],
                         capture_output=True, text=True, check=True).stdout
    insns, order = {}, []
    for ln in out.splitlines():
        m = re.match(r"\s*([0-9a-f]+):\s+(\S+)\s*([^#]*)(#.*)?$", ln)
        if not m:
            continue
        pc = int(m.group(1), 16)
        ops = re.sub(r"<[^>]*>", "", m.group(3)).strip().rstrip(",")
        comment = None
        if m.group(4):
            c = re.search(r"#\s*([0-9a-f]+)", m.group(4))
            if c:
                comment = int(c.group(1), 16)
        insns[pc] = (m.group(2), ops, comment)
        order.append(pc)
    return insns, order


def base_register(mnem: str, ops: str):
    """The register a `jr`/`jalr` transfers through, or None."""
    if mnem == "jr":
        m = re.search(r"\b([a-z][a-z0-9.]*)\b", ops)
        return m.group(1) if m else None
    m = re.match(r"\s*(?:([a-z][a-z0-9]*)\s*,\s*)?(-?\d+)?\(([a-z][a-z0-9]*)\)", ops)
    if m:
        return m.group(3)
    m2 = re.match(r"\s*([a-z][a-z0-9]*)\s*,\s*([a-z][a-z0-9]*)\s*$", ops)   # jalr rd, rs
    if m2:
        return m2.group(2)
    return ops.strip() or None                                              # jalr rs


def resolved_target(pc: int, insns):
    """The DIRECT target of a `jr`/`jalr` at `pc`, or None if the transfer is dynamic.

    Direct exactly when the preceding instruction is an `auipc` writing this transfer's base register
    AND objdump resolved a target — the `auipc`+`jalr` pair. A bare `jalr rs` is never direct, whatever
    comment objdump printed for it."""
    mnem, ops, comment = insns[pc]
    if mnem not in ("jr", "jalr") or comment is None:
        return None
    src = base_register(mnem, ops)
    prev = insns.get(pc - 4)
    if prev is None or prev[0] != "auipc" or src is None:
        return None
    return comment if prev[1].split(",")[0].strip() == src else None


def is_dynamic_transfer(pc: int, insns) -> bool:
    """True when the instruction's control transfer target is NOT statically known: `ret`-family
    returns and unresolved indirect `jr`/`jalr`. The generator models these as `exits`, never as
    declared `edges`, so the validators must route them to the exit check."""
    mnem, _, _ = insns[pc]
    if mnem in RET:
        return True
    if mnem in ("jr", "jalr"):
        return resolved_target(pc, insns) is None
    return False


def dynamic_transfer_pcs(objdump: str, elf: str) -> set:
    insns, order = disassemble(objdump, elf)
    return {pc for pc in order if is_dynamic_transfer(pc, insns)}


def is_call(pc: int, insns) -> bool:
    """True when the transfer at `pc` is a CALL — it links a return address, so control comes back to
    `pc + 4`. `j` / `jr` / `ret` link to `zero` and never return here.

    Leaving an occurrence's regions by a call is not the end of the occurrence's dynamic extent: the
    callee's effects (an allocation, for one) belong to the invocation that made the call."""
    mnem, ops, _ = insns[pc]
    if mnem == "jal":
        return True                       # objdump renders `jal zero,target` as `j`
    if mnem != "jalr":
        return False
    m = re.match(r"\s*(?:([a-z][a-z0-9]*)\s*,\s*)?(-?\d+)?\(([a-z][a-z0-9]*)\)", ops)
    if m:
        rd = m.group(1) or "ra"
    else:
        m2 = re.match(r"\s*([a-z][a-z0-9]*)\s*,\s*([a-z][a-z0-9]*)\s*$", ops)   # jalr rd, rs
        rd = m2.group(1) if m2 else "ra"                                        # bare `jalr rs`
    return rd not in ("zero", "x0")


def call_pcs(objdump: str, elf: str) -> set:
    insns, order = disassemble(objdump, elf)
    return {pc for pc in order if is_call(pc, insns)}
