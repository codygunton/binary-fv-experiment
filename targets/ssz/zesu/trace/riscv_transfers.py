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
TERMINAL = {"ecall", "ebreak", "mret", "sret", "wfi", "unimp"}


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


def jalr_fields(mnem: str, ops: str):
    """(rd, imm, rs) for a `jr`/`jalr` as objdump renders it, decoded exactly once.

    `jr rs` is `jalr zero, 0(rs)`; a bare `jalr rs` is `jalr ra, 0(rs)`. Mirrors the extractor's
    decode in `tools/generate_elfling_program.py:classify`, which is what decides call vs jump vs
    return — and therefore what decides the exits."""
    if mnem == "jr":
        m = re.search(r"\b([a-z][a-z0-9.]*)\b", ops)
        return "zero", 0, (m.group(1) if m else None)
    m = re.match(r"\s*(?:([a-z][a-z0-9]*)\s*,\s*)?(-?\d+)?\(([a-z][a-z0-9]*)\)", ops)
    if m:
        return (m.group(1) or "ra"), int(m.group(2) or "0"), m.group(3)
    m2 = re.match(r"\s*([a-z][a-z0-9]*)\s*,\s*([a-z][a-z0-9]*)\s*$", ops)   # jalr rd, rs
    if m2:
        return m2.group(1), 0, m2.group(2)
    return "ra", 0, (ops.strip() or None)                                   # jalr rs


def base_register(mnem: str, ops: str):
    """The register a `jr`/`jalr` transfers through, or None."""
    return jalr_fields(mnem, ops)[2]


def direct_target(ops: str):
    """The absolute target objdump printed as the last operand of a branch/jump, or None.

    `disassemble` has already stripped the trailing `<symbol+offset>`, so `bnez a5,11bb8` arrives as
    `a5,11bb8`. This is the same target the extractor's `_operand_target` reads off the unstripped
    text."""
    parts = [p.strip() for p in ops.split(",")]
    return int(parts[-1], 16) if parts and re.fullmatch(r"[0-9a-f]+", parts[-1]) else None


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

    Leaving a function instance's regions by a call is not the end of the function instance's dynamic extent: the
    callee's effects (an allocation, for one) belong to the invocation that made the call."""
    mnem, ops, _ = insns[pc]
    if mnem == "jal":
        return True                       # objdump renders `jal zero,target` as `j`
    if mnem != "jalr":
        return False
    return jalr_fields(mnem, ops)[0] not in ("zero", "x0")


def call_pcs(objdump: str, elf: str) -> set:
    insns, order = disassemble(objdump, elf)
    return {pc for pc in order if is_call(pc, insns)}


def continuations(pc: int, insns, next_addr: int | None = None):
    """`(departs_unconditionally, continuation_addresses)` for the transfer at `pc` — the ONE static
    exit rule, written here so the validators cannot each grow their own.

    A CONTINUATION is an address control reaches AND STAYS AT. It is deliberately NOT the direct
    successor set the EDGE rule uses, and the difference is the whole point: a resolved CALL's direct
    successors are `[callee, pc + 4]` but its only continuation is `pc + 4`, because control comes
    back. Counting the callee edge here makes EVERY call site an exit of its caller, which is what
    made the entry function instance's `FunctionTrace` (it carries `¬ exit pc`) halt at its first call.
    So a call leaves its function instance only in TAIL position — when its own fall-through is outside.

    Mirrors `tools/generate_elfling_program.py:compute_function_instance_cfg` and Lean's
    `GeneratedProgramCfg.exitContinuations` / `leavesFunctionInstance` case for case, including the
    two that have NO continuation at all (an unresolved indirect jump and an unresolved indirect
    call): the generator declares neither an exit, because neither has a decoded target to test."""
    mnem, ops, _ = insns[pc]
    nxt = pc + 4 if next_addr is None else next_addr
    if mnem == "ret" or mnem in TERMINAL:
        return True, []
    if mnem in COND:
        t = direct_target(ops)
        return False, ([nxt, t] if t is not None else [nxt])
    if mnem == "j":
        t = direct_target(ops)
        return False, ([t] if t is not None else [])
    if mnem == "jal":                                    # `jal ra,target`: control comes back
        return False, [nxt]
    if mnem in ("jr", "jalr"):
        rd, imm, _rs = jalr_fields(mnem, ops)
        resolved = resolved_target(pc, insns)
        if rd in ("zero", "x0"):
            if resolved is not None:
                return False, [resolved]                 # auipc+jr: a resolved TAIL jump
            if imm == 0:
                return True, []                          # `jr rs` — Sail models it as `.return_`
            return False, []                             # unresolved indirect jump: no known target
        return (False, [nxt]) if resolved is not None else (False, [])
    return False, [nxt]                                  # plain fall-through


def leaves_region(pc: int, insns, in_region, next_addr: int | None = None) -> bool:
    """The transfer at `pc` takes control OUT of the region `in_region` describes: it returns or
    terminates, or one of its CONTINUATIONS lands outside. Exactly the extractor's `exits` rule."""
    departs, conts = continuations(pc, insns, next_addr)
    return departs or any(not in_region(t) for t in conts)
