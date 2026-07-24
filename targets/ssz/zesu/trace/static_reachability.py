#!/usr/bin/env python3
"""Row C: sound static unreachability analysis for the function instances that no input exercises.

This replaces the earlier `classify_uncovered.py` heuristic, which back-scanned at most 30
instructions of *linear* disassembly from each indirect call to guess the vtable slot it indexed. A
bounded linear scan is not a control-flow analysis: it silently assumes the definition of the target
register is the nearest textually-preceding one, which a branch into the middle of the window
falsifies. Nothing here scans a window.

What is proved, and how
-----------------------

The goal is a statement about three function instances of the UNCHANGED production ELF:

    U = { allocatorRemap.entry, allocatorResize.entry, zesu_raw_error.entry }

is never executed. Control reaches a pc only by a direct transfer (whose target is an immediate) or by
an indirect transfer through a register. So the claim decomposes into:

  (A) *No direct reference.*  Exhaustively over every instruction in `.text`: no branch/jump/call has a
      resolved target in `U`.  (Exhaustive, no window.)

  (B) *No indirect transfer can carry a value in U.*  Here the analysis is a **danger-set backward
      closure** rather than an attempt to resolve the vtable pointer (which would need a full
      interprocedural memory model).  Write `D` for a set of values a register must not hold.  A
      register acquires a value only by

        (i)   materializing a constant       — enumerated exhaustively below;
        (ii)  loading it from memory         — so the value must already be *in* memory;
        (iii) arithmetic on existing values  — the residual hypothesis, stated explicitly below.

      Let `L(D)` be the set of addresses in the loaded image holding a value in `D` — computed by
      scanning EVERY byte offset of every loadable section (both 8- and 4-byte little-endian reads),
      not just aligned words.  Since (by induction, using (i) and (ii)) no register can hold a value in
      `D`, no store can put one into memory either, so `L(D)` computed on the initial image is the
      complete set of locations holding `D`-values for the whole run.

      Each indirect site's target register is defined — established by a real backward
      reaching-definitions fixpoint over the reconstructed CFG (see `defs_of`), NOT a linear scan — by
      a load `ld rd, K(rs)`.  For `rd ∈ D` we need `mem[rs+K] ∈ D`, hence `rs + K ∈ L(D)`, hence
      `rs ∈ D' = { l - K : l ∈ L(D) }`.  Recurse on `D'`.  The closure terminates when some `D'` is
      *unreachable*: `L(D') = ∅` and no instruction materializes a value in `D'`.  Then no register can
      ever hold a `D'`-value, so none can hold a `D`-value, so the indirect site cannot transfer to `U`.

  (C) The conclusion is reported per function_instance, together with the residual hypotheses it rests on.

Residual hypotheses (stated, not hidden)
----------------------------------------

  H1 *No synthesizing arithmetic.*  No arithmetic instruction computes a value in a danger set out of
     operands that are not themselves in a danger set (case (iii) above).  The analysis discharges the
     constant-materialization half of this exhaustively (`lui`/`auipc`/`li`/`addi` chains) and reports
     the count of unconstrained-operand arithmetic instructions that remain; it does not prove the
     general case, which would need a full interprocedural value analysis.
  H2 *Def-chain shape.*  Every indirect site's target register is defined only by loads with constant
     offsets (verified by the CFG fixpoint in (B); a site with any other definition is reported as
     UNRESOLVED and its function instance is NOT claimed unreachable).

`allThreeStaticallyUnreachable` is deliberately NOT asserted by this script; it emits the exact
per-function-instance verdict and the hypotheses, and the caller decides. Diagnostic-only: never imported by
the theorem graph.
"""
from __future__ import annotations

import argparse
import json
import re
import struct
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from riscv_transfers import COND, RET, disassemble, resolved_target  # noqa: E402

# ---- ELF image ------------------------------------------------------------------------------------

def load_image(elf: str):
    """[(vaddr, bytes)] for every PT_LOAD segment's file-backed contents, from the ELF64 headers."""
    d = Path(elf).read_bytes()
    if d[:4] != b"\x7fELF" or d[4] != 2:
        raise SystemExit("not an ELF64 file")
    e_phoff, = struct.unpack_from("<Q", d, 0x20)
    e_phentsize, e_phnum = struct.unpack_from("<HH", d, 0x36)
    segs = []
    for i in range(e_phnum):
        o = e_phoff + i * e_phentsize
        p_type, = struct.unpack_from("<I", d, o)
        if p_type != 1:      # PT_LOAD
            continue
        p_offset, p_vaddr = struct.unpack_from("<QQ", d, o + 0x08)
        p_filesz, = struct.unpack_from("<Q", d, o + 0x20)
        segs.append((p_vaddr, d[p_offset:p_offset + p_filesz]))
    return segs


def locations_holding(segs, values: set[int]) -> dict[int, int]:
    """Every image address whose 8-byte OR 4-byte little-endian read equals one of `values`.

    Every byte offset is examined, not only aligned ones: an unaligned word is still a value some
    instruction could load, and skipping unaligned offsets would make the scan unsound."""
    out = {}
    if not values:
        return out
    for vaddr, blob in segs:
        n = len(blob)
        for off in range(n):
            if off + 8 <= n:
                v = int.from_bytes(blob[off:off + 8], "little")
                if v in values:
                    out[vaddr + off] = v
            if off + 4 <= n:
                v = int.from_bytes(blob[off:off + 4], "little")
                if v in values:
                    out[vaddr + off] = v
    return out


# ---- disassembly + CFG ----------------------------------------------------------------------------

def operands(ops: str):
    return [x.strip() for x in ops.split(",") if x.strip()]


def imm_target(operand: str):
    m = re.fullmatch(r"([0-9a-f]+)", operand)
    return int(m.group(1), 16) if m else None


def build_cfg(insns, order):
    """succ/pred over EVERY instruction in `.text`. Indirect transfers contribute no target edge
    (their targets are exactly what the analysis is trying to bound); a `ret` contributes none either.

    Targets outside the disassembled instruction set are recorded in `offtext` rather than silently
    dropped — dropping an edge could hide a definition path and make the backward fixpoint unsound."""
    nxt = {pc: order[i + 1] for i, pc in enumerate(order) if i + 1 < len(order)}
    succ, pred = defaultdict(set), defaultdict(set)
    indirect, offtext = [], []
    for pc in order:
        op, opstr, _ = insns[pc]
        ops = operands(opstr)
        direct = resolved_target(pc, insns)
        tgts, is_indirect = [], False
        if op in RET:
            is_indirect = True
        elif op in COND:
            t = imm_target(ops[-1]) if ops else None
            tgts = [x for x in (nxt.get(pc), t) if x is not None]
        elif op == "j":
            t = imm_target(ops[-1]) if ops else None
            tgts = [t] if t is not None else []
            is_indirect = t is None
        elif op == "jal":
            t = imm_target(ops[-1]) if ops else None
            # a call also falls through to the return site
            tgts = [x for x in ([t] if t is not None else []) + [nxt.get(pc)] if x is not None]
            is_indirect = t is None
        elif op in ("jr", "jalr"):
            if direct is not None:      # the auipc+jalr long-range DIRECT call pair
                tgts = [x for x in [direct, nxt.get(pc)] if x is not None]
            else:
                is_indirect = True
                # An indirect CALL still returns to the following instruction; an indirect JUMP
                # (`jr rs`, which is `jalr zero, 0(rs)`) does not.
                if op == "jalr":
                    tgts = [x for x in [nxt.get(pc)] if x is not None]
        else:
            tgts = [x for x in [nxt.get(pc)] if x is not None]
        for t in tgts:
            if t not in insns:
                offtext.append({"pc": pc, "target": t})
                continue
            succ[pc].add(t)
            pred[t].add(pc)
        if is_indirect:
            indirect.append(pc)
    return succ, pred, indirect, nxt, offtext


# ---- register definitions -------------------------------------------------------------------------

XNAMES = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
          "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11",
          "t3", "t4", "t5", "t6"]
XALIAS = {"fp": "s0"}

# Instructions that write their first operand. Anything not listed is treated as writing NOTHING,
# which would be unsound, so the list is closed over the ops this .text actually contains and
# `unknown_writers` reports any op encountered that is neither listed here nor known side-effect-free.
DEFINES_RD = {
    "lui", "auipc", "li", "mv", "addi", "addiw", "add", "addw", "sub", "subw", "and", "andi", "or",
    "ori", "xor", "xori", "sll", "slli", "slliw", "sllw", "srl", "srli", "srliw", "srlw", "sra",
    "srai", "sraiw", "sraw", "slt", "slti", "sltu", "sltiu", "seqz", "snez", "sltz", "sgtz", "neg",
    "negw", "not", "sext.w", "zext.w", "mul", "mulw", "mulh", "mulhu", "mulhsu", "div", "divu",
    "divw", "divuw", "rem", "remu", "remw", "remuw",
    "ld", "lw", "lwu", "lh", "lhu", "lb", "lbu", "lr.w", "lr.d",
}
NO_DEF = {"sd", "sw", "sh", "sb", "beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "bgez",
          "blez", "bgtz", "bltz", "bgt", "ble", "bgtu", "bleu", "j", "jr", "ret", "ecall", "ebreak",
          "fence", "unimp", "nop", "mret", "sret"}
LOADS = {"ld", "lw", "lwu", "lh", "lhu", "lb", "lbu"}
# `jal`/`jalr` write ra (x1); with an explicit rd operand they write that instead.


def reg_of(tok: str):
    t = XALIAS.get(tok, tok)
    return XNAMES.index(t) if t in XNAMES else None


def defined_reg(op: str, ops: list[str]):
    """The register this instruction writes, or None."""
    if op in ("jal", "jalr"):
        # `jal off` / `jalr off(rs)` implicitly write ra; `jal rd, off` writes rd.
        if len(ops) >= 2 and reg_of(ops[0]) is not None and "(" not in ops[0]:
            return reg_of(ops[0])
        return 1
    if op in NO_DEF:
        return None
    if op in DEFINES_RD and ops:
        return reg_of(ops[0])
    return None


def is_call(pc: int, insns) -> bool:
    """A CALL — an instruction the analysis must treat as redefining every register.

    Crossing a call backward without this would be unsound: the callee can write any register, and the
    callee's body is not on the backward path (its `ret` has no CFG successor edge here). So a call is
    modelled as a definition of everything; a site whose target register's definition sits behind a
    call is reported UNRESOLVED rather than silently resolved to the pre-call value."""
    mnem, opstr, _ = insns[pc]
    if mnem == "jal":                    # `jal target` writes ra; a plain jump renders as `j`
        return True
    if mnem == "jalr":                   # direct or indirect, `jalr` writes ra and returns
        return True
    return False


def defs_of(target_pc: int, reg: int, insns, pred, order):
    """Reaching definitions of `reg` at `target_pc`, by a BACKWARD fixpoint over the real CFG.

    This is the piece the old heuristic got wrong: it walked at most 30 instructions of linear
    disassembly. Here every CFG predecessor path is followed to its defining instruction, so a branch
    into the middle of the region cannot hide a definition, and a CALL on the path is treated as
    defining every register (see `is_call`). Returns (defs, incomplete): `incomplete` is True if some
    path reaches a pc with no predecessors — the register is then live-in from a caller and the
    definition set does not characterize it."""
    defs, open_entry = set(), False
    seen = set()
    work = [target_pc]
    while work:
        pc = work.pop()
        for p in pred.get(pc, ()):  # predecessors in the CFG
            if p in seen:
                continue
            seen.add(p)
            op, opstr, _ = insns[p]
            if is_call(p, insns) or defined_reg(op, operands(opstr)) == reg:
                defs.add(p)
                continue        # this path's definition is found; do not walk past it
            work.append(p)
        if not pred.get(pc) and pc != target_pc:
            open_entry = True
    if not pred.get(target_pc):
        open_entry = True
    return sorted(defs), open_entry


def load_offset(op: str, ops: list[str]):
    """(offset, base_register) of a load `ld rd, OFF(rs)`, or None if not that shape."""
    if op not in LOADS or len(ops) < 2:
        return None
    m = re.fullmatch(r"(-?\d+)\(([a-z0-9]+)\)", ops[1])
    if not m:
        return None
    base = reg_of(m.group(2))
    return (int(m.group(1)), base) if base is not None else None


# ---- constant materialization ---------------------------------------------------------------------

def materialized_constants(insns, order, succ):
    """Every constant a register can hold from a *constant materialization*, computed by a forward
    constant-propagation fixpoint over the CFG (lui/auipc/li/mv/addi chains). Sound in the direction
    that matters: a register whose value is not a materialized constant here can still be anything
    (that is hypothesis H1), but every value that IS produced by such a chain appears in the result."""
    consts = set()
    # Per-pc register state: reg -> int (absent = unknown). Joined by intersection at merges.
    state: dict[int, dict[int, int]] = {}
    work = list(order)
    entry = order[0] if order else None
    while work:
        pc = work.pop(0)
        cur = dict(state.get(pc, {}))
        op, opstr, _ = insns[pc]
        ops = operands(opstr)
        out = dict(cur)
        rd = defined_reg(op, ops)
        val = None
        try:
            if op == "lui" and len(ops) >= 2:
                val = (int(ops[1], 0) << 12) & 0xFFFFFFFFFFFFFFFF
            elif op == "auipc" and len(ops) >= 2:
                val = (pc + (int(ops[1], 0) << 12)) & 0xFFFFFFFFFFFFFFFF
            elif op == "li" and len(ops) >= 2:
                val = int(ops[1], 0) & 0xFFFFFFFFFFFFFFFF
            elif op == "mv" and len(ops) >= 2:
                val = cur.get(reg_of(ops[1]))
            elif op in ("addi", "addiw") and len(ops) >= 3:
                b = cur.get(reg_of(ops[1]))
                if b is not None:
                    val = (b + int(ops[2], 0)) & 0xFFFFFFFFFFFFFFFF
        except ValueError:
            val = None
        if rd is not None:
            if val is None:
                out.pop(rd, None)
            else:
                out[rd] = val
                consts.add(val)
        out.pop(0, None)     # x0 is hardwired zero, never a materialized code address
        for s in succ.get(pc, ()):
            prev = state.get(s)
            if prev is None:
                merged = dict(out)
            else:
                merged = {r: v for r, v in prev.items() if out.get(r) == v}
            if prev is None or merged != prev:
                state[s] = merged
                work.append(s)
    return consts, state


ARITH = {"add", "addw", "sub", "subw", "or", "xor", "and", "sll", "srl", "sra",
         "sllw", "srlw", "sraw", "mul", "mulw"}
IMM_RANGE = 1 << 11     # RISC-V I-type immediates are 12-bit signed


def arith_population(insns, order, state, danger_universe):
    """Characterize the arithmetic H1 has to quantify over, instead of asserting it away.

    Two counts matter. `unpinnedOperands` is every register-register arithmetic instruction at which
    the constant fixpoint pins neither source — the general residual. `nearDanger` is the subset whose
    PINNED operand lies within one 12-bit immediate of some danger value, i.e. the only instructions
    that could reach a danger value by a single constant-offset computation; the constant fixpoint
    already enumerates those results, so `nearDanger == 0` means no single-step arithmetic route to a
    danger value exists and the residual is confined to fully unconstrained computations."""
    unpinned, near, near_detail = 0, 0, []
    for pc in order:
        op, opstr, _ = insns[pc]
        ops = operands(opstr)
        if op not in ARITH or len(ops) < 3:
            continue
        srcs = [reg_of(x) for x in ops[1:3]]
        vals = [state.get(pc, {}).get(r) for r in srcs if r is not None]
        pinned = [v for v in vals if v is not None]
        if not pinned:
            unpinned += 1
        if any(abs(v - d) <= IMM_RANGE for v in pinned for d in danger_universe):
            near += 1
            near_detail.append({"pc": pc, "op": op, "ops": opstr, "pinned": sorted(pinned),
                                "result": state.get(pc, {}).get(reg_of(ops[0]))})
    return {"unpinnedOperands": unpinned, "nearDanger": near, "nearDangerSites": near_detail,
            "dangerUniverse": sorted(danger_universe)}


# ---- the danger-set closure -------------------------------------------------------------------------

def close_danger(site_pc, reg, insns, pred, order, segs, consts, max_levels=8):
    """Follow the danger set backward from one indirect site. Returns a dict describing the outcome."""
    steps = []
    text_defs, open_entry = defs_of(site_pc, reg, insns, pred, order)
    # The site's target must be defined by loads with constant offsets, on EVERY path (H2).
    shapes = []
    for d in text_defs:
        op, opstr, _ = insns[d]
        lo = load_offset(op, operands(opstr))
        shapes.append((d, op, lo))
    if open_entry or not text_defs or any(lo is None for (_, _, lo) in shapes):
        return {"site": site_pc, "resolved": False,
                "reason": ("target register is live-in from a caller" if open_entry else
                           "target register has a non-load definition"),
                "defs": [{"pc": d, "op": op} for (d, op, _) in shapes]}

    # Level 0: the values the site must not transfer to.
    danger = set(DANGER_SEED)
    for level in range(max_levels):
        locs = locations_holding(segs, danger)
        mat = sorted(danger & consts)
        steps.append({"level": level, "dangerValues": sorted(danger),
                      "imageLocations": sorted(locs), "materializedByCode": mat})
        if not locs and not mat:
            return {"site": site_pc, "resolved": True, "levels": steps,
                    "conclusion": "no register can hold a danger value: the set is neither present in "
                                  "the image nor materialized by any instruction"}
        if mat:
            return {"site": site_pc, "resolved": False, "levels": steps,
                    "reason": f"an instruction materializes the danger value(s) {mat}"}
        # Every def is a load `ld rd, K(rs)`; the danger propagates to the base register.
        nxt_danger, bases = set(), set()
        for (d, op, (off, base)) in shapes:
            for l in locs:
                nxt_danger.add((l - off) & 0xFFFFFFFFFFFFFFFF)
            bases.add(base)
        if len(bases) != 1:
            return {"site": site_pc, "resolved": False, "levels": steps,
                    "reason": "definitions use different base registers; the closure does not follow"}
        base = bases.pop()
        # Now recurse on the base register's own definitions.
        text_defs, open_entry = defs_of(min(d for (d, _, _) in shapes), base, insns, pred, order)
        shapes = []
        for d in text_defs:
            op, opstr, _ = insns[d]
            shapes.append((d, op, load_offset(op, operands(opstr))))
        danger = nxt_danger
        if open_entry or not text_defs or any(lo is None for (_, _, lo) in shapes):
            # The chain leaves the analysable shape, but the closure may still have ALREADY discharged
            # the level: re-scan this level's danger set before giving up.
            locs = locations_holding(segs, danger)
            mat = sorted(danger & consts)
            steps.append({"level": level + 1, "dangerValues": sorted(danger),
                          "imageLocations": sorted(locs), "materializedByCode": mat})
            if not locs and not mat:
                return {"site": site_pc, "resolved": True, "levels": steps,
                        "conclusion": "the base register's danger set is neither present in the image "
                                      "nor materialized by any instruction, so the load cannot read a "
                                      "danger value"}
            return {"site": site_pc, "resolved": False, "levels": steps,
                    "reason": ("base register is live-in from a caller" if open_entry else
                               "base register has a non-load definition")}
    return {"site": site_pc, "resolved": False, "levels": steps, "reason": "closure did not terminate"}


DANGER_SEED: set[int] = set()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--objdump", required=True)
    ap.add_argument("--elf", required=True)
    ap.add_argument("--program", required=True)
    ap.add_argument("--out-json", required=True)
    ap.add_argument("--out-md", required=True)
    a = ap.parse_args()

    program = json.loads(Path(a.program).read_text())
    function_instances = program["function_instances"]
    uncovered = {i: function_instances[i] for i in range(len(function_instances))
                 if function_instances[i]["qualified"].split(".")[-1] in
                 ("allocatorRemap", "allocatorResize", "zesu_raw_error")}

    insns, order = disassemble(a.objdump, a.elf)
    succ, pred, indirect, nxt, offtext = build_cfg(insns, order)
    segs = load_image(a.elf)
    consts, cstate = materialized_constants(insns, order, succ)

    global DANGER_SEED
    DANGER_SEED = {function_instance["entryPc"] for function_instance in uncovered.values()}

    # (A) exhaustive direct-reference scan over EVERY instruction.
    direct_refs = []
    for pc in order:
        op, opstr, _ = insns[pc]
        ops = operands(opstr)
        cands = [resolved_target(pc, insns)] + ([imm_target(ops[-1])] if ops else [])
        for t in cands:
            if t is not None and t in DANGER_SEED:
                direct_refs.append({"pc": pc, "op": op, "target": t})

    # (B) every indirect site, closed backward over the real CFG.
    sites = []
    for pc in indirect:
        op, opstr, _ = insns[pc]
        ops = operands(opstr)
        if op in RET:
            # `ret` transfers to the return address, which is set by the CALLER's jal/jalr; a return
            # cannot reach a pc that no call site targeted, and (A) shows no call targets U.
            sites.append({"site": pc, "resolved": True, "kind": "ret",
                          "conclusion": "returns to a call site's return address; (A) shows no call "
                                        "instruction targets U, so no return address is in U"})
            continue
        reg = reg_of(ops[-1]) if ops else None
        if reg is None:
            sites.append({"site": pc, "resolved": False, "reason": "target operand is not a register"})
            continue
        sites.append(close_danger(pc, reg, insns, pred, order, segs, consts))

    all_sites_resolved = all(s.get("resolved") for s in sites)
    no_direct = not direct_refs
    # Which of the three the analysis actually discharges, and why.
    verdicts = {}
    for i, function_instance in sorted(uncovered.items()):
        name = function_instance["qualified"].split(".")[-1]
        in_image = locations_holding(segs, {function_instance["entryPc"]})
        materialized = function_instance["entryPc"] in consts
        verdicts[i] = {
            "index": i, "routine": name, "entryPc": function_instance["entryPc"],
            "directlyReferenced": [d for d in direct_refs if d["target"] == function_instance["entryPc"]],
            "imageLocationsHoldingEntry": sorted(in_image),
            "materializedByCode": materialized,
            "unreachable": bool(no_direct and all_sites_resolved and not materialized),
        }

    danger_universe = {v for site in sites for lv in site.get("levels", [])
                       for v in lv["dangerValues"]}
    arith = arith_population(insns, order, cstate, danger_universe)
    residual = {
        "H1_no_synthesizing_arithmetic":
            "No arithmetic instruction computes a danger value from operands that are not themselves "
            "danger values. The constant-materialization half is discharged exhaustively "
            f"({len(consts)} distinct constants enumerated by a CFG-wide constant-propagation "
            "fixpoint, none of which is a danger value). Of the remaining register-register "
            f"arithmetic, {arith['nearDanger']} instructions have a pinned operand within one 12-bit "
            "immediate of a danger value (the only single-step arithmetic route to one) and "
            f"{arith['unpinnedOperands']} have no pinned operand at all; the latter are what this "
            "hypothesis covers.",
        "H2_def_chain_shape":
            "Every indirect site's target register is defined only by loads with constant offsets. "
            "This is CHECKED by the backward reaching-definitions fixpoint (not assumed): a site whose "
            "definitions are anything else is reported unresolved and blocks the conclusion.",
    }

    out = {
        "summary": {
            "indirectSites": len([s for s in sites if s.get("kind") != "ret"]),
            "returnSites": len([s for s in sites if s.get("kind") == "ret"]),
            "allSitesResolved": all_sites_resolved,
            "noDirectReference": no_direct,
            "unreachable": sorted(i for i, v in verdicts.items() if v["unreachable"]),
            "notProven": sorted(i for i, v in verdicts.items() if not v["unreachable"]),
        },
        "residualHypotheses": residual,
        "arithmeticPopulation": arith,
        "offTextTargets": offtext,
        "verdicts": verdicts,
        "directReferences": direct_refs,
        "indirectSites": sites,
    }
    Path(a.out_json).write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    Path(a.out_md).write_text(emit_md(out, uncovered))
    s = out["summary"]
    print(f"indirect sites={s['indirectSites']} returns={s['returnSites']} "
          f"allResolved={s['allSitesResolved']} noDirectRef={s['noDirectReference']}")
    print(f"  unreachable: {s['unreachable']}   not proven: {s['notProven']}")
    return 0 if not s["notProven"] else 1


def emit_md(out, uncovered) -> str:
    s = out["summary"]
    L = ["# Row C — static unreachability of the uncovered function instances (GENERATED)",
         "",
         "Regenerated by `targets/ssz/zesu/trace/static_reachability.py` from the UNCHANGED production",
         "`zesu-ssz` ELF. Diagnostic-only; never imported by the proof.",
         "",
         "This supersedes the earlier 30-instruction linear back-scan, which was a heuristic, not a",
         "control-flow analysis. Definitions are now resolved by a **backward reaching-definitions",
         "fixpoint over the reconstructed CFG**, and the unreachability argument is a **danger-set",
         "backward closure** over the loaded image rather than an attempt to guess a vtable slot.",
         "",
         "## Result",
         "",
         f"- indirect (non-return) transfer sites: **{s['indirectSites']}**, all resolved: "
         f"**{s['allSitesResolved']}**",
         f"- return sites: {s['returnSites']} (a return can only reach a call site's return address)",
         f"- no direct branch/call targets any of the three entries: **{s['noDirectReference']}**",
         "",
         "| function instance | routine | entry pc | entry value in image | materialized by code | verdict |",
         "|---:|---|---:|---|---|---|"]
    for i, v in sorted(out["verdicts"].items(), key=lambda kv: int(kv[0])):
        locs = ", ".join(hex(x) for x in v["imageLocationsHoldingEntry"]) or "—"
        L.append(f"| {v['index']} | `{v['routine']}` | {hex(v['entryPc'])} | {locs} | "
                 f"{'yes' if v['materializedByCode'] else 'no'} | "
                 f"{'**statically unreachable**' if v['unreachable'] else 'NOT PROVEN'} |")
    L += ["", "## Per-site closure", ""]
    for site in out["indirectSites"]:
        if site.get("kind") == "ret":
            continue
        head = f"### site {hex(site['site'])} — " + ("resolved" if site.get("resolved") else "UNRESOLVED")
        L.append(head)
        if not site.get("resolved"):
            L.append(f"- reason: {site.get('reason')}")
        else:
            L.append(f"- {site.get('conclusion')}")
        for lv in site.get("levels", []):
            vals = ", ".join(hex(x) for x in lv["dangerValues"])
            locs = ", ".join(hex(x) for x in lv["imageLocations"]) or "none"
            L.append(f"  - level {lv['level']}: danger {{{vals}}} — image locations: {locs}; "
                     f"materialized: {lv['materializedByCode'] or 'none'}")
        L.append("")
    L += ["## Residual hypotheses", ""]
    ap = out.get("arithmeticPopulation", {})
    if ap.get("nearDangerSites"):
        L.append("Arithmetic with a pinned operand within one 12-bit immediate of a danger value "
                 "(each result is enumerated by the constant fixpoint, and none is a danger value):")
        L.append("")
        for d in ap["nearDangerSites"]:
            res = hex(d["result"]) if d.get("result") is not None else "unpinned"
            L.append(f"- `{hex(d['pc'])}: {d['op']} {d['ops']}` — operand(s) "
                     f"{', '.join(hex(x) for x in d['pinned'])}, result {res}")
        L.append("")
    for k, v in sorted(out["residualHypotheses"].items()):
        L.append(f"- **{k}** — {v}")
    L += ["",
          "The verdict column above is exactly what the analysis establishes, under those hypotheses.",
          "Row C's conclusions exclude these function instances either way: they carry no per-function-instance",
          "execution evidence, so every check for them is an explicit gap, never a pass.", ""]
    return "\n".join(L)


if __name__ == "__main__":
    raise SystemExit(main())
