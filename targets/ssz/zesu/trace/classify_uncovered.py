#!/usr/bin/env python3
"""Row C: mechanically classify the occurrences that no input dynamically exercises, using STATIC CFG
analysis of the UNCHANGED production `zesu-ssz` ELF disassembly — never "N test runs missed it".

For the three uncovered occurrences it establishes, from the binary alone, WHY they are unreachable in
this executable's control flow:

  allocatorResize / allocatorRemap
      Their addresses appear only as function pointers in the std.mem.Allocator VTable (four consecutive
      slots: alloc, resize, remap, free). A slot is invoked by `ld Fn, OFF(vtable); jalr Fn`. This scans
      every indirect (bare-`jalr`) call site and reports which vtable offsets are ever indexed. If the
      resize (+8) / remap (+16) slots are never indexed and no direct `jal` targets the functions, they
      are provably never invoked — the bump allocator makes exact-size allocations and never grows.

  zesu_raw_error
      An exported raw-ABI getter. This confirms no `jal`/`jalr`/data pointer anywhere in the binary
      references its entry, i.e. the `_start` harness never calls it (it discriminates success/failure
      via `zesu_raw_result`'s null return). Sealed executable: no ABI surface to invoke it without
      relinking (forbidden).

The verification is reproducible (objdump on the pinned ELF) and deterministic. It emits a JSON and a
markdown classification. Diagnostic-only; never imported by the proof.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path

# vtable layout offsets -> std.mem.Allocator method
VTABLE_SLOTS = {0: "alloc", 8: "resize", 16: "remap", 24: "free"}


def disassemble(objdump: str, elf: str) -> list[tuple[int, str, str]]:
    out = subprocess.run([objdump, "-d", "--no-show-raw-insn", elf],
                         capture_output=True, text=True, check=True).stdout
    insns = []
    for ln in out.splitlines():
        m = re.match(r"\s*([0-9a-f]+):\s+(\S+)\s*([^#]*)", ln)
        if m:
            insns.append((int(m.group(1), 16), m.group(2), m.group(3).strip().rstrip(",")))
    return insns


def data_words(objdump: str, elf: str) -> dict[int, int]:
    """Map every 8-byte-aligned data address to its little-endian 64-bit word (for vtable pointers)."""
    out = subprocess.run([objdump, "-s", elf], capture_output=True, text=True, check=True).stdout
    words = {}
    # Each content line: " <addr>  <=4 groups of exactly 8 hex digits>  <ascii>"
    line_re = re.compile(r"^\s*([0-9a-f]+)\s+((?:[0-9a-f]{8}\s+){1,4})")
    for ln in out.splitlines():
        m = line_re.match(ln)
        if not m:
            continue
        base = int(m.group(1), 16)
        bs = bytes.fromhex("".join(m.group(2).split()))
        for off in range(0, len(bs) - 7, 4):
            words[base + off] = int.from_bytes(bs[off:off + 8], "little")
    return words


def _def_reg(op: str, ops: str):
    if op in ("sd", "sw", "sh", "sb", "beq", "bne", "blt", "bge", "bltu", "bgeu",
              "beqz", "bnez", "j", "jr", "ret", "fence", "ecall"):
        return None
    m = re.match(r"([a-z][a-z0-9]+)", ops)
    return m.group(1) if m else None


def indirect_slot_offsets(insns) -> dict[int, list[str]]:
    """For each bare `jalr RD` (indirect call through a register), find the nearest prior load defining
    RD and record its offset — the vtable slot being called. `jalr N(base)` with N!=0 is a resolved
    direct call, not a slot dispatch, and is ignored."""
    offsets: dict[int, list[str]] = {}
    for i, (a, op, ops) in enumerate(insns):
        if op != "jalr":
            continue
        m = re.match(r"(?:[a-z0-9]+,)?(-?\d+)\((\w+)\)$", ops)
        if m:
            if int(m.group(1)) != 0:
                continue
            tgt = m.group(2)
        else:
            tgt = ops.strip().split(",")[-1].strip()
        for j in range(i - 1, max(i - 30, -1), -1):
            aj, opj, opsj = insns[j]
            if _def_reg(opj, opsj) == tgt:
                m2 = re.match(r"[a-z0-9]+,\s*(-?\d+)\((\w+)\)", opsj)
                if opj == "ld" and m2:
                    offsets.setdefault(int(m2.group(1)), []).append(hex(a))
                break
    return offsets


def references_to(insns, words, addr: int) -> dict:
    """All ways `addr` is referenced: as a resolved call/branch target (objdump '# <addr>' comment or
    literal), or as a stored data pointer."""
    hexaddr = format(addr, "x")
    call_sites = [hex(a) for (a, op, ops) in insns
                  if op in ("jal", "jalr", "j", "call") and re.search(rf"\b{hexaddr}\b", ops)]
    data_ptrs = [hex(k) for k, v in words.items() if v == addr]
    return {"callSites": call_sites, "dataPointers": data_ptrs}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--objdump", required=True)
    ap.add_argument("--elf", required=True)
    ap.add_argument("--program", required=True)
    ap.add_argument("--out-json", required=True)
    ap.add_argument("--out-md", required=True)
    a = ap.parse_args()

    occ = json.loads(Path(a.program).read_text())["occurrences"]
    by_short = {}
    for i, o in enumerate(occ):
        by_short.setdefault(o["qualified"].split(".")[-1], []).append(i)

    insns = disassemble(a.objdump, a.elf)
    words = data_words(a.objdump, a.elf)
    slot_offsets = indirect_slot_offsets(insns)

    def entry(short):
        return occ[by_short[short][0]]["entryPc"]

    resize_pc, remap_pc, error_pc = entry("allocatorResize"), entry("allocatorRemap"), entry("zesu_raw_error")
    # Which vtable base holds these slots? Find the 4 consecutive pointers {alloc,resize,remap,free}.
    alloc_pc, free_pc = entry("allocatorAlloc"), entry("allocatorFree")
    vtable_base = None
    for k, v in words.items():
        if v == alloc_pc and words.get(k + 8) == resize_pc and words.get(k + 16) == remap_pc \
                and words.get(k + 24) == free_pc:
            vtable_base = k
            break

    resize_refs = references_to(insns, words, resize_pc)
    remap_refs = references_to(insns, words, remap_pc)
    error_refs = references_to(insns, words, error_pc)

    indexed = sorted(slot_offsets)
    resize_invocable = 8 in slot_offsets or bool(resize_refs["callSites"])
    remap_invocable = 16 in slot_offsets or bool(remap_refs["callSites"])
    error_invocable = bool(error_refs["callSites"]) or bool(error_refs["dataPointers"])

    result = {
        "vtableBase": hex(vtable_base) if vtable_base else None,
        "vtableSlots": {VTABLE_SLOTS[o]: hex(entry({0: "allocatorAlloc", 8: "allocatorResize",
                        16: "allocatorRemap", 24: "allocatorFree"}[o])) for o in VTABLE_SLOTS},
        "indirectCallVtableOffsets": {str(o): slot_offsets[o] for o in indexed},
        "classifications": {
            "allocatorResize": {
                "occ": by_short["allocatorResize"][0], "entryPc": resize_pc,
                "invocable": resize_invocable,
                "reason": ("std.mem.Allocator resize slot (vtable+8); the vtable is indexed only at "
                           f"offsets {indexed} by any indirect call and no direct jal targets it, so the "
                           "decoder never calls allocator.resize (exact-size bump allocations never grow)."),
            },
            "allocatorRemap": {
                "occ": by_short["allocatorRemap"][0], "entryPc": remap_pc,
                "invocable": remap_invocable,
                "reason": ("std.mem.Allocator remap slot (vtable+16); the vtable is indexed only at "
                           f"offsets {indexed} by any indirect call and no direct jal targets it, so the "
                           "decoder never calls allocator.remap."),
            },
            "zesu_raw_error": {
                "occ": by_short["zesu_raw_error"][0], "entryPc": error_pc,
                "invocable": error_invocable,
                "reason": ("exported raw-ABI error getter; no jal/jalr/data pointer in the binary "
                           "references its entry, so the sealed _start harness never calls it (it "
                           "discriminates success/failure via zesu_raw_result's null return). No ABI "
                           "surface to invoke it without relinking (forbidden)."),
            },
        },
    }
    ok = not (resize_invocable or remap_invocable or error_invocable)
    result["allThreeStaticallyUnreachable"] = ok

    Path(a.out_json).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    md = ["# Row C — static classification of the uncovered occurrences (GENERATED)", "",
          "Mechanically derived from the UNCHANGED production `zesu-ssz` disassembly (objdump); not from",
          "test-run coverage. Diagnostic-only; never imported by the proof.", "",
          f"std.mem.Allocator VTable at `{result['vtableBase']}`: "
          + ", ".join(f"{m}=`{p}`" for m, p in result["vtableSlots"].items()) + ".",
          f"Indirect (jalr) calls index the vtable at offsets: `{indexed}` "
          "(0=alloc, 8=resize, 16=remap, 24=free).", ""]
    for name, c in result["classifications"].items():
        verdict = "INVOCABLE (revisit!)" if c["invocable"] else "statically unreachable"
        md.append(f"- **occ {c['occ']} `{name}`** (entry {c['entryPc']}): {verdict} — {c['reason']}")
    md += ["", f"All three statically unreachable: **{ok}**. Row C excludes them from its coverage claims.",
           ""]
    Path(a.out_md).write_text("\n".join(md))
    print(f"static classification: allThreeStaticallyUnreachable={ok}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
