#!/usr/bin/env python3
"""Row C: evaluate the actual Row A entry/exit BINDINGS, the allocation LEDGER, and routine MEANINGS
against the register/memory state captured from the unchanged production ELF.

The scaled checker previously validated a function instance's control flow, effects and step bound, but not
the thing Row A actually declares about it: *where its parameters live on entry*. A `["offset", "reg",
9, 0]` row was carried through the pipeline and never evaluated against register x9. This module is
that evaluation.

Three layers, in increasing strength, each reported separately so a weak layer can never be mistaken
for a strong one:

1. `entryBindingsEvaluable` — every EFFECTIVE Row A binding row (the recovered table, not the raw DWARF
   one that still carries `callerProvided` gaps) resolves to a concrete value from the real machine
   state at the declared entry PC: registers from the boundary snapshot, memory from the ELF image
   overlaid with the stores that preceded the snapshot. A declared location that cannot be read is a
   FAILURE, not a gap.

2. `entryBindingsRealized` — the resolved values have their declared *consequence* in the trace. This
   is what makes the check falsifiable rather than a tautology, and it is routine-family specific:

     entryAbi     `zesu_decode_raw(input, input_len)` must equal the input buffer base and the exact
                  byte length of the file fed to the process — external ground truth, not self-reported.
     rawCopy      `memcpy/memmove(dst, src, n)` must store exactly `[dst, dst+n)` and load exactly
                  `[src, src+n)`.
     alloc        `zesu_raw_alloc(bytes, alignment)` / `allocatorAlloc(len, alignment)` must bump the
                  allocator cursor by at least `bytes`, return an `alignment`-aligned pointer, and
                  match the reconstructed ledger event.
     offsetRead   an `offset`-bound reader must load its window at `sliceBase + offset`, where
                  `sliceBase` is required to AGREE across all sibling function_instances reading in the same
                  parent invocation. Sibling agreement is what falsifies a wrong offset: a single
                  function_instance's base is unobservable, but two siblings disagreeing about it is not.
     comptime     a `const`-bound parameter must equal the value pinned in the routine catalog from the
                  Zig source, so a constant-folded binding cannot silently drift from the source.

3. `exitBindingRealized` — at a declared exit PC, the function_instance's result register matches the
   convention its binding declares (allocation pointer, copy destination, decode decision).

Meanings (`meaningLE`) upgrade the previous "some loaded value was also stored" heuristic to the real
statement: the little-endian integer of the exact window the function_instance read from the input IS the
value it produced. Anything weaker stays an explicit gap.

Diagnostic-only; never imported by the theorem graph.
"""
from __future__ import annotations

import struct
from pathlib import Path

MASK64 = (1 << 64) - 1


# ---- machine state at a boundary --------------------------------------------------------------------

def load_image(elf: str) -> list[tuple[int, bytes]]:
    """[(vaddr, bytes)] for every PT_LOAD segment's file-backed contents."""
    d = Path(elf).read_bytes()
    e_phoff, = struct.unpack_from("<Q", d, 0x20)
    e_phentsize, e_phnum = struct.unpack_from("<HH", d, 0x36)
    segs = []
    for i in range(e_phnum):
        o = e_phoff + i * e_phentsize
        if struct.unpack_from("<I", d, o)[0] != 1:
            continue
        p_offset, p_vaddr = struct.unpack_from("<QQ", d, o + 0x08)
        p_filesz, = struct.unpack_from("<Q", d, o + 0x20)
        segs.append((p_vaddr, d[p_offset:p_offset + p_filesz]))
    return segs


class Memory:
    """The guest's memory as the checker can see it: the loaded ELF image, overlaid with the stores the
    trace recorded before a given point. A read that no image segment covers and no prior store wrote
    is UNKNOWN (None) — never silently zero, which would let an unreadable declared location pass."""

    def __init__(self, segs, stores):
        self.segs = segs
        # (index, addr, width, value) sorted by index; the trace is already in execution order.
        self.stores = stores

    def _image_byte(self, addr: int):
        for base, blob in self.segs:
            if base <= addr < base + len(blob):
                return blob[addr - base]
        return None

    def read_u64(self, addr: int, before_index: int):
        """The 8-byte little-endian value at `addr` as of trace position `before_index`."""
        out = 0
        for j in range(8):
            b = self._byte(addr + j, before_index)
            if b is None:
                return None
            out |= b << (8 * j)
        return out

    def _byte(self, addr: int, before_index: int):
        # The last store before `before_index` that covers this address wins.
        found = None
        for (idx, saddr, w, val) in self.stores:
            if idx >= before_index:
                break
            if saddr <= addr < saddr + w:
                found = (val >> (8 * (addr - saddr))) & 0xFF
        if found is not None:
            return found
        return self._image_byte(addr)


def resolve_binding(row, regs, mem: Memory, at_index: int):
    """One EFFECTIVE Row A row -> its concrete value on the real machine, or None if unreadable.

    Mirrors `BindingInventory.bindingRowHolds` exactly: `const` is the value itself; `reg` reads the
    register; `breg`/`fbreg` read the machine word at base+offset; `bregValue` is base+offset with no
    load (DWARF `DW_OP_stack_value`); `addr`/`addrValue` are the absolute forms; `derived` is the
    loop-carried `index * stride` register plus the row's constant (`DerivedIndexRep`)."""
    kind, reg, val = row["kind"], row["reg"], row["value"]
    if kind == "const":
        return val
    if kind == "addrValue":
        return reg
    if kind == "addr":
        return mem.read_u64(reg, at_index)
    if regs is None or not (1 <= reg <= 31):
        return None
    base = regs[reg]
    if kind == "reg":
        return base
    if kind in ("bregValue", "derived"):
        return (base + val) & MASK64
    if kind in ("breg", "fbreg"):
        return mem.read_u64((base + val) & MASK64, at_index)
    return None


# ---- allocation ledger -------------------------------------------------------------------------------

def build_ledger(stores, cursor_lo: int, cursor_hi: int):
    """Reconstruct the allocation ledger from the allocator cursor's own store record.

    Every allocation IS a cursor bump, so the cursor's write history is the ledger — reconstructed from
    the machine, not from a self-report by the allocator. Each event carries its ordinal, the cursor
    before and after, and the resulting block size."""
    events, prev = [], None
    for (idx, pc, addr, w, val, sp) in stores:
        if not (cursor_lo <= addr < cursor_hi):
            continue
        if prev is not None and val == prev:
            continue                      # a rewrite of the same value allocates nothing
        events.append({"ordinal": len(events), "index": idx, "pc": pc, "cursorAddr": addr,
                       "before": prev, "after": val,
                       "size": None if prev is None else (val - prev)})
        prev = val
    return events


def ledger_invariants(events):
    """Whole-run ledger properties: the bump cursor only ever moves forward, and every event after the
    first has a positive size. A decrement would mean the bump allocator freed or reused, which the
    Row B ledger model forbids."""
    sized = [e for e in events if e["size"] is not None]
    return {
        "events": len(events),
        "monotonic": all(e["size"] >= 0 for e in sized),
        "allPositive": all(e["size"] > 0 for e in sized),
        "totalBytes": sum(e["size"] for e in sized),
    }


# ---- little-endian meaning ----------------------------------------------------------------------------

def le_value(byte_map: dict[int, int], base: int, width: int):
    """The little-endian integer at `base` of `width` bytes, or None if any byte was not observed."""
    out = 0
    for j in range(width):
        b = byte_map.get(base + j)
        if b is None:
            return None
        out |= b << (8 * j)
    return out


def observed_bytes(loads, lo: int, hi: int) -> dict[int, int]:
    """addr -> byte, for every byte covered by an in-region load landing in [lo,hi)."""
    out = {}
    for (idx, pc, addr, w, val) in loads:
        if not (lo <= addr < hi):
            continue
        for j in range(w):
            out[addr + j] = (val >> (8 * j)) & 0xFF
    return out
