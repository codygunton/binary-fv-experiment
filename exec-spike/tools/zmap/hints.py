"""Source hints from the pre-link debug object (heuristic; never used in proofs).

Uses the vendored zesislar helpers: `code_dwarf` checks that the object's code matches the
linked ELF and relocates its DWARF to linked addresses.
"""
import bisect
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'vendor'))

from elftools.elf.elffile import ELFFile  # noqa: E402

from dwarf import code_dwarf, line_rows  # noqa: E402  (vendor/dwarf.py)
from inventory import die_attribute, die_ranges  # noqa: E402  (vendor/inventory.py)


def _inline_ranges(dwarf):
    """(lo, hi, depth, name) of every inlined-subroutine range; depth = inline nesting."""
    out = []
    for cu in dwarf.iter_CUs():
        stack = [(cu.get_top_DIE(), 0)]
        while stack:
            die, depth = stack.pop()
            child_depth = depth
            if die.tag == 'DW_TAG_inlined_subroutine':
                child_depth = depth + 1
                name = die_attribute(die, 'DW_AT_name')
                if name is not None:
                    name = name.value.decode(errors='replace')
                    for lo, hi in die_ranges(dwarf, die):
                        if hi > lo:
                            out.append((lo, hi, child_depth, name))
            for child in die.iter_children():
                stack.append((child, child_depth))
    out.sort()
    return out


def attach(static, elf_path, object_path):
    """Set `src` on every block; return the helper's evidence dict."""
    with open(object_path, 'rb') as fo, open(elf_path, 'rb') as fe:
        dwarf, evidence = code_dwarf(ELFFile(fo), ELFFile(fe))
        rows = line_rows(dwarf)
        inl = _inline_ranges(dwarf)
    row_addr = [r[0] for r in rows]
    inl_lo = [r[0] for r in inl]
    for fn in static['functions']:
        lo_i = bisect.bisect_left(inl_lo, fn['entry'])
        hi_i = bisect.bisect_left(inl_lo, fn['entry'] + fn['size'])
        fn_inl = inl[lo_i:hi_i]
        for block in fn['blocks']:
            s, e = block['start'], block['end']
            i = max(bisect.bisect_right(row_addr, s) - 1, 0)
            files, lines = [], []
            while i < len(rows) and rows[i][0] < e:
                if rows[i][1] > s:
                    files.append(rows[i][2])
                    lines.append(rows[i][3])
                i += 1
            best = None
            for lo, hi, depth, name in fn_inl:
                if lo <= s < hi and (best is None or depth > best[0]):
                    best = (depth, name)
            if files or best:
                block['src'] = {'file': files[0] if files else None,
                                'lines': [min(lines), max(lines)] if lines else None,
                                'inline': best[1] if best else None}
    return evidence
