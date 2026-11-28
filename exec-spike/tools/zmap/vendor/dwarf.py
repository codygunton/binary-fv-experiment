"""Recover code ranges from the selected object and validate their ELF anchors.

zmap additions (not in zesislar's copy): `file_name`, `line_rows` (moved from `hints.py`) and
`inline_frames`, the full inline chain of every out-of-line function (plan S9.4).
"""
from collections import defaultdict
from pathlib import Path

from inventory import die_attribute, die_ranges, die_source


def file_name(lp, cu, index):
    """Path of line-program file `index` (1-based) of `cu`, or None."""
    entries = lp.header.file_entry
    if not 0 < index <= len(entries):
        return None
    entry = entries[index - 1]
    if entry.dir_index:
        directory = lp.header.include_directory[entry.dir_index - 1]
    else:
        directory = cu.get_top_DIE().attributes['DW_AT_comp_dir'].value
    return str(Path(directory.decode(errors='replace')) / entry.name.decode(errors='replace'))


def line_rows(dwarf):
    """Sorted rows (address, end, file, line) of every line-table sequence; line 0 dropped."""
    rows = []
    for cu in dwarf.iter_CUs():
        lp = dwarf.line_program_for_CU(cu)
        if lp is None:
            continue
        names = {}
        prev = None
        for entry in lp.get_entries():
            st = entry.state
            if st is None:
                continue
            if prev is not None and st.address >= prev.address:
                if prev.line and st.address > prev.address:
                    if prev.file not in names:
                        names[prev.file] = file_name(lp, cu, prev.file)
                    rows.append((prev.address, st.address, names[prev.file], prev.line))
            prev = None if st.end_sequence else st
    rows.sort()
    return rows


def inline_frames(dwarf):
    """Every out-of-line subprogram with code, and every inlined subroutine nested in it.

    Returns frames as dicts: `parent` (index of the enclosing frame, None for a subprogram),
    `depth` (0 for a subprogram), `ranges` [(lo, hi)], `name` (linkage name, else DW_AT_name,
    through DW_AT_abstract_origin), `short` (DW_AT_name), `decl_file`, `decl_line`, and for an
    inlined frame `call_file`, `call_line` (where the parent's source calls it; None if absent or 0).
    Lexical blocks are transparent. The innermost frame whose ranges hold an address is the
    source function of that address; its parents up to depth 0 are the inline chain.
    """
    frames = []

    def value(die, key):
        a = die_attribute(die, key)
        if a is None:
            return None
        return a.value.decode(errors='replace') if isinstance(a.value, bytes) else a.value

    for cu in dwarf.iter_CUs():
        lp = dwarf.line_program_for_CU(cu)
        names = {}

        def path(index):
            if index is None or lp is None:
                return None
            if index not in names:
                names[index] = file_name(lp, cu, index)
            return names[index]

        for die in cu.iter_DIEs():
            if die.tag != 'DW_TAG_subprogram':
                continue
            ranges = [(lo, hi) for lo, hi in die_ranges(dwarf, die) if hi > lo]
            if not ranges:
                continue
            stack = [(die, None, 0)]
            while stack:
                node, parent, depth = stack.pop()
                me = parent
                if node is die or node.tag == 'DW_TAG_inlined_subroutine':
                    rs = ranges if node is die else [(lo, hi) for lo, hi in die_ranges(dwarf, node) if hi > lo]
                    call_file = node.attributes.get('DW_AT_call_file')
                    call_line = node.attributes.get('DW_AT_call_line')
                    frames.append({
                        'parent': parent, 'depth': depth, 'ranges': rs,
                        'name': value(node, 'DW_AT_linkage_name') or value(node, 'DW_AT_name'),
                        'short': value(node, 'DW_AT_name'),
                        'decl_file': path(value(node, 'DW_AT_decl_file')),
                        'decl_line': value(node, 'DW_AT_decl_line'),
                        'call_file': path(call_file.value) if call_file is not None else None,
                        # DWARF line 0 means "no source line" (compiler-generated inline).
                        'call_line': call_line.value or None if call_line is not None else None,
                    })
                    me = len(frames) - 1
                    depth = depth + 1 if node is not die else 1
                for child in node.iter_children():
                    if child.tag in ('DW_TAG_inlined_subroutine', 'DW_TAG_lexical_block'):
                        stack.append((child, me, depth))
    return frames


def code_dwarf(obj, final):
    """Apply only the RISC-V relocations present in this object's DWARF.

    Code sections need one common relocation delta and unchanged function sizes.
    This does not derive linked addresses for arbitrary merged data sections.
    """
    symbols = obj.get_section_by_name('.symtab')
    final_symbols = {s.name: s for s in final.get_section_by_name('.symtab').iter_symbols()
                     if s['st_info']['type'] == 'STT_FUNC' and s['st_size']}
    deltas = defaultdict(set)
    anchors = []
    final_code = [(s['sh_addr'],s.data()) for s in final.iter_sections() if s['sh_flags'] & 4]
    object_code = {}
    for symbol in symbols.iter_symbols():
        if symbol['st_info']['type'] != 'STT_FUNC' or not symbol['st_size']:
            continue
        linked = final_symbols.get(symbol.name)
        if linked is None: continue
        if linked['st_size'] != symbol['st_size']:
            raise ValueError(f'Changed function size: {symbol.name}')
        delta = linked['st_value']-symbol['st_value']
        index = symbol['st_shndx']
        if index not in object_code: object_code[index] = obj.get_section(index).data()
        before = object_code[index][symbol['st_value']:symbol['st_value']+symbol['st_size']]
        after = next((data[linked['st_value']-start:linked['st_value']-start+linked['st_size']]
                      for start,data in final_code if start <= linked['st_value'] and linked['st_value']+linked['st_size'] <= start+len(data)),None)
        if after is None or len(before) % 4: raise ValueError(f'Invalid code anchor: {symbol.name}')
        for offset in range(0,len(before),4):
            left = int.from_bytes(before[offset:offset+4],'little')
            right = int.from_bytes(after[offset:offset+4],'little')
            opcode = left & 127
            mask = (0xfff if opcode in {0x17,0x37,0x6f} else 0xfffff if opcode in {3,0x13,0x1b,0x67}
                    else 0x1fff07f if opcode in {0x23,0x63} else 0xffffffff)
            if left & 3 != 3 or left & mask != right & mask:
                raise ValueError(f'Changed instruction shape: {symbol.name}+{offset:#x}')
        deltas[symbol['st_shndx']].add(delta)
        anchors.append({'symbol': symbol.name, 'object_start': symbol['st_value'],
                        'linked_start': linked['st_value'], 'bytes': symbol['st_size']})
    if any(len(values) != 1 for values in deltas.values()):
        raise ValueError('Code sections do not have a single relocation delta')
    bases = {index: next(iter(values)) for index, values in deltas.items()}
    dwarf = obj.get_dwarf_info(relocate_dwarf_sections=False)
    counts = defaultdict(int)
    for relocations in obj.iter_sections():
        if not relocations.name.startswith('.rela.debug'): continue
        target = obj.get_section(relocations['sh_info'])
        descriptor = getattr(dwarf, target.name[1:]+'_sec', None)
        if descriptor is None: continue
        stream = descriptor.stream
        for relocation in relocations.iter_relocations():
            kind, offset = relocation['r_info_type'], relocation['r_offset']
            if kind not in {1, 2, 34, 38}:
                raise ValueError(f'Unsupported DWARF relocation {kind}')
            symbol = symbols.get_symbol(relocation['r_info_sym'])
            value = symbol['st_value']+bases.get(symbol['st_shndx'], 0)+relocation['r_addend']
            width = 8 if kind == 2 else 4
            if not 0 <= offset <= descriptor.size-width:
                raise ValueError('DWARF relocation lies outside its section')
            stream.seek(offset)
            old = int.from_bytes(stream.read(width), 'little')
            if kind == 34: value = old+value
            elif kind == 38: value = old-value
            stream.seek(offset)
            stream.write((value % (1 << (8*width))).to_bytes(width, 'little'))
            counts[kind] += 1
    return dwarf, {'method': 'Selected-object DWARF with checked code relocation deltas, sizes, instruction widths, opcodes, and register fields. Link relocation may change immediate fields.',
                   'code_section_deltas': {str(k): v for k, v in bases.items()},
                   'anchor_count': len(anchors), 'relocation_counts': dict(counts)}


def inline_ranges(obj, final, wanted):
    dwarf, evidence = code_dwarf(obj, final)
    result = {name: [] for name in wanted}
    for unit in dwarf.iter_CUs():
        for die in unit.iter_DIEs():
            if die.tag not in {'DW_TAG_subprogram', 'DW_TAG_inlined_subroutine'}: continue
            attribute = die_attribute(die, 'DW_AT_name')
            if attribute is None: continue
            name = attribute.value.decode(errors='replace').split('__anon_')[0]
            if name not in result: continue
            ranges = die_ranges(dwarf, die)
            if not ranges: continue
            line = die_attribute(die, 'DW_AT_decl_line')
            result[name].append({'kind': die.tag, 'die_offset': die.offset,
                'source_file': die_source(dwarf, die), 'source_line': line.value if line else None,
                'ranges': [{'start': start, 'end': end} for start, end in ranges]})
    return result, evidence
