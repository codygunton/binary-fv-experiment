"""Recover code ranges from the selected object and validate their ELF anchors."""
from collections import defaultdict

from inventory import die_attribute, die_ranges, die_source


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
