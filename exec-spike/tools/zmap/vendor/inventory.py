#!/usr/bin/env python3
"""Inventory stock source functions from ELF symbols, DWARF, and disassembly.

Counts describe static code, not executed paths. Inline ranges can overlap.
Memory notes come from source inspection; they are not pointer proofs.
"""
import argparse
import bisect
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re

from elftools.elf.elffile import ELFFile
from elftools.dwarf.descriptions import describe_form_class

DECODERS = {
    'src/stateless/stateless/ssz.zig': ['decode', 'decodeByteListList', 'decodeWithdrawal'],
    'src/stateless/rlp_decode.zig': ['decodeSingleTx', 'decodeTxList', 'decodeTxFields',
        'decodeParentHeader', 'decodeBlockHeader', 'decodeWithdrawals'],
    'src/stateless/mpt/rlp.zig': ['decodeItem'],
}
OPCODES = [f'src/evm/interpreter/opcodes/{name}.zig'
           for name in ['arithmetic', 'bitwise', 'comparison']]
GAS = 'src/evm/interpreter/gas_costs.zig'
VALIDATION = 'src/evm/handler/validation.zig'
FUNCTION = re.compile(r'^\s*(?:pub\s+)?(?:inline\s+)?fn\s+(\w+)\s*\(', re.M)
INSN = re.compile(r'^\s*([0-9a-f]+):\s+([0-9a-f]{4,16})\s+(\S+)\s*(.*?)\s*$')
CONDITIONAL = {'beq','bne','blt','bge','bltu','bgeu','beqz','bnez','bgez','bltz','blez','bgtz'}


def mask_source(text):
    return re.sub(r'//[^\n]*|"(?:\\.|[^"\\])*"',
                  lambda match: ' ' * len(match.group()), text)


def function_body(text, match):
    masked = mask_source(text)
    depth, cursor = 1, match.end()
    while depth:
        depth += (masked[cursor] == '(') - (masked[cursor] == ')')
        cursor += 1
    start = masked.index('{', cursor)
    if 'struct' in masked[cursor:start]:
        depth, cursor = 1, start + 1
        while depth:
            depth += (masked[cursor] == '{') - (masked[cursor] == '}')
            cursor += 1
        start = masked.index('{', cursor)
    depth, cursor = 1, start + 1
    while depth:
        depth += (masked[cursor] == '{') - (masked[cursor] == '}')
        cursor += 1
    return text[start:cursor]


def requested_functions(source):
    result = []
    for relative in [*DECODERS, *OPCODES, GAS, VALIDATION]:
        text = (source / relative).read_text()
        wanted = DECODERS.get(relative)
        if relative == VALIDATION:
            wanted = ['calculateInitialGas', 'calculateInitialGasAmsterdam']
        for match in FUNCTION.finditer(text):
            name = match.group(1)
            if wanted is not None and name not in wanted:
                continue
            body = function_body(text, match)
            module = ('ssz' if relative.endswith('/ssz.zig') else Path(relative).stem)
            result.append({'source_function': f'{module}.{name}', 'source_file': relative,
                'source_line': text.count('\n', 0, match.start(1)) + 1,
                'name': name, 'source_inline': 'inline' in match.group(),
                'source_loop_count': len(re.findall(r'\b(?:for|while)\s*\(', mask_source(body))),
                'body': body})
    return result


def die_attribute(die, key):
    if key in die.attributes:
        return die.attributes[key]
    for reference in ['DW_AT_abstract_origin', 'DW_AT_specification']:
        if reference in die.attributes:
            return die_attribute(die.get_DIE_from_attribute(reference), key)
    return None


def die_source(dwarf, die):
    file_index = die_attribute(die, 'DW_AT_decl_file')
    if file_index is None:
        return ''
    line = dwarf.line_program_for_CU(die.cu)
    if line is None:
        return ''
    entry = line.header.file_entry[file_index.value - 1]
    directory = (line.header.include_directory[entry.dir_index - 1]
                 if entry.dir_index else die.cu.get_top_DIE().attributes['DW_AT_comp_dir'].value)
    return str(Path(directory.decode(errors='replace')) / entry.name.decode(errors='replace'))


def die_ranges(dwarf, die):
    if 'DW_AT_ranges' in die.attributes:
        base = die.cu.get_top_DIE().attributes.get('DW_AT_low_pc')
        base = base.value if base else 0
        result = []
        for entry in dwarf.range_lists().get_range_list_at_offset(
                die.attributes['DW_AT_ranges'].value, die.cu):
            if hasattr(entry, 'base_address'):
                base = entry.base_address
            else:
                offset = 0 if entry.is_absolute else base
                result.append((offset + entry.begin_offset, offset + entry.end_offset))
        return result
    low, high = die.attributes.get('DW_AT_low_pc'), die.attributes.get('DW_AT_high_pc')
    if low is None or high is None:
        return []
    return [(low.value, high.value if describe_form_class(high.form) == 'address'
             else low.value + high.value)]


def branch_target(instruction):
    operand = instruction['operands']
    comment = re.search(r'#\s*([0-9a-f]+)\s*<', operand)
    if comment:
        return int(comment.group(1), 16)
    target = re.search(r'(?:^|,)\s*([0-9a-f]{6,16})(?:\s|$)', operand)
    return int(target.group(1), 16) if target else None


def cfg_loops(instructions):
    """Return cyclic SCCs of the range-local instruction graph."""
    pcs = {row['pc'] for row in instructions}
    graph = {}
    for row in instructions:
        pc, mnemonic = row['pc'], row['mnemonic']
        if 'successors' in row:
            graph[pc] = [target for target in row['successors'] if target in pcs]
            continue
        targets = []
        if mnemonic in CONDITIONAL | {'j'}:
            target = branch_target(row)
            if target in pcs:
                targets.append(target)
        if mnemonic not in {'j','jr','ret','tail'} and pc + row['size'] in pcs:
            targets.append(pc + row['size'])
        graph[pc] = targets
    # Iterative Kosaraju avoids recursion limits on large decoder functions.
    seen, order = set(), []
    for root in graph:
        if root in seen:
            continue
        stack = [(root, False)]
        while stack:
            node, finished = stack.pop()
            if finished:
                order.append(node)
            elif node not in seen:
                seen.add(node)
                stack.append((node, True))
                stack.extend((child, False) for child in graph[node] if child not in seen)
    reverse = {pc: [] for pc in graph}
    for pc, children in graph.items():
        for child in children:
            reverse[child].append(pc)
    seen, loops = set(), []
    for root in reversed(order):
        if root in seen:
            continue
        group, stack = [], [root]
        while stack:
            node = stack.pop()
            if node in seen:
                continue
            seen.add(node); group.append(node); stack.extend(reverse[node])
        if len(group) > 1 or root in graph[root]:
            members = set(group)
            loops.append({'instruction_count': len(group), 'minimum_pc': hex(min(group)),
                'backward_edges': [{'from': hex(pc), 'to': hex(target)}
                    for pc in sorted(group) for target in graph[pc]
                    if target in members and target <= pc]})
    return loops


def analyze_ranges(ranges, instructions, pcs, symbols):
    selected = {row['pc']: row for start, end in ranges
                for row in instructions[bisect.bisect_left(pcs, start):bisect.bisect_left(pcs, end)]}
    rows = sorted(selected.values(), key=lambda row: row['pc'])
    calls, adjustments, offsets = [], [], set()
    for row in rows:
        mnemonic, operands, pc = row['mnemonic'], row['operands'], row['pc']
        if mnemonic in {'jal','jalr','j','jr','call','tail'}:
            target = branch_target(row)
            external = target is None or target not in selected
            if (mnemonic in {'jal','jalr','call'} or mnemonic in {'jr','tail'}
                    or external and mnemonic == 'j' and target in symbols):
                if mnemonic == 'jr' and operands.strip() == 'ra':
                    continue
                calls.append({'pc': hex(pc), 'kind': 'call' if mnemonic in {'jal','jalr','call'} else 'tail',
                    'target_address': hex(target) if target is not None else None,
                    'target_symbols': symbols.get(target, []),
                    'instruction': f'{mnemonic} {operands}'})
        adjustment = re.match(r'sp,sp,(-?\d+)', operands)
        if mnemonic in {'addi','add','sub','addiw'} and operands.startswith('sp,sp,'):
            adjustments.append({'pc': hex(pc), 'bytes': int(adjustment.group(1))
                                if adjustment and mnemonic in {'addi','addiw'} else None,
                                'instruction': f'{mnemonic} {operands}'})
        offsets.update(int(value) for value in re.findall(r'(-?\d+)\(sp\)', operands))
    return {'ranges': [{'start': hex(start), 'end': hex(end), 'bytes': end-start} for start,end in ranges],
            'instruction_count': len(rows), 'calls': calls, 'loops': cfg_loops(rows),
            'stack_structure': {'sp_adjustments': adjustments, 'direct_sp_offsets': sorted(offsets)}}


def memory_notes(row):
    body, path = row['body'], row['source_file']
    notes = []
    if path in DECODERS:
        notes.append('Reads caller byte slices; source follows the guest input path. Concrete pointer provenance is not proved.')
        notes.append('Writes returned structures or caller result slots.')
    if re.search(r'\b(?:allocator|alloc)\.(?:alloc|dupe|realloc|create)\b', body):
        notes.append('Allocates heap output through the supplied allocator.')
    if re.search(r'\.stack\b|\bstack\.', body):
        notes.append('Reads or writes EVM operand stack: heap-backed U256 slice and length in interpreter/stack.zig.')
    if re.search(r'\.gas\b|chargeGas', body):
        notes.append('Reads or writes context gas fields.')
    if path == GAS:
        notes.append('Gas arithmetic uses scalar arguments; native spills and call frames appear in stack_structure.')
    if path == VALIDATION:
        notes.append('Reads transaction data, access lists, authorization lists, and configuration. Read pointers can alias input or decoded heap data.')
    if not notes:
        notes.append('Source uses scalar values or fixed-size limb arrays; native spills appear in stack_structure.')
    return notes


def inventory(elf_path, dump_path, source, debug_reference=None):
    instructions = []
    for line in dump_path.read_text().splitlines():
        match = INSN.match(line)
        if match:
            pc, encoding, mnemonic, operands = match.groups()
            instructions.append({'pc': int(pc,16), 'size': len(encoding)//2,
                                 'mnemonic': mnemonic, 'operands': operands})
    instructions.sort(key=lambda row: row['pc']);pcs=[row['pc'] for row in instructions]
    rows = requested_functions(source)
    by_source = {(row['source_file'],row['name']): row for row in rows}
    with elf_path.open('rb') as stream:
        elf = ELFFile(stream);symtab=elf.get_section_by_name('.symtab')
        symbols = defaultdict(list);function_symbols=[]
        for symbol in symtab.iter_symbols():
            if symbol['st_info']['type']=='STT_FUNC' and symbol['st_size']:
                symbols[symbol['st_value']].append(symbol.name)
                function_symbols.append(symbol)
        reference_stream = debug_reference.open('rb') if debug_reference else None
        reference_elf = ELFFile(reference_stream) if reference_stream else elf
        dwarf = reference_elf.get_dwarf_info()
        reference_symbols = [s for s in reference_elf.get_section_by_name('.symtab').iter_symbols()
                             if s['st_info']['type']=='STT_FUNC' and s['st_size']]
        final_by_name = {s.name:s for s in function_symbols}
        def relocate(ranges):
            if not debug_reference:
                return ranges
            mapped=[]
            for start,end in ranges:
                owners=[s for s in reference_symbols if s['st_value']<=start
                        and end<=s['st_value']+s['st_size'] and s.name in final_by_name]
                if not owners:
                    raise ValueError(f'No symbol anchor for DWARF range {start:x}..{end:x}')
                owner=min(owners,key=lambda s:s['st_size']); final=final_by_name[owner.name]
                if owner['st_size'] != final['st_size']:
                    raise ValueError(f'Changed function size: {owner.name}')
                delta=final['st_value']-owner['st_value']
                def bytes_at(image,address,length):
                    for section in image.iter_sections():
                        if section['sh_type']!='SHT_NOBITS' and section['sh_addr']<=address and address+length<=section['sh_addr']+section['sh_size']:
                            offset=address-section['sh_addr']
                            return section.data()[offset:offset+length]
                    raise ValueError('Unmapped instruction range')
                before=bytes_at(reference_elf,start,end-start)
                after=bytes_at(elf,start+delta,end-start)
                for offset in range(0,len(before),4):
                    left=int.from_bytes(before[offset:offset+4],'little')
                    right=int.from_bytes(after[offset:offset+4],'little')
                    opcode=left&0x7f
                    mask=0xfff if opcode in {0x17,0x37,0x6f} else 0xfffff if opcode in {0x03,0x13,0x1b,0x67} else 0x1fff07f if opcode in {0x23,0x63} else 0xffffffff
                    if left&3!=3 or (left&mask)!=(right&mask):
                        raise ValueError(f'Changed instruction shape at {start+offset:x}')
                mapped.append((start+delta,end+delta))
            return mapped
        concrete, inline, definitions = defaultdict(list),defaultdict(list),defaultdict(list)
        for cu in dwarf.iter_CUs():
            for die in cu.iter_DIEs():
                if die.tag not in {'DW_TAG_subprogram','DW_TAG_inlined_subroutine'}:
                    continue
                attr = die_attribute(die,'DW_AT_name')
                if attr is None:
                    continue
                name = attr.value.decode(errors='replace').split('__anon_')[0]
                path = die_source(dwarf,die)
                key = next((key for key in by_source if key[1]==name and path.endswith('/'+key[0])),None)
                if key is None:
                    continue
                ranges=relocate(die_ranges(dwarf,die))
                metadata={'die_offset':hex(die.offset), 'name':attr.value.decode(errors='replace'),
                          'source_file':path, 'source_line':die_attribute(die,'DW_AT_decl_line').value}
                if die.tag=='DW_TAG_inlined_subroutine':
                    inline[key].append((ranges,metadata))
                elif ranges:
                    concrete[key].append((ranges,metadata))
                else:
                    definitions[key].append(metadata)
        for row in rows:
            key=(row['source_file'],row['name']);instances=[]
            for kind,entries in [('symbol',concrete[key]),('inline',inline[key])]:
                for ranges,metadata in entries:
                    analysis=analyze_ranges(ranges,instructions,pcs,symbols)
                    matched=[{'name':sym.name,'address':hex(sym['st_value']),'size':sym['st_size']}
                        for sym in function_symbols if any(start<=sym['st_value']<end for start,end in ranges)] if kind=='symbol' else []
                    instances.append({'kind':kind,'symbols':matched,'dwarf':metadata,**analysis})
            row['instances']=instances
            row['symbols']=[symbol for instance in instances for symbol in instance['symbols']]
            row['status']='symbol' if row['symbols'] else 'inlined' if inline[key] else 'not emitted; no inline instance found'
            chosen=[instance for instance in instances if instance['kind']=='symbol'] if row['symbols'] else instances
            row['concrete_instruction_count']=sum(instance['instruction_count'] for instance in instances if instance['kind']=='symbol')
            row['inline_instruction_count']=sum(instance['instruction_count'] for instance in instances if instance['kind']=='inline')
            row['instruction_count']=sum(instance['instruction_count'] for instance in chosen)
            row['instruction_count_note']='Concrete bodies when symbols exist; otherwise sum of inline instances. Inline ranges can overlap other functions.'
            row['calls']=[call for instance in chosen for call in instance['calls']]
            row['loops']=[loop for instance in chosen for loop in instance['loops']]
            row['memory_notes']=memory_notes(row)
            row['inlining_evidence']={'source_inline':row['source_inline'],
                'abstract_definitions':definitions[key], 'inline_instance_count':len(inline[key])}
            row.pop('body')
        return {'schema':1,'elf_sha256':hashlib.sha256(elf_path.read_bytes()).hexdigest(),
            'entry':hex(elf['e_entry']), 'functions':rows,
            'methods':{'debug_reference':str(debug_reference) if debug_reference else None,
              'inlining_evidence':'Reference DWARF relocated through same-name, same-size enclosing symbols with matching instruction layout and non-immediate fields. Link relocation can change immediate fields.' if debug_reference else 'ELF DWARF.',
              'instruction_count':'GNU objdump instruction rows in symbol or DWARF address ranges.',
              'calls':'JAL/JALR and external jumps. Unresolved register targets remain explicit.',
              'loops':'Cyclic SCCs in range-local direct control flow; backward edges listed. Nested loops share an SCC.',
              'memory':'Source inspection plus native SP adjustments. No alias or reachability proof.'}}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--elf',type=Path,required=True);parser.add_argument('--objdump',type=Path,required=True)
    parser.add_argument('--source',type=Path,required=True);parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--debug-reference',type=Path)
    args=parser.parse_args();result=inventory(args.elf,args.objdump,args.source,args.debug_reference)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(f"Inventoried {len(result['functions'])} functions")


if __name__=='__main__':main()
