"""Read the ELF through the LLVM tools: symbols, sections, disassembly, section bytes."""
import hashlib
import os
import re
import subprocess
import tempfile

LLVM = '/usr/bin'

INSN = re.compile(r'^\s*([0-9a-f]+):\s+([0-9a-f]+)\s+(\S+)(?:\s+(.*?))?\s*$')
COMMENT = re.compile(r'\s*<[^>]*>\s*$')


def tool(name, *args):
    return subprocess.run([os.path.join(LLVM, name), *args], check=True,
                          capture_output=True, text=True).stdout


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def sections(elf):
    """name -> (addr, size) of every section with an address."""
    out = {}
    for line in tool('llvm-readelf', '-SW', elf).splitlines():
        m = re.match(r'\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]{16})\s+[0-9a-f]+\s+([0-9a-f]+)', line)
        if m:
            out[m.group(1)] = (int(m.group(2), 16), int(m.group(3), 16))
    return out


def func_symbols(elf):
    """[(entry, size, name)] for every FUNC symbol with nonzero size."""
    out = []
    for line in tool('llvm-readelf', '-sW', elf).splitlines():
        parts = line.split()
        if len(parts) >= 8 and parts[3] == 'FUNC':
            size = int(parts[2], 0)
            if size:
                out.append((int(parts[1], 16), size, parts[7]))
    return out


def symbol_value(elf, name):
    for line in tool('llvm-readelf', '-sW', elf).splitlines():
        parts = line.split()
        if len(parts) >= 8 and parts[7] == name:
            return int(parts[1], 16)
    raise KeyError(name)


def section_bytes(elf, name):
    with tempfile.TemporaryDirectory() as d:
        out = os.path.join(d, 'sec.bin')
        tool('llvm-objcopy', '-O', 'binary', f'--only-section={name}', elf, out)
        with open(out, 'rb') as f:
            return f.read()


class Insn:
    __slots__ = ('pc', 'size', 'mn', 'ops', 'target')

    def __init__(self, pc, size, mn, ops, target):
        self.pc, self.size, self.mn, self.ops, self.target = pc, size, mn, ops, target

    @property
    def next(self):
        return self.pc + self.size

    def __repr__(self):
        return f'{self.pc:x}: {self.mn} {", ".join(self.ops)}'


def parse_insn(line):
    m = INSN.match(line)
    if not m:
        return None
    pc, enc, mn, rest = int(m.group(1), 16), m.group(2), m.group(3), m.group(4) or ''
    rest = COMMENT.sub('', rest)
    ops = [o.strip() for o in rest.split(',')] if rest else []
    target = None
    if mn in BRANCHES or mn in ('jal', 'c.j', 'c.jal'):
        target = int(ops[-1], 16)
    return Insn(pc, len(enc) // 2, mn, ops, target)


BRANCHES = {'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'c.beqz', 'c.bnez'}


def disassemble(elf):
    """pc -> Insn for every instruction llvm-objdump prints."""
    out = {}
    for line in tool('llvm-objdump', '-d', '-M', 'no-aliases', elf).splitlines():
        insn = parse_insn(line)
        if insn is not None:
            out[insn.pc] = insn
    return out
