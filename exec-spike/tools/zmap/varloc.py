"""`zmap varloc`: where source variables live at each cut point (plan S23).

Reads the pre-link debug object through `vendor/dwarf.py` (`code_dwarf` checks that the object's
code matches the linked ELF and relocates its DWARF, location lists included, to linked
addresses, with the deltas the source hints use). For every target function it writes
`map/varloc/<id>.json`:

  frames   the inline chain: the subprogram (depth 0) and every inlined subroutine in it
  scopes   address ranges of the subprogram, inlined subroutines and lexical blocks
  vars     every variable and parameter DIE in the function: frame, scope, name, type name,
           byte size, `param`, and `locs` = [[lo, hi, kind, text, pieces], ...]; lo/hi null when
           the location holds wherever the variable is in scope (DW_FORM_exprloc, const_value)
  cuts     per map cut point: [[var, loc index], ...] for every variable in scope there; the loc
           index is -1 when no location covers the address (listed as missing; nothing guessed)
  coverage {in_scope, located} summed over the cut points

A location is a list of pieces [kind, bytes or null, a, b]: `reg` (a = DWARF register), `mem`
(a = base register, b = offset; DW_OP_fbreg resolved through the subprogram's frame base),
`addr` (a = absolute address), `const` (a = value), `expr` (a computed value), `undef` (an
optimised-out piece). Kinds of a whole location: the piece kind, or `pieces`.

Everything here is a proposal (rule 17): it enters a proof only as text that Lean checks.
`zmap varloc validate` compares the tables with the hand-written cut assertions of S23 step 3.
"""
import bisect
import glob
import hashlib
import json
import os
import re
import sys
import textwrap

sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'vendor'))

from elftools.dwarf.dwarf_expr import DWARFExprParser  # noqa: E402
from elftools.elf.elffile import ELFFile  # noqa: E402

from dwarf import code_dwarf, file_name  # noqa: E402  (vendor/dwarf.py)
from inventory import die_attribute, die_ranges  # noqa: E402  (vendor/inventory.py)

SCHEMA = 'zmap.varloc.v1'
ABI = ('zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4',
       'a5', 'a6', 'a7', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4',
       't5', 't6')
SCOPES = ('DW_TAG_inlined_subroutine', 'DW_TAG_lexical_block')
VARS = ('DW_TAG_variable', 'DW_TAG_formal_parameter')


def reg_name(r):
    return ABI[r] if 0 <= r < 32 else f'f{r - 32}' if 32 <= r < 64 else f'r{r}'


# ------------------------------------------------------------------------------ expressions

_BIN = {'DW_OP_plus': '+', 'DW_OP_minus': '-', 'DW_OP_mul': '*', 'DW_OP_and': '&',
        'DW_OP_or': '|', 'DW_OP_xor': '^', 'DW_OP_shl': '<<', 'DW_OP_shr': '>>',
        'DW_OP_shra': '>>>', 'DW_OP_div': '/', 'DW_OP_mod': '%'}


def _infix(ops, fb):
    """Infix text of a DWARF stack expression, or None when an operator is not rendered."""
    st = []
    for op in ops:
        n, a = op.op_name, op.args
        if n.startswith('DW_OP_lit'):
            st.append(n[9:])
        elif n in ('DW_OP_constu', 'DW_OP_consts', 'DW_OP_const1u', 'DW_OP_const2u',
                   'DW_OP_const4u', 'DW_OP_const8u', 'DW_OP_const1s', 'DW_OP_const2s',
                   'DW_OP_const4s', 'DW_OP_const8s'):
            st.append(str(a[0]))
        elif n.startswith('DW_OP_breg') and n != 'DW_OP_bregx':
            st.append(_plus(reg_name(int(n[10:])), a[0]))
        elif n == 'DW_OP_bregx':
            st.append(_plus(reg_name(a[0]), a[1]))
        elif n == 'DW_OP_fbreg':
            st.append(_plus(reg_name(fb) if fb is not None else 'fb', a[0]))
        elif n == 'DW_OP_plus_uconst' and st:
            st.append(_plus(st.pop(), a[0]))
        elif n in _BIN and len(st) >= 2:
            y, x = st.pop(), st.pop()
            st.append(f'({x}{_BIN[n]}{y})')
        elif n == 'DW_OP_not' and st:
            st.append(f'~{st.pop()}')
        elif n == 'DW_OP_neg' and st:
            st.append(f'-{st.pop()}')
        elif n == 'DW_OP_deref' and st:
            st.append(f'[{st.pop()}]')
        elif n == 'DW_OP_dup' and st:
            st.append(st[-1])
        else:
            return None
    return st[-1] if len(st) == 1 else None


def _plus(x, k):
    return x if k == 0 else f'{x}+{k:#x}' if k > 0 else f'{x}-{-k:#x}'


def _piece(ops, size, fb):
    """One piece [kind, size, a, b] and its text."""
    if not ops:
        return ['undef', size, None, None], '?'
    names = [o.op_name for o in ops]
    n0 = names[0]
    if len(ops) == 1 and n0.startswith('DW_OP_reg') and n0 != 'DW_OP_regx':
        r = int(n0[9:])
        return ['reg', size, r, None], reg_name(r)
    if len(ops) == 1 and n0 == 'DW_OP_regx':
        return ['reg', size, ops[0].args[0], None], reg_name(ops[0].args[0])
    if len(ops) == 1 and n0 == 'DW_OP_fbreg' and fb is not None:
        return ['mem', size, fb, ops[0].args[0]], f'[{_plus(reg_name(fb), ops[0].args[0])}]'
    if len(ops) == 1 and n0.startswith('DW_OP_breg') and n0 != 'DW_OP_bregx':
        r = int(n0[10:])
        return ['mem', size, r, ops[0].args[0]], f'[{_plus(reg_name(r), ops[0].args[0])}]'
    if len(ops) == 1 and n0 == 'DW_OP_addr':
        return ['addr', size, ops[0].args[0], None], f'[{ops[0].args[0]:#x}]'
    if len(ops) == 1 and n0 == 'DW_OP_implicit_value':
        v = int.from_bytes(bytes(ops[0].args[1]), 'little')
        return ['const', size, v, None], f'={v:#x}' if v > 9 else f'={v}'
    if names[-1] == 'DW_OP_stack_value':
        body = ops[:-1]
        text = _infix(body, fb)
        if text is not None and re.fullmatch(r'\d+', text):
            v = int(text)
            return ['const', size, v, None], f'={v:#x}' if v > 9 else f'={v}'
        return ['expr', size, None, None], f'={text}' if text is not None else '=expr'
    text = _infix(ops, fb)
    return ['expr', size, None, None], f'[{text}]' if text is not None else '[expr]'


def location(ops, fb):
    """(kind, text, pieces) of a DWARF location expression."""
    pieces, texts, cur = [], [], []
    for op in ops:
        if op.op_name == 'DW_OP_piece':
            p, t = _piece(cur, op.args[0], fb)
            pieces.append(p)
            texts.append(f'{t}:{op.args[0]}')
            cur = []
        else:
            cur.append(op)
    if cur or not pieces:
        p, t = _piece(cur, None, fb)
        pieces.append(p)
        texts.append(t)
    kind = pieces[0][0] if len(pieces) == 1 else 'pieces'
    return kind, ' '.join(texts), pieces


# ------------------------------------------------------------------------------ DIEs

def _str(die, key):
    a = die_attribute(die, key)
    if a is None:
        return None
    return a.value.decode(errors='replace') if isinstance(a.value, bytes) else a.value


def type_info(die, cache):
    """(type name, byte size) of a variable DIE's type."""
    a = die_attribute(die, 'DW_AT_type')
    if a is None:
        return None, None
    origin = die
    while 'DW_AT_type' not in origin.attributes:
        origin = origin.get_DIE_from_attribute(
            'DW_AT_abstract_origin' if 'DW_AT_abstract_origin' in origin.attributes
            else 'DW_AT_specification')
    t = origin.get_DIE_from_attribute('DW_AT_type')
    key = (t.cu.cu_offset, t.offset)
    if key not in cache:
        cache[key] = _type(t, 0)
    return cache[key]


def _type(t, depth):
    name = _str(t, 'DW_AT_name')
    size = t.attributes['DW_AT_byte_size'].value if 'DW_AT_byte_size' in t.attributes else None
    if depth > 8:
        return name or '?', size
    if t.tag in ('DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type') and 'DW_AT_type' in t.attributes:
        n, s = _type(t.get_DIE_from_attribute('DW_AT_type'), depth + 1)
        return name or n, size if size is not None else s
    if t.tag == 'DW_TAG_pointer_type':
        if name is None:
            name = '*' + (_type(t.get_DIE_from_attribute('DW_AT_type'), depth + 1)[0]
                          if 'DW_AT_type' in t.attributes else 'anyopaque')
        return name, size if size is not None else 8
    return name or t.tag[7:], size


class Debug:
    """Variables of every subprogram with code, indexed by its address ranges."""

    def __init__(self, elf_path, object_path):
        with open(object_path, 'rb') as fo, open(elf_path, 'rb') as fe:
            self.dwarf, self.evidence = code_dwarf(ELFFile(fo), ELFFile(fe))
            self.subs = []          # (lo, hi, sub index)
            self.funcs = []         # per subprogram: dict(frames, scopes, vars)
            self._load()
        self.subs.sort()
        self.sub_lo = [s[0] for s in self.subs]

    def _load(self):
        dw = self.dwarf
        parser = DWARFExprParser(dw.structs)
        lists = dw.location_lists()
        tcache = {}
        for cu in dw.iter_CUs():
            lp = dw.line_program_for_CU(cu)
            files = {}

            def path(i):
                if i is None or lp is None:
                    return None
                if i not in files:
                    files[i] = file_name(lp, cu, i)
                return files[i]
            cu_base = cu.get_top_DIE().attributes.get('DW_AT_low_pc')
            cu_base = cu_base.value if cu_base else 0
            for die in cu.iter_DIEs():
                if die.tag != 'DW_TAG_subprogram':
                    continue
                ranges = [(lo, hi) for lo, hi in die_ranges(dw, die) if hi > lo]
                if not ranges:
                    continue
                fb = None
                fba = die_attribute(die, 'DW_AT_frame_base')
                if fba is not None and fba.form == 'DW_FORM_exprloc':
                    fbo = parser.parse_expr(fba.value)
                    if len(fbo) == 1 and fbo[0].op_name.startswith('DW_OP_reg') and fbo[0].op_name != 'DW_OP_regx':
                        fb = int(fbo[0].op_name[9:])
                fn = {'frames': [], 'scopes': [], 'vars': [], 'frame_base': fb}
                stack = [(die, None, -1, 0)]
                while stack:
                    node, frame, scope, depth = stack.pop()
                    if node is die or node.tag in SCOPES:
                        rs = ranges if node is die else [(lo, hi) for lo, hi in die_ranges(dw, node) if hi > lo]
                        if rs or node is die:
                            fn['scopes'].append(rs)
                            scope = len(fn['scopes']) - 1
                        if node is die or node.tag == 'DW_TAG_inlined_subroutine':
                            cl = node.attributes.get('DW_AT_call_line')
                            cf = node.attributes.get('DW_AT_call_file')
                            fn['frames'].append({
                                'parent': frame, 'depth': depth,
                                'name': _str(node, 'DW_AT_linkage_name') or _str(node, 'DW_AT_name'),
                                'short': _str(node, 'DW_AT_name'),
                                'call_file': path(cf.value) if cf is not None else None,
                                'call_line': (cl.value or None) if cl is not None else None})
                            frame = len(fn['frames']) - 1
                            depth = depth + 1
                        for child in node.iter_children():
                            if child.tag in SCOPES or child.tag in VARS:
                                stack.append((child, frame, scope, depth))
                        continue
                    # a variable or parameter
                    tname, size = type_info(node, tcache)
                    v = {'frame': frame, 'scope': scope, 'name': _str(node, 'DW_AT_name'),
                         'type': tname, 'size': size,
                         'param': node.tag == 'DW_TAG_formal_parameter',
                         'decl_line': _str(node, 'DW_AT_decl_line'), 'locs': []}
                    la = node.attributes.get('DW_AT_location')
                    ca = node.attributes.get('DW_AT_const_value')
                    if la is not None and la.form == 'DW_FORM_exprloc':
                        v['locs'].append([None, None, *location(parser.parse_expr(la.value), fb)])
                    elif la is not None:
                        base = cu_base
                        for e in lists.get_location_list_at_offset(la.value):
                            if hasattr(e, 'base_address'):
                                base = e.base_address
                                continue
                            off = 0 if getattr(e, 'is_absolute', False) else base
                            lo, hi = off + e.begin_offset, off + e.end_offset
                            if hi > lo:
                                v['locs'].append([lo, hi, *location(parser.parse_expr(e.loc_expr), fb)])
                    elif ca is not None:
                        val = ca.value
                        if isinstance(val, list):
                            val = int.from_bytes(bytes(val), 'little')
                        v['locs'].append([None, None, 'const', f'={val:#x}' if val > 9 else f'={val}',
                                          [['const', None, val, None]]])
                    fn['vars'].append(v)
                k = len(self.funcs)
                self.funcs.append(fn)
                for lo, hi in ranges:
                    self.subs.append((lo, hi, k))

    def function(self, entry):
        """The subprogram whose ranges hold `entry`, or None."""
        i = bisect.bisect_right(self.sub_lo, entry) - 1
        while i >= 0 and self.subs[i][0] <= entry:
            lo, hi, k = self.subs[i]
            if lo <= entry < hi:
                return self.funcs[k]
            i -= 1
        return None


# ------------------------------------------------------------------------------ tables

def in_ranges(ranges, pc):
    return any(lo <= pc < hi for lo, hi in ranges)


def at(table, pc):
    """[(var index, loc index or -1)] of every variable in scope at `pc`."""
    out = []
    for i, v in enumerate(table['vars']):
        if v['scope'] < 0 or not in_ranges(table['scopes'][v['scope']], pc):
            continue
        li = next((j for j, l in enumerate(v['locs'])
                   if l[0] is None or l[0] <= pc < l[1]), -1)
        out.append((i, li))
    return out


def function_table(f, sub):
    """map/varloc/<id>.json of map function `f` with its subprogram `sub` (None: no debug info)."""
    t = {'schema': SCHEMA, 'id': f['id'], 'name': f['name'], 'entry': f['entry'],
         'debug': sub is not None, 'frame_base': None, 'frames': [], 'scopes': [], 'vars': [],
         'cuts': []}
    if sub is not None:
        t['frame_base'] = sub['frame_base']
        t['frames'], t['scopes'], t['vars'] = sub['frames'], sub['scopes'], sub['vars']
    n_in = n_loc = 0
    for c in f['cuts']:
        rows = at(t, c['pc'])
        n_in += len(rows)
        n_loc += sum(li >= 0 for _, li in rows)
        t['cuts'].append({'pc': c['pc'], 'why': c['why'], 'vars': [list(r) for r in rows]})
    t['coverage'] = {'in_scope': n_in, 'located': n_loc, 'cuts': len(f['cuts'])}
    return t


def digest(m):
    h = hashlib.sha256()
    for f in m['functions']:
        if f['set'] == 'target':
            h.update(f'{f["id"]}:{",".join(str(c["pc"]) for c in f["cuts"])};'.encode())
    return h.hexdigest()


def build(m, elf, obj, out, force=False):
    """Write map/varloc/<id>.json for every target function and map/varloc/index.json."""
    from . import elfread
    idx_path = os.path.join(out, 'index.json')
    key = {'elf_sha256': elfread.sha256(elf), 'object_sha256': elfread.sha256(obj),
           'cuts_sha256': digest(m), 'schema': SCHEMA}
    if not force and os.path.exists(idx_path):
        with open(idx_path) as fh:
            old = json.load(fh)
        if all(old.get(k) == v for k, v in key.items()):
            return old, False
    dbg = Debug(elf, obj)
    os.makedirs(out, exist_ok=True)
    for stale in glob.glob(os.path.join(out, 'f_*.json')):
        os.remove(stale)
    per = {}
    tot_in = tot_loc = 0
    no_debug = []
    hist = dict.fromkeys(PER_CUT, 0)
    for f in m['functions']:
        if f['set'] != 'target':
            continue
        t = function_table(f, dbg.function(f['entry']))
        with open(os.path.join(out, f'{f["id"]}.json'), 'w') as fh:
            json.dump(t, fh, separators=(',', ':'))
            fh.write('\n')
        c = t['coverage']
        per[f['id']] = {'in_scope': c['in_scope'], 'located': c['located'], 'cuts': c['cuts'],
                        'vars': len(t['vars']), 'debug': t['debug']}
        tot_in += c['in_scope']
        tot_loc += c['located']
        if not t['debug']:
            no_debug.append(f['id'])
        for cut in t['cuts']:
            hist[cut_bucket(cut['vars'])] += 1
    idx = dict(key, coverage={'in_scope': tot_in, 'located': tot_loc,
                              'share': round(tot_loc / tot_in, 4) if tot_in else None,
                              'functions': len(per), 'no_debug': no_debug, 'per_cut': hist},
               functions=per, evidence=dbg.evidence)
    with open(idx_path, 'w') as fh:
        json.dump(idx, fh, indent=1)
        fh.write('\n')
    return idx, True


# Per-cut share of located variables, bucketed (plan S23 step 4).
PER_CUT = ('none in scope', 'all located', '>=75%', '>=50%', '>0%', 'none located')


def cut_bucket(rows):
    if not rows:
        return PER_CUT[0]
    s = sum(li >= 0 for _, li in rows) / len(rows)
    return (PER_CUT[1] if s == 1 else PER_CUT[2] if s >= .75 else PER_CUT[3] if s >= .5
            else PER_CUT[4] if s > 0 else PER_CUT[5])


def load(package, fid):
    """map/varloc/<fid>.json, or None."""
    return load_file(os.path.join(package, 'map', 'varloc'), fid)


def load_file(directory, fid):
    """<directory>/<fid>.json, or None."""
    p = os.path.join(directory, f'{fid}.json')
    if not os.path.exists(p):
        return None
    with open(p) as fh:
        return json.load(fh)


# ------------------------------------------------------------------------------ text

def labels(t):
    """Short label per variable: its name, numbered `name#k` when several variables share it."""
    count = {}
    for v in t['vars']:
        count[v['name']] = count.get(v['name'], 0) + 1
    seen, out = {}, []
    for v in t['vars']:
        n = v['name'] or '?'
        if count[v['name']] > 1:
            seen[n] = seen.get(n, 0) + 1
            n = f'{n}#{seen[n]}'
        out.append(n)
    return out


def var_text(t, vi):
    """`frame.name: type (size)` of one variable."""
    v = t['vars'][vi]
    fr = t['frames'][v['frame']]['short'] if v['frame'] is not None else '?'
    size = '?' if v['size'] is None else v['size']
    return f'{fr}.{v["name"]}{" (param)" if v["param"] else ""}: {v["type"]} ({size} B)'


def rows_text(t, rows, lab):
    located = [f'{lab[vi]}={t["vars"][vi]["locs"][li][3]}' for vi, li in rows if li >= 0]
    missing = [lab[vi] for vi, li in rows if li < 0]
    return ' '.join(located) + (f'; missing {" ".join(missing)}' if missing else '')


def render(t):
    """The per-cut table printed by `zmap brief` (plan S23)."""
    c = t['coverage']
    L = [f'variables at cut points (map/varloc/{t["id"]}.json; DWARF proposals, rule 17): '
         f'{c["located"]}/{c["in_scope"]} in scope have a location'
         + ('' if t['debug'] else '; no debug information for this function')]
    if not t['vars']:
        return '\n'.join(L)
    lab = labels(t)
    used = sorted({vi for cut in t['cuts'] for vi, _ in cut['vars']})
    L += textwrap.wrap('vars: ' + '; '.join(f'{lab[vi]} = {var_text(t, vi)}' for vi in used),
                       width=160, initial_indent='  ', subsequent_indent='    ')
    for cut in t['cuts']:
        L.append(f'  {cut["pc"]:#x} {cut["why"]}: {rows_text(t, cut["vars"], lab) or "(none in scope)"}')
    return '\n'.join(L)


def block_rows(t, starts):
    """Viewer data: variable list and, per block start, [[var, loc text or null], ...]."""
    lab = labels(t)
    rows = []
    for pc in starts:
        rows.append([[vi, t['vars'][vi]['locs'][li][3] if li >= 0 else None] for vi, li in at(t, pc)])
    return {'vars': [[lab[i], var_text(t, i)] for i in range(len(t['vars']))], 'blocks': rows}


# ------------------------------------------------------------------------------ validation

# Step 3 of S23: copies whose cut assertions were written by hand, and their proof directories.
HAND = (('mem.rotate__anon_8330', 'ZesuExec/Fn/Rotate/C8330'),
        ('sort.block.mergeInPlace__anon_7964', 'ZesuExec/Fn/MergeInPlace/C7964'),
        ('sort.block.mergeInPlace__anon_11564', 'ZesuExec/Fn/MergeInPlace/C11564'))


def _num(s):
    return int(s, 0)


def _balanced(text, i):
    """The bracketed text starting at text[i] ('(' or '['), brackets included."""
    pairs = {'(': ')', '[': ']'}
    stack = []
    for j in range(i, len(text)):
        ch = text[j]
        if ch in pairs:
            stack.append(pairs[ch])
        elif stack and ch == stack[-1]:
            stack.pop()
            if not stack:
                return text[i:j + 1]
    raise ValueError(f'unbalanced at {text[i:i + 40]!r}')


def _split(text, sep):
    """Split at top-level `sep`."""
    out, depth, cur, i = [], 0, '', 0
    while i < len(text):
        ch = text[i]
        if ch in '([':
            depth += 1
        elif ch in ')]':
            depth -= 1
        if depth == 0 and text.startswith(sep, i):
            out.append(cur)
            cur = ''
            i += len(sep)
            continue
        cur += ch
        i += 1
    out.append(cur)
    return [x.strip() for x in out if x.strip()]


def _strip(text):
    text = text.strip()
    while text.startswith('(') and _balanced(text, 0) == text:
        text = text[1:-1].strip()
    return text


def _pairs(expr, helpers, seen=()):
    """(int, value text) pairs of a Lean `List (Nat × Word)` expression."""
    out = []
    for term in _split(_strip(expr), '++'):
        term = _strip(term)
        if term.startswith('['):
            for item in _split(term[1:-1], ','):
                a, b = _split(_strip(item), ',')[:2] if item.startswith('(') else (None, None)
                if a is None:
                    raise ValueError(f'list item {item!r}')
                out.append((_num(a), b))
        else:
            name = term.split()[0]
            if name not in helpers or name in seen:
                raise ValueError(f'list helper {name!r}')
            out += _pairs(helpers[name], helpers, seen + (name,))
    return out


def _defs(text, pattern):
    """{name: body} of every `def` whose header matches `pattern`; the body runs to the next line
    that is blank or starts in column 0."""
    out = {}
    for mt in re.finditer(pattern, text):
        end = re.compile(r'\n(?:\n|(?=\S))').search(text, mt.end())
        out[mt.group(1)] = text[mt.end():end.start() if end else len(text)]
    return out


def _after(body, key):
    """Each bracketed argument following `key` in body."""
    out = []
    for mt in re.finditer(re.escape(key), body):
        i = mt.end()
        while body[i] in ' \n':
            i += 1
        out.append(_balanced(body, i))
    return out


def hand_facts(package, rel):
    """The register and frame-slot facts of one copy's hand-written cut assertions.

    Returns (fs, [{pc, pc_name, kind: reg|slot, loc, size, value, class}]). `class` is `param`
    (the entry's argument registers, from `Spec`), `cut` (RegsAre, SlotsAre, the inner loops'
    byte pointers, frame contents) or `convention` (`Common`: sp, s0, ra, kept registers and the
    saved-register slots of `Cfg`)."""
    d = os.path.join(package, rel)
    def read(p):
        with open(p) as fh:
            return fh.read()
    text = ''.join(read(p) + '\n\n' for p in sorted(glob.glob(os.path.join(d, '*.lean'))))
    spec = read(os.path.join(os.path.dirname(d), 'Spec.lean'))
    pcs = {mt.group(1): _num(mt.group(2))
           for mt in re.finditer(r'def (\w+) : Nat := (0x[0-9a-fA-F]+|\d+)\b', text)}
    fs = _num(re.search(r'\bfs := (0x[0-9a-fA-F]+|\d+)', text).group(1))
    saved_m = re.search(r'\bsaved := ', text)
    saved = _pairs(_balanced(text, saved_m.end()), {})
    kept = [_num(x) for x in re.search(r'\bkept := \[([^\]]*)\]', text).group(1).split(',') if x.strip()]
    params = {}
    for d_name, r in re.findall(r'def (\w+) \(m : Machine\)[^\n]*:=[^\n]*\bm\.reg (\d+)', spec):
        if _num(r) not in (1, 2):
            params.setdefault(_num(r), []).append(d_name)
    helpers = _defs(text, r'def (\w+)(?: \([^)]*\))* : List \(Nat × Word\) :=')
    at_body = _defs(text, r'def (At) \(pc : Nat\) \(m mh : Machine\) : Prop :=').get('At', '')
    bodies = list(_defs(text, r'def (\w+) \(m mh : Machine\) : Prop :=').values())
    bodies += [mt.group(1) for mt in re.finditer(r'\n  A := ([^\n]*)', text)]
    facts, done = [], set()

    def add(pc_name, kind, loc, size, value, cls):
        facts.append({'pc': pcs[pc_name], 'pc_name': pc_name, 'kind': kind, 'loc': loc,
                      'size': size, 'value': value, 'class': cls})

    def body_facts(pc_name, body):
        for e in _after(body, 'RegsAre mh '):
            for r, v in _pairs(e, helpers):
                add(pc_name, 'reg', r, 8, v, 'cut')
        for e in _after(body, 'SlotsAre mh (f m) '):
            for off, v in _pairs(e, helpers):
                add(pc_name, 'slot', off, 8, v, 'cut')
        for n, off in re.findall(r'∀ j < (\d+), mh\.mem \(frame cfg m \+ w (?:\((\w+) \+ j\)|j)\)', body):
            add(pc_name, 'slot', _num(off) if off else 0, _num(n), 'frame bytes', 'cut')

    for body in bodies:
        mt = (re.search(r'\bAt (\w+) m mh', body) or re.search(r'mh\.pc\.toNat = (\w+)', body)
              or re.search(r'(?:OuterA|InnerA|EpiA) cfg (?:\.\w+ )?(\w+)', body))
        if mt is None or mt.group(1) not in pcs:
            continue
        name = mt.group(1)
        if name in done:
            continue
        done.add(name)
        if re.search(r'\bmh = m\b', body):
            for r in sorted(params):
                add(name, 'reg', r, 8, f'argument ({", ".join(params[r])})', 'param')
            continue
        body_facts(name, body)
        if re.search(r'\bAt \w+ m mh', body):
            body_facts(name, at_body)
        inner = re.search(r'InnerA cfg \.\w+ \w+ (\d+) (\d+) (\w+)', body)
        outer = re.search(r'OuterA cfg \.\w+ \w+ (\w+)', body)
        if inner:
            add(name, 'reg', _num(inner.group(1)), 8, 'lo byte pointer', 'cut')
            add(name, 'reg', _num(inner.group(2)), 8, 'hi byte pointer', 'cut')
            for r, v in _pairs(helpers[inner.group(3)], helpers):
                add(name, 'reg', r, 8, v, 'cut')
        elif outer:
            for r, v in _pairs(helpers[outer.group(1)], helpers):
                add(name, 'reg', r, 8, v, 'cut')
        for r, v in ((2, 'frame'), (8, 'entry sp'), (1, 'return address')):
            add(name, 'reg', r, 8, v, 'convention')
        for r in kept:
            add(name, 'reg', r, 8, 'kept', 'convention')
        for off, r in saved:
            add(name, 'slot', off, 8, f'saved {r}', 'convention')
    facts.sort(key=lambda x: (x['pc'], x['class'], x['kind'], x['loc']))
    return fs, facts


def supplied(t, pc, fact, fs, lab):
    """Labels of the located variables at `pc` that the table places at the fact's register or
    frame slot (frame = sp after the prologue; s0 = frame + fs)."""
    out = []
    for vi, li in at(t, pc):
        if li < 0:
            continue
        v = t['vars'][vi]
        for kind, size, a, b in v['locs'][li][4]:
            size = size if size is not None else (v['size'] or 8)
            if fact['kind'] == 'reg' and kind == 'reg' and a == fact['loc']:
                out.append(lab[vi])
            elif fact['kind'] == 'reg' and kind == 'mem' and a == fact['loc'] and a not in (2, 8):
                out.append('&' + lab[vi])
            elif fact['kind'] == 'slot' and kind == 'mem' and a in (2, 8):
                lo = b + (fs if a == 8 else 0)
                if lo < fact['loc'] + fact['size'] and fact['loc'] < lo + size:
                    out.append(lab[vi])
    return sorted(set(out))


def validate(m, package, dbg):
    """Step 3 of S23 for every copy in HAND."""
    from . import workqueue
    report = []
    for name, rel in HAND:
        f = workqueue.find(m, name)
        t = function_table(f, dbg.function(f['entry']))
        lab = labels(t)
        fs, facts = hand_facts(package, rel)
        cuts = {c['pc'] for c in f['cuts']}
        for x in facts:
            x['supplied_by'] = supplied(t, x['pc'], x, fs, lab)
            x['map_cut'] = x['pc'] in cuts
        share = {}
        for cls in ('param', 'cut', 'convention'):
            xs = [x for x in facts if x['class'] == cls]
            share[cls] = {'facts': len(xs), 'supplied': sum(bool(x['supplied_by']) for x in xs),
                          'reg': sum(x['kind'] == 'reg' for x in xs),
                          'slot': sum(x['kind'] == 'slot' for x in xs)}
        hand_pcs = sorted({x['pc'] for x in facts})
        report.append({'id': f['id'], 'name': name, 'dir': rel, 'fs': fs, 'share': share,
                       'cuts': [{'pc': pc, 'map_cut': pc in cuts,
                                 'table': rows_text(t, at(t, pc), lab)} for pc in hand_pcs],
                       'facts': facts})
    return report


def validation_text(report, verbose=False):
    L = []
    tot = {'facts': 0, 'supplied': 0}
    for r in report:
        s = r['share']
        hw = {k: s['param'][k] + s['cut'][k] for k in ('facts', 'supplied')}
        tot = {k: tot[k] + hw[k] for k in tot}
        L.append(f'{r["id"]} {r["name"]}: hand-written register/slot facts supplied by the table '
                 f'{hw["supplied"]}/{hw["facts"]} (entry arguments {s["param"]["supplied"]}/'
                 f'{s["param"]["facts"]}, cut facts {s["cut"]["supplied"]}/{s["cut"]["facts"]}: '
                 f'{s["cut"]["reg"]} registers, {s["cut"]["slot"]} slots); frame convention '
                 f'{s["convention"]["supplied"]}/{s["convention"]["facts"]}')
        for c in r['cuts'] if verbose else ():
            fx = [x for x in r['facts'] if x['pc'] == c['pc'] and x['class'] != 'convention']
            L.append(f'  {c["pc"]:#x}{"" if c["map_cut"] else " (not a map cut)"}: table {c["table"] or "-"}')
            for x in fx:
                loc = reg_name(x['loc']) if x['kind'] == 'reg' else f'frame+{x["loc"]:#x}/{x["size"]}'
                L.append(f'    {loc} = {x["value"]}  <- {", ".join(x["supplied_by"]) or "not supplied"}')
    L.insert(0, f'S23 step 3: {tot["supplied"]}/{tot["facts"]} hand-written register and slot facts '
                f'would have been supplied by the table'
                + (f' ({tot["supplied"] / tot["facts"]:.1%})' if tot['facts'] else ''))
    return '\n'.join(L)


# ------------------------------------------------------------------------------ CLI

def register(sub, package, load_json):
    mp = os.path.join(package, 'map')
    vp = sub.add_parser('varloc', help='variable locations at cut points (plan S23)')
    vs = vp.add_subparsers(dest='varloc_cmd', required=True)
    b = vs.add_parser('build', help='write map/varloc/<id>.json for every target function')
    b.add_argument('--map', default=os.path.join(mp, 'map.json'))
    b.add_argument('--elf', required=True)
    b.add_argument('--debug-object', required=True)
    b.add_argument('--out', default=os.path.join(mp, 'varloc'))
    b.add_argument('--force', action='store_true')

    def go_build(a):
        idx, wrote = build(load_json(a.map), a.elf, a.debug_object, a.out, a.force)
        c = idx['coverage']
        print(f'zmap: varloc {"->" if wrote else "up to date in"} {a.out} ({c["functions"]} functions, '
              f'{c["located"]}/{c["in_scope"]} variables in scope at cut points have a location'
              f'{"" if wrote else "; not rebuilt"})')
    b.set_defaults(func=go_build)

    v = vs.add_parser('validate', help='compare with the hand-written cut assertions (S23 step 3)')
    v.add_argument('--map', default=os.path.join(mp, 'map.json'))
    v.add_argument('--elf', required=True)
    v.add_argument('--debug-object', required=True)
    v.add_argument('--out', default=os.path.join(mp, 'varloc', 'validation.json'))
    v.add_argument('-v', '--verbose', action='store_true', help='every fact and the table at its cut')

    def go_validate(a):
        report = validate(load_json(a.map), package, Debug(a.elf, a.debug_object))
        with open(a.out, 'w') as fh:
            json.dump(report, fh, indent=1)
            fh.write('\n')
        print(validation_text(report, a.verbose))
    v.set_defaults(func=go_validate)
