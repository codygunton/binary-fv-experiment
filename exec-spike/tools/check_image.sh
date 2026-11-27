#!/usr/bin/env bash
# Verification item 9: the image tables in ZesuExec/Image/Gen.lean match the ELF,
# checked by a second extraction path (llvm-objdump / llvm-objcopy, not gen_image.py).
# Usage: tools/check_image.sh [GEN.lean] [ELF]
# Exits 0 iff every text word and every rodata byte matches.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GEN="${1:-$HERE/ZesuExec/Image/Gen.lean}"
ELF="${2:-/home/cody/zesislar/build/stock-zisk/zesu-zisk.elf}"
OBJDUMP="${OBJDUMP:-llvm-objdump}"
OBJCOPY="${OBJCOPY:-llvm-objcopy}"

exec python3 - "$GEN" "$ELF" "$OBJDUMP" "$OBJCOPY" <<'PY'
import re, subprocess, sys, tempfile, os
gen, elf, objdump, objcopy = sys.argv[1:5]
src = open(gen).read()

# def NAME : Seg|RoSeg where  base := 0x…  words|bytes := [ … ]
seg_re = re.compile(
    r"def\s+(\S+)\s*:\s*(Seg|RoSeg)\s+where\s+base\s*:=\s*(0x[0-9a-fA-F]+)\s+"
    r"(words|bytes)\s*:=\s*\[([^\]]*)\]", re.S)
segs = [(m[1], m[2], int(m[3], 16), [int(x, 0) for x in m[5].replace("\n", " ").split(",") if x.strip()])
        for m in seg_re.finditer(src)]
if not segs:
    sys.exit(f"check_image: no segments parsed from {gen}")

def run(*a):
    return subprocess.run(a, check=True, capture_output=True, text=True).stdout

bad = 0
n_text = n_words = n_ro = n_bytes = 0
insn_re = re.compile(r"^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2,8}\s)+)")
for name, kind, base, vals in segs:
    if kind != "Seg":
        continue
    n_text += 1
    stop = base + 4 * len(vals)
    out = run(objdump, "-d",  # llvm-objdump prints raw instruction bytes by default
              f"--start-address={base:#x}", f"--stop-address={stop:#x}", elf)
    got = {}
    for line in out.splitlines():
        m = insn_re.match(line)
        if not m:
            continue
        addr = int(m[1], 16)
        enc = m[2].split()
        if len(enc) != 1 or len(enc[0]) != 8:
            print(f"MISMATCH {name} {addr:#x}: non-4-byte encoding {' '.join(enc)}")
            bad += 1
            continue
        got[addr] = int(enc[0], 16)
    seg_bad = 0
    for i, w in enumerate(vals):
        a = base + 4 * i
        g = got.pop(a, None)
        if g == w:
            n_words += 1
        else:
            print(f"MISMATCH {name} {a:#x}: Gen {w:#010x} objdump {('missing' if g is None else f'{g:#010x}')}")
            seg_bad += 1
    for a, g in sorted(got.items()):
        print(f"MISMATCH {name} {a:#x}: objdump {g:#010x} not in Gen")
        seg_bad += 1
    bad += seg_bad
    print(f"text {name:8s} {base:#x} {len(vals):4d} words {'ok' if seg_bad == 0 else f'{seg_bad} mismatches'}")

# rodata: dump the section bytes with llvm-objcopy, locate by VMA from llvm-objdump -h.
hdr = run(objdump, "-h", elf)
sec = None
for line in hdr.splitlines():
    f = line.split()
    if len(f) >= 4 and f[1] == ".rodata":
        sec = (int(f[3], 16), int(f[2], 16))  # (vma, size)
if any(k == "RoSeg" for _, k, _, _ in segs):
    if sec is None:
        sys.exit("check_image: no .rodata section in ELF")
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "rodata.bin")
        run(objcopy, f"--dump-section=.rodata={p}", elf, os.path.join(d, "discard.elf"))
        data = open(p, "rb").read()
    vma, size = sec
    for name, kind, base, vals in segs:
        if kind != "RoSeg":
            continue
        n_ro += 1
        seg_bad = 0
        for i, b in enumerate(vals):
            off = base + i - vma
            g = data[off] if 0 <= off < len(data) else None
            if g != b:
                print(f"MISMATCH {name} {base + i:#x}: Gen {b} elf {g}")
                seg_bad += 1
        bad += seg_bad
        n_bytes += len(vals) - seg_bad
        print(f"rodata {name} {base:#x} {len(vals):4d} bytes {'ok' if seg_bad == 0 else f'{seg_bad} mismatches'}")

print(f"check_image: {n_text} text segments, {n_words} words matched; "
      f"{n_ro} rodata segments, {n_bytes} bytes matched; {bad} mismatches")
sys.exit(1 if bad else 0)
PY
