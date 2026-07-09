#!/usr/bin/env bash
set -euo pipefail

: "${SHA3_SRC:?set SHA3_SRC to the tiny_sha3 source tree}"
: "${MINIZ_SRC:?set MINIZ_SRC to the miniz source tree}"
: "${OUT_DIR:?set OUT_DIR to the output directory}"

CC="${CC:-gcc}"
ZIG="${ZIG:-zig}"
SIZE="${SIZE:-size}"
NM="${NM:-nm}"
OBJDUMP="${OBJDUMP:-objdump}"

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
WORK_DIR="${WORK_DIR:-$OUT_DIR/work}"
BUILD_DIR="$OUT_DIR/build"

COMMON_CFLAGS=(
  -Os
  -g0
  -DNDEBUG
  -ffunction-sections
  -fdata-sections
  -fno-asynchronous-unwind-tables
  -fno-unwind-tables
  -fno-stack-protector
  -fomit-frame-pointer
  -fno-pie
)

rm -rf "$WORK_DIR" "$BUILD_DIR"
mkdir -p "$WORK_DIR" "$BUILD_DIR"

cp -R "$SHA3_SRC" "$WORK_DIR/tiny_sha3"
cp -R "$MINIZ_SRC" "$WORK_DIR/miniz"
chmod -R u+w "$WORK_DIR"

"$CC" "${COMMON_CFLAGS[@]}" \
  -I"$WORK_DIR/tiny_sha3" \
  -c "$WORK_DIR/tiny_sha3/sha3.c" \
  -o "$BUILD_DIR/sha3.o"

"$CC" "${COMMON_CFLAGS[@]}" \
  -I"$SCRIPT_DIR" \
  -I"$WORK_DIR/miniz" \
  -c "$WORK_DIR/miniz/miniz_tinfl.c" \
  -o "$BUILD_DIR/tinfl.o"

"$CC" "${COMMON_CFLAGS[@]}" -no-pie \
  -I"$WORK_DIR/tiny_sha3" \
  "$SCRIPT_DIR/sha3_harness.c" \
  "$BUILD_DIR/sha3.o" \
  -Wl,--gc-sections \
  -o "$BUILD_DIR/sha3_probe"

"$CC" "${COMMON_CFLAGS[@]}" -no-pie \
  -I"$SCRIPT_DIR" \
  -I"$WORK_DIR/miniz" \
  "$SCRIPT_DIR/tinfl_harness.c" \
  "$BUILD_DIR/tinfl.o" \
  -Wl,--gc-sections \
  -o "$BUILD_DIR/tinfl_probe"

"$ZIG" cc -target aarch64-linux-gnu "${COMMON_CFLAGS[@]}" \
  -I"$WORK_DIR/tiny_sha3" \
  -c "$WORK_DIR/tiny_sha3/sha3.c" \
  -o "$BUILD_DIR/sha3.aarch64.o"

"$ZIG" cc -target aarch64-linux-gnu "${COMMON_CFLAGS[@]}" \
  -I"$SCRIPT_DIR" \
  -I"$WORK_DIR/miniz" \
  -c "$WORK_DIR/miniz/miniz_tinfl.c" \
  -o "$BUILD_DIR/tinfl.aarch64.o"

"$ZIG" cc -target aarch64-linux-gnu "${COMMON_CFLAGS[@]}" -no-pie \
  -I"$WORK_DIR/tiny_sha3" \
  "$SCRIPT_DIR/sha3_harness.c" \
  "$BUILD_DIR/sha3.aarch64.o" \
  -Wl,--gc-sections \
  -o "$BUILD_DIR/sha3_probe.aarch64"

"$ZIG" cc -target aarch64-linux-gnu "${COMMON_CFLAGS[@]}" -no-pie \
  -I"$SCRIPT_DIR" \
  -I"$WORK_DIR/miniz" \
  "$SCRIPT_DIR/tinfl_harness.c" \
  "$BUILD_DIR/tinfl.aarch64.o" \
  -Wl,--gc-sections \
  -o "$BUILD_DIR/tinfl_probe.aarch64"

count_symbol_instructions() {
  local file="$1"
  local symbol="$2"
  "$OBJDUMP" -d --disassemble="$symbol" "$file" |
    awk '/^[[:space:]]+[0-9a-f]+:/ { n++ } END { print n + 0 }'
}

selected_instruction_total() {
  local file="$1"
  shift
  local total=0
  local count
  for symbol in "$@"; do
    count="$(count_symbol_instructions "$file" "$symbol")"
    total=$((total + count))
  done
  printf '%s\n' "$total"
}

branchish_total() {
  local tmp
  tmp="$(mktemp)"
  local item file symbol
  for item in "$@"; do
    file="${item%%:*}"
    symbol="${item#*:}"
    "$OBJDUMP" -d --disassemble="$symbol" "$file" >> "$tmp"
  done
  awk '
    /^[[:space:]]+[0-9a-f]+:/ {
      nfields = split($0, tabbed, "\t")
      instr = tabbed[nfields]
      sub(/^[[:space:]]+/, "", instr)
      split(instr, a, /[[:space:]]+/)
      m = a[1]
      if (m ~ /^j/ && m != "jmp") cond++
      else if (m == "jmp") uncond++
      else if (m ~ /^call/) call++
      else if (m ~ /^ret/) ret++
    }
    END { print cond + uncond + call + ret + 0 }
  ' "$tmp"
  rm -f "$tmp"
}

text_size() {
  local file="$1"
  "$SIZE" "$file" | awk 'NR == 2 { print $1 }'
}

file_size() {
  local file="$1"
  stat -c '%s' "$file"
}

sha3_native_object_text="$(text_size "$BUILD_DIR/sha3.o")"
tinfl_native_object_text="$(text_size "$BUILD_DIR/tinfl.o")"
sha3_native_linked_text="$(text_size "$BUILD_DIR/sha3_probe")"
tinfl_native_linked_text="$(text_size "$BUILD_DIR/tinfl_probe")"
sha3_aarch64_object_text="$(text_size "$BUILD_DIR/sha3.aarch64.o")"
tinfl_aarch64_object_text="$(text_size "$BUILD_DIR/tinfl.aarch64.o")"
sha3_aarch64_linked_text="$(text_size "$BUILD_DIR/sha3_probe.aarch64")"
tinfl_aarch64_linked_text="$(text_size "$BUILD_DIR/tinfl_probe.aarch64")"

sha3_selected_instrs="$(
  selected_instruction_total "$BUILD_DIR/sha3_probe" \
    sha3_keccakf sha3_init sha3_update sha3_final sha3 main
)"
tinfl_selected_instrs="$(
  selected_instruction_total "$BUILD_DIR/tinfl_probe" \
    tinfl_decompress tinfl_decompress_mem_to_mem main
)"

sha3_branchish="$(
  branchish_total \
    "$BUILD_DIR/sha3_probe:sha3_keccakf" \
    "$BUILD_DIR/sha3_probe:sha3_init" \
    "$BUILD_DIR/sha3_probe:sha3_update" \
    "$BUILD_DIR/sha3_probe:sha3_final" \
    "$BUILD_DIR/sha3_probe:sha3"
)"
tinfl_branchish="$(
  branchish_total \
    "$BUILD_DIR/tinfl_probe:tinfl_decompress" \
    "$BUILD_DIR/tinfl_probe:tinfl_decompress_mem_to_mem"
)"

"$BUILD_DIR/sha3_probe"
"$BUILD_DIR/tinfl_probe"

"$SIZE" \
  "$BUILD_DIR/sha3.o" \
  "$BUILD_DIR/tinfl.o" \
  "$BUILD_DIR/sha3_probe" \
  "$BUILD_DIR/tinfl_probe" \
  "$BUILD_DIR/sha3.aarch64.o" \
  "$BUILD_DIR/tinfl.aarch64.o" \
  "$BUILD_DIR/sha3_probe.aarch64" \
  "$BUILD_DIR/tinfl_probe.aarch64" > "$OUT_DIR/size.txt"

"$NM" -S --size-sort --radix=d \
  "$BUILD_DIR/sha3.o" \
  "$BUILD_DIR/tinfl.o" \
  "$BUILD_DIR/sha3_probe" \
  "$BUILD_DIR/tinfl_probe" \
  "$BUILD_DIR/sha3.aarch64.o" \
  "$BUILD_DIR/tinfl.aarch64.o" > "$OUT_DIR/symbols.txt"

{
  echo "tool,value"
  printf 'cc,%s\n' "$("$CC" --version | head -n 1)"
  printf 'zig,%s\n' "$("$ZIG" version)"
  printf 'size,%s\n' "$("$SIZE" --version | head -n 1)"
  printf 'nm,%s\n' "$("$NM" --version | head -n 1)"
  printf 'objdump,%s\n' "$("$OBJDUMP" --version | head -n 1)"
} > "$OUT_DIR/toolchain.csv"

cat > "$OUT_DIR/stats.tsv" <<EOF
target	arch	object_text	linked_text	selected_instructions	branchish	file_size_object	file_size_linked
sha3	x86_64	$sha3_native_object_text	$sha3_native_linked_text	$sha3_selected_instrs	$sha3_branchish	$(file_size "$BUILD_DIR/sha3.o")	$(file_size "$BUILD_DIR/sha3_probe")
tinfl	x86_64	$tinfl_native_object_text	$tinfl_native_linked_text	$tinfl_selected_instrs	$tinfl_branchish	$(file_size "$BUILD_DIR/tinfl.o")	$(file_size "$BUILD_DIR/tinfl_probe")
sha3	aarch64	$sha3_aarch64_object_text	$sha3_aarch64_linked_text			$(file_size "$BUILD_DIR/sha3.aarch64.o")	$(file_size "$BUILD_DIR/sha3_probe.aarch64")
tinfl	aarch64	$tinfl_aarch64_object_text	$tinfl_aarch64_linked_text			$(file_size "$BUILD_DIR/tinfl.aarch64.o")	$(file_size "$BUILD_DIR/tinfl_probe.aarch64")
EOF

cat > "$OUT_DIR/stats.md" <<EOF
# Binary Size Stats

## Inputs

- SHA-3: \`mjosaarinen/tiny_sha3\` at \`dcbb3192047c2a721f5f851db591871d428036a9\`
- DEFLATE: \`richgel999/miniz\` at \`77d0dce8627735138c51770d1799a1ef48f2117d\`

## Toolchain

\`\`\`text
$("$CC" --version | head -n 1)
zig $("$ZIG" version)
$("$SIZE" --version | head -n 1)
\`\`\`

## Native x86-64

| Target | Object \`.text\` | Linked \`.text\` | Selected implementation instructions | Branch/call/ret-ish |
|---|---:|---:|---:|---:|
| \`tiny_sha3/sha3.c\` | ${sha3_native_object_text} B | ${sha3_native_linked_text} B | ${sha3_selected_instrs} | ${sha3_branchish} |
| \`miniz/miniz_tinfl.c\` | ${tinfl_native_object_text} B | ${tinfl_native_linked_text} B | ${tinfl_selected_instrs} | ${tinfl_branchish} |

## AArch64

| Target | Object \`.text\` | Linked \`.text\` |
|---|---:|---:|
| \`tiny_sha3/sha3.c\` | ${sha3_aarch64_object_text} B | ${sha3_aarch64_linked_text} B |
| \`miniz/miniz_tinfl.c\` | ${tinfl_aarch64_object_text} B | ${tinfl_aarch64_linked_text} B |

## Sanity

The native SHA-3 and \`tinfl\` harness executables both ran successfully. The AArch64 executables
were cross-compiled but not run.

Raw \`size\` output is in \`size.txt\`, symbol sizes are in \`symbols.txt\`, and machine-readable
summary data is in \`stats.tsv\`.
EOF

rm -rf "$WORK_DIR"
