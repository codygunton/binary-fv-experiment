#!/usr/bin/env bash
#
# Strict equivalence gate between the canonical (stripped) raw-SSZ objects and the DWARF sidecar
# objects (same pinned Zig source/target/code-model/optimization, changing only `.strip = false`).
#
# The sidecar is only trusted for source/inline extraction after this passes. It proves the sidecar
# is the *same compilation* as the canonical object, differing solely by retained debug info: every
# canonical allocatable section is byte-identical, the RISC-V ISA attributes match, code+data
# relocations resolve identically, and every canonical non-debug symbol is present. The `-fno-strip`
# rename of temporary `.L`/`__anon` labels is handled by comparing relocations/symbols by resolved
# value rather than by label text. The decoder `.text` is additionally pinned to its SHA-256.
#
# Usage: sidecar_equivalence.sh <canonical-obj-dir> <sidecar-obj-dir>
# Env:   READELF (target readelf), ZIG (for `zig objcopy`), EXPECT_TEXT_SHA (decoder .text sha256).
set -euo pipefail

CANON_DIR="$1"
SIDE_DIR="$2"
READELF="${READELF:-readelf}"
ZIG="${ZIG:-zig}"
EXPECT_TEXT_SHA="${EXPECT_TEXT_SHA:-f946b25ea2a0d19ee82ade02ef14eebce363e16190bf54a117eea7eec7805d3b}"

fail() { echo "SIDECAR EQUIVALENCE FAILURE [$1]: $2" >&2; exit 1; }

cmp_object() {
  local name="$1" canon="$2" side="$3"
  local wd; wd="$(mktemp -d)"
  echo "== $name =="

  # Sidecar must carry DWARF; canonical must be stripped.
  "$READELF" -SW "$side"  | grep -q '\.debug_info' || fail "$name" "sidecar has no .debug_info"
  if "$READELF" -SW "$canon" | grep -q '\.debug_info'; then
    fail "$name" "canonical unexpectedly carries DWARF"
  fi

  # Section table rows as: name<TAB>type<TAB>size<TAB>align (Size = field 5, Align = last field).
  sectbl() {
    "$READELF" -SW "$1" | sed -E 's/^[[:space:]]*\[[[:space:]]*[0-9]+\][[:space:]]*//' \
      | awk 'NF>=6 && $1 ~ /^\./ {print $1"\t"$2"\t"$5"\t"$NF}'
  }
  sectbl "$canon" > "$wd/c.sec"
  sectbl "$side"  > "$wd/s.sec"

  # (1) Every canonical non-debug PROGBITS/NOBITS/attributes section exists in the sidecar with
  #     identical size+align, and (for content-bearing sections) byte-identical content.
  while IFS=$'\t' read -r sname stype ssize salign; do
    case "$sname" in
      .debug*|.rela.debug*) continue ;;
      .symtab|.strtab|.shstrtab) continue ;;  # tables legitimately grow under -fno-strip
      .rela.*) continue ;;                      # relocations compared semantically below
    esac
    local srow; srow="$(awk -F'\t' -v n="$sname" '$1==n{print; exit}' "$wd/s.sec")"
    [ -n "$srow" ] || fail "$name" "section $sname missing from sidecar"
    local zsize zalign; zsize="$(cut -f3 <<<"$srow")"; zalign="$(cut -f4 <<<"$srow")"
    [ "$ssize" = "$zsize" ]   || fail "$name" "section $sname size differs ($ssize vs $zsize)"
    [ "$salign" = "$zalign" ] || fail "$name" "section $sname align differs ($salign vs $zalign)"
    case "$stype" in
      PROGBITS|RISCV_ATTRIBUTES)
        "$READELF" -x "$sname" "$canon" | grep '^  0x' > "$wd/c.hex" || true
        "$READELF" -x "$sname" "$side"  | grep '^  0x' > "$wd/s.hex" || true
        cmp -s "$wd/c.hex" "$wd/s.hex" || fail "$name" "section $sname bytes differ"
        ;;
      *) : ;;  # NOBITS (.bss): size/align only
    esac
  done < "$wd/c.sec"

  # (2) Pin the decoder .text SHA-256.
  if [ "$name" = decoder ]; then
    "$ZIG" objcopy -O binary --only-section=.text "$side" "$wd/text.bin"
    local sha; sha="$(sha256sum "$wd/text.bin" | cut -d' ' -f1)"
    [ "$sha" = "$EXPECT_TEXT_SHA" ] || fail "$name" ".text sha256 $sha != $EXPECT_TEXT_SHA"
    echo "  .text sha256 = $sha (pinned OK)"
  fi

  # (3) Code+data relocations identical by (offset,type,symbol-value,addend).
  relo() { "$READELF" -rW "$1" | awk '/^Relocation section/{k=($0!~/debug/)} k&&/^[0-9a-f]{16} /{print $1,$3,$4,$6,$7}' | sort; }
  relo "$canon" > "$wd/c.rel"; relo "$side" > "$wd/s.rel"
  cmp -s "$wd/c.rel" "$wd/s.rel" || fail "$name" "relocations differ (offset/type/symval/addend)"

  # (4) Every canonical non-debug symbol (value,size,type,bind,section-name) present in the sidecar.
  emit_syms() {
    "$READELF" -SW "$1" | awk 'match($0,/\[[ ]*[0-9]+\]/){i=substr($0,RSTART+1,RLENGTH-2)+0; r=substr($0,RSTART+RLENGTH); sub(/^ */,"",r); split(r,a," "); print i"\t"a[1]}' > "$wd/secmap"
    "$READELF" -sW "$1" | awk -v M="$wd/secmap" 'BEGIN{while((getline l < M)>0){split(l,p,"\t");sec[p[1]]=p[2]}}
      $1~/:$/ && $4!="FILE" && $4!="SECTION" { n=$7; s=(n=="ABS"||n=="UND"||n=="COM")?n:sec[n+0]; print $2,$3,$4,$5,s }' | sort -u
  }
  emit_syms "$canon" > "$wd/c.sym"; emit_syms "$side" > "$wd/s.sym"
  local missing; missing="$(comm -23 "$wd/c.sym" "$wd/s.sym" | wc -l)"
  if [ "$missing" != 0 ]; then
    comm -23 "$wd/c.sym" "$wd/s.sym" | head >&2
    fail "$name" "$missing canonical symbols absent from sidecar"
  fi

  echo "  OK: allocatable bytes, size/align, .riscv.attributes, relocations, symbols agree"
  rm -rf "$wd"
}

cmp_object allocator "$CANON_DIR/zesu-raw-ssz-allocator.o" "$SIDE_DIR/zesu-raw-ssz-allocator.o"
cmp_object decoder   "$CANON_DIR/zesu-raw-ssz-decoder.o"   "$SIDE_DIR/zesu-raw-ssz-decoder.o"
cmp_object sink      "$CANON_DIR/zesu-raw-ssz-sink.o"      "$SIDE_DIR/zesu-raw-ssz-sink.o"
echo "SIDECAR EQUIVALENCE: all objects agree; DWARF sidecar is the pinned canonical compilation."
