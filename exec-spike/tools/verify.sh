#!/usr/bin/env bash
# Runs plan Verification items 2 (forbidden constructs), 3 (layering) and 9 (image check);
# item 1 (clean build) only with --build. Run from anywhere; works in exec-spike/.
# Exits 0 iff every item run passes.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
BUILD=0
for a in "$@"; do
  case "$a" in
    --build) BUILD=1 ;;
    *) echo "usage: tools/verify.sh [--build]" >&2; exit 2 ;;
  esac
done
GTIME=/home/cody/.cache/zesu-tmp/exec-spike/gtime/bin/time
[ -x "$GTIME" ] || GTIME=/usr/bin/time

declare -a RESULTS
FAIL=0
record() { RESULTS+=("$1: $2"); [ "$2" = PASS ] || FAIL=1; }

if [ "$BUILD" = 1 ]; then
  echo "== 1. clean build"
  rm -rf .lake/build
  if "$GTIME" -v lake build; then record "1 clean build" PASS; else record "1 clean build" FAIL; fi
fi

echo "== 2. forbidden constructs"
hits=$(grep -rnE "\bsorry\b|\badmit\b|native_decide|^axiom |implemented_by" ZesuExec bfv)
# bv_decide adds `_native` axioms (rule 3); backticked mentions in doc comments are not uses.
bvd=$(grep -rnE '(^|[^`])\bbv_decide\b($|[^`])' ZesuExec bfv)
hits="$hits${hits:+${bvd:+$'\n'}}$bvd"
# `unsafe` only in elaborator code: Sym/Tactic.lean and ZesuExec/Vc/ (programme plan rule 2).
unsafe=$(grep -rln "unsafe" ZesuExec | grep -vx "ZesuExec/Sym/Tactic.lean" | grep -v "^ZesuExec/Vc/")
[ -n "$hits" ] && echo "$hits"
[ -n "$unsafe" ] && echo "unsafe outside ZesuExec/Sym/Tactic.lean and ZesuExec/Vc/:" && echo "$unsafe"
if [ -z "$hits$unsafe" ]; then record "2 forbidden constructs" PASS; else record "2 forbidden constructs" FAIL; fi

echo "== 3. layering"
shopt -s nullglob
files=(ZesuExec/Machine.lean ZesuExec/Decode.lean ZesuExec/Image.lean ZesuExec/Service.lean
       ZesuExec/Logic.lean ZesuExec/Sym/*.lean ZesuExec/Fn/*/Spec.lean ZesuExec/Fn/*/Regions.lean
       ZesuExec/Fn/*/Proof.lean)
shopt -u nullglob
existing=()
for f in "${files[@]}"; do [ -f "$f" ] && existing+=("$f"); done
echo "checking ${#existing[@]} files"
lay=$(grep -lE "^import (Sail|LeanRV64DExecutable|BinaryFv|Evm)" "${existing[@]}")
[ -n "$lay" ] && echo "$lay"
if [ -z "$lay" ]; then record "3 layering" PASS; else record "3 layering" FAIL; fi

echo "== 9. image tables vs ELF"
if tools/check_image.sh; then record "9 image check" PASS; else record "9 image check" FAIL; fi

echo "== map freshness (map.json vs static.json and zesu-status output)"
fresh=""
if [ ! -f map/map.json ] || [ ! -f map/status.json ]; then fresh="map/map.json or map/status.json missing"
elif [ map/map.json -ot map/static.json ] || [ map/map.json -ot map/status.json ]; then
  fresh="map/map.json is older than map/static.json or map/status.json"
elif ! lake exe zesu-status 2>/dev/null | cmp -s - map/status.json; then
  fresh="map/status.json differs from the current lake exe zesu-status output"
fi
if [ -z "$fresh" ]; then record "map freshness" PASS
else echo "$fresh; run make -C tools/zmap map"; record "map freshness" FAIL; fi

echo "== zmap check (programme plan S10.7)"
if (cd tools && python3 -m zmap check); then record "zmap check" PASS; else record "zmap check" FAIL; fi

echo "== summary"
printf '%s\n' "${RESULTS[@]}"
exit $FAIL
