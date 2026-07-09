#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

nix build "$repo_root#stats" >/dev/null
exec "$repo_root/result/build/sha3_probe"
