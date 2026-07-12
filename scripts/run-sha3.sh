#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
default_message="sha3-sample-message"

if [ "$#" -eq 0 ]; then
  set -- "$default_message"
fi

exec nix run "$repo_root#sha3" -- "$@"
