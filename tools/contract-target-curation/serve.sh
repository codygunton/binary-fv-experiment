#!/usr/bin/env bash
set -euo pipefail

readonly PORT=8420
readonly SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
readonly REPO_ROOT="$(cd -- "${SCRIPT_DIR}/../.." && pwd)"

cd "${REPO_ROOT}"
ui_dir="$(nix build .#machine-regions-ui --no-link --print-out-paths)"
echo "Serving the generated Zesu call hierarchy at http://127.0.0.1:${PORT}/"
exec python3 -m http.server "${PORT}" --bind 0.0.0.0 --directory "${ui_dir}"
