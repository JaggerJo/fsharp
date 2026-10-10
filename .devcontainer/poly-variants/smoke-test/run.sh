#!/usr/bin/env bash
# Builds and runs the sample with the patched compiler, then checks FsAutoComplete against it.
# Usage: run.sh [path to fsautocomplete.dll]
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
fsac=${1:-/opt/fsharp-pv/fsautocomplete/fsautocomplete.dll}

work=$(mktemp -d)
cp -R "$here/sample/." "$work"
cd "$work"

output=$(dotnet run)
echo "$output"
grep -qx "rgb(1, 2, 3)" <<<"$output"
echo "ok: sample compiled with the patched compiler and ran"

python3 "$here/lsp_smoke.py" "$fsac" "$work"
