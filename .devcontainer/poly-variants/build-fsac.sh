#!/usr/bin/env bash
# Builds FsAutoComplete against a locally built FSharp.Compiler.Service.
# Usage: build-fsac.sh <fsac checkout> <folder with FSharp.Compiler.Service.dll, FSharp.Core.dll, FSharp.DependencyManager.Nuget.dll> <output folder>
#
# FsAutoComplete's packages are restored unchanged (its analyzer SDK pins FSharp.Core exactly, so Paket cannot
# resolve a newer FSharp.Core); UseLocalFcs.targets then swaps in the local assemblies for compilation and publish.
set -euo pipefail

fsac=$(cd "$1" && pwd)
lib=$(cd "$2" && pwd)
out=$3
here=$(cd "$(dirname "$0")" && pwd)

for assembly in FSharp.Compiler.Service FSharp.Core FSharp.DependencyManager.Nuget; do
  if [ ! -f "$lib/$assembly.dll" ]; then
    echo "error: $lib/$assembly.dll not found" >&2
    exit 1
  fi
done

cd "$fsac"

if [ -s "$here/fsac.patch" ]; then
  git apply "$here/fsac.patch"
fi

sed -i.bak "s|^</Project>|  <Import Project=\"$here/UseLocalFcs.targets\" />\n</Project>|" Directory.Build.targets
rm Directory.Build.targets.bak

dotnet tool restore
dotnet paket restore

dotnet publish src/FsAutoComplete/FsAutoComplete.fsproj -c Release -f net10.0 -o "$out" \
  -p:TreatWarningsAsErrors=false \
  -p:LocalFcsDir="$lib"
