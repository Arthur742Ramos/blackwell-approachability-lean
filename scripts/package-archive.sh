#!/usr/bin/env bash
set -euo pipefail

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

output=${1:-.cache/blackwell-approachability-lean-0.2.0.zip}
force=0
if [ "${2:-}" = "--force" ]; then
  force=1
elif [ "${2:-}" != "" ]; then
  echo "usage: bash scripts/package-archive.sh [OUTPUT.zip] [--force]" >&2
  exit 2
fi

case "$output" in
  *.zip) ;;
  *) echo "error: output must have a .zip suffix" >&2; exit 2 ;;
esac

if [ -e "$output" ] && [ "$force" -ne 1 ]; then
  echo "error: refusing to overwrite existing archive: $output" >&2
  exit 1
fi

commit=$(git rev-parse HEAD)
if [ -n "$(git status --porcelain=v1 --untracked-files=all)" ]; then
  echo "error: refusing to package a dirty checkout" >&2
  exit 1
fi

mkdir -p "$(dirname -- "$output")"
git archive --format=zip --prefix=blackwell-approachability-lean/ "$commit" -o "$output"
unzip -t "$output" >/dev/null

bad_members=0
while IFS= read -r member; do
  case "$member" in
    blackwell-approachability-lean/) ;;
    blackwell-approachability-lean/*) ;;
    *) echo "error: archive member escapes prefix: $member" >&2; bad_members=1 ;;
  esac
  case "$member" in
    */._*|__MACOSX/*|*/.lake/*|*/.cache/*|*/submission/*|*/output/*|*/mirabelle*/*|*/heaps/*|*/theories/*)
      echo "error: generated or hidden archive member: $member" >&2
      bad_members=1
      ;;
  esac
done < <(unzip -Z1 "$output")

if [ "$bad_members" -ne 0 ]; then
  exit 1
fi

if command -v sha256sum >/dev/null 2>&1; then
  digest=$(sha256sum "$output" | cut -d" " -f1)
else
  digest=$(shasum -a 256 "$output" | cut -d" " -f1)
fi
printf "commit=%s\narchive=%s\nsha256=%s\n" "$commit" "$output" "$digest"
