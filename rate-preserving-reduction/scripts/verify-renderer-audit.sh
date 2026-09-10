#!/usr/bin/env bash
set -euo pipefail

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
renderer_repository=https://github.com/PalomarRegistry/PalomarSubmission.git
renderer_commit=ef2fa1eadcb246c2346ddba39b52eaa53d4bb763
cache_root="$root/.cache"
renderer_dir="$cache_root/palomar-renderer"

for required_command in git lake python3; do
  command -v "$required_command" >/dev/null 2>&1 || {
    echo "error: $required_command is required for the renderer audit" >&2
    exit 1
  }
done

mkdir -p "$cache_root"
if [ ! -d "$renderer_dir/.git" ]; then
  # The pinned audit revision is the current main tip when this script is
  # updated.  A shallow initial clone avoids downloading the renderer's full
  # history in fresh hosted runners; the exact fetch below remains the source
  # of truth for the revision we execute.
  git clone --depth 1 --filter=blob:none --no-checkout "$renderer_repository" "$renderer_dir"
fi
git -C "$renderer_dir" fetch --depth 1 origin "$renderer_commit"
git -C "$renderer_dir" checkout --detach "$renderer_commit"

audit_dir=$(mktemp -d "$cache_root/palomar-core-notation-audit.XXXXXX")
cleanup() {
  rm -rf "$audit_dir"
}
trap cleanup EXIT

cp "$renderer_dir/scripts/core_notation_audit.lean" "$audit_dir/PalomarAudit.lean"
cp "$root/scripts/palomar-core-notation-audit.lakefile.toml" "$audit_dir/lakefile.toml"
cp "$root/scripts/palomar-core-notation-audit.manifest.json" "$audit_dir/lake-manifest.json"
cp "$root/lean-toolchain" "$audit_dir/lean-toolchain"

(cd "$audit_dir" && lake build palomar-audit)
export LEAN_PATH="$(cd "$root" && lake env printenv LEAN_PATH)"

python3 - "$root/comparator.json" "$audit_dir/.lake/build/bin/palomar-audit" <<'PY'
import json
import os
import subprocess
import sys

config_path, audit = sys.argv[1:]
config = json.loads(open(config_path, encoding="utf-8").read())
requests = [
    *(("theorem", name) for name in config.get("theorem_names", [])),
    *(("def", name) for name in config.get("definition_names", [])),
]
if not requests:
    raise SystemExit("error: Comparator configuration has no selected declarations")

command = [audit, config["challenge_module"]]
for kind, name in requests:
    command.extend((kind, name))
result = subprocess.run(command, text=True, capture_output=True, env=os.environ.copy())
if result.returncode:
    sys.stderr.write(result.stderr)
    raise SystemExit(result.returncode)

rows = json.loads(result.stdout)
expected_names = [name for _, name in requests]
if [row.get("name") for row in rows] != expected_names:
    raise SystemExit("error: renderer audit did not return the selected declarations in order")
if any(not isinstance(row.get("declaration"), str) for row in rows):
    raise SystemExit("error: renderer audit returned an invalid declaration payload")
print(f"Official renderer notation audit passed for {len(rows)} declarations.")
PY
