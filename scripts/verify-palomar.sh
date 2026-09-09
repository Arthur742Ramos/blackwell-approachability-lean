#!/usr/bin/env bash
set -euo pipefail

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

for file in lean-toolchain lakefile.lean lake-manifest.json \
  BlackwellChallenge.lean BlackwellSolution.lean BlackwellApproachability.lean \
  BlackwellExamples.lean comparator.json formalization.yaml LICENSE; do
  test -f "$file" || {
    echo "error: missing $file" >&2
    exit 1
  }
done

python3 scripts/check-shape.py "$root"

challenge_dependencies=$(lake env lean --src-deps BlackwellChallenge.lean)
while IFS= read -r dependency; do
  case "$dependency" in
    */src/lean/*|*/.lake/packages/mathlib/*) ;;
    *) echo "error: non-Mathlib Challenge dependency: $dependency" >&2; exit 1 ;;
  esac
done <<< "$challenge_dependencies"

lake build
lake env lean --src-deps BlackwellSolution.lean >/dev/null

python3 scripts/test-axiom-report.py
axioms=$(lake env lean scripts/AxiomAudit.lean 2>&1)
printf "%s\n" "$axioms"
printf "%s\n" "$axioms" | python3 scripts/check-axiom-report.py comparator.json
python3 scripts/check-metadata.py "$root"

lake env lean BlackwellExamples.lean >/dev/null

if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  git diff --check
fi

echo "Standalone preparation checks passed."

