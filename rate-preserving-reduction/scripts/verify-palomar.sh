#!/usr/bin/env bash
set -euo pipefail

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

for file in lean-toolchain lakefile.lean lake-manifest.json \
  RateReduction.lean RateReductionChallenge.lean RateReductionSolution.lean \
  RateReductionExamples.lean comparator.json formalization.yaml CITATION.cff LICENSE \
  scripts/AxiomAudit.lean scripts/check-shape.py scripts/check-metadata.py \
  scripts/check-axiom-report.py scripts/verify-renderer-audit.sh \
  scripts/package-archive.sh scripts/verify-comparator.sh \
  scripts/palomar-core-notation-audit.lakefile.toml \
  scripts/palomar-core-notation-audit.manifest.json; do
  test -f "$file" || {
    echo "error: missing $file" >&2
    exit 1
  }
done

python3 scripts/check-shape.py "$root"

challenge_dependencies=$(lake env lean --src-deps RateReductionChallenge.lean)
while IFS= read -r dependency; do
  case "$dependency" in
    */src/lean/*|*/.lake/packages/mathlib/*) ;;
    *) echo "error: non-Mathlib Challenge dependency: $dependency" >&2; exit 1 ;;
  esac
done <<< "$challenge_dependencies"

lake build
bash scripts/verify-renderer-audit.sh

axioms=$(lake env lean scripts/AxiomAudit.lean 2>&1)
printf "%s\n" "$axioms"
printf "%s\n" "$axioms" | python3 scripts/check-axiom-report.py comparator.json
python3 scripts/check-metadata.py "$root"

lake env lean RateReductionExamples.lean >/dev/null

repository_root=$(git rev-parse --show-toplevel 2>/dev/null || true)
if [ -n "$repository_root" ]; then
  git -C "$repository_root" diff --check
fi

echo "Standalone preparation checks passed."
