#!/usr/bin/env bash
set -euo pipefail

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

for file in \
  lean-toolchain lakefile.lean lake-manifest.json \
  FiniteBlackwell.lean ApproachabilityCore.lean FiniteBlackwellRate.lean \
  FiniteBlackwellChallenge.lean FiniteBlackwellSolution.lean \
  FiniteBlackwellExamples.lean comparator.json formalization.yaml \
  CITATION.cff LICENSE README.md REUSE_AUDIT.md \
  scripts/AxiomAudit.lean scripts/check-axiom-report.py \
  scripts/check-metadata.py scripts/check-shape.py \
  scripts/verify-metadata-contract.py \
  scripts/verify-comparator.sh scripts/verify-renderer-audit.sh \
  scripts/package-archive.sh scripts/palomar-core-notation-audit.lakefile.toml \
  scripts/palomar-core-notation-audit.manifest.json scripts/fake-landrun.sh \
  scripts/landrun-wrapper.sh; do
  test -f "$file" || { echo "error: missing $file" >&2; exit 1; }
done

python3 scripts/check-shape.py "$root"

challenge_dependencies=$(lake env lean --src-deps FiniteBlackwellChallenge.lean)
while IFS= read -r dependency; do
  case "$dependency" in
    */src/lean/*|*/.lake/packages/mathlib/*) ;;
    *) echo "error: non-Mathlib Challenge dependency: $dependency" >&2; exit 1 ;;
  esac
done <<< "$challenge_dependencies"

lake build
bash scripts/verify-renderer-audit.sh
python3 scripts/verify-metadata-contract.py \
  "$root/.cache/palomar-renderer" "$root/formalization.yaml"

axioms=$(lake env lean scripts/AxiomAudit.lean 2>&1)
printf "%s\n" "$axioms"
printf "%s\n" "$axioms" | python3 scripts/check-axiom-report.py comparator.json
python3 scripts/check-metadata.py "$root"
lake env lean FiniteBlackwellExamples.lean >/dev/null

echo "Standalone Palomar preparation checks passed."
