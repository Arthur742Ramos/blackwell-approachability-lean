import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
challenge = root / "BlackwellChallenge.lean"
implementation = root / "BlackwellIrreducibility.lean"
text = challenge.read_text(encoding="utf-8")

if challenge.stat().st_size > 100 * 1024 or len(text.splitlines()) > 1000:
    raise SystemExit("error: BlackwellChallenge.lean exceeds the Palomar size cap")
if not implementation.is_file():
    raise SystemExit("error: missing irreducibility implementation module")

imports = [
    line.split()[1] for line in text.splitlines() if line.startswith("import ")
]
if imports != ["Mathlib"]:
    raise SystemExit(f"error: unexpected Challenge imports: {imports}")

holes = len(re.findall(r"\bsorry\b", text))
if holes != 5:
    raise SystemExit(f"error: expected five Challenge holes, found {holes}")

targets = [
    "Blackwell.Palomar.skewPhi_valid_improper_instance",
    "Blackwell.Palomar.affine_hyperplane_canonical_properizer_has_nonzero_common_invariant",
    "Blackwell.Palomar.skewPhi_has_no_nonzero_common_invariant",
    "Blackwell.Palomar.canonical_proper_matrices_are_singular",
    "Blackwell.Palomar.skewPhi_not_canonically_proper_reducible",
]
expected = {
    "challenge_module": "BlackwellChallenge",
    "solution_module": "BlackwellSolution",
    "theorem_names": targets,
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "enable_nanoda": True,
}
config = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
if config != expected:
    raise SystemExit("error: Comparator surface does not match the standalone theorem surface")

for source_path in (root / "BlackwellChallenge.lean", root / "BlackwellSolution.lean"):
    source = source_path.read_text(encoding="utf-8")
    for required in (
        "def validImproperInstance",
        "def nonzeroVec3",
        "def displacement",
        "def commonInvariant",
        "def canonicalProper",
        "def canonicalProperReduction",
        "def displacementFor",
        "def commonInvariantFor",
        "def correctedFor",
        "def canonicalProperFor",
        "def affineHyperplaneWitness",
        "def commonInvariantOn",
        "def canonicalProperOn",
        "theorem skewPhi_valid_improper_instance",
        "theorem affine_hyperplane_canonical_properizer_has_nonzero_common_invariant",
        "theorem skewPhi_has_no_nonzero_common_invariant",
        "theorem canonical_proper_matrices_are_singular",
        "theorem skewPhi_not_canonically_proper_reducible",
    ):
        if required not in source:
            raise SystemExit(f"error: {source_path.name} is missing {required}")

scope_marker = "canonical normal form"
for source_path in (
    root / "BlackwellChallenge.lean",
    root / "README.md",
    root / "DEVELOPMENT.md",
    root / "formalization.yaml",
):
    source = source_path.read_text(encoding="utf-8")
    if scope_marker not in source:
        raise SystemExit(
            f"error: {source_path.name} must state the canonical-normal-form scope"
        )
    if "full bidirectional affine equivalence" in source:
        raise SystemExit(
            f"error: {source_path.name} overstates the formalized reduction model"
        )

implementation_sources = [
    path for path in root.rglob("*.lean")
    if ".lake" not in path.parts and ".cache" not in path.parts
    and path.name != "BlackwellChallenge.lean"
]
if not implementation_sources:
    raise SystemExit("error: no implementation Lean sources found")

for path in sorted(implementation_sources):
    source = path.read_text(encoding="utf-8")
    if re.search(r"(^|[^A-Za-z0-9_])(sorry|admit|oops)([^A-Za-z0-9_]|$)", source):
        raise SystemExit(f"error: proof placeholder found in {path.relative_to(root)}")
    if re.search(r"^\s*(axiom|unsafe)\b", source, re.MULTILINE):
        raise SystemExit(f"error: axiom or unsafe declaration found in {path.relative_to(root)}")

print(
    f"Standalone shape passed: Challenge {challenge.stat().st_size} bytes, "
    "five holes, five selected targets."
)
