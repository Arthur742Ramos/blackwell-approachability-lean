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
if holes != 21:
    raise SystemExit(f"error: expected twenty-one Challenge holes, found {holes}")

targets = [
    "Blackwell.Palomar.skewPhi_valid_improper_instance",
    "Blackwell.Palomar.sourceAB_valid_improper_family",
    "Blackwell.Palomar.normalized_proper_reduction_implies_canonical_properization",
    "Blackwell.Palomar.loss_basis_pairing_implies_normalized_matrix_identity",
    "Blackwell.Palomar.matrixProperOn_simplex3_iff_on_vertices",
    "Blackwell.Palomar.canonicalProperOn_simplex3_iff_vertex_constraints",
    "Blackwell.Palomar.affine_hyperplane_canonical_properizer_has_nonzero_common_invariant",
    "Blackwell.Palomar.extreme_antipodal_no_canonical_properizer",
    "Blackwell.Palomar.skewPhi_has_no_nonzero_common_invariant",
    "Blackwell.Palomar.canonical_proper_matrices_are_singular",
    "Blackwell.Palomar.skewPhi_not_canonically_proper_reducible",
    "Blackwell.Palomar.skew_canonicalProper_iff_vertex_constraints",
    "Blackwell.Palomar.skewPhi_no_invertible_nine_vertex_properizer",
    "Blackwell.Palomar.skewPhi_not_normalized_proper_reducible",
    "Blackwell.Palomar.skewPhi_not_loss_basis_proper_reducible",
    "Blackwell.Palomar.sourceAB_has_nonzero_common_invariant",
    "Blackwell.Palomar.sourceAB_not_canonically_proper_reducible",
    "Blackwell.Palomar.sourceAB_canonicalProperOn_iff_twelve_corner_constraints",
    "Blackwell.Palomar.sourceAB_no_invertible_twelve_corner_properizer",
    "Blackwell.Palomar.sourceAB_not_normalized_proper_reducible",
    "Blackwell.Palomar.sourceAB_not_loss_basis_proper_reducible",
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
        "def sourceMFor",
        "def normalizedMIntertwining",
        "def properOn",
        "def normalizedProperReductionOn",
        "def basisVector",
        "def matrixColumn",
        "def lossBasisPairingIntertwining",
        "def matrixComparator",
        "def matrixComparatorRepresentation",
        "def matrixProperOn",
        "def canonicalVertexProperOn",
        "def skewCanonicalVertexConstraints",
        "def lossBasisProperReductionOn",
        "def skewDisplacementMatrix",
        "def sourceDisplacementMatrix",
        "def extremePoint",
        "def antipodalDisplacements",
        "def validImproperFamily",
        "def sourceCoefficients",
        "def sourcePhi",
        "def sourceCorners",
        "def sourceABCanonicalCornerConstraints",
        "theorem skewPhi_valid_improper_instance",
        "theorem affine_hyperplane_canonical_properizer_has_nonzero_common_invariant",
        "theorem normalized_proper_reduction_implies_canonical_properization",
        "theorem loss_basis_pairing_implies_normalized_matrix_identity",
        "theorem matrixProperOn_simplex3_iff_on_vertices",
        "theorem canonicalProperOn_simplex3_iff_vertex_constraints",
        "theorem extreme_antipodal_no_canonical_properizer",
        "theorem skewPhi_has_no_nonzero_common_invariant",
        "theorem canonical_proper_matrices_are_singular",
        "theorem skewPhi_not_canonically_proper_reducible",
        "theorem skew_canonicalProper_iff_vertex_constraints",
        "theorem skewPhi_no_invertible_nine_vertex_properizer",
        "theorem skewPhi_not_normalized_proper_reducible",
        "theorem skewPhi_not_loss_basis_proper_reducible",
        "theorem sourceAB_valid_improper_family",
        "theorem sourceAB_has_nonzero_common_invariant",
        "theorem sourceAB_not_canonically_proper_reducible",
        "theorem sourceAB_canonicalProperOn_iff_twelve_corner_constraints",
        "theorem sourceAB_no_invertible_twelve_corner_properizer",
        "theorem sourceAB_not_normalized_proper_reducible",
        "theorem sourceAB_not_loss_basis_proper_reducible",
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
    "twenty-one holes, twenty-one selected targets."
)
