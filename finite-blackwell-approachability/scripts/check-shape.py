import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
challenge_path = root / "FiniteBlackwellChallenge.lean"
solution_path = root / "FiniteBlackwellSolution.lean"
implementation_paths = [
    root / "FiniteBlackwell.lean",
    root / "ApproachabilityCore.lean",
    root / "FiniteBlackwellRate.lean",
    solution_path,
    root / "FiniteBlackwellExamples.lean",
]
challenge = challenge_path.read_text(encoding="utf-8")
solution = solution_path.read_text(encoding="utf-8")

targets = [
    "Blackwell.FiniteApproachability.Palomar.exists_projection",
    "Blackwell.FiniteApproachability.Palomar.exists_uniform_mixed_response",
    "Blackwell.FiniteApproachability.Palomar.finite_game_approachability_bound",
    "Blackwell.FiniteApproachability.Palomar.finite_game_approachability_of_mixedBlackwell",
]
expected_config = {
    "challenge_module": "FiniteBlackwellChallenge",
    "solution_module": "FiniteBlackwellSolution",
    "theorem_names": targets,
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "enable_nanoda": True,
}
config = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
if config != expected_config:
    raise SystemExit("error: Comparator configuration does not match the selected surface")

imports = [line.split()[1] for line in challenge.splitlines() if line.startswith("import ")]
if imports != ["Mathlib"]:
    raise SystemExit(f"error: Challenge imports must be Mathlib only, found {imports}")

if len(re.findall(r"\bsorry\b", challenge)) != len(targets):
    raise SystemExit("error: expected one Challenge hole for each selected theorem")
if re.search(r"\b(sorry|admit|oops)\b", "\n".join(
    path.read_text(encoding="utf-8") for path in implementation_paths
)):
    raise SystemExit("error: proof placeholder found outside the Challenge")
if re.search(r"^\s*(axiom|unsafe)\b", "\n".join(
    path.read_text(encoding="utf-8") for path in implementation_paths
), re.MULTILINE):
    raise SystemExit("error: axiom or unsafe declaration found in implementation")

for short_name in (
    "exists_projection",
    "exists_uniform_mixed_response",
    "finite_game_approachability_bound",
    "finite_game_approachability_of_mixedBlackwell",
):
    declaration = f"theorem {short_name}"
    for path, source in ((challenge_path, challenge), (solution_path, solution)):
        start = source.find(declaration)
        if start < 0:
            raise SystemExit(f"error: {path.name} is missing {declaration}")
        end = source.find(":=", start)
        if end < 0:
            raise SystemExit(f"error: cannot parse {declaration} in {path.name}")
        signature = source[start:end]
        if "(I → ℝ)" not in signature or "FiniteEuclideanSpace I" in signature:
            raise SystemExit(
                f"error: {declaration} in {path.name} does not expose raw coordinate vectors"
            )
        for forbidden in (
            "[InnerProductSpace ℝ E]", "PiLp", "ULift", "Metric.infDist",
            "FiniteEuclideanSpace I", "Mixed A",
        ):
            if forbidden in signature:
                raise SystemExit(
                    f"error: public theorem surface exposes {forbidden} in {path.name}"
                )
        if "inner ℝ" in signature:
            raise SystemExit(
                f"error: public theorem surface bypasses the coordinate-sum score in {path.name}"
            )

for path, source in ((challenge_path, challenge), (solution_path, solution)):
    if "abbrev FiniteEuclideanSpace (I : Type u) : Type u := I → ℝ" not in source:
        raise SystemExit(
            f"error: {path.name} does not use raw finite-coordinate vectors"
        )
    start = source.find("abbrev mixedBlackwellCondition")
    end = source.find(":=", start)
    signature = source[start:end]
    for assumption in ("[Nonempty A]", "[Nonempty B]", "[Nonempty I]"):
        if assumption not in signature:
            raise SystemExit(
                f"error: mixedBlackwellCondition in {path.name} lacks {assumption}"
            )

for short_name in (
    "exists_uniform_mixed_response",
    "finite_game_approachability_bound",
    "finite_game_approachability_of_mixedBlackwell",
):
    declaration = f"theorem {short_name}"
    for path, source in ((challenge_path, challenge), (solution_path, solution)):
        start = source.find(declaration)
        end = source.find(":=", start)
        signature = source[start:end]
        for assumption in ("[Nonempty A]", "[Nonempty B]", "[Nonempty I]"):
            if assumption not in signature:
                raise SystemExit(
                    f"error: {declaration} in {path.name} lacks {assumption}"
                )

if "def coordinateInner" not in challenge or \
        "coordinateInner (y - z)" not in challenge:
    raise SystemExit("error: Challenge does not expose its coordinate-sum inner product")

for path in implementation_paths:
    source = path.read_text(encoding="utf-8")
    if path.stat().st_size > 500 * 1024:
        raise SystemExit(f"error: unexpectedly large source file: {path.name}")

print(
    "Standalone shape passed: Mathlib-only Challenge, four selected holes, "
    "matching nonempty finite-action and coordinate guards, a coordinate-sum "
    "Euclidean interface over raw finite-coordinate vectors, no implementation "
    "placeholders or user axioms, and exact "
    "Comparator alignment."
)
