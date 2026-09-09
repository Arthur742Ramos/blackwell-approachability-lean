import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
challenge = root / "BlackwellChallenge.lean"
text = challenge.read_text(encoding="utf-8")

if challenge.stat().st_size > 100 * 1024 or len(text.splitlines()) > 1000:
    raise SystemExit("error: BlackwellChallenge.lean exceeds the Palomar size cap")

imports = [
    line.split()[1] for line in text.splitlines() if line.startswith("import ")
]
expected_imports = [
    "Mathlib.Analysis.InnerProductSpace.Projection.Minimal",
    "Mathlib.Topology.MetricSpace.HausdorffDistance",
    "Mathlib.Topology.Sion",
    "Mathlib.Tactic",
]
if imports != expected_imports:
    raise SystemExit(f"error: unexpected Challenge imports: {imports}")

holes = len(re.findall(r"\bsorry\b", text))
if holes != 11:
    raise SystemExit(f"error: expected eleven Challenge holes, found {holes}")

config = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
targets = [
    "Blackwell.Palomar.exists_projection",
    "Blackwell.Palomar.exists_uniform_response_of_sion",
    "Blackwell.Palomar.blackwell_approachability_bound",
    "Blackwell.Palomar.blackwell_approximate_bound",
    "Blackwell.Palomar.exists_pure_pointwise_strategy",
    "Blackwell.Palomar.pure_game_approachability_of_response",
    "Blackwell.Palomar.mixed_game_approachability_of_response",
    "Blackwell.Palomar.exists_mixed_pointwise_strategy",
    "Blackwell.Palomar.regret_coordinate_of_l2_bound",
    "Blackwell.Palomar.l2_bound_of_coordinate_bound",
    "Blackwell.Palomar.dimension_factor_is_attained",
]
expected = {
    "challenge_module": "BlackwellChallenge",
    "solution_module": "BlackwellSolution",
    "theorem_names": targets,
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "enable_nanoda": True,
}
if config != expected:
    raise SystemExit("error: Comparator surface does not match the standalone theorem surface")

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
    "eleven holes, eleven selected targets."
)
