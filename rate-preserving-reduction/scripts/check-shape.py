import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
challenge = root / "RateReductionChallenge.lean"
solution = root / "RateReductionSolution.lean"
implementation = root / "RateReduction.lean"
text = challenge.read_text(encoding="utf-8")

if challenge.stat().st_size > 100 * 1024 or len(text.splitlines()) > 1000:
    raise SystemExit("error: RateReductionChallenge.lean exceeds the Palomar size cap")
if not implementation.is_file() or not solution.is_file():
    raise SystemExit("error: missing implementation or Solution module")

imports = [line.split()[1] for line in text.splitlines() if line.startswith("import ")]
if imports != ["Mathlib"]:
    raise SystemExit(f"error: unexpected Challenge imports: {imports}")

holes = len(re.findall(r"\bsorry\b", text))
if holes != 9:
    raise SystemExit(f"error: expected nine Challenge holes, found {holes}")

targets = [
    "Blackwell.RateReduction.Palomar.marginal_simplex",
    "Blackwell.RateReduction.Palomar.outer_jointSimplex",
    "Blackwell.RateReduction.Palomar.marginal_outer",
    "Blackwell.RateReduction.Palomar.pairing_shift_sub_pairing_eq_score",
    "Blackwell.RateReduction.Palomar.regretSum_eq_approachSum",
    "Blackwell.RateReduction.Palomar.regretLoss_eq_approachLoss",
    "Blackwell.RateReduction.Palomar.shift_is_improper",
    "Blackwell.RateReduction.Palomar.finiteTensorTightReduction_of_anchor",
    "Blackwell.RateReduction.Palomar.algorithmicFiniteTensorTightReduction_of_anchor",
]
expected = {
    "challenge_module": "RateReductionChallenge",
    "solution_module": "RateReductionSolution",
    "theorem_names": targets,
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "enable_nanoda": True,
}
config = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
if config != expected:
    raise SystemExit("error: Comparator surface does not match the theorem surface")

for source_path in (challenge, solution):
    source = source_path.read_text(encoding="utf-8")
    for required in (
        "def simplex", "def jointSimplex", "def marginal", "def outer", "def shift",
        "def lift", "def decode", "def reducedLoss", "def pairing", "def score",
        "def approachSum", "def regretSum", "def approachLoss", "def regretLoss",
        "def liftTrajectory", "def decodeTrajectory", "def shiftImproper",
        "def liftStrategy", "def decodeStrategy", "def onlineApproachLoss",
        "def onlineRegretLoss", "def AlgorithmicFiniteTensorTightReduction",
        "theorem pairing_shift_sub_pairing_eq_score", "theorem regretSum_eq_approachSum",
        "theorem regretLoss_eq_approachLoss", "theorem shift_is_improper",
        "theorem finiteTensorTightReduction_of_anchor",
        "theorem algorithmicFiniteTensorTightReduction_of_anchor",
    ):
        if required not in source:
            raise SystemExit(f"error: {source_path.name} is missing {required}")

for path in (implementation, solution, root / "RateReductionExamples.lean"):
    source = path.read_text(encoding="utf-8")
    if re.search(r"(^|[^A-Za-z0-9_])(sorry|admit|oops)([^A-Za-z0-9_]|$)", source):
        raise SystemExit(f"error: proof placeholder found in {path.relative_to(root)}")
    if re.search(r"^\s*(axiom|unsafe)\b", source, re.MULTILINE):
        raise SystemExit(f"error: axiom or unsafe declaration found in {path.relative_to(root)}")

print(f"Standalone shape passed: Challenge {challenge.stat().st_size} bytes, nine holes, nine selected targets.")
