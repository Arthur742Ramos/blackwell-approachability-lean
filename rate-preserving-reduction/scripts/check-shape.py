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
challenge_lines = text.splitlines()
undocumented = []
for index, line in enumerate(challenge_lines):
    if re.match(r"^(?:def|abbrev)\s", line):
        previous = index - 1
        while previous >= 0 and not challenge_lines[previous].strip():
            previous -= 1
        if previous < 0 or not challenge_lines[previous].rstrip().endswith("-/"):
            undocumented.append(line.strip())
if undocumented:
    raise SystemExit(
        "error: Challenge definitions lack precise docstrings: " + ", ".join(undocumented)
    )
if not implementation.is_file() or not solution.is_file():
    raise SystemExit("error: missing implementation or Solution module")

imports = [line.split()[1] for line in text.splitlines() if line.startswith("import ")]
if imports != ["Mathlib"]:
    raise SystemExit(f"error: unexpected Challenge imports: {imports}")

holes = len(re.findall(r"\bsorry\b", text))
if holes != 12:
    raise SystemExit(f"error: expected twelve Challenge holes, found {holes}")

targets = [
    "Blackwell.RateReduction.Palomar.marginal_simplex",
    "Blackwell.RateReduction.Palomar.outer_jointSimplex",
    "Blackwell.RateReduction.Palomar.elementaryTensor_eq_outer_pointMass",
    "Blackwell.RateReduction.Palomar.jointSimplex_eq_finiteTensorCombination",
    "Blackwell.RateReduction.Palomar.jointSimplex_eq_finiteRowRankOneCombination",
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
        "def pointMass", "def elementaryTensor",
        "theorem elementaryTensor_eq_outer_pointMass", "def FiniteTensorCombination",
        "theorem jointSimplex_eq_finiteTensorCombination",
        "def FiniteRowRankOneCombination",
        "theorem jointSimplex_eq_finiteRowRankOneCombination",
        "theorem regretLoss_eq_approachLoss", "theorem shift_is_improper",
        "theorem finiteTensorTightReduction_of_anchor",
        "theorem algorithmicFiniteTensorTightReduction_of_anchor",
    ):
        if required not in source:
            raise SystemExit(f"error: {source_path.name} is missing {required}")
    if "FiniteTensorTightReduction u anchor" not in source:
        raise SystemExit(f"error: {source_path.name} does not retain the supplied finite anchor")
    if "AlgorithmicFiniteTensorTightReduction u anchor" not in source:
        raise SystemExit(f"error: {source_path.name} does not retain the supplied algorithmic anchor")

nonempty_declarations = (
    "def approachSum",
    "def regretSum",
    "theorem regretSum_eq_approachSum",
    "theorem jointSimplex_eq_finiteTensorCombination",
    "theorem jointSimplex_eq_finiteRowRankOneCombination",
    "def approachLoss",
    "def regretLoss",
    "theorem regretLoss_eq_approachLoss",
    "theorem approach_to_regret_exact",
    "theorem regret_to_approach_exact",
    "def liftTrajectory",
    "def decodeTrajectory",
    "def FiniteTensorTightReduction",
    "def shiftImproper",
    "theorem shift_is_improper",
    "theorem finiteTensorTightReduction_of_anchor",
    "def onlineApproachLoss",
    "def onlineRegretLoss",
    "def liftStrategy",
    "def decodeStrategy",
    "def AlgorithmicFiniteTensorTightReduction",
    "theorem algorithmicFiniteTensorTightReduction_of_anchor",
)
for source_path in (implementation, challenge, solution):
    source = source_path.read_text(encoding="utf-8")
    for declaration in nonempty_declarations:
        start = source.find(declaration)
        if start < 0:
            raise SystemExit(f"error: {source_path.name} is missing {declaration}")
        signature_end = source.find(":=", start)
        if signature_end < 0:
            raise SystemExit(f"error: cannot parse signature for {declaration} in {source_path.name}")
        signature = source[start:signature_end]
        for assumption in ("[Nonempty m]", "[Nonempty n]"):
            if assumption not in signature:
                raise SystemExit(
                    f"error: {declaration} in {source_path.name} is missing {assumption}"
                )

# These source-level helper theorems are the bridge from history-dependent
# strategy maps to the trajectory-level reduction. Keep the same guards on
# their signatures so the causal translation cannot silently become a
# totalized construction over an empty action type.
strategy_translation_declarations = (
    "theorem runTrajectory_liftStrategy",
    "theorem runTrajectory_decodeStrategy",
    "theorem online_approach_to_regret_exact",
    "theorem online_regret_to_approach_exact",
)
source = implementation.read_text(encoding="utf-8")
for declaration in strategy_translation_declarations:
    start = source.find(declaration)
    if start < 0:
        raise SystemExit(f"error: {implementation.name} is missing {declaration}")
    signature_end = source.find(":=", start)
    if signature_end < 0:
        raise SystemExit(f"error: cannot parse signature for {declaration} in {implementation.name}")
    signature = source[start:signature_end]
    for assumption in ("[Nonempty m]", "[Nonempty n]"):
        if assumption not in signature:
            raise SystemExit(
                f"error: {declaration} in {implementation.name} is missing {assumption}"
            )

# Keep nonemptiness in the proposition itself, not only as an implicit
# typeclass parameter, so the headline claims are visibly non-vacuous.
explicit_existence_declarations = (
    "def FiniteTensorTightReduction",
    "def AlgorithmicFiniteTensorTightReduction",
    "def shiftImproper",
)
for source_path in (implementation, challenge, solution):
    source = source_path.read_text(encoding="utf-8")
    for declaration in explicit_existence_declarations:
        start = source.find(declaration)
        if start < 0:
            raise SystemExit(f"error: {source_path.name} is missing {declaration}")
        definition_end = source.find("\n\n", start)
        if definition_end < 0:
            definition_end = len(source)
        definition = source[start:definition_end]
        if "Nonempty m ∧ Nonempty n" not in definition:
            raise SystemExit(
                f"error: {declaration} in {source_path.name} does not return explicit "
                "nonemptiness witnesses"
            )

for path in (implementation, solution, root / "RateReductionExamples.lean"):
    source = path.read_text(encoding="utf-8")
    if re.search(r"(^|[^A-Za-z0-9_])(sorry|admit|oops)([^A-Za-z0-9_]|$)", source):
        raise SystemExit(f"error: proof placeholder found in {path.relative_to(root)}")
    if re.search(r"^\s*(axiom|unsafe)\b", source, re.MULTILINE):
        raise SystemExit(f"error: axiom or unsafe declaration found in {path.relative_to(root)}")

print(
    f"Standalone shape passed: Challenge {challenge.stat().st_size} bytes, "
    "twelve holes, twelve selected targets, documented Challenge definitions, "
    "and nonemptiness guards on public "
    "definitions and reduction theorems, explicit witnesses in the reduction "
    "and improperness predicates, and guards on all causal strategy translations."
)
