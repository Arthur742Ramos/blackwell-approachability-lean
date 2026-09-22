import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
challenge_path = root / "NonnegativeRankChallenge.lean"
solution_path = root / "NonnegativeRankSolution.lean"
challenge = challenge_path.read_text(encoding="utf-8")
solution = solution_path.read_text(encoding="utf-8")
config = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
targets = config["theorem_names"]

imports = [line.split()[1] for line in challenge.splitlines() if line.startswith("import ")]
if not imports or any(not item.startswith("Mathlib.") for item in imports):
    raise SystemExit(f"error: Challenge imports must be Mathlib-only, found {imports}")
if len(re.findall(r"\bsorry\b", challenge)) != len(targets):
    raise SystemExit("error: expected one Challenge hole per selected theorem")
if re.search(r"\b(sorry|admit|oops)\b", solution):
    raise SystemExit("error: proof placeholder found in Solution")
if re.search(r"^\s*(axiom|unsafe)\b", solution, re.MULTILINE):
    raise SystemExit("error: user axiom or unsafe declaration found in Solution")

for full_name in targets:
    short_name = full_name.rsplit(".", 1)[1]
    signatures = []
    for path, source in ((challenge_path, challenge), (solution_path, solution)):
        start = source.find(f"theorem {short_name}")
        if start < 0:
            raise SystemExit(f"error: {path.name} is missing theorem {short_name}")
        end = source.find(":=", start)
        if end < 0:
            raise SystemExit(f"error: cannot parse theorem {short_name} in {path.name}")
        signatures.append(source[start:end].strip())
    if signatures[0] != signatures[1]:
        raise SystemExit(f"error: Challenge/Solution statement mismatch for {short_name}")

if "[Nonempty m] [Nonempty n]" not in challenge:
    raise SystemExit("error: normalized factorization theorem must guard both finite types")
if "zero-mass" not in (root / "README.md").read_text(encoding="utf-8"):
    raise SystemExit("error: documentation must explain zero-mass normalization")

print("Standalone shape passed: Mathlib-only Challenge, matched statements, explicit finite nonemptiness, and no Solution holes or user axioms.")
