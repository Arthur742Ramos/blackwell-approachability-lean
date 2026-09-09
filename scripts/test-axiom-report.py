from pathlib import Path
import json
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
config = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
names = config["theorem_names"]
valid = "".join(
    f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
    for name in names
)
cases = {
    "complete": (valid, True),
    "unknown axiom": (valid.replace("propext", "unexpectedAxiom", 1), False),
    "missing declaration": ("".join(valid.splitlines(True)[1:]), False),
    "duplicate declaration": (valid + valid.splitlines(True)[0], False),
    "unexpected output": (valid + "warning: output\n", False),
    "empty": ("", False),
}

for label, (report, expected) in cases.items():
    result = subprocess.run(
        [
            sys.executable,
            str(root / "scripts/check-axiom-report.py"),
            str(root / "comparator.json"),
        ],
        input=report,
        text=True,
        capture_output=True,
    )
    if (result.returncode == 0) != expected:
        raise SystemExit(f"FAIL {label}: {result.stdout}{result.stderr}")

print(f"Axiom parser regression tests passed ({len(cases)} cases).")

