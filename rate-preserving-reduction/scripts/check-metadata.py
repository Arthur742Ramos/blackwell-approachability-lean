import json
from pathlib import Path
import sys
import yaml

root = Path(sys.argv[1])
data = yaml.safe_load((root / "formalization.yaml").read_text(encoding="utf-8"))
authors = [
    "Arthur Freitas Ramos",
    "Ruy Jose Guerra Barretto de Queiroz",
    "David Barros Hulak",
]
assert data["version"] == "v0.4"
project = data["project"]
assert project["authors"] == authors
assert project["responsible_maintainers"] == ["Arthur Freitas Ramos"]
assert project["license"] == "BSD-3-Clause"

citation = yaml.safe_load((root / "CITATION.cff").read_text(encoding="utf-8"))
got = [f'{a["given-names"]} {a["family-names"]}' for a in citation["authors"]]
assert got == authors
assert citation["version"] == "0.1.0"
assert 'version := v!"0.1.0"' in (root / "lakefile.lean").read_text(encoding="utf-8")

selected = json.loads((root / "comparator.json").read_text(encoding="utf-8"))["theorem_names"]
aligned = [item["lean"] for item in data["alignment"]["statements"]]
assert aligned == selected
assert len(selected) == 9
assert data["classification"]["arxiv"]
assert data["classification"]["msc2020"]
for key in ("question", "selected_result", "audience", "boundary"):
    assert isinstance(data["research_context"][key], str) and data["research_context"][key].strip()
assert data["sources"]
assert any(source["relationship"] == "formalizes" for source in data["sources"])
assert data["related_formalizations"] == [{
    "id": "PALOMAR-2026-09-10-000003",
    "relationship": "builds-on",
    "note": (
        "A separate approved Palomar entry at the repository root formalizes "
        "finite irreducibility obstructions. This nested project has an "
        "independent Challenge, Solution, Comparator configuration, and intended "
        "blank existing-id field; it is not a version update of that entry."
    ),
}]
assert data["automation"]["methods"]
assert isinstance(data["review"]["status"], str)
assert "Nine selected statements" in data["status"]["scope"]
assert "finite convex-hull/simplex specialization" in data["research_context"]["boundary"]
assert "existing COLT 2025 theorem" in data["research_context"]["boundary"]

print("formalization metadata shape passed.")
