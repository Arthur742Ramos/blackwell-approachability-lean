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
assert citation["version"] == "0.2.0"
assert 'version := v!"0.2.0"' in (root / "lakefile.lean").read_text(encoding="utf-8")

selected = json.loads((root / "comparator.json").read_text(encoding="utf-8"))["theorem_names"]
aligned = [item["lean"] for item in data["alignment"]["statements"]]
assert aligned == selected
assert len(selected) == 11
assert data["classification"]["arxiv"]
assert data["classification"]["msc2020"]
for key in ("question", "selected_result", "audience", "boundary"):
    assert isinstance(data["research_context"][key], str) and data["research_context"][key].strip()
assert data["sources"]
assert any(source["relationship"] == "formalizes" for source in data["sources"])
assert any(
    source["relationship"] == "formalizes" and source.get("location") == "Theorem 4"
    for source in data["sources"]
)
assert data["related_formalizations"] == [{
    "id": "PALOMAR-2026-09-10-000003",
    "relationship": "independent",
    "note": (
        "A separate approved Palomar entry by the same maintainer in this "
        "repository formalizes finite irreducibility obstructions. This project "
        "has no proof dependency on it and is linked only as an independent "
        "registry entry; it has a separate Challenge, Solution, and Comparator "
        "configuration and is not a version update of that entry."
    ),
}]
assert data["automation"]["methods"]
assert isinstance(data["review"]["status"], str)
assert "Eleven selected statements" in data["status"]["scope"]
assert "nonempty finite convex-hull/simplex specialization" in data["research_context"]["boundary"]
assert "existing COLT 2025 theorem" in data["research_context"]["boundary"]
scope = data["status"]["scope"]
for assumption in ("[Nonempty m]", "[Nonempty n]"):
    assert assumption in scope
assert "return" in scope and "witnesses" in scope
assert "empty-index" in data["review"]["notes"]
assert "output witnesses" in data["review"]["notes"]

print("formalization metadata shape passed.")
