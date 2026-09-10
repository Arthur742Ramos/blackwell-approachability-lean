import json
from pathlib import Path
import sys
import yaml

root = Path(sys.argv[1])
data = yaml.safe_load((root / "formalization.yaml").read_text(encoding="utf-8"))
authors = ["Arthur Freitas Ramos"]
assert data["version"] == "v0.4"
project = data["project"]
assert project["authors"] == authors
assert project["responsible_maintainers"] == authors
assert project["license"] == "BSD-3-Clause"

citation = yaml.safe_load((root / "CITATION.cff").read_text(encoding="utf-8"))
got = [f'{a["given-names"]} {a["family-names"]}' for a in citation["authors"]]
assert got == authors

selected = json.loads((root / "comparator.json").read_text(encoding="utf-8"))[
    "theorem_names"
]
aligned = [item["lean"] for item in data["alignment"]["statements"]]
assert aligned == selected
assert data["classification"]["arxiv"]
assert data["classification"]["msc2020"]
research_context = data["research_context"]
for key in ("question", "selected_result", "audience", "boundary"):
    assert isinstance(research_context[key], str) and research_context[key].strip()
assert "rate-preserving" in research_context["question"]
assert "existing COLT 2025" in research_context["boundary"]
assert data["sources"]
allowed_source_relationships = {
    "formalizes",
    "adapts",
    "independently-proves",
    "background",
    "other",
}
assert all(
    source["relationship"] in allowed_source_relationships
    for source in data["sources"]
)
assert any(
    source["relationship"] in {"formalizes", "adapts", "independently-proves"}
    for source in data["sources"]
)
assert data["automation"]["methods"]
assert isinstance(data["review"]["status"], str)

allowed_relationships = {
    "",
    "builds-on",
    "adapts",
    "independent",
    "supersedes",
    "other",
    "formalizes",
}
for related in data.get("related_formalizations", []):
    assert related["relationship"] in allowed_relationships

print("formalization metadata shape passed.")
