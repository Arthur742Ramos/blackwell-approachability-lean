import json
import sys
from pathlib import Path

import yaml

root = Path(sys.argv[1])
metadata = yaml.safe_load((root / "formalization.yaml").read_text(encoding="utf-8"))
citation = yaml.safe_load((root / "CITATION.cff").read_text(encoding="utf-8"))
config = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
authors = ["Arthur Freitas Ramos"]

assert metadata["version"] == "v0.4"
assert metadata["project"]["authors"] == authors
assert metadata["project"]["responsible_maintainers"] == authors
assert metadata["project"]["license"] == "BSD-3-Clause"
assert [f'{author["given-names"]} {author["family-names"]}'
        for author in citation["authors"]] == authors
assert citation["version"] == "0.1.0"
assert 'version := v!"0.1.0"' in (root / "lakefile.lean").read_text(encoding="utf-8")
assert metadata["sources"] and metadata["review"]["status"] == "self-assessed"
assert metadata["status"]["sorry_count"] == 0
assert metadata["status"]["challenge_holes"] == len(config["theorem_names"])
assert metadata["status"]["axioms"] == config["permitted_axioms"]
assert [item["lean"] for item in metadata["alignment"]["statements"]] == config["theorem_names"]
assert all(item["status"] == "proved" for item in metadata["alignment"]["statements"])
for field in ("question", "selected_result", "audience", "boundary"):
    assert metadata["research_context"][field].strip()

print("Formalization metadata and citation shape passed.")
