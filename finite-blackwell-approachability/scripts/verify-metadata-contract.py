import sys
from pathlib import Path

renderer_root = Path(sys.argv[1]).resolve()
metadata_path = Path(sys.argv[2]).resolve()
if not (renderer_root / "scripts" / "submission_contract.py").is_file():
    raise SystemExit("error: pinned Palomar submission contract is missing")

sys.path.insert(0, str(renderer_root))
from scripts.submission_contract import load_formalization_metadata  # noqa: E402

load_formalization_metadata(metadata_path)
print("Pinned Palomar formalization metadata contract passed.")
