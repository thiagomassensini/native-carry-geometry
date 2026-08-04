#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repository_root="$(cd -- "${script_dir}/.." && pwd)"
output_dir="${1:?usage: scripts/run_audits.sh OUTPUT_DIRECTORY}"

if [[ "${output_dir}" != /* ]]; then
  output_dir="${repository_root}/${output_dir}"
fi

mkdir -p -- "${output_dir}"

python3 "${script_dir}/check_reproducibility.py" \
  --report "${output_dir}/reproducibility.json"
python3 "${script_dir}/check_no_placeholders.py" \
  --report "${output_dir}/source-trust.json"
python3 "${script_dir}/check_dependency_boundary.py" \
  --report "${output_dir}/dependency-boundary.json"
python3 "${script_dir}/check_theorem_registry.py" \
  --report "${output_dir}/theorem-registry.json"
python3 "${script_dir}/generate_theorem_registry.py" \
  --check \
  --report "${output_dir}/elaborated-theorem-registry.json"

(
  cd -- "${repository_root}"
  files=(
    lean-toolchain
    lakefile.toml
    lake-manifest.json
    NativeCarryGeometry.lean
    README.md
    LICENSE
    CITATION.cff
    .zenodo.json
    .release/v0.1.0.md
    .release/v0.2.0.md
  )
  while IFS= read -r -d '' path; do
    files+=("${path#./}")
  done < <(
    find NativeCarryGeometry audit scripts .github/workflows docs \
      -type f -print0 |
      LC_ALL=C sort -z
  )
  sha256sum -- "${files[@]}" > "${output_dir}/audited-files.sha256"
)

python3 - "${output_dir}" <<'PY'
import json
import sys
from pathlib import Path

output = Path(sys.argv[1])
checks = []
for path in sorted(output.glob("*.json")):
    if path.name == "summary.json":
        continue
    payload = json.loads(path.read_text(encoding="utf-8"))
    checks.append(
        {
            "check": payload.get("check"),
            "report": path.name,
            "status": payload.get("status"),
        }
    )
summary = {
    "schema": "native-carry-static-audit-summary-v1",
    "status": "pass" if checks and all(item["status"] == "pass" for item in checks) else "fail",
    "checks": checks,
}
(output / "summary.json").write_text(
    json.dumps(summary, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
if summary["status"] != "pass":
    raise SystemExit("audit summary is not green")
PY

echo "PASS: audit bundle written to ${output_dir}"
